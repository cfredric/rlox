use const_format::formatcp;
use std::iter::Peekable;

use crate::chunk::ConstantIndex;
use crate::obj::{Function, UpValueIndex};
use crate::opcode::OpCode;
use crate::scanner::{ScanError, Token, TokenPayload, TokenType};
use crate::stack::StackSlotOffset;
use crate::value::Value;
use crate::vm::{Mode, VM};
use crate::Opt;

const MAX_NESTED_CLASSES: usize = 10;
const MAX_NESTED_BLOCKS: usize = 10;
const MAX_NESTED_FUNCTIONS: usize = 10;
const MAX_ARITY: usize = 255;
const MAX_LOCALS: usize = 256;
const MAX_UPVALUES: usize = 256;
const MAX_JUMP_SIZE: usize = 2_usize.pow(16) - 1;

const ARGS_ERROR_STR: &str = formatcp!("Can't have more than {} arguments.", MAX_ARITY);
const PARAMS_ERROR_STR: &str = formatcp!("Can't have more than {} parameters.", MAX_ARITY);

struct Compiler<'opt, 'source, 'vm, I: Iterator<Item = Result<Token<'source>, ScanError>>> {
    opt: &'opt Opt,
    scanner: Peekable<I>,
    current_token: Token<'source>,
    had_error: bool,
    panic_mode: bool,

    vm: &'vm mut VM<'opt>,
    mode: Mode,

    functions: Vec<FunctionState<'source>>,
    class_compilers: Vec<ClassState>,

    block_depth: usize,
}

struct FunctionState<'source> {
    function: Function,
    function_type: FunctionType,

    locals: Vec<Local<'source>>,
    scope_depth: usize,

    upvalues: Vec<CompiledUpValue>,
}

impl<'source> FunctionState<'source> {
    fn new(function_type: FunctionType) -> Self {
        Self::with_name(function_type, "")
    }
    fn with_name(function_type: FunctionType, name: &str) -> Self {
        let local = if function_type != FunctionType::Function {
            Local::new("this")
        } else {
            Local::new("")
        };
        Self {
            function: Function::new(name),
            function_type,
            locals: vec![local],
            scope_depth: 0,
            upvalues: Vec::new(),
        }
    }

    fn local_at_mut(&mut self, offset: StackSlotOffset) -> &mut Local<'source> {
        &mut self.locals[offset.0]
    }

    fn chunk_len(&self) -> usize {
        self.function.chunk.code.len()
    }
}

struct ClassState {
    has_superclass: bool,
}

impl ClassState {
    fn new() -> Self {
        Self {
            has_superclass: false,
        }
    }
}

pub(crate) fn compile<'opt, 'source, 'vm, I: Iterator<Item = Result<Token<'source>, ScanError>>>(
    opt: &'opt Opt,
    scanner: I,
    vm: &'vm mut VM<'opt>,
    mode: Mode,
) -> Option<Function> {
    Compiler::new(opt, scanner, vm, mode).compile()
}

impl<'opt, 'source, 'vm, I: Iterator<Item = Result<Token<'source>, ScanError>>>
    Compiler<'opt, 'source, 'vm, I>
{
    fn new(opt: &'opt Opt, scanner: I, vm: &'vm mut VM<'opt>, mode: Mode) -> Self {
        Self {
            opt,
            scanner: scanner.peekable(),
            current_token: Token::eof(0),
            had_error: false,
            panic_mode: false,
            vm,
            mode,
            functions: vec![FunctionState::with_name(FunctionType::Script, "script")],
            class_compilers: Vec::new(),
            block_depth: 0,
        }
    }

    fn compile(mut self) -> Option<Function> {
        self.skip_invalid_next_tokens();

        while !self.maybe_consume(TokenType::Eof) {
            self.declaration();
        }

        self.consume(TokenType::Eof, "Expect end of expression");
        self.end_compiler()
            .map(|(f, _)| f)
            .filter(|_| !self.had_error)
    }

    fn next_token(&mut self) -> Token<'source> {
        self.scanner
            .peek()
            .expect("no None values from this iterator")
            .expect("all Err values have been skipped")
    }

    /// Sets the current token to the next valid token from the scanner. If the
    /// scanner emits an error, enters panic mode and emits that error.
    fn advance(&mut self) {
        // Advance the current token until we find a valid one.
        loop {
            match self.scanner.next().expect("no None values") {
                Ok(token) => {
                    self.current_token = token;
                    break;
                }
                Err(err) => self.error_at(None, err.message, err.line),
            }
        }

        // Now advance the "next" token until we find a valid one.
        self.skip_invalid_next_tokens();
    }

    fn skip_invalid_next_tokens(&mut self) {
        while let Err(err) = self.scanner.peek().expect("no None values") {
            let err = *err;
            self.error_at(None, err.message, err.line);
            self.scanner.next();
        }
    }

    /// Consumes a token with the given type, setting that token as the current
    /// token. If the next token does not have the expected type, enters panic
    /// mode.
    fn consume<'s: 'source>(&mut self, ty: TokenType, message: &'s str) {
        if self.next_token().ty == ty {
            self.advance();
        } else {
            self.error_at_next(message);
        }
    }

    /// Potentially consumes a token with the given type, setting that token as
    /// the current token. If the next token does not have the expected type,
    /// does nothing.
    fn maybe_consume(&mut self, ty: TokenType) -> bool {
        if self.next_token_is(ty) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn next_token_is(&mut self, ty: TokenType) -> bool {
        self.next_token().ty == ty
    }

    fn emit_opcodes(&mut self, a: OpCode, b: OpCode) {
        self.emit_opcode(a);
        self.emit_opcode(b);
    }

    fn emit_jump(&mut self, opcode: OpCode) -> usize {
        self.emit_opcode(opcode);
        self.current_function().chunk_len() - 1
    }

    fn patch_jump(&mut self, jump_index: usize) {
        let distance = self.current_function().chunk_len() - jump_index - 1;
        if distance > MAX_JUMP_SIZE {
            self.error("Too much code to jump over.");
        }
        self.current_function_mut().function.chunk.code[jump_index] =
            match self.current_function().function.chunk.code[jump_index] {
                OpCode::JumpIfFalse { .. } => OpCode::JumpIfFalse { distance },
                OpCode::Jump { .. } => OpCode::Jump { distance },
                _ => unreachable!("Tried to patch non-jump OpCode"),
            };
    }

    fn emit_loop(&mut self, loop_start: usize) {
        let distance_to_loop_start = self.current_function().chunk_len() - loop_start + 1;
        if distance_to_loop_start > MAX_JUMP_SIZE {
            self.error("Loop body too large.");
        }
        self.emit_opcode(OpCode::Loop {
            distance_to_loop_start,
        });
    }

    fn emit_opcode(&mut self, opcode: OpCode) {
        let line = self.current_token.line;
        self.current_function_mut()
            .function
            .chunk
            .write_chunk(opcode, line);
    }

    fn end_compiler(&mut self) -> Option<(Function, Vec<CompiledUpValue>)> {
        self.emit_return();

        if self.opt.print_code && !self.had_error {
            self.current_function()
                .function
                .chunk
                .disassemble_chunk(&self.current_function().function.name, &self.vm.heap);
        }
        if self.had_error {
            self.functions.pop();
            None
        } else {
            self.functions.pop().map(|f| (f.function, f.upvalues))
        }
    }

    fn synchronize(&mut self) {
        self.panic_mode = false;

        while self.next_token().ty != TokenType::Eof {
            if self.current_token.ty == TokenType::Semicolon {
                return;
            }
            use TokenType::*;
            match self.next_token().ty {
                Class | Fun | Var | For | If | While | Print | Return => {
                    return;
                }
                _ => {}
            }
            self.advance();
        }
    }

    fn declaration(&mut self) {
        if self.maybe_consume(TokenType::Class) {
            self.class_declaration();
        } else if self.maybe_consume(TokenType::Fun) {
            self.fun_declaration();
        } else if self.maybe_consume(TokenType::Var) {
            self.var_declaration();
        } else {
            self.statement();
        }

        if self.panic_mode {
            self.synchronize();
        }
    }

    fn class_declaration(&mut self) {
        let name = self.consume_identifier("Expect class name.");
        let name_constant = self.identifier_constant(name);
        self.declare_variable(name);

        self.emit_opcode(OpCode::Class {
            name: name_constant,
        });
        self.define_variable(name_constant);

        if self.class_compilers.len() > MAX_NESTED_CLASSES {
            self.error("Too many nested classes.");
            return;
        }

        self.class_compilers.push(ClassState::new());

        if self.maybe_consume(TokenType::Less) {
            let superclass_name = self.consume_identifier("Expect superclass name.");
            self.variable(superclass_name, false);

            if name == superclass_name {
                self.error("A class can't inherit from itself.");
            }

            self.begin_scope(); // Matched with end below.
            self.add_local("super");
            self.define_variable(ConstantIndex::special());

            self.named_variable(name, false);
            self.emit_opcode(OpCode::Inherit);
            self.class_compilers
                .last_mut()
                .expect("class stack is nonempty")
                .has_superclass = true;
        }

        self.named_variable(name, false);
        self.consume(TokenType::LeftBrace, "Expect '{' before class body.");
        while !self.next_token_is(TokenType::RightBrace) && !self.next_token_is(TokenType::Eof) {
            self.method();
        }
        self.consume(TokenType::RightBrace, "Expect '}' after class body.");
        self.emit_opcode(OpCode::Pop);

        if self
            .class_compilers
            .last()
            .expect("class stack is nonempty")
            .has_superclass
        {
            self.end_scope(); // Matched with begin in this function.
        }
        self.class_compilers.pop();
    }

    fn fun_declaration(&mut self) {
        let (global, name) = self.parse_variable("Expect function name.");
        self.mark_initialized();
        self.function(FunctionType::Function, name);
        self.define_variable(global);
    }

    fn var_declaration(&mut self) {
        let (global, _) = self.parse_variable("Expect variable name.");

        if self.maybe_consume(TokenType::Equal) {
            self.expression();
        } else {
            self.emit_constant(Value::Nil);
        }
        self.consume(
            TokenType::Semicolon,
            "Expect ';' after variable declaration.",
        );

        self.define_variable(global);
    }

    fn statement(&mut self) {
        if self.maybe_consume(TokenType::Print) {
            self.print_statement();
        } else if self.maybe_consume(TokenType::For) {
            self.for_statement();
        } else if self.maybe_consume(TokenType::If) {
            self.if_statement();
        } else if self.maybe_consume(TokenType::Return) {
            self.return_statement();
        } else if self.maybe_consume(TokenType::While) {
            self.while_statement();
        } else if self.maybe_consume(TokenType::LeftBrace) {
            self.begin_scope(); // Matched with end below.
            self.block();
            self.end_scope(); // Matched with begin immediately above.
        } else {
            self.expression_statement();
        }
    }

    fn for_statement(&mut self) {
        self.begin_scope(); // Matched with end below.
        self.consume(TokenType::LeftParen, "Expect '(' after 'for'.");
        if self.maybe_consume(TokenType::Semicolon) {
            // No initializer.
        } else if self.maybe_consume(TokenType::Var) {
            self.var_declaration();
        } else {
            self.expression_statement();
        }

        let mut loop_start = self.current_function().chunk_len();
        let mut exit_jump = None;
        if !self.maybe_consume(TokenType::Semicolon) {
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after loop condition.");

            exit_jump = Some(self.emit_jump(OpCode::JumpIfFalse { distance: 0 }));
            self.emit_opcode(OpCode::Pop);
        }

        if !self.maybe_consume(TokenType::RightParen) {
            let body_jump = self.emit_jump(OpCode::Jump { distance: 0 });
            let increment_start = self.current_function().chunk_len();
            self.expression();
            self.emit_opcode(OpCode::Pop);
            self.consume(TokenType::RightParen, "Expect ')' after for clauses.");

            self.emit_loop(loop_start);
            loop_start = increment_start;
            self.patch_jump(body_jump);
        }

        self.statement();
        self.emit_loop(loop_start);

        if let Some(offset) = exit_jump {
            self.patch_jump(offset);
            self.emit_opcode(OpCode::Pop);
        }

        self.end_scope(); // Matched with begin at the beginning of this fn.
    }

    fn if_statement(&mut self) {
        self.consume(TokenType::LeftParen, "Expect '(' after 'if'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");

        let then_jump = self.emit_jump(OpCode::JumpIfFalse { distance: 0 });
        self.emit_opcode(OpCode::Pop);
        self.statement();
        let else_jump = self.emit_jump(OpCode::Jump { distance: 0 });
        self.patch_jump(then_jump);
        self.emit_opcode(OpCode::Pop);
        if self.maybe_consume(TokenType::Else) {
            self.statement();
        }
        self.patch_jump(else_jump);
    }

    fn while_statement(&mut self) {
        let loop_start = self.current_function().chunk_len();
        self.consume(TokenType::LeftParen, "Expect '(' after 'while'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");

        let exit_jump = self.emit_jump(OpCode::JumpIfFalse { distance: 0 });
        self.emit_opcode(OpCode::Pop);
        self.statement();
        self.emit_loop(loop_start);

        self.patch_jump(exit_jump);
        self.emit_opcode(OpCode::Pop);
    }

    fn block(&mut self) {
        if self.block_depth > MAX_NESTED_BLOCKS {
            self.error("Too many nested blocks.");
            return;
        }
        self.block_depth += 1;
        while !self.next_token_is(TokenType::RightBrace) && !self.next_token_is(TokenType::Eof) {
            self.declaration();
        }

        self.consume(TokenType::RightBrace, "Expect '}' after block.");
        self.block_depth -= 1;
    }

    fn function(&mut self, ty: FunctionType, function_name: &'source str) {
        if self.functions.len() > MAX_NESTED_FUNCTIONS {
            self.error("Too many nested functions.");
            return;
        }
        self.functions.push(if ty == FunctionType::Script {
            FunctionState::new(ty)
        } else {
            FunctionState::with_name(ty, function_name)
        });
        self.begin_scope();

        self.consume(TokenType::LeftParen, "Expect '(' after function name.");
        if !self.next_token_is(TokenType::RightParen) {
            loop {
                self.current_function_mut().function.arity += 1;
                if self.current_function().function.arity > MAX_ARITY {
                    self.error_at_next(PARAMS_ERROR_STR);
                }
                let (constant, _) = self.parse_variable("Expect parameter name.");
                self.define_variable(constant);

                if !self.maybe_consume(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(TokenType::RightParen, "Expect ')' after parameters.");
        self.consume(TokenType::LeftBrace, "Expect '{' before function body.");
        self.block();

        // Not in book, and not strictly necessary, but no big reason not to do
        // it.
        self.end_scope();
        if let Some((function, upvalues)) = self.end_compiler() {
            let function = self.vm.new_function(function);
            let function = self.make_constant(Value::ObjReference(function));
            self.emit_opcode(OpCode::Closure { function, upvalues });
        }
    }

    fn consume_identifier<'e: 'source>(&mut self, error_message: &'e str) -> &'source str {
        match self.next_token().ty {
            TokenType::Identifier { name } => {
                self.advance();
                name
            }
            _ => {
                self.error_at_next(error_message);
                ""
            }
        }
    }

    fn method(&mut self) {
        let method_name = self.consume_identifier("Expect method name.");
        let name = self.identifier_constant(method_name);

        let mut ty = FunctionType::Method;
        if method_name == "init" {
            ty = FunctionType::Initializer;
        }
        self.function(ty, method_name);

        self.emit_opcode(OpCode::Method { name });
    }

    fn begin_scope(&mut self) {
        self.current_function_mut().scope_depth += 1;
    }

    fn end_scope(&mut self) {
        self.current_function_mut().scope_depth -= 1;

        while matches!(self.current_function().locals.last(), Some(local) if local.depth.map_or(false, |d| d > self.current_function().scope_depth))
        {
            if self
                .current_function()
                .locals
                .last()
                .expect("already checked via matches!")
                .is_captured
            {
                self.emit_opcode(OpCode::CloseUpvalue);
            } else {
                self.emit_opcode(OpCode::Pop);
            }
            self.current_function_mut().locals.pop();
        }
    }

    fn print_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after value.");
        self.emit_opcode(OpCode::Print);
    }

    fn return_statement(&mut self) {
        if self.current_function().function_type == FunctionType::Script {
            self.error("Can't return from top-level code.");
        }
        if self.maybe_consume(TokenType::Semicolon) {
            self.emit_return();
        } else {
            if self.current_function().function_type == FunctionType::Initializer {
                self.error("Can't return a value from an initializer.");
            }
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after return value.");
            self.emit_opcode(OpCode::Return);
        }
    }

    fn expression_statement(&mut self) {
        self.expression();
        if match self.mode {
            Mode::Repl => {
                if self.current_function().function_type == FunctionType::Script {
                    if self.maybe_consume(TokenType::Semicolon) {
                        true
                    } else if self.next_token().ty == TokenType::Eof {
                        // If we're at the EOF, it's ok to omit the last
                        // semicolon from the last expression. The VM should
                        // find that value on the stack and print it.
                        false
                    } else {
                        // If we're not at EOF, then semicolons are still required.
                        self.error("Expect ';' after expression.");
                        false // Doesn't matter due to panic mode, but we can still be correct.
                    }
                } else {
                    self.consume(TokenType::Semicolon, "Expect ';' after expression.");
                    true
                }
            }
            Mode::Script => {
                self.consume(TokenType::Semicolon, "Expect ';' after expression.");
                true
            }
        } {
            self.emit_opcode(OpCode::Pop);
        }
    }

    fn grouping(&mut self) {
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after expression.");
    }

    fn number(&mut self, value: f64) {
        self.emit_constant(Value::Double(value));
    }

    fn string(&mut self, string: &str) {
        let len = string.len();
        let lox_string = self.vm.copy_string(&string[1..len - 1]);
        self.emit_constant(Value::ObjReference(lox_string));
    }

    fn unary(&mut self) {
        let op_ty = self.current_token.ty;
        self.parse_precedence(Precedence::Unary);
        match op_ty {
            TokenType::Minus => self.emit_opcode(OpCode::Negate),
            TokenType::Bang => self.emit_opcode(OpCode::Not),
            _ => self.error("Unexpected unary operand."),
        }
    }

    fn binary(&mut self, precedence: Precedence) {
        let ty = self.current_token.ty;
        self.parse_precedence(precedence.plus_one());

        match ty {
            TokenType::BangEqual => self.emit_opcodes(OpCode::Equal, OpCode::Not),
            TokenType::EqualEqual => self.emit_opcode(OpCode::Equal),
            TokenType::Greater => self.emit_opcode(OpCode::Greater),
            TokenType::GreaterEqual => self.emit_opcodes(OpCode::Less, OpCode::Not),
            TokenType::Less => self.emit_opcode(OpCode::Less),
            TokenType::LessEqual => self.emit_opcodes(OpCode::Greater, OpCode::Not),
            TokenType::Plus => self.emit_opcode(OpCode::Add),
            TokenType::Minus => self.emit_opcode(OpCode::Subtract),
            TokenType::Star => self.emit_opcode(OpCode::Multiply),
            TokenType::Slash => self.emit_opcode(OpCode::Divide),
            _ => {}
        }
    }

    fn call(&mut self) {
        let arg_count = self.argument_list();
        self.emit_opcode(OpCode::Call { arg_count });
    }

    fn dot(&mut self, can_assign: bool) {
        let name = self.consume_identifier("Expect property name after '.'.");
        let name = self.identifier_constant(name);

        if can_assign && self.maybe_consume(TokenType::Equal) {
            self.expression();
            self.emit_opcode(OpCode::SetProperty { name });
        } else if self.maybe_consume(TokenType::LeftParen) {
            let arg_count = self.argument_list();
            self.emit_opcode(OpCode::Invoke {
                method_name: name,
                arg_count,
            });
        } else {
            self.emit_opcode(OpCode::GetProperty { name });
        }
    }

    fn literal(&mut self) {
        match self.current_token.ty {
            TokenType::False => self.emit_opcode(OpCode::Bool { value: false }),
            TokenType::Nil => self.emit_opcode(OpCode::Nil),
            TokenType::True => self.emit_opcode(OpCode::Bool { value: true }),
            _ => unreachable!("Unexpected TokenType in literal"),
        }
    }

    fn parse_precedence(&mut self, prec: Precedence) {
        self.advance();
        let can_assign = prec <= Precedence::Assignment;
        match get_rule(self.current_token.ty).prefix {
            Some(f) => f(
                self,
                ParseFnCtx {
                    can_assign,
                    payload: self.current_token.ty.payload(),
                },
            ),
            None => {
                self.error("Expect expression.");
                return;
            }
        }

        while let Some(infix) = get_rule::<'source, I>(self.next_token().ty).infix {
            if infix.precedence < prec {
                break;
            }
            self.advance();
            (infix.parse)(
                self,
                ParseFnCtx {
                    can_assign,
                    payload: self.current_token.ty.payload(),
                },
            );
        }

        if can_assign && self.maybe_consume(TokenType::Equal) {
            self.error("Invalid assignment target.");
        }
    }

    fn parse_variable<'e: 'source>(
        &mut self,
        error_message: &'e str,
    ) -> (ConstantIndex, &'source str) {
        let name = self.consume_identifier(error_message);
        self.declare_variable(name);
        if self.current_function().scope_depth > 0 {
            (ConstantIndex::error(), "")
        } else {
            (self.identifier_constant(name), name)
        }
    }

    fn identifier_constant(&mut self, name: &str) -> ConstantIndex {
        let ptr = self.vm.copy_string(name);
        self.make_constant(Value::ObjReference(ptr))
    }

    fn define_variable(&mut self, global: ConstantIndex) {
        if self.current_function().scope_depth > 0 {
            self.mark_initialized();
        } else {
            self.emit_opcode(OpCode::DefineGlobal(global))
        }
    }

    fn argument_list(&mut self) -> usize {
        let mut arg_count = 0;
        if !self.next_token_is(TokenType::RightParen) {
            loop {
                self.expression();
                arg_count += 1;
                if arg_count > MAX_ARITY {
                    self.error(ARGS_ERROR_STR);
                }

                if !self.maybe_consume(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen, "Expect ')' after arguments.");
        arg_count
    }

    fn and(&mut self) {
        let end_jump = self.emit_jump(OpCode::JumpIfFalse { distance: 0 });
        self.emit_opcode(OpCode::Pop);
        self.parse_precedence(Precedence::And);
        self.patch_jump(end_jump);
    }

    fn or(&mut self) {
        let else_jump = self.emit_jump(OpCode::JumpIfFalse { distance: 0 });
        let end_jump = self.emit_jump(OpCode::Jump { distance: 0 });

        self.patch_jump(else_jump);
        self.emit_opcode(OpCode::Pop);

        self.parse_precedence(Precedence::Or);
        self.patch_jump(end_jump);
    }

    fn mark_initialized(&mut self) {
        if self.current_function().scope_depth != 0 {
            self.current_function_mut()
                .locals
                .last_mut()
                .expect("locals is never empty")
                .depth = Some(self.current_function().scope_depth);
        }
    }

    fn declare_variable(&mut self, name: &'source str) {
        if self.current_function().scope_depth == 0 {
            return;
        }
        let current_function = self.current_function();
        if current_function
            .locals
            .iter()
            .any(|l| !l.depth.map_or(false, |d| d < current_function.scope_depth) && name == l.name)
        {
            self.error("Already a variable with this name in this scope.");
        }
        self.add_local(name);
    }

    fn add_local(&mut self, name: &'source str) {
        if self.current_function().locals.len() >= MAX_LOCALS {
            self.error("Too many local variables in function.");
        } else {
            self.current_function_mut().locals.push(Local {
                name,
                depth: None,
                is_captured: false,
            });
        }
    }

    fn variable(&mut self, name: &str, can_assign: bool) {
        self.named_variable(name, can_assign)
    }

    fn this(&mut self) {
        if self.class_compilers.last().is_some() {
            self.variable("this", false);
        } else {
            self.error("Can't use 'this' outside of a class.");
        }
    }

    fn super_(&mut self) {
        match self.class_compilers.last() {
            Some(c) if !c.has_superclass => {
                self.error("Can't use 'super' in a class with no superclass.");
            }
            Some(_) => {}
            None => {
                self.error("Can't use 'super' outside of a class.");
            }
        }
        self.consume(TokenType::Dot, "Expect '.' after 'super'.");
        let method = self.consume_identifier("Expect superclass method name.");
        let method = self.identifier_constant(method);

        self.named_variable("this", false);
        if self.maybe_consume(TokenType::LeftParen) {
            let arg_count = self.argument_list();
            self.named_variable("super", false);
            self.emit_opcode(OpCode::SuperInvoke { method, arg_count });
        } else {
            self.named_variable("super", false);
            self.emit_opcode(OpCode::GetSuper { method });
        }
    }

    fn named_variable(&mut self, name: &str, can_assign: bool) {
        let current_idx = self.functions.len() - 1;
        let (get_op, set_op) = if let Some(arg) = self.resolve_local(current_idx, name) {
            (OpCode::GetLocal(arg), OpCode::SetLocal(arg))
        } else if let Some(arg) = self.resolve_upvalue(self.functions.len() - 1, name) {
            (OpCode::GetUpvalue(arg), OpCode::SetUpvalue(arg))
        } else {
            let arg = self.identifier_constant(name);
            (OpCode::GetGlobal(arg), OpCode::SetGlobal(arg))
        };
        if can_assign && self.maybe_consume(TokenType::Equal) {
            self.expression();
            self.emit_opcode(set_op);
        } else {
            self.emit_opcode(get_op);
        }
    }

    fn resolve_local(&mut self, state_idx: usize, name: &str) -> Option<StackSlotOffset> {
        if let Some((i, local)) = self.functions[state_idx]
            .locals
            .iter()
            .enumerate()
            .rev()
            .find(|(_, local)| local.name == name)
        {
            Some(match local.depth {
                Some(_) => StackSlotOffset::new(i),
                None => {
                    self.error("Can't read local variable in its own initializer.");
                    StackSlotOffset::error()
                }
            })
        } else {
            None
        }
    }

    fn add_upvalue(&mut self, func_state_index: usize, upvalue: CompiledUpValue) -> UpValueIndex {
        if let Some(index) = self.functions[func_state_index]
            .upvalues
            .iter()
            .enumerate()
            .find(|(_, uv)| upvalue == **uv)
            .map(|(i, _)| i)
        {
            UpValueIndex(index)
        } else if self.functions[func_state_index].upvalues.len() >= MAX_UPVALUES {
            self.error("Too many closure variables in function.");
            UpValueIndex(99999)
        } else {
            self.functions[func_state_index].upvalues.push(upvalue);
            UpValueIndex(self.functions[func_state_index].upvalues.len() - 1)
        }
    }

    fn resolve_upvalue(&mut self, state_index: usize, name: &str) -> Option<UpValueIndex> {
        if state_index == 0 {
            return None;
        }

        let enclosing = state_index - 1;
        if let Some(local) = self.resolve_local(enclosing, name) {
            self.functions[enclosing].local_at_mut(local).is_captured = true;
            Some(self.add_upvalue(state_index, CompiledUpValue::Local { index: local }))
        } else {
            self.resolve_upvalue(enclosing, name).map(|upvalue| {
                self.add_upvalue(state_index, CompiledUpValue::Nonlocal { index: upvalue })
            })
        }
    }

    fn emit_return(&mut self) {
        if self.current_function().function_type == FunctionType::Initializer {
            self.emit_opcode(OpCode::GetLocal(StackSlotOffset::special()));
        } else {
            self.emit_opcode(OpCode::Nil);
        }
        self.emit_opcode(OpCode::Return);
    }

    fn make_constant(&mut self, value: Value) -> ConstantIndex {
        match self
            .current_function_mut()
            .function
            .chunk
            .add_constant(value)
        {
            None => {
                self.error("Too many constants in one chunk.");
                ConstantIndex::error()
            }
            Some(idx) => idx,
        }
    }

    fn emit_constant(&mut self, value: Value) {
        let index = self.make_constant(value);
        self.emit_opcode(OpCode::Constant { index });
    }

    fn current_function(&self) -> &FunctionState<'source> {
        self.functions
            .last()
            .expect("function stack should not be empty")
    }

    fn current_function_mut(&mut self) -> &mut FunctionState<'source> {
        self.functions
            .last_mut()
            .expect("function stack should not be empty")
    }

    fn error_at_next(&mut self, message: &str) {
        let next = self.next_token();
        self.error_at(Some(next), message, next.line);
    }
    fn error(&mut self, message: &str) {
        let cur = self.current_token;
        self.error_at(Some(cur), message, cur.line)
    }
    fn error_at(&mut self, token: Option<Token>, message: &str, line: usize) {
        if self.panic_mode {
            return;
        }
        self.panic_mode = true;
        self.had_error = true;
        eprintln!(
            "[line {}] Error{}: {}",
            line,
            token.map_or_else(|| "".to_string(), |t| t.location()),
            message
        );
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }
}

fn get_rule<'source, I: Iterator<Item = Result<Token<'source>, ScanError>>>(
    ty: TokenType<'source>,
) -> Rule<'source, I> {
    match ty {
        TokenType::LeftParen => Rule::new(
            Some(|c, _ctx| c.grouping()),
            Some(InfixRule::new(|c, _ctx| c.call(), Precedence::Call)),
        ),
        TokenType::Dot => Rule::new(
            None,
            Some(InfixRule::new(
                |c, ctx| c.dot(ctx.can_assign),
                Precedence::Call,
            )),
        ),
        TokenType::Minus => Rule::new(
            Some(|c, _ctx| c.unary()),
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Term),
                Precedence::Term,
            )),
        ),
        TokenType::Plus => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Term),
                Precedence::Term,
            )),
        ),
        TokenType::Slash => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Factor),
                Precedence::Factor,
            )),
        ),
        TokenType::Star => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Factor),
                Precedence::Factor,
            )),
        ),
        TokenType::Bang => Rule::new(Some(|c, _ctx| c.unary()), None),
        TokenType::BangEqual => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Equality),
                Precedence::Equality,
            )),
        ),
        TokenType::EqualEqual => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Equality),
                Precedence::Equality,
            )),
        ),
        TokenType::Greater => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Comparison),
                Precedence::Comparison,
            )),
        ),
        TokenType::GreaterEqual => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Comparison),
                Precedence::Comparison,
            )),
        ),
        TokenType::Less => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Comparison),
                Precedence::Comparison,
            )),
        ),
        TokenType::LessEqual => Rule::new(
            None,
            Some(InfixRule::new(
                |c, _ctx| c.binary(Precedence::Comparison),
                Precedence::Comparison,
            )),
        ),
        TokenType::Identifier { .. } => Rule::new(
            Some(|c, ctx| c.variable(ctx.payload.as_string().unwrap(), ctx.can_assign)),
            None,
        ),
        TokenType::String { .. } => Rule::new(
            Some(|c, ctx| c.string(ctx.payload.as_string().unwrap())),
            None,
        ),
        TokenType::Number { .. } => Rule::new(
            Some(|c, ctx| c.number(*ctx.payload.as_double().unwrap().0)),
            None,
        ),
        TokenType::And => Rule::new(
            None,
            Some(InfixRule::new(|c, _ctx| c.and(), Precedence::And)),
        ),
        TokenType::False => Rule::new(Some(|c, _ctx| c.literal()), None),
        TokenType::Nil => Rule::new(Some(|c, _ctx| c.literal()), None),
        TokenType::Or => Rule::new(None, Some(InfixRule::new(|c, _ctx| c.or(), Precedence::Or))),
        TokenType::Super => Rule::new(Some(|c, _ctx| c.super_()), None),
        TokenType::This => Rule::new(Some(|c, _ctx| c.this()), None),
        TokenType::True => Rule::new(Some(|c, _ctx| c.literal()), None),
        _ => Rule::new(None, None),
    }
}

#[derive(PartialOrd, Ord, Eq, PartialEq)]
enum Precedence {
    Assignment,
    Or,
    And,
    Equality,
    Comparison,
    Term,
    Factor,
    Unary,
    Call,
    Primary,
}

impl Precedence {
    fn plus_one(&self) -> Self {
        use Precedence::*;
        match self {
            Assignment => Or,
            Or => And,
            And => Equality,
            Equality => Comparison,
            Comparison => Term,
            Term => Factor,
            Factor => Unary,
            Unary => Call,
            Call => Primary,
            Primary => Primary,
        }
    }
}

#[derive(Clone, Copy)]
struct ParseFnCtx<'source> {
    can_assign: bool,
    payload: TokenPayload<'source>,
}

type ParseFn<'source, I> =
    for<'compiler, 'opt, 'vm> fn(&'compiler mut Compiler<'opt, 'source, 'vm, I>, ParseFnCtx);

struct InfixRule<'source, I: Iterator<Item = Result<Token<'source>, ScanError>>> {
    parse: ParseFn<'source, I>,
    precedence: Precedence,
}

impl<'source, I: Iterator<Item = Result<Token<'source>, ScanError>>> InfixRule<'source, I> {
    fn new(parse: ParseFn<'source, I>, precedence: Precedence) -> Self {
        Self { parse, precedence }
    }
}

struct Rule<'source, I: Iterator<Item = Result<Token<'source>, ScanError>>> {
    prefix: Option<ParseFn<'source, I>>,
    infix: Option<InfixRule<'source, I>>,
}

impl<'source, I: Iterator<Item = Result<Token<'source>, ScanError>>> Rule<'source, I> {
    fn new(prefix: Option<ParseFn<'source, I>>, infix: Option<InfixRule<'source, I>>) -> Self {
        Self { prefix, infix }
    }
}

struct Local<'source> {
    name: &'source str,
    depth: Option<usize>,
    is_captured: bool,
}

impl<'source> Local<'source> {
    fn new(name: &'static str) -> Self {
        Self {
            name,
            depth: Some(0),
            is_captured: false,
        }
    }
}

#[derive(Eq, PartialEq)]
enum FunctionType {
    Function,
    Initializer,
    Method,
    Script,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CompiledUpValue {
    Local { index: StackSlotOffset },
    Nonlocal { index: UpValueIndex },
}
