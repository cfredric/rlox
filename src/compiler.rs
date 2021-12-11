mod scanner;

use crate::chunk::{Chunk, OpCode};
use crate::obj::{Function, Obj};
use crate::table::Table;
use crate::value::Value;
use crate::Opt;
use scanner::{Token, TokenType};

pub(crate) struct Compiler<'opt, 'source, 'vm> {
    opt: &'opt Opt,
    scanner: scanner::Scanner<'source>,
    current: Token<'source>,
    previous: Token<'source>,
    had_error: bool,
    panic_mode: bool,

    heap: &'vm mut Vec<Obj>,

    strings: &'vm mut Table<usize>,
    functions: Vec<FunctionState<'source>>,
}

#[derive(Debug)]
struct FunctionState<'source> {
    function: Function,
    function_type: FunctionType,

    locals: Vec<Local<'source>>,
    scope_depth: isize,
}

impl<'source> FunctionState<'source> {
    fn new(function_type: FunctionType) -> Self {
        Self::with_name(function_type, "")
    }
    fn with_name(function_type: FunctionType, name: &str) -> Self {
        Self {
            function: Function::new(name),
            function_type,
            locals: Vec::new(),
            scope_depth: 0,
        }
    }
}

impl<'opt, 'source, 'vm> Compiler<'opt, 'source, 'vm> {
    pub fn new(
        opt: &'opt Opt,
        source: &'source str,
        heap: &'vm mut Vec<Obj>,
        function_type: FunctionType,
        strings: &'vm mut Table<usize>,
    ) -> Self {
        Self {
            opt,
            scanner: scanner::Scanner::new(source),
            current: Token::default(),
            previous: Token::default(),
            had_error: false,
            panic_mode: false,
            heap,
            strings,
            functions: vec![FunctionState::with_name(function_type, "script")],
        }
    }

    pub fn compile(mut self) -> Option<Function> {
        self.advance();

        while !self.matches(TokenType::Eof) {
            self.declaration();
        }

        self.consume(TokenType::Eof, "Expect end of expression");
        let f = self.end_compiler();
        if !self.had_error {
            f
        } else {
            None
        }
    }

    fn advance(&mut self) -> Token<'source> {
        self.previous = self.current;
        loop {
            self.current = self.scanner.scan_token();
            if self.current.ty != TokenType::Error {
                return self.current;
            }

            self.error_at_current(self.current.lexeme);
        }
    }

    fn consume<'s: 'source>(&mut self, ty: TokenType, message: &'s str) {
        if self.current.ty == ty {
            self.advance();
            return;
        }

        self.error_at_current(message);
    }

    fn matches(&mut self, ty: TokenType) -> bool {
        if !self.check(ty) {
            return false;
        }
        self.advance();
        true
    }

    fn check(&self, ty: TokenType) -> bool {
        self.current.ty == ty
    }

    fn emit_opcodes(&mut self, a: OpCode, b: OpCode) {
        self.emit_opcode(a);
        self.emit_opcode(b);
    }

    fn emit_jump(&mut self, opcode: OpCode) -> usize {
        self.emit_opcode(opcode);
        self.current_chunk().code.len() - 1
    }

    fn patch_jump(&mut self, jump_index: usize) {
        let distance = self.current_chunk().code.len() - jump_index - 1;
        match self.current_chunk().code[jump_index] {
            OpCode::JumpIfFalse(_) => {
                self.current_chunk_mut().code[jump_index] = OpCode::JumpIfFalse(distance);
            }
            OpCode::Jump(_) => {
                self.current_chunk_mut().code[jump_index] = OpCode::Jump(distance);
            }
            _ => unreachable!(),
        }
    }

    fn emit_loop(&mut self, loop_start: usize) {
        let distance = self.current_chunk().code.len() - loop_start + 1;
        self.emit_opcode(OpCode::Loop(distance));
    }

    fn emit_opcode(&mut self, opcode: OpCode) {
        let line = self.previous.line;
        self.current_chunk_mut().write_chunk(opcode, line);
    }

    fn end_compiler(&mut self) -> Option<Function> {
        self.emit_return();

        if self.opt.print_code && !self.had_error {
            self.current_chunk()
                .disassemble_chunk(&self.function_state().function.name, self.heap);
        }
        if self.had_error {
            return None;
        }
        Some(self.functions.pop().unwrap().function)
    }

    fn synchronize(&mut self) {
        self.panic_mode = false;

        while self.current.ty != TokenType::Eof {
            if self.previous.ty == TokenType::Semicolon {
                return;
            }
            use TokenType::*;
            match self.current.ty {
                Class | Fun | Var | For | If | While | Print | Return => {
                    return;
                }
                _ => {}
            }
            self.advance();
        }
    }

    fn declaration(&mut self) {
        if self.matches(TokenType::Fun) {
            self.fun_declaration();
        } else if self.matches(TokenType::Var) {
            self.var_declaration();
        } else {
            self.statement();
        }

        if self.panic_mode {
            self.synchronize();
        }
    }

    fn fun_declaration(&mut self) {
        let global = self.parse_variable("Expect function name.");
        self.mark_initialized();
        self.function(FunctionType::Function);
        self.define_variable(global);
    }

    fn var_declaration(&mut self) {
        let global = self.parse_variable("Expect variable name.");

        if self.matches(TokenType::Equal) {
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
        if self.matches(TokenType::Print) {
            self.print_statement();
        } else if self.matches(TokenType::For) {
            self.for_statement();
        } else if self.matches(TokenType::If) {
            self.if_statement();
        } else if self.matches(TokenType::Return) {
            self.return_statement();
        } else if self.matches(TokenType::While) {
            self.while_statement();
        } else if self.matches(TokenType::LeftBrace) {
            self.begin_scope();
            self.block();
            self.end_scope();
        } else {
            self.expression_statement();
        }
    }

    fn for_statement(&mut self) {
        self.begin_scope();
        self.consume(TokenType::LeftParen, "Expect '(' after 'for'.");
        if self.matches(TokenType::Semicolon) {
            // No initializer.
        } else if self.matches(TokenType::Var) {
            self.var_declaration();
        } else {
            self.expression_statement();
        }

        let mut loop_start = self.current_chunk().code.len();
        let mut exit_jump = None;
        if !self.matches(TokenType::Semicolon) {
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after loop condition.");

            exit_jump = Some(self.emit_jump(OpCode::JumpIfFalse(0)));
            self.emit_opcode(OpCode::Pop);
        }

        if !self.matches(TokenType::RightParen) {
            let body_jump = self.emit_jump(OpCode::Jump(0));
            let increment_start = self.current_chunk().code.len();
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

        self.end_scope();
    }

    fn if_statement(&mut self) {
        self.consume(TokenType::LeftParen, "Expect '(' after 'if'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");

        let then_jump = self.emit_jump(OpCode::JumpIfFalse(0));
        self.emit_opcode(OpCode::Pop);
        self.statement();
        let else_jump = self.emit_jump(OpCode::Jump(0));
        self.patch_jump(then_jump);
        self.emit_opcode(OpCode::Pop);
        if self.matches(TokenType::Else) {
            self.statement();
        }
        self.patch_jump(else_jump);
    }

    fn while_statement(&mut self) {
        let loop_start = self.current_chunk().code.len();
        self.consume(TokenType::LeftParen, "Expect '(' after 'while'.");
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after condition.");

        let exit_jump = self.emit_jump(OpCode::JumpIfFalse(0));
        self.emit_opcode(OpCode::Pop);
        self.statement();
        self.emit_loop(loop_start);

        self.patch_jump(exit_jump);
        self.emit_opcode(OpCode::Pop);
    }

    fn block(&mut self) {
        while !self.check(TokenType::RightBrace) && !self.check(TokenType::Eof) {
            self.declaration();
        }

        self.consume(TokenType::RightBrace, "Expect '}' after block.");
    }

    fn function(&mut self, ty: FunctionType) {
        self.functions.push(if ty == FunctionType::Script {
            FunctionState::new(ty)
        } else {
            FunctionState::with_name(ty, self.previous.lexeme)
        });
        self.begin_scope();

        self.consume(TokenType::LeftParen, "Expect '(' after function name.");
        if !self.check(TokenType::RightParen) {
            loop {
                self.function_state_mut().function.arity += 1;
                if self.function_state().function.arity > 255 {
                    self.error_at_current("Can't have more than 255 parameters.");
                }
                let constant = self.parse_variable("Expect parameter name.");
                self.define_variable(constant);

                if !self.matches(TokenType::Comma) {
                    break;
                }
            }
        }
        self.consume(TokenType::RightParen, "Expect ')' after parameters.");
        self.consume(TokenType::LeftBrace, "Expect '{' before function body.");
        self.block();

        let function = self.end_compiler().unwrap();
        let heap_index = Obj::allocate_object(self.heap, Obj::Function(function));
        self.emit_constant(Value::ObjIndex(heap_index));
    }

    fn begin_scope(&mut self) {
        self.function_state_mut().scope_depth += 1;
    }

    fn end_scope(&mut self) {
        self.function_state_mut().scope_depth -= 1;

        while matches!(self.function_state().locals.last(), Some(local) if local.depth > self.function_state().scope_depth)
        {
            self.emit_opcode(OpCode::Pop);
            self.function_state_mut().locals.pop();
        }
    }

    fn print_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after value.");
        self.emit_opcode(OpCode::Print);
    }

    fn return_statement(&mut self) {
        if self.function_state().function_type == FunctionType::Script {
            self.error("Can't return from top-level code.");
        }
        if self.matches(TokenType::Semicolon) {
            self.emit_return();
        } else {
            self.expression();
            self.consume(TokenType::Semicolon, "Expect ';' after return value.");
            self.emit_opcode(OpCode::Return);
        }
    }

    fn expression_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after expression.");
        self.emit_opcode(OpCode::Pop);
    }

    fn grouping(&mut self) {
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after expression.");
    }

    fn number(&mut self) {
        let value = self.previous.lexeme.parse::<f64>().unwrap();
        self.emit_constant(Value::Double(value));
    }

    fn string(&mut self) {
        let len = self.previous.lexeme.len();
        let index = Obj::copy_string(
            &mut self.heap,
            &mut self.strings,
            &self.previous.lexeme[1..len - 1],
        );
        self.emit_constant(Value::ObjIndex(index));
    }

    fn unary(&mut self) {
        let op_ty = self.previous.ty;
        self.parse_precedence(Precedence::Unary);
        match op_ty {
            TokenType::Minus => self.emit_opcode(OpCode::Negate),
            TokenType::Bang => self.emit_opcode(OpCode::Not),
            _ => unreachable!(),
        }
    }

    fn binary(&mut self) {
        let ty = self.previous.ty;
        let rule = get_rule(ty);
        self.parse_precedence(rule.precedence.plus_one());

        match ty {
            TokenType::BangEqual => self.emit_opcodes(OpCode::Equal, OpCode::Not),
            TokenType::EqualEqual => self.emit_opcode(OpCode::Equal),
            TokenType::Greater => self.emit_opcode(OpCode::Equal),
            TokenType::GreaterEqual => self.emit_opcodes(OpCode::Not, OpCode::Less),
            TokenType::Less => self.emit_opcode(OpCode::Less),
            TokenType::LessEqual => self.emit_opcodes(OpCode::Not, OpCode::Greater),
            TokenType::Plus => self.emit_opcode(OpCode::Add),
            TokenType::Minus => self.emit_opcode(OpCode::Subtract),
            TokenType::Star => self.emit_opcode(OpCode::Multiply),
            TokenType::Slash => self.emit_opcode(OpCode::Divide),
            _ => {}
        }
    }

    fn call(&mut self) {
        let arg_count = self.argument_list();
        self.emit_opcode(OpCode::Call(arg_count));
    }

    fn literal(&mut self) {
        match self.previous.ty {
            TokenType::False => self.emit_opcode(OpCode::Bool(false)),
            TokenType::Nil => self.emit_opcode(OpCode::Nil),
            TokenType::True => self.emit_opcode(OpCode::Bool(true)),
            _ => unreachable!(),
        }
    }

    fn parse_precedence(&mut self, prec: Precedence) {
        self.advance();
        let prefix = get_rule(self.previous.ty).prefix;
        let can_assign = prec <= Precedence::Assignment;
        match prefix {
            Some(f) => f(self, ParseFnCtx { can_assign }),
            None => {
                self.error("Expect expression.");
                return;
            }
        }

        while prec <= get_rule(self.current.ty).precedence {
            self.advance();
            let infix = get_rule(self.previous.ty).infix;
            infix.unwrap()(self, ParseFnCtx { can_assign });
        }

        if can_assign && self.matches(TokenType::Equal) {
            self.error("Invalid assignment target.");
        }
    }

    fn parse_variable<'e: 'source>(&mut self, error_message: &'e str) -> usize {
        self.consume(TokenType::Identifier, error_message);
        self.declare_variable();
        if self.function_state().scope_depth > 0 {
            return 0;
        }
        let name = self.previous.lexeme;
        self.identifier_constant(name)
    }

    fn identifier_constant(&mut self, name: &str) -> usize {
        let idx = Obj::copy_string(self.heap, self.strings, name);
        self.make_constant(Value::ObjIndex(idx))
    }

    fn identifiers_equal(&self, a: Token<'source>, b: Token<'source>) -> bool {
        a.lexeme == b.lexeme
    }

    fn define_variable(&mut self, global: usize) {
        if self.function_state().scope_depth > 0 {
            self.mark_initialized();
            return;
        }
        self.emit_opcode(OpCode::DefineGlobal(global))
    }

    fn argument_list(&mut self) -> usize {
        let mut arg_count = 0;
        if !self.check(TokenType::RightParen) {
            loop {
                self.expression();
                if arg_count == 255 {
                    self.error("Can't have more than 255 arguments.");
                }
                arg_count += 1;

                if !self.matches(TokenType::Comma) {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen, "Expect ')' after arguments.");
        arg_count
    }

    fn and(&mut self) {
        let end_jump = self.emit_jump(OpCode::JumpIfFalse(0));
        self.emit_opcode(OpCode::Pop);
        self.parse_precedence(Precedence::And);
        self.patch_jump(end_jump);
    }

    fn or(&mut self) {
        let else_jump = self.emit_jump(OpCode::JumpIfFalse(0));
        let end_jump = self.emit_jump(OpCode::Jump(0));

        self.patch_jump(else_jump);
        self.emit_opcode(OpCode::Pop);

        self.parse_precedence(Precedence::Or);
        self.patch_jump(end_jump);
    }

    fn mark_initialized(&mut self) {
        if self.function_state().scope_depth == 0 {
            return;
        }
        self.function_state_mut().locals.last_mut().unwrap().depth =
            self.function_state().scope_depth;
    }

    fn declare_variable(&mut self) {
        if self.function_state().scope_depth == 0 {
            return;
        }
        let name = self.previous;
        // TODO: don't clone here.
        for local in self.function_state().locals.clone().iter().rev() {
            if local.depth != -1 && local.depth < self.function_state().scope_depth {
                break;
            }
            if self.identifiers_equal(name, local.name) {
                self.error("Already a variable with this name in this scope.");
            }
        }
        self.add_local(name);
    }

    fn add_local(&mut self, name: Token<'source>) {
        if self.function_state().locals.len() > 256 {
            self.error("Too many local variables in function.");
            return;
        }
        self.function_state_mut()
            .locals
            .push(Local { name, depth: -1 });
    }

    fn variable(&mut self, can_assign: bool) {
        self.named_variable(self.previous.lexeme, can_assign)
    }

    fn named_variable(&mut self, name: &str, can_assign: bool) {
        let arg = self.resolve_local(name);
        let (get_op, set_op) = if arg != -1 {
            (
                OpCode::GetLocal(arg as usize),
                OpCode::SetLocal(arg as usize),
            )
        } else {
            let arg = self.identifier_constant(name);
            (OpCode::GetGlobal(arg), OpCode::SetGlobal(arg))
        };
        if can_assign && self.matches(TokenType::Equal) {
            self.expression();
            self.emit_opcode(set_op);
        } else {
            self.emit_opcode(get_op);
        }
    }

    fn resolve_local(&mut self, name: &str) -> isize {
        for (i, local) in self.function_state().locals.iter().enumerate().rev() {
            if local.name.lexeme == name && local.depth != -1 {
                return i as isize;
            }
        }
        -1
    }

    fn emit_return(&mut self) {
        self.emit_opcode(OpCode::Nil);
        self.emit_opcode(OpCode::Return);
    }

    fn make_constant(&mut self, value: Value) -> usize {
        self.current_chunk_mut().add_constant(value)
    }

    fn emit_constant(&mut self, value: Value) {
        let idx = self.make_constant(value);
        self.emit_opcode(OpCode::Constant(idx));
    }

    fn current_chunk_mut(&mut self) -> &mut Chunk {
        &mut self.function_state_mut().function.chunk
    }

    fn current_chunk(&self) -> &Chunk {
        &self.function_state().function.chunk
    }

    fn function_state(&self) -> &FunctionState<'source> {
        self.functions.last().unwrap()
    }

    fn function_state_mut(&mut self) -> &mut FunctionState<'source> {
        self.functions.last_mut().unwrap()
    }

    fn error_at_current(&mut self, message: &str) {
        let cur = self.current;
        self.error_at(&cur, message);
    }
    fn error(&mut self, message: &str) {
        let prev = self.previous;
        self.error_at(&prev, message)
    }
    fn error_at(&mut self, token: &Token, message: &str) {
        if self.panic_mode {
            return;
        }
        eprint!("[line {}] Error", token.line);
        match token.ty {
            scanner::TokenType::Eof => eprint!(" at end"),
            scanner::TokenType::Error => {}
            _ => eprint!(" at {}", token.lexeme),
        }

        eprintln!(": {}", message);
        self.had_error = true;
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }
}

fn get_rule(ty: TokenType) -> Rule {
    match ty {
        TokenType::LeftParen => Rule::new(
            Some(|c, _ctx| c.grouping()),
            Some(|c, _ctx| c.call()),
            Precedence::Call,
        ),
        TokenType::RightParen => Rule::new(None, None, Precedence::None),
        TokenType::LeftBrace => Rule::new(None, None, Precedence::None),
        TokenType::RightBrace => Rule::new(None, None, Precedence::None),
        TokenType::Comma => Rule::new(None, None, Precedence::None),
        TokenType::Dot => Rule::new(None, None, Precedence::None),
        TokenType::Minus => Rule::new(
            Some(|c, _ctx| c.unary()),
            Some(|c, _ctx| c.binary()),
            Precedence::Term,
        ),
        TokenType::Plus => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Term),
        TokenType::Semicolon => Rule::new(None, None, Precedence::None),
        TokenType::Slash => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Factor),
        TokenType::Star => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Factor),
        TokenType::Bang => Rule::new(Some(|c, _ctx| c.unary()), None, Precedence::None),
        TokenType::BangEqual => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Equality),
        TokenType::Equal => Rule::new(None, None, Precedence::None),
        TokenType::EqualEqual => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Equality),
        TokenType::Greater => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Comparison),
        TokenType::GreaterEqual => {
            Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Comparison)
        }
        TokenType::Less => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Comparison),
        TokenType::LessEqual => Rule::new(None, Some(|c, _ctx| c.binary()), Precedence::Comparison),
        TokenType::Identifier => Rule::new(
            Some(|c, ctx| c.variable(ctx.can_assign)),
            None,
            Precedence::None,
        ),
        TokenType::String => Rule::new(Some(|c, _ctx| c.string()), None, Precedence::None),
        TokenType::Number => Rule::new(Some(|c, _ctx| c.number()), None, Precedence::None),
        TokenType::And => Rule::new(None, Some(|c, _ctx| c.and()), Precedence::And),
        TokenType::Class => Rule::new(None, None, Precedence::None),
        TokenType::Else => Rule::new(None, None, Precedence::None),
        TokenType::False => Rule::new(Some(|c, _ctx| c.literal()), None, Precedence::None),
        TokenType::For => Rule::new(None, None, Precedence::None),
        TokenType::If => Rule::new(None, None, Precedence::None),
        TokenType::Nil => Rule::new(Some(|c, _ctx| c.literal()), None, Precedence::None),
        TokenType::Or => Rule::new(None, Some(|c, _ctx| c.or()), Precedence::Or),
        TokenType::Print => Rule::new(None, None, Precedence::None),
        TokenType::Return => Rule::new(None, None, Precedence::None),
        TokenType::Super => Rule::new(None, None, Precedence::None),
        TokenType::This => Rule::new(None, None, Precedence::None),
        TokenType::True => Rule::new(Some(|c, _ctx| c.literal()), None, Precedence::None),
        TokenType::Var => Rule::new(None, None, Precedence::None),
        TokenType::While => Rule::new(None, None, Precedence::None),
        TokenType::Error => Rule::new(None, None, Precedence::None),
        TokenType::Fun => Rule::new(None, None, Precedence::None),
        TokenType::Eof => Rule::new(None, None, Precedence::None),
    }
}

#[derive(PartialOrd, Ord, Eq, PartialEq)]
enum Precedence {
    None,
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
            None => Assignment,
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

#[derive(Copy, Clone)]
struct ParseFnCtx {
    can_assign: bool,
}

type ParseFn = Option<
    for<'compiler, 'opt, 'source, 'vm> fn(&'compiler mut Compiler<'opt, 'source, 'vm>, ParseFnCtx),
>;

struct Rule {
    prefix: ParseFn,
    infix: ParseFn,
    precedence: Precedence,
}

impl Rule {
    fn new(prefix: ParseFn, infix: ParseFn, precedence: Precedence) -> Self {
        Self {
            prefix,
            infix,
            precedence,
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct Local<'source> {
    name: Token<'source>,
    depth: isize,
}

#[derive(Debug, Eq, PartialEq)]
pub enum FunctionType {
    Function,
    Script,
}
