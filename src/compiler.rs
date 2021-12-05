mod scanner;

use crate::chunk::{Chunk, OpCode};
use crate::obj::Obj;
use crate::table::Table;
use crate::value::Value;
use scanner::{Token, TokenType};

pub struct Compiler<'source, 'vm> {
    print_code: bool,
    scanner: scanner::Scanner<'source>,
    current: Token<'source>,
    previous: Token<'source>,
    had_error: bool,
    panic_mode: bool,

    compiling_chunk: &'vm mut Chunk,

    heap: &'vm mut Vec<Obj>,

    strings: &'vm mut Table,
}

impl<'source, 'vm> Compiler<'source, 'vm> {
    pub fn new(
        print_code: bool,
        source: &'source str,
        chunk: &'vm mut Chunk,
        heap: &'vm mut Vec<Obj>,
        strings: &'vm mut Table,
    ) -> Self {
        Self {
            print_code,
            scanner: scanner::Scanner::new(source),
            current: Token::default(),
            previous: Token::default(),
            had_error: false,
            panic_mode: false,
            compiling_chunk: chunk,
            heap,
            strings,
        }
    }

    pub fn compile(mut self) -> bool {
        self.advance();

        while !self.matches(TokenType::Eof) {
            self.declaration();
        }

        self.consume(TokenType::Eof, "Expect end of expression");
        self.end_compiler();
        !self.had_error
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

    fn emit_opcode(&mut self, opcode: OpCode) {
        let line = self.previous.line;
        self.current_chunk_mut().write_chunk(opcode, line);
    }

    fn end_compiler(&mut self) {
        self.emit_return();

        if self.print_code && !self.had_error {
            self.current_chunk().disassemble_chunk("code", self.heap);
        }
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
        if self.matches(TokenType::Var) {
            self.var_declaration();
        } else {
            self.statement();
        }

        if self.panic_mode {
            self.synchronize();
        }
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
        } else {
            self.expression_statement();
        }
    }

    fn print_statement(&mut self) {
        self.expression();
        self.consume(TokenType::Semicolon, "Expect ';' after value.");
        self.emit_opcode(OpCode::Print);
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
        let value = Obj::copy_string(
            &mut self.heap,
            &mut self.strings,
            &self.previous.lexeme[1..len - 1],
        );
        self.emit_constant(value);
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
        let name = self.previous.lexeme;
        self.identifier_constant(name)
    }

    fn identifier_constant(&mut self, name: &str) -> usize {
        let idx = Obj::copy_string(self.heap, self.strings, name);
        self.make_constant(idx)
    }

    fn define_variable(&mut self, global: usize) {
        self.emit_opcode(OpCode::DefineGlobal(global))
    }

    fn variable(&mut self, can_assign: bool) {
        self.named_variable(self.previous.lexeme, can_assign)
    }

    fn named_variable(&mut self, name: &str, can_assign: bool) {
        let arg = self.identifier_constant(name);
        if can_assign && self.matches(TokenType::Equal) {
            self.expression();
            self.emit_opcode(OpCode::SetGlobal(arg));
        } else {
            self.emit_opcode(OpCode::GetGlobal(arg));
        }
    }

    fn emit_return(&mut self) {
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
        &mut self.compiling_chunk
    }

    fn current_chunk(&self) -> &Chunk {
        self.compiling_chunk
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

        eprint!(": {}", message);
        self.had_error = true;
    }

    fn expression(&mut self) {
        self.parse_precedence(Precedence::Assignment);
    }
}

fn get_rule(ty: TokenType) -> Rule {
    match ty {
        TokenType::LeftParen => Rule::new(Some(|c, _ctx| c.grouping()), None, Precedence::None),
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
        TokenType::And => Rule::new(None, None, Precedence::None),
        TokenType::Class => Rule::new(None, None, Precedence::None),
        TokenType::Else => Rule::new(None, None, Precedence::None),
        TokenType::False => Rule::new(Some(|c, _ctx| c.literal()), None, Precedence::None),
        TokenType::For => Rule::new(None, None, Precedence::None),
        TokenType::If => Rule::new(None, None, Precedence::None),
        TokenType::Nil => Rule::new(Some(|c, _ctx| c.literal()), None, Precedence::None),
        TokenType::Or => Rule::new(None, None, Precedence::None),
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

type ParseFn = Option<for<'c, 'source, 'vm> fn(&'c mut Compiler<'source, 'vm>, ParseFnCtx)>;

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
