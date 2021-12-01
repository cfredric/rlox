use lazy_static::lazy_static;
use std::collections::HashMap;

mod scanner;

pub fn compile(source: &str) -> Option<crate::chunk::Chunk> {
    let compiler = Compiler::new(scanner::Scanner::new(source));

    compiler.compile()
}

use crate::chunk::{Chunk, OpCode};
use crate::common::DEBUG_PRINT_CODE;
use crate::value::Value;
use scanner::{Token, TokenType};

struct Compiler<'source> {
    scanner: scanner::Scanner<'source>,
    current: Token<'source>,
    previous: Token<'source>,
    had_error: bool,
    panic_mode: bool,

    compiling_chunk: Chunk,
}

impl<'source> Compiler<'source> {
    fn new(scanner: scanner::Scanner<'source>) -> Self {
        Self {
            scanner,
            current: Token::default(),
            previous: Token::default(),
            had_error: false,
            panic_mode: false,
            compiling_chunk: Chunk::default(),
        }
    }

    fn compile(mut self) -> Option<crate::chunk::Chunk> {
        self.advance();
        self.expression();

        self.consume(TokenType::Eof, "Expect end of expression");
        self.end_compiler();
        if self.had_error {
            None
        } else {
            Some(self.compiling_chunk)
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

    fn emit_opcode(&mut self, opcode: OpCode) {
        let line = self.previous.line;
        self.current_chunk_mut().write_chunk(opcode, line);
    }

    fn end_compiler(&mut self) {
        self.emit_return();

        if DEBUG_PRINT_CODE && !self.had_error {
            self.current_chunk_mut().disassemble_chunk("code");
        }
    }

    fn grouping(&mut self) {
        self.expression();
        self.consume(TokenType::RightParen, "Expect ')' after expression.");
    }

    fn number(&mut self) {
        let value = self.previous.lexeme.parse::<f64>().unwrap();
        self.emit_constant(value);
    }

    fn unary(&mut self) {
        let op_ty = self.previous.ty;
        self.parse_precedence(Precedence::Unary);
        match op_ty {
            TokenType::Minus => self.emit_opcode(OpCode::Negate),
            _ => unreachable!(),
        }
    }

    fn binary(&mut self) {
        let ty = self.previous.ty;
        let rule = get_rule(ty);
        self.parse_precedence(rule.precedence.plus_one());

        match ty {
            TokenType::Plus => self.emit_opcode(OpCode::Add),
            TokenType::Minus => self.emit_opcode(OpCode::Subtract),
            TokenType::Star => self.emit_opcode(OpCode::Multiply),
            TokenType::Slash => self.emit_opcode(OpCode::Divide),
            _ => {}
        }
    }

    fn parse_precedence(&mut self, prec: Precedence) {
        self.advance();
        let prefix = get_rule(self.previous.ty).prefix;
        match prefix {
            Some(f) => f(self),
            None => {
                self.error("Expect expression.");
                return;
            }
        }

        while prec <= get_rule(self.current.ty).precedence {
            self.advance();
            let infix = get_rule(self.previous.ty).infix;
            infix.unwrap()(self);
        }
    }

    fn emit_return(&mut self) {
        self.emit_opcode(OpCode::Return);
    }

    fn make_constant(&mut self, value: Value) -> usize {
        self.current_chunk_mut().add_constant(value)
    }

    fn emit_constant(&mut self, value: f64) {
        let idx = self.make_constant(Value::Double(value));
        self.emit_opcode(OpCode::Constant(idx));
    }

    fn current_chunk_mut(&mut self) -> &mut Chunk {
        &mut self.compiling_chunk
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

// TODO: extract this to a giant match statement instead of a hashmap.
lazy_static! {
    static ref RULES: HashMap<TokenType, Rule> = HashMap::from([
        (
            TokenType::LeftParen,
            Rule::new(Some(|c| c.grouping()), None, Precedence::None)
        ),
        empty(TokenType::RightParen),
        empty(TokenType::LeftBrace),
        empty(TokenType::RightBrace),
        empty(TokenType::Comma),
        empty(TokenType::Dot),
        (
            TokenType::Minus,
            Rule::new(Some(|c| c.unary()), Some(|c| c.binary()), Precedence::Term)
        ),
        (
            TokenType::Plus,
            Rule::new(None, Some(|c| c.binary()), Precedence::Term)
        ),
        empty(TokenType::Semicolon),
        (
            TokenType::Slash,
            Rule::new(None, Some(|c| c.binary()), Precedence::Factor)
        ),
        (
            TokenType::Star,
            Rule::new(None, Some(|c| c.binary()), Precedence::Factor)
        ),
        empty(TokenType::Bang),
        empty(TokenType::BangEqual),
        empty(TokenType::Equal),
        empty(TokenType::EqualEqual),
        empty(TokenType::Greater),
        empty(TokenType::GreaterEqual),
        empty(TokenType::Less),
        empty(TokenType::LessEqual),
        empty(TokenType::Identifier),
        empty(TokenType::String),
        (
            TokenType::Number,
            Rule::new(Some(|c| c.number()), None, Precedence::None)
        ),
        empty(TokenType::And),
        empty(TokenType::Class),
        empty(TokenType::Else),
        empty(TokenType::False),
        empty(TokenType::For),
        empty(TokenType::If),
        empty(TokenType::Nil),
        empty(TokenType::Or),
        empty(TokenType::Print),
        empty(TokenType::Return),
        empty(TokenType::Super),
        empty(TokenType::This),
        empty(TokenType::Var),
        empty(TokenType::While),
        empty(TokenType::Error),
        empty(TokenType::Eof),
    ]);
}

fn get_rule(ty: TokenType) -> &'static Rule {
    &RULES[&ty]
}

fn empty(ty: TokenType) -> (TokenType, Rule) {
    (ty, Rule::new(None, None, Precedence::None))
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

type ParseFn = Option<for<'c, 'source> fn(&'c mut Compiler<'source>)>;

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
