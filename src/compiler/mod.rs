mod scanner;

pub fn compile(source: &str) -> Option<crate::chunk::Chunk> {
    let mut compiler = Compiler::new(scanner::Scanner::new(source));

    compiler.compile()
}

use crate::chunk::{Chunk, OpCode};
use scanner::{Token, TokenType};

struct Compiler<'a> {
    scanner: scanner::Scanner<'a>,
    current: Token<'a>,
    previous: Token<'a>,
    had_error: bool,
    panic_mode: bool,
}

impl<'a> Compiler<'a> {
    fn new(scanner: scanner::Scanner<'a>) -> Self {
        Self {
            scanner,
            current: Token::default(),
            previous: Token::default(),
            had_error: false,
            panic_mode: false,
        }
    }

    fn compile(&mut self) -> Option<crate::chunk::Chunk> {
        self.advance();
        self.expression();

        todo!()
    }

    fn advance(&mut self) -> Token<'a> {
        self.previous = self.current;
        loop {
            self.current = self.scanner.scan_token();
            if self.current.ty != TokenType::Error {
                return self.current;
            }

            self.error_at_current(self.current.lexeme);
        }
    }

    fn consume(&'a mut self, ty: TokenType, message: &str) {
        if self.current.ty == ty {
            self.advance();
            return;
        }

        self.error_at_current(message);
    }

    fn emit_opcode(&mut self, opcode: OpCode) {
        let chunk = self.current_chunk_mut();
        self.write_chunk(chunk, opcode, self.previous.line);
    }

    fn current_chunk_mut(&mut self) -> &'a mut Chunk {
        todo!()
    }

    fn write_chunk(&mut self, chunk: &mut Chunk, opcode: OpCode, line: usize) {
        todo!()
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

    fn expression(&mut self) {}
}
