mod scanner;

pub fn compile(source: &str) -> Option<crate::chunk::Chunk> {
    let mut parser = Parser::new(scanner::Scanner::new(source));

    parser.parse()
}

use scanner::{Token, TokenType};

struct Parser<'a> {
    scanner: scanner::Scanner<'a>,
    current: Token<'a>,
    previous: Token<'a>,
    had_error: bool,
    panic_mode: bool,
}

impl<'a> Parser<'a> {
    fn new(scanner: scanner::Scanner<'a>) -> Self {
        Parser {
            scanner,
            current: Token::default(),
            previous: Token::default(),
            had_error: false,
            panic_mode: false,
        }
    }

    fn parse(&mut self) -> Option<crate::chunk::Chunk> {
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
