pub struct Scanner<'a> {
    source: &'a [u8],
    current: usize,
    line: usize,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Self {
        Scanner {
            source: source.as_bytes(),
            // Starts at 0. The next byte to be consumed.
            current: 0,
            line: 1,
        }
    }

    pub fn scan_token(&mut self) -> Token<'a> {
        use TokenType::*;
        self.skip_whitespace();

        self.source = &self.source[self.current..];
        self.current = 0;

        if self.is_at_end() {
            return self.make_token(Eof);
        }

        let c = self.advance();
        if c.is_alphabetic() {
            return self.identifier();
        }
        if c.is_digit(10) {
            return self.number();
        }
        match c {
            '(' => self.make_token(LeftParen),
            ')' => self.make_token(RightParen),
            '{' => self.make_token(LeftBrace),
            '}' => self.make_token(RightBrace),
            ';' => self.make_token(Semicolon),
            ',' => self.make_token(Comma),
            '.' => self.make_token(Dot),
            '-' => self.make_token(Minus),
            '+' => self.make_token(Plus),
            '/' => self.make_token(Slash),
            '*' => self.make_token(Star),
            '!' => {
                let t = if self.matches('=') { BangEqual } else { Bang };
                self.make_token(t)
            }
            '=' => {
                let t = if self.matches('=') { EqualEqual } else { Equal };
                self.make_token(t)
            }
            '<' => {
                let t = if self.matches('=') { LessEqual } else { Less };
                self.make_token(t)
            }
            '>' => {
                let t = if self.matches('=') {
                    GreaterEqual
                } else {
                    Greater
                };
                self.make_token(t)
            }
            '"' => self.string(),
            _ => {
                unreachable!();
            }
        }
    }

    fn matches(&mut self, expected: char) -> bool {
        if self.is_at_end() {
            return false;
        }
        if self.source[self.current] as char != expected {
            return false;
        }

        self.source = &self.source[self.current + 1..];
        self.current = 0;
        true
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.source.len()
    }

    fn advance(&mut self) -> char {
        self.current += 1;
        self.source[self.current - 1] as char
    }

    fn peek(&self) -> char {
        self.source[self.current] as char
    }

    fn peek_next(&self) -> char {
        if self.is_at_end() {
            return '\0';
        }
        self.source[self.current + 1] as char
    }

    fn make_token(&self, ty: TokenType) -> Token<'a> {
        Token {
            ty,
            lexeme: std::str::from_utf8(&self.source[0..self.current]).unwrap(),
            line: self.line,
        }
    }

    fn error_token<'s: 'a>(&self, message: &'s str) -> Token<'a> {
        Token {
            ty: TokenType::Error,
            lexeme: message,
            line: self.line,
        }
    }

    fn skip_whitespace(&mut self) {
        loop {
            if self.is_at_end() {
                return;
            }
            match self.peek() {
                ' ' | '\r' | '\t' => {
                    self.advance();
                }
                '\n' => {
                    self.line += 1;
                    self.advance();
                }
                '/' => {
                    if self.peek_next() == '/' {
                        while self.peek() != '\n' && !self.is_at_end() {
                            self.advance();
                        }
                    }
                }
                _ => {
                    return;
                }
            }
        }
    }

    fn identifier(&mut self) -> Token<'a> {
        while self.peek().is_alphabetic() || self.peek().is_digit(10) {
            self.advance();
        }
        let ty = self.identifier_type();
        self.make_token(ty)
    }

    fn number(&mut self) -> Token<'a> {
        while self.peek().is_digit(10) {
            self.advance();
        }

        if self.peek() == '.' && self.peek_next().is_digit(10) {
            self.advance();
            while self.peek().is_digit(10) {
                self.advance();
            }
        }
        self.make_token(TokenType::Number)
    }

    fn string(&mut self) -> Token<'a> {
        while self.peek() != '"' && !self.is_at_end() {
            if self.peek() == '\n' {
                self.line += 1;
            }
            self.advance();
        }

        if self.is_at_end() {
            return self.error_token("Unterminated string.");
        }

        self.advance();
        self.make_token(TokenType::String)
    }

    fn identifier_type(&self) -> TokenType {
        use TokenType::*;
        let ident = std::str::from_utf8(&self.source[0..self.current]).unwrap();
        match ident {
            "and" => And,
            "class" => Class,
            "else" => Else,
            "false" => False,
            "for" => For,
            "fun" => Fun,
            "if" => If,
            "nil" => Nil,
            "or" => Or,
            "print" => Print,
            "return" => Return,
            "super" => Super,
            "this" => This,
            "true" => True,
            "var" => Var,
            "while" => While,
            _ => Identifier,
        }
    }
}

#[derive(Debug, Default, Clone, Copy)]
pub struct Token<'a> {
    pub ty: TokenType,
    pub lexeme: &'a str,
    pub line: usize,
}

#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum TokenType {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    Identifier,
    String,
    Number,

    And,
    Class,
    Else,
    False,
    For,
    Fun,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,

    Error,
    Eof,
}

impl Default for TokenType {
    fn default() -> Self {
        TokenType::Eof
    }
}
