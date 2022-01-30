pub(crate) struct Scanner<'source> {
    source: &'source [u8],
    current: usize,
    line: usize,
}

fn is_alphabetic(c: char) -> bool {
    ('a'..='z').contains(&c) || ('A'..='Z').contains(&c) || c == '_'
}

impl<'source> Scanner<'source> {
    pub(crate) fn new(source: &'source str) -> Self {
        Scanner {
            source: source.as_bytes(),
            // Starts at 0. The next byte to be consumed.
            current: 0,
            line: 1,
        }
    }

    fn matches(&mut self, expected: char) -> bool {
        if self.is_at_end() || self.source[self.current] as char != expected {
            false
        } else {
            self.source = &self.source[self.current + 1..];
            self.current = 0;
            true
        }
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
        if self.is_at_end() || self.current + 1 == self.source.len() {
            return '\0';
        }
        self.source[self.current + 1] as char
    }

    fn make_token(&self, ty: TokenType) -> Token<'source> {
        Token {
            ty,
            lexeme: std::str::from_utf8(&self.source[0..self.current]).unwrap(),
            line: self.line,
        }
    }

    fn error_token<'s: 'source>(&self, message: &'s str) -> ScanError<'s> {
        ScanError {
            message,
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
                '/' if self.peek_next() == '/' => {
                    while !self.is_at_end() && self.peek() != '\n' {
                        self.advance();
                    }
                }
                _ => {
                    return;
                }
            }
        }
    }

    fn identifier(&mut self) -> Token<'source> {
        while !self.is_at_end() && (is_alphabetic(self.peek()) || self.peek().is_digit(10)) {
            self.advance();
        }

        self.make_token(self.identifier_type())
    }

    fn number(&mut self) -> Token<'source> {
        while !self.is_at_end() && self.peek().is_digit(10) {
            self.advance();
        }

        if !self.is_at_end() && self.peek() == '.' && self.peek_next().is_digit(10) {
            self.advance();
            while !self.is_at_end() && self.peek().is_digit(10) {
                self.advance();
            }
        }
        self.make_token(TokenType::Number)
    }

    fn string(&mut self) -> Result<Token<'source>, ScanError<'source>> {
        while !self.is_at_end() && self.peek() != '"' {
            if self.peek() == '\n' {
                self.line += 1;
            }
            self.advance();
        }

        if self.is_at_end() {
            return Err(self.error_token("Unterminated string."));
        }

        self.advance();
        Ok(self.make_token(TokenType::String))
    }

    fn identifier_type(&self) -> TokenType {
        use TokenType::*;
        match std::str::from_utf8(&self.source[0..self.current]).unwrap() {
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

impl<'source> Iterator for Scanner<'source> {
    type Item = Result<Token<'source>, ScanError<'source>>;

    fn next(&mut self) -> Option<Self::Item> {
        use TokenType::*;
        self.skip_whitespace();

        self.source = &self.source[self.current..];
        self.current = 0;

        if self.is_at_end() {
            return Some(Ok(self.make_token(Eof)));
        }

        Some(match self.advance() {
            c if is_alphabetic(c) => Ok(self.identifier()),
            c if c.is_digit(10) => Ok(self.number()),
            '(' => Ok(self.make_token(LeftParen)),
            ')' => Ok(self.make_token(RightParen)),
            '{' => Ok(self.make_token(LeftBrace)),
            '}' => Ok(self.make_token(RightBrace)),
            ';' => Ok(self.make_token(Semicolon)),
            ',' => Ok(self.make_token(Comma)),
            '.' => Ok(self.make_token(Dot)),
            '-' => Ok(self.make_token(Minus)),
            '+' => Ok(self.make_token(Plus)),
            '/' => Ok(self.make_token(Slash)),
            '*' => Ok(self.make_token(Star)),
            '!' => {
                let t = if self.matches('=') { BangEqual } else { Bang };
                Ok(self.make_token(t))
            }
            '=' => {
                let t = if self.matches('=') { EqualEqual } else { Equal };
                Ok(self.make_token(t))
            }
            '<' => {
                let t = if self.matches('=') { LessEqual } else { Less };
                Ok(self.make_token(t))
            }
            '>' => {
                let t = if self.matches('=') {
                    GreaterEqual
                } else {
                    Greater
                };
                Ok(self.make_token(t))
            }
            '"' => self.string(),
            _ => Err(self.error_token("Unexpected character.")),
        })
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Token<'a> {
    pub(crate) ty: TokenType,
    pub(crate) lexeme: &'a str,
    pub(crate) line: usize,
}

impl<'source> Token<'source> {
    pub(crate) fn new(ty: TokenType, lexeme: &'static str) -> Self {
        Self {
            ty,
            lexeme,
            line: 0,
        }
    }
    pub(crate) fn eof() -> Self {
        Self {
            ty: TokenType::Eof,
            lexeme: "",
            line: 0,
        }
    }
}

#[derive(PartialEq, Copy, Clone)]
pub(crate) enum TokenType {
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

    Eof,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ScanError<'a> {
    pub(crate) message: &'a str,
    pub(crate) line: usize,
}