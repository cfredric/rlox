pub(crate) struct Scanner<'source> {
    source: &'source [u8],
    current: usize,
    line: usize,
}

fn is_alphabetic(c: char) -> bool {
    ('a'..='z').contains(&c) || ('A'..='Z').contains(&c) || c == '_'
}

fn is_numeric(c: char) -> bool {
    c.is_digit(10)
}

fn is_alphanumeric(c: char) -> bool {
    is_alphabetic(c) || is_numeric(c)
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

    fn maybe_consume(&mut self, expected: char) -> bool {
        if self.peek().map_or(false, |c| c == expected) {
            self.source = &self.source[self.current + 1..];
            self.current = 0;
            true
        } else {
            false
        }
    }

    fn peek(&self) -> Option<char> {
        self.source.get(self.current).map(|x| *x as char)
    }

    fn peek_next(&self) -> Option<char> {
        self.source.get(self.current + 1).map(|x| *x as char)
    }

    fn make_token(&self, ty: TokenType) -> Token<'source> {
        Token {
            ty,
            lexeme: std::str::from_utf8(&self.source[0..self.current]).unwrap(),
            line: self.line,
        }
    }

    fn error(&self, message: &'static str) -> ScanError {
        ScanError {
            message,
            line: self.line,
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            match c {
                ' ' | '\r' | '\t' => {
                    self.current += 1;
                }
                '\n' => {
                    self.line += 1;
                    self.current += 1;
                }
                '/' if matches!(self.peek_next(), Some('/')) => {
                    while self.peek().map_or(false, |c| c != '\n') {
                        self.current += 1;
                    }
                }
                _ => {
                    return;
                }
            }
        }
    }

    fn identifier(&mut self) -> Token<'source> {
        while self.peek().map_or(false, is_alphanumeric) {
            self.current += 1;
        }

        self.make_token(self.identifier_type())
    }

    fn number(&mut self) -> Token<'source> {
        while self.peek().map_or(false, is_numeric) {
            self.current += 1;
        }

        if self.peek().map_or(false, |c| c == '.') && self.peek_next().map_or(false, is_numeric) {
            self.current += 1;
            while self.peek().map_or(false, is_numeric) {
                self.current += 1;
            }
        }
        self.make_token(TokenType::Number)
    }

    fn string(&mut self) -> Result<Token<'source>, ScanError> {
        loop {
            match self.peek() {
                Some('"') => {
                    self.current += 1;
                    return Ok(self.make_token(TokenType::String));
                }
                Some(c) => {
                    if c == '\n' {
                        self.line += 1;
                    }
                    self.current += 1;
                }
                None => {
                    return Err(self.error("Unterminated string."));
                }
            }
        }
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
    type Item = Result<Token<'source>, ScanError>;

    fn next(&mut self) -> Option<Self::Item> {
        use TokenType::*;
        self.skip_whitespace();

        self.source = &self.source[self.current..];
        self.current = 0;

        let next_char = match self.peek() {
            Some(c) => c,
            None => {
                return Some(Ok(Token::eof(self.line)));
            }
        };
        self.current += 1;

        Some(match next_char {
            c if is_alphabetic(c) => Ok(self.identifier()),
            c if is_numeric(c) => Ok(self.number()),
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
                let t = if self.maybe_consume('=') {
                    BangEqual
                } else {
                    Bang
                };
                Ok(self.make_token(t))
            }
            '=' => {
                let t = if self.maybe_consume('=') {
                    EqualEqual
                } else {
                    Equal
                };
                Ok(self.make_token(t))
            }
            '<' => {
                let t = if self.maybe_consume('=') {
                    LessEqual
                } else {
                    Less
                };
                Ok(self.make_token(t))
            }
            '>' => {
                let t = if self.maybe_consume('=') {
                    GreaterEqual
                } else {
                    Greater
                };
                Ok(self.make_token(t))
            }
            '"' => self.string(),
            _ => Err(self.error("Unexpected character.")),
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
    pub(crate) fn eof(line: usize) -> Self {
        Self {
            ty: TokenType::Eof,
            lexeme: "",
            line,
        }
    }

    pub(crate) fn location(&self) -> String {
        match self.ty {
            TokenType::Eof => " at end".to_string(),
            _ => format!(" at '{}'", self.lexeme),
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
pub(crate) struct ScanError {
    pub(crate) message: &'static str,
    pub(crate) line: usize,
}
