use enum_as_inner::EnumAsInner;

pub(crate) struct Scanner<'source> {
    source: &'source [u8],
    // The next byte to be consumed.
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

        Token::new(self.identifier_type(), self.line)
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
        Token::new(TokenType::number(self.current_token()), self.line)
    }

    fn current_token(&self) -> &'source str {
        std::str::from_utf8(&self.source[0..self.current]).unwrap()
    }

    fn string(&mut self) -> Result<Token<'source>, ScanError> {
        Ok(loop {
            match self.peek() {
                Some('"') => {
                    self.current += 1;
                    break Token::new(
                        TokenType::String {
                            string: self.current_token(),
                        },
                        self.line,
                    );
                }
                Some('\n') => {
                    self.line += 1;
                }
                Some(_) => {}
                None => {
                    return Err(self.error("Unterminated string."));
                }
            }
            self.current += 1;
        })
    }

    fn identifier_type(&self) -> TokenType<'source> {
        use TokenType::*;
        match self.current_token() {
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
            name => Identifier { name },
        }
    }

    fn compound_eq(
        &mut self,
        with: TokenType<'source>,
        without: TokenType<'source>,
    ) -> TokenType<'source> {
        if self.maybe_consume('=') {
            with
        } else {
            without
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

        Some(Ok(Token::new(
            match next_char {
                c if is_alphabetic(c) => {
                    return Some(Ok(self.identifier()));
                }
                c if is_numeric(c) => {
                    return Some(Ok(self.number()));
                }
                '"' => {
                    return Some(self.string());
                }
                '(' => LeftParen,
                ')' => RightParen,
                '{' => LeftBrace,
                '}' => RightBrace,
                ';' => Semicolon,
                ',' => Comma,
                '.' => Dot,
                '-' => Minus,
                '+' => Plus,
                '/' => Slash,
                '*' => Star,
                '!' => self.compound_eq(BangEqual, Bang),
                '=' => self.compound_eq(EqualEqual, Equal),
                '<' => self.compound_eq(LessEqual, Less),
                '>' => self.compound_eq(GreaterEqual, Greater),
                _ => {
                    return Some(Err(self.error("Unexpected character.")));
                }
            },
            self.line,
        )))
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Token<'a> {
    pub(crate) ty: TokenType<'a>,
    pub(crate) line: usize,
}

impl<'source> Token<'source> {
    fn new(ty: TokenType<'source>, line: usize) -> Self {
        Token { ty, line }
    }

    pub(crate) fn eof(line: usize) -> Self {
        Self {
            ty: TokenType::Eof,
            line,
        }
    }

    pub(crate) fn location(&self) -> String {
        format!(" at {}", self.ty)
    }
}

impl<'source> std::fmt::Display for TokenType<'source> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if *self == TokenType::Eof {
            return write!(f, "end");
        }
        write!(
            f,
            "'{}'",
            match &self {
                TokenType::LeftParen => "(",
                TokenType::RightParen => ")",
                TokenType::LeftBrace => "{",
                TokenType::RightBrace => "}",
                TokenType::Comma => ",",
                TokenType::Dot => ".",
                TokenType::Minus => "-",
                TokenType::Plus => "+",
                TokenType::Semicolon => ";",
                TokenType::Slash => "/",
                TokenType::Star => "*",
                TokenType::Bang => "!",
                TokenType::BangEqual => "!=",
                TokenType::Equal => "=",
                TokenType::EqualEqual => "==",
                TokenType::Greater => ">",
                TokenType::GreaterEqual => ">=",
                TokenType::Less => "<",
                TokenType::LessEqual => "<=",
                TokenType::Identifier { name } => name,
                TokenType::String { string } => string,
                TokenType::Number { lexeme, .. } => lexeme,
                TokenType::And => "and",
                TokenType::Class => "class",
                TokenType::Else => "else",
                TokenType::False => "false",
                TokenType::For => "for",
                TokenType::Fun => "fun",
                TokenType::If => "if",
                TokenType::Nil => "nil",
                TokenType::Or => "or",
                TokenType::Print => "print",
                TokenType::Return => "return",
                TokenType::Super => "super",
                TokenType::This => "this",
                TokenType::True => "true",
                TokenType::Var => "var",
                TokenType::While => "while",
                TokenType::Eof => unreachable!(),
            }
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) enum TokenType<'source> {
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

    Identifier { name: &'source str },
    String { string: &'source str },
    Number { value: f64, lexeme: &'source str },

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

impl<'source> PartialEq for TokenType<'source> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Identifier { name: l_name }, Self::Identifier { name: r_name }) => {
                l_name == r_name
            }
            (Self::String { string: l_string }, Self::String { string: r_string }) => {
                l_string == r_string
            }
            (Self::Number { lexeme: l_lex, .. }, Self::Number { lexeme: r_lex, .. }) => {
                l_lex == r_lex
            }
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl<'a> TokenType<'a> {
    fn number(lexeme: &'a str) -> Self {
        TokenType::Number {
            value: lexeme.parse().unwrap(),
            lexeme,
        }
    }

    pub(crate) fn payload(&self) -> TokenPayload<'a> {
        match self {
            TokenType::Identifier { name } => TokenPayload::String(name),
            TokenType::String { string } => TokenPayload::String(string),
            TokenType::Number { value, lexeme } => TokenPayload::Double(*value, lexeme),
            _ => TokenPayload::Nothing,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ScanError {
    pub(crate) message: &'static str,
    pub(crate) line: usize,
}

#[derive(Clone, Copy, EnumAsInner)]
pub(crate) enum TokenPayload<'source> {
    String(&'source str),
    Double(f64, &'source str),
    Nothing,
}
