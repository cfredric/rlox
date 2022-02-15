use enum_as_inner::EnumAsInner;

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

    fn make_token(&self, ty: TokenType<'source>) -> Token<'source> {
        Token {
            ty,
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
        self.make_token(TokenType::Number {
            value: self.current_token().parse().unwrap(),
            lexeme: self.current_token(),
        })
    }

    fn current_token(&self) -> &'source str {
        std::str::from_utf8(&self.source[0..self.current]).unwrap()
    }

    fn string(&mut self) -> Result<Token<'source>, ScanError> {
        loop {
            match self.peek() {
                Some('"') => {
                    self.current += 1;
                    return Ok(self.make_token(TokenType::String {
                        string: self.current_token(),
                    }));
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

    fn compound_equal_token(
        &mut self,
        with: TokenType<'source>,
        without: TokenType<'source>,
    ) -> Token<'source> {
        let t = if self.maybe_consume('=') {
            with
        } else {
            without
        };
        self.make_token(t)
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
            '!' => Ok(self.compound_equal_token(BangEqual, Bang)),
            '=' => Ok(self.compound_equal_token(EqualEqual, Equal)),
            '<' => Ok(self.compound_equal_token(LessEqual, Less)),
            '>' => Ok(self.compound_equal_token(GreaterEqual, Greater)),
            '"' => self.string(),
            _ => Err(self.error("Unexpected character.")),
        })
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Token<'a> {
    pub(crate) ty: TokenType<'a>,
    pub(crate) line: usize,
}

impl<'source> Token<'source> {
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

#[derive(Copy, Clone)]
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
