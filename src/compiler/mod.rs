mod scanner;

pub fn compile(source: &str) {
    let mut scanner = scanner::Scanner::new(source);
    let mut line: Option<usize> = None;
    loop {
        let token = scanner.scan_token();
        if line.map_or(true, |line| token.line != line) {
            print!("{:4} ", token.line);
            line = Some(token.line);
        } else {
            print!("    | ");
        }
        println!(
            "{:?} '{}'",
            token.ty,
            std::str::from_utf8(&token.lexeme).unwrap(),
        );

        if token.ty == scanner::TokenType::Eof {
            break;
        }
    }
}
