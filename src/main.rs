use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use structopt::StructOpt;

mod chunk;
mod common;
mod compiler;
mod obj;
mod value;
mod vm;

#[derive(StructOpt, Debug)]
struct Opt {
    #[structopt(name = "PATH", parse(from_os_str))]
    path: Option<PathBuf>,
}

fn main() -> io::Result<()> {
    let opt = Opt::from_args();

    match opt.path {
        Some(path) => {
            run_file(&path);
            Ok(())
        }
        None => repl(),
    }
}

fn run_file(path: &Path) {
    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(_) => todo!(),
    };
    let result = vm::interpret(&source);

    match result {
        vm::InterpretResult::Ok => {}
        vm::InterpretResult::CompileError => std::process::exit(65),
        vm::InterpretResult::RuntimeError => std::process::exit(70),
    }
}

fn repl() -> io::Result<()> {
    let mut buffer = String::new();
    let stdin = std::io::stdin();
    let mut handle = stdin.lock();

    loop {
        print!("> ");
        std::io::stdout().flush()?;
        handle.read_line(&mut buffer)?;

        if buffer.is_empty() {
            return Ok(());
        }
        if buffer != "\n" {
            vm::interpret(&buffer);
        }
        buffer.clear();
    }
}
