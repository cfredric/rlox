use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
use structopt::StructOpt;

mod chunk;
mod common;
mod compiler;
mod obj;
mod table;
mod value;
mod vm;

#[derive(StructOpt, Debug)]
pub(crate) struct Opt {
    #[structopt(name = "PATH", parse(from_os_str))]
    path: Option<PathBuf>,

    #[structopt(short = "e", long = "trace_execution")]
    trace_execution: bool,

    #[structopt(short = "p", long = "print_code")]
    print_code: bool,

    #[structopt(short = "c", long = "compile_only")]
    compile_only: bool,

    #[structopt(short = "s", long = "slow_execution")]
    slow_execution: bool,
}

fn main() -> io::Result<()> {
    let mut opt = Opt::from_args();
    if opt.slow_execution {
        opt.trace_execution = true;
    }
    if opt.compile_only {
        opt.print_code = true;
    }

    match &opt.path {
        Some(path) => {
            run_file(path, &opt);
            Ok(())
        }
        None => repl(&opt),
    }
}

fn run_file(path: &Path, opt: &Opt) {
    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(_) => todo!(),
    };
    let mut vm = vm::VM::new(opt);
    let result = vm.interpret(&source);

    match result {
        vm::InterpretResult::Ok => {}
        vm::InterpretResult::CompileError => std::process::exit(65),
        vm::InterpretResult::RuntimeError => std::process::exit(70),
    }
}

fn repl(opt: &Opt) -> io::Result<()> {
    let mut buffer = String::new();
    let stdin = std::io::stdin();
    let mut handle = stdin.lock();

    let mut vm = vm::VM::new(opt);

    loop {
        print!("> ");
        std::io::stdout().flush()?;
        handle.read_line(&mut buffer)?;

        if buffer.is_empty() {
            return Ok(());
        }
        if buffer != "\n" {
            vm.interpret(&buffer);
        }
        buffer.clear();
    }
}
