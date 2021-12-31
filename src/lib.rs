use std::io::{self, BufRead, Write};
use std::path::PathBuf;
use structopt::StructOpt;

mod chunk;
mod common;
mod compiler;
mod obj;
mod value;
mod vm;

#[derive(StructOpt, Debug, Default)]
pub struct Opt {
    #[structopt(name = "PATH", parse(from_os_str))]
    pub path: Option<PathBuf>,

    #[structopt(short = "e", long = "trace_execution")]
    pub trace_execution: bool,

    #[structopt(short = "p", long = "print_code")]
    pub print_code: bool,

    #[structopt(short = "c", long = "compile_only")]
    pub compile_only: bool,

    #[structopt(short = "s", long = "slow_execution")]
    pub slow_execution: bool,

    #[structopt(short = "g", long = "stress_garbage_collector")]
    stress_garbage_collector: bool,

    #[structopt(short = "l", long = "log_garbage_collection")]
    log_garbage_collection: bool,
}

impl Opt {
    pub fn new() -> Self {
        Self::default()
    }
}

pub fn run_file(opt: &Opt, source: String) -> Result<(), i32> {
    if !source.is_ascii() {
        return Err(65);
    }
    let result = vm::VM::new(opt).interpret(&source);

    match result {
        vm::InterpretResult::CompileError => Err(65),
        vm::InterpretResult::RuntimeError => Err(70),
        vm::InterpretResult::Ok => Ok(()),
    }
}

pub fn repl(opt: &Opt) -> io::Result<()> {
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
