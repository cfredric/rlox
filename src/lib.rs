use std::io::{self, Write};
use std::path::PathBuf;
use structopt::StructOpt;

mod chunk;
mod compiler;
mod heap;
mod obj;
mod rewrite;
mod scanner;
mod stack;
mod to_string;
mod value;
mod vm;

#[derive(StructOpt, Default)]
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

    #[structopt(short = "d", long = "disable_garbage_collection")]
    disable_garbage_collection: bool,
}

impl Opt {
    pub fn new() -> Self {
        Self::default()
    }
}

pub fn run_file(opt: &Opt, source: String) -> Result<(), i32> {
    vm::VM::new(opt)
        .interpret(&source, vm::Mode::Script)
        .map_err(|err| match err {
            vm::InterpretResult::CompileError => 65,
            vm::InterpretResult::RuntimeError => 70,
        })
}

pub fn repl(opt: &Opt) -> io::Result<()> {
    let mut vm = vm::VM::new(opt);

    let mut rl = rustyline::Editor::<()>::with_config(
        rustyline::Config::builder()
            .edit_mode(rustyline::EditMode::Vi)
            .build(),
    );

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(&line);
                let _ = vm.interpret(&line, vm::Mode::Repl);
            }
            Err(rustyline::error::ReadlineError::Eof) => {
                println!("^D");
                break;
            }
            Err(rustyline::error::ReadlineError::Interrupted) => {
                println!("^C");
            }
            Err(e) => {
                dbg!(e);
            }
        }
        std::io::stdout().flush()?;
    }

    Ok(())
}

// Exposed only for fuzzing the REPL, since the fuzzer can't create a VM
// directly, and can't easily plumb input through stdin either.
pub fn run_as_repl(opt: &Opt, line: &str) {
    let mut vm = vm::VM::new(opt);
    let _ = vm.interpret(line, vm::Mode::Repl);
}
