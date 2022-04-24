use std::io::{self, Write};

mod chunk;
mod compiler;
mod heap;
mod obj;
mod opcode;
mod opt;
mod scanner;
mod stack;
mod value;
mod vm;

pub use opt::Opt;

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
