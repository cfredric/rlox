use std::io::{self, Write};

mod chunk;
mod compiler;
mod heap;
mod obj;
mod opcode;
mod opt;
mod post_process_gc_sweep;
mod scanner;
mod stack;
mod value;
mod vm;

pub use opt::Opt;

/// Interprets `source` according to the semantics defined by `opt`. Returns Ok
/// on success, or Err(err_code) in case of failure.
pub fn run_file(opt: &Opt, source: String) -> Result<(), i32> {
    if opt.path.is_none() {
        return Err(22);
    }
    vm::VM::new(opt, vm::Mode::Script)
        .interpret(&source)
        .map_err(|err| match err {
            vm::InterpretResult::CompileError => 65,
            vm::InterpretResult::RuntimeError => 70,
        })
}

/// Runs a REPL (Read-Eval-Print-Loop) that reads from stdin. Exits at the end
/// of input (^D).
pub fn repl(opt: &Opt) -> io::Result<()> {
    if opt.path.is_some() {
        return Ok(());
    }
    let mut vm = vm::VM::new(opt, vm::Mode::Repl);

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
                let _ = vm.interpret(&line);
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

/// Interprets a given string in the REPL mode, rather than in script mode.
///
/// Exposed only for fuzzing the REPL, since the fuzzer can't create a VM
/// directly, and can't easily plumb input through stdin either.
pub fn run_as_repl(opt: &Opt, line: &str) {
    if opt.path.is_some() {
        return;
    }
    let mut vm = vm::VM::new(opt, vm::Mode::Repl);
    let _ = vm.interpret(line);
}
