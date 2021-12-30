use std::io;

use structopt::StructOpt;

fn main() -> io::Result<()> {
    let mut opt = rlox::Opt::from_args();
    if opt.slow_execution {
        opt.trace_execution = true;
    }
    if opt.compile_only {
        opt.print_code = true;
    }

    match &opt.path {
        Some(path) => {
            let source = std::fs::read_to_string(path)?;
            match rlox::run_file(&opt, source) {
                Ok(_) => Ok(()),
                Err(err_code) => std::process::exit(err_code),
            }
        }
        None => rlox::repl(&opt),
    }
}
