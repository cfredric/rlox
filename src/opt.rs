use std::path::PathBuf;
use structopt::StructOpt;

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
}
