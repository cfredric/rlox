use std::path::PathBuf;
use structopt::StructOpt;

#[derive(StructOpt, Default)]
pub struct Opt {
    #[structopt(name = "PATH", parse(from_os_str))]
    /// The path of the file to be used as input, if any. If no path is present,
    /// the VM starts in REPL mode.
    pub path: Option<PathBuf>,

    #[structopt(short = "e", long = "trace_execution")]
    /// Tells the VM to print a trace of the execution during interpretation,
    /// showing the instruction codes and the state of the value stack. Implied
    /// by `slow_execution`.
    pub trace_execution: bool,

    #[structopt(short = "p", long = "print_code")]
    /// Tells the VM to print the compiled bytecode before interpreting it.
    /// Implied by `compile_only`.
    pub print_code: bool,

    #[structopt(short = "c", long = "compile_only")]
    /// Tells the VM to only compile the input, without interpreting it. Implies
    /// the `print_code` option.
    pub compile_only: bool,

    #[structopt(short = "s", long = "slow_execution")]
    /// Tells the VM to interpret the bytecode slowly, for the purposes of
    /// debugging / understanding the behavior of the value stack. Implies the
    /// `trace_execution` option.
    pub slow_execution: bool,

    #[structopt(short = "g", long = "stress_garbage_collector")]
    /// Stress tests the garbage collector in several ways:
    ///
    /// * Frequency: forces the GC to run at every opportunity. It'll do a
    /// sweep/collection before every allocation, and between interpreting every
    /// separate bytecode op.
    ///
    /// * Behavior: when doing sweep/collect operations, the GC will alternately
    /// insert/remove a dummy item at the start of the heap, so that *every*
    /// heap element is guaranteed to be relocated by the GC. This is intended
    /// to shake out bugs due to un-rewritten heap pointers; but has a large
    /// impact on GC performance.
    pub stress_garbage_collector: bool,

    #[structopt(short = "l", long = "log_garbage_collection")]
    /// Tells the VM to log some events related to garbage collection, e.g. when
    /// an allocation occurs, or when GC starts and ends.
    pub log_garbage_collection: bool,

    #[structopt(short = "d", long = "disable_garbage_collection")]
    /// Tells the VM to never do garbage collection. I.e., the memory management
    /// strategy is to "leak everything".
    pub disable_garbage_collection: bool,
}
