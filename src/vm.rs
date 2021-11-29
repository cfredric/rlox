use crate::chunk::{Chunk, OpCode};
use crate::value::Value;

pub struct VM<'a> {
    chunk: &'a Chunk,
    ip: usize,
}

pub enum InterpretResult {
    Ok,
    CompileError,
    RuntimeError,
}

// lazy_static! {
//     pub static ref vm: VM = VM::new();
// }

impl<'a> VM<'a> {
    pub fn new(chunk: &'a Chunk) -> Self {
        VM { chunk, ip: 0 }
    }

    fn read_byte(&mut self) -> OpCode {
        // NB: this reads by OpCodes, not by bytes. Differs from the book.
        let op = self.chunk.code[self.ip];
        self.ip += 1;
        op
    }

    fn read_constant(&self, offset: usize) -> Value {
        self.chunk.constants[offset]
    }

    fn run(&mut self) -> InterpretResult {
        loop {
            if crate::common::debug_trace_execution {
                self.chunk.disassemble_instruction(self.ip);
            }
            match &self.read_byte() {
                OpCode::Constant(offset) => {
                    let constant = self.read_constant(*offset);
                    println!("{}", constant);
                }
                OpCode::Return => return InterpretResult::Ok,
            }
        }
    }
}

pub fn interpret(chunk: &Chunk) -> InterpretResult {
    let mut vm = VM::new(chunk);
    vm.run()
}
