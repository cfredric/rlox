use crate::chunk::{Chunk, OpCode};
use crate::value::Value;

pub struct VM<'a> {
    chunk: &'a Chunk,
    ip: usize,
    stack: Vec<Value>,
}

pub enum InterpretResult {
    Ok,
    CompileError,
    RuntimeError,
}

fn add(a: f64, b: f64) -> f64 {
    a + b
}
fn sub(a: f64, b: f64) -> f64 {
    a - b
}
fn mul(a: f64, b: f64) -> f64 {
    a * b
}
fn div(a: f64, b: f64) -> f64 {
    a / b
}

impl<'a> VM<'a> {
    pub fn new(chunk: &'a Chunk) -> Self {
        VM {
            chunk,
            ip: 0,
            stack: Vec::new(),
        }
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

    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn binary_op<F>(&mut self, op: F)
    where
        F: Fn(f64, f64) -> f64,
    {
        let b = self.pop();
        let a = self.pop();
        match (a, b) {
            (Value::Double(ad), Value::Double(bd)) => {
                self.push(Value::Double(op(ad, bd)));
            }
        }
    }

    fn run(&mut self) -> InterpretResult {
        loop {
            if crate::common::DEBUG_TRACE_EXECUTION {
                print!("          ");
                for val in &self.stack {
                    print!("[ {} ]", val);
                }
                println!();
                self.chunk.disassemble_instruction(self.ip);
            }
            match &self.read_byte() {
                OpCode::Constant(offset) => {
                    let constant = self.read_constant(*offset);
                    self.push(constant);
                }
                OpCode::Return => {
                    println!("{}", self.pop());
                    return InterpretResult::Ok;
                }
                OpCode::Negate => match self.pop() {
                    Value::Double(d) => self.push(Value::Double(-d)),
                },
                OpCode::Add => self.binary_op(add),
                OpCode::Subtract => self.binary_op(sub),
                OpCode::Multiply => self.binary_op(mul),
                OpCode::Divide => self.binary_op(div),
            }
        }
    }
}

pub fn interpret(chunk: &Chunk) -> InterpretResult {
    let mut vm = VM::new(chunk);
    vm.run()
}

pub fn interpret_source(source: &str) -> InterpretResult {
    crate::compiler::compile(source);
    InterpretResult::Ok
}
