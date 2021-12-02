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
fn gt(a: f64, b: f64) -> bool {
    a > b
}
fn lt(a: f64, b: f64) -> bool {
    a < b
}

macro_rules! binary_op {
    ($self:ident, $op:ident, $value_type:ident) => {{
        let b = $self.pop();
        let a = $self.pop();
        match (a, b) {
            (Value::Double(ad), Value::Double(bd)) => {
                $self.push($value_type($op(ad, bd)));
            }
            _ => {
                $self.runtime_error("Operands must be numbers.");
                $self.push(a);
                $self.push(b);
                return InterpretResult::RuntimeError;
            }
        }
    }};
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

    fn runtime_error(&mut self, message: &str) {
        eprintln!("{}", message);
        let instruction = self.ip - 1;
        let line = self.chunk.lines[instruction];
        eprintln!("[line {}] in script", line)
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
            use crate::value::*;
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
                    _ => {
                        self.runtime_error("Operand must be a number.");
                        return InterpretResult::RuntimeError;
                    }
                },
                OpCode::Add => binary_op!(self, add, double),
                OpCode::Subtract => binary_op!(self, sub, double),
                OpCode::Multiply => binary_op!(self, mul, double),
                OpCode::Divide => binary_op!(self, div, double),
                OpCode::Nil => self.push(Value::Nil),
                OpCode::Bool(b) => self.push(Value::Bool(*b)),
                OpCode::Not => {
                    let falsey = self.pop().is_falsey();
                    self.push(Value::Bool(falsey));
                }
                OpCode::Equal => {
                    let b = self.pop();
                    let a = self.pop();
                    self.push(Value::Bool(Value::equal(a, b)));
                }
                OpCode::Greater => binary_op!(self, gt, vbool),
                OpCode::Less => binary_op!(self, lt, vbool),
            }
        }
    }
}

pub fn interpret(source: &str) -> InterpretResult {
    let chunk = match crate::compiler::compile(source) {
        Some(chunk) => chunk,
        None => return InterpretResult::CompileError,
    };

    let mut vm = VM::new(&chunk);
    vm.run()
}
