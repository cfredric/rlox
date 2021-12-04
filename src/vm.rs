use crate::chunk::{Chunk, OpCode};
use crate::compiler::{compile, CompiledResult};
use crate::obj::Obj;
use crate::table::Table;
use crate::value::Value;

pub struct VM<'a> {
    chunk: &'a Chunk,
    heap: Vec<Obj>,
    ip: usize,
    stack: Vec<Value>,
    strings: Table,
}

pub enum InterpretResult {
    Ok,
    CompileError,
    RuntimeError,
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
    pub fn new(chunk: &'a Chunk, heap: Vec<Obj>, strings: Table) -> Self {
        Self {
            chunk,
            heap,
            ip: 0,
            stack: Vec::new(),
            strings,
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

    fn concatenate(&mut self, s: &str, t: &str) -> Value {
        let mut conc = String::new();
        conc.push_str(s);
        conc.push_str(t);
        Obj::take_string(&mut self.heap, &mut self.strings, conc)
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
                    print!("[ {} ]", val.print(&self.heap));
                }
                println!();
                self.chunk.disassemble_instruction(&self.heap, self.ip);
            }
            use crate::value::*;
            match &self.read_byte() {
                OpCode::Constant(offset) => {
                    let constant = self.read_constant(*offset);
                    self.push(constant);
                }
                OpCode::Return => {
                    println!("{}", self.pop().print(&self.heap));
                    return InterpretResult::Ok;
                }
                OpCode::Negate => match self.pop() {
                    Value::Double(d) => self.push(Value::Double(-d)),
                    _ => {
                        self.runtime_error("Operand must be a number.");
                        return InterpretResult::RuntimeError;
                    }
                },
                OpCode::Add => match (self.pop(), self.pop()) {
                    (Value::Double(b), Value::Double(a)) => {
                        self.push(Value::Double(a + b));
                    }
                    (Value::ObjIndex(i), Value::ObjIndex(j)) => {
                        match (&self.heap[i], &self.heap[j]) {
                            (Obj::String(t), Obj::String(s)) => {
                                // Have to clone here, since adding to the heap
                                // might invalidate references to s and t.
                                let (s, t) = (s.clone(), t.clone());
                                let val = self.concatenate(&s, &t);
                                self.push(val);
                            }
                        }
                    }
                    _ => {
                        self.runtime_error("Operands must be two numbers or two strings.");
                        return InterpretResult::RuntimeError;
                    }
                },
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
    let CompiledResult {
        chunk,
        heap,
        strings,
    } = match compile(source) {
        Some(x) => x,
        None => return InterpretResult::CompileError,
    };

    let mut vm = VM::new(&chunk, heap, strings);
    vm.run()
}
