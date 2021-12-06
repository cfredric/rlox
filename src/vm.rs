use crate::chunk::{Chunk, OpCode};
use crate::compiler::Compiler;
use crate::obj::Obj;
use crate::table::Table;
use crate::value::Value;

pub struct VM {
    trace_execution: bool,
    print_code: bool,
    chunk: Chunk,
    heap: Vec<Obj>,
    ip: usize,
    stack: Vec<Value>,
    strings: Table,
    globals: Table,
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

impl VM {
    pub(crate) fn new(opt: &crate::Opt) -> Self {
        Self {
            print_code: opt.print_code,
            trace_execution: opt.trace_execution,
            chunk: Chunk::default(),
            heap: Vec::new(),
            ip: 0,
            stack: Vec::new(),
            strings: Table::new(),
            globals: Table::new(),
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

    fn read_string(&self, offset: usize) -> &str {
        self.as_string(self.read_constant(offset))
    }

    fn as_string(&self, val: Value) -> &str {
        match val {
            Value::ObjIndex(idx) => match &self.heap[idx] {
                Obj::String(s) => s,
            },
            _ => unreachable!(),
        }
    }

    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn peek(&self, offset: usize) -> Value {
        self.stack[self.stack.len() - 1 - offset]
    }

    fn concatenate(&mut self, s: &str, t: &str) -> Value {
        let mut conc = String::new();
        conc.push_str(s);
        conc.push_str(t);
        Value::ObjIndex(Obj::take_string(&mut self.heap, &mut self.strings, conc))
    }

    fn runtime_error(&mut self, message: &str) {
        eprintln!("{}", message);
        let instruction = self.ip - 1;
        let line = self.chunk.lines[instruction];
        eprintln!("[line {}] in script", line)
    }

    fn run(&mut self) -> InterpretResult {
        loop {
            if self.trace_execution {
                println!(
                    "stack:    {}",
                    self.stack
                        .iter()
                        .map(|i| format!("[ {} ]", i.print(&self.heap)))
                        .collect::<String>()
                );
                self.chunk.disassemble_instruction(&self.heap, self.ip);
            }
            use crate::value::*;
            match &self.read_byte() {
                OpCode::Constant(offset) => {
                    let constant = self.read_constant(*offset);
                    self.push(constant);
                }
                OpCode::Return => {
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
                OpCode::Print => {
                    println!("{}", self.pop().print(&self.heap));
                }
                OpCode::Pop => {
                    self.pop();
                }
                OpCode::DefineGlobal(index) => {
                    let name = self.read_string(*index).to_string();
                    let v = self.pop();
                    self.globals.set(&name, v);
                }
                OpCode::GetGlobal(index) => {
                    let name = self.read_string(*index).to_string();
                    let v = self.globals.get(&name);
                    if v.is_none() {
                        self.runtime_error(&format!("Undefined variable '{}'.", name));
                        return InterpretResult::RuntimeError;
                    }
                    let v = *v.unwrap();
                    self.push(v);
                }
                OpCode::SetGlobal(index) => {
                    let name = self.read_string(*index).to_string();
                    if self.globals.set(&name, self.peek(0)) {
                        self.globals.delete(&name);
                        self.runtime_error(&format!("Undefined variable '{}'.", name));
                        return InterpretResult::RuntimeError;
                    }
                }
                OpCode::SetLocal(slot) => {
                    self.stack[*slot] = self.peek(0);
                }
                OpCode::GetLocal(slot) => {
                    self.stack.push(self.stack[*slot]);
                }
            }
        }
    }

    pub fn interpret(&mut self, source: &str) -> InterpretResult {
        let compiler = Compiler::new(
            self.print_code,
            source,
            &mut self.chunk,
            &mut self.heap,
            &mut self.strings,
        );
        if !compiler.compile() {
            return InterpretResult::CompileError;
        };

        self.run()
    }
}
