use crate::chunk::OpCode;
use crate::compiler::Compiler;
use crate::obj::{Function, Obj};
use crate::table::Table;
use crate::value::Value;

pub struct VM {
    trace_execution: bool,
    print_code: bool,
    compile_only: bool,
    slow_execution: bool,

    frames: Vec<CallFrame>,

    heap: Vec<Obj>,
    stack: Vec<Value>,
    strings: Table<usize>,
    globals: Table<Value>,
}

const MAX_FRAMES: usize = 1024;

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
            print_code: opt.print_code || opt.compile_only,
            trace_execution: opt.trace_execution,
            compile_only: opt.compile_only,
            slow_execution: opt.trace_execution && opt.slow_execution,
            frames: Vec::new(),
            heap: Vec::new(),
            stack: Vec::new(),
            strings: Table::new(),
            globals: Table::new(),
        }
    }

    fn function(&self) -> &Function {
        match &self.heap[self.frame().heap_index] {
            Obj::Function(f) => f,
            Obj::String(_) => unreachable!(),
        }
    }

    fn frame(&self) -> &CallFrame {
        self.frames.last().expect("frames was unexpectedly empty")
    }

    fn frame_mut(&mut self) -> &mut CallFrame {
        self.frames
            .last_mut()
            .expect("frames was unexpectedly empty")
    }

    fn read_byte(&mut self) -> OpCode {
        // NB: this reads by OpCodes, not by bytes. Differs from the book.
        let op = self.function().chunk.code[self.frame().ip];
        self.frame_mut().ip += 1;
        op
    }

    fn read_constant(&self, offset: usize) -> Value {
        self.function().chunk.constants[offset]
    }

    fn read_string(&self, offset: usize) -> &str {
        self.as_string(self.read_constant(offset))
    }

    fn as_string(&self, val: Value) -> &str {
        match val {
            Value::ObjIndex(idx) => match &self.heap[idx] {
                Obj::String(s) => s,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    /// Pops a value from the stack.
    fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    fn peek(&self, offset: usize) -> Value {
        self.stack[self.stack.len() - 1 - offset]
    }

    fn reset_stack(&mut self) {
        self.stack.clear();
    }

    fn concatenate(&mut self, s: &str, t: &str) -> Value {
        let mut conc = String::new();
        conc.push_str(s);
        conc.push_str(t);
        Value::ObjIndex(Obj::take_string(&mut self.heap, &mut self.strings, conc))
    }

    fn runtime_error(&mut self, message: &str) {
        eprintln!("{}", message);

        for frame in self.frames.iter().rev() {
            let func = self.heap[frame.heap_index].as_function().unwrap();
            let instruction = frame.ip;
            eprintln!("[line {}] in {}", func.chunk.lines[instruction], func.name);
        }

        self.reset_stack();
    }

    fn call_value(&mut self, callee: Value, arg_count: usize) -> bool {
        if let Value::ObjIndex(heap_index) = callee {
            if let Obj::Function(_) = &self.heap[heap_index] {
                return self.call(heap_index, arg_count);
            }
        }
        self.runtime_error("Can only call functions and classes.");
        false
    }

    fn call(&mut self, func_heap_index: usize, arg_count: usize) -> bool {
        let arity = self.heap[func_heap_index].as_function().unwrap().arity;
        if arg_count != arity {
            self.runtime_error(&format!(
                "Expected {} arguments but got {}.",
                arity, arg_count
            ));
            return false;
        }

        if self.frames.len() == MAX_FRAMES {
            self.runtime_error("Stack overflow.");
            return false;
        }

        self.frames.push(CallFrame::new(
            func_heap_index,
            self.stack.len() - arg_count - 1,
        ));
        true
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

                println!(
                    "frame:    {}",
                    self.stack
                        .iter()
                        .skip(self.frame().frame_start)
                        .map(|i| format!("[ {} ]", i.print(&self.heap)))
                        .collect::<String>()
                );
                self.function()
                    .chunk
                    .disassemble_instruction(&self.heap, self.frame().ip);

                println!();
            }
            if self.slow_execution {
                std::thread::sleep(std::time::Duration::new(1, 0));
            }
            use crate::value::*;
            match &self.read_byte() {
                OpCode::Constant(offset) => {
                    let constant = self.read_constant(*offset);
                    self.push(constant);
                }
                OpCode::Return => {
                    let result = self.pop();
                    let finished_frame = self.frames.pop().unwrap();
                    if self.frames.is_empty() {
                        self.pop();
                        return InterpretResult::Ok;
                    }

                    self.stack.truncate(finished_frame.frame_start);
                    self.push(result);
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
                            (_, _) => {
                                unreachable!();
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
                    let index = self.frame().slots(*slot);
                    self.stack[index] = self.peek(0);
                }
                OpCode::GetLocal(slot) => {
                    let value = self.stack[self.frame().slots(*slot)];
                    self.stack.push(value);
                }
                OpCode::JumpIfFalse(distance) => {
                    if self.peek(0).is_falsey() {
                        self.frame_mut().ip += distance;
                    }
                }
                OpCode::Jump(distance) => {
                    self.frame_mut().ip += distance;
                }
                OpCode::Loop(distance) => {
                    self.frame_mut().ip -= distance;
                }
                OpCode::Call(arity) => {
                    if !self.call_value(self.peek(*arity), *arity) {
                        return InterpretResult::RuntimeError;
                    }
                }
            }
        }
    }

    pub fn interpret(&mut self, source: &str) -> InterpretResult {
        let compiler = Compiler::new(
            self.print_code,
            source,
            &mut self.heap,
            crate::compiler::FunctionType::Script,
            &mut self.strings,
        );
        let function = compiler.compile();
        match function {
            Some(function) => {
                let heap_index = Obj::allocate_object(&mut self.heap, Obj::Function(function));
                self.push(Value::ObjIndex(heap_index));
                self.call(heap_index, 0);
            }
            None => {
                return InterpretResult::CompileError;
            }
        };

        if self.compile_only {
            return InterpretResult::Ok;
        }

        self.run()
    }
}

struct CallFrame {
    // Offset into heap.
    heap_index: usize,
    // Offset into function.chunk.code.
    ip: usize,
    // The first index of the stack that belongs to this frame.
    frame_start: usize,
}

impl CallFrame {
    fn new(heap_index: usize, frame_start: usize) -> Self {
        Self {
            heap_index,
            ip: 0,
            frame_start,
        }
    }

    fn slots(&self, offset: usize) -> usize {
        self.frame_start + 1 + offset
    }
}
