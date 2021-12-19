use crate::chunk::OpCode;
use crate::compiler::Compiler;
use crate::obj::{Function, NativeFn, Obj, OpenOrClosed, UpValue};
use crate::table::Table;
use crate::value::Value;
use crate::Opt;

pub struct VM<'opt> {
    opt: &'opt Opt,

    frames: Vec<CallFrame>,

    heap: Vec<Obj>,
    stack: Vec<Value>,
    strings: Table<usize>,
    /// open_upvalues is a pointer into the heap, to the head of the linked list
    /// of upvalue objects.
    open_upvalues: Option<usize>,
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

mod ffi {
    extern "C" {
        pub fn clock() -> libc::clock_t;
    }
}

fn clock_native(_args: Vec<Value>) -> Value {
    let t = unsafe { ffi::clock() };
    Value::Double(t as f64 / 1_000_000_f64)
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

impl<'opt> VM<'opt> {
    pub(crate) fn new(opt: &'opt Opt) -> Self {
        let mut vm = Self {
            opt,
            frames: Vec::new(),
            heap: Vec::new(),
            stack: Vec::new(),
            strings: Table::new(),
            open_upvalues: None,
            globals: Table::new(),
        };
        vm.define_native("clock", clock_native);

        vm
    }

    fn function(&self) -> &Function {
        let closure = self.heap[self.frame().heap_index].as_closure().unwrap();
        self.heap[closure.function_index].as_function().unwrap()
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
        let op = self.function().chunk.code[self.frame().ip].clone();
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
        self.open_upvalues = None;
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
            let closure = self.heap[frame.heap_index].as_closure().unwrap();
            let func = self.heap[closure.function_index].as_function().unwrap();
            let instruction = frame.ip;
            eprintln!("[line {}] in {}", func.chunk.lines[instruction], func.name);
        }

        self.reset_stack();
    }

    fn define_native(&mut self, name: &str, function: NativeFn) {
        let index = Value::ObjIndex(Obj::copy_string(&mut self.heap, &mut self.strings, name));
        self.push(index);
        let index = Value::ObjIndex(Obj::new_native(&mut self.heap, function));
        self.push(index);

        let key = self.as_string(self.stack[0]).to_string();
        let value = self.stack[1];
        self.globals.set(&key, value);
    }

    fn call_value(&mut self, callee: Value, arg_count: usize) -> bool {
        if let Value::ObjIndex(heap_index) = callee {
            match &self.heap[heap_index] {
                Obj::String(_) | Obj::Function(_) | Obj::UpValue(_) => unreachable!(),
                Obj::Closure(_) => {
                    return self.call(heap_index, arg_count);
                }
                Obj::NativeFn(native) => {
                    let result = native(self.stack.iter().rev().take(arg_count).cloned().collect());
                    for _ in 0..arg_count + 1 {
                        self.pop();
                    }
                    self.push(result);
                    return true;
                }
            }
        }
        self.runtime_error("Can only call functions and classes.");
        false
    }

    /// Captures the given stack slot as a local upvalue. Inserts the new
    /// upvalue into the linked list of upvalues on the heap, sorted by stack
    /// slot (higher first). May insert below previously-closed upvalues, since
    /// they don't have a meaningful stack index.
    fn capture_upvalue(&mut self, local: usize) -> usize {
        let mut prev_upvalue = None;
        let mut upvalue = self.open_upvalues;
        while upvalue.is_some()
            && self.heap[upvalue.unwrap()]
                .as_up_value()
                .unwrap()
                .is_at_or_above(local)
        {
            prev_upvalue = upvalue;
            upvalue = self.heap[upvalue.unwrap()].as_up_value().unwrap().next;
        }

        let created_upvalue = Obj::new_upvalue(
            &mut self.heap,
            UpValue {
                value: OpenOrClosed::Open(local),
                next: upvalue,
            },
        );

        if let Some(prev) = prev_upvalue {
            self.heap[prev].as_up_value_mut().unwrap().next = Some(created_upvalue);
        } else {
            self.open_upvalues = Some(created_upvalue);
        }

        created_upvalue
    }

    /// Closes upvalues that point to or above the given stack slot. Upvalues
    /// that are already closed are ignored.
    fn close_upvalues(&mut self, stack_slot: usize) {
        while matches!(
            self.open_upvalues,
            Some(ptr) if self.heap[ptr].as_up_value().unwrap().is_at_or_above(stack_slot)
        ) {
            let upvalue = self.heap[self.open_upvalues.unwrap()]
                .as_up_value_mut()
                .unwrap();
            match upvalue.value {
                OpenOrClosed::Open(loc) => {
                    upvalue.value = OpenOrClosed::Closed(loc, self.stack[loc]);
                }
                OpenOrClosed::Closed(_, _) => {}
            }
            self.open_upvalues = upvalue.next;
        }
    }

    fn call(&mut self, closure_heap_index: usize, arg_count: usize) -> bool {
        let closure = self.heap[closure_heap_index].as_closure().unwrap();
        let arity = self.heap[closure.function_index]
            .as_function()
            .unwrap()
            .arity;
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
            closure_heap_index,
            self.stack.len() - arg_count - 1,
        ));
        true
    }

    fn run(&mut self) -> InterpretResult {
        loop {
            if self.opt.trace_execution {
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
            if self.opt.slow_execution {
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
                    self.close_upvalues(self.frame().slots());
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
                    let index = self.frame().slots() + *slot;
                    self.stack[index] = self.peek(0);
                }
                OpCode::GetLocal(slot) => {
                    let value = self.stack[self.frame().slots() + *slot];
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
                OpCode::Closure(constant, upvalues) => {
                    let value = self.read_constant(*constant);
                    let function_heap_index = value.as_obj_index().unwrap();
                    let upvalues = upvalues
                        .iter()
                        .map(|uv| {
                            if uv.is_local {
                                self.capture_upvalue(self.frame().slots() + uv.index)
                            } else {
                                self.heap[self.frame().heap_index]
                                    .as_closure()
                                    .unwrap()
                                    .upvalues[uv.index]
                            }
                        })
                        .collect();
                    let closure_heap_index =
                        Obj::new_closure(&mut self.heap, *function_heap_index, upvalues);
                    self.push(Value::ObjIndex(closure_heap_index));
                }
                OpCode::GetUpvalue(slot) => {
                    let closure = self.heap[self.frame().heap_index].as_closure().unwrap();
                    let uv_index = closure.upvalues[*slot];
                    let uv = self.heap[uv_index].as_up_value().unwrap();
                    let val = match uv.value {
                        OpenOrClosed::Open(loc) => self.stack[loc],
                        OpenOrClosed::Closed(_, val) => val,
                    };
                    self.push(val);
                }
                OpCode::SetUpvalue(slot) => {
                    let closure = self.heap[self.frame().heap_index].as_closure().unwrap();
                    let uv_index = closure.upvalues[*slot];
                    let val = self.peek(0);
                    let uv = self.heap[uv_index].as_up_value_mut().unwrap();
                    match uv.value {
                        OpenOrClosed::Open(loc) => self.stack[loc] = val,
                        OpenOrClosed::Closed(loc, _) => uv.value = OpenOrClosed::Closed(loc, val),
                    };
                }
                OpCode::CloseUpvalue => {
                    self.close_upvalues(self.stack.len() - 1);
                    self.pop();
                }
            }
        }
    }

    pub fn interpret(&mut self, source: &str) -> InterpretResult {
        let compiler = Compiler::new(
            self.opt,
            source,
            &mut self.heap,
            crate::compiler::FunctionType::Script,
            &mut self.strings,
        );
        let function = compiler.compile();
        match function {
            Some(function) => {
                let function_heap_index =
                    Obj::allocate_object(&mut self.heap, Obj::Function(function));
                self.push(Value::ObjIndex(function_heap_index));
                let closure_heap_index =
                    Obj::new_closure(&mut self.heap, function_heap_index, Vec::new());
                self.pop();
                self.push(Value::ObjIndex(closure_heap_index));
                self.call(closure_heap_index, 0);
            }
            None => {
                return InterpretResult::CompileError;
            }
        };

        if self.opt.compile_only {
            return InterpretResult::Ok;
        }

        self.run()
    }
}

struct CallFrame {
    // Offset into heap. Points to a Closure.
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

    fn slots(&self) -> usize {
        self.frame_start + 1
    }
}
