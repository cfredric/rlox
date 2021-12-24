use std::collections::{HashMap, HashSet};

use crate::chunk::{Chunk, OpCode};
use crate::compiler::Compiler;
use crate::obj::{
    BoundMethod, Class, Closure, Function, Instance, LoxString, NativeFn, Obj, OpenOrClosed,
    UpValue,
};
use crate::table::Table;
use crate::value::Value;
use crate::Opt;

const GC_HEAP_GROWTH_FACTOR: usize = 2;
const INIT_STR: &str = "init";

pub struct VM<'opt> {
    opt: &'opt Opt,

    frames: Vec<CallFrame>,

    pub heap: Vec<Obj>,
    stack: Vec<Value>,
    pub strings: Table<usize>,
    /// open_upvalues is a pointer into the heap, to the head of the linked list
    /// of upvalue objects.
    open_upvalues: Option<usize>,
    globals: Table<Value>,

    /// Vector of heap indices, used during GC.
    gray_stack: Vec<usize>,

    bytes_allocated: usize,
    next_gc: usize,
    /// Hack: we don't do garbage collection during compilation, since we don't
    /// have visibility into the compiler's data structures and therefore can't
    /// trace the roots it is in the process of adding.
    is_compiling: bool,
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
            gray_stack: Vec::new(),
            bytes_allocated: 0,
            next_gc: 1024 * 1024,
            is_compiling: false,
        };
        vm.define_native("clock", NativeFn::new(clock_native));

        vm
    }

    pub fn copy_string(&mut self, s: &str) -> usize {
        if let Some(v) = self.strings.get(s) {
            return *v;
        }
        self.allocate_string(s.to_string())
    }

    pub fn take_string(&mut self, s: String) -> usize {
        if let Some(v) = self.strings.get(&s) {
            return *v;
        }
        self.allocate_string(s)
    }

    fn allocate_string(&mut self, s: String) -> usize {
        let idx = self.allocate_object(Obj::String(LoxString::new(&s)));
        self.strings
            .set(&self.heap[idx].as_string().unwrap().string, idx);
        idx
    }

    pub fn new_function(&mut self, f: Function) -> usize {
        self.allocate_object(Obj::Function(f))
    }

    pub fn new_native(&mut self, f: NativeFn) -> usize {
        self.allocate_object(Obj::NativeFn(f))
    }

    pub fn new_closure(&mut self, func_index: usize, upvalues: Vec<usize>) -> usize {
        self.allocate_object(Obj::Closure(Closure::new(func_index, upvalues)))
    }

    pub fn new_class(&mut self, name: &str) -> usize {
        self.allocate_object(Obj::Class(Class::new(name)))
    }

    pub fn new_instance(&mut self, class_index: usize) -> usize {
        self.allocate_object(Obj::Instance(Instance::new(class_index, Table::new())))
    }

    pub fn new_bound_method(&mut self, receiver: Value, closure_idx: usize) -> usize {
        self.allocate_object(Obj::BoundMethod(BoundMethod::new(receiver, closure_idx)))
    }

    pub fn new_upvalue(&mut self, upvalue: UpValue) -> usize {
        self.allocate_object(Obj::UpValue(upvalue))
    }

    pub fn allocate_object(&mut self, obj: Obj) -> usize {
        if self.opt.log_garbage_collection {
            eprintln!("allocate for {}", obj.print(&self.heap));
        }

        self.bytes_allocated += std::mem::size_of::<Obj>();
        if self.bytes_allocated > self.next_gc || self.opt.stress_garbage_collector {
            self.collect_garbage();
        }
        self.heap.push(obj);
        self.heap.len() - 1
    }

    fn function(&self) -> &Function {
        self.heap[self.closure().function_index]
            .as_function()
            .unwrap()
    }

    fn frame(&self) -> &CallFrame {
        self.frames.last().expect("frames was unexpectedly empty")
    }

    fn frame_mut(&mut self) -> &mut CallFrame {
        self.frames
            .last_mut()
            .expect("frames was unexpectedly empty")
    }

    fn closure(&self) -> &Closure {
        self.heap[self.frame().heap_index].as_closure().unwrap()
    }

    fn read_byte(&mut self) -> OpCode {
        // NB: this reads by OpCodes, not by bytes. Differs from the book.
        let op = self.function().chunk.code[self.frame().ip].clone();
        self.frame_mut().ip += 1;
        op
    }

    // Reads a constant from the constants table.
    fn read_constant(&self, offset: usize) -> Value {
        self.function().chunk.constants[offset]
    }

    /// Reads a string from the constants table.
    fn read_string(&self, offset: usize) -> &str {
        self.as_string(self.read_constant(offset))
    }

    fn as_string(&self, val: Value) -> &str {
        &self.heap[*val.as_obj_index().unwrap()]
            .as_string()
            .unwrap()
            .string
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
        Value::ObjIndex(self.take_string(conc))
    }

    fn runtime_error(&mut self, message: &str) {
        eprintln!("Runtime error: {}", message);

        for frame in self.frames.iter().rev() {
            let func = self.function();
            let instruction = frame.ip;
            eprintln!("[line {}] in {}", func.chunk.lines[instruction], func.name);
        }

        self.reset_stack();
    }

    fn define_native(&mut self, name: &str, function: NativeFn) {
        let index = self.copy_string(name);
        self.heap[index].set_gc_exempt();
        let index = Value::ObjIndex(index);
        self.push(index);
        let index = Value::ObjIndex(self.new_native(function));
        self.push(index);

        let key = self.as_string(self.stack[0]).to_string();
        let value = self.stack[1];
        self.globals.set(&key, value);

        self.pop();
        self.pop();
    }

    fn call_value(&mut self, callee: Value, arg_count: usize) -> bool {
        if let Value::ObjIndex(heap_index) = callee {
            match &self.heap[heap_index] {
                Obj::String(_) | Obj::Function(_) | Obj::UpValue(_) | Obj::Instance(_) => {}
                Obj::Closure(_) => {
                    return self.call(heap_index, arg_count);
                }
                Obj::NativeFn(native) => {
                    let result =
                        (native.f)(self.stack.iter().rev().take(arg_count).cloned().collect());
                    for _ in 0..arg_count + 1 {
                        self.pop();
                    }
                    self.push(result);
                    return true;
                }
                Obj::Class(_) => {
                    let stack_len = self.stack.len();
                    let instance = self.new_instance(heap_index);
                    self.stack[stack_len - arg_count - 1] = Value::ObjIndex(instance);

                    if let Some(initializer) = self.heap[heap_index]
                        .as_class()
                        .unwrap()
                        .methods
                        .get(INIT_STR)
                        .cloned()
                    {
                        return self.call(*initializer.as_obj_index().unwrap(), arg_count);
                    } else if arg_count != 0 {
                        self.runtime_error(&format!("Expected 0 arguments but got {}", arg_count));
                        return false;
                    }
                    return true;
                }
                Obj::BoundMethod(b) => {
                    let bound_ptr = b.closure_idx;
                    let stack_top = self.stack.len();
                    self.stack[stack_top - arg_count - 1] = b.receiver;
                    return self.call(bound_ptr, arg_count);
                }
            };
        }
        self.runtime_error("Can only call functions and classes.");
        false
    }

    fn invoke_from_class(&mut self, class_index: usize, name: &str, arg_count: usize) -> bool {
        let method = match self.heap[class_index].as_class().unwrap().methods.get(name) {
            Some(m) => *m.as_obj_index().unwrap(),
            None => {
                self.runtime_error(&format!("Undefined property {}", name));
                return false;
            }
        };
        self.call(method, arg_count)
    }

    fn invoke(&mut self, name: &str, arg_count: usize) -> bool {
        let receiver = self.peek(arg_count);
        let (class_index, fields) = match self.heap[*receiver.as_obj_index().unwrap()].as_instance()
        {
            Some(i) => (i.class_index, i.fields.clone()),
            None => {
                self.runtime_error("Only instances have methods.");
                return false;
            }
        };

        if let Some(value) = fields.get(name) {
            let stack_len = self.stack.len();
            self.stack[stack_len - arg_count - 1] = *value;
            return self.call_value(*value, arg_count);
        }
        self.invoke_from_class(class_index, name, arg_count)
    }

    fn bind_method(&mut self, class_idx: usize, name: &str) -> bool {
        let method = match self.heap[class_idx].as_class().unwrap().methods.get(name) {
            Some(m) => *m,
            None => {
                self.runtime_error(&format!("Undefined property {}", name));
                return false;
            }
        };

        let bound = self.new_bound_method(self.peek(0), *method.as_obj_index().unwrap());
        self.pop();
        self.push(Value::ObjIndex(bound));
        true
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

        let created_upvalue = self.new_upvalue(UpValue::new(local, upvalue));

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

    fn define_method(&mut self, name_idx: Value) {
        let method = self.peek(0);
        let class_index = *self.peek(1).as_obj_index().unwrap();
        let name = self.heap[*name_idx.as_obj_index().unwrap()]
            .as_string()
            .unwrap()
            .string
            .clone();
        let class = self.heap[class_index].as_class_mut().unwrap();

        class.methods.set(&name, method);
        self.pop();
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

    fn collect_garbage(&mut self) {
        if self.is_compiling {
            return;
        }
        if self.opt.log_garbage_collection {
            eprintln!("-- gc begin");
        }
        let before = self.bytes_allocated;

        self.mark_roots();
        self.trace_references();
        let removed = self.sweep();

        self.bytes_allocated -= removed * std::mem::size_of::<Obj>();
        self.next_gc = self.bytes_allocated * GC_HEAP_GROWTH_FACTOR;

        if self.opt.log_garbage_collection {
            eprintln!("-- gc end");
            eprintln!(
                "   collected {} bytes ({} to {}), next at {}",
                before - self.bytes_allocated,
                before,
                self.bytes_allocated,
                self.next_gc
            );
        }
    }

    fn trace_references(&mut self) {
        while let Some(index) = self.gray_stack.pop() {
            self.blacken_object(index);
        }
    }

    fn mark_roots(&mut self) {
        for slot in 0..self.stack.len() {
            self.mark_value(self.stack[slot]);
        }

        for index in self.frames.iter().map(|f| f.heap_index).collect::<Vec<_>>() {
            self.mark_object(index)
        }

        {
            let mut upvalue = self.open_upvalues;
            while let Some(index) = upvalue {
                self.mark_object(index);
                upvalue = self.heap[index].as_up_value().unwrap().next;
            }
        }

        for v in self.globals.table.clone().values() {
            self.mark_value(*v);
        }

        // Not marking compiler roots, since the compiler doesn't exist after
        // the call to `compile` completes. This implementation has no static
        // state, unlike clox.
    }

    fn mark_value(&mut self, value: Value) {
        if self.opt.log_garbage_collection {
            eprintln!("    mark value ({})", value.print(&self.heap));
        }
        match value {
            Value::Nil | Value::Bool(_) | Value::Double(_) => {}
            Value::ObjIndex(index) => {
                self.mark_object(index);
            }
        }
    }

    fn blacken_object(&mut self, index: usize) {
        if self.opt.log_garbage_collection {
            eprintln!("{} blacken {}", index, self.heap[index].print(&self.heap));
        }

        match &self.heap[index] {
            Obj::String(_) | Obj::NativeFn(_) => {}
            Obj::Function(f) => {
                // TODO: don't clone here.
                for v in f.chunk.constants.clone().iter_mut() {
                    self.mark_value(*v);
                }
            }
            Obj::Closure(c) => {
                let fn_idx = c.function_index;
                let uvs = c.upvalues.clone();
                self.mark_object(fn_idx);
                for uv in &uvs {
                    self.mark_object(*uv);
                }
            }
            Obj::UpValue(upvalue) => {
                if let OpenOrClosed::Closed(_, v) = upvalue.value {
                    self.mark_value(v);
                }
            }
            Obj::Class(c) => {
                let methods = c.methods.table.values().copied().collect::<Vec<_>>();
                for m in methods {
                    self.mark_value(m);
                }
            }
            Obj::Instance(i) => {
                let idx = i.class_index;
                let field_values = i.fields.table.values().copied().collect::<Vec<_>>();
                self.mark_object(idx);
                for value in field_values {
                    self.mark_value(value);
                }
            }
            Obj::BoundMethod(b) => {
                let rec = b.receiver;
                let c = b.closure_idx;
                self.mark_value(rec);
                self.mark_object(c);
            }
        }
    }

    fn mark_object(&mut self, index: usize) {
        if self.opt.log_garbage_collection {
            eprintln!(
                "{:3} mark object {}",
                index,
                self.heap[index].print(&self.heap)
            );
        }

        if self.heap[index].is_marked() {
            return;
        }

        self.heap[index].mark(true);

        self.gray_stack.push(index);
    }

    /// Does a sweep & compaction of the heap. Since heap pointers are just
    /// indices, and we're moving objects around, we also have to rewrite
    /// pointers within objects.
    ///
    /// Returns the number of items removed from the heap.
    ///
    /// Differs from the book, since clox doesn't do compaction (since it uses
    /// C's heap, rather than manually managing a separate heap).
    fn sweep(&mut self) -> usize {
        // Build the mapping from pre-sweep pointers to post-sweep pointers.
        let mapping = {
            let mut mapping = HashMap::new();
            let mut post_compaction_index = 0;
            for (i, obj) in self.heap.iter().enumerate() {
                if obj.is_marked() {
                    // If this object is marked, it is reachable, and will be kept.
                    // We add an entry for this pointer, and then increment the
                    // post-compaction pointer.
                    mapping.insert(i, post_compaction_index);
                    post_compaction_index += 1;
                }
            }
            mapping
        };

        // Remove unreachable objects.
        let before = self.heap.len();
        self.heap.retain(|obj| obj.is_marked());

        // Now apply pointer rewriting.
        // Rewrite heap-internal pointers:
        for obj in self.heap.iter_mut() {
            obj.mark(false);
            match obj {
                Obj::String(_) | Obj::NativeFn(_) | Obj::Class(_) => {
                    // Nothing to do here.
                }
                Obj::Function(f) => {
                    Self::rewrite_chunk(&mut f.chunk, &mapping);
                }
                Obj::Closure(c) => {
                    c.function_index = mapping[&c.function_index];
                    for uv in c.upvalues.iter_mut() {
                        *uv = mapping[uv];
                    }
                }
                Obj::UpValue(uv) => {
                    if let Some(ptr) = uv.next {
                        uv.next = Some(mapping[&ptr]);
                    }
                }
                Obj::Instance(i) => {
                    i.class_index = mapping[&i.class_index];
                }
                Obj::BoundMethod(b) => {
                    let rec = *b.receiver.as_obj_index().unwrap();
                    *b.receiver.as_obj_index_mut().unwrap() = mapping[&rec];
                    b.closure_idx = mapping[&b.closure_idx];
                }
            }
        }

        // Rewrite pointers from the stack into the heap:
        for v in self.stack.iter_mut() {
            if let Value::ObjIndex(i) = v {
                *i = mapping[i];
            }
        }

        // Prune out unused strings from the strings table:
        let reachable_strings = self
            .heap
            .iter()
            .filter_map(|o| o.as_string())
            .collect::<HashSet<_>>();
        self.strings
            .table
            .retain(|s, _| reachable_strings.contains(s));

        before - self.heap.len()
    }

    fn rewrite_chunk(chunk: &mut Chunk, mapping: &HashMap<usize, usize>) {
        for v in chunk.constants.iter_mut() {
            Self::rewrite_value(v, mapping);
        }
    }

    fn rewrite_value(value: &mut Value, mapping: &HashMap<usize, usize>) {
        match value {
            Value::Nil | Value::Bool(_) | Value::Double(_) => {}
            Value::ObjIndex(ptr) => {
                *ptr = mapping[ptr];
            }
        }
    }

    fn print_stack_slice(&self, label: &str, skip: usize) {
        eprintln!(
            "{}:    {}",
            label,
            self.stack
                .iter()
                .skip(skip)
                .map(|i| format!("[ {} ]", i.print(&self.heap)))
                .collect::<String>()
        );
    }

    fn run(&mut self) -> InterpretResult {
        loop {
            if self.opt.trace_execution {
                self.print_stack_slice("stack", 0);
                self.print_stack_slice("frame", self.frame().frame_start);

                self.function()
                    .chunk
                    .disassemble_instruction(&self.heap, self.frame().ip);

                eprintln!();
            }
            if self.opt.slow_execution {
                std::thread::sleep(std::time::Duration::new(1, 0));
            }

            if self.opt.stress_garbage_collector {
                self.collect_garbage();
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
                        if self.opt.trace_execution {
                            self.print_stack_slice("stack", 0);
                        }
                        debug_assert!(self.stack.is_empty());
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
                OpCode::Add => match (self.peek(0), self.peek(1)) {
                    (Value::Double(b), Value::Double(a)) => {
                        self.pop();
                        self.pop();
                        self.push(Value::Double(a + b));
                    }
                    (Value::ObjIndex(i), Value::ObjIndex(j)) => {
                        match (&self.heap[i], &self.heap[j]) {
                            (Obj::String(t), Obj::String(s)) => {
                                // Have to clone here, since adding to the heap
                                // might invalidate references to s and t.
                                let (s, t) = (s.string.clone(), t.string.clone());
                                let val = self.concatenate(&s, &t);
                                self.pop();
                                self.pop();
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
                    let closure_heap_index = self.new_closure(*function_heap_index, upvalues);
                    self.push(Value::ObjIndex(closure_heap_index));
                }
                OpCode::GetUpvalue(slot) => {
                    let uv_index = self.closure().upvalues[*slot];
                    let uv = self.heap[uv_index].as_up_value().unwrap();
                    let val = match uv.value {
                        OpenOrClosed::Open(loc) => self.stack[loc],
                        OpenOrClosed::Closed(_, val) => val,
                    };
                    self.push(val);
                }
                OpCode::SetUpvalue(slot) => {
                    let uv_index = self.closure().upvalues[*slot];
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
                OpCode::Class(index) => {
                    let name = self.read_string(*index).to_string();
                    let heap_index = self.new_class(&name);
                    self.push(Value::ObjIndex(heap_index));
                }
                OpCode::GetProperty(constant) => {
                    let instance_idx = *self.peek(0).as_obj_index().unwrap();
                    if self.heap[instance_idx].as_instance().is_none() {
                        self.runtime_error("Only instances have properties.");
                        return InterpretResult::RuntimeError;
                    }
                    let name = self.read_string(*constant).to_string();
                    if let Some(v) = self.heap[instance_idx]
                        .as_instance()
                        .unwrap()
                        .fields
                        .get(&name)
                        .cloned()
                    {
                        self.pop(); // Instance.
                        self.push(v);
                        continue;
                    }
                    if !self.bind_method(
                        self.heap[instance_idx].as_instance().unwrap().class_index,
                        &name,
                    ) {
                        return InterpretResult::RuntimeError;
                    }
                }
                OpCode::SetProperty(constant) => {
                    let instance_idx = *self.peek(1).as_obj_index().unwrap();
                    if self.heap[instance_idx].as_instance().is_none() {
                        self.runtime_error("Only instances have properties.");
                        return InterpretResult::RuntimeError;
                    }
                    let name = self.read_string(*constant).to_string();
                    let value = self.peek(0);
                    self.heap[instance_idx]
                        .as_instance_mut()
                        .unwrap()
                        .fields
                        .set(&name, value);
                    self.pop(); // Value.
                    self.pop(); // Instance.
                    self.push(value);
                }
                OpCode::GetSuper(name_index) => {
                    let name = self.read_string(*name_index).to_string();
                    let superclass_ptr = *self.pop().as_obj_index().unwrap();
                    if !self.bind_method(superclass_ptr, &name) {
                        return InterpretResult::RuntimeError;
                    }
                }
                OpCode::Method(constant) => {
                    self.define_method(self.read_constant(*constant));
                }
                OpCode::Invoke(constant, arg_count) => {
                    let arg_count = *arg_count;
                    let method = self.read_string(*constant).to_string();
                    if !self.invoke(&method, arg_count) {
                        return InterpretResult::RuntimeError;
                    }
                }
                OpCode::Inherit => {
                    let superclass = *self.peek(1).as_obj_index().unwrap();
                    let superclass_methods = match &self.heap[superclass] {
                        Obj::Class(c) => c.methods.table.clone(),
                        _ => {
                            self.runtime_error("Superclass must be a class.");
                            return InterpretResult::RuntimeError;
                        }
                    };
                    let subclass = *self.peek(0).as_obj_index().unwrap();
                    let subclass_methods = &mut self.heap[subclass].as_class_mut().unwrap().methods;
                    subclass_methods
                        .table
                        .extend(superclass_methods.into_iter());
                    self.pop(); // Subclass.
                }
                OpCode::SuperInvoke(constant, arg_count) => {
                    let arg_count = *arg_count;
                    let method = self.read_string(*constant).to_string();
                    let superclass_ptr = *self.pop().as_obj_index().unwrap();
                    if !self.invoke_from_class(superclass_ptr, &method, arg_count) {
                        return InterpretResult::RuntimeError;
                    }
                }
            }
        }
    }

    pub fn interpret(&mut self, source: &str) -> InterpretResult {
        self.is_compiling = true;
        let compiler = Compiler::new(
            self.opt,
            source,
            self,
            crate::compiler::FunctionType::Script,
        );
        let function = compiler.compile();
        match function {
            Some(function) => {
                let function_heap_index = self.new_function(function);
                self.push(Value::ObjIndex(function_heap_index));
                let closure_heap_index = self.new_closure(function_heap_index, Vec::new());
                self.pop();
                self.push(Value::ObjIndex(closure_heap_index));
                self.call(closure_heap_index, 0);
            }
            None => {
                self.is_compiling = false;
                return InterpretResult::CompileError;
            }
        };

        self.is_compiling = false;
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
        self.frame_start
    }
}
