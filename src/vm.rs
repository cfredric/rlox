use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::chunk::{ConstantIndex, OpCode};
use crate::compiler::Compiler;
use crate::heap::{Heap, Ptr};
use crate::obj::{
    BoundMethod, Class, Closed, Closure, Function, Instance, LoxString, NativeFn, Obj, Open,
};
use crate::print::Print;
use crate::rewrite::Rewrite;
use crate::stack::{Slot, Stack};
use crate::value::Value;
use crate::Opt;

const GC_HEAP_GROWTH_FACTOR: usize = 2;

pub struct VM<'opt> {
    opt: &'opt Opt,

    frames: Vec<CallFrame>,

    pub heap: Heap,
    stack: Stack,
    /// Values are pointers into the heap, to LoxStrings.
    pub strings: HashMap<String, Ptr>,
    /// open_upvalues is a pointer into the heap, to the head of the linked list
    /// of upvalue objects.
    open_upvalues: Option<Ptr>,
    globals: HashMap<String, Value>,

    bytes_allocated: usize,
    next_gc: usize,
    /// Hack: we don't do garbage collection until we start executing. Differs from the book.
    is_executing: bool,
}

const MAX_FRAMES: usize = 1024;

pub enum InterpretResult {
    CompileError,
    RuntimeError,
}

mod ffi {
    extern "C" {
        pub fn clock() -> libc::clock_t;
    }
}

fn clock_native(_args: &[Value]) -> Value {
    let t = unsafe { ffi::clock() };
    Value::Double(t as f64 / 1_000_000_f64)
}

fn sleep_native(args: &[Value]) -> Value {
    if args.is_empty() {
        return Value::Nil;
    }
    let duration = match args[0] {
        Value::Double(d) => d.floor() as u64,
        _ => {
            return Value::Nil;
        }
    };

    std::thread::sleep(std::time::Duration::from_millis(duration));
    Value::Nil
}

fn now_native(_args: &[Value]) -> Value {
    let now = std::time::SystemTime::now();
    let now = match now.duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_millis(),
        Err(_) => 0,
    };
    Value::Double(now as f64)
}

impl<'opt> VM<'opt> {
    pub(crate) fn new(opt: &'opt Opt) -> Self {
        let mut vm = Self {
            opt,
            frames: Vec::new(),
            heap: Heap::new(opt.log_garbage_collection),
            stack: Stack::new(),
            strings: HashMap::new(),
            open_upvalues: None,
            globals: HashMap::new(),
            bytes_allocated: 0,
            next_gc: 1024 * 1024,
            is_executing: false,
        };
        vm.define_native("clock", NativeFn::new(clock_native));
        vm.define_native("sleep", NativeFn::new(sleep_native));
        vm.define_native("now", NativeFn::new(now_native));

        vm
    }

    pub fn copy_string(&mut self, s: &str) -> Ptr {
        if let Some(v) = self.strings.get(s) {
            return *v;
        }
        self.allocate_string(s.to_string())
    }

    pub fn take_string(&mut self, s: String) -> Ptr {
        if let Some(v) = self.strings.get(&s) {
            return *v;
        }
        self.allocate_string(s)
    }

    fn allocate_string(&mut self, s: String) -> Ptr {
        let ptr = self.allocate_object::<()>(Obj::String(LoxString::new(&s)), None);
        self.strings
            .insert(self.heap.as_string(ptr).string.to_string(), ptr);
        ptr
    }

    pub fn new_function(&mut self, f: Function) -> Ptr {
        self.allocate_object::<()>(Obj::Function(f), None)
    }

    pub fn new_native(&mut self, f: NativeFn) -> Ptr {
        self.allocate_object::<()>(Obj::NativeFn(f), None)
    }

    pub fn new_closure(&mut self, func: Ptr, upvalues: Vec<Ptr>) -> Ptr {
        self.allocate_object::<()>(Obj::Closure(Closure::new(func, upvalues)), None)
    }

    pub fn new_class(&mut self, name: &str) -> Ptr {
        self.allocate_object::<()>(Obj::Class(Class::new(name)), None)
    }

    pub fn new_instance(&mut self, class: &mut Ptr) -> Ptr {
        self.allocate_object(Obj::Instance(Instance::new(*class)), Some(class))
    }

    pub fn new_bound_method(&mut self, receiver: Ptr, closure: Ptr) -> Ptr {
        self.allocate_object::<()>(Obj::BoundMethod(BoundMethod::new(receiver, closure)), None)
    }

    pub fn new_upvalue(&mut self, open: Open, prev_to_rewrite: &mut Option<Ptr>) -> Ptr {
        self.allocate_object(Obj::OpenUpValue(open), prev_to_rewrite.as_mut())
    }

    pub fn allocate_object<R: Rewrite>(
        &mut self,
        mut obj: Obj,
        mut pending_rewrite: Option<R>,
    ) -> Ptr {
        if self.opt.log_garbage_collection {
            eprintln!("allocate for {}", obj.print(&self.heap));
        }

        self.bytes_allocated += std::mem::size_of::<Obj>();
        if self.bytes_allocated > self.next_gc || self.opt.stress_garbage_collector {
            self.collect_garbage(Some((&mut obj, &mut pending_rewrite)));
        }
        self.heap.push(obj)
    }

    fn function(&self) -> &Function {
        self.heap.as_function(self.closure().function)
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
        self.heap.as_closure(self.frame().closure)
    }

    fn read_byte(&mut self) -> &OpCode {
        // NB: this reads by OpCodes, not by bytes. Differs from the book.
        self.frame_mut().ip += 1;
        &self.function().chunk.code[self.frame().ip - 1]
    }

    // Reads a constant from the constants table.
    fn read_constant(&self, index: ConstantIndex) -> Value {
        self.function().chunk.constant_at(index)
    }

    /// Reads a string from the constants table.
    fn read_string(&self, index: ConstantIndex) -> &str {
        let ptr = *self
            .read_constant(index)
            .as_obj_reference()
            .expect("constant index should be a string reference");
        &self.heap.as_string(ptr).string
    }

    fn reset_stack(&mut self) {
        self.stack.clear();
        self.open_upvalues = None;
    }

    fn concatenate(&mut self, s: &str, t: &str) -> Value {
        let mut conc = String::new();
        conc.push_str(s);
        conc.push_str(t);
        Value::ObjReference(self.take_string(conc))
    }
    fn binary_op<R>(
        &mut self,
        op: fn(f64, f64) -> R,
        value_type: fn(R) -> Value,
    ) -> Result<(), InterpretResult> {
        let b = self.stack.pop();
        let a = self.stack.pop();
        match (a, b) {
            (Value::Double(ad), Value::Double(bd)) => {
                self.stack.push(value_type(op(ad, bd)));
                Ok(())
            }
            _ => {
                self.runtime_error("Operands must be numbers.");
                self.stack.push(a);
                self.stack.push(b);
                Err(InterpretResult::RuntimeError)
            }
        }
    }

    fn runtime_error(&mut self, message: &str) {
        eprintln!("{}", message);

        for frame in self.frames.iter().rev() {
            let closure = self.heap.as_closure(frame.closure);
            let func = self.heap.as_function(closure.function);
            let instruction = frame.ip - 1;
            eprintln!("[line {}] in {}", func.chunk.lines[instruction], func.name);
        }

        self.reset_stack();
    }

    fn define_native(&mut self, name: &str, function: NativeFn) {
        debug_assert!(!self.should_run_garbage_collection());
        let string = self.copy_string(name);
        self.heap.deref_mut(string).set_gc_exempt();
        let func_ref = Value::ObjReference(self.new_native(function));

        self.globals.insert(name.to_string(), func_ref);
    }

    fn call_value(&mut self, callee: Value, arg_count: usize) -> bool {
        if let Value::ObjReference(mut ptr) = callee {
            match &self.heap.deref(ptr) {
                Obj::String(_)
                | Obj::Function(_)
                | Obj::OpenUpValue(_)
                | Obj::ClosedUpValue(_)
                | Obj::Instance(_) => {
                    // Fall through to error handling.
                }
                Obj::Closure(_) => {
                    return self.call(ptr, arg_count);
                }
                Obj::NativeFn(native) => {
                    let result = (native.f)(self.stack.top_n(arg_count));
                    self.stack.pop_n(arg_count + 1);
                    self.stack.push(result);
                    return true;
                }
                Obj::Class(_) => {
                    let instance = self.new_instance(&mut ptr);
                    self.stack.assign(
                        self.stack.from_top_slot(arg_count),
                        Value::ObjReference(instance),
                    );

                    if let Some(closure) = self.heap.as_class(ptr).methods.get("init").copied() {
                        return self.call(closure, arg_count);
                    } else if arg_count != 0 {
                        self.runtime_error(&format!("Expected 0 arguments but got {}.", arg_count));
                        return false;
                    }
                    return true;
                }
                Obj::BoundMethod(b) => {
                    let bound_ptr = b.closure;
                    self.stack.assign(
                        self.stack.from_top_slot(arg_count),
                        Value::ObjReference(b.receiver),
                    );
                    return self.call(bound_ptr, arg_count);
                }
            };
        }
        self.runtime_error("Can only call functions and classes.");
        false
    }

    fn invoke_from_class(&mut self, class: Ptr, name: &str, arg_count: usize) -> bool {
        let method = match self.heap.as_class(class).methods.get(name) {
            Some(ptr) => *ptr,
            None => {
                self.runtime_error(&format!("Undefined property '{}'.", name));
                return false;
            }
        };
        self.call(method, arg_count)
    }

    fn invoke(&mut self, name: &str, arg_count: usize) -> bool {
        let receiver = *self
            .stack
            .peek(arg_count)
            .as_obj_reference()
            .expect("receiver stack slot should have been an object reference");
        let (class, field) = match self.heap.deref(receiver).as_instance() {
            Some(i) => (i.class, i.fields.get(name).copied()),
            None => {
                self.runtime_error("Only instances have methods.");
                return false;
            }
        };

        if let Some(value) = field {
            self.stack
                .assign(self.stack.from_top_slot(arg_count), value);
            return self.call_value(value, arg_count);
        }
        self.invoke_from_class(class, name, arg_count)
    }

    fn bind_method(&mut self, class: Ptr, name: &str) -> bool {
        let method = match self.heap.as_class(class).methods.get(name) {
            Some(ptr) => *ptr,
            None => {
                self.runtime_error(&format!("Undefined property '{}'.", name));
                return false;
            }
        };

        let bound = self.new_bound_method(
            *self
                .stack
                .peek(0)
                .as_obj_reference()
                .expect("receiver stack slot should have been an object reference"),
            method,
        );
        self.stack.pop();
        self.stack.push(Value::ObjReference(bound));
        true
    }

    /// Captures the given stack slot as a local upvalue. Inserts the new
    /// upvalue into the linked list of upvalues on the heap, sorted by stack
    /// slot (higher first).
    fn capture_upvalue(&mut self, slot: Slot) -> Ptr {
        let mut prev_upvalue = None;
        let mut next = self.open_upvalues;
        while matches!(next, Some(uv) if self.heap.as_open_up_value(uv).slot > slot) {
            prev_upvalue = next;
            next = self
                .heap
                .as_open_up_value(next.expect("already checked via matches!"))
                .next;
        }

        if matches!(next, Some(ptr) if self.heap.as_open_up_value(ptr).slot == slot) {
            return next.expect("already checked via matches!");
        }

        let created_upvalue = self.new_upvalue(Open::new(slot, next), &mut prev_upvalue);

        if let Some(prev) = prev_upvalue {
            self.heap.as_open_up_value_mut(prev).next = Some(created_upvalue);
        } else {
            self.open_upvalues = Some(created_upvalue);
        }

        created_upvalue
    }

    /// Closes upvalues that point to or above the given stack slot. This
    /// includes removing the upvalue from the open_upvalues linked list.
    fn close_upvalues(&mut self, slot: Slot) {
        while matches!(self.open_upvalues, Some(ptr) if self.heap.as_open_up_value(ptr).slot >= slot)
        {
            let ptr = self.open_upvalues.expect("already checked via matches!");
            let open = self.heap.as_open_up_value(ptr);
            self.open_upvalues = open.next;
            let obj = Obj::ClosedUpValue(Closed::new(self.stack.at(open.slot)));
            self.heap.assign(ptr, obj);
        }
    }

    fn define_method(&mut self, name_ptr: Ptr) {
        let method = *self
            .stack
            .peek(0)
            .as_obj_reference()
            .expect("stack slot should have been a method reference");
        let class = *self
            .stack
            .peek(1)
            .as_obj_reference()
            .expect("stack slot should have been a class reference");
        let name = self.heap.as_string(name_ptr).string.clone();
        let class = self.heap.as_class_mut(class);

        class.methods.insert(name, method);
        self.stack.pop();
    }

    fn call(&mut self, closure_ptr: Ptr, arg_count: usize) -> bool {
        let closure = self.heap.as_closure(closure_ptr);
        let arity = self.heap.as_function(closure.function).arity;
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
            closure_ptr,
            self.stack.from_top_slot(arg_count),
        ));
        true
    }

    fn should_run_garbage_collection(&self) -> bool {
        self.is_executing && !self.opt.disable_garbage_collection
    }

    fn collect_garbage<R: Rewrite>(&mut self, pending_rewrites: Option<(&mut Obj, &mut R)>) {
        if !self.should_run_garbage_collection() {
            return;
        }
        if self.opt.log_garbage_collection {
            eprintln!("-- gc begin");
        }
        let before = self.bytes_allocated;

        self.mark_roots();
        self.heap.trace_references();
        let removed = self.sweep_and_compact(pending_rewrites);

        self.bytes_allocated -= removed * std::mem::size_of::<Obj>();
        self.next_gc = self.bytes_allocated * GC_HEAP_GROWTH_FACTOR;

        if self.opt.log_garbage_collection {
            eprintln!("-- gc end");
            eprintln!(
                "   collected {} bytes ({} objects) ({} to {}), next at {}",
                before - self.bytes_allocated,
                (before - self.bytes_allocated) / std::mem::size_of::<Obj>(),
                before,
                self.bytes_allocated,
                self.next_gc
            );
        }
    }

    fn mark_roots(&mut self) {
        for value in self.stack.iter() {
            self.heap.mark_value(*value);
        }

        for closure in self.frames.iter().map(|f| f.closure) {
            self.heap.mark_object(closure)
        }

        {
            let mut upvalue = self.open_upvalues;
            while let Some(ptr) = upvalue {
                self.heap.mark_object(ptr);
                upvalue = self.heap.as_open_up_value(ptr).next;
            }
        }

        for v in self.globals.values() {
            self.heap.mark_value(*v);
        }

        // Not marking compiler roots, since the compiler doesn't exist after
        // the call to `compile` completes. This implementation has no static
        // state, unlike clox.
    }

    /// Does a sweep & compaction of the heap. Since heap pointers are just
    /// indices, and we're moving objects around, we also have to rewrite
    /// pointers within objects.
    ///
    /// Returns the number of items removed from the heap.
    ///
    /// Differs from the book, since clox doesn't do compaction (since it uses
    /// C's heap, rather than manually managing a separate heap).
    fn sweep_and_compact<R: Rewrite>(
        &mut self,
        pending_rewrites: Option<(&mut Obj, &mut R)>,
    ) -> usize {
        let (mapping, diff) = self.heap.sweep_and_compact();

        // Prune out unused strings from the strings table:
        let reachable_strings = self
            .heap
            .iter()
            .filter_map(|o| o.as_string())
            .map(|ls| &ls.string)
            .collect::<HashSet<_>>();
        self.strings.retain(|s, _| reachable_strings.contains(s));

        // Now apply all the pointer rewriting.
        self.heap.rewrite(&mapping);
        self.stack.rewrite(&mapping);
        self.globals.rewrite(&mapping);
        self.frames.rewrite(&mapping);
        self.strings.rewrite(&mapping);
        self.open_upvalues.rewrite(&mapping);

        if let Some((obj, pending_rewrite)) = pending_rewrites {
            obj.rewrite(&mapping);
            pending_rewrite.rewrite(&mapping);
        }

        debug_assert!(self.check_upvalues());

        diff
    }

    fn open_upvalues_iter(&self) -> OpenUpValueIter {
        OpenUpValueIter {
            heap: &self.heap,
            it: self.open_upvalues,
        }
    }

    fn check_upvalues(&self) -> bool {
        let is_sorted_and_unique = self
            .open_upvalues_iter()
            .tuple_windows()
            .all(|(a, b)| a > b);
        let opens_ll = self.open_upvalues_iter().collect::<HashSet<_>>();

        let opens_heap = self.heap.open_upvalues().collect();

        opens_ll == opens_heap && is_sorted_and_unique
    }

    fn print_stack_slice(&self, label: &str, start: Slot) {
        eprintln!(
            "{}:    {}",
            label,
            self.stack
                .iter_from(start)
                .map(|i| format!("[ {} ]", i.print(&self.heap)))
                .collect::<String>()
        );
    }

    fn run(&mut self) -> Result<(), InterpretResult> {
        loop {
            if self.opt.trace_execution {
                self.print_stack_slice("stack", Slot::new(0));
                self.print_stack_slice("frame", self.frame().start_slot);

                self.function()
                    .chunk
                    .disassemble_instruction(&self.heap, self.frame().ip);

                eprintln!();
            }
            if self.opt.slow_execution {
                std::thread::sleep(std::time::Duration::new(1, 0));
            }

            if self.opt.stress_garbage_collector {
                self.collect_garbage::<()>(None);
            }

            use crate::value::*;
            match &self.read_byte().clone() {
                OpCode::Constant { index } => {
                    let constant = self.read_constant(*index);
                    self.stack.push(constant);
                }
                OpCode::Return => {
                    let result = self.stack.pop();
                    self.close_upvalues(self.frame().start_slot);
                    let finished_frame = self.frames.pop().expect("frames cannot be empty");
                    if self.frames.is_empty() {
                        self.stack.pop();
                        if self.opt.trace_execution {
                            self.print_stack_slice("stack", Slot::new(0));
                        }
                        debug_assert!(self.stack.is_empty());
                        return Ok(());
                    }

                    self.stack.truncate_from(finished_frame.start_slot);
                    self.stack.push(result);
                }
                OpCode::Negate => match self.stack.pop() {
                    Value::Double(d) => self.stack.push(Value::Double(-d)),
                    _ => {
                        self.runtime_error("Operand must be a number.");
                        return Err(InterpretResult::RuntimeError);
                    }
                },
                OpCode::Add => {
                    match (self.stack.peek(0), self.stack.peek(1)) {
                        (Value::Double(b), Value::Double(a)) => {
                            self.stack.pop();
                            self.stack.pop();
                            self.stack.push(Value::Double(a + b));
                            continue;
                        }
                        (Value::ObjReference(i), Value::ObjReference(j)) => {
                            match (&self.heap.deref(i), &self.heap.deref(j)) {
                                (Obj::String(t), Obj::String(s)) => {
                                    // Have to clone here, since adding to the heap
                                    // might invalidate references to s and t.
                                    let (s, t) = (s.string.clone(), t.string.clone());
                                    let val = self.concatenate(&s, &t);
                                    self.stack.pop();
                                    self.stack.pop();
                                    self.stack.push(val);
                                    continue;
                                }
                                (_, _) => {}
                            }
                        }
                        _ => {}
                    };
                    self.runtime_error("Operands must be two numbers or two strings.");
                    return Err(InterpretResult::RuntimeError);
                }
                OpCode::Subtract => self.binary_op(|a, b| a - b, Value::Double)?,
                OpCode::Multiply => self.binary_op(|a, b| a * b, Value::Double)?,
                OpCode::Divide => self.binary_op(|a, b| a / b, Value::Double)?,
                OpCode::Nil => self.stack.push(Value::Nil),
                OpCode::Bool { value } => self.stack.push(Value::Bool(*value)),
                OpCode::Not => {
                    let falsey = self.stack.pop().is_falsey();
                    self.stack.push(Value::Bool(falsey));
                }
                OpCode::Equal => {
                    let b = self.stack.pop();
                    let a = self.stack.pop();
                    self.stack.push(Value::Bool(Value::equal(a, b)));
                }
                OpCode::Greater => self.binary_op(|a, b| a > b, Value::Bool)?,
                OpCode::Less => self.binary_op(|a, b| a < b, Value::Bool)?,
                OpCode::Print => {
                    println!("{}", self.stack.pop().print(&self.heap));
                }
                OpCode::Pop => {
                    self.stack.pop();
                }
                OpCode::DefineGlobal(index) => {
                    let name = self.read_string(*index).to_string();
                    let v = self.stack.pop();
                    self.globals.insert(name, v);
                }
                OpCode::GetGlobal(index) => {
                    let name = self.read_string(*index);
                    if let Some(v) = self.globals.get(name) {
                        self.stack.push(*v);
                    } else {
                        let msg = format!("Undefined variable '{}'.", name);
                        self.runtime_error(&msg);
                        return Err(InterpretResult::RuntimeError);
                    }
                }
                OpCode::SetGlobal(index) => {
                    let name = self.read_string(*index).to_string();
                    let key = match self.globals.entry(name) {
                        std::collections::hash_map::Entry::Occupied(mut o) => {
                            let val = self.stack.peek(0);
                            o.insert(val);
                            continue;
                        }
                        std::collections::hash_map::Entry::Vacant(e) => e.key().to_string(),
                    };
                    self.runtime_error(&format!("Undefined variable '{}'.", key));
                    return Err(InterpretResult::RuntimeError);
                }
                OpCode::SetLocal(slot_offset) => {
                    let slot = self.frame().start_slot.offset(*slot_offset);
                    self.stack.assign(slot, self.stack.peek(0));
                }
                OpCode::GetLocal(slot_offset) => {
                    let value = self.stack.at(self.frame().start_slot.offset(*slot_offset));
                    self.stack.push(value);
                }
                OpCode::JumpIfFalse { distance } => {
                    if self.stack.peek(0).is_falsey() {
                        self.frame_mut().ip += distance;
                    }
                }
                OpCode::Jump { distance } => {
                    self.frame_mut().ip += distance;
                }
                OpCode::Loop {
                    distance_to_loop_start,
                } => {
                    self.frame_mut().ip -= distance_to_loop_start;
                }
                OpCode::Call { arg_count } => {
                    if !self.call_value(self.stack.peek(*arg_count), *arg_count) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
                OpCode::Closure { function, upvalues } => {
                    let function = *self
                        .read_constant(*function)
                        .as_obj_reference()
                        .expect("constant should have been a function reference");
                    let upvalues = upvalues
                        .iter()
                        .map(|uv| match uv {
                            crate::compiler::Upvalue::Local { index } => {
                                self.capture_upvalue(self.frame().start_slot.offset(*index))
                            }
                            crate::compiler::Upvalue::Nonlocal { index } => self
                                .heap
                                .as_closure(self.frame().closure)
                                .upvalue_at(*index),
                        })
                        .collect();
                    let closure = self.new_closure(function, upvalues);
                    self.stack.push(Value::ObjReference(closure));
                }
                OpCode::GetUpvalue(slot) => {
                    let uv = self.closure().upvalue_at(*slot);
                    let val = match &self.heap.deref(uv) {
                        Obj::ClosedUpValue(c) => c.value,
                        Obj::OpenUpValue(o) => self.stack.at(o.slot),
                        _ => unreachable!(),
                    };
                    self.stack.push(val);
                }
                OpCode::SetUpvalue(slot) => {
                    let uv = self.closure().upvalue_at(*slot);
                    let val = self.stack.peek(0);
                    match &mut self.heap.deref_mut(uv) {
                        Obj::ClosedUpValue(c) => c.value = val,
                        Obj::OpenUpValue(o) => self.stack.assign(o.slot, val),
                        _ => unreachable!(),
                    };
                }
                OpCode::CloseUpvalue => {
                    self.close_upvalues(self.stack.top_slot());
                    self.stack.pop();
                }
                OpCode::Class { name } => {
                    let name = self.read_string(*name).to_string();
                    let class = self.new_class(&name);
                    self.stack.push(Value::ObjReference(class));
                }
                OpCode::GetProperty { name } => {
                    match self.stack.peek(0) {
                        Value::ObjReference(instance)
                            if self.heap.deref(instance).as_instance().is_some() =>
                        {
                            let name = self.read_string(*name).to_string();
                            let i = self.heap.as_instance(instance);
                            if let Some(v) = i.fields.get(&name) {
                                self.stack.pop(); // Instance.
                                self.stack.push(*v);
                                continue;
                            }
                            let class = i.class;
                            if !self.bind_method(class, &name) {
                                return Err(InterpretResult::RuntimeError);
                            }
                        }
                        _ => {
                            self.runtime_error("Only instances have properties.");
                            return Err(InterpretResult::RuntimeError);
                        }
                    };
                }
                OpCode::SetProperty { name } => {
                    match self.stack.peek(1) {
                        Value::ObjReference(instance)
                            if self.heap.deref(instance).as_instance().is_some() =>
                        {
                            let name = self.read_string(*name).to_string();
                            let value = self.stack.peek(0);
                            self.heap
                                .as_instance_mut(instance)
                                .fields
                                .insert(name, value);
                            self.stack.pop(); // Value.
                            self.stack.pop(); // Instance.
                            self.stack.push(value);
                        }
                        _ => {
                            self.runtime_error("Only instances have fields.");
                            return Err(InterpretResult::RuntimeError);
                        }
                    }
                }
                OpCode::GetSuper { method } => {
                    let name = self.read_string(*method).to_string();
                    let superclass = *self
                        .stack
                        .pop()
                        .as_obj_reference()
                        .expect("top of stack should have been a class reference");
                    if !self.bind_method(superclass, &name) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
                OpCode::Method { name } => {
                    self.define_method(
                        *self
                            .read_constant(*name)
                            .as_obj_reference()
                            .expect("constant should have been a string reference"),
                    );
                }
                OpCode::Invoke {
                    method_name,
                    arg_count,
                } => {
                    let arg_count = *arg_count;
                    let method = self.read_string(*method_name).to_string();
                    if !self.invoke(&method, arg_count) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
                OpCode::Inherit => {
                    match self.stack.peek(1) {
                        Value::ObjReference(superclass)
                            if self.heap.deref(superclass).as_class().is_some() =>
                        {
                            let superclass_methods = self.heap.as_class(superclass).methods.clone();
                            let subclass = *self
                                .stack
                                .peek(0)
                                .as_obj_reference()
                                .expect("stack top should have been a superclass reference");
                            self.heap
                                .as_class_mut(subclass)
                                .methods
                                .extend(superclass_methods.into_iter());
                            self.stack.pop(); // Subclass.
                        }
                        _ => {
                            self.runtime_error("Superclass must be a class.");
                            return Err(InterpretResult::RuntimeError);
                        }
                    }
                }
                OpCode::SuperInvoke { method, arg_count } => {
                    let arg_count = *arg_count;
                    let method = self.read_string(*method).to_string();
                    let superclass = *self
                        .stack
                        .pop()
                        .as_obj_reference()
                        .expect("stack top should have been a superclass reference");
                    if !self.invoke_from_class(superclass, &method, arg_count) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
            }
        }
    }

    pub fn interpret(&mut self, source: &str) -> Result<(), InterpretResult> {
        match Compiler::new(self.opt, source, self).compile() {
            Some(function) => {
                let function = self.new_function(function);
                self.stack.push(Value::ObjReference(function));
                let closure = self.new_closure(function, Vec::new());
                self.stack.pop();
                self.stack.push(Value::ObjReference(closure));
                self.call(closure, 0);
            }
            None => {
                return Err(InterpretResult::CompileError);
            }
        };

        if self.opt.compile_only {
            return Ok(());
        }

        self.is_executing = true;
        let result = self.run();
        self.is_executing = false;
        result
    }
}

struct CallFrame {
    closure: Ptr,
    // Offset into function.chunk.code.
    ip: usize,
    // The first stack slot that belongs to this frame.
    start_slot: Slot,
}

impl CallFrame {
    fn new(closure: Ptr, start_slot: Slot) -> Self {
        Self {
            closure,
            ip: 0,
            start_slot,
        }
    }
}

impl Rewrite for CallFrame {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.closure.rewrite(mapping);
    }
}

struct OpenUpValueIter<'h> {
    heap: &'h Heap,
    it: Option<Ptr>,
}

impl<'h> Iterator for OpenUpValueIter<'h> {
    type Item = Ptr;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.it;
        if let Some(ptr) = self.it {
            self.it = self.heap.as_open_up_value(ptr).next;
        }
        cur
    }
}
