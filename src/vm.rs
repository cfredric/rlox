use std::collections::{HashMap, HashSet};

use crate::chunk::{ConstantIndex, OpCodeIndex};
use crate::compiler::{compile, CompiledUpValue};
use crate::heap::{Heap, Ptr};
use crate::obj::{
    BoundMethod, Class, Closed, Closure, Function, Instance, LoxString, NativeFn, Obj,
    ObjWithContext, Open,
};
use crate::opcode::OpCode;
use crate::opt::Opt;
use crate::post_process_gc_sweep::{GcSweepData, PostProcessGcSweep};
use crate::stack::{Slot, Stack};
use crate::value::{Value, ValueWithContext};

const GC_HEAP_GROWTH_FACTOR: usize = 2;

/// A bytecode Virtual Machine that can compile and interpret source code,
/// either line-by-line as a REPL, or as a single whole script.
pub(crate) struct VM<'opt> {
    /// Configuration options.
    opt: &'opt Opt,

    /// Stack frames.
    frames: Vec<CallFrame>,

    /// The heap, for storing dynamically-allocated objects.
    pub(crate) heap: Heap<'opt>,
    /// The value stack.
    stack: Stack,
    /// Values are pointers into the heap, to LoxStrings.
    strings: HashMap<String, Ptr>,
    /// open_upvalues is a pointer into the heap, to the head of the linked list
    /// of upvalue objects.
    open_upvalues: Option<Ptr>,
    globals: HashMap<String, Value>,

    next_gc: usize,
    /// Hack: we don't do garbage collection until we start executing. Differs from the book.
    is_executing: bool,

    mode: Mode,
}

const MAX_FRAMES: usize = 1024;

pub(crate) enum InterpretResult {
    CompileError,
    RuntimeError,
}

mod ffi {
    extern "C" {
        pub(crate) fn clock() -> libc::clock_t;
    }
}

fn clock_native<'opt>(_: &mut VM<'opt>, _: &mut Ptr, _args: &[Value]) -> Value {
    let t = unsafe { ffi::clock() };
    Value::Double(t as f64 / 1_000_000_f64)
}

fn sleep_native<'opt>(_: &mut VM<'opt>, _: &mut Ptr, args: &[Value]) -> Value {
    if let Some(Value::Double(d)) = args.get(0) {
        std::thread::sleep(std::time::Duration::from_millis(d.floor() as u64));
    }

    Value::Nil
}

fn now_native<'opt>(_: &mut VM<'opt>, _: &mut Ptr, _args: &[Value]) -> Value {
    let now = std::time::SystemTime::now();
    let now = match now.duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_millis(),
        Err(_) => 0,
    };
    Value::Double(now as f64)
}

fn atoi_native<'opt>(vm: &mut VM<'opt>, ptr: &mut Ptr, args: &[Value]) -> Value {
    if let Some(Value::Double(d)) = args.get(0) {
        return Value::ObjReference(vm.take_string(format!("{}", d), ptr));
    }
    Value::Nil
}

fn itoa_native<'opt>(vm: &mut VM<'opt>, _pending: &mut Ptr, args: &[Value]) -> Value {
    if let Some(Value::ObjReference(ptr)) = args.get(0) {
        if let Some(LoxString { string, .. }) = vm.heap[ptr].as_string() {
            if let Ok(d) = string.parse::<f64>() {
                return Value::Double(d);
            }
        }
    }

    Value::Nil
}

impl<'opt> VM<'opt> {
    pub(crate) fn new(opt: &'opt Opt, mode: Mode) -> Self {
        let mut vm = Self {
            opt,
            frames: Vec::new(),
            heap: Heap::new(opt),
            stack: Stack::new(),
            strings: HashMap::new(),
            open_upvalues: None,
            globals: HashMap::new(),
            next_gc: 1024 * 1024,
            is_executing: false,
            mode,
        };
        vm.define_native("clock", NativeFn::new(clock_native));
        vm.define_native("sleep", NativeFn::new(sleep_native));
        vm.define_native("now", NativeFn::new(now_native));
        vm.define_native("atoi", NativeFn::new(atoi_native));
        vm.define_native("itoa", NativeFn::new(itoa_native));

        vm
    }

    pub(crate) fn take_string<R: PostProcessGcSweep>(&mut self, s: String, pending: R) -> Ptr {
        if let Some(v) = self.strings.get(&s) {
            v.clone()
        } else {
            self.allocate_string(s, pending)
        }
    }

    fn allocate_string<R: PostProcessGcSweep>(&mut self, s: String, pending: R) -> Ptr {
        let ptr = self.allocate_object(Obj::String(LoxString::new(s.clone())), pending);
        self.strings.insert(s, ptr.clone());
        ptr
    }

    pub(crate) fn new_function(&mut self, f: Function) -> Ptr {
        self.allocate_object(Obj::Function(f), ())
    }

    pub(crate) fn new_native(&mut self, f: NativeFn) -> Ptr {
        self.allocate_object(Obj::NativeFn(f), ())
    }

    pub(crate) fn new_closure(&mut self, func: Ptr, upvalues: Vec<Ptr>) -> Ptr {
        self.allocate_object(Obj::Closure(Closure::new(func, upvalues)), ())
    }

    pub(crate) fn new_class(&mut self, name: &str) -> Ptr {
        self.allocate_object(Obj::Class(Class::new(name)), ())
    }

    pub(crate) fn new_instance<R: PostProcessGcSweep>(&mut self, class: Ptr, pending: R) -> Ptr {
        self.allocate_object(Obj::Instance(Instance::new(class)), pending)
    }

    pub(crate) fn new_bound_method(&mut self, receiver: Ptr, closure: Ptr) -> Ptr {
        self.allocate_object(Obj::BoundMethod(BoundMethod::new(receiver, closure)), ())
    }

    pub(crate) fn new_upvalue<R: PostProcessGcSweep>(&mut self, open: Open, pending: R) -> Ptr {
        self.allocate_object(Obj::OpenUpValue(open), pending)
    }

    fn allocate_object<R: PostProcessGcSweep>(&mut self, mut obj: Obj, pending: R) -> Ptr {
        if self.opt.log_garbage_collection {
            eprintln!("allocate for {}", ObjWithContext::new(&obj, &self.heap));
        }

        if self.allocation_would_cause_gc() {
            self.collect_garbage((&mut obj, pending));
        }
        self.heap.push(obj)
    }

    fn allocation_would_cause_gc(&self) -> bool {
        self.opt.stress_garbage_collector
            || self.heap.bytes_allocated() + std::mem::size_of::<Obj>() > self.next_gc
    }

    fn function(&self) -> &Function {
        self.heap.as_function(&self.closure().function)
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
        self.heap.as_closure(&self.frame().closure)
    }

    fn read_byte(&mut self) -> &OpCode {
        // NB: this reads by OpCodes, not by bytes. Differs from the book.
        self.frame_mut().ip.increment();
        &self.function().chunk[self.frame().ip - 1]
    }

    // Reads a constant from the constants table.
    fn read_constant(&self, index: ConstantIndex) -> Value {
        self.function().chunk[index].clone()
    }

    /// Reads a string from the constants table.
    fn read_string(&self, index: ConstantIndex) -> &str {
        let val = self.read_constant(index);
        let ptr = val
            .as_obj_reference()
            .expect("constant index should be a string reference");
        &self.heap.as_string(ptr).string
    }

    fn concatenate(&mut self, s: &str, t: &str) -> Value {
        Value::ObjReference(self.take_string(format!("{}{}", s, t), ()))
    }

    fn binary_op(&mut self, op: fn(f64, f64) -> Value) -> Result<(), InterpretResult> {
        let b = self.stack.pop();
        let a = self.stack.pop();
        match (a, b) {
            (Value::Double(ad), Value::Double(bd)) => {
                self.stack.push(op(ad, bd));
                Ok(())
            }
            _ => self.runtime_error("Operands must be numbers."),
        }
    }

    fn runtime_error(&mut self, message: &str) -> Result<(), InterpretResult> {
        eprintln!("{}", message);

        for frame in self.frames.iter().rev() {
            let closure = self.heap.as_closure(&frame.closure);
            let func = self.heap.as_function(&closure.function);
            let instruction = frame.ip - 1;
            eprintln!(
                "[line {}] in {}",
                func.chunk.line_of(instruction),
                func.name
            );
        }

        self.stack.clear();
        self.open_upvalues = None;

        Err(InterpretResult::RuntimeError)
    }

    fn define_native(&mut self, name: &str, function: NativeFn) {
        debug_assert!(!self.should_run_garbage_collection());
        let func_ref = Value::ObjReference(self.new_native(function));

        self.globals.insert(name.to_string(), func_ref);
    }

    fn call_value(&mut self, callee: &Value, arg_count: usize) -> Result<(), InterpretResult> {
        if let Value::ObjReference(ptr) = callee {
            match &self.heap[ptr] {
                Obj::Dummy => unreachable!(),
                Obj::String(_)
                | Obj::Function(_)
                | Obj::OpenUpValue(_)
                | Obj::ClosedUpValue(_)
                | Obj::Instance(_) => self.runtime_error("Can only call functions and classes."),
                Obj::Closure(_) => self.call(ptr, arg_count),
                Obj::NativeFn(native) => {
                    let mut ptr = ptr.clone();
                    let args = self.stack.top_n(arg_count).to_vec();
                    let result = (native.f)(self, &mut ptr, &*args);
                    self.stack.pop_n(arg_count + 1);
                    self.stack.push(result);
                    Ok(())
                }
                Obj::Class(_) => {
                    let mut ptr = ptr.clone();
                    let instance = self.new_instance(ptr.clone(), &mut ptr);
                    let instance_slot = self.stack.offset_from_top_slot(arg_count);
                    self.stack[instance_slot] = Value::ObjReference(instance);

                    if let Some(closure) = self.heap.as_class(&ptr).methods.get("init").cloned() {
                        self.call(&closure, arg_count)
                    } else if arg_count != 0 {
                        self.runtime_error(&format!("Expected 0 arguments but got {}.", arg_count))
                    } else {
                        Ok(())
                    }
                }
                Obj::BoundMethod(b) => {
                    let bound_ptr = b.closure.clone();
                    let slot = self.stack.offset_from_top_slot(arg_count);
                    self.stack[slot] = Value::ObjReference(b.receiver.clone());
                    self.call(&bound_ptr, arg_count)
                }
            }
        } else {
            self.runtime_error("Can only call functions and classes.")
        }
    }

    fn invoke_from_class(
        &mut self,
        class: &Ptr,
        name: &str,
        arg_count: usize,
    ) -> Result<(), InterpretResult> {
        match self.heap.as_class(class).methods.get(name) {
            Some(ptr) => {
                let ptr = ptr.clone();
                self.call(&ptr, arg_count)
            }
            None => self.runtime_error(&format!("Undefined property '{}'.", name)),
        }
    }

    fn invoke(&mut self, name: &str, arg_count: usize) -> Result<(), InterpretResult> {
        let receiver = self.stack.peek(arg_count);
        let receiver = match receiver.as_obj_reference() {
            Some(ptr) => ptr,
            None => {
                return self.runtime_error("Method receivers must be objects.");
            }
        };
        let (class, field) = match self.heap[receiver].as_instance() {
            Some(i) => (&i.class, i.fields.get(name).cloned()),
            None => {
                return self.runtime_error("Only instances have methods.");
            }
        };

        if let Some(value) = field {
            let slot = self.stack.offset_from_top_slot(arg_count);
            self.stack[slot] = value.clone();
            self.call_value(&value, arg_count)
        } else {
            let class = class.clone();
            self.invoke_from_class(&class, name, arg_count)
        }
    }

    fn bind_method(&mut self, class: &Ptr, name: &str) -> Result<(), InterpretResult> {
        let method = match self.heap.as_class(class).methods.get(name) {
            Some(ptr) => ptr.clone(),
            None => {
                return self.runtime_error(&format!("Undefined property '{}'.", name));
            }
        };

        let bound = self.new_bound_method(
            self.stack
                .peek(0)
                .as_obj_reference()
                .expect("receiver stack slot should have been an object reference")
                .clone(),
            method,
        );
        self.stack.pop();
        self.stack.push(Value::ObjReference(bound));
        Ok(())
    }

    /// Captures the given stack slot as a local upvalue. Inserts the new
    /// upvalue into the linked list of upvalues on the heap, sorted by stack
    /// slot (higher first).
    fn capture_upvalue<R: PostProcessGcSweep>(&mut self, slot: Slot, pending: R) -> Ptr {
        let mut prev_upvalue = None;
        let mut next = self.open_upvalues.as_ref();
        while matches!(next, Some(uv) if self.heap.as_open_up_value(uv).slot > slot) {
            prev_upvalue = next;
            next = self
                .heap
                .as_open_up_value(next.expect("already checked via matches!"))
                .next
                .as_ref();
        }
        let mut prev_upvalue = prev_upvalue.cloned();

        if matches!(next, Some(ptr) if self.heap.as_open_up_value(ptr).slot == slot) {
            return next.expect("already checked via matches!").clone();
        }

        let next = next.cloned();
        let created_upvalue =
            self.new_upvalue(Open::new(slot, next), (prev_upvalue.as_mut(), pending));

        if let Some(prev) = prev_upvalue {
            self.heap.as_open_up_value_mut(&prev).next = Some(created_upvalue.clone());
        } else {
            self.open_upvalues = Some(created_upvalue.clone());
        }

        created_upvalue
    }

    /// Closes upvalues that point to or above the given stack slot. This
    /// includes removing the upvalue from the open_upvalues linked list.
    fn close_upvalues(&mut self, slot: Slot) {
        while matches!(self.open_upvalues.as_ref(), Some(ptr) if self.heap.as_open_up_value(ptr).slot >= slot)
        {
            let ptr = self
                .open_upvalues
                .take()
                .expect("already checked via matches!");
            let open = self.heap.as_open_up_value(&ptr);
            self.open_upvalues = open.next.clone();
            // TODO: We really ought to not need to clone these stack values,
            // since we're about to pop them anyway.
            self.heap[&ptr] = Obj::ClosedUpValue(Closed::new(self.stack[open.slot].clone()));
        }
    }

    fn define_method(&mut self, name_ptr: &Ptr) {
        let method = self
            .stack
            .peek(0)
            .as_obj_reference()
            .expect("stack slot should have been a method reference");
        let class = self
            .stack
            .peek(1)
            .as_obj_reference()
            .expect("stack slot should have been a class reference");
        let name = self.heap.as_string(name_ptr).string.clone();
        let class = self.heap.as_class_mut(class);

        class.methods.insert(name, method.clone());
        self.stack.pop();
    }

    fn call(&mut self, closure_ptr: &Ptr, arg_count: usize) -> Result<(), InterpretResult> {
        let closure = self.heap.as_closure(closure_ptr);
        let arity = self.heap.as_function(&closure.function).arity;
        if arg_count != arity {
            return self.runtime_error(&format!(
                "Expected {} arguments but got {}.",
                arity, arg_count
            ));
        }

        if self.frames.len() == MAX_FRAMES {
            return self.runtime_error("Stack overflow.");
        }

        self.frames.push(CallFrame::new(
            closure_ptr.clone(),
            self.stack.offset_from_top_slot(arg_count),
        ));
        Ok(())
    }

    fn should_run_garbage_collection(&self) -> bool {
        self.is_executing && !self.opt.disable_garbage_collection
    }

    fn collect_garbage<R: PostProcessGcSweep>(&mut self, pending: R) {
        if !self.should_run_garbage_collection() {
            return;
        }
        if self.opt.log_garbage_collection {
            eprintln!("-- gc begin");
        }
        let before = self.heap.bytes_allocated();

        self.mark_roots();
        self.heap.trace_references();
        self.sweep_and_compact(pending);

        let after = self.heap.bytes_allocated();
        self.next_gc = after * GC_HEAP_GROWTH_FACTOR;

        if self.opt.log_garbage_collection {
            eprintln!("-- gc end");
            eprintln!(
                "   collected {} bytes ({} objects) ({} to {}), next at {}",
                before - after,
                (before - after) / std::mem::size_of::<Obj>(),
                before,
                after,
                self.next_gc
            );
        }
    }

    fn mark_roots(&mut self) {
        for value in self.stack.iter() {
            self.heap.mark_value(value);
        }

        for closure in self.frames.iter().map(|f| f.closure.clone()) {
            self.heap.mark_object(&closure)
        }

        {
            let mut upvalue = self.open_upvalues.clone();
            while let Some(ptr) = upvalue {
                self.heap.mark_object(&ptr);
                upvalue = self.heap.as_open_up_value(&ptr).next.clone();
            }
        }

        for v in self.globals.values() {
            self.heap.mark_value(v);
        }

        // Not marking compiler roots, since the compiler doesn't exist after
        // the call to `compile` completes. This implementation has no static
        // state, unlike clox.
    }

    /// Does a sweep & compaction of the heap. Since heap pointers are just
    /// indices, and we're moving objects around, we also have to fix up
    /// pointers within objects.
    ///
    /// Returns the number of items removed from the heap.
    ///
    /// Differs from the book, since clox doesn't do compaction (since it uses
    /// C's heap, rather than manually managing a separate heap).
    fn sweep_and_compact<R: PostProcessGcSweep>(&mut self, mut pending: R) {
        let sweep_data = self.heap.sweep_and_compact();

        // Prune out unused strings from the strings table:
        let reachable_strings = self
            .heap
            .iter()
            .filter_map(|o| o.as_string())
            .map(|ls| &ls.string)
            .collect::<HashSet<_>>();
        self.strings.retain(|s, _| reachable_strings.contains(s));

        // Now apply all the pointer rewriting.
        self.heap.process(&sweep_data);
        self.stack.process(&sweep_data);
        self.globals.process(&sweep_data);
        self.frames.process(&sweep_data);
        self.strings.process(&sweep_data);
        self.open_upvalues.process(&sweep_data);

        pending.process(&sweep_data);

        debug_assert!(self.check_upvalues());
    }

    fn open_upvalues_iter(&self) -> OpenUpValueIter {
        OpenUpValueIter {
            heap: &self.heap,
            it: self.open_upvalues.clone(),
        }
    }

    fn check_upvalues(&self) -> bool {
        use itertools::Itertools;
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
                .map(|i| format!("[ {} ]", ValueWithContext::new(i, &self.heap)))
                .collect::<String>()
        );
    }

    fn run(&mut self) -> Result<(), InterpretResult> {
        loop {
            if self.opt.trace_execution {
                self.print_stack_slice("stack", Slot::bottom());
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
                self.collect_garbage(());
            }

            use crate::value::*;
            match &self.read_byte().clone() {
                OpCode::Constant { index } => {
                    let constant = self.read_constant(*index);
                    self.stack.push(constant);
                }
                OpCode::Return => {
                    let result = self.stack.pop();
                    let finished_frame = self.frames.pop().expect("frames cannot be empty");
                    self.close_upvalues(finished_frame.start_slot);
                    if self.frames.is_empty() {
                        let top = self.stack.pop();
                        if !self.stack.is_empty() {
                            debug_assert!(self.mode == Mode::Repl);
                            println!("{}", ValueWithContext::new(&top, &self.heap));
                            self.stack.pop();
                        }
                        if self.opt.trace_execution {
                            self.print_stack_slice("stack", Slot::bottom());
                        }
                        debug_assert!(self.stack.is_empty());
                        return Ok(());
                    }

                    self.stack.truncate_from(finished_frame.start_slot);
                    self.stack.push(result);
                }
                OpCode::Negate => match self.stack.pop() {
                    Value::Double(d) => self.stack.push(Value::Double(-d)),
                    _ => self.runtime_error("Operand must be a number.")?,
                },
                OpCode::Add => {
                    match (self.stack.peek(0), self.stack.peek(1)) {
                        (Value::Double(b), Value::Double(a)) => {
                            let a = *a;
                            let b = *b;
                            self.stack.pop();
                            self.stack.pop();
                            self.stack.push(Value::Double(a + b));
                        }
                        (Value::ObjReference(i), Value::ObjReference(j)) => {
                            match (&self.heap[i], &self.heap[j]) {
                                (Obj::String(t), Obj::String(s)) => {
                                    // Have to clone here, since adding to the heap
                                    // might invalidate references to s and t.
                                    let (s, t) = (s.string.clone(), t.string.clone());
                                    let val = self.concatenate(&s, &t);
                                    self.stack.pop();
                                    self.stack.pop();
                                    self.stack.push(val);
                                }
                                _ => self.runtime_error(
                                    "Operands must be two numbers or two strings.",
                                )?,
                            }
                        }
                        _ => self.runtime_error("Operands must be two numbers or two strings.")?,
                    }
                }
                OpCode::Subtract => self.binary_op(|a, b| Value::Double(a - b))?,
                OpCode::Multiply => self.binary_op(|a, b| Value::Double(a * b))?,
                OpCode::Divide => self.binary_op(|a, b| Value::Double(a / b))?,
                OpCode::Nil => self.stack.push(Value::Nil),
                OpCode::Bool { value } => self.stack.push(Value::Bool(*value)),
                OpCode::Not => {
                    let falsey = self.stack.pop().is_falsey();
                    self.stack.push(Value::Bool(falsey));
                }
                OpCode::Equal => {
                    let b = self.stack.pop();
                    let a = self.stack.pop();
                    self.stack.push(Value::Bool(Value::equals(a, b)));
                }
                OpCode::Greater => self.binary_op(|a, b| Value::Bool(a > b))?,
                OpCode::Less => self.binary_op(|a, b| Value::Bool(a < b))?,
                OpCode::Print => {
                    println!("{}", ValueWithContext::new(&self.stack.pop(), &self.heap));
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
                        self.stack.push(v.clone());
                    } else {
                        let msg = format!("Undefined variable '{}'.", name);
                        self.runtime_error(&msg)?;
                    }
                }
                OpCode::SetGlobal(index) => {
                    let name = self.read_string(*index).to_string();
                    match self.globals.entry(name) {
                        std::collections::hash_map::Entry::Occupied(mut o) => {
                            o.insert(self.stack.peek(0).clone());
                        }
                        std::collections::hash_map::Entry::Vacant(e) => {
                            let key = e.key().to_string();
                            self.runtime_error(&format!("Undefined variable '{}'.", key))?;
                        }
                    }
                }
                OpCode::SetLocal(slot_offset) => {
                    let slot = self.frame().start_slot.offset(*slot_offset);
                    self.stack[slot] = self.stack.peek(0).clone();
                }
                OpCode::GetLocal(slot_offset) => {
                    let value = self.stack[self.frame().start_slot.offset(*slot_offset)].clone();
                    self.stack.push(value);
                }
                OpCode::JumpIfFalse { distance } => {
                    if self.stack.peek(0).is_falsey() {
                        self.frame_mut().ip += *distance;
                    }
                }
                OpCode::Jump { distance } => {
                    self.frame_mut().ip += *distance;
                }
                OpCode::Call { arg_count } => {
                    let arg_count = *arg_count;
                    let callee = self.stack.peek(arg_count).clone();
                    self.call_value(&callee, arg_count)?
                }
                OpCode::Closure { function, upvalues } => {
                    let mut function = self
                        .read_constant(*function)
                        .as_obj_reference()
                        .expect("constant should have been a function reference")
                        .clone();
                    let uvs = {
                        let mut uvs = vec![];
                        for uv in upvalues {
                            let new_uv_ptr = match uv {
                                CompiledUpValue::Local { index } => self.capture_upvalue(
                                    self.frame().start_slot.offset(*index),
                                    (&mut uvs, &mut function),
                                ),
                                CompiledUpValue::Nonlocal { index } => self
                                    .heap
                                    .as_closure(&self.frame().closure)
                                    .upvalue_at(*index)
                                    .clone(),
                            };
                            uvs.push(new_uv_ptr);
                        }
                        uvs
                    };
                    let closure = self.new_closure(function, uvs);
                    self.stack.push(Value::ObjReference(closure));
                }
                OpCode::GetUpvalue(slot) => {
                    let uv = self.closure().upvalue_at(*slot);
                    let val = match &self.heap[uv] {
                        Obj::ClosedUpValue(c) => c.value.clone(),
                        Obj::OpenUpValue(o) => self.stack[o.slot].clone(),
                        _ => unreachable!(),
                    };
                    self.stack.push(val);
                }
                OpCode::SetUpvalue(slot) => {
                    let uv = self.closure().upvalue_at(*slot).clone();
                    let val = self.stack.peek(0).clone();
                    match &mut self.heap[&uv] {
                        Obj::ClosedUpValue(c) => c.value = val,
                        Obj::OpenUpValue(o) => self.stack[o.slot] = val,
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
                            if self.heap[instance].as_instance().is_some() =>
                        {
                            let name = self.read_string(*name);
                            let i = self.heap.as_instance(instance);
                            if let Some(v) = i.fields.get(name) {
                                self.stack.pop(); // Instance.
                                self.stack.push(v.clone());
                            } else {
                                let class = i.class.clone();
                                let name = name.to_string();
                                self.bind_method(&class, &name)?
                            }
                        }
                        _ => self.runtime_error("Only instances have properties.")?,
                    };
                }
                OpCode::SetProperty { name } => {
                    match self.stack.peek(1) {
                        Value::ObjReference(instance)
                            if self.heap[instance].as_instance().is_some() =>
                        {
                            let name = self.read_string(*name).to_string();
                            let value = self.stack.peek(0).clone();
                            self.heap
                                .as_instance_mut(instance)
                                .fields
                                .insert(name, value.clone());
                            self.stack.pop(); // Value.
                            self.stack.pop(); // Instance.
                            self.stack.push(value);
                        }
                        _ => self.runtime_error("Only instances have fields.")?,
                    }
                }
                OpCode::GetSuper { method } => {
                    let name = self.read_string(*method).to_string();
                    let superclass = self
                        .stack
                        .pop()
                        .as_obj_reference()
                        .expect("top of stack should have been a class reference")
                        .clone();
                    self.bind_method(&superclass, &name)?
                }
                OpCode::Method { name } => {
                    self.define_method(
                        self.read_constant(*name)
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
                    self.invoke(&method, arg_count)?
                }
                OpCode::Inherit => {
                    match self.stack.peek(1) {
                        Value::ObjReference(superclass)
                            if self.heap[superclass].as_class().is_some() =>
                        {
                            let superclass_methods = self.heap.as_class(superclass).methods.clone();
                            let subclass = self
                                .stack
                                .peek(0)
                                .as_obj_reference()
                                .expect("stack top should have been a subclass reference")
                                .clone();
                            self.heap
                                .as_class_mut(&subclass)
                                .methods
                                .extend(superclass_methods.into_iter());
                            self.stack.pop(); // Subclass.
                        }
                        _ => self.runtime_error("Superclass must be a class.")?,
                    }
                }
                OpCode::SuperInvoke { method, arg_count } => {
                    let arg_count = *arg_count;
                    let method = self.read_string(*method).to_string();
                    let superclass = self
                        .stack
                        .pop()
                        .as_obj_reference()
                        .expect("stack top should have been a superclass reference")
                        .clone();
                    self.invoke_from_class(&superclass, &method, arg_count)?
                }
            }
        }
    }

    pub(crate) fn interpret(&mut self, source: &str) -> Result<(), InterpretResult> {
        match compile(
            self.opt,
            crate::scanner::Scanner::new(source),
            self,
            self.mode,
        ) {
            Some(function) => {
                let function = self.new_function(function);
                self.stack.push(Value::ObjReference(function.clone()));
                let closure = self.new_closure(function, Vec::new());
                self.stack.pop();
                self.stack.push(Value::ObjReference(closure.clone()));
                self.call(&closure, 0)?;
            }
            None => return Err(InterpretResult::CompileError),
        };

        if self.opt.compile_only {
            return Ok(());
        }

        debug_assert!(self.heap.len() > 0);

        self.is_executing = true;
        let result = self.run();
        self.is_executing = false;
        result
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Mode {
    Repl,
    Script,
}

#[derive(Debug)]
struct CallFrame {
    closure: Ptr,
    // Offset into function.chunk.code.
    ip: OpCodeIndex,
    // The first stack slot that belongs to this frame.
    start_slot: Slot,
}

impl CallFrame {
    fn new(closure: Ptr, start_slot: Slot) -> Self {
        Self {
            closure,
            ip: OpCodeIndex::zero(),
            start_slot,
        }
    }
}

impl PostProcessGcSweep for CallFrame {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.closure.process(sweep_data);
    }
}

struct OpenUpValueIter<'h, 'opt> {
    heap: &'h Heap<'opt>,
    it: Option<Ptr>,
}

impl<'h, 'opt> Iterator for OpenUpValueIter<'h, 'opt> {
    type Item = Ptr;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.it.clone();
        if let Some(ptr) = self.it.take() {
            self.it = self.heap.as_open_up_value(&ptr).next.clone();
        }
        cur
    }
}
