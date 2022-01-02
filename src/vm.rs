use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::chunk::OpCode;
use crate::compiler::Compiler;
use crate::obj::{
    BoundMethod, Class, Closed, Closure, Function, Instance, LoxString, NativeFn, Obj, Open,
};
use crate::print::Print;
use crate::rewrite::Rewrite;
use crate::value::Value;
use crate::Opt;

const GC_HEAP_GROWTH_FACTOR: usize = 2;
const INIT_STR: &str = "init";

pub struct VM<'opt> {
    opt: &'opt Opt,

    frames: Vec<CallFrame>,

    pub heap: Heap,
    stack: Stack,
    /// Values are pointers into the heap, to LoxStrings.
    pub strings: HashMap<String, usize>,
    /// open_upvalues is a pointer into the heap, to the head of the linked list
    /// of upvalue objects.
    open_upvalues: Option<usize>,
    globals: HashMap<String, Value>,

    bytes_allocated: usize,
    next_gc: usize,
    /// Hack: we don't do garbage collection during compilation, since we don't
    /// have visibility into the compiler's data structures and therefore can't
    /// trace the roots it is in the process of adding.
    is_compiling: bool,
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
            is_compiling: false,
        };
        vm.define_native("clock", NativeFn::new(clock_native));
        vm.define_native("sleep", NativeFn::new(sleep_native));
        vm.define_native("now", NativeFn::new(now_native));

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
        let idx = self.allocate_object::<usize>(Obj::String(LoxString::new(&s)), None);
        self.strings
            .insert(self.heap.as_string(idx).string.to_string(), idx);
        idx
    }

    pub fn new_function(&mut self, f: Function) -> usize {
        self.allocate_object::<usize>(Obj::Function(f), None)
    }

    pub fn new_native(&mut self, f: NativeFn) -> usize {
        self.allocate_object::<usize>(Obj::NativeFn(f), None)
    }

    pub fn new_closure(&mut self, func_index: usize, upvalues: Vec<usize>) -> usize {
        self.allocate_object::<usize>(Obj::Closure(Closure::new(func_index, upvalues)), None)
    }

    pub fn new_class(&mut self, name: &str) -> usize {
        self.allocate_object::<usize>(Obj::Class(Class::new(name)), None)
    }

    pub fn new_instance(&mut self, class_index: &mut usize) -> usize {
        let instance = self.allocate_object(
            Obj::Instance(Instance::new(*class_index)),
            Some(class_index),
        );
        instance
    }

    pub fn new_bound_method(&mut self, receiver: usize, closure_idx: usize) -> usize {
        self.allocate_object::<usize>(
            Obj::BoundMethod(BoundMethod::new(receiver, closure_idx)),
            None,
        )
    }

    pub fn new_upvalue(&mut self, open: Open, prev_to_rewrite: &mut Option<usize>) -> usize {
        self.allocate_object(Obj::OpenUpValue(open), prev_to_rewrite.as_mut())
    }

    pub fn allocate_object<R: Rewrite>(
        &mut self,
        mut obj: Obj,
        mut pending_rewrite: Option<R>,
    ) -> usize {
        if self.opt.log_garbage_collection {
            eprintln!("allocate for {}", obj.print(&self.heap));
        }

        self.bytes_allocated += std::mem::size_of::<Obj>();
        if self.bytes_allocated > self.next_gc || self.opt.stress_garbage_collector {
            self.collect_garbage(Some((&mut obj, &mut pending_rewrite)));
        }
        self.heap.heap.push(obj);
        self.heap.heap.len() - 1
    }

    fn function(&self) -> &Function {
        self.heap.as_function(self.closure().function_index)
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
        self.heap.as_closure(self.frame().heap_index)
    }

    fn read_byte(&mut self) -> &OpCode {
        // NB: this reads by OpCodes, not by bytes. Differs from the book.
        self.frame_mut().ip += 1;
        &self.function().chunk.code[self.frame().ip - 1]
    }

    // Reads a constant from the constants table.
    fn read_constant(&self, offset: usize) -> Value {
        self.function().chunk.constants[offset]
    }

    /// Reads a string from the constants table.
    fn read_string(&self, offset: usize) -> &str {
        let heap_idx = *self.read_constant(offset).as_obj_index().unwrap();
        &self.heap.as_string(heap_idx).string
    }

    fn reset_stack(&mut self) {
        self.stack.stack.clear();
        self.open_upvalues = None;
    }

    fn concatenate(&mut self, s: &str, t: &str) -> Value {
        let mut conc = String::new();
        conc.push_str(s);
        conc.push_str(t);
        Value::ObjIndex(self.take_string(conc))
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
            let closure = self.heap.as_closure(frame.heap_index);
            let func = self.heap.as_function(closure.function_index);
            let instruction = frame.ip - 1;
            eprintln!("[line {}] in {}", func.chunk.lines[instruction], func.name);
        }

        self.reset_stack();
    }

    fn define_native(&mut self, name: &str, function: NativeFn) {
        let index = self.copy_string(name);
        self.heap.heap[index].set_gc_exempt();
        let index = Value::ObjIndex(index);
        self.stack.push(index);
        let index = Value::ObjIndex(self.new_native(function));
        self.stack.push(index);

        let key = self
            .heap
            .as_string(*self.stack.stack[0].as_obj_index().unwrap())
            .string
            .to_string();
        let value = self.stack.stack[1];
        self.globals.insert(key, value);

        self.stack.pop();
        self.stack.pop();
    }

    fn call_value(&mut self, callee: Value, arg_count: usize) -> bool {
        if let Value::ObjIndex(mut heap_index) = callee {
            match &self.heap.heap[heap_index] {
                Obj::String(_)
                | Obj::Function(_)
                | Obj::OpenUpValue(_)
                | Obj::ClosedUpValue(_)
                | Obj::Instance(_) => {
                    // Fall through to error handling.
                }
                Obj::Closure(_) => {
                    return self.call(heap_index, arg_count);
                }
                Obj::NativeFn(native) => {
                    let result = (native.f)(self.stack.top_n(arg_count));
                    self.stack.pop_n(arg_count + 1);
                    self.stack.push(result);
                    return true;
                }
                Obj::Class(_) => {
                    let instance = self.new_instance(&mut heap_index);
                    let stack_len = self.stack.stack.len();
                    self.stack.stack[stack_len - arg_count - 1] = Value::ObjIndex(instance);

                    if let Some(idx) = self
                        .heap
                        .as_class(heap_index)
                        .methods
                        .get(INIT_STR)
                        .copied()
                    {
                        return self.call(idx, arg_count);
                    } else if arg_count != 0 {
                        self.runtime_error(&format!("Expected 0 arguments but got {}.", arg_count));
                        return false;
                    }
                    return true;
                }
                Obj::BoundMethod(b) => {
                    let bound_ptr = b.closure_idx;
                    let stack_top = self.stack.stack.len();
                    self.stack.stack[stack_top - arg_count - 1] = Value::ObjIndex(b.receiver_idx);
                    return self.call(bound_ptr, arg_count);
                }
            };
        }
        self.runtime_error("Can only call functions and classes.");
        false
    }

    fn invoke_from_class(&mut self, class_index: usize, name: &str, arg_count: usize) -> bool {
        let method = match self.heap.as_class(class_index).methods.get(name) {
            Some(idx) => *idx,
            None => {
                self.runtime_error(&format!("Undefined property '{}'.", name));
                return false;
            }
        };
        self.call(method, arg_count)
    }

    fn invoke(&mut self, name: &str, arg_count: usize) -> bool {
        let receiver = *self.stack.peek(arg_count).as_obj_index().unwrap();
        let (class_index, field) = match self.heap.heap[receiver].as_instance() {
            Some(i) => (i.class_index, i.fields.get(name).copied()),
            None => {
                self.runtime_error("Only instances have methods.");
                return false;
            }
        };

        if let Some(value) = field {
            let stack_len = self.stack.stack.len();
            self.stack.stack[stack_len - arg_count - 1] = value;
            return self.call_value(value, arg_count);
        }
        self.invoke_from_class(class_index, name, arg_count)
    }

    fn bind_method(&mut self, class_idx: usize, name: &str) -> bool {
        let method = match self.heap.as_class(class_idx).methods.get(name) {
            Some(idx) => *idx,
            None => {
                self.runtime_error(&format!("Undefined property '{}'.", name));
                return false;
            }
        };

        let bound = self.new_bound_method(*self.stack.peek(0).as_obj_index().unwrap(), method);
        self.stack.pop();
        self.stack.push(Value::ObjIndex(bound));
        true
    }

    /// Captures the given stack slot as a local upvalue. Inserts the new
    /// upvalue into the linked list of upvalues on the heap, sorted by stack
    /// slot (higher first).
    fn capture_upvalue(&mut self, local: usize) -> usize {
        let mut prev_upvalue = None;
        let mut next = self.open_upvalues;
        while matches!(next, Some(uv) if self.heap.as_open_up_value(uv).slot > local) {
            prev_upvalue = next;
            next = self.heap.as_open_up_value(next.unwrap()).next;
        }

        if matches!(next, Some(ptr) if self.heap.as_open_up_value(ptr).slot == local) {
            return next.unwrap();
        }

        let created_upvalue = self.new_upvalue(Open::new(local, next), &mut prev_upvalue);

        if let Some(prev) = prev_upvalue {
            self.heap.as_open_up_value_mut(prev).next = Some(created_upvalue);
        } else {
            self.open_upvalues = Some(created_upvalue);
        }

        created_upvalue
    }

    /// Closes upvalues that point to or above the given stack slot. This
    /// includes removing the upvalue from the open_upvalues linked list.
    fn close_upvalues(&mut self, stack_slot: usize) {
        while matches!(self.open_upvalues, Some(ptr) if self.heap.as_open_up_value(ptr).slot >= stack_slot)
        {
            let ptr = self.open_upvalues.unwrap();
            let open = self.heap.as_open_up_value(ptr);
            self.open_upvalues = open.next;
            self.heap.heap[ptr] = Obj::ClosedUpValue(Closed::new(self.stack.stack[open.slot]));
        }
    }

    fn define_method(&mut self, name_idx: usize) {
        let method_idx = *self.stack.peek(0).as_obj_index().unwrap();
        let class_index = *self.stack.peek(1).as_obj_index().unwrap();
        let name = self.heap.as_string(name_idx).string.clone();
        let class = self.heap.as_class_mut(class_index);

        class.methods.insert(name, method_idx);
        self.stack.pop();
    }

    fn call(&mut self, closure_heap_index: usize, arg_count: usize) -> bool {
        let closure = self.heap.as_closure(closure_heap_index);
        let arity = self.heap.as_function(closure.function_index).arity;
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
            self.stack.stack.len() - arg_count - 1,
        ));
        true
    }

    fn collect_garbage<R: Rewrite>(&mut self, pending_rewrites: Option<(&mut Obj, &mut R)>) {
        if self.is_compiling || self.opt.disable_garbage_collection {
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
        for slot in &self.stack.stack {
            self.heap.mark_value(*slot);
        }

        for index in self.frames.iter().map(|f| f.heap_index) {
            self.heap.mark_object(index)
        }

        {
            let mut upvalue = self.open_upvalues;
            while let Some(index) = upvalue {
                self.heap.mark_object(index);
                upvalue = self.heap.as_open_up_value(index).next;
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
        // Build the mapping from pre-sweep pointers to post-sweep pointers.
        let mapping = {
            let mut mapping = HashMap::new();
            let mut post_compaction_index = 0;
            for i in self
                .heap
                .heap
                .iter()
                .enumerate()
                .filter_map(|(i, obj)| obj.is_marked().then(|| i))
            {
                // Since the object at index `i` is marked, it is reachable, and
                // will be kept.  We add an entry for this pointer, and then
                // increment the post-compaction pointer.
                mapping.insert(i, post_compaction_index);
                post_compaction_index += 1;
            }
            mapping
        };

        // Remove unreachable objects.
        let before = self.heap.heap.len();
        self.heap.heap.retain(|obj| obj.is_marked());
        for obj in self.heap.heap.iter_mut() {
            obj.mark(false);
        }

        // Prune out unused strings from the strings table:
        let reachable_strings = self
            .heap
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

        before - self.heap.heap.len()
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

        let opens_heap = self
            .heap
            .heap
            .iter()
            .enumerate()
            .filter_map(|(i, o)| o.as_open_up_value().map(|_| i))
            .collect();

        opens_ll == opens_heap && is_sorted_and_unique
    }

    fn print_stack_slice(&self, label: &str, skip: usize) {
        eprintln!(
            "{}:    {}",
            label,
            self.stack
                .stack
                .iter()
                .skip(skip)
                .map(|i| format!("[ {} ]", i.print(&self.heap)))
                .collect::<String>()
        );
    }

    fn run(&mut self) -> Result<(), InterpretResult> {
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
                self.collect_garbage::<usize>(None);
            }

            use crate::value::*;
            match &self.read_byte().clone() {
                OpCode::Constant(offset) => {
                    let constant = self.read_constant(*offset);
                    self.stack.push(constant);
                }
                OpCode::Return => {
                    let result = self.stack.pop();
                    self.close_upvalues(self.frame().slots());
                    let finished_frame = self.frames.pop().unwrap();
                    if self.frames.is_empty() {
                        self.stack.pop();
                        if self.opt.trace_execution {
                            self.print_stack_slice("stack", 0);
                        }
                        debug_assert!(self.stack.stack.is_empty());
                        return Ok(());
                    }

                    self.stack.stack.truncate(finished_frame.frame_start);
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
                        (Value::ObjIndex(i), Value::ObjIndex(j)) => {
                            match (&self.heap.heap[i], &self.heap.heap[j]) {
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
                OpCode::Bool(b) => self.stack.push(Value::Bool(*b)),
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
                OpCode::SetLocal(slot) => {
                    let index = self.frame().slots() + *slot;
                    self.stack.stack[index] = self.stack.peek(0);
                }
                OpCode::GetLocal(slot) => {
                    let value = self.stack.stack[self.frame().slots() + *slot];
                    self.stack.push(value);
                }
                OpCode::JumpIfFalse(distance) => {
                    if self.stack.peek(0).is_falsey() {
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
                    if !self.call_value(self.stack.peek(*arity), *arity) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
                OpCode::Closure(constant, upvalues) => {
                    let function_heap_index =
                        *self.read_constant(*constant).as_obj_index().unwrap();
                    let upvalues = upvalues
                        .iter()
                        .map(|uv| {
                            if uv.is_local {
                                self.capture_upvalue(self.frame().slots() + uv.index)
                            } else {
                                self.heap.as_closure(self.frame().heap_index).upvalues[uv.index]
                            }
                        })
                        .collect();
                    let closure_heap_index = self.new_closure(function_heap_index, upvalues);
                    self.stack.push(Value::ObjIndex(closure_heap_index));
                }
                OpCode::GetUpvalue(slot) => {
                    let uv_index = self.closure().upvalues[*slot];
                    let val = match &self.heap.heap[uv_index] {
                        Obj::ClosedUpValue(c) => c.value,
                        Obj::OpenUpValue(o) => self.stack.stack[o.slot],
                        _ => unreachable!(),
                    };
                    self.stack.push(val);
                }
                OpCode::SetUpvalue(slot) => {
                    let uv_index = self.closure().upvalues[*slot];
                    let val = self.stack.peek(0);
                    match &mut self.heap.heap[uv_index] {
                        Obj::ClosedUpValue(c) => c.value = val,
                        Obj::OpenUpValue(o) => self.stack.stack[o.slot] = val,
                        _ => unreachable!(),
                    };
                }
                OpCode::CloseUpvalue => {
                    self.close_upvalues(self.stack.stack.len() - 1);
                    self.stack.pop();
                }
                OpCode::Class(index) => {
                    let name = self.read_string(*index).to_string();
                    let heap_index = self.new_class(&name);
                    self.stack.push(Value::ObjIndex(heap_index));
                }
                OpCode::GetProperty(constant) => {
                    match self.stack.peek(0) {
                        Value::ObjIndex(instance_idx)
                            if self.heap.heap[instance_idx].as_instance().is_some() =>
                        {
                            let name = self.read_string(*constant).to_string();
                            let i = self.heap.as_instance(instance_idx);
                            if let Some(v) = i.fields.get(&name) {
                                self.stack.pop(); // Instance.
                                self.stack.push(*v);
                                continue;
                            }
                            let class_index = i.class_index;
                            if !self.bind_method(class_index, &name) {
                                return Err(InterpretResult::RuntimeError);
                            }
                        }
                        _ => {
                            self.runtime_error("Only instances have properties.");
                            return Err(InterpretResult::RuntimeError);
                        }
                    };
                }
                OpCode::SetProperty(constant) => {
                    match self.stack.peek(1) {
                        Value::ObjIndex(instance_idx)
                            if self.heap.heap[instance_idx].as_instance().is_some() =>
                        {
                            let name = self.read_string(*constant).to_string();
                            let value = self.stack.peek(0);
                            self.heap
                                .as_instance_mut(instance_idx)
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
                OpCode::GetSuper(name_index) => {
                    let name = self.read_string(*name_index).to_string();
                    let superclass_ptr = *self.stack.pop().as_obj_index().unwrap();
                    if !self.bind_method(superclass_ptr, &name) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
                OpCode::Method(constant) => {
                    self.define_method(*self.read_constant(*constant).as_obj_index().unwrap());
                }
                OpCode::Invoke(constant, arg_count) => {
                    let arg_count = *arg_count;
                    let method = self.read_string(*constant).to_string();
                    if !self.invoke(&method, arg_count) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
                OpCode::Inherit => {
                    match self.stack.peek(1) {
                        Value::ObjIndex(superclass)
                            if self.heap.heap[superclass].as_class().is_some() =>
                        {
                            let superclass_methods = self.heap.as_class(superclass).methods.clone();
                            let subclass = *self.stack.peek(0).as_obj_index().unwrap();
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
                OpCode::SuperInvoke(constant, arg_count) => {
                    let arg_count = *arg_count;
                    let method = self.read_string(*constant).to_string();
                    let superclass_ptr = *self.stack.pop().as_obj_index().unwrap();
                    if !self.invoke_from_class(superclass_ptr, &method, arg_count) {
                        return Err(InterpretResult::RuntimeError);
                    }
                }
            }
        }
    }

    pub fn interpret(&mut self, source: &str) -> Result<(), InterpretResult> {
        self.is_compiling = true;
        let compiler = Compiler::new(
            self.opt,
            source,
            self,
            crate::compiler::FunctionType::Script,
        );
        let function = compiler.compile();
        self.is_compiling = false;
        match function {
            Some(function) => {
                let function_heap_index = self.new_function(function);
                self.stack.push(Value::ObjIndex(function_heap_index));
                let closure_heap_index = self.new_closure(function_heap_index, Vec::new());
                self.stack.pop();
                self.stack.push(Value::ObjIndex(closure_heap_index));
                self.call(closure_heap_index, 0);
            }
            None => {
                return Err(InterpretResult::CompileError);
            }
        };

        if self.opt.compile_only {
            return Ok(());
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

impl Rewrite for CallFrame {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.heap_index.rewrite(mapping);
    }
}

struct Stack {
    pub stack: Vec<Value>,
}

impl Stack {
    fn new() -> Self {
        Self { stack: Vec::new() }
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

    fn top_n(&self, n: usize) -> &[Value] {
        &self.stack[self.stack.len() - n..]
    }

    fn pop_n(&mut self, n: usize) {
        self.stack.truncate(self.stack.len() - n);
    }
}

impl Rewrite for Stack {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.stack.rewrite(mapping);
    }
}

pub struct Heap {
    pub heap: Vec<Obj>,

    /// Vector of heap indices, used during GC.
    pub gray_stack: Vec<usize>,

    log_gc: bool,
}

impl Heap {
    fn new(log_gc: bool) -> Self {
        Self {
            heap: Vec::new(),
            gray_stack: Vec::new(),
            log_gc,
        }
    }

    fn mark_value(&mut self, value: Value) {
        if self.log_gc {
            eprintln!("    mark value ({})", value.print(self));
        }
        match value {
            Value::Nil | Value::Bool(_) | Value::Double(_) => {}
            Value::ObjIndex(index) => {
                self.mark_object(index);
            }
        }
    }

    fn mark_object(&mut self, index: usize) {
        if self.log_gc {
            eprintln!("{:3} mark object {}", index, self.heap[index].print(self));
        }

        if self.heap[index].is_marked() {
            return;
        }

        self.heap[index].mark(true);

        self.gray_stack.push(index);
    }

    fn trace_references(&mut self) {
        while let Some(index) = self.gray_stack.pop() {
            self.blacken_object(index);
        }
    }

    fn blacken_object(&mut self, index: usize) {
        if self.log_gc {
            eprintln!("{} blacken {}", index, self.heap[index].print(self));
        }

        match &self.heap[index] {
            Obj::String(_) | Obj::NativeFn(_) | Obj::OpenUpValue(_) => {}
            Obj::Function(f) => {
                // TODO: don't clone here.
                for v in f.chunk.constants.clone().iter() {
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
            Obj::ClosedUpValue(c) => {
                let v = c.value;
                self.mark_value(v);
            }
            Obj::Class(c) => {
                let methods = c.methods.values().copied().collect::<Vec<_>>();
                for m in methods {
                    self.mark_object(m);
                }
            }
            Obj::Instance(i) => {
                let idx = i.class_index;
                let field_values = i.fields.values().copied().collect::<Vec<_>>();
                self.mark_object(idx);
                for value in field_values {
                    self.mark_value(value);
                }
            }
            Obj::BoundMethod(b) => {
                let r = b.receiver_idx;
                let c = b.closure_idx;
                self.mark_object(r);
                self.mark_object(c);
            }
        }
    }

    fn as_string(&self, idx: usize) -> &LoxString {
        self.heap[idx].as_string().unwrap()
    }
    pub fn as_function(&self, idx: usize) -> &Function {
        self.heap[idx].as_function().unwrap()
    }
    pub fn as_closure(&self, idx: usize) -> &Closure {
        self.heap[idx].as_closure().unwrap()
    }
    pub fn as_class(&self, idx: usize) -> &Class {
        self.heap[idx].as_class().unwrap()
    }
    fn as_class_mut(&mut self, idx: usize) -> &mut Class {
        self.heap[idx].as_class_mut().unwrap()
    }
    fn as_instance(&self, idx: usize) -> &Instance {
        self.heap[idx].as_instance().unwrap()
    }
    fn as_instance_mut(&mut self, idx: usize) -> &mut Instance {
        self.heap[idx].as_instance_mut().unwrap()
    }
    fn as_open_up_value(&self, idx: usize) -> &Open {
        self.heap[idx].as_open_up_value().unwrap()
    }
    fn as_open_up_value_mut(&mut self, idx: usize) -> &mut Open {
        self.heap[idx].as_open_up_value_mut().unwrap()
    }
}

impl Rewrite for Heap {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.heap.rewrite(mapping);
    }
}

struct OpenUpValueIter<'h> {
    heap: &'h Heap,
    it: Option<usize>,
}

impl<'h> Iterator for OpenUpValueIter<'h> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.it;
        if let Some(ptr) = self.it {
            self.it = self.heap.as_open_up_value(ptr).next;
        }
        cur
    }
}
