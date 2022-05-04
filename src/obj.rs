use std::{collections::HashMap, fmt::Display};

use enum_as_inner::EnumAsInner;

use crate::{
    chunk::Chunk,
    heap::{Heap, Ptr},
    post_process_gc_sweep::{GcSweepData, PostProcessGcSweep},
    stack::Slot,
    value::Value,
};

#[derive(Clone, Debug)]
struct GcMetadata {
    is_reachable: bool,
}

impl GcMetadata {
    fn new() -> Self {
        Self {
            is_reachable: false,
        }
    }
}

#[derive(Clone, Debug, EnumAsInner)]
pub(crate) enum Obj {
    Dummy,
    String(LoxString),
    Function(Function),
    Closure(Closure),
    NativeFn(NativeFn),
    OpenUpValue(Open),
    ClosedUpValue(Closed),
    Class(Class),
    Instance(Instance),
    BoundMethod(BoundMethod),
}

impl Obj {
    pub(crate) fn mark_reached(&mut self, reached: bool) {
        let gc_metadata = match self {
            Obj::Dummy => return,
            Obj::String(s) => &mut s.gc_metadata,
            Obj::Function(f) => &mut f.gc_metadata,
            Obj::Closure(c) => &mut c.gc_metadata,
            Obj::NativeFn(_) => return,
            Obj::OpenUpValue(o) => &mut o.gc_metadata,
            Obj::ClosedUpValue(c) => &mut c.gc_metadata,
            Obj::Class(c) => &mut c.gc_metadata,
            Obj::Instance(i) => &mut i.gc_metadata,
            Obj::BoundMethod(b) => &mut b.gc_metadata,
        };

        gc_metadata.is_reachable = reached;
    }

    pub(crate) fn is_eligible_for_deletion(&self) -> bool {
        let gc_metadata = match self {
            Obj::Dummy => return false,
            Obj::String(s) => &s.gc_metadata,
            Obj::Function(f) => &f.gc_metadata,
            Obj::Closure(c) => &c.gc_metadata,
            Obj::NativeFn(_) => return false,
            Obj::OpenUpValue(o) => &o.gc_metadata,
            Obj::ClosedUpValue(c) => &c.gc_metadata,
            Obj::Class(c) => &c.gc_metadata,
            Obj::Instance(i) => &i.gc_metadata,
            Obj::BoundMethod(b) => &b.gc_metadata,
        };

        !gc_metadata.is_reachable
    }
}

pub(crate) struct ObjWithContext<'a, 'opt> {
    obj: &'a Obj,
    heap: &'a Heap<'opt>,
}

impl<'a, 'opt> ObjWithContext<'a, 'opt> {
    pub(crate) fn new(obj: &'a Obj, heap: &'a Heap<'opt>) -> Self {
        Self { obj, heap }
    }
}

impl<'a, 'opt> Display for ObjWithContext<'a, 'opt> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.obj {
            Obj::Dummy => write!(f, "<Dummy>"),
            Obj::String(s) => write!(f, "{}", s.string),
            Obj::Function(fun) => write!(f, "<fn {}>", fun.name),
            Obj::Closure(c) => write!(
                f,
                "{}",
                ObjWithContext::new(&self.heap[&c.function], self.heap)
            ),
            Obj::NativeFn(_) => write!(f, "<native fn>"),
            Obj::OpenUpValue(_) => write!(f, "<OpenUpValue>"),
            Obj::ClosedUpValue(_) => write!(f, "ClosedUpValue>"),
            Obj::Class(c) => write!(f, "{}", c.name),
            Obj::Instance(i) => write!(f, "{} instance", self.heap.as_class(&i.class).name),
            Obj::BoundMethod(b) => {
                let fun = &self.heap[&self.heap.as_closure(&b.closure).function];
                write!(f, "{}", ObjWithContext::new(fun, self.heap))
            }
        }
    }
}

impl PostProcessGcSweep for Obj {
    fn process(&mut self, sweep_data: &GcSweepData) {
        match self {
            Obj::Dummy => {}
            Obj::String(s) => s.process(sweep_data),
            Obj::NativeFn(n) => n.process(sweep_data),
            Obj::Class(c) => c.process(sweep_data),
            Obj::Function(f) => f.process(sweep_data),
            Obj::Closure(c) => c.process(sweep_data),
            Obj::OpenUpValue(uv) => uv.process(sweep_data),
            Obj::ClosedUpValue(uv) => uv.process(sweep_data),
            Obj::Instance(i) => i.process(sweep_data),
            Obj::BoundMethod(b) => b.process(sweep_data),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct LoxString {
    gc_metadata: GcMetadata,
    pub(crate) string: String,
}

impl LoxString {
    pub(crate) fn new(s: String) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            string: s,
        }
    }
}
impl PostProcessGcSweep for LoxString {
    fn process(&mut self, _sweep_data: &GcSweepData) {}
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    gc_metadata: GcMetadata,
    pub(crate) arity: usize,
    pub(crate) chunk: Chunk,
    pub(crate) name: String,
}

impl Function {
    pub(crate) fn new(name: &str) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            arity: 0,
            name: name.to_string(),
            chunk: Chunk::new(),
        }
    }
}

impl PostProcessGcSweep for Function {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.chunk.process(sweep_data);
    }
}

type Native =
    for<'opt, 'vm, 'args> fn(&'vm mut crate::vm::VM<'opt>, &mut Ptr, &'args [Value]) -> Value;

#[derive(Clone)]
pub(crate) struct NativeFn {
    pub(crate) f: Native,
}

impl NativeFn {
    pub(crate) fn new(f: Native) -> Self {
        Self { f }
    }
}

impl std::fmt::Debug for NativeFn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NativeFn")
    }
}

impl PostProcessGcSweep for NativeFn {
    fn process(&mut self, _sweep_data: &GcSweepData) {}
}

#[derive(Clone, Debug)]
pub(crate) struct Closure {
    gc_metadata: GcMetadata,
    pub(crate) function: Ptr,
    upvalues: Vec<Ptr>,
}

impl Closure {
    pub(crate) fn new(function: Ptr, upvalues: Vec<Ptr>) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            function,
            upvalues,
        }
    }

    pub(crate) fn upvalue_at(&self, index: UpValueIndex) -> &Ptr {
        &self.upvalues[index.0]
    }

    pub(crate) fn upvalues<'s>(&'s self) -> impl Iterator<Item = &Ptr> + 's {
        self.upvalues.iter()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct UpValueIndex(pub(crate) usize);

impl Display for UpValueIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl PostProcessGcSweep for Closure {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.function.process(sweep_data);
        self.upvalues.process(sweep_data);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Class {
    gc_metadata: GcMetadata,
    name: String,
    /// Each method value is a pointer into the heap, pointing to a Closure.
    pub(crate) methods: HashMap<String, Ptr>,
}

impl Class {
    pub(crate) fn new(name: &str) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            name: name.to_string(),
            methods: HashMap::new(),
        }
    }
}

impl PostProcessGcSweep for Class {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.methods.process(sweep_data);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Instance {
    gc_metadata: GcMetadata,
    pub(crate) class: Ptr,
    pub(crate) fields: HashMap<String, Value>,
}

impl Instance {
    pub(crate) fn new(class: Ptr) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            class,
            fields: HashMap::new(),
        }
    }
}

impl PostProcessGcSweep for Instance {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.class.process(sweep_data);
        self.fields.process(sweep_data);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BoundMethod {
    gc_metadata: GcMetadata,
    pub(crate) receiver: Ptr,
    pub(crate) closure: Ptr,
}

impl BoundMethod {
    pub(crate) fn new(receiver: Ptr, closure: Ptr) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            receiver,
            closure,
        }
    }
}

impl PostProcessGcSweep for BoundMethod {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.receiver.process(sweep_data);
        self.closure.process(sweep_data);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Open {
    gc_metadata: GcMetadata,
    /// The stack slot that holds the associated value.
    pub(crate) slot: Slot,
    /// Heap pointer to the next open upvalue.
    pub(crate) next: Option<Ptr>,
}

impl Open {
    pub(crate) fn new(slot: Slot, next: Option<Ptr>) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            slot,
            next,
        }
    }
}
impl PostProcessGcSweep for Open {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.next.process(sweep_data);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Closed {
    gc_metadata: GcMetadata,
    pub(crate) value: Value,
}

impl Closed {
    pub(crate) fn new(value: Value) -> Self {
        Self {
            gc_metadata: GcMetadata::new(),
            value,
        }
    }
}
impl PostProcessGcSweep for Closed {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.value.process(sweep_data);
    }
}
