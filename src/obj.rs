use std::{collections::HashMap, fmt::Display};

use enum_as_inner::EnumAsInner;

use crate::{chunk::Chunk, heap::Ptr, stack::Slot, value::Value};

#[derive(Clone, Debug)]
struct GcMetadata {}

impl GcMetadata {}

#[derive(Clone, Debug, EnumAsInner)]
pub(crate) enum Obj {
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

impl Display for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Obj::String(s) => write!(f, "{}", s.string),
            Obj::Function(fun) => write!(f, "<fn {}>", fun.name),
            Obj::Closure(c) => write!(f, "{}", c.function.borrow()),
            Obj::NativeFn(_) => write!(f, "<native fn>"),
            Obj::OpenUpValue(_) => write!(f, "<OpenUpValue>"),
            Obj::ClosedUpValue(_) => write!(f, "ClosedUpValue>"),
            Obj::Class(c) => write!(f, "{}", c.name),
            Obj::Instance(i) => write!(f, "{} instance", i.class.borrow()),
            Obj::BoundMethod(b) => {
                write!(f, "{}", b.closure.borrow())
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct LoxString {
    pub(crate) string: String,
}

impl LoxString {
    pub(crate) fn new(s: String) -> Self {
        Self { string: s }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    pub(crate) arity: usize,
    pub(crate) chunk: Chunk,
    pub(crate) name: String,
}

impl Function {
    pub(crate) fn new(name: &str) -> Self {
        Self {
            arity: 0,
            name: name.to_string(),
            chunk: Chunk::new(),
        }
    }
}

type Native = for<'opt, 'vm, 'args> fn(&'vm mut crate::vm::VM<'opt>, &'args [Value]) -> Value;

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
        f.debug_struct("NativeFn").finish()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Closure {
    pub(crate) function: Ptr,
    upvalues: Vec<Ptr>,
}

impl Closure {
    pub(crate) fn new(function: Ptr, upvalues: Vec<Ptr>) -> Self {
        Self { function, upvalues }
    }

    pub(crate) fn upvalue_at(&self, index: UpValueIndex) -> &Ptr {
        &self.upvalues[index.0]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct UpValueIndex(pub(crate) usize);

impl Display for UpValueIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Class {
    name: String,
    /// Each method value is a pointer into the heap, pointing to a Closure.
    pub(crate) methods: HashMap<String, Ptr>,
}

impl Class {
    pub(crate) fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            methods: HashMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Instance {
    pub(crate) class: Ptr,
    pub(crate) fields: HashMap<String, Value>,
}

impl Instance {
    pub(crate) fn new(class: Ptr) -> Self {
        Self {
            class,
            fields: HashMap::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BoundMethod {
    pub(crate) receiver: Ptr,
    pub(crate) closure: Ptr,
}

impl BoundMethod {
    pub(crate) fn new(receiver: Ptr, closure: Ptr) -> Self {
        Self { receiver, closure }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Open {
    /// The stack slot that holds the associated value.
    pub(crate) slot: Slot,
    /// Heap pointer to the next open upvalue.
    pub(crate) next: Option<Ptr>,
}

impl Open {
    pub(crate) fn new(slot: Slot, next: Option<Ptr>) -> Self {
        Self { slot, next }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Closed {
    pub(crate) value: Value,
}

impl Closed {
    pub(crate) fn new(value: Value) -> Self {
        Self { value }
    }
}
