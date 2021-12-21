use enum_as_inner::EnumAsInner;

use crate::{chunk::Chunk, table::Table, value::Value};

#[derive(Debug)]
pub struct Obj {
    pub is_marked: bool,
    pub variant: ObjVariant,
}

#[derive(Debug, EnumAsInner)]
pub enum ObjVariant {
    String(String),
    Function(Function),
    Closure(Closure),
    NativeFn(NativeFn),
    UpValue(UpValue),
    Class(Class),
    Instance(Instance),
}

impl Obj {
    pub fn new(variant: ObjVariant) -> Self {
        Self {
            is_marked: false,
            variant,
        }
    }

    pub fn mark(&mut self) {
        self.is_marked = true;
    }

    pub fn print(&self, heap: &[Obj]) -> String {
        match &self.variant {
            ObjVariant::String(s) => s.to_string(),
            ObjVariant::Function(fun) => format!("<fn {}>", fun.name),
            ObjVariant::NativeFn(_) => "<native fn>".to_string(),
            ObjVariant::Closure(fun) => format!(
                "<closure (fn {})>",
                heap[fun.function_index].variant.as_function().unwrap().name
            ),
            ObjVariant::UpValue(upvalue) => format!("upvalue {:?}", upvalue),
            ObjVariant::Class(c) => c.name.to_string(),
            ObjVariant::Instance(i) => {
                format!(
                    "{} instance",
                    heap[i.class_index].variant.as_class().unwrap().name
                )
            }
        }
    }
}

#[derive(Debug)]
pub struct Function {
    pub arity: usize,
    pub chunk: Chunk,
    pub name: String,
}

impl Function {
    pub fn new(name: &str) -> Self {
        Self {
            arity: 0,
            name: name.to_string(),
            chunk: Chunk::new(),
        }
    }
}

pub type NativeFn = fn(args: Vec<Value>) -> Value;

#[derive(Debug)]
pub struct Closure {
    /// The heap index of the underlying function.
    pub function_index: usize,
    /// Pointers into the heap.
    pub upvalues: Vec<usize>,
}

impl Closure {
    pub fn new(function_index: usize, upvalues: Vec<usize>) -> Self {
        Self {
            function_index,
            upvalues,
        }
    }
}

#[derive(Debug)]
pub struct Class {
    name: String,
}

impl Class {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

#[derive(Debug)]
pub struct Instance {
    pub class_index: usize,
    pub fields: Table<Value>,
}

impl Instance {
    pub fn new(class_index: usize, fields: Table<Value>) -> Self {
        Self {
            class_index,
            fields,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct UpValue {
    /// The value.
    pub value: OpenOrClosed,
    /// next is a pointer into the heap, to another UpValue object. This forms a linked list.
    pub next: Option<usize>,
}

impl UpValue {
    /// Returns true iff this upvalue points (or used to point) at or above the
    /// given stack slot.
    pub fn is_at_or_above(&self, stack_slot: usize) -> bool {
        self.value.is_at_or_above(stack_slot)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum OpenOrClosed {
    /// Open holds a pointer into the stack.
    Open(usize),
    /// Value holds the old stack slot (for sorting), and a closed-over value.
    Closed(usize, Value),
}

impl OpenOrClosed {
    fn is_at_or_above(&self, stack_slot: usize) -> bool {
        let loc = match self {
            OpenOrClosed::Open(loc) => *loc,
            OpenOrClosed::Closed(loc, _) => *loc,
        };
        loc >= stack_slot
    }
}
