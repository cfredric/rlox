use enum_as_inner::EnumAsInner;

use crate::{chunk::Chunk, table::Table, value::Value};

#[derive(Copy, Clone, Debug)]
pub struct Header {
    is_marked: bool,
    is_gc_able: bool,
}

impl Header {
    fn new(gcs: bool) -> Self {
        Self {
            is_marked: false,
            is_gc_able: gcs,
        }
    }

    fn mark(&mut self, marked: bool) {
        if self.is_gc_able {
            self.is_marked = marked;
        }
    }

    fn is_marked(&self) -> bool {
        self.is_marked || !self.is_gc_able
    }
}

#[derive(Debug, EnumAsInner)]
pub enum Obj {
    String(LoxString),
    Function(Function),
    Closure(Closure),
    NativeFn(NativeFn),
    UpValue(UpValue),
    Class(Class),
    Instance(Instance),
}

impl Obj {
    fn header(&self) -> &Header {
        match self {
            Obj::String(s) => &s.header,
            Obj::Function(f) => &f.header,
            Obj::Closure(c) => &c.header,
            Obj::NativeFn(f) => &f.header,
            Obj::UpValue(u) => &u.header,
            Obj::Class(c) => &c.header,
            Obj::Instance(i) => &i.header,
        }
    }

    fn header_mut(&mut self) -> &mut Header {
        match self {
            Obj::String(s) => &mut s.header,
            Obj::Function(f) => &mut f.header,
            Obj::Closure(c) => &mut c.header,
            Obj::NativeFn(f) => &mut f.header,
            Obj::UpValue(u) => &mut u.header,
            Obj::Class(c) => &mut c.header,
            Obj::Instance(i) => &mut i.header,
        }
    }

    pub fn mark(&mut self, marked: bool) {
        self.header_mut().mark(marked);
    }

    pub fn is_marked(&self) -> bool {
        self.header().is_marked()
    }

    pub fn print(&self, heap: &[Obj]) -> String {
        match &self {
            Obj::String(s) => s.string.to_string(),
            Obj::Function(fun) => format!("<fn {}>", fun.name),
            Obj::NativeFn(_) => "<native fn>".to_string(),
            Obj::Closure(fun) => format!(
                "<closure (fn {})>",
                heap[fun.function_index].as_function().unwrap().name
            ),
            Obj::UpValue(upvalue) => format!("upvalue {:?}", upvalue),
            Obj::Class(c) => c.name.to_string(),
            Obj::Instance(i) => {
                format!("{} instance", heap[i.class_index].as_class().unwrap().name)
            }
        }
    }
}

#[derive(Debug)]
pub struct LoxString {
    header: Header,
    pub string: String,
}

impl LoxString {
    pub fn new(s: &str) -> Self {
        Self {
            header: Header::new(false),
            string: s.to_string(),
        }
    }
}

#[derive(Debug)]
pub struct Function {
    header: Header,
    pub arity: usize,
    pub chunk: Chunk,
    pub name: String,
}

impl Function {
    pub fn new(name: &str) -> Self {
        Self {
            header: Header::new(true),
            arity: 0,
            name: name.to_string(),
            chunk: Chunk::new(),
        }
    }
}

type Native = fn(args: Vec<Value>) -> Value;

#[derive(Debug)]
pub struct NativeFn {
    header: Header,
    pub f: Native,
}

impl NativeFn {
    pub fn new(f: Native) -> Self {
        Self {
            header: Header::new(false),
            f,
        }
    }
}

#[derive(Debug)]
pub struct Closure {
    header: Header,
    /// The heap index of the underlying function.
    pub function_index: usize,
    /// Pointers into the heap.
    pub upvalues: Vec<usize>,
}

impl Closure {
    pub fn new(function_index: usize, upvalues: Vec<usize>) -> Self {
        Self {
            header: Header::new(true),
            function_index,
            upvalues,
        }
    }
}

#[derive(Debug)]
pub struct Class {
    header: Header,
    name: String,
}

impl Class {
    pub fn new(name: &str) -> Self {
        Self {
            header: Header::new(true),
            name: name.to_string(),
        }
    }
}

#[derive(Debug)]
pub struct Instance {
    header: Header,
    pub class_index: usize,
    pub fields: Table<Value>,
}

impl Instance {
    pub fn new(class_index: usize, fields: Table<Value>) -> Self {
        Self {
            header: Header::new(true),
            class_index,
            fields,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct UpValue {
    header: Header,
    /// The value.
    pub value: OpenOrClosed,
    /// next is a pointer into the heap, to another UpValue object. This forms a linked list.
    pub next: Option<usize>,
}

impl UpValue {
    pub fn new(local: usize, upvalue: Option<usize>) -> Self {
        Self {
            header: Header::new(true),
            value: OpenOrClosed::Open(local),
            next: upvalue,
        }
    }

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
