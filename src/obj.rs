use std::collections::HashMap;

use enum_as_inner::EnumAsInner;

use crate::{
    chunk::Chunk,
    value::Value,
    vm::{Heap, Rewrite},
};

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

    pub fn is_marked(&self) -> bool {
        self.is_marked || !self.is_gc_able
    }

    fn set_gc_able(&mut self, gc: bool) {
        self.is_gc_able = gc;
    }
}

#[derive(EnumAsInner)]
pub enum Obj {
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
    fn header(&self) -> &Header {
        match self {
            Obj::String(s) => &s.header,
            Obj::Function(f) => &f.header,
            Obj::Closure(c) => &c.header,
            Obj::NativeFn(f) => &f.header,
            Obj::OpenUpValue(u) => &u.header,
            Obj::ClosedUpValue(u) => &u.header,
            Obj::Class(c) => &c.header,
            Obj::Instance(i) => &i.header,
            Obj::BoundMethod(b) => &b.header,
        }
    }

    fn header_mut(&mut self) -> &mut Header {
        match self {
            Obj::String(s) => &mut s.header,
            Obj::Function(f) => &mut f.header,
            Obj::Closure(c) => &mut c.header,
            Obj::NativeFn(f) => &mut f.header,
            Obj::OpenUpValue(u) => &mut u.header,
            Obj::ClosedUpValue(u) => &mut u.header,
            Obj::Class(c) => &mut c.header,
            Obj::Instance(i) => &mut i.header,
            Obj::BoundMethod(b) => &mut b.header,
        }
    }

    pub fn set_gc_exempt(&mut self) {
        self.header_mut().set_gc_able(false);
    }

    pub fn mark(&mut self, marked: bool) {
        self.header_mut().mark(marked);
    }

    pub fn is_marked(&self) -> bool {
        self.header().is_marked()
    }

    pub fn print(&self, heap: &Heap) -> String {
        match self {
            Obj::String(s) => s.string.to_string(),
            Obj::Function(fun) => format!("<fn {}>", fun.name),
            Obj::NativeFn(_) => "<native fn>".to_string(),
            Obj::Closure(fun) => heap.heap[fun.function_index].print(heap),
            Obj::OpenUpValue(_) => unreachable!(),
            Obj::ClosedUpValue(_) => unreachable!(),
            Obj::Class(c) => c.name.to_string(),
            Obj::Instance(i) => {
                format!("{} instance", heap.as_class(i.class_index).name)
            }
            Obj::BoundMethod(b) => {
                heap.heap[heap.as_closure(b.closure_idx).function_index].print(heap)
            }
        }
    }
}

pub struct LoxString {
    pub header: Header,
    pub string: String,
}

impl LoxString {
    pub fn new(s: &str) -> Self {
        Self {
            header: Header::new(true),
            string: s.to_string(),
        }
    }
}

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

type Native = fn(args: &[Value]) -> Value;

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

pub struct Class {
    header: Header,
    name: String,
    /// Each method value is an index into the heap, pointing to a Closure.
    pub methods: HashMap<String, usize>,
}

impl Class {
    pub fn new(name: &str) -> Self {
        Self {
            header: Header::new(true),
            name: name.to_string(),
            methods: HashMap::new(),
        }
    }
}

pub struct Instance {
    header: Header,
    pub class_index: usize,
    pub fields: HashMap<String, Value>,
}

impl Instance {
    pub fn new(class_index: usize) -> Self {
        Self {
            header: Header::new(true),
            class_index,
            fields: HashMap::new(),
        }
    }
}

pub struct BoundMethod {
    header: Header,
    pub receiver_idx: usize,
    pub closure_idx: usize,
}

impl BoundMethod {
    pub fn new(receiver_idx: usize, closure_idx: usize) -> Self {
        Self {
            header: Header::new(true),
            receiver_idx,
            closure_idx,
        }
    }
}

pub struct Open {
    header: Header,
    /// The stack slot that holds the associated value.
    pub slot: usize,
    /// Heap pointer to the next open upvalue.
    pub next: Option<usize>,
}

impl Open {
    pub fn new(slot: usize, next: Option<usize>) -> Self {
        Self {
            header: Header::new(true),
            slot,
            next,
        }
    }
}

pub struct Closed {
    header: Header,
    pub value: Value,
}

impl Closed {
    pub fn new(value: Value) -> Self {
        Self {
            header: Header::new(true),
            value,
        }
    }
}

impl Rewrite for Open {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.next.rewrite(mapping);
    }
}
impl Rewrite for Closed {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.value.rewrite(mapping);
    }
}

impl Rewrite for Obj {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.mark(false);
        match self {
            Obj::String(_) | Obj::NativeFn(_) => {
                // Nothing to do here.
            }
            Obj::Class(c) => {
                c.methods.rewrite(mapping);
            }
            Obj::Function(f) => {
                f.chunk.rewrite(mapping);
            }
            Obj::Closure(c) => {
                c.function_index = mapping[&c.function_index];
                c.upvalues.rewrite(mapping);
            }
            Obj::OpenUpValue(uv) => {
                uv.rewrite(mapping);
            }
            Obj::ClosedUpValue(uv) => {
                uv.rewrite(mapping);
            }
            Obj::Instance(i) => {
                i.class_index.rewrite(mapping);
                i.fields.rewrite(mapping);
            }
            Obj::BoundMethod(b) => {
                b.receiver_idx.rewrite(mapping);
                b.closure_idx.rewrite(mapping);
            }
        }
    }
}
