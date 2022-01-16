use std::collections::HashMap;

use enum_as_inner::EnumAsInner;

use crate::{
    chunk::Chunk,
    print::Print,
    rewrite::Rewrite,
    stack::Slot,
    value::Value,
    vm::{Heap, Ptr},
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
}

impl Print for Obj {
    fn print(&self, heap: &Heap) -> String {
        match self {
            Obj::String(s) => s.string.to_string(),
            Obj::Function(fun) => format!("<fn {}>", fun.name),
            Obj::NativeFn(_) => "<native fn>".to_string(),
            Obj::Closure(fun) => heap.deref(fun.function).print(heap),
            Obj::OpenUpValue(_) => unreachable!(),
            Obj::ClosedUpValue(_) => unreachable!(),
            Obj::Class(c) => c.name.to_string(),
            Obj::Instance(i) => {
                format!("{} instance", heap.as_class(i.class).name)
            }
            Obj::BoundMethod(b) => heap.deref(heap.as_closure(b.closure).function).print(heap),
        }
    }
}

impl Rewrite for Obj {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        match self {
            Obj::String(s) => s.rewrite(mapping),
            Obj::NativeFn(n) => n.rewrite(mapping),
            Obj::Class(c) => c.rewrite(mapping),
            Obj::Function(f) => f.rewrite(mapping),
            Obj::Closure(c) => c.rewrite(mapping),
            Obj::OpenUpValue(uv) => uv.rewrite(mapping),
            Obj::ClosedUpValue(uv) => uv.rewrite(mapping),
            Obj::Instance(i) => i.rewrite(mapping),
            Obj::BoundMethod(b) => b.rewrite(mapping),
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
impl Rewrite for LoxString {
    fn rewrite(&mut self, _mapping: &HashMap<usize, usize>) {}
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

impl Rewrite for Function {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.chunk.rewrite(mapping);
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

impl Rewrite for NativeFn {
    fn rewrite(&mut self, _mapping: &HashMap<usize, usize>) {}
}

pub struct Closure {
    header: Header,
    pub function: Ptr,
    pub upvalues: Vec<Ptr>,
}

impl Closure {
    pub fn new(function: Ptr, upvalues: Vec<Ptr>) -> Self {
        Self {
            header: Header::new(true),
            function,
            upvalues,
        }
    }
}

impl Rewrite for Closure {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.function.rewrite(mapping);
        self.upvalues.rewrite(mapping);
    }
}

pub struct Class {
    header: Header,
    name: String,
    /// Each method value is an index into the heap, pointing to a Closure.
    pub methods: HashMap<String, Ptr>,
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

impl Rewrite for Class {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.methods.rewrite(mapping);
    }
}

pub struct Instance {
    header: Header,
    pub class: Ptr,
    pub fields: HashMap<String, Value>,
}

impl Instance {
    pub fn new(class: Ptr) -> Self {
        Self {
            header: Header::new(true),
            class,
            fields: HashMap::new(),
        }
    }
}

impl Rewrite for Instance {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.class.rewrite(mapping);
        self.fields.rewrite(mapping);
    }
}

pub struct BoundMethod {
    header: Header,
    pub receiver: Ptr,
    pub closure: Ptr,
}

impl BoundMethod {
    pub fn new(receiver: Ptr, closure: Ptr) -> Self {
        Self {
            header: Header::new(true),
            receiver,
            closure,
        }
    }
}

impl Rewrite for BoundMethod {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.receiver.rewrite(mapping);
        self.closure.rewrite(mapping);
    }
}

pub struct Open {
    header: Header,
    /// The stack slot that holds the associated value.
    pub slot: Slot,
    /// Heap pointer to the next open upvalue.
    pub next: Option<Ptr>,
}

impl Open {
    pub fn new(slot: Slot, next: Option<Ptr>) -> Self {
        Self {
            header: Header::new(true),
            slot,
            next,
        }
    }
}
impl Rewrite for Open {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.next.rewrite(mapping);
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
impl Rewrite for Closed {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        self.value.rewrite(mapping);
    }
}
