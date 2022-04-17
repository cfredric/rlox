use std::{collections::HashMap, fmt::Display};

use enum_as_inner::EnumAsInner;

use crate::{
    chunk::Chunk,
    heap::{Heap, Ptr},
    rewrite::Rewrite,
    stack::Slot,
    value::Value,
};

#[derive(Clone, Debug)]
struct Header {
    is_marked: bool,
}

impl Header {
    fn new() -> Self {
        Self { is_marked: false }
    }
}

#[derive(Clone, Debug, EnumAsInner)]
pub(crate) enum Obj {
    Dummy(Dummy),
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
    pub(crate) fn mark(&mut self, marked: bool) {
        let header = match self {
            Obj::Dummy(_) => return,
            Obj::String(s) => &mut s.header,
            Obj::Function(f) => &mut f.header,
            Obj::Closure(c) => &mut c.header,
            Obj::NativeFn(_) => return,
            Obj::OpenUpValue(o) => &mut o.header,
            Obj::ClosedUpValue(c) => &mut c.header,
            Obj::Class(c) => &mut c.header,
            Obj::Instance(i) => &mut i.header,
            Obj::BoundMethod(b) => &mut b.header,
        };

        header.is_marked = marked;
    }

    pub(crate) fn is_marked(&self) -> bool {
        let header = match self {
            Obj::Dummy(_) => return true,
            Obj::String(s) => &s.header,
            Obj::Function(f) => &f.header,
            Obj::Closure(c) => &c.header,
            Obj::NativeFn(_) => return true,
            Obj::OpenUpValue(o) => &o.header,
            Obj::ClosedUpValue(c) => &c.header,
            Obj::Class(c) => &c.header,
            Obj::Instance(i) => &i.header,
            Obj::BoundMethod(b) => &b.header,
        };

        header.is_marked
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
            Obj::Dummy(_) => write!(f, "<Dummy>"),
            Obj::String(s) => write!(f, "{}", s.string),
            Obj::Function(fun) => write!(f, "<fn {}>", fun.name),
            Obj::Closure(c) => write!(
                f,
                "{}",
                ObjWithContext::new(&self.heap[c.function], self.heap)
            ),
            Obj::NativeFn(_) => write!(f, "<native fn>"),
            Obj::OpenUpValue(_) => write!(f, "<OpenUpValue>"),
            Obj::ClosedUpValue(_) => write!(f, "ClosedUpValue>"),
            Obj::Class(c) => write!(f, "{}", c.name),
            Obj::Instance(i) => write!(f, "{} instance", self.heap.as_class(i.class).name),
            Obj::BoundMethod(b) => {
                let fun = &self.heap[self.heap.as_closure(b.closure).function];
                write!(f, "{}", ObjWithContext::new(fun, self.heap))
            }
        }
    }
}

impl Rewrite for Obj {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        match self {
            Obj::Dummy(_) => {}
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

#[derive(Clone, Debug)]
pub(crate) struct Dummy {}

#[derive(Clone, Debug)]
pub(crate) struct LoxString {
    header: Header,
    pub(crate) string: String,
}

impl LoxString {
    pub(crate) fn new(s: String) -> Self {
        Self {
            header: Header::new(),
            string: s,
        }
    }
}
impl Rewrite for LoxString {
    fn rewrite(&mut self, _mapping: &HashMap<Ptr, Ptr>) {}
}

#[derive(Clone, Debug)]
pub(crate) struct Function {
    header: Header,
    pub(crate) arity: usize,
    pub(crate) chunk: Chunk,
    pub(crate) name: String,
}

impl Function {
    pub(crate) fn new(name: &str) -> Self {
        Self {
            header: Header::new(),
            arity: 0,
            name: name.to_string(),
            chunk: Chunk::new(),
        }
    }
}

impl Rewrite for Function {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.chunk.rewrite(mapping);
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
        f.debug_struct("NativeFn").finish()
    }
}

impl Rewrite for NativeFn {
    fn rewrite(&mut self, _mapping: &HashMap<Ptr, Ptr>) {}
}

#[derive(Clone, Debug)]
pub(crate) struct Closure {
    header: Header,
    pub(crate) function: Ptr,
    upvalues: Vec<Ptr>,
}

impl Closure {
    pub(crate) fn new(function: Ptr, upvalues: Vec<Ptr>) -> Self {
        Self {
            header: Header::new(),
            function,
            upvalues,
        }
    }

    pub(crate) fn upvalue_at(&self, index: UpValueIndex) -> Ptr {
        self.upvalues[index.0]
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

impl Rewrite for Closure {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.function.rewrite(mapping);
        self.upvalues.rewrite(mapping);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Class {
    header: Header,
    name: String,
    /// Each method value is a pointer into the heap, pointing to a Closure.
    pub(crate) methods: HashMap<String, Ptr>,
}

impl Class {
    pub(crate) fn new(name: &str) -> Self {
        Self {
            header: Header::new(),
            name: name.to_string(),
            methods: HashMap::new(),
        }
    }
}

impl Rewrite for Class {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.methods.rewrite(mapping);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Instance {
    header: Header,
    pub(crate) class: Ptr,
    pub(crate) fields: HashMap<String, Value>,
}

impl Instance {
    pub(crate) fn new(class: Ptr) -> Self {
        Self {
            header: Header::new(),
            class,
            fields: HashMap::new(),
        }
    }
}

impl Rewrite for Instance {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.class.rewrite(mapping);
        self.fields.rewrite(mapping);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BoundMethod {
    header: Header,
    pub(crate) receiver: Ptr,
    pub(crate) closure: Ptr,
}

impl BoundMethod {
    pub(crate) fn new(receiver: Ptr, closure: Ptr) -> Self {
        Self {
            header: Header::new(),
            receiver,
            closure,
        }
    }
}

impl Rewrite for BoundMethod {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.receiver.rewrite(mapping);
        self.closure.rewrite(mapping);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Open {
    header: Header,
    /// The stack slot that holds the associated value.
    pub(crate) slot: Slot,
    /// Heap pointer to the next open upvalue.
    pub(crate) next: Option<Ptr>,
}

impl Open {
    pub(crate) fn new(slot: Slot, next: Option<Ptr>) -> Self {
        Self {
            header: Header::new(),
            slot,
            next,
        }
    }
}
impl Rewrite for Open {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.next.rewrite(mapping);
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Closed {
    header: Header,
    pub(crate) value: Value,
}

impl Closed {
    pub(crate) fn new(value: Value) -> Self {
        Self {
            header: Header::new(),
            value,
        }
    }
}
impl Rewrite for Closed {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.value.rewrite(mapping);
    }
}
