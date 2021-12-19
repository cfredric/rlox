use enum_as_inner::EnumAsInner;
use std::fmt::Display;

use crate::{chunk::Chunk, table::Table, value::Value};

#[derive(Debug, EnumAsInner)]
pub enum Obj {
    String(String),
    Function(Function),
    Closure(Closure),
    NativeFn(NativeFn),
    UpValue(UpValue),
}

impl Obj {
    pub fn copy_string(heap: &mut Vec<Obj>, strings: &mut Table<usize>, s: &str) -> usize {
        if let Some(v) = strings.get(s) {
            return *v;
        }
        Obj::allocate_string(heap, strings, s.to_string())
    }

    pub fn take_string(heap: &mut Vec<Obj>, strings: &mut Table<usize>, s: String) -> usize {
        if let Some(v) = strings.get(&s) {
            return *v;
        }
        Obj::allocate_string(heap, strings, s)
    }

    fn allocate_string(heap: &mut Vec<Obj>, strings: &mut Table<usize>, s: String) -> usize {
        let c = s.to_string();
        let idx = Obj::allocate_object(heap, Obj::String(s));
        strings.set(&c, idx);
        idx
    }

    pub fn new_native(heap: &mut Vec<Obj>, f: NativeFn) -> usize {
        Self::allocate_object(heap, Obj::NativeFn(f))
    }

    pub fn new_closure(heap: &mut Vec<Obj>, func_index: usize, upvalues: Vec<usize>) -> usize {
        Self::allocate_object(heap, Obj::Closure(Closure::new(func_index, upvalues)))
    }

    pub fn new_upvalue(heap: &mut Vec<Obj>, upvalue: UpValue) -> usize {
        Self::allocate_object(heap, Obj::UpValue(upvalue))
    }

    pub fn allocate_object(heap: &mut Vec<Obj>, obj: Obj) -> usize {
        heap.push(obj);
        heap.len() - 1
    }
}

impl Display for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Obj::String(s) => write!(f, "{}", s.to_string()),
            Obj::Function(fun) => write!(f, "<fn {}>", fun.name),
            Obj::NativeFn(_) => write!(f, "<native fn>"),
            Obj::Closure(fun) => write!(f, "<closure (fn {})>", fun.function_index),
            Obj::UpValue(_) => write!(f, "upvalue"),
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
    fn new(function_index: usize, upvalues: Vec<usize>) -> Self {
        Self {
            function_index,
            upvalues,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct UpValue {
    /// Location is a pointer into the heap.
    pub location: usize,
}
