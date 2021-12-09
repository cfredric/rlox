use enum_as_inner::EnumAsInner;
use std::fmt::Display;

use crate::{chunk::Chunk, table::Table};

#[derive(Debug, EnumAsInner)]
pub enum Obj {
    String(String),
    Function(Function),
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
