use std::fmt::Display;

use crate::{table::Table, value::Value};

pub enum Obj {
    String(String),
}

impl Obj {
    pub fn copy_string(heap: &mut Vec<Obj>, strings: &mut Table, s: &str) -> Value {
        Obj::allocate_string(heap, strings, s.to_string())
    }

    pub fn take_string(heap: &mut Vec<Obj>, strings: &mut Table, s: String) -> Value {
        Obj::allocate_string(heap, strings, s)
    }

    fn allocate_string(heap: &mut Vec<Obj>, strings: &mut Table, s: String) -> Value {
        strings.set(&s, Value::Nil);
        Obj::allocate_object(heap, Obj::String(s))
    }

    fn allocate_object(heap: &mut Vec<Obj>, obj: Obj) -> Value {
        heap.push(obj);
        Value::ObjIndex(heap.len() - 1)
    }
}

impl Display for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Obj::String(s) => write!(f, "{}", s.to_string()),
        }
    }
}
