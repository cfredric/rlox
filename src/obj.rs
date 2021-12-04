use std::fmt::Display;

use crate::value::Value;

pub enum Obj {
    String(String),
}

impl Obj {
    pub fn copy_string(heap: &mut Vec<Obj>, s: &str) -> Value {
        heap.push(Obj::String(s.to_string()));
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
