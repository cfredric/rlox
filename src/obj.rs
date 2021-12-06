use std::fmt::Display;

use crate::table::Table;

#[derive(Debug)]
pub enum Obj {
    String(String),
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

    fn allocate_object(heap: &mut Vec<Obj>, obj: Obj) -> usize {
        heap.push(obj);
        heap.len() - 1
    }
}

impl Display for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Obj::String(s) => write!(f, "{}", s.to_string()),
        }
    }
}
