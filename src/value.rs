use std::collections::HashMap;

use enum_as_inner::EnumAsInner;

use crate::{rewrite::Rewrite, vm::Heap};

#[derive(Copy, Clone, EnumAsInner)]
pub enum Value {
    Nil,
    Bool(bool),
    Double(f64),
    ObjIndex(usize),
}

const ERROR_MARGIN: f64 = 0.00000000001;

impl Value {
    pub fn is_falsey(&self) -> bool {
        match self {
            Value::Nil => true,
            Value::Bool(b) => !b,
            _ => false,
        }
    }

    pub fn equal(a: Value, b: Value) -> bool {
        use Value::*;
        match (a, b) {
            (Nil, Nil) => true,
            (Bool(a), Bool(b)) => a == b,
            (Double(f), Double(g)) => (f - g).abs() < ERROR_MARGIN,
            (ObjIndex(i), ObjIndex(j)) => i == j,
            _ => false,
        }
    }

    pub fn print(&self, heap: &Heap) -> String {
        match self {
            Value::Double(d) => d.to_string(),
            Value::Nil => "nil".to_string(),
            Value::Bool(b) => b.to_string(),
            Value::ObjIndex(i) => heap.heap[*i].print(heap),
        }
    }
}

impl Rewrite for Value {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        if let Value::ObjIndex(i) = self {
            i.rewrite(mapping);
        }
    }
}
