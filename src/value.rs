use std::collections::HashMap;

use enum_as_inner::EnumAsInner;

use crate::{
    heap::{Heap, Ptr},
    rewrite::Rewrite,
    to_string::ToString,
};

#[derive(Copy, Clone, Debug, EnumAsInner)]
pub(crate) enum Value {
    Nil,
    Bool(bool),
    Double(f64),
    ObjReference(Ptr),
}

const ERROR_MARGIN: f64 = 0.00000000001;

impl Value {
    pub(crate) fn is_falsey(&self) -> bool {
        match self {
            Value::Nil => true,
            Value::Bool(b) => !b,
            _ => false,
        }
    }

    pub(crate) fn equal(a: Value, b: Value) -> bool {
        use Value::*;
        match (a, b) {
            (Nil, Nil) => true,
            (Bool(a), Bool(b)) => a == b,
            (Double(f), Double(g)) => (f - g).abs() < ERROR_MARGIN,
            (ObjReference(i), ObjReference(j)) => i == j,
            _ => false,
        }
    }
}

impl ToString for Value {
    fn to_string(&self, heap: &Heap) -> String {
        match self {
            Value::Double(d) => d.to_string(),
            Value::Nil => "nil".to_string(),
            Value::Bool(b) => b.to_string(),
            Value::ObjReference(i) => heap[*i].to_string(heap),
        }
    }
}

impl Rewrite for Value {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        if let Value::ObjReference(i) = self {
            i.rewrite(mapping);
        }
    }
}
