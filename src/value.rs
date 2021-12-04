use crate::obj::Obj;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Double(f64),
    ObjIndex(usize),
}

pub fn double(f: f64) -> Value {
    Value::Double(f)
}
pub fn vbool(b: bool) -> Value {
    Value::Bool(b)
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

    pub fn equal(heap: &[Obj], a: Value, b: Value) -> bool {
        use Value::*;
        match (a, b) {
            (Nil, Nil) => true,
            (Bool(a), Bool(b)) => a == b,
            (Double(f), Double(g)) => (f - g).abs() < ERROR_MARGIN,
            (ObjIndex(i), ObjIndex(j)) => {
                if i == j {
                    return true;
                }
                match (&heap[i], &heap[j]) {
                    (Obj::String(s1), Obj::String(s2)) => s1 == s2,
                }
            }
            _ => false,
        }
    }

    pub fn print(&self, heap: &[crate::obj::Obj]) -> String {
        match self {
            Value::Double(d) => d.to_string(),
            Value::Nil => "nil".to_string(),
            Value::Bool(b) => b.to_string(),
            Value::ObjIndex(i) => heap[*i].to_string(),
        }
    }
}
