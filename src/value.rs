use std::fmt::Display;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Double(f64),
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
            Value::Double(_) => false,
        }
    }

    pub fn equal(a: Value, b: Value) -> bool {
        use Value::*;
        match (a, b) {
            (Nil, Nil) => true,
            (Bool(a), Bool(b)) => a == b,
            (Double(f), Double(g)) => (f - g).abs() < ERROR_MARGIN,
            _ => false,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Double(d) => write!(f, "{}", d),
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
        }
    }
}
