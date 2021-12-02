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

impl Value {
    pub fn is_falsey(&self) -> bool {
        match self {
            Value::Nil => true,
            Value::Bool(b) => !b,
            Value::Double(_) => false,
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
