use std::fmt::Display;

use enum_as_inner::EnumAsInner;

use crate::heap::Ptr;

#[derive(Clone, Debug, EnumAsInner)]
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

    pub(crate) fn equals(self, b: Value) -> bool {
        use Value::*;
        match (self, b) {
            (Nil, Nil) => true,
            (Bool(a), Bool(b)) => a == b,
            (Double(f), Double(g)) => (f - g).abs() < ERROR_MARGIN,
            (ObjReference(i), ObjReference(j)) => i == j,
            _ => false,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Double(d) => write!(f, "{}", d),
            Value::ObjReference(i) => {
                write!(f, "{}", &i.borrow())
            }
        }
    }
}
