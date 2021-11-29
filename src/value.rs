use std::fmt::Display;

#[derive(Debug, PartialEq)]
pub enum Value {
    Double(f64),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Double(d) => write!(f, "{}", d),
        }
    }
}
