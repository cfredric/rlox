use std::fmt::Display;

use enum_as_inner::EnumAsInner;

use crate::{
    heap::{Heap, Ptr},
    obj::ObjWithContext,
    post_process_gc_sweep::{GcSweepData, PostProcessGcSweep},
};

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

impl PostProcessGcSweep for Value {
    fn process(&mut self, sweep_data: &GcSweepData) {
        if let Value::ObjReference(i) = self {
            i.process(sweep_data);
        }
    }
}

pub(crate) struct ValueWithContext<'a, 'opt> {
    val: &'a Value,
    heap: &'a Heap<'opt>,
}

impl<'a, 'opt> ValueWithContext<'a, 'opt> {
    pub(crate) fn new(val: &'a Value, heap: &'a Heap<'opt>) -> Self {
        Self { val, heap }
    }
}

impl<'a, 'opt> Display for ValueWithContext<'a, 'opt> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.val {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Double(d) => write!(f, "{}", d),
            Value::ObjReference(i) => {
                write!(f, "{}", ObjWithContext::new(&self.heap[i], self.heap))
            }
        }
    }
}
