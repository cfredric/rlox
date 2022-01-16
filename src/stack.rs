use std::collections::HashMap;

use crate::{heap::Ptr, rewrite::Rewrite, value::Value};

#[derive(Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
pub struct Slot(usize);

impl Slot {
    pub fn new(s: usize) -> Self {
        Self(s)
    }

    pub fn offset(&self, offset: StackSlotOffset) -> Self {
        Slot::new(self.0 + offset.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct StackSlotOffset(pub usize);

impl StackSlotOffset {
    pub fn new(n: usize) -> Self {
        Self(n)
    }

    pub fn error() -> Self {
        Self(99999)
    }

    pub fn special() -> Self {
        Self(0)
    }
}

pub struct Stack {
    stack: Vec<Value>,
}

impl Stack {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    /// Pops a value from the stack.
    pub fn pop(&mut self) -> Value {
        self.stack.pop().unwrap()
    }

    pub fn peek(&self, offset: usize) -> Value {
        self.stack[self.stack.len() - 1 - offset]
    }

    pub fn top_slot(&self) -> Slot {
        self.from_top_slot(0)
    }

    pub fn from_top_slot(&self, offset: usize) -> Slot {
        Slot::new(self.stack.len() - offset - 1)
    }

    pub fn top_n(&self, n: usize) -> &[Value] {
        &self.stack[self.stack.len() - n..]
    }

    pub fn pop_n(&mut self, n: usize) {
        self.stack.truncate(self.stack.len() - n);
    }

    pub fn clear(&mut self) {
        self.stack.clear();
    }

    pub fn truncate_from(&mut self, slot: Slot) {
        self.stack.truncate(slot.0);
    }

    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub fn at(&self, slot: Slot) -> Value {
        self.stack[slot.0]
    }

    pub fn assign(&mut self, slot: Slot, val: Value) {
        self.stack[slot.0] = val;
    }

    pub fn iter(&self) -> impl Iterator<Item = &Value> + '_ {
        self.stack.iter()
    }
    pub fn iter_from(&self, s: Slot) -> impl Iterator<Item = &Value> + '_ {
        self.stack.iter().skip(s.0)
    }
}

impl Rewrite for Stack {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.stack.rewrite(mapping);
    }
}
