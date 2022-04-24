use std::{
    fmt::Display,
    ops::{Index, IndexMut},
};

use crate::value::Value;

#[derive(Clone, Copy, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct Slot(usize);

impl Slot {
    fn new(s: usize) -> Self {
        Self(s)
    }

    pub(crate) fn offset(&self, offset: StackSlotOffset) -> Self {
        Slot::new(self.0 + offset.0)
    }

    pub(crate) fn bottom() -> Self {
        Self(0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StackSlotOffset(pub(crate) usize);

impl StackSlotOffset {
    pub(crate) fn new(n: usize) -> Self {
        Self(n)
    }

    pub(crate) fn error() -> Self {
        Self(99999)
    }

    pub(crate) fn special() -> Self {
        Self(0)
    }
}

impl Display for StackSlotOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

pub(crate) struct Stack {
    stack: Vec<Value>,
}

impl Stack {
    pub(crate) fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub(crate) fn push(&mut self, value: Value) {
        self.stack.push(value);
    }

    /// Pops a value from the stack.
    pub(crate) fn pop(&mut self) -> Value {
        self.stack.pop().expect("stack should not have been empty")
    }

    pub(crate) fn peek(&self, offset: usize) -> &Value {
        &self.stack[self.stack.len() - 1 - offset]
    }

    pub(crate) fn top_slot(&self) -> Slot {
        self.offset_from_top_slot(0)
    }

    pub(crate) fn offset_from_top_slot(&self, offset: usize) -> Slot {
        Slot::new(self.stack.len() - offset - 1)
    }

    pub(crate) fn top_n(&self, n: usize) -> &[Value] {
        &self.stack[self.stack.len() - n..]
    }

    pub(crate) fn pop_n(&mut self, n: usize) {
        self.stack.truncate(self.stack.len() - n);
    }

    pub(crate) fn clear(&mut self) {
        self.stack.clear();
    }

    pub(crate) fn truncate_from(&mut self, slot: Slot) {
        self.stack.truncate(slot.0);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub(crate) fn iter_from(&self, s: Slot) -> impl Iterator<Item = &Value> + '_ {
        self.stack.iter().skip(s.0)
    }
}

impl Index<Slot> for Stack {
    type Output = Value;

    fn index(&self, slot: Slot) -> &Self::Output {
        &self.stack[slot.0]
    }
}

impl IndexMut<Slot> for Stack {
    fn index_mut(&mut self, slot: Slot) -> &mut Self::Output {
        &mut self.stack[slot.0]
    }
}
