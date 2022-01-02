use crate::vm::Heap;

pub trait Print {
    fn print(&self, heap: &Heap) -> String;
}
