use crate::heap::Heap;

pub trait Print {
    fn print(&self, heap: &Heap) -> String;
}
