use crate::heap::Heap;

pub(crate) trait Print {
    fn print(&self, heap: &Heap) -> String;
}
