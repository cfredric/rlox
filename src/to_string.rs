use crate::heap::Heap;

pub(crate) trait ToString {
    fn to_string(&self, heap: &Heap) -> String;
}
