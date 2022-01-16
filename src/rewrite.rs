use std::collections::HashMap;

use crate::heap::Ptr;

pub trait Rewrite {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>);
}

impl<T: Rewrite> Rewrite for Vec<T> {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        for e in self {
            e.rewrite(mapping);
        }
    }
}

impl<T: Rewrite> Rewrite for [T] {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        for e in self {
            e.rewrite(mapping);
        }
    }
}

impl<K, V: Rewrite> Rewrite for HashMap<K, V> {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        for v in self.values_mut() {
            v.rewrite(mapping);
        }
    }
}

impl<T: Rewrite> Rewrite for Option<T> {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        if let Some(t) = self {
            t.rewrite(mapping);
        }
    }
}

impl<T: Rewrite> Rewrite for &mut T {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        (*self).rewrite(mapping);
    }
}
