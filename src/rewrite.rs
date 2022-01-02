use std::collections::HashMap;

pub trait Rewrite {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>);
}

impl<T: Rewrite> Rewrite for Vec<T> {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        for e in self {
            e.rewrite(mapping);
        }
    }
}

impl<T: Rewrite> Rewrite for [T] {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        for e in self {
            e.rewrite(mapping);
        }
    }
}

impl<K, V: Rewrite> Rewrite for HashMap<K, V> {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        for v in self.values_mut() {
            v.rewrite(mapping);
        }
    }
}

impl Rewrite for usize {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        *self = mapping[self];
    }
}

impl<T: Rewrite> Rewrite for Option<T> {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        if let Some(t) = self {
            t.rewrite(mapping);
        }
    }
}

impl<T: Rewrite> Rewrite for &mut T {
    fn rewrite(&mut self, mapping: &HashMap<usize, usize>) {
        (*self).rewrite(mapping);
    }
}
