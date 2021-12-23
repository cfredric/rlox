use std::collections::HashMap;

use crate::obj::LoxString;

#[derive(Debug, Clone)]
pub struct Table<V> {
    pub table: HashMap<LoxString, V>,
}

impl<V> Table<V> {
    pub fn new() -> Self {
        Self {
            table: HashMap::new(),
        }
    }

    pub fn set(&mut self, key: &str, val: V) -> bool {
        match self.table.entry(LoxString::new(key)) {
            std::collections::hash_map::Entry::Occupied(mut occ) => {
                occ.insert(val);
                false
            }
            std::collections::hash_map::Entry::Vacant(vac) => {
                vac.insert(val);
                true
            }
        }
    }

    pub fn get(&self, key: &str) -> Option<&V> {
        self.table.get(&LoxString::new(key))
    }

    pub fn delete(&mut self, key: &str) -> Option<V> {
        self.table.remove(&LoxString::new(key))
    }
}
