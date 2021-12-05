use std::collections::HashMap;

use crate::value::Value;

#[derive(Debug)]
pub struct Table {
    table: HashMap<String, Value>,
}

impl Table {
    pub fn new() -> Self {
        Self {
            table: HashMap::new(),
        }
    }

    pub fn set(&mut self, key: &str, val: Value) -> bool {
        match self.table.entry(key.to_string()) {
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

    pub fn get(&mut self, key: &str) -> Option<&Value> {
        self.table.get(key)
    }

    pub fn delete(&mut self, key: &str) -> Option<Value> {
        self.table.remove(key)
    }
}
