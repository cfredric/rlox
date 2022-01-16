use std::collections::HashMap;

use crate::{
    obj::{Class, Closure, Function, Instance, LoxString, Obj, Open},
    print::Print,
    rewrite::Rewrite,
    value::Value,
};

#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Ptr(usize);

impl Ptr {
    fn new(index: usize) -> Self {
        Self(index)
    }
}

impl Rewrite for Ptr {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        *self = mapping[self];
    }
}

pub struct Heap {
    heap: Vec<Obj>,

    /// Vector of heap indices, used during GC.
    gray_stack: Vec<Ptr>,

    log_gc: bool,
}

impl Heap {
    pub fn new(log_gc: bool) -> Self {
        Self {
            heap: Vec::new(),
            gray_stack: Vec::new(),
            log_gc,
        }
    }

    pub fn mark_value(&mut self, value: Value) {
        if self.log_gc {
            eprintln!("    mark value ({})", value.print(self));
        }
        match value {
            Value::Nil | Value::Bool(_) | Value::Double(_) => {}
            Value::ObjReference(index) => {
                self.mark_object(index);
            }
        }
    }

    pub fn mark_object(&mut self, ptr: Ptr) {
        if self.log_gc {
            eprintln!("{:3} mark object {}", ptr.0, self.heap[ptr.0].print(self));
        }

        if self.heap[ptr.0].is_marked() {
            return;
        }

        self.heap[ptr.0].mark(true);

        self.gray_stack.push(ptr);
    }

    pub fn trace_references(&mut self) {
        while let Some(ptr) = self.gray_stack.pop() {
            self.blacken_object(ptr);
        }
    }

    pub fn blacken_object(&mut self, ptr: Ptr) {
        if self.log_gc {
            eprintln!("{} blacken {}", ptr.0, self.heap[ptr.0].print(self));
        }

        match &self.heap[ptr.0] {
            Obj::String(_) | Obj::NativeFn(_) | Obj::OpenUpValue(_) => {}
            Obj::Function(f) => {
                // TODO: don't clone here.
                for v in f.chunk.constants_iter().cloned().collect::<Vec<_>>() {
                    self.mark_value(v);
                }
            }
            Obj::Closure(c) => {
                let func = c.function;
                let uvs = c.upvalues.clone();
                self.mark_object(func);
                for uv in &uvs {
                    self.mark_object(*uv);
                }
            }
            Obj::ClosedUpValue(c) => {
                let v = c.value;
                self.mark_value(v);
            }
            Obj::Class(c) => {
                let methods = c.methods.values().copied().collect::<Vec<_>>();
                for m in methods {
                    self.mark_object(m);
                }
            }
            Obj::Instance(i) => {
                let class = i.class;
                let field_values = i.fields.values().copied().collect::<Vec<_>>();
                self.mark_object(class);
                for value in field_values {
                    self.mark_value(value);
                }
            }
            Obj::BoundMethod(b) => {
                let r = b.receiver;
                let c = b.closure;
                self.mark_object(r);
                self.mark_object(c);
            }
        }
    }

    pub fn sweep_and_compact(&mut self) -> (HashMap<Ptr, Ptr>, usize) {
        // Build the mapping from pre-sweep pointers to post-sweep pointers.
        let mapping = self
            .heap
            .iter()
            .enumerate()
            .filter_map(|(i, obj)| obj.is_marked().then(|| i))
            .enumerate()
            .map(|(post, pre)| (Ptr::new(pre), Ptr::new(post)))
            .collect();

        // Remove unreachable objects.
        let before = self.heap.len();
        self.heap.retain(|obj| obj.is_marked());
        for obj in self.heap.iter_mut() {
            obj.mark(false);
        }

        (mapping, before - self.heap.len())
    }

    pub fn deref(&self, ptr: Ptr) -> &Obj {
        &self.heap[ptr.0]
    }
    pub fn deref_mut(&mut self, ptr: Ptr) -> &mut Obj {
        &mut self.heap[ptr.0]
    }

    pub fn assign(&mut self, ptr: Ptr, obj: Obj) {
        self.heap[ptr.0] = obj;
    }

    pub fn push(&mut self, obj: Obj) -> Ptr {
        self.heap.push(obj);
        Ptr::new(self.heap.len() - 1)
    }

    pub fn as_string(&self, ptr: Ptr) -> &LoxString {
        self.heap[ptr.0].as_string().unwrap()
    }
    pub fn as_function(&self, ptr: Ptr) -> &Function {
        self.heap[ptr.0].as_function().unwrap()
    }
    pub fn as_closure(&self, ptr: Ptr) -> &Closure {
        self.heap[ptr.0].as_closure().unwrap()
    }
    pub fn as_class(&self, ptr: Ptr) -> &Class {
        self.heap[ptr.0].as_class().unwrap()
    }
    pub fn as_class_mut(&mut self, ptr: Ptr) -> &mut Class {
        self.heap[ptr.0].as_class_mut().unwrap()
    }
    pub fn as_instance(&self, ptr: Ptr) -> &Instance {
        self.heap[ptr.0].as_instance().unwrap()
    }
    pub fn as_instance_mut(&mut self, ptr: Ptr) -> &mut Instance {
        self.heap[ptr.0].as_instance_mut().unwrap()
    }
    pub fn as_open_up_value(&self, ptr: Ptr) -> &Open {
        self.heap[ptr.0].as_open_up_value().unwrap()
    }
    pub fn as_open_up_value_mut(&mut self, ptr: Ptr) -> &mut Open {
        self.heap[ptr.0].as_open_up_value_mut().unwrap()
    }

    pub fn iter<'s>(&'s self) -> impl Iterator<Item = &Obj> + 's {
        self.heap.iter()
    }

    pub fn open_upvalues<'s>(&'s self) -> impl Iterator<Item = Ptr> + 's {
        self.heap
            .iter()
            .enumerate()
            .filter_map(|(i, o)| o.as_open_up_value().map(|_| Ptr::new(i)))
    }
}

impl Rewrite for Heap {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.heap.rewrite(mapping);
    }
}
