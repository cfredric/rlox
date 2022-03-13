use std::collections::HashMap;

use crate::{
    obj::{Class, Closure, Function, Instance, LoxString, Obj, Open},
    rewrite::Rewrite,
    to_string::ToString,
    value::Value,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub(crate) struct Ptr(usize);

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

impl ToString for Ptr {
    fn to_string(&self, heap: &Heap) -> String {
        heap.deref(*self).to_string(heap)
    }
}

pub(crate) struct Heap {
    heap: Vec<Obj>,

    /// Vector of heap indices, used during GC.
    gray_stack: Vec<Ptr>,

    log_gc: bool,
}

impl Heap {
    pub(crate) fn new(log_gc: bool) -> Self {
        Self {
            heap: Vec::new(),
            gray_stack: Vec::new(),
            log_gc,
        }
    }

    pub(crate) fn bytes_allocated(&self) -> usize {
        std::mem::size_of::<Obj>() * self.heap.len()
    }

    pub(crate) fn mark_value(&mut self, value: Value) {
        if self.log_gc {
            eprintln!("    mark value ({})", value.to_string(self));
        }
        if let Value::ObjReference(ptr) = value {
            self.mark_object(ptr);
        }
    }

    pub(crate) fn mark_object(&mut self, ptr: Ptr) {
        if self.log_gc {
            eprintln!(
                "{:3} mark object {}",
                ptr.0,
                self.heap[ptr.0].to_string(self)
            );
        }

        if self.heap[ptr.0].is_marked() {
            return;
        }

        self.heap[ptr.0].mark(true);

        self.gray_stack.push(ptr);
    }

    pub(crate) fn trace_references(&mut self) {
        while let Some(ptr) = self.gray_stack.pop() {
            self.blacken_object(ptr);
        }
    }

    pub(crate) fn blacken_object(&mut self, ptr: Ptr) {
        if self.log_gc {
            eprintln!("{} blacken {}", ptr.0, self.heap[ptr.0].to_string(self));
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
                let uvs = c.upvalues().cloned().collect::<Vec<_>>();
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

    pub(crate) fn sweep_and_compact(&mut self) -> HashMap<Ptr, Ptr> {
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
        self.heap.retain(|obj| obj.is_marked());
        for obj in self.heap.iter_mut() {
            obj.mark(false);
        }

        mapping
    }

    pub(crate) fn deref(&self, ptr: Ptr) -> &Obj {
        &self.heap[ptr.0]
    }
    pub(crate) fn deref_mut(&mut self, ptr: Ptr) -> &mut Obj {
        &mut self.heap[ptr.0]
    }

    pub(crate) fn assign(&mut self, ptr: Ptr, obj: Obj) {
        self.heap[ptr.0] = obj;
    }

    pub(crate) fn push(&mut self, obj: Obj) -> Ptr {
        self.heap.push(obj);
        Ptr::new(self.heap.len() - 1)
    }

    pub(crate) fn as_string(&self, ptr: Ptr) -> &LoxString {
        self.heap[ptr.0].as_string().expect("expected a LoxString")
    }
    pub(crate) fn as_function(&self, ptr: Ptr) -> &Function {
        self.heap[ptr.0].as_function().expect("expected a Function")
    }
    pub(crate) fn as_closure(&self, ptr: Ptr) -> &Closure {
        self.heap[ptr.0].as_closure().expect("expected a Closure")
    }
    pub(crate) fn as_class(&self, ptr: Ptr) -> &Class {
        self.heap[ptr.0].as_class().expect("expected a Class")
    }
    pub(crate) fn as_class_mut(&mut self, ptr: Ptr) -> &mut Class {
        self.heap[ptr.0].as_class_mut().expect("expected a Class")
    }
    pub(crate) fn as_instance(&self, ptr: Ptr) -> &Instance {
        self.heap[ptr.0]
            .as_instance()
            .expect("expected an Instance")
    }
    pub(crate) fn as_instance_mut(&mut self, ptr: Ptr) -> &mut Instance {
        self.heap[ptr.0]
            .as_instance_mut()
            .expect("expected an Instance")
    }
    pub(crate) fn as_open_up_value(&self, ptr: Ptr) -> &Open {
        self.heap[ptr.0]
            .as_open_up_value()
            .expect("expected an OpenUpValue")
    }
    pub(crate) fn as_open_up_value_mut(&mut self, ptr: Ptr) -> &mut Open {
        self.heap[ptr.0]
            .as_open_up_value_mut()
            .expect("expected an OpenUpValue")
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = &Obj> + '_ {
        self.heap.iter()
    }

    pub(crate) fn open_upvalues(&self) -> impl Iterator<Item = Ptr> + '_ {
        self.heap
            .iter()
            .enumerate()
            .filter_map(|(i, o)| o.as_open_up_value().map(|_| Ptr::new(i)))
    }

    pub(crate) fn len(&self) -> usize {
        self.heap.len()
    }
}

impl Rewrite for Heap {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.heap.rewrite(mapping);
    }
}
