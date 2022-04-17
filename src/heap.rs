use std::{
    collections::HashMap,
    ops::{Index, IndexMut},
};

use crate::{
    obj::{Class, Closure, Function, Instance, LoxString, Obj, ObjWithContext, Open},
    rewrite::Rewrite,
    value::{Value, ValueWithContext},
    Opt,
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

pub(crate) struct Heap<'opt> {
    opt: &'opt Opt,
    heap: Vec<Obj>,

    /// Vector of heap indices, used during GC.
    gray_stack: Vec<Ptr>,
}

impl<'opt> Heap<'opt> {
    pub(crate) fn new(opt: &'opt Opt) -> Self {
        Self {
            opt,
            heap: Vec::new(),
            gray_stack: Vec::new(),
        }
    }

    pub(crate) fn bytes_allocated(&self) -> usize {
        std::mem::size_of::<Obj>() * self.heap.len()
    }

    pub(crate) fn mark_value(&mut self, value: Value) {
        if self.opt.log_garbage_collection {
            eprintln!("    mark value ({})", ValueWithContext::new(value, self));
        }
        if let Value::ObjReference(ptr) = value {
            self.mark_object(ptr);
        }
    }

    pub(crate) fn mark_object(&mut self, ptr: Ptr) {
        if self.opt.log_garbage_collection {
            eprintln!(
                "{:3} mark object {}",
                ptr.0,
                ObjWithContext::new(&self.heap[ptr.0], self)
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
        if self.opt.log_garbage_collection {
            eprintln!(
                "{} blacken {}",
                ptr.0,
                ObjWithContext::new(&self.heap[ptr.0], self)
            );
        }

        match &self.heap[ptr.0] {
            Obj::Dummy => {}
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
        let delta: i32 = match (self.opt.stress_garbage_collector, self.heap.get(0)) {
            (true, Some(Obj::Dummy)) => -1,
            (true, Some(_)) => 1,
            _ => 0,
        };
        let mapping = self
            .heap
            .iter()
            .enumerate()
            .filter_map(|(i, obj)| obj.is_marked().then(|| i))
            .enumerate()
            .map(|(post, pre)| (Ptr::new(pre), Ptr::new(((post as i32) + delta) as usize)))
            .collect::<HashMap<Ptr, Ptr>>();

        // Remove unreachable objects.
        self.heap.retain(|obj| obj.is_marked());
        for obj in self.heap.iter_mut() {
            obj.mark(false);
        }

        match delta {
            1 => {
                self.heap.insert(0, Obj::Dummy);
            }
            -1 => {
                self.heap.remove(0);
            }
            _ => {}
        }

        mapping
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

impl<'opt> Index<Ptr> for Heap<'opt> {
    type Output = Obj;

    fn index(&self, ptr: Ptr) -> &Self::Output {
        &self.heap[ptr.0]
    }
}

impl<'opt> IndexMut<Ptr> for Heap<'opt> {
    fn index_mut(&mut self, ptr: Ptr) -> &mut Self::Output {
        &mut self.heap[ptr.0]
    }
}

impl<'opt> Rewrite for Heap<'opt> {
    fn rewrite(&mut self, mapping: &HashMap<Ptr, Ptr>) {
        self.heap.rewrite(mapping);
    }
}
