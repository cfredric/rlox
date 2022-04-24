use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::Debug,
    hash::Hash,
    ops::{Deref, DerefMut},
    ptr,
    rc::Rc,
};

use crate::obj::{Class, Closure, Function, Instance, LoxString, Obj, Open};

#[derive(Clone, Debug)]
pub(crate) struct Ptr(Rc<RefCell<Obj>>);

impl PartialEq for Ptr {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Ptr {}

impl Hash for Ptr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        ptr::hash(&*self.0, state);
    }
}

impl Deref for Ptr {
    type Target = Rc<RefCell<Obj>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Ptr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub(crate) fn allocate(obj: Obj) -> Ptr {
    Ptr(Rc::new(RefCell::new(obj)))
}

pub(crate) fn as_string(ptr: &Ptr) -> Ref<LoxString> {
    Ref::map(ptr.0.borrow(), |r| {
        r.as_string().expect("expected a LoxString")
    })
}
pub(crate) fn as_function(ptr: &Ptr) -> Ref<Function> {
    Ref::map(ptr.0.borrow(), |r| {
        r.as_function().expect("expected a Function")
    })
}
pub(crate) fn as_closure(ptr: &Ptr) -> Ref<Closure> {
    Ref::map(ptr.0.borrow(), |r| {
        r.as_closure().expect("expected a Closure")
    })
}
pub(crate) fn as_class(ptr: &Ptr) -> Ref<Class> {
    Ref::map(ptr.0.borrow(), |r| r.as_class().expect("expected a Class"))
}
pub(crate) fn as_class_mut(ptr: &Ptr) -> RefMut<Class> {
    RefMut::map(ptr.0.borrow_mut(), |r| {
        r.as_class_mut().expect("expected a Class")
    })
}
pub(crate) fn as_instance(ptr: &Ptr) -> Ref<Instance> {
    Ref::map(ptr.0.borrow(), |r| {
        r.as_instance().expect("expected an Instance")
    })
}
pub(crate) fn as_instance_mut(ptr: &Ptr) -> RefMut<Instance> {
    RefMut::map(ptr.0.borrow_mut(), |r| {
        r.as_instance_mut().expect("expected an Instance")
    })
}
pub(crate) fn as_open_up_value(ptr: &Ptr) -> Ref<Open> {
    Ref::map(ptr.0.borrow(), |r| {
        r.as_open_up_value().expect("expected an OpenUpValue")
    })
}
pub(crate) fn as_open_up_value_mut(ptr: &Ptr) -> RefMut<Open> {
    RefMut::map(ptr.0.borrow_mut(), |r| {
        r.as_open_up_value_mut().expect("expected an OpenUpValue")
    })
}
