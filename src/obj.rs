use enum_as_inner::EnumAsInner;

use crate::{chunk::Chunk, table::Table, value::Value};

#[derive(Debug, EnumAsInner)]
pub enum Obj {
    String(String),
    Function(Function),
    Closure(Closure),
    NativeFn(NativeFn),
    UpValue(UpValue),
}

impl Obj {
    pub fn copy_string(heap: &mut Vec<Obj>, strings: &mut Table<usize>, s: &str) -> usize {
        if let Some(v) = strings.get(s) {
            return *v;
        }
        Obj::allocate_string(heap, strings, s.to_string())
    }

    pub fn take_string(heap: &mut Vec<Obj>, strings: &mut Table<usize>, s: String) -> usize {
        if let Some(v) = strings.get(&s) {
            return *v;
        }
        Obj::allocate_string(heap, strings, s)
    }

    fn allocate_string(heap: &mut Vec<Obj>, strings: &mut Table<usize>, s: String) -> usize {
        let idx = Obj::allocate_object(heap, Obj::String(s));
        strings.set(heap[idx].as_string().unwrap(), idx);
        idx
    }

    pub fn new_function(heap: &mut Vec<Obj>, f: Function) -> usize {
        Self::allocate_object(heap, Obj::Function(f))
    }

    pub fn new_native(heap: &mut Vec<Obj>, f: NativeFn) -> usize {
        Self::allocate_object(heap, Obj::NativeFn(f))
    }

    pub fn new_closure(heap: &mut Vec<Obj>, func_index: usize, upvalues: Vec<usize>) -> usize {
        Self::allocate_object(heap, Obj::Closure(Closure::new(func_index, upvalues)))
    }

    pub fn new_upvalue(heap: &mut Vec<Obj>, upvalue: UpValue) -> usize {
        Self::allocate_object(heap, Obj::UpValue(upvalue))
    }

    pub fn allocate_object(heap: &mut Vec<Obj>, obj: Obj) -> usize {
        heap.push(obj);
        heap.len() - 1
    }

    pub fn print(&self, heap: &[Obj]) -> String {
        match self {
            Obj::String(s) => s.to_string(),
            Obj::Function(fun) => format!("<fn {}>", fun.name),
            Obj::NativeFn(_) => "<native fn>".to_string(),
            Obj::Closure(fun) => format!(
                "<closure (fn {})>",
                heap[fun.function_index].as_function().unwrap().name
            ),
            Obj::UpValue(upvalue) => format!("upvalue {:?}", upvalue),
        }
    }
}

#[derive(Debug)]
pub struct Function {
    pub arity: usize,
    pub chunk: Chunk,
    pub name: String,
}

impl Function {
    pub fn new(name: &str) -> Self {
        Self {
            arity: 0,
            name: name.to_string(),
            chunk: Chunk::new(),
        }
    }
}

pub type NativeFn = fn(args: Vec<Value>) -> Value;

#[derive(Debug)]
pub struct Closure {
    /// The heap index of the underlying function.
    pub function_index: usize,
    /// Pointers into the heap.
    pub upvalues: Vec<usize>,
}

impl Closure {
    fn new(function_index: usize, upvalues: Vec<usize>) -> Self {
        Self {
            function_index,
            upvalues,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct UpValue {
    /// The value.
    pub value: OpenOrClosed,
    /// next is a pointer into the heap, to another UpValue object. This forms a linked list.
    pub next: Option<usize>,
}

impl UpValue {
    /// Returns true iff this upvalue points (or used to point) at or above the
    /// given stack slot.
    pub fn is_at_or_above(&self, stack_slot: usize) -> bool {
        self.value.is_at_or_above(stack_slot)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum OpenOrClosed {
    /// Open holds a pointer into the stack.
    Open(usize),
    /// Value holds the old stack slot (for sorting), and a closed-over value.
    Closed(usize, Value),
}

impl OpenOrClosed {
    fn is_at_or_above(&self, stack_slot: usize) -> bool {
        let loc = match self {
            OpenOrClosed::Open(loc) => *loc,
            OpenOrClosed::Closed(loc, _) => *loc,
        };
        loc >= stack_slot
    }
}
