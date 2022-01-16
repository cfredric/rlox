use crate::compiler::Upvalue;
use crate::heap::{Heap, Ptr};
use crate::obj::UpValueIndex;
use crate::print::Print;
use crate::rewrite::Rewrite;
use crate::stack::StackSlotOffset;
use crate::value::Value;

#[derive(Clone)]
pub enum OpCode {
    Constant(ConstantIndex),
    Nil,
    Bool(bool),
    GetGlobal(ConstantIndex),
    DefineGlobal(ConstantIndex),
    SetGlobal(ConstantIndex),
    GetLocal(StackSlotOffset),
    SetLocal(StackSlotOffset),
    Equal,
    Greater,
    Less,
    Add,
    Subtract,
    Multiply,
    Divide,
    Not,
    Negate,
    Pop,
    Print,
    /// Operand is the distance to jump.
    JumpIfFalse(usize),
    /// Operand is the distance to jump.
    Jump(usize),
    /// Operand is the distance to jump backwards.
    Loop(usize),
    /// Operand is the number of arguments passed to the callee.
    Call(usize),
    /// First operand is the index into the constants table of the method name;
    /// second operand is the argument count.
    Invoke(ConstantIndex, usize),
    /// First operand is the index into the constants table for the function;
    /// second operand is the list of upvalue metadata used by the closure.
    Closure(ConstantIndex, Vec<Upvalue>),
    CloseUpvalue,
    GetUpvalue(UpValueIndex),
    SetUpvalue(UpValueIndex),
    GetProperty(ConstantIndex),
    SetProperty(ConstantIndex),
    /// Operand is the index into the constants table for the superclass method name.
    GetSuper(ConstantIndex),
    /// First operand is the index into the constants table of the superclass method name;
    /// second operand is the argument count.
    SuperInvoke(ConstantIndex, usize),
    Return,
    Class(ConstantIndex),
    Inherit,
    Method(ConstantIndex),
}

#[derive(Default)]
pub struct Chunk {
    pub code: Vec<OpCode>,
    constants: Vec<Value>,
    pub lines: Vec<usize>,
}

#[derive(Copy, Clone)]
pub struct ConstantIndex(usize);

impl ConstantIndex {
    fn new(index: usize) -> Self {
        Self(index)
    }

    pub fn error() -> Self {
        Self(999999)
    }

    pub fn special() -> Self {
        Self(0)
    }
}

impl Chunk {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn write_chunk(&mut self, op: OpCode, line: usize) {
        self.code.push(op);
        self.lines.push(line);
    }

    pub fn add_constant(&mut self, value: Value) -> Option<ConstantIndex> {
        self.constants.push(value);
        if self.constants.len() > 2_usize.pow(8) {
            return None;
        }
        Some(ConstantIndex::new(self.constants.len() - 1))
    }

    pub fn constant_at(&self, index: ConstantIndex) -> Value {
        self.constants[index.0]
    }

    pub fn constants_iter<'s>(&'s self) -> impl Iterator<Item = &Value> + 's {
        self.constants.iter()
    }

    pub fn disassemble_chunk(&self, name: &str, heap: &Heap) {
        println!("== {} ==", name);

        for offset in 0..self.code.len() {
            self.disassemble_instruction(heap, offset);
        }
    }

    pub fn disassemble_instruction(&self, heap: &Heap, offset: usize) {
        print!("{:04} ", offset);

        if offset > 0 && self.lines[offset] == self.lines[offset - 1] {
            print!("   | ");
        } else {
            print!("{:04} ", self.lines[offset]);
        }

        match &self.code[offset] {
            OpCode::Return => simple_instruction("OP_RETURN"),
            OpCode::Constant(i) => self.constant_instruction("OP_CONSTANT", heap, *i),
            OpCode::Negate => simple_instruction("OP_NEGATE"),
            OpCode::Add => simple_instruction("OP_ADD"),
            OpCode::Subtract => simple_instruction("OP_SUBTRACT"),
            OpCode::Multiply => simple_instruction("OP_MULTIPLY"),
            OpCode::Divide => simple_instruction("OP_DIVIDE"),
            OpCode::Nil => simple_instruction("OP_NIL"),
            OpCode::Bool(b) => simple_instruction(if *b { "OP_TRUE" } else { "OP_FALSE" }),
            OpCode::Not => simple_instruction("OP_NOT"),
            OpCode::Equal => simple_instruction("OP_EQUAL"),
            OpCode::Greater => simple_instruction("OP_GREATER"),
            OpCode::Less => simple_instruction("OP_LESS"),
            OpCode::Print => simple_instruction("OP_PRINT"),
            OpCode::Pop => simple_instruction("OP_POP"),
            OpCode::DefineGlobal(i) => self.constant_instruction("OP_DEFINE_GLOBAL", heap, *i),
            OpCode::GetGlobal(i) => self.constant_instruction("OP_GET_GLOBAL", heap, *i),
            OpCode::SetGlobal(i) => self.constant_instruction("OP_SET_GLOBAL", heap, *i),
            OpCode::GetLocal(i) => byte_instruction("OP_GET_LOCAL", i.0),
            OpCode::SetLocal(i) => byte_instruction("OP_SET_LOCAL", i.0),
            OpCode::JumpIfFalse(distance) => jump_instruction("OP_JUMP_IF_FALSE", *distance, true),
            OpCode::Jump(distance) => jump_instruction("OP_JUMP", *distance, true),
            OpCode::Loop(distance) => jump_instruction("OP_LOOP", *distance, false),
            OpCode::Call(arity) => byte_instruction("OP_CALL", *arity),
            OpCode::Closure(constant, upvalues) => {
                print!("{:16} {} ", "OP_CLOSURE", constant.0);
                print!("{}", self.constant_at(*constant).print(heap));
                println!();

                println!(
                    "{}",
                    upvalues
                        .iter()
                        .map(|upvalue| {
                            let (ty, index) = match upvalue {
                                Upvalue::Local { index } => ("local", index.0),
                                Upvalue::Nonlocal { index } => ("upvalue", index.0),
                            };
                            format!("        |   {} {}", ty, index)
                        })
                        .collect::<String>()
                );
            }
            OpCode::GetUpvalue(index) => byte_instruction("OP_GET_UPVALUE", index.0),
            OpCode::SetUpvalue(index) => byte_instruction("OP_SET_UPVALUE", index.0),
            OpCode::CloseUpvalue => simple_instruction("OP_CLOSE_UPVALUE"),
            OpCode::Class(index) => self.constant_instruction("OP_CLASS", heap, *index),
            OpCode::GetProperty(constant) => {
                self.constant_instruction("OP_GET_PROPERTY", heap, *constant)
            }
            OpCode::SetProperty(constant) => {
                self.constant_instruction("OP_SET_PROPERTY", heap, *constant)
            }
            OpCode::Method(constant) => self.constant_instruction("OP_METHOD", heap, *constant),
            OpCode::Invoke(constant, arg_count) => {
                invoke_instruction("OP_INVOKE", *constant, *arg_count)
            }
            OpCode::Inherit => simple_instruction("OP_INHERIT"),
            OpCode::GetSuper(c) => self.constant_instruction("OP_GET_SUPER", heap, *c),
            OpCode::SuperInvoke(name, arg_count) => {
                invoke_instruction("OP_SUPER_INVOKE", *name, *arg_count);
            }
        }
    }

    fn constant_instruction(&self, name: &str, heap: &Heap, index: ConstantIndex) {
        println!("{:16} {}", name, self.constant_at(index).print(heap));
    }
}

fn simple_instruction(name: &str) {
    println!("{}", name);
}
fn byte_instruction(name: &str, slot: usize) {
    println!("{:16} {}", name, slot);
}
fn jump_instruction(name: &str, distance: usize, positive: bool) {
    let distance = distance as isize * if positive { 1 } else { -1 };
    println!("{:16} {}", name, distance);
}

fn invoke_instruction(name: &str, constant: ConstantIndex, arg_count: usize) {
    println!("{:16} ({} args) {}", name, arg_count, constant.0)
}

impl Rewrite for Chunk {
    fn rewrite(&mut self, mapping: &std::collections::HashMap<Ptr, Ptr>) {
        self.constants.rewrite(mapping);
    }
}
