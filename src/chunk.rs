use std::fmt::Display;
use std::ops::{Add, AddAssign, Index, IndexMut, Neg, Sub, SubAssign};

use crate::compiler::CompiledUpValue;
use crate::heap::{Heap, Ptr};
use crate::opcode::OpCode;
use crate::rewrite::Rewrite;
use crate::value::{Value, ValueWithContext};

#[derive(Clone)]
pub(crate) struct CodeEntry {
    pub op: OpCode,
    pub line: usize,
}

#[derive(Clone, Default)]
pub(crate) struct Chunk {
    code: Vec<CodeEntry>,
    constants: Vec<Value>,
}

impl std::fmt::Debug for Chunk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Chunk").finish()
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct ConstantIndex(usize);

impl ConstantIndex {
    fn new(index: usize) -> Self {
        Self(index)
    }

    pub(crate) fn error() -> Self {
        Self(999999)
    }

    pub(crate) fn special() -> Self {
        Self(0)
    }
}

impl Display for ConstantIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct OpCodeIndex(usize);

impl OpCodeIndex {
    pub(crate) fn zero() -> Self {
        Self(0)
    }

    pub(crate) fn increment(&mut self) {
        self.0 += 1;
    }

    pub(crate) fn distance_to(self, other: Self) -> OpCodeDelta {
        other - self
    }
}

impl Display for OpCodeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl AddAssign<OpCodeDelta> for OpCodeIndex {
    fn add_assign(&mut self, rhs: OpCodeDelta) {
        self.0 = (self.0 as isize + rhs.0) as usize
    }
}

impl Sub<usize> for OpCodeIndex {
    type Output = OpCodeIndex;

    fn sub(self, rhs: usize) -> Self::Output {
        OpCodeIndex(self.0 - rhs)
    }
}

impl Sub<OpCodeIndex> for OpCodeIndex {
    type Output = OpCodeDelta;

    fn sub(self, rhs: OpCodeIndex) -> Self::Output {
        OpCodeDelta(self.0 as isize - rhs.0 as isize)
    }
}

impl SubAssign<OpCodeDelta> for OpCodeIndex {
    fn sub_assign(&mut self, rhs: OpCodeDelta) {
        self.0 = (self.0 as isize - rhs.0) as usize;
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub(crate) struct OpCodeDelta(isize);

impl OpCodeDelta {
    pub(crate) fn zero() -> Self {
        Self(0)
    }

    pub(crate) const fn bound(b: isize) -> Self {
        Self(b)
    }
}

impl Display for OpCodeDelta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Neg for OpCodeDelta {
    type Output = OpCodeDelta;

    fn neg(self) -> Self::Output {
        OpCodeDelta(-self.0)
    }
}

impl Add<isize> for OpCodeDelta {
    type Output = OpCodeDelta;

    fn add(self, rhs: isize) -> Self::Output {
        OpCodeDelta(self.0 + rhs)
    }
}

impl Sub<isize> for OpCodeDelta {
    type Output = OpCodeDelta;

    fn sub(self, rhs: isize) -> Self::Output {
        OpCodeDelta(self.0 - rhs)
    }
}

impl Chunk {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn next_opcode_index(&self) -> OpCodeIndex {
        OpCodeIndex(self.code.len())
    }
    pub(crate) fn last_opcode_index(&self) -> OpCodeIndex {
        self.next_opcode_index() - 1
    }

    pub(crate) fn line_of(&self, index: OpCodeIndex) -> usize {
        self.code[index.0].line
    }

    pub(crate) fn append_opcode(&mut self, op: OpCode, line: usize) -> OpCodeIndex {
        self.code.push(CodeEntry { op, line });
        self.last_opcode_index()
    }

    pub(crate) fn append_constant(&mut self, value: Value) -> Option<ConstantIndex> {
        self.constants.push(value);
        if self.constants.len() > 2_usize.pow(8) {
            return None;
        }
        Some(ConstantIndex::new(self.constants.len() - 1))
    }

    pub(crate) fn constants_iter<'s>(&'s self) -> impl Iterator<Item = &Value> + 's {
        self.constants.iter()
    }

    pub(crate) fn disassemble_chunk(&self, name: &str, heap: &Heap) {
        println!("== {} ==", name);

        let mut prev_line = None;
        for index in 0..self.code.len() {
            let index = OpCodeIndex(index);
            print!("{:04} ", index);

            let current_line = self.line_of(index);
            if prev_line == Some(current_line) {
                print!("   | ");
            } else {
                print!("{:04} ", self.line_of(index));
            }
            self.disassemble_instruction(heap, index);
            prev_line = Some(current_line);
        }
    }

    pub(crate) fn disassemble_instruction(&self, heap: &Heap, index: OpCodeIndex) {
        match &self[index] {
            OpCode::Return => println!("OP_RETURN"),
            OpCode::Constant { index } => {
                unary_instruction("OP_CONSTANT", ValueWithContext::new(self[*index], heap))
            }
            OpCode::Negate => println!("OP_NEGATE"),
            OpCode::Add => println!("OP_ADD"),
            OpCode::Subtract => println!("OP_SUBTRACT"),
            OpCode::Multiply => println!("OP_MULTIPLY"),
            OpCode::Divide => println!("OP_DIVIDE"),
            OpCode::Nil => println!("OP_NIL"),
            OpCode::Bool { value } => {
                println!("{}", if *value { "OP_TRUE" } else { "OP_FALSE" })
            }
            OpCode::Not => println!("OP_NOT"),
            OpCode::Equal => println!("OP_EQUAL"),
            OpCode::Greater => println!("OP_GREATER"),
            OpCode::Less => println!("OP_LESS"),
            OpCode::Print => println!("OP_PRINT"),
            OpCode::Pop => println!("OP_POP"),
            OpCode::DefineGlobal(i) => {
                unary_instruction("OP_DEFINE_GLOBAL", ValueWithContext::new(self[*i], heap))
            }
            OpCode::GetGlobal(i) => {
                unary_instruction("OP_GET_GLOBAL", ValueWithContext::new(self[*i], heap))
            }
            OpCode::SetGlobal(i) => {
                unary_instruction("OP_SET_GLOBAL", ValueWithContext::new(self[*i], heap))
            }
            OpCode::GetLocal(i) => unary_instruction("OP_GET_LOCAL", *i),
            OpCode::SetLocal(i) => unary_instruction("OP_SET_LOCAL", *i),
            OpCode::JumpIfFalse { distance } => unary_instruction("OP_JUMP_IF_FALSE", *distance),
            OpCode::Jump { distance } => unary_instruction("OP_JUMP", *distance),
            OpCode::Call { arg_count } => unary_instruction("OP_CALL", *arg_count),
            OpCode::Closure { function, upvalues } => {
                println!(
                    "{:16} {} {}",
                    "OP_CLOSURE",
                    function.0,
                    ValueWithContext::new(self[*function], heap)
                );

                for upvalue in upvalues {
                    let (ty, index) = match upvalue {
                        CompiledUpValue::Local { index } => ("local", index.0),
                        CompiledUpValue::Nonlocal { index } => ("upvalue", index.0),
                    };
                    println!("        | {:7} {}", ty, index)
                }
            }
            OpCode::GetUpvalue(index) => unary_instruction("OP_GET_UPVALUE", index),
            OpCode::SetUpvalue(index) => unary_instruction("OP_SET_UPVALUE", index),
            OpCode::CloseUpvalue => println!("OP_CLOSE_UPVALUE"),
            OpCode::Class { name } => {
                unary_instruction("OP_CLASS", ValueWithContext::new(self[*name], heap))
            }
            OpCode::GetProperty { name } => {
                unary_instruction("OP_GET_PROPERTY", ValueWithContext::new(self[*name], heap))
            }
            OpCode::SetProperty { name } => {
                unary_instruction("OP_SET_PROPERTY", ValueWithContext::new(self[*name], heap))
            }
            OpCode::Method { name } => {
                unary_instruction("OP_METHOD", ValueWithContext::new(self[*name], heap))
            }
            OpCode::Invoke {
                method_name,
                arg_count,
            } => invoke_instruction("OP_INVOKE", *method_name, *arg_count),
            OpCode::Inherit => println!("OP_INHERIT"),
            OpCode::GetSuper { method } => {
                unary_instruction("OP_GET_SUPER", ValueWithContext::new(self[*method], heap))
            }
            OpCode::SuperInvoke { method, arg_count } => {
                invoke_instruction("OP_SUPER_INVOKE", *method, *arg_count);
            }
        }
    }
}

impl Index<OpCodeIndex> for Chunk {
    type Output = OpCode;

    fn index(&self, index: OpCodeIndex) -> &Self::Output {
        &self.code[index.0].op
    }
}

impl IndexMut<OpCodeIndex> for Chunk {
    fn index_mut(&mut self, index: OpCodeIndex) -> &mut Self::Output {
        &mut self.code[index.0].op
    }
}

impl Index<ConstantIndex> for Chunk {
    type Output = Value;

    fn index(&self, index: ConstantIndex) -> &Self::Output {
        &self.constants[index.0]
    }
}

fn unary_instruction<D: Display>(name: &str, d: D) {
    println!("{:16} {}", name, d);
}
fn invoke_instruction(name: &str, constant: ConstantIndex, arg_count: usize) {
    println!("{:16} ({} args) {}", name, arg_count, constant)
}

impl Rewrite for Chunk {
    fn rewrite(&mut self, mapping: &std::collections::HashMap<Ptr, Ptr>) {
        self.constants.rewrite(mapping);
    }
}
