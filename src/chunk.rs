use std::ops::{Add, AddAssign, Index, IndexMut, Sub, SubAssign};

use crate::compiler::CompiledUpValue;
use crate::heap::{Heap, Ptr};
use crate::opcode::OpCode;
use crate::rewrite::Rewrite;
use crate::to_string::ToString;
use crate::value::Value;

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

#[derive(Copy, Clone, Debug)]
pub(crate) struct OpCodeIndex(usize);

impl OpCodeIndex {
    pub(crate) fn zero() -> Self {
        Self(0)
    }

    pub(crate) fn increment(&mut self) {
        self.0 += 1;
    }
}

impl AddAssign<OpCodeDelta> for OpCodeIndex {
    fn add_assign(&mut self, rhs: OpCodeDelta) {
        self.0 += rhs.0;
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
        OpCodeDelta(self.0 - rhs.0)
    }
}

impl SubAssign<OpCodeDelta> for OpCodeIndex {
    fn sub_assign(&mut self, rhs: OpCodeDelta) {
        self.0 -= rhs.0;
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialOrd, PartialEq)]
pub(crate) struct OpCodeDelta(usize);

impl OpCodeDelta {
    pub(crate) fn zero() -> Self {
        Self(0)
    }

    pub(crate) const fn bound(b: usize) -> Self {
        Self(b)
    }
}

impl Add<usize> for OpCodeDelta {
    type Output = OpCodeDelta;

    fn add(self, rhs: usize) -> Self::Output {
        OpCodeDelta(self.0 + rhs)
    }
}

impl Chunk {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn next_opcode_index(&self) -> OpCodeIndex {
        OpCodeIndex(self.code.len())
    }

    pub(crate) fn line_of(&self, index: OpCodeIndex) -> usize {
        self.code[index.0].line
    }

    pub(crate) fn write_chunk(&mut self, op: OpCode, line: usize) -> OpCodeIndex {
        self.code.push(CodeEntry { op, line });
        OpCodeIndex(self.code.len() - 1)
    }

    pub(crate) fn distance_from(&self, op: OpCodeIndex) -> OpCodeDelta {
        OpCodeDelta(self.code.len() - op.0 - 1)
    }

    pub(crate) fn add_constant(&mut self, value: Value) -> Option<ConstantIndex> {
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

        for offset in 0..self.code.len() {
            self.disassemble_instruction(heap, OpCodeIndex(offset));
        }
    }

    pub(crate) fn disassemble_instruction(&self, heap: &Heap, index: OpCodeIndex) {
        print!("{:04} ", index.0);

        if index.0 > 0 && self.line_of(index) == self.line_of(index - 1) {
            print!("   | ");
        } else {
            print!("{:04} ", self.line_of(index));
        }

        match &self[index] {
            OpCode::Return => simple_instruction("OP_RETURN"),
            OpCode::Constant { index } => self.constant_instruction("OP_CONSTANT", heap, *index),
            OpCode::Negate => simple_instruction("OP_NEGATE"),
            OpCode::Add => simple_instruction("OP_ADD"),
            OpCode::Subtract => simple_instruction("OP_SUBTRACT"),
            OpCode::Multiply => simple_instruction("OP_MULTIPLY"),
            OpCode::Divide => simple_instruction("OP_DIVIDE"),
            OpCode::Nil => simple_instruction("OP_NIL"),
            OpCode::Bool { value } => {
                simple_instruction(if *value { "OP_TRUE" } else { "OP_FALSE" })
            }
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
            OpCode::JumpIfFalse { distance } => {
                jump_instruction("OP_JUMP_IF_FALSE", *distance, true)
            }
            OpCode::Jump { distance } => jump_instruction("OP_JUMP", *distance, true),
            OpCode::BackwardJump { distance } => jump_instruction("OP_BACK_JUMP", *distance, false),
            OpCode::Call { arg_count } => byte_instruction("OP_CALL", *arg_count),
            OpCode::Closure { function, upvalues } => {
                print!("{:16} {} ", "OP_CLOSURE", function.0);
                print!("{}", self[*function].to_string(heap));
                println!();

                println!(
                    "{}",
                    upvalues
                        .iter()
                        .map(|upvalue| {
                            let (ty, index) = match upvalue {
                                CompiledUpValue::Local { index } => ("local", index.0),
                                CompiledUpValue::Nonlocal { index } => ("upvalue", index.0),
                            };
                            format!("        |   {} {}", ty, index)
                        })
                        .collect::<String>()
                );
            }
            OpCode::GetUpvalue(index) => byte_instruction("OP_GET_UPVALUE", index.0),
            OpCode::SetUpvalue(index) => byte_instruction("OP_SET_UPVALUE", index.0),
            OpCode::CloseUpvalue => simple_instruction("OP_CLOSE_UPVALUE"),
            OpCode::Class { name } => self.constant_instruction("OP_CLASS", heap, *name),
            OpCode::GetProperty { name } => {
                self.constant_instruction("OP_GET_PROPERTY", heap, *name)
            }
            OpCode::SetProperty { name } => {
                self.constant_instruction("OP_SET_PROPERTY", heap, *name)
            }
            OpCode::Method { name } => self.constant_instruction("OP_METHOD", heap, *name),
            OpCode::Invoke {
                method_name,
                arg_count,
            } => invoke_instruction("OP_INVOKE", *method_name, *arg_count),
            OpCode::Inherit => simple_instruction("OP_INHERIT"),
            OpCode::GetSuper { method } => self.constant_instruction("OP_GET_SUPER", heap, *method),
            OpCode::SuperInvoke { method, arg_count } => {
                invoke_instruction("OP_SUPER_INVOKE", *method, *arg_count);
            }
        }
    }

    fn constant_instruction(&self, name: &str, heap: &Heap, index: ConstantIndex) {
        println!("{:16} {}", name, self[index].to_string(heap));
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

fn simple_instruction(name: &str) {
    println!("{}", name);
}
fn byte_instruction(name: &str, slot: usize) {
    println!("{:16} {}", name, slot);
}
fn jump_instruction(name: &str, distance: OpCodeDelta, positive: bool) {
    let distance = distance.0 as isize * if positive { 1 } else { -1 };
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
