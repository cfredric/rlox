use crate::compiler::CompiledUpValue;
use crate::heap::{Heap, Ptr};
use crate::obj::UpValueIndex;
use crate::print::Print;
use crate::rewrite::Rewrite;
use crate::stack::StackSlotOffset;
use crate::value::Value;

#[derive(Clone)]
pub(crate) enum OpCode {
    Constant {
        index: ConstantIndex,
    },
    Nil,
    Bool {
        value: bool,
    },
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
    JumpIfFalse {
        distance: usize,
    },
    Jump {
        distance: usize,
    },
    Loop {
        distance_to_loop_start: usize,
    },
    Call {
        arg_count: usize,
    },
    Invoke {
        method_name: ConstantIndex,
        arg_count: usize,
    },
    Closure {
        function: ConstantIndex,
        upvalues: Vec<CompiledUpValue>,
    },
    CloseUpvalue,
    GetUpvalue(UpValueIndex),
    SetUpvalue(UpValueIndex),
    GetProperty {
        name: ConstantIndex,
    },
    SetProperty {
        name: ConstantIndex,
    },
    GetSuper {
        method: ConstantIndex,
    },
    SuperInvoke {
        method: ConstantIndex,
        arg_count: usize,
    },
    Return,
    Class {
        name: ConstantIndex,
    },
    Inherit,
    Method {
        name: ConstantIndex,
    },
}

#[derive(Default)]
pub(crate) struct Chunk {
    pub(crate) code: Vec<OpCode>,
    constants: Vec<Value>,
    pub(crate) lines: Vec<usize>,
}

#[derive(Copy, Clone)]
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

impl Chunk {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn write_chunk(&mut self, op: OpCode, line: usize) {
        self.code.push(op);
        self.lines.push(line);
    }

    pub(crate) fn add_constant(&mut self, value: Value) -> Option<ConstantIndex> {
        self.constants.push(value);
        if self.constants.len() > 2_usize.pow(8) {
            return None;
        }
        Some(ConstantIndex::new(self.constants.len() - 1))
    }

    pub(crate) fn constant_at(&self, index: ConstantIndex) -> Value {
        self.constants[index.0]
    }

    pub(crate) fn constants_iter<'s>(&'s self) -> impl Iterator<Item = &Value> + 's {
        self.constants.iter()
    }

    pub(crate) fn disassemble_chunk(&self, name: &str, heap: &Heap) {
        println!("== {} ==", name);

        for offset in 0..self.code.len() {
            self.disassemble_instruction(heap, offset);
        }
    }

    pub(crate) fn disassemble_instruction(&self, heap: &Heap, offset: usize) {
        print!("{:04} ", offset);

        if offset > 0 && self.lines[offset] == self.lines[offset - 1] {
            print!("   | ");
        } else {
            print!("{:04} ", self.lines[offset]);
        }

        match &self.code[offset] {
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
            OpCode::Loop {
                distance_to_loop_start,
            } => jump_instruction("OP_LOOP", *distance_to_loop_start, false),
            OpCode::Call { arg_count } => byte_instruction("OP_CALL", *arg_count),
            OpCode::Closure { function, upvalues } => {
                print!("{:16} {} ", "OP_CLOSURE", function.0);
                print!("{}", self.constant_at(*function).print(heap));
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
