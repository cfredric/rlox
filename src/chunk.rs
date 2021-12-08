use crate::obj::Obj;
use crate::value::Value;

#[derive(Copy, Clone, Debug)]
pub enum OpCode {
    Constant(usize),
    Nil,
    Bool(bool),
    GetGlobal(usize),
    DefineGlobal(usize),
    SetGlobal(usize),
    GetLocal(usize),
    SetLocal(usize),
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
    JumpIfFalse(usize),
    Jump(usize),
    Loop(usize),
    Return,
}

impl OpCode {
    pub fn simple_instruction(&self, name: &str, _offset: usize) {
        println!("{}", name);
    }
}

#[derive(Default, Debug)]
pub struct Chunk {
    pub code: Vec<OpCode>,
    pub constants: Vec<Value>,
    pub lines: Vec<usize>,
}

impl Chunk {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn write_chunk(&mut self, op: OpCode, line: usize) {
        self.code.push(op);
        self.lines.push(line);
    }
    pub fn add_constant(&mut self, value: Value) -> usize {
        self.constants.push(value);
        self.constants.len() - 1
    }

    pub fn disassemble_chunk(&self, name: &str, heap: &[Obj]) {
        println!("== {} ==", name);

        for offset in 0..self.code.len() {
            self.disassemble_instruction(heap, offset);
        }
    }

    pub fn disassemble_instruction(&self, heap: &[Obj], offset: usize) {
        print!("{:04} ", offset);

        if offset > 0 && self.lines[offset] == self.lines[offset - 1] {
            print!("   | ");
        } else {
            print!("{:04} ", self.lines[offset]);
        }

        let op = &self.code[offset];
        match op {
            OpCode::Return => op.simple_instruction("OP_RETURN", offset),
            OpCode::Constant(i) => self.constant_instruction("OP_CONSTANT", heap, *i),
            OpCode::Negate => op.simple_instruction("OP_NEGATE", offset),
            OpCode::Add => op.simple_instruction("OP_ADD", offset),
            OpCode::Subtract => op.simple_instruction("OP_SUBTRACT", offset),
            OpCode::Multiply => op.simple_instruction("OP_MULTIPLY", offset),
            OpCode::Divide => op.simple_instruction("OP_DIVIDE", offset),
            OpCode::Nil => op.simple_instruction("OP_NIL", offset),
            OpCode::Bool(b) => {
                op.simple_instruction(if *b { "OP_TRUE" } else { "OP_FALSE" }, offset)
            }
            OpCode::Not => op.simple_instruction("OP_NOT", offset),
            OpCode::Equal => op.simple_instruction("OP_EQUAL", offset),
            OpCode::Greater => op.simple_instruction("OP_GREATER", offset),
            OpCode::Less => op.simple_instruction("OP_LESS", offset),
            OpCode::Print => op.simple_instruction("OP_PRINT", offset),
            OpCode::Pop => op.simple_instruction("OP_POP", offset),
            OpCode::DefineGlobal(i) => self.constant_instruction("OP_DEFINE_GLOBAL", heap, *i),
            OpCode::GetGlobal(i) => self.constant_instruction("OP_GET_GLOBAL", heap, *i),
            OpCode::SetGlobal(i) => self.constant_instruction("OP_SET_GLOBAL", heap, *i),
            OpCode::GetLocal(i) => self.byte_instruction("OP_GET_LOCAL", *i),
            OpCode::SetLocal(i) => self.byte_instruction("OP_SET_LOCAL", *i),
            OpCode::JumpIfFalse(distance) => {
                self.jump_instruction("OP_JUMP_IF_FALSE", *distance, true)
            }
            OpCode::Jump(distance) => self.jump_instruction("OP_JUMP", *distance, true),
            OpCode::Loop(distance) => self.jump_instruction("OP_LOOP", *distance, false),
        }
    }

    fn constant_instruction(&self, name: &str, heap: &[Obj], offset: usize) {
        println!("{:16} {}", name, self.constants[offset].print(heap));
    }

    fn byte_instruction(&self, name: &str, slot: usize) {
        println!("{:16} {}", name, slot);
    }

    fn jump_instruction(&self, name: &str, distance: usize, positive: bool) {
        let distance = distance as isize * if positive { 1 } else { -1 };
        println!("{:16} {}", name, distance);
    }
}
