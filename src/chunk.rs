use crate::value::Value;

#[derive(Copy, Clone)]
pub enum OpCode {
    Constant(usize),
    Return,
}

impl OpCode {
    pub fn simple_instruction(&self, name: &str, _offset: usize) {
        println!("{}", name);
    }
}

pub struct Chunk {
    pub code: Vec<OpCode>,
    pub constants: Vec<Value>,
    lines: Vec<usize>,
}

impl Chunk {
    pub fn new() -> Self {
        Self {
            code: Vec::new(),
            constants: Vec::new(),
            lines: Vec::new(),
        }
    }
    pub fn write_chunk(&mut self, op: OpCode, line: usize) {
        self.code.push(op);
        self.lines.push(line);
    }
    pub fn add_constant(&mut self, value: Value) -> usize {
        self.constants.push(value);
        self.constants.len() - 1
    }

    pub fn disassemble_chunk(&self, name: &str) {
        println!("== {} ==", name);

        for offset in 0..self.code.len() {
            self.disassemble_instruction(offset);
        }
    }

    pub fn disassemble_instruction(&self, offset: usize) {
        print!("{:04} ", offset);

        if offset > 0 && self.lines[offset] == self.lines[offset - 1] {
            print!("   | ");
        } else {
            print!("{:04} ", self.lines[offset]);
        }

        let op = &self.code[offset];
        match op {
            OpCode::Return => op.simple_instruction("OP_RETURN", offset),
            OpCode::Constant(_) => self.constant_instruction("OP_CONSTANT", offset),
        }
    }

    fn constant_instruction(&self, name: &str, offset: usize) {
        if let OpCode::Constant(constant) = self.code[offset] {
            println!("{:16} {}", name, self.constants[constant]);
        }
    }
}
