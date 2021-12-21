use crate::compiler::Upvalue;
use crate::obj::Obj;
use crate::value::Value;

#[derive(Clone, Debug)]
pub enum OpCode {
    /// Operand is the index into the constants table.
    Constant(usize),
    Nil,
    /// Operand is the boolean value itself.
    Bool(bool),
    /// Operand is the index into the constants table.
    GetGlobal(usize),
    /// Operand is the index into the constants table.
    DefineGlobal(usize),
    /// Operand is the index into the constants table.
    SetGlobal(usize),
    /// Operand is the stack frame's slot. Starts counting from the start of the
    /// frame.
    GetLocal(usize),
    /// Operand is the stack frame's slot. Starts counting from the start of the
    /// frame.
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
    /// Operand is the distance to jump.
    JumpIfFalse(usize),
    /// Operand is the distance to jump.
    Jump(usize),
    /// Operand is the distance to jump backwards.
    Loop(usize),
    /// Operand is the number of arguments passed to the callee.
    Call(usize),
    /// First operand is the index into the constants table for the function;
    /// second operand is the list of upvalue metadata used by the closure.
    Closure(usize, Vec<Upvalue>),
    CloseUpvalue,
    /// Operand is the index into the closure's upvalue array.
    GetUpvalue(usize),
    /// Operand is the index into the closure's upvalue array.
    SetUpvalue(usize),
    Return,
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

        match &self.code[offset] {
            OpCode::Return => Self::simple_instruction("OP_RETURN"),
            OpCode::Constant(i) => self.constant_instruction("OP_CONSTANT", heap, *i),
            OpCode::Negate => Self::simple_instruction("OP_NEGATE"),
            OpCode::Add => Self::simple_instruction("OP_ADD"),
            OpCode::Subtract => Self::simple_instruction("OP_SUBTRACT"),
            OpCode::Multiply => Self::simple_instruction("OP_MULTIPLY"),
            OpCode::Divide => Self::simple_instruction("OP_DIVIDE"),
            OpCode::Nil => Self::simple_instruction("OP_NIL"),
            OpCode::Bool(b) => Self::simple_instruction(if *b { "OP_TRUE" } else { "OP_FALSE" }),
            OpCode::Not => Self::simple_instruction("OP_NOT"),
            OpCode::Equal => Self::simple_instruction("OP_EQUAL"),
            OpCode::Greater => Self::simple_instruction("OP_GREATER"),
            OpCode::Less => Self::simple_instruction("OP_LESS"),
            OpCode::Print => Self::simple_instruction("OP_PRINT"),
            OpCode::Pop => Self::simple_instruction("OP_POP"),
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
            OpCode::Call(arity) => self.byte_instruction("OP_CALL", *arity),
            OpCode::Closure(constant, upvalues) => {
                print!("{:16} {} ", "OP_CLOSURE", constant);
                print!("{}", self.constants[*constant].print(heap));
                println!();

                println!(
                    "{}",
                    upvalues
                        .iter()
                        .map(|upvalue| format!(
                            "        |   {} {}",
                            if upvalue.is_local { "local" } else { "upvalue" },
                            upvalue.index
                        ))
                        .collect::<String>()
                );
            }
            OpCode::GetUpvalue(index) => self.byte_instruction("OP_GET_UPVALUE", *index),
            OpCode::SetUpvalue(index) => self.byte_instruction("OP_SET_UPVALUE", *index),
            OpCode::CloseUpvalue => Self::simple_instruction("OP_CLOSE_UPVALUE"),
        }
    }

    fn simple_instruction(name: &str) {
        println!("{}", name);
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
