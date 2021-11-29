mod chunk;
mod common;
mod value;
mod vm;

use value::Value;

fn main() {
    let mut chunk = chunk::Chunk::new();

    let constant = chunk.add_constant(Value::Double(1.2));
    chunk.write_chunk(chunk::OpCode::Constant(constant), 123);

    let constant = chunk.add_constant(Value::Double(3.4));
    chunk.write_chunk(chunk::OpCode::Constant(constant), 123);

    chunk.write_chunk(chunk::OpCode::Add, 123);

    let constant = chunk.add_constant(Value::Double(5.6));
    chunk.write_chunk(chunk::OpCode::Constant(constant), 123);

    chunk.write_chunk(chunk::OpCode::Divide, 123);

    chunk.write_chunk(chunk::OpCode::Negate, 123);
    chunk.write_chunk(chunk::OpCode::Return, 123);
    chunk.disassemble_chunk("test chunk");

    vm::interpret(&chunk);
}
