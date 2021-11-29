mod chunk;
mod common;
mod value;

use value::Value;

fn main() {
    let mut chunk = chunk::Chunk::new();

    let constant = chunk.add_constant(Value::Double(1.2));
    chunk.write_chunk(chunk::OpCode::Constant(constant), 123);
    chunk.write_chunk(chunk::OpCode::Return, 123);
    chunk.disassemble_chunk("test chunk");
}
