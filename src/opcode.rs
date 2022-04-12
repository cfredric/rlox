use crate::{
    chunk::{ConstantIndex, OpCodeDelta},
    compiler::CompiledUpValue,
    obj::UpValueIndex,
    stack::StackSlotOffset,
};

#[derive(Clone, Debug)]
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
        distance: OpCodeDelta,
    },
    Jump {
        distance: OpCodeDelta,
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
