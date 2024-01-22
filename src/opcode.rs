//! Defines the opcodes used in VM-1
use std::fmt::{Display, Formatter};
use num_enum::{IntoPrimitive, FromPrimitive};
use anyhow::{anyhow, Error};

#[derive(FromPrimitive, IntoPrimitive, Default, PartialEq, Eq, Copy, Clone, Debug)]
#[repr(u8)]
/// Represents an opcode in vm-1
pub enum Opcode {
    // General
    /// No operation: NOP
    #[default]
    Noop = 0xFF,
    /// Move immediate to register: MOV DEST VAL (8-bit)
    MovRegImm = 0x00,
    /// Move immediate value to memory address: MOVMEM DEST (32-bit) VAL (8-bit)
    MovMemImm = 0x01,
    /// Move register contents to memory address: MOVMEM DEST SRC (8-bit)
    MovRegMem = 0x02,


    // Math
    /// Add two registers together: ADD DEST SRC (8-bit)
    Add  = 0x03,
    /// Subtract two registers: SUB DEST SRC (8-bit)
    Sub  = 0x04,
    /// Divide two registers: DIV DEST SRC (8-bit)
    Div  = 0x05,
    /// Multiply two registers: MUL DEST SRC (8-bit)
    Mul  = 0x06,

    // Increment/Decrement
    /// Increment a register: INC DEST (8-bit)
    Inc  = 0x07,
    /// Decrement a register: DEC DEST (8-bit)
    Dec  = 0x08,

    // Stack Operations
    /// Push a register onto the stack: PUSH DEST (8-bit)
    Push = 0x09,
    /// Pop the top of the stack into a register: POP DEST (8-bit)
    Pop  = 0x0A,

    // Comparison
    /// Perform logical and on two registers, ignoring the result and set flags: TEST DEST SRC (8-bit)
    Test = 0x0B,
    /// Perform a subtraction between two registers, ignoring the result and set flags: CMP DEST SRC (8-bit)
    Cmp = 0x0C,

    // Jumps
    /// Unconditional jump to a destination: JMP DEST (32-bit)
    Jmp  = 0x0d,
    /// Jump if Zero flag set (Equivalent to jump if equal): JZ DEST (32-bit)
    Jz   = 0x0E,
    /// Jump if not Zero flag set (Equivalent to jump if not equal): JNZ DEST (32-bit)
    Jnz  = 0x0F,
    // Signed
    /// Jump if less than (sign flag != overflow flag): JL DEST (32-bit)
    Jl = 0x10,
    /// Jump if greater than (Zero flag == 0, sign flag == overflow flag): JG DEST (32-bit)
    Jg = 0x11,
    // Unsigned
    /// Jump if above (carry flag == 1): JA DEST (32-bit)
    Ja = 0x12,
    /// Jump if below (carry flag == 0, zero flag == 0): : JB DEST (32-bit)
    Jb = 0x13,

    // Function calls
    /// Call function at a given destination: CALL DEST (32-bit)
    Call = 0x14,
    /// Return from function call: RET
    Ret  = 0x15,
    /// Halt execution: HALT
    Halt = 0x16,
}

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Opcode::Noop => "NOP",
            Opcode::MovRegImm => "MOV",
            Opcode::MovMemImm => "MOV",
            Opcode::MovRegMem => "MOV",
            Opcode::Add => "ADD",
            Opcode::Sub => "SUB",
            Opcode::Div => "DIV",
            Opcode::Mul => "MUL",
            Opcode::Inc => "INC",
            Opcode::Dec => "DEC",
            Opcode::Push => "PUSH",
            Opcode::Pop => "POP",
            Opcode::Test => "TEST",
            Opcode::Cmp => "CMP",
            Opcode::Jmp => "JMP",
            Opcode::Jz => "JZ",
            Opcode::Jnz => "JNZ",
            Opcode::Jl => "JL",
            Opcode::Jg => "JG",
            Opcode::Ja => "JA",
            Opcode::Jb => "JB",
            Opcode::Call => "CALL",
            Opcode::Ret => "RET",
            Opcode::Halt => "HALT",
        };
        write!(f, "{str}")
    }
}

impl TryFrom<&str> for Opcode {
    type Error = Error;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "NOP" => Ok(Opcode::Noop),
            "MOV" => {
                Err(anyhow!("Todo: Figure out how to correctly implement identifying the correct MOV instruction"))
            }
            "ADD" => Ok(Opcode::Add),
            "SUB" => Ok(Opcode::Sub),
            "DIV" => Ok(Opcode::Div),
            "MUL" => Ok(Opcode::Mul),
            "INC" => Ok(Opcode::Inc),
            "DEC" => Ok(Opcode::Dec),
            "PUSH" => Ok(Opcode::Push),
            "POP" => Ok(Opcode::Pop),
            "TEST" => Ok(Opcode::Test),
            "CMP" => Ok(Opcode::Cmp),
            "JMP" => Ok(Opcode::Jmp),
            "JZ" => Ok(Opcode::Jz),
            "JNZ" => Ok(Opcode::Jnz),
            "JL" => Ok(Opcode::Jl),
            "JG" => Ok(Opcode::Jg),
            "JA" => Ok(Opcode::Ja),
            "JB" => Ok(Opcode::Jb),
            "CALL" => Ok(Opcode::Call),
            "RET" => Ok(Opcode::Ret),
            "HALT" => Ok(Opcode::Halt),
            _ => Err(anyhow!("Could not convert from string to Opcode"))
        }
    }
}

