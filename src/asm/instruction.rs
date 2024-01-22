use libvm::opcode::Opcode;
use super::operand::Operand;

#[derive(Debug)]
/// Represents a machine code instruction.
///
/// Contains the [opcode][Opcode] and [operands][Operand]
pub struct Instruction {
    pub opcode: Opcode,
    pub operands: Vec<Operand>
}

impl Default for Instruction {
    fn default() -> Self {
        Self {
            opcode: Opcode::Noop,
            operands: Vec::new(),
        }
    }
}

impl Instruction {
    /// Converts an instruction to it's bytecode representation.
    pub fn to_bytecode(&self) -> Vec<u8> {
        let mut result: Vec<u8> = Vec::new();
        result.push(self.opcode.into());
        for operand in self.operands.iter() {
            let single_byte = TryInto::<u8>::try_into(*operand);
            if single_byte.is_ok() {
                result.push(single_byte.unwrap())
            } else {
                let multi_byte = TryInto::<u32>::try_into(*operand);
                if multi_byte.is_ok() {
                    for byte in multi_byte.unwrap().to_le_bytes() {
                        result.push(byte);
                    }
                }
            }
        }
        result
    }
}
