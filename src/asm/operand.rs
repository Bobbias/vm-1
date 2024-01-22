use anyhow::anyhow;
use libvm::vm::Register;
use super::errors::OperandError;

#[derive(Debug, Copy, Clone)]
/// Encodes an operand for an [`super::instruction::Instruction`]
pub enum Operand {
    Memory(u32),
    Register(Register),
    Immediate(u8),
}

impl TryFrom<&str> for Operand {
    type Error = OperandError;

    /// Converts a string slice to an [`Operand`].
    ///
    /// # Errors
    ///
    /// If this function fails to parse the operand, it will generate an [`OperandError`].
    fn try_from(value: &str) -> std::result::Result<Self, Self::Error> {
        match value {
            "A" => Ok(Operand::Register(Register::from(value))),
            "B" => Ok(Operand::Register(Register::from(value))),
            "C" => Ok(Operand::Register(Register::from(value))),
            "X" => Ok(Operand::Register(Register::from(value))),
            "Y" => Ok(Operand::Register(Register::from(value))),
            "Z" => Ok(Operand::Register(Register::from(value))),
            "SP" => Ok(Operand::Register(Register::from(value))),
            _ => {
                if value.starts_with("#") {
                    let val_str = value.strip_prefix("#").unwrap();
                    let val = val_str.parse::<u8>();
                    if val.is_err() {
                        // fixme: Do proper checking for 0x perfix
                        let val_str = val_str.strip_prefix("0x").unwrap();
                        let from_hex = u8::from_str_radix(val_str, 16);
                        if from_hex.is_err() {
                            return Err(OperandError::from(anyhow!("Could not parse hex value")));
                        }
                        return Ok(Operand::Immediate(from_hex.unwrap()));
                    }
                    Ok(Operand::Immediate(val.unwrap()))
                } else if value.starts_with("$") {
                    let val_str = value.strip_prefix("$").unwrap();
                    let val = val_str.parse::<u32>();
                    if val.is_err() {
                        // fixme: Do proper checking for 0x perfix
                        let val_str = val_str.strip_prefix("0x").unwrap();
                        let from_hex = u32::from_str_radix(val_str, 16);
                        if from_hex.is_err() {
                            return Err(OperandError::from(anyhow!("Could not parse hex value")));
                        }
                        return Ok(Operand::Memory(from_hex.unwrap()));
                    }
                    Ok(Operand::Memory(val.unwrap()))
                } else {
                    Err(OperandError::ParseError(value.to_string()))
                }
            }
        }
    }
}

impl TryInto<u8> for Operand {
    type Error = OperandError;

    /// Converts an [`Operand`] to a [`u8`].
    ///
    /// # Errors
    ///
    /// If this function fails to convert the operand, it will generate an [`OperandError`]. The only failure mode it
    /// has currently is if the operand is [`Operand::Memory`], which fails because a memory address must be [`u32`],
    /// not [`u8`].
    fn try_into(self) -> std::result::Result<u8, Self::Error> {
        match self {
            Operand::Immediate(val) => Ok(val),
            Operand::Register(val) => Ok(val.into()),
            Operand::Memory(_) => Err(OperandError::MemoryConversionError)
        }
    }
}

impl TryInto<u32> for Operand {
    type Error = OperandError;

    /// Converts an [`Operand`] to a [`u32`].
    ///
    /// # Errors
    ///
    /// If this function fails to convert the operand, it will generate an [`OperandError`]. If the operand is either
    /// [`Operand::Immediate`] or [`Operand::Register`], it will return an [`OperandError::ImmediateConversionError`]
    /// or an [`OperandError::RegisterConversionError`] respectively.
    fn try_into(self) -> std::result::Result<u32, Self::Error> {
        match self {
            Operand::Immediate(val) =>
                Err(OperandError::ImmediateConversionError),
            Operand::Register(val) =>
                Err(OperandError::RegisterConversionError),
            Operand::Memory(val) => Ok(val)
        }
    }
}
