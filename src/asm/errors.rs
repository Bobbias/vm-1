use thiserror::Error;

#[derive(Error, Debug)]
pub enum OperandError {
    #[error("Could not parse operand: `{0}`")]
    ParseError(String),
    #[error("Could not convert memory address to u8")]
    MemoryConversionError,
    #[error("Could not convert immediate to u32, perhaps you intended to convert it to u8 instead?")]
    ImmediateConversionError,
    #[error("Could not convert immediate to u32, perhaps you intended to convert it to u8 instead?")]
    RegisterConversionError,
    #[error("Another error occurred during the process: {0}")]
    Other(#[from] anyhow::Error),
}
