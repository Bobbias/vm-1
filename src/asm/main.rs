//! This is the assembler for vm-1.
pub mod instruction;
pub mod operand;
pub mod errors;

use std::fs;
use std::fs::read_to_string;
use std::io::Write;
use std::path::PathBuf;
use anyhow::{anyhow, Result};
use itertools::Itertools;
use clap::Parser;

use libvm::opcode::Opcode;
use instruction::Instruction;
use operand::Operand;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long)]
    input: String,
    #[arg(short, long)]
    output: String
}

/// The main function which loads an assembly file into memory, and then writes out a binary file which can be
/// executed by the VM.
fn main() -> Result<()> {
    // Parse command line arguments.
    let args = Args::parse();

    let in_path: std::io::Result<PathBuf> = fs::canonicalize(args.input.clone())
        .or_else(|_| panic!("Could not canonicalize {:?}", args.input));
    let out_path = PathBuf::from(args.output.clone());
    // Note: Cannot use canonicalize on a file that may not exist.

    // Process files
    let text = read_to_string(in_path.unwrap()).expect("Couldn't read file");

    let output = text.lines()
        .filter(|&line| !line.is_empty())
        .map(|line| {
            parse_line(line)
        })
        .filter_map(|instruction| {
            if let Ok(instruction) = instruction {
                return Some(instruction.to_bytecode());
            };
            None
        })
        .flatten()
        .collect_vec();

    let mut out_file = fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(out_path)
        .expect("Could not open output file");

    out_file.write_all(&output).expect("Could not write to output file");

    Ok(())
}

fn parse_line(input: &str) -> Result<Instruction> {
    let mut result = Instruction::default();
    // todo: there's gotta be a better solution than this garbage.
    let mut first: &str = "";
    let mut rest: &str = "";
    if !input.contains(" ") {
        first = input;
    } else {
        (first, rest) = input.split_once(" ")
            .expect("Failed to split input in parse_line");
    }
    match first {
        "MOV" => {
            let (first, second) = rest.split_once(" ")
                .expect("Failed to split line in parse_line");
            if second.is_empty() {
                return Err(anyhow!("Missing second operand for MOV"));
            }

            let operand1 = Operand::try_from(first)?;
            match operand1 {
                Operand::Register(_) => {
                    result.operands.push(operand1);
                }
                Operand::Memory(_) => {
                    result.operands.push(operand1);
                }
                Operand::Immediate(_) => {
                    return Err(anyhow!("Cannot use immediate value as a destination in MOV"));
                }
            }
            let operand2 = Operand::try_from(second)?;
            match operand2 {
                Operand::Register(_) => {
                    return Err(anyhow!("Cannot use register value as a source in MOV"));
                }
                Operand::Memory(_) => {
                    match operand1 {
                        Operand::Register(_) => {
                            result.operands.push(operand2);
                            result.opcode = Opcode::MovRegMem;
                        }
                        _ => {
                            return Err(anyhow!("Invalid operand combination for MOV instruction: "));
                        }
                    }
                }
                Operand::Immediate(_) => {
                    match operand1 {
                        Operand::Register(_) => {
                            result.operands.push(operand2);
                            result.opcode = Opcode::MovRegImm;
                        }
                        Operand::Memory(_) => {
                            result.operands.push(operand2);
                            result.opcode = Opcode::MovMemImm;
                        }
                        _ => {
                            unreachable!("We already ensured that operand1 cannot be Operand::Immediate.")
                        }
                    }
                }
            }
        }
        "ADD" => {
            result.opcode = Opcode::Add;
            let (first, second) = rest.split_once(" ")
                .expect("Failed to split line in parse_line ADD section");
            if second.is_empty() {
                return Err(anyhow!("Missing second operand for AND"));
            }

            let operand = Operand::try_from(first)?;
            match operand {
                Operand::Register(_) => {
                    result.operands.push(operand);
                }
                _ => {
                    return Err(anyhow!("Invalid operand for AND: `{:?}`", operand));
                }
            }
            let operand = Operand::try_from(second)?;
            match operand {
                Operand::Register(_) => {
                    result.operands.push(operand);
                }
                _ => {
                    return Err(anyhow!("Invalid operand for AND: `{:?}`", operand));
                }
            }
        },
        "SUB" => {
            result.opcode = Opcode::Sub;
        },
        "DIV" => {
            result.opcode = Opcode::Div;
        },
        "MUL" => {
            result.opcode = Opcode::Mul;
        },
        "INC" => {
            result.opcode = Opcode::Inc;
        },
        "DEC" => {
            result.opcode = Opcode::Dec;
        },
        "PUSH" => {
            result.opcode = Opcode::Push;
            let operand = Operand::try_from(rest)?;
            match operand {
                Operand::Register(_) => {
                    result.operands.push(operand);
                }
                _ => {
                    return Err(anyhow!("Invalid operand for PUSH: `{:?}`", operand));
                }
            }
        },
        "POP" => {
            result.opcode = Opcode::Pop;
            let operand = Operand::try_from(rest)?;
            match operand {
                Operand::Register(_) => {
                    result.operands.push(operand);
                }
                _ => {
                    return Err(anyhow!("Invalid operand for POP: `{:?}`", operand));
                }
            }
        },
        "TEST" => {
            result.opcode = Opcode::Test;
            todo!("Implement TEST");
        },
        "CMP" => {
            result.opcode = Opcode::Cmp;
            todo!("Implement CMP");
        },
        "JMP" => {
            result.opcode = Opcode::Jmp;
            todo!("Implement JMP");
        },
        "JZ" => {
            result.opcode = Opcode::Jz;
            todo!("Implement JZ");
        },
        "JNZ" => {
            result.opcode = Opcode::Jnz;
            todo!("Implement JNZ");
        },
        "JL" => {
            result.opcode = Opcode::Jl;
            todo!("Implement JL");
        },
        "JG" => {
            result.opcode = Opcode::Jg;
            todo!("Implement JG");
        },
        "JA" => {
            result.opcode = Opcode::Ja;
            todo!("Implement JA");
        },
        "JB" => {
            result.opcode = Opcode::Jb;
            todo!("Implement JB");
        },
        "CALL" => {
            result.opcode = Opcode::Call;
            todo!("Implement CALL");
        },
        "RET" => {
            result.opcode = Opcode::Ret;
            todo!("Implement RET");
        },
        "HALT" => {
            result.opcode = Opcode::Halt;
        },
        _ => {}
    }
    Ok(result)
}
