#![warn(missing_docs)]
//! The library for vm-1 implementing the actual virtual machine.
use std::fs::File;
use std::io::Read;

use num_enum::{IntoPrimitive, TryFromPrimitive};
use anyhow::{anyhow, Result};
use itertools::Itertools;

use crate::opcode::Opcode;

// References:
// x86 emulator
// https://github.com/jafarlihi/core86/blob/master/src/emulator.rs#L3583
// For handling flags and stuff.

/// Memory size is 5 MB
const MEM_MAX: usize = 5*1024*1024;

#[derive(TryFromPrimitive, IntoPrimitive, Eq, PartialEq, Debug, Copy, Clone)]
#[repr(u8)]
/// Represents the registers present in the machine. Used to access registers by name rather than by numeric index.
pub enum Register {
    /// General purpose register A
    A = 0x00,
    /// General purpose register B
    B = 0x01,
    /// General purpose register C
    C = 0x02,

    /// General purpose register X
    X = 0x03,
    /// General purpose register Y
    Y = 0x04,
    /// General purpose register Z
    Z = 0x05,

    /// The stack pointer.
    SP = 0x06,

    #[num_enum(catch_all)]
    /// Represents invalid registers
    Invalid(u8),
}

impl Register {
    /// Indicates whether a register is valid.
    pub fn is_valid(&self) -> bool {
        match self {
            Register::Invalid(_) => true,
            _ => false
        }
    }

    /// Returns the display name for the current register. Useful for GUI stuff.
    pub fn display_name(&self) -> Result<String> {
        match self {
            Register::Invalid(_) => {
                Err(anyhow!("Invalid Register"))
            }
            Register::A => {
                Ok("A".to_owned())
            }
            Register::B => {
                Ok("B".to_owned())
            }
            Register::C => {
                Ok("C".to_owned())
            }
            Register::X => {
                Ok("X".to_owned())
            }
            Register::Y => {
                Ok("Y".to_owned())
            }
            Register::Z => {
                Ok("Z".to_owned())
            }
            Register::SP => {
                Ok("SP".to_owned())
            }
        }
    }
}

impl From<&str> for Register {
    fn from(value: &str) -> Register {
        match value {
            "A" => Register::A,
            "B" => Register::B,
            "C" => Register::C,
            "X" => Register::X,
            "Y" => Register::Y,
            "Z" => Register::Z,
            "SP" => Register::SP,
            _ => {
                let val = value.parse::<u8>();
                if val.is_err() {
                    return Register::Invalid(0xFF);
                }
                return Register::Invalid(val.unwrap());
            }
        }
    }
}

impl Into<usize> for Register {
    fn into(self) -> usize {
        let prim: u8 = self.into();
        prim as usize
    }
}

/// Represents the current state of the VM.
///
/// All instructions with 2 operands are in the format:
/// ```asm
/// INSTRUCTION DESTINATION SOURCE
/// ```
pub struct VM {
    /// An array containing the 7 general purpose 8-bit [registers][Register].
    ///
    /// * [`A`][Register::A]
    /// * [`B`][Register::B]
    /// * [`C`][Register::C]
    /// * [`X`][Register::X]
    /// * [`Y`][Register::Y]
    /// * [`Z`][Register::Z]
    /// * [`SP`][Register::SP] The stack pointer. This register is used by the [`Opcode::Push`] and [`Opcode::Pop`]
    /// opcodes.
    ///
    /// See also: [`VM::push()`], [`VM::pop()`]
    registers: [u8; 7],
    /// The program counter as a 32-bit unsigned integer. Allows for a total of 4gb of ram.
    pc: u32,
    /// Represents the status flags in the register:
    ///
    /// |7  |6  |5  |4  |3  |2  |1  |0  |
    /// |---|---|---|---|---|---|---|---|
    /// |SF |OF |CF |ZF |NA |NA |NA |NA |
    ///
    /// * `SF` Sign Flag
    /// * `OF` Overflow Flag
    /// * `CF` Carry Flag
    /// * `ZF` Zero Flag
    flags: u8,
    /// A Boxed slice containing the system ram. Initialized to length [`MEM_MAX`].
    memory: Box<[u8]>,
    /// Indicates whether the VM has been halted by a [`VM::halt()`] instruction
    halted: bool
}

impl VM {
    /// Constructs a new VM with everything initialized to 0s.
    ///
    /// Allocates `MEM_MAX` bytes of memory.
    pub fn new() -> Self {
        Self {
            registers: [0; 7],
            pc: 0,
            flags: 0,
            memory: vec![0; MEM_MAX].into_boxed_slice(),
            halted: false,
        }
    }

    /// Loads a binary file and places it's contents in memory.
    pub fn load_file(&mut self, path: &str) -> Result<()> {
        let mut f = File::open(path).expect("Something went wrong opening the file");
        let mut in_buff = Vec::<u8>::new();
        let bytes_read = f.read_to_end(&mut in_buff).expect("Something went wrong reading the file");
        if bytes_read != (f.metadata().unwrap().len() as usize) {
            return Err(anyhow!("Failed to read entire file for some reason"));
        }
        for (index, byte) in in_buff.iter().enumerate() {
            self.memory[index] = *byte;
        }
        Ok(())
    }

    /// Runs the processor one instruction at a time.
    ///
    /// This is the heart of the interpreter. This function fetches, decodes, and executes the next instruction,
    /// setting flags and incrementing the program counter as it runs.
    ///
    /// Will return errors if any instruction fails, or if instructed to step after a halt instruction has been
    /// executed.
    pub fn step(&mut self) -> Result<()> {
        if self.halted {
            return Err(anyhow!("Attempted to step while processor is in halted state"));
        }

        let instruction = self.read8(self.pc)
            .expect("Could not read next instruction.");
        let opcode = Opcode::try_from(instruction)?;
        match opcode {
            Opcode::Noop => {}

            // ----------
            // Move Instructions
            // ----------

            // MOV DEST (8-bit) VAL (8-bit)
            Opcode::MovRegImm => {
                self.mov_reg()?;
            }
            // MOV DEST (32-bit) VAL (8-bit)
            Opcode::MovMemImm => {
                self.mov_mem_imm()?;
            }
            // MOV DEST (8-bit) SRC (32-bit)
            Opcode::MovRegMem => {
                self.mov_reg_mem()?;
            }

            // ----------
            // Math Instructions
            // ----------

            Opcode::Add => {
                self.add()?;
            }
            Opcode::Sub => {
                self.sub()?;
            }
            Opcode::Div => {
                self.div()?;
            }
            Opcode::Mul => {
                self.mul()?;
            }

            // ----------
            // Increment/Decrement
            // ----------

            Opcode::Inc => {
                self.inc()?;
            }
            Opcode::Dec => {
                self.dec()?;
            }

            // ----------
            // Stack Operations
            // ----------

            Opcode::Push => {
                self.push()?;
            }
            Opcode::Pop => {
                self.pop()?;
            }

            // ----------
            // Comparison
            // ----------

            Opcode::Test => {
                self.test()?;
            }
            Opcode::Cmp => {
                self.cmp()?;
            }

            // ----------
            // Jumps
            // ----------

            Opcode::Jmp => {
                self.jmp()?;
            }
            Opcode::Jz => {
                self.jz()?;
            }
            Opcode::Jnz => {
                self.jnz()?;
            }
            Opcode::Jl => {
                self.jl()?;
            }
            Opcode::Jg => {
                self.jg()?;
            }
            Opcode::Ja => {
                self.ja()?;
            }
            Opcode::Jb => {
                self.jb()?;
            }
            // ----------
            // Function calls
            // ----------

            Opcode::Call => {
                self.call()?;
            }
            Opcode::Ret => {
                self.ret()?;
            }
            Opcode::Halt => {
                self.halt()?;
            }
        }
        Ok(())
    }

    /// Advance the PC by some number of bytes, wrapping around if the result would overflow.
    pub fn advance_pc(&mut self, count: u32) {
        self.pc = u32::wrapping_add(self.pc, count);
    }

    /// Prints out the first `len` bytes of memory.
    pub fn dump_mem(&self, len: u32) -> String {
        self.memory.iter()
            .take(len as usize)
            .map(|&byte| format!("{:02X}", byte).to_owned())
            .collect_vec()
            .join(" ")
    }

    /// Dumps the registers in a readable format.
    ///
    /// # Example Output
    /// ```no_test
    /// A: 00, b: 00, C: 00, X: 00, Y: 00, Z: 00, SP: 00
    /// ```
    pub fn dump_registers(&self) -> Vec<(String, String)> {
        let mut result: Vec<(String, String)> = Vec::new();
        for (index, &value) in self.registers.iter().enumerate() {
            let register = Register::try_from(index as u8).unwrap();
            result.push((register.display_name().unwrap(), format!("{:02X}", value)));
        }
        result
    }

    /// Dumps the program counter and FLAGS registers in a readable format.
    ///
    /// # Example Output:
    /// ```no_test
    /// PC: FFFFFFFF, FLAGS: FF
    /// ```
    pub fn dump_pc_and_flags(&self) -> Vec<(String, String)> {
        vec![
            ("PC".to_owned() ,format!("{:08X}", self.pc)),
            ("FLAGS".to_owned(), format!("{:02X}", self.flags))
        ]
    }

    // ----------
    // Memory operations
    // ----------

    /// Reads a u8 from the given memory address.
    pub fn read8(&self, address: u32) -> Result<u8> {
        let val = self.memory.get(address as usize);
        if let Some(val) = val {
            Ok(*val)
        } else {
            Err(anyhow!("Could not read from address: 0x{:8X}", address).into())
        }
    }

    /// Reads a u16 from the given memory address.
    pub fn read16(&self, address: u32) -> Result<u16> {
        let low_byte = self.read8(address)? as u16;
        let high_byte = self.read8(address + 1)? as u16;
        Ok((high_byte << 8) | low_byte)
    }

    /// Reads a u32 from the given memory address.
    pub fn read32(&self, address: u32) -> Result<u32> {
        let lowest_byte = self.read8(address)? as u32;
        let low_byte = self.read8(address + 1)? as u32;
        let high_byte = self.read8(address + 2)? as u32;
        let highest_byte = self.read8(address + 3)? as u32;
        Ok((highest_byte << 24) | (high_byte << 16) | (low_byte << 8) | lowest_byte)
    }

    /// Writes a u8 to the given memory address.
    pub fn write8(&mut self, address: u32, val: u8) -> Result<()> {
        if (address as usize) < self.memory.len() {
            self.memory[address as usize] = val;
            Ok(())
        } else {
            Err(anyhow!("Could not write to address: 0x{:8X}", address).into())
        }
    }

    /// Writes a u16 to the given memory address.
    pub fn write16(&mut self, address: u32, val: u16) -> Result<()> {
        let low_byte = (val & 0xFF) as u8;
        let high_byte = ((val >> 8) & 0xFF) as u8;
        self.write8(address, low_byte)?;
        self.write8(address + 1, high_byte)?;
        Ok(())
    }

    /// Writes a u32 to the given memory address.
    pub fn write32(&mut self, address: u32, val: u32) -> Result<()> {
        let lowest_byte = (val & 0xFF) as u8;
        let low_byte = ((val >> 8) & 0xFF) as u8;
        let high_byte = ((val >> 16) & 0xFF) as u8;
        let highest_byte = ((val >> 24) & 0xFF) as u8;
        self.write8(address, lowest_byte)?;
        self.write8(address + 1, low_byte)?;
        self.write8(address + 2, high_byte)?;
        self.write8(address + 3, highest_byte)?;
        Ok(())
    }

    /// Sets the sign flag, or bit 7 of the `FLAGS` register.
    pub fn set_sign(&mut self, status: bool) -> Result<()> {
        self.flags &= if status {1_u8 << 7} else {0};
        Ok(())
    }

    /// Sets the overflow flag, or bit 6 of the `FLAGS` register.
    pub fn set_overflow(&mut self, status: bool) -> Result<()> {
        self.flags &= if status { 1_u8 << 6 } else { 0 };
        Ok(())
    }

    /// Sets the carry flag, or bit 5 of the `FLAGS` register.
    pub fn set_carry(&mut self, status: bool) -> Result<()> {
        self.flags &= if status { 1_u8 << 5 } else { 0 };
        Ok(())
    }

    /// Sets the zero flag, or bit 4 of the `FLAGS` register.
    pub fn set_zero(&mut self, status: bool) -> Result<()> {
        self.flags &= if status { 1_u8 << 4 } else { 0 };
        Ok(())
    }

    /// Gets the sign flag, or bit 7 of the `FLAGS` register.
    pub fn get_sign(&mut self) -> Result<bool> {
        Ok(
            if self.flags & (1_u8 << 7) != 0 {
                true
            } else {
                false
            }
        )
    }

    /// Gets the overflow flag, or bit 6 of the `FLAGS` register.
    pub fn get_overflow(&mut self) -> Result<bool> {
        Ok(
            if self.flags & (1_u8 << 6) != 0 {
                true
            } else {
                false
            }
        )
    }

    /// Gets the carry flag, or bit 5 of the `FLAGS` register.
    pub fn get_carry(&mut self) -> Result<bool> {
        Ok(
            if self.flags & (1_u8 << 5) != 0 {
                true
            } else {
                false
            }
        )
    }

    /// Gets the zero flag, or bit 4 of the `FLAGS` register.
    pub fn get_zero(&mut self) -> Result<bool> {
        Ok(
            if self.flags & (1_u8 << 4) != 0 {
                true
            } else {
                false
            }
        )
    }

    // ----------
    // Opcode Fns
    // ----------

    /// Moves a literal value into the destination register.
    ///
    /// # Assemply:
    /// ```asm
    /// MOV A #5
    /// ```
    fn mov_reg(&mut self) -> Result<()> {
        let dest_byte = self.read8(self.pc + 1)
            .expect("Could not read destination register value in MovReg instruction");
        let dest = Register::try_from(dest_byte)?;
        if let Register::Invalid(val) = dest {
            return Err(anyhow!("Invalid register id in Add instruction dest: {val:#04X?}"));
        }
        let val = self.read8(self.pc + 2)
            .expect("Could not read value while processing MovReg instruction");
        self.registers[dest_byte as usize] = val;

        self.advance_pc(3);
        Ok(())
    }

    /// Moves a literal value into the destination memory address.
    ///
    /// # Assembly:
    /// ```asm
    /// MOV $0xFFFFFFFF #5
    /// ```
    fn mov_mem_imm(&mut self) -> Result<()> {
        let dest = self.read32(self.pc + 1)
            .expect("Could not read destination memory address in MovReg in MovMemImm instruction");
        if dest >= MEM_MAX as u32 {
            return Err(anyhow!("Attempt to move to memory location above MEM_MAX in MovMemImm instruction"));
        }
        let val = self.read8(self.pc + 5)
            .expect("Could not read value while processing MovMemImm instruction");
        self.write8(dest, val)
            .expect("Could not write value while processing MovMemImm instruction");
        self.advance_pc(6);
        Ok(())
    }

    /// Moves a value from a memory address into the destination register.
    ///
    /// # Assembly:
    /// ```asm
    /// MOV A $0xFFFFFFFF
    /// ```
    fn mov_reg_mem(&mut self) -> Result<()> {
        let dest_byte = self.read8(self.pc + 1)
            .expect("Could not read destination memory address in MovMemReg instruction");
        let dest_reg = Register::try_from(dest_byte)?;
        let src = self.read32(self.pc + 2)
            .expect("Could not read source memory address in MovMemReg instruction");
        if let Register::Invalid(val) = dest_reg {
            return Err(anyhow!("Invalid register id in Add instruction dest: {val:#04X?}"));
        }
        self.registers[dest_byte as usize] = self.memory[src as usize];
        self.advance_pc(6);
        Ok(())
    }

    // ----------
    // Math
    // ----------

    /// Adds two registers together, leaving the result in the destination register.
    ///
    /// # Assembly:
    /// ```asm
    /// ADD DEST SRC
    /// ```
    fn add(&mut self) -> Result<()> {
        // load data
        let dest_byte = self.read8(self.pc + 1)
            .expect("Failed to read dest byte in Add instruction");
        let dest_reg = Register::try_from(dest_byte)?;
        let src_byte = self.read8(self.pc + 2)
            .expect("Failed to read src byte in Add instruction");
        let src_reg = Register::try_from(src_byte)?;
        // check for errors
        if let Register::Invalid(val) = dest_reg {
            return Err(anyhow!("Invalid register id in Add instruction dest: {val:#04X?}"));
        }
        if let Register::Invalid(val) = src_reg {
            return Err(anyhow!("Invalid register id in Add instruction src: {val:#04X?}"));
        }
        // calculate result and update flags
        let (result, carry) =
            u8::overflowing_add(self.registers[dest_byte as usize], self.registers[src_byte as usize]);
        let overflow = {
            let before = self.registers[dest_byte as usize];
            before > result
        };
        self.registers[dest_byte as usize] = result;
        self.set_overflow(overflow)?;
        self.set_carry(carry)?;
        self.advance_pc(3);
        Ok(())
    }

    /// Subtracts two registers, leaving the result in the destination register.
    ///
    /// # Assembly:
    /// ```asm
    /// SUB DEST SRC
    /// ```
    fn sub(&mut self) -> Result<()> {
        // load data
        let dest_byte = self.read8(self.pc + 1)
            .expect("Failed to read dest byte in Add instruction");
        let dest_reg = Register::try_from(dest_byte)?;
        let src_byte = self.read8(self.pc + 2)
            .expect("Failed to read src byte in Add instruction");
        let src_reg = Register::try_from(src_byte)?;
        // check for errors
        if let Register::Invalid(val) = dest_reg {
            return Err(anyhow!("Invalid register id in Add instruction dest: {val:#04X?}"));
        }
        if let Register::Invalid(val) = src_reg {
            return Err(anyhow!("Invalid register id in Add instruction src: {val:#04X?}"));
        }
        let (result, carry) =
            u8::overflowing_sub(self.registers[dest_byte as usize], self.registers[src_byte as usize]);
        let overflow = {
            let before = self.registers[dest_byte as usize];
            before > result
        };
        self.registers[dest_byte as usize] = result;
        self.set_overflow(overflow)?;
        self.set_carry(carry)?;
        self.advance_pc(3);
        Ok(())
    }

    /// Divides two registers, leaving the result in the destination register.
    ///
    /// Assembly:
    /// ```asm
    /// DIV DEST SRC
    /// ```
    fn div(&mut self) -> Result<()> {
        todo!("DIV not implemented")
    }

    /// Multiplies two registers, leaving the result in the destination register.
    ///
    /// Assembly:
    /// ```asm
    /// MUL DEST SRC
    /// ```
    fn mul(&mut self) -> Result<()> {
        todo!("MUL not implemented")
    }

    // ----------
    // INC/DEC
    // ----------

    /// Increments a register.
    ///
    /// Assembly:
    /// ```asm
    /// INC X
    /// ```
    fn inc(&mut self) -> Result<()> {
        todo!("INC not implemented")
    }

    /// Decrements a register.
    ///
    /// Assembly:
    /// ```asm
    /// DEC B
    /// ```
    fn dec(&mut self) -> Result<()> {
        todo!("DEC not implemented")
    }

    // ----------
    // Stack ops
    // ----------

    /// Pushes the source register's value onto the stack, incrementing [`SP`][Register::SP] in the process.
    ///
    /// Assembly:
    /// ```asm
    /// PUSH A
    /// ```
    fn push(&mut self) -> Result<()> {
        todo!("PUSH not implemented")
    }

    /// Pops a value off the stack into the destination register, decrementing [`SP`][Register::SP] in the process.
    ///
    /// Assembly:
    /// ```asm
    /// POP Z
    /// ```
    fn pop(&mut self) -> Result<()> {
        todo!("POP not implemented")
    }

    // ----------
    // Comparisons
    // ----------

    /// Performs a bitwise `and` between the two operands, discarding the result, but setting processor flags.
    ///
    /// Assembly:
    /// ```asm
    /// TEST A B
    /// ```
    ///
    /// See: <https://stackoverflow.com/questions/39556649/in-x86-whats-difference-between-test-eax-eax-and-cmp-eax-0>
    fn test(&mut self) -> Result<()> {
        todo!("TEST not implemented")
    }

    /// Subtracts the second operand from the first, discarding the result, but setting processor flags.
    ///
    /// Assembly:
    /// ```asm
    /// CMP A B
    /// ```
    ///
    /// See: <https://stackoverflow.com/questions/39556649/in-x86-whats-difference-between-test-eax-eax-and-cmp-eax-0>
    fn cmp(&mut self) -> Result<()> {
        todo!("CMP not implemented")
    }

    // ----------
    // Jump
    // ----------

    /// Performs an unconditional jump to the given memory address.
    ///
    /// Assembly:
    /// ```asm
    /// JMP #0xFFFFFFFF
    /// ```
    fn jmp(&mut self) -> Result<()> {
        todo!("JMP not implemented")
    }

    /// Jump if zero.
    ///
    /// Jumps to the provided memory address if the zero flag is `1`.
    ///
    /// Assembly:
    /// ```asm
    /// JZ #0xFFFFFFFF
    /// ```
    fn jz(&mut self) -> Result<()> {
        todo!("JZ not implemented")
    }

    /// Jump if not zero.
    ///
    /// Jumps to the provided memory address if the zero flag is `0`.
    ///
    /// Assembly:
    /// ```asm
    /// JNZ #0xFFFFFFFF
    /// ```
    fn jnz(&mut self) -> Result<()> {
        todo!("JNZ not implemented")
    }

    /// Jump if less than. (Signed)
    ///
    /// Jumps to the provided memory address if the sign flag is not equal to the overflow flag.
    ///
    /// Assembly:
    /// ```asm
    /// JZ #0xFFFFFFFF
    /// ```
    fn jl(&mut self) -> Result<()> {
        todo!("JL not implemented")
    }

    /// Jump if greater than. (Signed)
    ///
    /// Jumps to the provided memory address if the zero flag is `0` and the sign flag is equal to the overflow flag.
    ///
    /// Assembly:
    /// ```asm
    /// JZ #0xFFFFFFFF
    /// ```
    fn jg(&mut self) -> Result<()> {
        todo!("JG not implemented")
    }

    /// Jump if above. (Unsigned)
    ///
    /// Jumps to the provided memory address if the carry flag is `0` and the zero flag is `0`.
    ///
    /// Assembly:
    /// ```asm
    /// JZ #0xFFFFFFFF
    /// ```
    fn ja(&mut self) -> Result<()> {
        todo!("JA not implemented")
    }

    /// Jump if below. (Unsigned)
    ///
    /// Jumps to the provided memory address if the carry flag is `1`.
    ///
    /// Assembly:
    /// ```asm
    /// JZ #0xFFFFFFFF
    /// ```
    fn jb(&mut self) -> Result<()> {
        todo!("JB not implemented")
    }

    // ----------
    // Function
    // ----------

    /// Call subroutine.
    ///
    /// Calls the subroutine at the provided memory location.
    ///
    /// Assembly:
    /// ```asm
    /// CALL #0xFFFFFFFF
    /// ```
    fn call(&mut self) -> Result<()> {
        todo!("CALL not implemented")
    }

    /// Return from subroutine.
    ///
    /// Returns from the subroutine.
    ///
    /// Assembly:
    /// ```asm
    /// RET
    /// ```
    fn ret(&mut self) -> Result<()> {
        todo!("RET not implemented")
    }

    /// Halt the processor.
    ///
    /// Halts all execution on the processor. Calling [step][VM::step()] after this will crash.
    ///
    /// Assembly:
    /// ```asm
    /// HALT
    /// ```
    fn halt(&mut self) -> Result<()> {
        self.halted = true;
        Ok(())
    }
}
