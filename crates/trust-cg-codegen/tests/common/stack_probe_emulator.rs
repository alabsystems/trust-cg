// Copyright 2026 Andrew Yates | Apache-2.0
//! Stack-touch emulator for AArch64 stack-probe decode checks.
//!
//! Executes encoded function bytes, decoded by the independent leaf decoder in
//! `trust-cg-lift`, over the integer subset frame lowering emits for
//! prologues, probe loops, runtime allocations and epilogues. Any other word
//! fails closed. Every store is a stack touch; every SP decrement is checked
//! against the lowest address touched so far. The caller is modeled at its
//! worst case: `STACK_PROBE_MAX_UNPROBED` bytes above the entry SP untouched.
//!
//! This is executable evidence for the exercised inputs, not a proof over all
//! frame sizes, and it does not model other threads, signals or the kernel.

#![allow(dead_code)]

use std::collections::HashMap;

use trust_cg_lift::disasm::aarch64::{Instruction, LoadStorePairAddressMode, decode};

/// Bytes between probes (frame::STACK_PROBE_INTERVAL, restated independently).
pub const INTERVAL: u64 = 4096;
/// Untouched bytes a caller may leave above SP at a call.
pub const MAX_UNPROBED: u64 = 1024;

pub const ENTRY_SP: u64 = 0x0000_7000_0000_0000;
pub const ENTRY_FP: u64 = 0x0000_7000_0000_1230;
pub const RETURN_ADDRESS: u64 = 0x0000_1234_5678_9abc;
const STEP_LIMIT: usize = 2_000_000;

/// Observations of one call, from entry to its RET.
#[derive(Debug, Default)]
pub struct Run {
    /// X0 at RET.
    pub result: u64,
    /// Addresses of every `str xzr, [sp]`, in execution order.
    pub probes: Vec<u64>,
    /// Lowest SP reached.
    pub min_sp: u64,
    /// Lowest address stored to.
    pub lowest_touch: u64,
    /// Largest distance an SP decrement moved below the lowest touch.
    pub max_untouched_decrement: u64,
    /// Number of SP decrements.
    pub decrements: usize,
    /// SP decrements whose new SP sat more than `INTERVAL` below every touch.
    pub violations: Vec<String>,
    /// SP decrements executed while X29 did not hold `entry SP - 16`, the
    /// FP-based CFA rule (`CFA = x29 + 16`) that frame CFI relies on, after
    /// the frame record was saved.
    pub cfa_violations: Vec<String>,
    /// Instructions executed.
    pub steps: usize,
    /// X0-X30 at RET.
    pub registers: [u64; 31],
    /// How the run ended (always `Ret` under [`run`]).
    pub exit: Exit,
}

/// How a run left the function.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum Exit {
    /// `RET` to the caller.
    #[default]
    Ret,
    /// An unresolved direct branch (`B .`, the single-function encoding of a
    /// symbol tail call): left with SP, X29 and X30 restored.
    TailCall,
    /// `BRK #imm16`.
    Trap(u16),
}

/// Exits [`run_with_exits`] accepts besides `RET`. Off in [`run`], so the
/// stack-probe tests keep failing on any other way out.
#[derive(Debug, Default, Clone, Copy)]
pub struct Exits {
    /// Stop at `B .` and check the restored frame as at `RET`.
    pub tail_call: bool,
    /// Stop at `BRK`, with no frame check.
    pub trap: bool,
}

struct Machine<'a> {
    text: &'a [u8],
    x: [u64; 31],
    sp: u64,
    n: bool,
    z: bool,
    c: bool,
    v: bool,
    mem: HashMap<u64, u8>,
    frame_record_saved: bool,
    exits: Exits,
    run: Run,
}

fn sext(value: u64, bits: u32) -> i64 {
    let shift = 64 - bits;
    ((value << shift) as i64) >> shift
}

fn mask(bits: u32) -> u64 {
    if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

fn add_with_carry(x: u64, y: u64, carry: bool, bits: u32) -> (u64, bool, bool, bool, bool) {
    let m = mask(bits);
    let (x, y) = (x & m, y & m);
    let unsigned = u128::from(x) + u128::from(y) + u128::from(carry);
    let result = (unsigned as u64) & m;
    let signed = i128::from(sext(x, bits)) + i128::from(sext(y, bits)) + i128::from(carry);
    let n = (result >> (bits - 1)) & 1 == 1;
    let z = result == 0;
    let c = unsigned > u128::from(m);
    let v = i128::from(sext(result, bits)) != signed;
    (result, n, z, c, v)
}

impl Machine<'_> {
    fn read(&self, r: u8) -> u64 {
        if r == 31 { 0 } else { self.x[r as usize] }
    }
    fn write(&mut self, r: u8, value: u64) {
        if r != 31 {
            self.x[r as usize] = value;
        }
    }
    fn read_sp(&self, r: u8) -> u64 {
        if r == 31 { self.sp } else { self.x[r as usize] }
    }
    fn write_sp(&mut self, r: u8, value: u64, pc: usize) {
        if r != 31 {
            self.x[r as usize] = value;
            return;
        }
        if value < self.sp {
            self.run.decrements += 1;
            let below = self.run.lowest_touch.saturating_sub(value);
            self.run.max_untouched_decrement = self.run.max_untouched_decrement.max(below);
            if below > INTERVAL {
                self.run.violations.push(format!(
                    "pc {pc:#x}: SP {value:#x} is {below} bytes below the lowest touch {:#x}",
                    self.run.lowest_touch
                ));
            }
            if self.frame_record_saved && self.x[29] != ENTRY_SP - 16 {
                self.run.cfa_violations.push(format!(
                    "pc {pc:#x}: SP decrement with x29 {:#x} != CFA - 16",
                    self.x[29]
                ));
            }
        }
        self.sp = value;
        self.run.min_sp = self.run.min_sp.min(value);
    }
    fn store(&mut self, address: u64, bytes: u32, value: u64) {
        for k in 0..u64::from(bytes) {
            self.mem.insert(address + k, (value >> (8 * k)) as u8);
        }
        self.run.lowest_touch = self.run.lowest_touch.min(address);
        if address == ENTRY_SP - 16 {
            self.frame_record_saved = true;
        }
    }
    fn load(&self, address: u64, bytes: u32) -> u64 {
        (0..u64::from(bytes)).fold(0, |value, k| {
            value | u64::from(self.mem.get(&(address + k)).copied().unwrap_or(0)) << (8 * k)
        })
    }
    /// Zero-extending scalar load (opc 01) or store (opc 00).
    fn scalar_access(
        &mut self,
        opc: u8,
        rt: u8,
        address: u64,
        bytes: u32,
        pc: usize,
    ) -> Result<(), String> {
        match opc {
            0b00 => {
                let value = self.read(rt) & mask(8 * bytes);
                self.store(address, bytes, value);
            }
            0b01 => {
                let value = self.load(address, bytes);
                self.write(rt, value);
            }
            other => return Err(format!("pc {pc:#x}: scalar load/store opc {other:#b}")),
        }
        Ok(())
    }

    fn condition(&self, cond: u8) -> bool {
        let result = match cond >> 1 {
            0 => self.z,
            1 => self.c,
            2 => self.n,
            3 => self.v,
            4 => self.c && !self.z,
            5 => self.n == self.v,
            6 => self.n == self.v && !self.z,
            _ => true,
        };
        if cond & 1 == 1 && cond != 0b1111 {
            !result
        } else {
            result
        }
    }

    fn step(&mut self, pc: usize) -> Result<Option<usize>, String> {
        let word = self
            .text
            .get(pc..pc + 4)
            .map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
            .ok_or_else(|| format!("pc {pc:#x} ran off the {}-byte text", self.text.len()))?;
        let next = pc + 4;
        // SUBS Xd, SP|Xn, Xm, UXTX #0 (add/subtract extended register,
        // 64-bit, op=1, S=1, option=011, imm3=000), decoded here from the Arm
        // ARM fields because the leaf decoder does not name this class. Rn 31
        // is SP and Rd 31 is XZR; Rm 31 is XZR.
        if word & 0xFFE0_FC00 == 0xEB20_6000 {
            let (rm, rn, rd) = (
                ((word >> 16) & 31) as u8,
                ((word >> 5) & 31) as u8,
                (word & 31) as u8,
            );
            let (result, n, z, c, v) = add_with_carry(self.read_sp(rn), !self.read(rm), true, 64);
            (self.n, self.z, self.c, self.v) = (n, z, c, v);
            self.write(rd, result);
            return Ok(Some(next));
        }
        // BRK #imm16, decoded from the Arm ARM fields (the leaf decoder
        // names only some immediates).
        if self.exits.trap && word & 0xFFE0_001F == 0xD420_0000 {
            self.run.exit = Exit::Trap(((word >> 5) & 0xFFFF) as u16);
            return Ok(None);
        }
        let inst =
            decode(word).map_err(|e| format!("pc {pc:#x}: undecodable {word:#010x}: {e:?}"))?;
        match inst {
            Instruction::Nop => {}
            Instruction::MoveWide(m) => {
                let shift = u32::from(m.hw) * 16;
                let imm = u64::from(m.imm16) << shift;
                let bits = if m.sf == 1 { 64 } else { 32 };
                let value = match m.opc {
                    0b00 => !imm,
                    0b10 => imm,
                    0b11 => (self.read(m.rd) & !(0xffff << shift)) | imm,
                    other => return Err(format!("pc {pc:#x}: move-wide opc {other:#b}")),
                };
                self.write(m.rd, value & mask(bits));
            }
            Instruction::AddSubImm(a) => {
                let bits = if a.sf == 1 { 64 } else { 32 };
                let imm = u64::from(a.imm12) << if a.shift12 { 12 } else { 0 };
                let lhs = self.read_sp(a.rn) & mask(bits);
                let (y, carry) = if a.op == 1 {
                    (!imm, true)
                } else {
                    (imm, false)
                };
                let (result, n, z, c, v) = add_with_carry(lhs, y, carry, bits);
                if a.set_flags {
                    (self.n, self.z, self.c, self.v) = (n, z, c, v);
                    self.write(a.rd, result);
                } else {
                    self.write_sp(a.rd, result, pc);
                }
            }
            Instruction::AddSubShiftedReg(a) => {
                let bits = if a.sf == 1 { 64 } else { 32 };
                if a.shift != 0 {
                    return Err(format!(
                        "pc {pc:#x}: shifted add/sub shift type {}",
                        a.shift
                    ));
                }
                let rhs = (self.read(a.rm) << a.imm6) & mask(bits);
                let lhs = self.read(a.rn) & mask(bits);
                let (y, carry) = if a.op == 1 {
                    (!rhs, true)
                } else {
                    (rhs, false)
                };
                let (result, n, z, c, v) = add_with_carry(lhs, y, carry, bits);
                if a.set_flags {
                    (self.n, self.z, self.c, self.v) = (n, z, c, v);
                }
                self.write(a.rd, result);
            }
            Instruction::LogicalShiftedReg(l) if l.opc == 0b01 && !l.n && l.shift == 0 => {
                let bits = if l.sf == 1 { 64 } else { 32 };
                let value = (self.read(l.rn) | (self.read(l.rm) << l.imm6)) & mask(bits);
                self.write(l.rd, value);
            }
            Instruction::BitfieldMove(b) if b.opc == 0b10 => {
                let bits = if b.sf == 1 { 64 } else { 32 };
                let (immr, imms) = (u32::from(b.immr), u32::from(b.imms));
                let source = self.read(b.rn) & mask(bits);
                let value = if imms >= immr {
                    (source >> immr) & mask(imms - immr + 1)
                } else {
                    ((source & mask(imms + 1)) << (bits - immr)) & mask(bits)
                };
                self.write(b.rd, value);
            }
            Instruction::ConditionalSelect(s) if !s.op && !s.o2 => {
                let bits = if s.sf == 1 { 64 } else { 32 };
                let value = if self.condition(s.cond) {
                    self.read(s.rn)
                } else {
                    self.read(s.rm)
                };
                self.write(s.rd, value & mask(bits));
            }
            Instruction::LoadStorePair(p) if !p.vector && p.opc == 0b10 => {
                let base = self.read_sp(p.rn);
                let offset = sext(u64::from(p.imm7), 7) * 8;
                let (address, writeback) = match p.mode {
                    LoadStorePairAddressMode::SignedOffset => {
                        (base.wrapping_add_signed(offset), None)
                    }
                    LoadStorePairAddressMode::PreIndex => {
                        let a = base.wrapping_add_signed(offset);
                        (a, Some(a))
                    }
                    LoadStorePairAddressMode::PostIndex => {
                        (base, Some(base.wrapping_add_signed(offset)))
                    }
                };
                // A pre-index store's writeback and access are one instruction:
                // check the new SP, then record the touch at it.
                let pre_index = matches!(p.mode, LoadStorePairAddressMode::PreIndex);
                if pre_index && let Some(value) = writeback {
                    self.write_sp(p.rn, value, pc);
                }
                if p.load {
                    let (first, second) = (self.load(address, 8), self.load(address + 8, 8));
                    self.write(p.rt, first);
                    self.write(p.rt2, second);
                } else {
                    let (first, second) = (self.read(p.rt), self.read(p.rt2));
                    self.store(address, 8, first);
                    self.store(address + 8, 8, second);
                }
                if !pre_index && let Some(value) = writeback {
                    self.write_sp(p.rn, value, pc);
                }
            }
            Instruction::LoadStoreUnsignedImm(ls) if !ls.vector => {
                let bytes = 1u32 << ls.size;
                let address = self.read_sp(ls.rn) + u64::from(ls.imm12) * u64::from(bytes);
                if ls.opc == 0b00 && ls.size == 3 && ls.rt == 31 && ls.rn == 31 && ls.imm12 == 0 {
                    self.run.probes.push(address);
                }
                self.scalar_access(ls.opc, ls.rt, address, bytes, pc)?;
            }
            Instruction::LoadStoreUnscaled(ls) if !ls.vector => {
                let bytes = 1u32 << ls.size;
                let address = self.read_sp(ls.rn).wrapping_add_signed(i64::from(ls.imm9));
                self.scalar_access(ls.opc, ls.rt, address, bytes, pc)?;
            }
            Instruction::CompareBranch(b) => {
                let bits = if b.sf == 1 { 64 } else { 32 };
                let zero = self.read(b.rt) & mask(bits) == 0;
                if zero != b.nonzero {
                    let offset = sext(u64::from(b.imm19), 19) * 4;
                    return Ok(Some(pc.wrapping_add_signed(offset as isize)));
                }
            }
            Instruction::CondBranch(b) => {
                if self.condition(b.cond) {
                    let offset = sext(u64::from(b.imm19), 19) * 4;
                    return Ok(Some(pc.wrapping_add_signed(offset as isize)));
                }
            }
            Instruction::UncondBranch(b) if !b.link && b.imm26 == 0 && self.exits.tail_call => {
                self.run.exit = Exit::TailCall;
                return Ok(None);
            }
            Instruction::UncondBranch(b) if !b.link => {
                let offset = sext(u64::from(b.imm26), 26) * 4;
                return Ok(Some(pc.wrapping_add_signed(offset as isize)));
            }
            Instruction::BranchReg(b) if b.opc == 0b0010 => {
                if self.read(b.rn) != RETURN_ADDRESS {
                    return Err(format!("pc {pc:#x}: RET to {:#x}", self.read(b.rn)));
                }
                return Ok(None);
            }
            other => return Err(format!("pc {pc:#x}: unmodeled {other:?}")),
        }
        Ok(Some(next))
    }
}

/// Run the function at byte 0 of `text` with the given integer arguments.
/// Fails on an unmodeled word, a runaway loop, or a RET that does not
/// restore SP, X29 and X30.
pub fn run(text: &[u8], args: &[u64]) -> Result<Run, String> {
    let mut registers = [0; 31];
    registers[..args.len()].copy_from_slice(args);
    run_with_registers(text, registers)
}

/// [`run`] with every general register seeded; X29 and X30 are replaced by
/// `ENTRY_FP` and `RETURN_ADDRESS`.
pub fn run_with_registers(text: &[u8], registers: [u64; 31]) -> Result<Run, String> {
    run_with_exits(text, registers, Exits::default())
}

/// [`run_with_registers`] that also accepts the `exits` named. A tail-call
/// exit must restore SP, X29 and X30 like a `RET`; a trap exit is checked by
/// the caller.
pub fn run_with_exits(text: &[u8], registers: [u64; 31], exits: Exits) -> Result<Run, String> {
    let mut machine = Machine {
        text,
        x: registers,
        sp: ENTRY_SP,
        n: false,
        z: false,
        c: false,
        v: false,
        mem: HashMap::new(),
        frame_record_saved: false,
        exits,
        run: Run {
            min_sp: ENTRY_SP,
            lowest_touch: ENTRY_SP + MAX_UNPROBED,
            ..Run::default()
        },
    };
    machine.x[29] = ENTRY_FP;
    machine.x[30] = RETURN_ADDRESS;
    let mut pc = 0usize;
    for _ in 0..STEP_LIMIT {
        machine.run.steps += 1;
        match machine.step(pc)? {
            Some(next) => pc = next,
            None if matches!(machine.run.exit, Exit::Trap(_)) => {
                machine.run.registers = machine.x;
                return Ok(machine.run);
            }
            None => {
                if machine.run.exit == Exit::TailCall && machine.x[30] != RETURN_ADDRESS {
                    return Err(format!(
                        "tail call with x30 {:#x}, expected {RETURN_ADDRESS:#x}",
                        machine.x[30]
                    ));
                }
                if machine.sp != ENTRY_SP || machine.x[29] != ENTRY_FP {
                    return Err(format!(
                        "RET with SP {:#x} / x29 {:#x}, expected {ENTRY_SP:#x} / {ENTRY_FP:#x}",
                        machine.sp, machine.x[29]
                    ));
                }
                machine.run.result = machine.x[0];
                machine.run.registers = machine.x;
                return Ok(machine.run);
            }
        }
    }
    Err("step limit reached".into())
}
