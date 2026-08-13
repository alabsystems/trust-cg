#![allow(dead_code)]
// x86_interp.rs — a minimal, host-independent x86-64 machine-code interpreter for
// the guard-elimination link/run proofs.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// # Why this exists
//
// The x86 guard-elimination proof (`guard_kernel_gate_x86_linkrun.rs`) proves
// correctness on this arm64 macOS host only by an objdump *decode* oracle and a
// cross-arch (AArch64) link+RUN mirror — the real x86 link+RUN test SKIPs because
// Rosetta cannot execute x86-64 here. The RISC-V backend, by contrast, literally
// EXECUTES its emitted machine-code words in-process (`RiscVByteInterp`). This
// module brings the SAME literal-execution power to x86: it decodes and executes
// the exact, closed instruction subset the guard corpus emits, so both
//   (A) proven-in-bounds returns the correct `arr[idx]` with the guard eliminated,
//   (B) an undischarged/out-of-bounds access reaches `UD2` (TRAPPED),
// are proven by *running the x86 bytes* on this host, with no Rosetta and no link.
//
// # Fail-closed / decode-or-reject
//
// Per the repo's DECODE-OR-REJECT mandate, this interpreter NEVER silently skips a
// byte it does not understand: any unrecognized opcode / ModRM / SIB / REX form
// returns `Err(DecodeError::..)`. `UD2` (`0F 0B`) is modeled as a DISTINCT
// `Outcome::Trapped`, never as normal completion. This is what makes the test
// trustworthy: it cannot give a false PASS by ignoring the instruction under test.
//
// # The closed instruction subset (verified against objdump on the corpus)
//
//   prologue  : 55 push rbp ; 48 89 e5 mov rbp,rsp ; 53 push rbx ; 48 83 ec 48 sub rsp,0x48 ;
//               48 89 fb mov rbx,rdi
//   byval copy: 48 8d 4d 10 lea rcx,[rbp+0x10] ; 48 8d 55 b8 lea rdx,[rbp-0x48] ; then 8x
//               48 8b 41 dd mov rax,[src+dd] ; 48 89 42 dd mov [dst+dd],rax   (regs swap by regalloc)
//   guard     : 48 83 fb 08 cmp rbx,0x8 ; 0f 83 11 00 00 00 jae +0x11 (-> ud2)   [kept cases only]
//   access    : 48 8d 04 da lea rax,[base+rbx*8] ; 48 8b 08 mov rcx,[rax] ; 48 89 c8 mov rax,rcx
//   epilogue  : 48 83 c4 48 add rsp,0x48 ; 5b pop rbx ; 5d pop rbp ; c3 ret
//   trap block: 0f 0b ud2
//
// Decode is VARIABLE-LENGTH; the instruction pointer advances by the real decoded
// length. Register choice (rcx/rdx) swaps between gate-off and default-on builds
// (regalloc), so we ALWAYS decode the actual ModRM/SIB bytes — never hardcode a reg.

use std::collections::HashMap;
use std::process::Command;

// ---------------------------------------------------------------------------
// Register file
// ---------------------------------------------------------------------------

// x86-64 4-bit hardware encodings (matches trust_cg_ir::x86_64_regs::x86_hw_encoding).
const RAX: usize = 0;
const RCX: usize = 1;
const RDX: usize = 2;
const RBX: usize = 3;
const RSP: usize = 4;
const RBP: usize = 5;
const RSI: usize = 6;
const RDI: usize = 7;

const REG_NAMES: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

/// Distinct execution outcome. `UD2` produces `Trapped` — never normal completion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// `ret` to the sentinel return address: normal completion, with `%rax`.
    Returned(u64),
    /// `ud2` (`0F 0B`) was reached: a distinct trap, never normal completion.
    Trapped,
}

/// Typed decode/exec error. Any unrecognized byte pattern fails closed here —
/// it is NEVER skipped or treated as a NOP.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    UnknownOpcode {
        byte: u8,
        rip: usize,
    },
    UnknownTwoByteOpcode {
        byte: u8,
        rip: usize,
    },
    /// REX.R/X/B set: would reference r8-r15, which the corpus never emits. Fail
    /// closed rather than silently mis-decode a register.
    UnsupportedRexExtension {
        rex: u8,
        rip: usize,
    },
    /// A ModRM/SIB addressing form outside the supported subset.
    UnsupportedAddressing {
        detail: String,
        rip: usize,
    },
    /// An `83 /n` group extension we do not model (only /0 ADD, /5 SUB, /7 CMP).
    UnsupportedGroupExt {
        ext: u8,
        rip: usize,
    },
    /// Instruction pointer ran off the end of the text.
    RipOutOfBounds {
        rip: usize,
        len: usize,
    },
    /// Memory access out of the modeled arena.
    MemOutOfBounds {
        addr: u64,
    },
    /// Step limit hit: a corrupted return address / nonterminating program.
    StepLimit,
}

/// A flat, byte-addressed memory arena big enough for the call frame plus the
/// incoming by-value array. The interpreter places `%rsp`/`%rbp` near the top.
const MEM_SIZE: usize = 1 << 16;
/// Step cap: the corpus is a short leaf body, so any overrun means corruption.
const STEP_LIMIT: usize = 10_000;
/// A return address far outside the text: when `ret` pops it, execution stops.
const SENTINEL_RA: u64 = 0xFFFF_FFFF_FFFF_FF00;

pub struct X86ByteInterp {
    pub regs: [u64; 16],
    pub cf: bool,
    pub mem: Vec<u8>,
    pub text: Vec<u8>,
    /// Decoded `(mnemonic, length)` trace of every instruction executed, used to
    /// cross-check this in-house decoder against the objdump oracle.
    pub trace: Vec<(String, usize)>,
}

impl X86ByteInterp {
    pub fn new(text: Vec<u8>) -> Self {
        Self {
            regs: [0u64; 16],
            cf: false,
            mem: vec![0u8; MEM_SIZE],
            text,
            trace: Vec::new(),
        }
    }

    fn read_u64(&self, addr: u64) -> Result<u64, DecodeError> {
        let a = addr as usize;
        if a.checked_add(8).map(|e| e > self.mem.len()).unwrap_or(true) {
            return Err(DecodeError::MemOutOfBounds { addr });
        }
        let mut b = [0u8; 8];
        b.copy_from_slice(&self.mem[a..a + 8]);
        Ok(u64::from_le_bytes(b))
    }

    fn write_u64(&mut self, addr: u64, val: u64) -> Result<(), DecodeError> {
        let a = addr as usize;
        if a.checked_add(8).map(|e| e > self.mem.len()).unwrap_or(true) {
            return Err(DecodeError::MemOutOfBounds { addr });
        }
        self.mem[a..a + 8].copy_from_slice(&val.to_le_bytes());
        Ok(())
    }

    /// Set up the System V call frame for `fn f([i64;8] arr_byval, i64 idx) -> i64`.
    ///
    /// CRITICAL ABI fact: `[i64;8]` is 64 bytes (> 16) => System V MEMORY class =>
    /// the array is passed BY VALUE ON THE STACK, and only `idx` arrives in a
    /// register (`%rdi`). The emitted prologue reads the array from `0x10(%rbp)`
    /// (the caller's by-value slot) and `%rdi` holds `idx` (proven by `mov %rdi,%rbx`).
    ///
    /// So we lay out, from the top of `mem` downward, a synthetic caller frame:
    ///   [rbp_at_entry + 0x10 .. +0x10+64) : the 64 array bytes (8 LE i64s)
    ///   [rbp_at_entry + 0x08]             : caller-saved slot (unused here)
    ///   [rsp_at_entry]                    : the return address = SENTINEL_RA
    /// then jump to the function entry with `%rdi = idx`. `%rbp` is NOT yet set;
    /// the prologue's `push rbp ; mov rbp,rsp` establishes it. We arrange the
    /// initial `%rsp` so that AFTER the prologue, `%rbp + 0x10` lands exactly on
    /// our array bytes.
    ///
    /// Frame geometry after `push rbp ; mov rbp,rsp`:
    ///   rbp_post == rsp_after_push_rbp
    ///   [rbp_post + 0x00] = saved old rbp
    ///   [rbp_post + 0x08] = return address (what `ret` pops)
    ///   [rbp_post + 0x10] = first by-value stack arg (the array)  <-- prologue reads here
    /// We therefore pick rbp_post, place the array at rbp_post+0x10, the return
    /// address (SENTINEL) at rbp_post+0x08, and set the initial `%rsp = rbp_post + 0x08`
    /// (so the entry `push rbp` decrements rsp to rbp_post and stores old rbp there).
    pub fn setup_call(&mut self, arr: &[i64; 8], idx: i64) {
        // Choose rbp_post comfortably below the top of mem so the array (64 bytes
        // at +0x10) and the saved-rbp / return-address slots all fit, and so the
        // `sub $0x48,%rsp` local frame below rbp_post stays in-bounds.
        let rbp_post: u64 = (MEM_SIZE as u64) - 4096;

        // Return address slot ([rbp_post+0x08]) holds the sentinel; `ret` pops it.
        self.write_u64(rbp_post + 0x08, SENTINEL_RA)
            .expect("return-addr slot in bounds");

        // By-value array at [rbp_post+0x10 .. +0x10+64).
        for (i, &v) in arr.iter().enumerate() {
            self.write_u64(rbp_post + 0x10 + (i as u64) * 8, v as u64)
                .expect("byval array slot in bounds");
        }

        // Initial rsp = rbp_post + 0x08; entry `push rbp` will push old rbp at
        // [rbp_post], leaving rsp = rbp_post, then `mov rbp,rsp` sets rbp = rbp_post.
        self.regs[RSP] = rbp_post + 0x08;
        // idx arrives in %rdi (NOT an array pointer — the array is on the stack).
        self.regs[RDI] = idx as u64;
        // %rsi is unused by this body but is the SysV second int arg slot; leave 0.
        self.regs[RSI] = 0;
    }

    /// Decode + execute from `entry_pc` (function entry, offset 0) until `ret`
    /// (to the sentinel) or `ud2`. Returns the outcome, or a typed decode error
    /// the moment an unrecognized byte pattern is seen (fail-closed).
    pub fn run(&mut self, entry_pc: usize) -> Result<Outcome, DecodeError> {
        let mut rip = entry_pc;
        for _ in 0..STEP_LIMIT {
            if rip >= self.text.len() {
                return Err(DecodeError::RipOutOfBounds {
                    rip,
                    len: self.text.len(),
                });
            }
            let (outcome, next) = self.step(rip)?;
            if let Some(o) = outcome {
                return Ok(o);
            }
            rip = next;
        }
        Err(DecodeError::StepLimit)
    }

    fn byte(&self, rip: usize) -> Result<u8, DecodeError> {
        self.text
            .get(rip)
            .copied()
            .ok_or(DecodeError::RipOutOfBounds {
                rip,
                len: self.text.len(),
            })
    }

    /// Decode + execute ONE instruction at `rip`. Returns `(Some(outcome), _)` if
    /// the instruction halts (`ret`/`ud2`), else `(None, next_rip)`.
    fn step(&mut self, rip: usize) -> Result<(Option<Outcome>, usize), DecodeError> {
        let b0 = self.byte(rip)?;

        // --- One-byte opcodes that take no REX prefix in this corpus. ---
        match b0 {
            0x50..=0x57 => {
                // PUSH r64 (opcode-embedded reg, no REX.B here).
                let reg = (b0 - 0x50) as usize;
                self.regs[RSP] = self.regs[RSP].wrapping_sub(8);
                let sp = self.regs[RSP];
                self.write_u64(sp, self.regs[reg])?;
                self.trace.push((format!("push %{}", REG_NAMES[reg]), 1));
                return Ok((None, rip + 1));
            }
            0x58..=0x5F => {
                // POP r64.
                let reg = (b0 - 0x58) as usize;
                let sp = self.regs[RSP];
                self.regs[reg] = self.read_u64(sp)?;
                self.regs[RSP] = self.regs[RSP].wrapping_add(8);
                self.trace.push((format!("pop %{}", REG_NAMES[reg]), 1));
                return Ok((None, rip + 1));
            }
            0xC3 => {
                // RET: pop return address; if it's the sentinel, stop with %rax.
                let sp = self.regs[RSP];
                let ra = self.read_u64(sp)?;
                self.regs[RSP] = self.regs[RSP].wrapping_add(8);
                self.trace.push(("ret".to_string(), 1));
                if ra == SENTINEL_RA {
                    return Ok((Some(Outcome::Returned(self.regs[RAX])), rip + 1));
                }
                // The corpus never has an internal call/ret to a non-sentinel
                // address; treat anything else as a fail-closed error.
                return Err(DecodeError::UnsupportedAddressing {
                    detail: format!("ret to non-sentinel address {ra:#x}"),
                    rip,
                });
            }
            0x0F => {
                // Two-byte opcode escape.
                let b1 = self.byte(rip + 1)?;
                return self.step_0f(rip, b1);
            }
            _ => {}
        }

        // --- REX-prefixed opcodes (corpus always uses 0x48 = REX.W only). ---
        if (0x40..=0x4F).contains(&b0) {
            let rex = b0;
            // REX.R (0x04) / REX.X (0x02) / REX.B (0x01) would select r8-r15; the
            // corpus never sets them. Fail closed rather than mis-decode.
            if rex & 0x07 != 0 {
                return Err(DecodeError::UnsupportedRexExtension { rex, rip });
            }
            let op = self.byte(rip + 1)?;
            return self.step_rexw(rip, op);
        }

        Err(DecodeError::UnknownOpcode { byte: b0, rip })
    }

    /// Two-byte (`0F ..`) opcodes: only UD2 (`0F 0B`) and Jcc rel32 (`0F 83`).
    fn step_0f(&mut self, rip: usize, b1: u8) -> Result<(Option<Outcome>, usize), DecodeError> {
        match b1 {
            0x0B => {
                // UD2 => distinct TRAPPED outcome (never normal completion).
                self.trace.push(("ud2".to_string(), 2));
                Ok((Some(Outcome::Trapped), rip + 2))
            }
            0x83 => {
                // JAE/JNB rel32: taken iff CF == 0 (unsigned idx >= bound).
                let rel = self.read_i32(rip + 2)?;
                let len = 6usize; // 0F 83 + 4-byte rel32
                self.trace.push(("jae".to_string(), len));
                let fallthrough = rip + len;
                if !self.cf {
                    // Target is relative to the END of the instruction.
                    let target = (fallthrough as i64 + rel as i64) as usize;
                    Ok((None, target))
                } else {
                    Ok((None, fallthrough))
                }
            }
            other => Err(DecodeError::UnknownTwoByteOpcode { byte: other, rip }),
        }
    }

    /// REX.W (0x48)-prefixed opcodes: MOV r/m<->r, LEA, and the `83 /n` group.
    fn step_rexw(&mut self, rip: usize, op: u8) -> Result<(Option<Outcome>, usize), DecodeError> {
        match op {
            0x89 => {
                // MOV r/m64, r64  (store / reg-copy; ModRM.reg = source).
                let m = self.decode_modrm(rip + 2)?;
                let src = self.regs[m.reg];
                match m.operand {
                    Operand::Reg(r) => self.regs[r] = src,
                    Operand::Mem(addr) => self.write_u64(addr, src)?,
                }
                self.trace.push(("mov".to_string(), 2 + m.len));
                Ok((None, rip + 2 + m.len))
            }
            0x8B => {
                // MOV r64, r/m64  (load / reg-copy; ModRM.reg = dest).
                let m = self.decode_modrm(rip + 2)?;
                let val = match m.operand {
                    Operand::Reg(r) => self.regs[r],
                    Operand::Mem(addr) => self.read_u64(addr)?,
                };
                self.regs[m.reg] = val;
                self.trace.push(("mov".to_string(), 2 + m.len));
                Ok((None, rip + 2 + m.len))
            }
            0x8D => {
                // LEA r64, m  (compute effective address; NO memory access).
                let m = self.decode_modrm(rip + 2)?;
                let addr = match m.operand {
                    Operand::Mem(addr) => addr,
                    Operand::Reg(_) => {
                        return Err(DecodeError::UnsupportedAddressing {
                            detail: "lea with register-direct ModRM".to_string(),
                            rip,
                        });
                    }
                };
                self.regs[m.reg] = addr;
                self.trace.push(("lea".to_string(), 2 + m.len));
                Ok((None, rip + 2 + m.len))
            }
            0x83 => {
                // Group: 83 /n r/m64, imm8 (sign-extended). /0=ADD /5=SUB /7=CMP.
                let m = self.decode_modrm(rip + 2)?;
                // imm8 follows the ModRM/SIB/disp.
                let imm_off = rip + 2 + m.len;
                let imm = self.byte(imm_off)? as i8 as i64;
                let total = 2 + m.len + 1;
                let dst = match m.operand {
                    Operand::Reg(r) => r,
                    Operand::Mem(_) => {
                        return Err(DecodeError::UnsupportedAddressing {
                            detail: "83 /n with memory operand".to_string(),
                            rip,
                        });
                    }
                };
                match m.reg_ext {
                    0 => {
                        // ADD r/m64, imm8 (used for `add $0x48,%rsp`).
                        self.regs[dst] = self.regs[dst].wrapping_add(imm as u64);
                        self.trace.push(("add".to_string(), total));
                    }
                    5 => {
                        // SUB r/m64, imm8 (used for `sub $0x48,%rsp`).
                        self.regs[dst] = self.regs[dst].wrapping_sub(imm as u64);
                        self.trace.push(("sub".to_string(), total));
                    }
                    7 => {
                        // CMP r/m64, imm8: set CF for the UNSIGNED compare that the
                        // following `jae` consumes. CF = (dst < imm) as unsigned.
                        // imm8 is sign-extended to 64 bits before the unsigned test
                        // (matches x86: cmp $8 is cmp $0x0000000000000008).
                        let lhs = self.regs[dst];
                        let rhs = imm as u64;
                        self.cf = lhs < rhs;
                        self.trace.push(("cmp".to_string(), total));
                    }
                    ext => return Err(DecodeError::UnsupportedGroupExt { ext, rip }),
                }
                Ok((None, rip + total))
            }
            other => Err(DecodeError::UnknownOpcode { byte: other, rip }),
        }
    }

    fn read_i32(&self, rip: usize) -> Result<i32, DecodeError> {
        let b = [
            self.byte(rip)?,
            self.byte(rip + 1)?,
            self.byte(rip + 2)?,
            self.byte(rip + 3)?,
        ];
        Ok(i32::from_le_bytes(b))
    }

    /// Decode a ModRM byte (and any SIB / disp) starting at `at`. Supports:
    ///   mod=11 register-direct; mod=00 [rm] (with rm=100 => SIB, no disp);
    ///   mod=01 [rm]+disp8; mod=10 [rm]+disp32. Fails closed on RIP-relative
    ///   (mod=00,rm=101) and any unsupported SIB.index/base, since the corpus
    ///   never emits them.
    fn decode_modrm(&self, at: usize) -> Result<ModRm, DecodeError> {
        let modrm = self.byte(at)?;
        let mod_bits = modrm >> 6;
        let reg = ((modrm >> 3) & 0x07) as usize;
        let rm = (modrm & 0x07) as usize;

        if mod_bits == 0b11 {
            // Register-direct: operand is a register.
            return Ok(ModRm {
                reg,
                reg_ext: reg as u8,
                operand: Operand::Reg(rm),
                len: 1,
            });
        }

        // Memory form. Handle SIB (rm == 100) and plain [rm].
        if rm == 0b100 {
            // SIB byte follows.
            let sib = self.byte(at + 1)?;
            let scale = 1u64 << (sib >> 6);
            let index = ((sib >> 3) & 0x07) as usize;
            let base = (sib & 0x07) as usize;

            // index == 100 means "no index"; the corpus always has a real index
            // (rbx) so reject the no-index form to stay fail-closed/tight.
            if index == 0b100 {
                return Err(DecodeError::UnsupportedAddressing {
                    detail: "SIB with no index".to_string(),
                    rip: at,
                });
            }
            // base == 101 with mod==00 means disp32 with no base; the corpus
            // always has a real base, so reject.
            if base == 0b101 && mod_bits == 0b00 {
                return Err(DecodeError::UnsupportedAddressing {
                    detail: "SIB disp32-no-base".to_string(),
                    rip: at,
                });
            }

            let (disp, disp_len) = self.decode_disp(at + 2, mod_bits)?;
            let addr = self.regs[base]
                .wrapping_add(self.regs[index].wrapping_mul(scale))
                .wrapping_add(disp as u64);
            return Ok(ModRm {
                reg,
                reg_ext: reg as u8,
                operand: Operand::Mem(addr),
                // ModRM(1) + SIB(1) + disp.
                len: 2 + disp_len,
            });
        }

        // Plain [rm] (no SIB). rm==101 with mod==00 is RIP-relative — reject:
        // the corpus body has no RIP-relative loads.
        if rm == 0b101 && mod_bits == 0b00 {
            return Err(DecodeError::UnsupportedAddressing {
                detail: "RIP-relative addressing".to_string(),
                rip: at,
            });
        }

        let (disp, disp_len) = self.decode_disp(at + 1, mod_bits)?;
        let addr = self.regs[rm].wrapping_add(disp as u64);
        Ok(ModRm {
            reg,
            reg_ext: reg as u8,
            operand: Operand::Mem(addr),
            len: 1 + disp_len,
        })
    }

    /// Decode the displacement for a given ModRM `mod`: none (mod=00), disp8
    /// (mod=01, sign-extended), or disp32 (mod=10). Returns (value, byte_count).
    fn decode_disp(&self, at: usize, mod_bits: u8) -> Result<(i64, usize), DecodeError> {
        match mod_bits {
            0b00 => Ok((0, 0)),
            0b01 => {
                let d = self.byte(at)? as i8 as i64;
                Ok((d, 1))
            }
            0b10 => {
                let d = self.read_i32(at)? as i64;
                Ok((d, 4))
            }
            _ => unreachable!("mod=11 handled before decode_disp"),
        }
    }
}

/// A decoded ModRM operand: either a register index or a computed memory address.
enum Operand {
    Reg(usize),
    Mem(u64),
}

/// Decoded ModRM result: the `reg` field (and its raw value as a group extension),
/// the addressed operand, and the total ModRM+SIB+disp length in bytes.
struct ModRm {
    reg: usize,
    reg_ext: u8,
    operand: Operand,
    len: usize,
}

// ===========================================================================
// Mach-O __TEXT,__text extraction
// ===========================================================================

fn read_u32_le(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}

/// Extract the `__TEXT,__text` section bytes (the function's machine code, entry
/// at offset 0) from an emitted x86-64 Mach-O object. Parses the LC_SEGMENT_64
/// load commands, finds the `__text` section, and slices `[offset, offset+size)`.
pub fn extract_macho_text(obj: &[u8]) -> Vec<u8> {
    const MH_MAGIC_64: u32 = 0xFEED_FACF;
    const LC_SEGMENT_64: u32 = 0x19;
    const MACH_HEADER_64_SIZE: usize = 32;
    const SEGMENT_COMMAND_64_SIZE: usize = 72;
    const SECTION_64_SIZE: usize = 80;

    assert!(
        obj.len() >= MACH_HEADER_64_SIZE,
        "object too small for Mach-O header"
    );
    assert_eq!(
        read_u32_le(obj, 0),
        MH_MAGIC_64,
        "not a 64-bit little-endian Mach-O"
    );

    let ncmds = read_u32_le(obj, 16) as usize;
    let mut offset = MACH_HEADER_64_SIZE;

    for _ in 0..ncmds {
        let cmd = read_u32_le(obj, offset);
        let cmdsize = read_u32_le(obj, offset + 4) as usize;
        if cmd == LC_SEGMENT_64 {
            let nsects = read_u32_le(obj, offset + 64) as usize;
            let mut sec = offset + SEGMENT_COMMAND_64_SIZE;
            for _ in 0..nsects {
                // section_64: sectname[16] segname[16] addr(u64) size(u64) offset(u32) ...
                let sectname = &obj[sec..sec + 16];
                let name_end = sectname.iter().position(|&c| c == 0).unwrap_or(16);
                if &sectname[..name_end] == b"__text" {
                    // section_64 layout: sectname[16] segname[16] addr(u64,+32)
                    // size(u64,+40) offset(u32,+48) ...
                    let size =
                        u64::from_le_bytes(obj[sec + 40..sec + 48].try_into().unwrap()) as usize;
                    let file_off = read_u32_le(obj, sec + 48) as usize;
                    return obj[file_off..file_off + size].to_vec();
                }
                sec += SECTION_64_SIZE;
            }
        }
        offset += cmdsize;
    }
    panic!("__text section not found in Mach-O object");
}

// ===========================================================================
// objdump cross-check
// ===========================================================================

/// True if `objdump` is available (the same toolchain the link corpus uses).
pub fn has_objdump() -> bool {
    Command::new("objdump")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Disassemble the object with objdump and return the ordered `(offset, mnemonic)`
/// stream of the `__text` section. Used to cross-check the in-house decoder.
/// Returns `None` if objdump is unavailable or fails.
pub fn objdump_mnemonics(obj: &[u8]) -> Option<Vec<(u64, String)>> {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_x86interp_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).ok()?;
    let path = dir.join("g.o");
    std::fs::write(&path, obj).ok()?;
    let output = Command::new("objdump")
        .args(["-d", "--no-show-raw-insn", path.to_str()?])
        .output()
        .ok();
    let _ = std::fs::remove_dir_all(&dir);
    let output = output?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut out = Vec::new();
    for line in text.lines() {
        let Some((addr_part, rest)) = line.split_once(':') else {
            continue;
        };
        let addr_tok = addr_part.trim();
        if addr_tok.is_empty() || !addr_tok.chars().all(|c| c.is_ascii_hexdigit()) {
            continue;
        }
        let Ok(offset) = u64::from_str_radix(addr_tok, 16) else {
            continue;
        };
        let body = rest.trim_start_matches([' ', '\t']);
        if body.is_empty() {
            continue;
        }
        let mnem = body
            .split('\t')
            .next()
            .unwrap_or("")
            .trim()
            .to_ascii_lowercase();
        if mnem.is_empty() {
            continue;
        }
        out.push((offset, mnem));
    }
    Some(out)
}

/// Normalize an objdump x86 mnemonic to the bare operation our interpreter trace
/// uses (drop the AT&T size suffix `q`, collapse all `j*` to `jae`/branch class).
/// We compare on operation class so the cross-check is robust to suffix spelling.
pub fn normalize_objdump_mnemonic(m: &str) -> String {
    match m {
        "pushq" | "push" => "push".to_string(),
        "popq" | "pop" => "pop".to_string(),
        "retq" | "ret" => "ret".to_string(),
        "ud2" => "ud2".to_string(),
        "leaq" | "lea" => "lea".to_string(),
        "movq" | "mov" => "mov".to_string(),
        "cmpq" | "cmp" => "cmp".to_string(),
        "addq" | "add" => "add".to_string(),
        "subq" | "sub" => "sub".to_string(),
        // Any conditional/unconditional jump: the only one the corpus emits is jae.
        j if j.starts_with('j') => "jae".to_string(),
        other => other.to_string(),
    }
}

/// Collapse a trace entry mnemonic (e.g. "push %rbp") to its operation class.
pub fn trace_op_class(m: &str) -> String {
    m.split_whitespace().next().unwrap_or("").to_string()
}

/// Decode the WHOLE `__text` linearly (entry .. end), returning the ordered
/// `(offset, op_class)` stream. Unlike `run`, this does NOT follow control flow
/// or stop at `ret` — it decodes every instruction byte (including the trailing
/// `ud2` trap block past the `ret`), so its sequence can be compared 1:1 with
/// objdump's. Fails closed on any unrecognized byte.
pub fn decode_all(text: &[u8]) -> Result<Vec<(u64, String)>, DecodeError> {
    // We reuse the decoder's length computation by running a no-side-effect
    // variant: build a throwaway interp, but only call the pure length/mnemonic
    // decode. Simplest: replicate the dispatch using a fresh interp whose regs
    // are all zero (addresses are irrelevant — we only need lengths + mnemonics).
    let mut interp = X86ByteInterp::new(text.to_vec());
    // Point rsp/rbp into the arena so any (unused) address math stays in-bounds.
    interp.regs[RSP] = (MEM_SIZE as u64) - 4096;
    interp.regs[RBP] = (MEM_SIZE as u64) - 4096;

    let mut out = Vec::new();
    let mut rip = 0usize;
    while rip < text.len() {
        let before = interp.trace.len();
        // step() executes effects, but for linear decode we only consume the
        // returned length; ret/ud2 return Some(outcome) which we ignore here so
        // we keep walking past them to cover the whole section.
        let (_outcome, next) = interp.linear_step(rip)?;
        // The trace just got one new entry; record its op-class at this offset.
        let (mnem, _len) = interp.trace[before].clone();
        out.push((rip as u64, trace_op_class(&mnem)));
        rip = next;
    }
    Ok(out)
}

impl X86ByteInterp {
    /// Like `step`, but for LINEAR decode: it still decodes (and computes the real
    /// length / mnemonic), but for `ret` and the `jae` branch it just advances to
    /// the next sequential instruction so the whole section is walked. `ud2` is
    /// decoded as length 2 and walking continues. Memory effects of mov/push/pop
    /// are harmless here (regs/mem are scratch). Fails closed on unknown bytes.
    fn linear_step(&mut self, rip: usize) -> Result<(Option<Outcome>, usize), DecodeError> {
        let b0 = self.byte(rip)?;
        // For control-flow-affecting opcodes, override the next-rip to be linear.
        match b0 {
            0xC3 => {
                self.trace.push(("ret".to_string(), 1));
                return Ok((None, rip + 1));
            }
            0x0F => {
                let b1 = self.byte(rip + 1)?;
                match b1 {
                    0x0B => {
                        self.trace.push(("ud2".to_string(), 2));
                        return Ok((None, rip + 2));
                    }
                    0x83 => {
                        // jae rel32: length 6; linear walk to fallthrough.
                        let _ = self.read_i32(rip + 2)?;
                        self.trace.push(("jae".to_string(), 6));
                        return Ok((None, rip + 6));
                    }
                    other => return Err(DecodeError::UnknownTwoByteOpcode { byte: other, rip }),
                }
            }
            _ => {}
        }
        // Everything else has no control-flow effect; reuse the executing step,
        // whose returned next_rip equals rip + decoded_length for straight-line
        // instructions (push/pop/mov/lea/add/sub/cmp).
        self.step(rip)
    }
}

/// Helper map for tests that want to count instruction op-classes.
pub fn count_op_classes(stream: &[(u64, String)]) -> HashMap<String, usize> {
    let mut m = HashMap::new();
    for (_, op) in stream {
        *m.entry(op.clone()).or_insert(0) += 1;
    }
    m
}
