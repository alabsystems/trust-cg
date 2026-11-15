// trust-cg-verify/tests/support/x86_addressing_live_encode.rs - the memory-MOV address corpus, re-derived from the live encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! FRESHNESS for the x86-64 memory-MOV ADDRESS credit, in one place.
//!
//! `trust-cg-verify` cannot call `trust-cg-codegen` (that crate depends on this
//! one, so it is a DEV-dependency and only in tests), so the address obligation
//! is checked against bytes the LIVE encoder produces here and the credit hook
//! consumes them. Shared by the gate target and by every target that PINS the
//! published x86-64 ratio, via `#[path]`, so there is ONE definition of "what
//! the encoder emits today" rather than one per file — the failure mode the
//! MovRI and SSE lanes each hit when a re-derivation lived in only one gate.

#![allow(dead_code)]

use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::{X86Opcode, X86PReg};
use trust_cg_verify::x86_addressing_proofs as addr;

/// The `trust-cg-ir` physical register whose DISPLAY NAME is `name`. The scan
/// is over `trust-cg-ir`'s own name table — never over `x86_hw_encoding`, which
/// is part of the table under test.
pub fn preg_named(name: &str) -> X86PReg {
    (0u16..80)
        .map(X86PReg::new)
        .find(|r| r.to_string() == name)
        .unwrap_or_else(|| panic!("trust-cg-ir has no register named `{name}`"))
}

/// The 64-bit ROOT number of a GPR64. For `encoding() <= 15` this is the SDM
/// register number: `GPR64_NAMES` is in SDM order (rax, rcx, rdx, rbx, rsp,
/// rbp, rsi, rdi, r8..r15).
pub fn root_of(name: &str) -> u8 {
    let r = preg_named(name);
    if r.is_gpr64() {
        return r.encoding() as u8;
    }
    // XMM registers: the SDM number is the offset within the XMM file. Derived
    // from `trust-cg-ir`'s own display names, never from `x86_hw_encoding`.
    if let Some(rest) = name.strip_prefix("xmm") {
        return rest.parse::<u8>().expect("an xmm register is xmm<N>");
    }
    panic!("{name} is neither a GPR64 nor an XMM register");
}

/// Every memory opcode this lane covers: the access width and direction its
/// opcode fixes, whether it takes a SIB operand, and which register FILE its
/// register operand names.
pub const MEM_MOV_OPCODES: &[(X86Opcode, u32, bool, bool, bool)] = &[
    // (opcode, access_bits, is_store, is_sib, reg_is_xmm)
    // --- integer MOV ---
    (X86Opcode::MovRM, 64, false, false, false),
    (X86Opcode::MovRM32, 32, false, false, false),
    (X86Opcode::MovRM16, 16, false, false, false),
    (X86Opcode::MovRM8, 8, false, false, false),
    (X86Opcode::MovMR, 64, true, false, false),
    (X86Opcode::MovMR32, 32, true, false, false),
    (X86Opcode::MovMR16, 16, true, false, false),
    (X86Opcode::MovMR8, 8, true, false, false),
    (X86Opcode::MovRMSib, 64, false, true, false),
    (X86Opcode::MovRM32Sib, 32, false, true, false),
    (X86Opcode::MovRM8Sib, 8, false, true, false),
    (X86Opcode::MovMRSib, 64, true, true, false),
    (X86Opcode::MovMR32Sib, 32, true, true, false),
    (X86Opcode::MovMR8Sib, 8, true, true, false),
    // --- SSE scalar: the mandatory F3/F2 prefix picks the access width ---
    (X86Opcode::MovssRM, 32, false, false, true),
    (X86Opcode::MovsdRM, 64, false, false, true),
    (X86Opcode::MovssMR, 32, true, false, true),
    (X86Opcode::MovsdMR, 64, true, false, true),
    (X86Opcode::MovssRMSib, 32, false, true, true),
    (X86Opcode::MovsdRMSib, 64, false, true, true),
    // --- packed 128-bit ---
    (X86Opcode::MovdqaRM, 128, false, false, true),
    (X86Opcode::MovdquRM, 128, false, false, true),
    (X86Opcode::MovdqaMR, 128, true, false, true),
    (X86Opcode::MovdquMR, 128, true, false, true),
    (X86Opcode::MovdquRMSib, 128, false, true, true),
    (X86Opcode::MovdquMRSib, 128, true, true, true),
    // --- memory ALU: memory is the SOURCE for RM forms, the DESTINATION for
    //     MR forms. The ADDRESS facet is the same question either way ---
    (X86Opcode::AddRM, 64, false, false, false),
    (X86Opcode::SubRM, 64, false, false, false),
    (X86Opcode::CmpRM, 64, false, false, false),
    (X86Opcode::ImulRM, 64, false, false, false),
    (X86Opcode::XorMR, 64, true, false, false),
    (X86Opcode::AddMR, 64, true, false, false),
    (X86Opcode::ImulRMSib, 64, false, true, false),
    (X86Opcode::XorMRSib, 64, true, true, false),
    (X86Opcode::AddMRSib, 64, true, true, false),
    // --- LEA: computes the address, accesses no memory. The width is the
    //     DESTINATION operand's, and `is_store` is false because there is no
    //     memory operand to be the destination of ---
    (X86Opcode::Lea, 64, false, false, false),
    (X86Opcode::LeaSib, 64, false, true, false),
    // --- VOLATILE forms. Byte-identical to their plain siblings (the encoder
    //     handles `MovRM | VolatileMovRM` in one arm), so the decoder reads
    //     them unchanged. Their ADDRESS is the same question as any other
    //     memory access; what makes them volatile — that the access is emitted
    //     exactly once, at that width, in that order — is the separate
    //     `x86_volatile_trace` obligation, enforced per compile. None has a SIB
    //     form. ---
    (X86Opcode::VolatileMovRM8, 8, false, false, false),
    (X86Opcode::VolatileMovRM16, 16, false, false, false),
    (X86Opcode::VolatileMovRM32, 32, false, false, false),
    (X86Opcode::VolatileMovRM, 64, false, false, false),
    (X86Opcode::VolatileMovMR8, 8, true, false, false),
    (X86Opcode::VolatileMovMR16, 16, true, false, false),
    (X86Opcode::VolatileMovMR32, 32, true, false, false),
    (X86Opcode::VolatileMovMR, 64, true, false, false),
    (X86Opcode::VolatileMovssRM, 32, false, false, true),
    (X86Opcode::VolatileMovsdRM, 64, false, false, true),
    (X86Opcode::VolatileMovssMR, 32, true, false, true),
    (X86Opcode::VolatileMovsdMR, 64, true, false, true),
    (X86Opcode::VolatileMovdquRM, 128, false, false, true),
    (X86Opcode::VolatileMovdqaRM, 128, false, false, true),
    (X86Opcode::VolatileMovdquMR, 128, true, false, true),
    (X86Opcode::VolatileMovdqaMR, 128, true, false, true),
    // --- ZERO-EXTENDING loads (`[REX] 0F B6/B7 /r`): the access width is the
    //     opcode's, the register operand a 32-bit destination written whole.
    //     Their DESTINATION facet rides the same decode
    //     (`addr::destination_write_holds`). ---
    (X86Opcode::MovzxRM8, 8, false, false, false),
    (X86Opcode::MovzxRM16, 16, false, false, false),
    (X86Opcode::MovzxRM8Sib, 8, false, true, false),
    (X86Opcode::VolatileMovzxRM8, 8, false, false, false),
    (X86Opcode::VolatileMovzxRM16, 16, false, false, false),
];

/// Whether `op` is a ZERO-EXTENDING load (`movzx r32, m8/m16`), which the
/// intent states so that the bytes must decode as one. Spelled here, from the
/// opcode NAMES, rather than read from any table the library uses.
pub fn opcode_zero_extends(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::MovzxRM8
            | X86Opcode::MovzxRM16
            | X86Opcode::MovzxRM8Sib
            | X86Opcode::VolatileMovzxRM8
            | X86Opcode::VolatileMovzxRM16
    )
}

/// The narrow LOCK CMPXCHG forms (`F0 0F B0 /r`, `F0 66 0F B1 /r`): memory is
/// the DESTINATION (read, and written in both branches), the register operand
/// the replacement. `(opcode, access_bits)`. They take their own shapes
/// (`COMPARE_EXCHANGE_SHAPES`): the encoder refuses a source or base
/// overlapping the AL/AX accumulator, so `PLAIN_SHAPES`' `rax` rows do not
/// apply.
pub const COMPARE_EXCHANGE_OPCODES: &[(X86Opcode, u32)] =
    &[(X86Opcode::Cmpxchg8, 8), (X86Opcode::Cmpxchg16, 16)];

/// `(register, base, disp)` for the narrow compare-exchange forms: the same
/// `rbp`/`rsp`/REX-extended/disp8/disp32 corners as `PLAIN_SHAPES`, a mod=00
/// row, and `sil`/`dil` sources, whose byte form needs the forced REX that
/// keeps them from reading as DH/BH.
pub const COMPARE_EXCHANGE_SHAPES: &[(&str, &str, i64)] = &[
    ("r12", "r13", -8),
    ("rcx", "rbp", 0),
    ("rdx", "rsp", 4096),
    ("r8", "r9", -129),
    ("rsi", "rbx", 0),
    ("rdi", "rbx", 16),
];

/// `(base, disp)` for the 128-bit atomic-load pseudo, whose base may be none
/// of the four registers it zeroes (RAX/RBX/RCX/RDX): the same corners, and a
/// mod=00 row.
pub const ATOMIC_LOAD_CMPXCHG16B_BASES: &[(&str, i64)] = &[
    ("r13", -8),
    ("rbp", 0),
    ("rsp", 4096),
    ("r9", -129),
    ("rsi", 0),
    ("rdi", 16),
];

/// The four zeroing XORs the 128-bit atomic-load pseudo emits ahead of its
/// `LOCK CMPXCHG16B` (`xor eax,eax; xor edx,edx; xor ebx,ebx; xor ecx,ecx`,
/// as the host assembler encodes them).
pub const ATOMIC_LOAD_CMPXCHG16B_ZEROING: [u8; 8] =
    [0x31, 0xC0, 0x31, 0xD2, 0x31, 0xDB, 0x31, 0xC9];

/// The ADDRESS-bearing instruction of the 128-bit atomic-load pseudo — its
/// trailing `LOCK CMPXCHG16B [base + disp]` — from the live encoder, or `None`
/// when the encoder refuses the base (RAX/RBX/RCX/RDX). Panics if the pseudo
/// no longer starts with exactly the four zeroing XORs: the address lane
/// strips them, so it must know it strips nothing else (that the XORs are
/// right is ENC-3's per-compile check).
pub fn live_encode_atomic_load_cmpxchg16b(base: &str, disp: i64) -> Option<Vec<u8>> {
    let mut e = X86Encoder::new();
    e.encode_instruction(
        X86Opcode::AtomicLoadCmpxchg16b,
        &X86InstOperands {
            base: Some(preg_named(base)),
            disp,
            ..X86InstOperands::none()
        },
    )
    .ok()?;
    let bytes = e.finish();
    let zeroing = ATOMIC_LOAD_CMPXCHG16B_ZEROING.len();
    assert_eq!(
        bytes.get(..zeroing),
        Some(&ATOMIC_LOAD_CMPXCHG16B_ZEROING[..]),
        "AtomicLoadCmpxchg16b [{base}{disp:+}]: the pseudo no longer begins with the four \
         zeroing XORs ({bytes:02x?})"
    );
    Some(bytes[zeroing..].to_vec())
}

/// XMM registers used for the SSE and packed families, chosen to cover both
/// the low eight and the REX.R-extended high eight.
pub const XMM_REGS: &[&str] = &["xmm0", "xmm9", "xmm3", "xmm15"];

/// Operand shapes every opcode is exercised over. Chosen to cover the SDM
/// corner cases the encoder has to get right: an `rbp`/`r13` base (which cannot
/// use `mod = 00`), an `rsp`/`r12` slot, extended registers that need REX.B and
/// REX.X, every scale factor, and displacements on both sides of zero and past
/// the disp8 boundary.
pub const SIB_SHAPES: &[(&str, &str, &str, u8, i64)] = &[
    ("rax", "rbx", "rcx", 8, 16),
    ("r12", "r13", "r14", 4, -8),
    ("rdx", "rbp", "rsi", 1, 0),
    ("rdi", "rsp", "rbx", 2, 4096),
    ("r8", "r9", "r10", 8, -129),
    ("rcx", "r12", "r15", 4, 127),
    // mod=00: a zero displacement on a base that is NOT rbp/r13, which is the
    // only way the encoder emits the no-displacement form. Without this row
    // the whole `mod = 00` addressing mode goes unexercised and
    // `DispField::absent()` is never constructed.
    ("rax", "rbx", "rcx", 4, 0),
    // index field 100b WITH REX.X set is r12, not the no-index sentinel. This
    // is the one place REX.X changes the MEANING of the field rather than just
    // extending it: drop REX.X and the address silently loses its index term
    // entirely. Without this row that discriminating case is absent.
    ("rax", "rbx", "r12", 4, 16),
];

pub const PLAIN_SHAPES: &[(&str, &str, i64)] = &[
    ("rax", "rbx", 16),
    ("r12", "r13", -8),
    ("rcx", "rbp", 0),
    ("rdx", "rsp", 4096),
    ("r8", "r9", -129),
    // mod=00 again, for the non-SIB form: `[rbx]` with no displacement bytes.
    // This is the row that exposed the anti-vacuity guard refuting a CORRECT
    // encoding, because an absent displacement was being denoted as `+0`.
    ("rax", "rbx", 0),
];

pub fn live_encode_sib(
    op: X86Opcode,
    reg: &str,
    base: &str,
    index: &str,
    scale: u8,
    disp: i64,
) -> Option<Vec<u8>> {
    let mut e = X86Encoder::new();
    e.encode_instruction(
        op,
        &X86InstOperands::rm_sib(
            preg_named(reg),
            preg_named(base),
            preg_named(index),
            scale,
            disp,
        ),
    )
    .ok()?;
    Some(e.finish())
}

pub fn live_encode_plain(op: X86Opcode, reg: &str, base: &str, disp: i64) -> Option<Vec<u8>> {
    let mut e = X86Encoder::new();
    e.encode_instruction(
        op,
        &X86InstOperands::rm(preg_named(reg), preg_named(base), disp),
    )
    .ok()?;
    Some(e.finish())
}

/// One corpus entry: the bytes the encoder emitted and the INTENT they were
/// asked to encode.
pub struct MemMovCase {
    pub label: String,
    pub bytes: Vec<u8>,
    pub intent: addr::MemAccessIntent,
}

/// Build the whole live corpus. Entries the encoder REFUSES are skipped rather
/// than counted, so an encoder that silently stops supporting a form shrinks
/// the corpus and trips the size floor instead of quietly passing.
pub fn live_mem_mov_corpus() -> Vec<MemMovCase> {
    let mut out = Vec::new();
    for &(op, bits, is_store, is_sib, reg_is_xmm) in MEM_MOV_OPCODES {
        let reg_file = if reg_is_xmm {
            addr::RegFile::Xmm
        } else {
            addr::RegFile::Gpr
        };
        if is_sib {
            for (n, &(gpr_reg, base, index, scale, disp)) in SIB_SHAPES.iter().enumerate() {
                let reg = if reg_is_xmm {
                    XMM_REGS[n % XMM_REGS.len()]
                } else {
                    gpr_reg
                };
                let Some(bytes) = live_encode_sib(op, reg, base, index, scale, disp) else {
                    continue;
                };
                out.push(MemMovCase {
                    label: format!("{op:?} {reg},[{base}+{index}*{scale}{disp:+}]"),
                    bytes,
                    intent: addr::MemAccessIntent {
                        reg_root: root_of(reg),
                        reg_file,
                        base_root: root_of(base),
                        index_root: Some(root_of(index)),
                        scale: u32::from(scale),
                        disp,
                        access_bits: bits,
                        is_store,
                        zero_extending_load: opcode_zero_extends(op),
                    },
                });
            }
        } else {
            for (n, &(gpr_reg, base, disp)) in PLAIN_SHAPES.iter().enumerate() {
                let reg = if reg_is_xmm {
                    XMM_REGS[n % XMM_REGS.len()]
                } else {
                    gpr_reg
                };
                let Some(bytes) = live_encode_plain(op, reg, base, disp) else {
                    continue;
                };
                out.push(MemMovCase {
                    label: format!("{op:?} {reg},[{base}{disp:+}]"),
                    bytes,
                    intent: addr::MemAccessIntent {
                        reg_root: root_of(reg),
                        reg_file,
                        base_root: root_of(base),
                        index_root: None,
                        scale: 1,
                        disp,
                        access_bits: bits,
                        is_store,
                        zero_extending_load: opcode_zero_extends(op),
                    },
                });
            }
        }
    }
    // The narrow compare-exchange forms, over their own shapes.
    for &(op, bits) in COMPARE_EXCHANGE_OPCODES {
        for &(reg, base, disp) in COMPARE_EXCHANGE_SHAPES {
            let Some(bytes) = live_encode_plain(op, reg, base, disp) else {
                continue;
            };
            out.push(MemMovCase {
                label: format!("{op:?} {reg},[{base}{disp:+}]"),
                bytes,
                intent: addr::MemAccessIntent {
                    reg_root: root_of(reg),
                    reg_file: addr::RegFile::Gpr,
                    base_root: root_of(base),
                    index_root: None,
                    scale: 1,
                    disp,
                    access_bits: bits,
                    is_store: true,
                    zero_extending_load: false,
                },
            });
        }
    }
    // The 128-bit atomic-load pseudo: its address is its trailing
    // `LOCK CMPXCHG16B m128`, whose ModR/M.reg is the `/1` extension (the
    // intent names 1), a 16-byte access with memory as the destination.
    for &(base, disp) in ATOMIC_LOAD_CMPXCHG16B_BASES {
        let Some(bytes) = live_encode_atomic_load_cmpxchg16b(base, disp) else {
            continue;
        };
        out.push(MemMovCase {
            label: format!("AtomicLoadCmpxchg16b /1,[{base}{disp:+}]"),
            bytes,
            intent: addr::MemAccessIntent {
                reg_root: 1,
                reg_file: addr::RegFile::Gpr,
                base_root: root_of(base),
                index_root: None,
                scale: 1,
                disp,
                access_bits: 128,
                is_store: true,
                zero_extending_load: false,
            },
        });
    }
    out
}
