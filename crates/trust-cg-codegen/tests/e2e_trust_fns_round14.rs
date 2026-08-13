//! TRUST-SELF ROUND 27 (thread R27, TRUST BATCH 14): verifying trust-cg's
//! AArch64 INSTRUCTION DECODER (the Phase-1 binary-lifting `word -> opcode +
//! operand fields` disassembler, `trust-cg-lift/src/disasm/aarch64.rs`) through
//! the full pipeline Rust -> MIR -> trust-ir (stage1 `trust_ir_mir
//! --mir-emit-closure`) -> trust-cg JIT -> machine code, asserting native Rust ==
//! JIT over swept real inputs, and — the round's power — the ENCODE<->DECODE
//! ROUND-TRIP against the R2-verified production encoders as an INDEPENDENT
//! cross-check (the analogue of R26's host-FPU oracle: an encoder and its decoder
//! must be inverses; an asymmetry is a real bug).
//!
//! WHY THIS SURFACE: rounds 1/3/7/16 verified the instruction-word BUILDERS
//! (fields -> word); round 24 verified the relocation encode/decode + fixup byte
//! patchers. This round verifies the DECODER — the inverse map `word -> fields`.
//! The decoder is not linkable into this crate (it lives in trust-cg-lift, which
//! trust-cg-codegen does not depend on), so the dual-oracle is built differently
//! and MORE independently:
//!   * NATIVE ORACLE = the verbatim slice `trust_aa_decode_slice.rs`, included as
//!     a module and compiled by NATIVE rustc; `native == JIT` compares the SAME
//!     source through two compilers.
//!   * ENCODE<->DECODE ROUND-TRIP = the LINKED, R2-verified production encoders
//!     `trust_cg_codegen::aarch64::encoding::encode_*` produce real instruction
//!     words; the JIT decoder must recover EXACTLY the encoder's input fields.
//!     A mismatch is an encoder/decoder ASYMMETRY (isolated + attributed if hit).
//!   * INDEPENDENT ORACLES = an ARM `DecodeBitMasks` reserved-gate reimplemented
//!     from the spec (for the logical-immediate bitmask decoder), and hand-built
//!     ARM-ARM boundary words.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe at
//! suite scale (jit-parallel-race-2026-06-29.md). Every JIT execution runs inside
//! a WATCHDOG worker thread. The output POD is 0xDEAD-poisoned before each JIT
//! call so a silent no-op fails loudly.
//!
//! REGENERATION CONTRACT: emit `trust_aa_decode.tir` with
//! `-C overflow-checks=off -C debug-assertions=off -C panic=abort`.  The JIT
//! deliberately rejects unwind/personality metadata, so omitting `panic=abort`
//! must fail closed instead of silently weakening the execution boundary.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED, R2-verified production encoders (the encode side of the round-trip):
use trust_cg_codegen::aarch64::encoding::{
    encode_add_sub_imm, encode_add_sub_shifted_reg, encode_branch_reg, encode_cmp_branch,
    encode_cond_branch, encode_load_store_pair, encode_load_store_ui, encode_load_store_unscaled,
    encode_logical_shifted_reg, encode_move_wide, encode_uncond_branch,
};

// NATIVE ORACLE: the verbatim decoder slice, compiled by native rustc.
#[path = "slices/trust_aa_decode_slice.rs"]
mod dec;
// NATIVE ORACLE: the verbatim logical-immediate gate slice.
#[path = "slices/trust_aa_logimm_gate_slice.rs"]
mod lg;

// ── shared harness (round-11/22/23 pattern) ───────────────────────────────────

const DECODE_IR: &str = include_str!("slices/trust_aa_decode.tir");
const LOGIMM_GATE_IR: &str = include_str!("slices/trust_aa_logimm_gate.tir");

fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

const WATCHDOG_SECS: u64 = 240;

fn run_watchdogged<T: Send + 'static>(
    what: &'static str,
    expected: usize,
    worker: impl FnOnce(mpsc::Sender<T>) + Send + 'static,
) -> Vec<T> {
    let (tx, rx) = mpsc::channel::<T>();
    std::thread::spawn(move || worker(tx));
    let mut rows = Vec::with_capacity(expected);
    for i in 0..expected {
        match rx.recv_timeout(Duration::from_secs(WATCHDOG_SECS)) {
            Ok(row) => rows.push(row),
            Err(_) => panic!(
                "JIT `{what}` HUNG (watchdog {WATCHDOG_SECS}s): no progress at row {i} of {expected}"
            ),
        }
    }
    rows
}

// ============================================================================
// SLICE 1 — the AArch64 instruction DECODER (disasm/aarch64.rs::decode).
// ============================================================================

type DecodeFn = unsafe extern "C" fn(u32, *mut dec::DecOut);

fn poison_out() -> dec::DecOut {
    dec::DecOut {
        tag: 0xDEAD,
        a: 0xDEAD,
        b: 0xDEAD,
        c: 0xDEAD,
        d: 0xDEAD,
        e: 0xDEAD,
        f: 0xDEAD,
        g: 0xDEAD,
        h: 0xDEAD,
    }
}

fn as9(o: &dec::DecOut) -> [u32; 9] {
    [o.tag, o.a, o.b, o.c, o.d, o.e, o.f, o.g, o.h]
}

/// Native oracle: run the verbatim decoder (compiled by native rustc) and reduce
/// to the packed row, exactly as the JIT root does.
fn native_decode_row(word: u32) -> [u32; 9] {
    let mut o = poison_out();
    dec::decode_root(word, &mut o);
    as9(&o)
}

/// A deterministic PCG-ish stream of pseudo-random 32-bit words — hammers the
/// WHOLE dispatch tree (every family arm + the Unsupported catch-all) so any
/// dispatch/extraction divergence between native and JIT surfaces.
fn random_words(n: usize) -> Vec<u32> {
    let mut state: u64 = 0x4d59_5f52_3237_0001;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        v.push((state >> 32) as u32);
    }
    v
}

/// Structured template words that pin specific families/edges (incl. the
/// reserved/reject direction the encoders cannot reach in-contract).
fn structured_words() -> Vec<u32> {
    vec![
        0xd503_201f, // NOP
        0xd420_0020, // BRK #1
        0x9000_0000, // ADRP x0, .
        0x1000_0000, // ADR  x0, .
        0x8b02_0020, // ADD  x0, x1, x2
        0x4b05_0083, // SUB  w3, w4, w5
        0x8a02_0020, // AND  x0, x1, x2  (logical shifted reg)
        0x9240_0c00, // AND  x0, x0, #0xf (logical imm, allocated)
        0x1100_0400, // ADD  w0, w0, #1  (add/sub imm)
        0xd280_0000, // MOVZ x0, #0
        0xd65f_03c0, // RET
        0xd63f_0000, // BLR  x0
        0xd61f_0000, // BR   x0
        0x1400_0000, // B    .
        0x9400_0000, // BL   .
        0x5400_0000, // B.eq .
        0xb400_0000, // CBZ  x0, .
        0x3600_0000, // TBZ  w0, #0, .
        0xf940_0000, // LDR  x0, [x0]
        0xf800_0400, // STR  x0, [x0], #0 (indexed post)
        0xf810_0400, // STUR-ish / indexed
        0xa940_0400, // LDP  x0, x1, [x0]
        // Allocated encodings with CONSTRAINED UNPREDICTABLE operand aliases.
        // These must reach the dedicated fail-closed tag in both native and JIT.
        0xf81e_b7de, // str x30,[x30],#-21 (Rt==Rn with writeback)
        0xa97b_8040, // ldp x0,x0,[x2,#-72] (Rt==Rt2)
        0xa989_0442, // stp x2,x1,[x2,#144]! (Rt==Rn with writeback)
        0x8803_fca3, // stlxr w3,w3,[x5] (Rs==Rt)
        0x8805_fca4, // stlxr w5,w4,[x5] (Rs==Rn)
        // Legal one-field neighbours and distinct-register-file boundaries.
        0xf81e_b7dd,
        0xa97b_8440,
        0xa989_0443,
        0x8803_fca4,
        0x3cc1_0400, // ldr q0,[x0],#16 (Vt and Xn do not alias)
        0xacc1_0c42, // ldp q2,q3,[x2],#32 (Vt and Xn do not alias)
        0x18000000,  // LDR  (literal)
        0x1ac0_2400, // (data-proc-2-source template)
        0x9b00_7c00, // MADD-ish (data-proc-3-source)
        0x1a80_0000, // CSEL-ish (conditional select)
        0x1e20_2800, // FADD s0,s1,s0 (fp arith)
        0x1e20_2000, // FCMP (fp compare)
        0x1e22_0000, // FMOV/precision (fp)
        0xd538_0000, // MRS  x0, (system reg read)
        0xd503_309f, // DSB-ish (system barrier)
        0x0e20_1c00, // NEON logic template
        0x4e21_0400, // NEON 3-same template
        0x0f00_e400, // MOVI template
        // DUP (element) — exercises decode_neon_element_imm5 (the trailing_zeros
        // rewrite): imm5 selects B/H/S/D by trailing-zero count.
        0x4e01_0400, // DUP Vd.16B, Vn.B[0]  (imm5=1, tz0 -> B)
        0x4e02_0400, // DUP Vd.8H,  Vn.H[0]  (imm5=2, tz1 -> H)
        0x4e04_0400, // DUP Vd.4S,  Vn.S[0]  (imm5=4, tz2 -> S)
        0x4e08_0400, // DUP Vd.2D,  Vn.D[0]  (imm5=8, tz3 -> D, q=1 ok)
        0x0e08_0400, // DUP .D with q=0 -> Unallocated
        0x4e10_0400, // imm5=16 (tz4) 128-bit element -> Unallocated
        0x4e04_0c00, // DUP (general) Vd.4S, Wn (imm5=4 -> S)
        // Reserved / reject direction (encoders cannot reach these in-contract):
        0x8bc0_0000, // add/sub shifted reg shift=0b11 (Unallocated)
        0xb280_0000, // move-wide opc=0b01 (Unallocated)
        0xd65f_03c1, // branch-reg with rt-bits!=0 (falls through)
        0x1240_0000, // 32-bit logical imm with N=1 (Unallocated)
        0xffff_ffff, // all-ones (Unsupported/whatever the tree yields)
        0x0000_0000, // all-zero (UDF -> Unsupported)
    ]
}

/// The AArch64 instruction decoder, native==JIT over a structured template set
/// + a 40k pseudo-random word stream that exercises the whole dispatch tree and
///   the Unsupported catch-all. Any dispatch or field-extraction divergence between
///   the native transcription and the JIT machine code fails loudly.
#[test]
fn trust_aa_decode_native_eq_jit() {
    let mut words = structured_words();
    words.extend(random_words(40_000));
    let expected = words.len();
    let sweep = words.clone();
    let rows = run_watchdogged::<[u32; 9]>("aa_decode", expected, move |tx| {
        let buffer = jit_module(DECODE_IR, "aa_decode");
        let f: DecodeFn = unsafe { std::mem::transmute(bind(&buffer, "decode_root")) };
        for &w in &sweep {
            let mut out = poison_out();
            unsafe { f(w, &mut out) };
            if tx.send(as9(&out)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &w) in words.iter().enumerate() {
        let native = native_decode_row(w);
        assert_eq!(
            rows[i], native,
            "decode(word={w:#010x}): JIT {:?} != native {:?}",
            rows[i], native
        );
        assert_ne!(
            rows[i][0], 0xDEAD,
            "row {i} tag still poisoned (word {w:#010x})"
        );
    }

    // ---- Independent ground-truth spot-checks (ARM DDI 0487 by hand). ----
    let r = |w: u32| rows[words.iter().position(|&x| x == w).expect("present")];
    // NOP -> tag 32 (Nop), no fields.
    assert_eq!(r(0xd503_201f)[0], 32, "NOP decodes to Instruction::Nop");
    // BRK #1 -> tag 33, imm16 = 1.
    assert_eq!((r(0xd420_0020)[0], r(0xd420_0020)[1]), (33, 1), "BRK #1");
    // RET -> tag 10 BranchReg{opc=2 (RET), rn=30}.
    assert_eq!(
        (r(0xd65f_03c0)[0], r(0xd65f_03c0)[1], r(0xd65f_03c0)[2]),
        (10, 2, 30),
        "RET -> BranchReg opc=2 rn=30"
    );
    // BLR x0 -> tag 10 opc=1 rn=0.
    assert_eq!(
        (r(0xd63f_0000)[0], r(0xd63f_0000)[1], r(0xd63f_0000)[2]),
        (10, 1, 0),
        "BLR x0"
    );
    // ADD x0,x1,x2 -> tag 0 {sf=1,op=0,s=0,shift=0,rm=2,imm6=0,rn=1,rd=0}.
    assert_eq!(
        r(0x8b02_0020),
        [0, 1, 0, 0, 0, 2, 0, 1, 0],
        "ADD x0,x1,x2 decodes to AddSubShiftedReg fields"
    );
    // Reserved add/sub shifted-reg shift=0b11 -> tag 0xE1 (Unallocated).
    assert_eq!(r(0x8bc0_0000)[0], 0xE1, "add/sub shift=0b11 is Unallocated");
    // Move-wide opc=0b01 -> tag 0xE1 (Unallocated).
    assert_eq!(r(0xb280_0000)[0], 0xE1, "move-wide opc=0b01 is Unallocated");
    // 32-bit logical-imm with N=1 -> tag 0xE1 (Unallocated).
    assert_eq!(
        r(0x1240_0000)[0],
        0xE1,
        "32-bit logical imm N=1 is Unallocated"
    );
    for word in [
        0xf81e_b7de,
        0xa97b_8040,
        0xa989_0442,
        0x8803_fca3,
        0x8805_fca4,
    ] {
        assert_eq!(
            r(word)[0],
            0xE2,
            "0x{word:08x} must be ConstrainedUnpredictable"
        );
    }
    // ADRP -> tag 7 PcRelAddress (page=1).
    assert_eq!(
        (r(0x9000_0000)[0], r(0x9000_0000)[1]),
        (7, 1),
        "ADRP is PcRelAddress page=1"
    );
    // ADR -> tag 7 page=0.
    assert_eq!(
        (r(0x1000_0000)[0], r(0x1000_0000)[1]),
        (7, 0),
        "ADR is PcRelAddress page=0"
    );

    // ---- NEON DUP element-size selection: INDEPENDENT ground-truth for the
    //      `trailing_zeros` rewrite (element_size discriminant B=0,H=1,S=2,D=3). ----
    // tag 41 = NeonDupElement {q, element_size, lane, rn, rd}.
    assert_eq!(
        (r(0x4e01_0400)[0], r(0x4e01_0400)[2]),
        (41, 0),
        "DUP imm5=1 -> element B(0)"
    );
    assert_eq!(
        (r(0x4e02_0400)[0], r(0x4e02_0400)[2]),
        (41, 1),
        "DUP imm5=2 -> element H(1)"
    );
    assert_eq!(
        (r(0x4e04_0400)[0], r(0x4e04_0400)[2]),
        (41, 2),
        "DUP imm5=4 -> element S(2)"
    );
    assert_eq!(
        (r(0x4e08_0400)[0], r(0x4e08_0400)[2]),
        (41, 3),
        "DUP imm5=8 -> element D(3), q=1"
    );
    assert_eq!(r(0x0e08_0400)[0], 0xE1, "DUP .D with q=0 -> Unallocated");
    assert_eq!(
        r(0x4e10_0400)[0],
        0xE1,
        "imm5=16 (128-bit element) -> Unallocated"
    );
    // tag 42 = NeonDupGeneral {q, element_size, rn, rd}.
    assert_eq!(
        (r(0x4e04_0c00)[0], r(0x4e04_0c00)[2]),
        (42, 2),
        "DUP general imm5=4 -> element S(2)"
    );
}

// ---- The ENCODE<->DECODE ROUND-TRIP: build words with the LINKED R2 encoders,
//      decode them in the JIT, assert every field is recovered (asymmetry = bug).

/// One round-trip case: the word an R2 encoder produced + the field row the
/// decoder must recover, with a label for attribution.
struct RtCase {
    word: u32,
    expect: [u32; 9],
    label: String,
}

fn roundtrip_cases() -> Vec<RtCase> {
    let mut v: Vec<RtCase> = Vec::new();
    let regs = [0u32, 1, 15, 30, 31];

    // 1. add/sub (shifted register) — encoder rejects shift==0b11 (reserved).
    for &sf in &[0u32, 1] {
        for &op in &[0u32, 1] {
            for &s in &[0u32, 1] {
                for &shift in &[0u32, 1, 2] {
                    for &imm6 in &[0u32, 1, 31, 63] {
                        let (rm, rn, rd) = (2u32, 1u32, 0u32);
                        let w = encode_add_sub_shifted_reg(sf, op, s, shift, rm, imm6, rn, rd);
                        v.push(RtCase {
                            word: w,
                            expect: [0, sf, op, s, shift, rm, imm6, rn, rd],
                            label: format!("add_sub_shifted_reg sf={sf} op={op} s={s} shift={shift} imm6={imm6}"),
                        });
                    }
                }
            }
        }
    }

    // 2. logical (shifted register).
    for &sf in &[0u32, 1] {
        for &opc in &[0u32, 1, 2, 3] {
            for &shift in &[0u32, 1, 2, 3] {
                for &n in &[0u32, 1] {
                    let (rm, imm6, rn, rd) = (7u32, 5u32, 6u32, 8u32);
                    let w = encode_logical_shifted_reg(sf, opc, shift, n, rm, imm6, rn, rd);
                    v.push(RtCase {
                        word: w,
                        expect: [1, sf, opc, shift, n, rm, imm6, rn, rd],
                        label: format!("logical_shifted_reg sf={sf} opc={opc} shift={shift} n={n}"),
                    });
                }
            }
        }
    }

    // 3. add/sub (immediate).
    for &sf in &[0u32, 1] {
        for &op in &[0u32, 1] {
            for &s in &[0u32, 1] {
                for &sh in &[0u32, 1] {
                    for &imm12 in &[0u32, 1, 2048, 4095] {
                        let (rn, rd) = (13u32, 14u32);
                        let w = encode_add_sub_imm(sf, op, s, sh, imm12, rn, rd);
                        v.push(RtCase {
                            word: w,
                            expect: [3, sf, op, s, sh, imm12, rn, rd, 0],
                            label: format!(
                                "add_sub_imm sf={sf} op={op} s={s} sh={sh} imm12={imm12}"
                            ),
                        });
                    }
                }
            }
        }
    }

    // 4. move-wide — encoder rejects opc==0b01 (unallocated); sweep {00,10,11}.
    for &sf in &[0u32, 1] {
        for &opc in &[0u32, 2, 3] {
            for &hw in &[0u32, 1, 2, 3] {
                if sf == 0 && hw >= 2 {
                    continue;
                }
                for &imm16 in &[0u32, 1, 0xABCD, 0xFFFF] {
                    let rd = 9u32;
                    let w = encode_move_wide(sf, opc, hw, imm16, rd);
                    v.push(RtCase {
                        word: w,
                        expect: [5, sf, opc, hw, imm16, rd, 0, 0, 0],
                        label: format!("move_wide sf={sf} opc={opc} hw={hw} imm16={imm16:#x}"),
                    });
                }
            }
        }
    }

    // 5. conditional branch (B.cond).
    for &cond in &[0u32, 1, 7, 14, 15] {
        for &imm19 in &[0u32, 1, 0x3FFFF, 0x7FFFF] {
            let w = encode_cond_branch(imm19, cond);
            v.push(RtCase {
                word: w,
                expect: [8, imm19, cond, 0, 0, 0, 0, 0, 0],
                label: format!("cond_branch imm19={imm19:#x} cond={cond}"),
            });
        }
    }

    // 6. unconditional branch (B/BL).
    for &op in &[0u32, 1] {
        for &imm26 in &[0u32, 1, 2, 0x01FF_FFFF, 0x03FF_FFFF] {
            let w = encode_uncond_branch(op, imm26);
            v.push(RtCase {
                word: w,
                expect: [9, op, imm26, 0, 0, 0, 0, 0, 0],
                label: format!("uncond_branch op={op} imm26={imm26:#x}"),
            });
        }
    }

    // 7. branch-register — encoder allows opc 0..=15; decoder accepts only 0..=2.
    for &opc in &[0u32, 1, 2] {
        for &rn in &regs {
            let w = encode_branch_reg(opc, rn);
            v.push(RtCase {
                word: w,
                expect: [10, opc, rn, 0, 0, 0, 0, 0, 0],
                label: format!("branch_reg opc={opc} rn={rn}"),
            });
        }
    }

    // 8. load/store register (unsigned immediate offset).
    for &size in &[0u32, 1, 2, 3] {
        for &vbit in &[0u32, 1] {
            for &opc in &[0u32, 1, 2, 3] {
                for &imm12 in &[0u32, 1, 2048, 4095] {
                    let (rn, rt) = (5u32, 6u32);
                    let w = encode_load_store_ui(size, vbit, opc, imm12, rn, rt);
                    v.push(RtCase {
                        word: w,
                        expect: [12, size, vbit, opc, imm12, rn, rt, 0, 0],
                        label: format!("ldst_ui size={size} v={vbit} opc={opc} imm12={imm12}"),
                    });
                }
            }
        }
    }

    // 9. load/store (unscaled, signed imm9) — the sign-extend round-trip.
    for &size in &[0u32, 1, 2, 3] {
        for &vbit in &[0u32, 1] {
            for &opc in &[0u32, 1] {
                for &imm9 in &[-256i32, -128, -1, 0, 1, 127, 255] {
                    let (rn, rt) = (5u32, 6u32);
                    let w = encode_load_store_unscaled(size, vbit, opc, imm9, rn, rt);
                    // decoder yields i16; packed as (imm9 as i16) as u32 (two's-comp).
                    let imm_bits = (imm9 as i16) as u32;
                    v.push(RtCase {
                        word: w,
                        expect: [13, size, vbit, opc, imm_bits, rn, rt, 0, 0],
                        label: format!("ldst_unscaled size={size} v={vbit} opc={opc} imm9={imm9}"),
                    });
                }
            }
        }
    }

    // 10. load/store pair (signed offset).
    for &opc in &[0u32, 1, 2] {
        for &vbit in &[0u32, 1] {
            for &l in &[0u32, 1] {
                if opc == 1 && vbit == 0 && l == 0 {
                    continue; // STGP tagged-memory semantics are not modeled.
                }
                for &imm7 in &[0u32, 1, 63, 127] {
                    let (rt2, rn, rt) = (3u32, 5u32, 7u32);
                    let w = encode_load_store_pair(opc, vbit, l, imm7, rt2, rn, rt);
                    // mode = SignedOffset -> discriminant 0.
                    v.push(RtCase {
                        word: w,
                        expect: [17, opc, vbit, l, 0, imm7, rt2, rn, rt],
                        label: format!("ldst_pair opc={opc} v={vbit} l={l} imm7={imm7}"),
                    });
                }
            }
        }
    }

    // 11. compare-and-branch (CBZ/CBNZ).
    for &sf in &[0u32, 1] {
        for &op in &[0u32, 1] {
            for &imm19 in &[0u32, 1, 0x3FFFF, 0x7FFFF] {
                let rt = 11u32;
                let w = encode_cmp_branch(sf, op, imm19, rt);
                v.push(RtCase {
                    word: w,
                    expect: [22, sf, op, imm19, rt, 0, 0, 0, 0],
                    label: format!("cmp_branch sf={sf} op={op} imm19={imm19:#x}"),
                });
            }
        }
    }

    v
}

/// The ENCODE<->DECODE ROUND-TRIP: the R2-verified production encoders build real
/// AArch64 words; the JIT decoder must recover EXACTLY the encoder's input fields.
/// This is the round's independent cross-check — an encoder/decoder asymmetry
/// (encode then decode not the identity on fields) is a real bug. native==JIT is
/// also asserted per case.
#[test]
fn trust_aa_decode_encode_roundtrip() {
    let cases = roundtrip_cases();
    let expected = cases.len();
    let words: Vec<u32> = cases.iter().map(|c| c.word).collect();
    let sweep = words.clone();
    let rows = run_watchdogged::<[u32; 9]>("aa_roundtrip", expected, move |tx| {
        let buffer = jit_module(DECODE_IR, "aa_roundtrip");
        let f: DecodeFn = unsafe { std::mem::transmute(bind(&buffer, "decode_root")) };
        for &w in &sweep {
            let mut out = poison_out();
            unsafe { f(w, &mut out) };
            if tx.send(as9(&out)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, c) in cases.iter().enumerate() {
        // (a) native==JIT.
        let native = native_decode_row(c.word);
        assert_eq!(
            rows[i], native,
            "roundtrip[{i}] {}: word={:#010x} JIT {:?} != native {:?}",
            c.label, c.word, rows[i], native
        );
        // (b) the round-trip identity: decode(encode(fields)) == fields.
        assert_eq!(
            rows[i], c.expect,
            "ENCODE<->DECODE ASYMMETRY at {}: word={:#010x} decoded {:?} != encoder input {:?}",
            c.label, c.word, rows[i], c.expect
        );
        assert_ne!(rows[i][0], 0xDEAD, "roundtrip row {i} still poisoned");
    }
}

/// ARMED negative control (Slice 1): patch the BRANCH-REGISTER dispatch pattern
/// (`const u32 107` = 0b1101011 -> 108), so the `bits(word,25,7)==0b1101011` guard
/// never fires. RET/BLR/BR (which `encode_branch_reg` produces and which the
/// decoder must classify as BranchReg) then fall through the dispatch tree to
/// Unsupported — a silent mis-decode of every register-branch. Prove divergence,
/// restore, re-pass.
#[test]
fn trust_aa_decode_armed_control() {
    const ANCHOR: &str = "const u32 107";
    assert_eq!(
        DECODE_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (branch-register dispatch pattern 0b1101011)"
    );
    let corrupted = DECODE_IR.replace(ANCHOR, "const u32 108");
    assert_ne!(corrupted, DECODE_IR);

    // RET = 0xd65f03c0 -> native BranchReg{opc=2, rn=30} (tag 10).
    let ret = 0xd65f_03c0u32;
    let corrupt = run_watchdogged::<[u32; 9]>("decode CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "decode CORRUPTED");
        let f: DecodeFn = unsafe { std::mem::transmute(bind(&buffer, "decode_root")) };
        let mut out = poison_out();
        unsafe { f(ret, &mut out) };
        let _ = tx.send(as9(&out));
    })[0];
    let pristine = run_watchdogged::<[u32; 9]>("decode RESTORED", 1, move |tx| {
        let buffer = jit_module(DECODE_IR, "decode RESTORED");
        let f: DecodeFn = unsafe { std::mem::transmute(bind(&buffer, "decode_root")) };
        let mut out = poison_out();
        unsafe { f(ret, &mut out) };
        let _ = tx.send(as9(&out));
    })[0];

    let native = native_decode_row(ret);
    assert_eq!(
        (native[0], native[1], native[2]),
        (10, 2, 30),
        "native: RET -> BranchReg opc=2 rn=30"
    );
    assert_eq!(
        corrupt[0], 0xE0,
        "corrupted module mis-decodes RET as Unsupported (dispatch guard dead)"
    );
    assert_ne!(corrupt[0], native[0], "corrupted JIT DIVERGES from native");
    assert_eq!(
        pristine, native,
        "pristine module AGREES (restore + re-pass)"
    );
}

// ============================================================================
// SLICE 2 — the logical-immediate bitmask DECODER gate
//   (disasm/aarch64.rs::logical_immediate_bitmask_is_allocated), the inverse-check
//   of the R1-verified `encode_logical_imm_fields`.
// ============================================================================

type LogimmGateFn = unsafe extern "C" fn(u32, u32) -> u32;

/// INDEPENDENT ORACLE: the ARM DDI 0487 `DecodeBitMasks` reserved-value gate,
/// reimplemented from the spec (HighestSetBit via an explicit scan — NOT the
/// production `leading_zeros` path), so it is a genuinely independent check of the
/// decoder's allocation predicate.
fn decode_bitmasks_allocated_oracle(n: bool, imms: u8) -> bool {
    let field: u8 = ((n as u8) << 6) | (!imms & 0x3f); // 7-bit N:NOT(imms)
    // HighestSetBit(field) over bits 6..0, or -1 if field == 0.
    let mut len: i32 = -1;
    let mut k: i32 = 6;
    while k >= 0 {
        if field & (1u8 << (k as u8)) != 0 {
            len = k;
            break;
        }
        k -= 1;
    }
    if len < 1 {
        return false; // field==0 (len=-1) or esize=1 degenerate (len=0): reserved
    }
    let levels: u8 = ((1u16 << len) - 1) as u8;
    (imms & levels) != levels
}

/// The logical-immediate bitmask decoder gate, EXHAUSTIVE over the full (N,imms)
/// domain (all 2*64 = 128 combinations — the reserved-value space the ARM
/// `DecodeBitMasks` gate decides), JIT == native transcription == the independent
/// spec oracle. Covers the REJECT direction (reserved patterns -> false) as a
/// decoder must.
#[test]
fn trust_aa_logimm_gate_exhaustive() {
    // Full (n, imms) product.
    let mut inputs: Vec<(u32, u32)> = Vec::new();
    for n in 0..2u32 {
        for imms in 0..64u32 {
            inputs.push((n, imms));
        }
    }
    let expected = inputs.len();
    let sweep = inputs.clone();
    let rows = run_watchdogged::<u32>("logimm_gate", expected, move |tx| {
        let buffer = jit_module(LOGIMM_GATE_IR, "logimm_gate");
        let f: LogimmGateFn = unsafe { std::mem::transmute(bind(&buffer, "logimm_gate_root")) };
        for &(n, imms) in &sweep {
            let got = unsafe { f(n, imms) };
            if tx.send(got).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut n_alloc = 0u32;
    let mut n_reject = 0u32;
    for (i, &(n, imms)) in inputs.iter().enumerate() {
        let native = lg::logimm_gate_root(n, imms);
        let oracle = decode_bitmasks_allocated_oracle(n != 0, imms as u8) as u32;
        assert_eq!(
            rows[i], native,
            "logimm_gate(n={n},imms={imms}): JIT {} != native {}",
            rows[i], native
        );
        assert_eq!(
            rows[i], oracle,
            "logimm_gate(n={n},imms={imms}): JIT {} != independent DecodeBitMasks oracle {}",
            rows[i], oracle
        );
        if rows[i] == 1 {
            n_alloc += 1;
        } else {
            n_reject += 1;
        }
    }
    // Both directions must be non-trivially exercised.
    assert!(
        n_alloc > 0 && n_reject > 0,
        "sweep must hit both allocated and reserved verdicts"
    );

    // ---- Independent spot-checks. ----
    // n=1, imms=0: N:NOT(imms)=1000000 -> len=6 (esize=64), levels=63, imms&63=0!=63 -> allocated.
    assert_eq!(
        rows[inputs.iter().position(|&x| x == (1, 0)).unwrap()],
        1,
        "N=1 imms=0 -> allocated"
    );
    // n=0, imms=0x3e (0b111110): NOT&0x3f=1 -> field=1 -> len=0 -> reserved.
    assert_eq!(
        rows[inputs.iter().position(|&x| x == (0, 0x3e)).unwrap()],
        0,
        "N=0 imms=0x3e -> len<1 reserved"
    );
    // n=0, imms=0x3f: NOT&0x3f=0, field=0 -> reserved (pattern==0).
    assert_eq!(
        rows[inputs.iter().position(|&x| x == (0, 0x3f)).unwrap()],
        0,
        "N=0 imms=0x3f -> pattern==0 reserved"
    );
    // n=0, imms=0x1f (esize=32, S=all-ones-for-esize) -> reserved (imms&levels==levels).
    assert_eq!(
        rows[inputs.iter().position(|&x| x == (0, 0x1f)).unwrap()],
        0,
        "N=0 imms=0x1f -> all-ones esize reserved"
    );
    // n=0, imms=0: field=0b0111111 -> len=6? NOT: N=0 so bit6=0; NOT(0)&0x3f=0x3f -> field=0x3f -> len=5 (esize=32), levels=31, imms&31=0 -> allocated.
    assert_eq!(
        rows[inputs.iter().position(|&x| x == (0, 0)).unwrap()],
        1,
        "N=0 imms=0 -> allocated (esize 32, 1 one)"
    );
}

/// ARMED negative control (Slice 2): patch the bitmask field mask (`const u8 63`
/// = 0x3f -> 31 = 0x1f) in `!imms & 0x3f`, so the reserved-value gate mis-computes
/// the N:NOT(imms) pattern length. Allocation verdicts then flip for the inputs
/// whose top NOT(imms) bit is dropped — a decoder that would ACCEPT unallocated
/// bitmask encodings (or reject valid ones). Prove divergence, restore, re-pass.
#[test]
fn trust_aa_logimm_gate_armed_control() {
    const ANCHOR: &str = "const u8 63";
    assert_eq!(
        LOGIMM_GATE_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (bitmask field mask 0x3f)"
    );
    let corrupted = LOGIMM_GATE_IR.replace(ANCHOR, "const u8 31");
    assert_ne!(corrupted, LOGIMM_GATE_IR);

    // Find an input whose verdict the mask-narrowing flips, by scanning natively.
    let mut flipped: Option<(u32, u32)> = None;
    for n in 0..2u32 {
        for imms in 0..64u32 {
            let good = lg::logimm_gate_root(n, imms);
            // emulate the corrupted mask (0x3f -> 0x1f) natively for target selection
            let bad = {
                let field: u8 = ((n as u8) << 6) | ((!(imms as u8)) & 0x1f);
                if field == 0 {
                    0
                } else {
                    let len = 7 - field.leading_zeros() as u8;
                    if len < 1 {
                        0
                    } else {
                        let levels = (1u8 << len) - 1;
                        ((imms as u8) & levels != levels) as u32
                    }
                }
            };
            if good != bad {
                flipped = Some((n, imms));
                break;
            }
        }
        if flipped.is_some() {
            break;
        }
    }
    let (n, imms) = flipped.expect("mask narrowing must flip at least one verdict");
    let good_native = lg::logimm_gate_root(n, imms);

    let corrupt = run_watchdogged::<u32>("logimm CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "logimm CORRUPTED");
        let f: LogimmGateFn = unsafe { std::mem::transmute(bind(&buffer, "logimm_gate_root")) };
        let _ = tx.send(unsafe { f(n, imms) });
    })[0];
    let pristine = run_watchdogged::<u32>("logimm RESTORED", 1, move |tx| {
        let buffer = jit_module(LOGIMM_GATE_IR, "logimm RESTORED");
        let f: LogimmGateFn = unsafe { std::mem::transmute(bind(&buffer, "logimm_gate_root")) };
        let _ = tx.send(unsafe { f(n, imms) });
    })[0];

    assert_ne!(
        corrupt, good_native,
        "corrupted JIT (n={n},imms={imms}) DIVERGES from native gate"
    );
    assert_eq!(
        pristine, good_native,
        "pristine module AGREES (restore + re-pass)"
    );
    // The independent oracle sides with native, not the corruption.
    assert_eq!(
        good_native,
        decode_bitmasks_allocated_oracle(n != 0, imms as u8) as u32,
        "native gate agrees with the independent DecodeBitMasks oracle"
    );
}
