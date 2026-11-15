// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Decoded-word value obligations for emitted AArch64 register copies,
//! scalar value instructions (X-OPCODES-P8/P9), the half-precision FCVT
//! conversions (X-OPCODES-P7), and the `CSET` alias.
//!
//! The `CSET` family is a second lane in the same style with its own forms,
//! producer, controls and registration — see the "CSET" section at the end of
//! this file. It reads its decode from [`crate::aarch64_csel_semantics`] rather
//! than from [`decode_a64_value_word`], is registered under
//! `ProofCategory::Comparison` by its own `all_a64_cset_value_decode_proofs`,
//! and is deliberately ABSENT from [`a64_value_forms`], so it never covers the
//! opcode-level coverage-gate row for `CSet` (that row is covered only through
//! the NZCV producer/consumer family) and ENC-5 keeps its own structural
//! verdict for that opcode.
//!
//! Every obligation here states, for one emitted instruction FORM, that the
//! architectural effect of the instruction WORD the encoder emits equals what
//! the machine-IR instruction claims:
//!
//! * the word is read by an independent decoder written from the Arm A64
//!   encoding diagrams (Arm ARM DDI 0487, C4.1 encoding index and the C6/C7
//!   instruction pages), never by inverting `trust-cg-codegen`'s encoder;
//! * the decoded fields get their Arm ARM pseudo-code semantics over a
//!   symbolic machine state: the complete 64-bit destination register for a
//!   general-purpose write, so the zeroing of bits 63:32 by a W write is part
//!   of the claim, and the complete 128-bit vector register for an FP write;
//! * the machine-IR intent is stated independently, from the operands'
//!   register classes and numbers and the immediates.
//!
//! Evidence strength is stated per decision.
//!
//! * Pure bit-routing forms (register copies, FMOV, RBIT, BFM with concrete
//!   fields, MRS) are decided EXACTLY by [`exact_routing`]: each side reduces to
//!   a per-bit map (a constant or a named input bit) and the maps are compared,
//!   which settles equality for every register value. This is an in-process
//!   decision procedure, not an independently checked certificate.
//! * Arithmetic forms (SMULL, `ADD #imm12, LSL #12`) and the symbolic-field BFM
//!   obligation are registered `ProofObligation`s discharged by the ordinary
//!   evaluator: sampled `Statistical(N)` acceptance by default, which is
//!   regression evidence, not proof.
//! * The four half-precision FCVT forms compare the Arm ARM `FPConvert`
//!   transcription of the decoded word with an independently written IEEE 754
//!   `convertFormat` intent ([`crate::aarch64_fcvt_half`]), bit for bit over
//!   the whole destination register. Each obligation's only input is the
//!   source scalar: the binary16-source (widening) forms are evaluated
//!   EXHAUSTIVELY over all 65,536 inputs; the binary32/binary64-source
//!   (narrowing) forms are first checked on a structured battery of exact
//!   values, ties and near-ties across every binade, overflow, underflow and
//!   NaN payloads, then sampled — testing evidence, not proof. Both sides
//!   assume the default FPCR (RNE, FZ=0, DN=0, AHP=0); nothing proves the
//!   FPCR value at run time.
//!
//! The coverage gate cannot run the encoder (trust-cg-codegen depends on this
//! crate), so it credits words CAPTURED from it ([`CAPTURED_A64_VALUE_WORDS`]);
//! `coverage_gate_tests` and `tests/aarch64_value_decode_gate.rs` re-derive
//! every captured word from the live encoder. Per compile, the AArch64 decode
//! check (ENC-5, `trust-cg-codegen/src/aarch64/decode_check.rs`) runs
//! [`check_emitted_a64_value_word`] on every emitted instance of these opcodes,
//! and the function verifier binds every instance whose operands name a form
//! to that form's registered obligation ([`a64_value_bound_form`]); an
//! instance of another shape stays unverified. The register copies include
//! the typed `MOVWrr`/`MOVXrr` that post-allocation copy lowering emits, whose
//! width the opcode (not the operand view) fixes.
//!
//! What this does NOT establish: that the lowering chose the right registers,
//! widths or immediates (a wrong choice encodes and decodes perfectly); any
//! dataflow, liveness or ABI property, including whether the upper half of a
//! W-class source is defined when an X-width copy reads it; that TPIDR_EL0
//! holds the thread pointer (the AArch64 ELF TLS ABI, trust base); FEAT_FP16
//! availability for half-precision FMOV words; the FPCR mode a half-precision
//! FCVT runs under; or agreement with silicon. The
//! Arm ARM rules are transcribed; the native differential in trust-cg-codegen
//! samples them on the host CPU.

use crate::aarch64_csel_semantics::{DecodedConditionalSelect, SymbolicRegisterState};
use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    verify_by_evaluation_with_config,
};
use crate::proof_database::ProofCategory;
use crate::smt::SmtExpr;
use crate::verify::VerificationResult;
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, PReg, RegClass, SpecialReg, VReg};
use trust_cg_lower::isel::AArch64CC;

#[path = "aarch64_value_decode_scalar.rs"]
mod scalar;

#[path = "aarch64_value_decode_flags.rs"]
mod flags;

#[path = "aarch64_value_decode_compact.rs"]
mod compact;

pub use compact::denote_a64_value_word_compact;
pub use flags::denote_a64_value_flags;
pub(crate) use scalar::{decode_logical_imm, move_wide_fields};

// ===========================================================================
// Independent A64 decoder
// ===========================================================================

/// Instruction classes the value decoder models, with raw fields named after
/// the Arm ARM encoding diagrams.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64ValueWord {
    /// Logical (immediate): `sf opc 100100 N immr imms Rn Rd`.
    LogicalImmediate {
        sf: u32,
        opc: u32,
        n: u32,
        immr: u32,
        imms: u32,
        rn: u32,
        rd: u32,
    },
    /// Move wide: `sf opc 100101 hw imm16 Rd`.
    MoveWide {
        sf: u32,
        opc: u32,
        hw: u32,
        imm16: u32,
        rd: u32,
    },
    /// Add/subtract (shifted register): `sf op S 01011 shift 0 Rm imm6 Rn Rd`.
    AddSubShiftedReg {
        sf: u32,
        op: u32,
        s: u32,
        shift: u32,
        rm: u32,
        imm6: u32,
        rn: u32,
        rd: u32,
    },
    /// Logical (shifted register): `sf opc 01010 shift N Rm imm6 Rn Rd`.
    LogicalShiftedReg {
        sf: u32,
        opc: u32,
        shift: u32,
        n: u32,
        rm: u32,
        imm6: u32,
        rn: u32,
        rd: u32,
    },
    /// Add/subtract (immediate): `sf op S 100010 sh imm12 Rn Rd`.
    AddSubImm {
        sf: u32,
        op: u32,
        s: u32,
        sh: u32,
        imm12: u32,
        rn: u32,
        rd: u32,
    },
    /// Floating-point data-processing (1 source):
    /// `0 0 0 11110 ftype 1 opcode(6) 10000 Rn Rd`.
    FpDp1 {
        ftype: u32,
        opcode: u32,
        rn: u32,
        rd: u32,
    },
    /// FMOV (general), the move rows of "conversion between floating-point
    /// and integer": `sf 0 0 11110 ftype 1 rmode 11x 000000 Rn Rd`.
    FpIntMove {
        sf: u32,
        ftype: u32,
        rmode: u32,
        /// `true` for opcode 110 (FP to general register), `false` for 111.
        to_general: bool,
        rn: u32,
        rd: u32,
    },
    /// Data-processing (3 source): `sf op54 11011 op31 Rm o0 Ra Rn Rd`.
    Dp3 {
        sf: u32,
        op54: u32,
        op31: u32,
        rm: u32,
        o0: u32,
        ra: u32,
        rn: u32,
        rd: u32,
    },
    /// Bitfield: `sf opc 100110 N immr imms Rn Rd`.
    Bitfield {
        sf: u32,
        opc: u32,
        n: u32,
        immr: u32,
        imms: u32,
        rn: u32,
        rd: u32,
    },
    /// Data-processing (1 source), opcode2 = 00000:
    /// `sf 1 0 11010110 00000 opcode(6) Rn Rd`.
    Dp1 {
        sf: u32,
        opcode: u32,
        rn: u32,
        rd: u32,
    },
    /// Advanced SIMD three same, logical opcode 00011:
    /// `0 Q U 01110 size 1 Rm 00011 1 Rn Rd` (AND, BIC, ORR, ORN; EOR, BSL,
    /// BIT, BIF).
    SimdLogical {
        q: u32,
        u: u32,
        size: u32,
        rm: u32,
        rn: u32,
        rd: u32,
    },
    /// System register move: `1101010100 L 1 o0 op1 CRn CRm op2 Rt`.
    SysRegMove {
        /// 1 = MRS (read), 0 = MSR (register) (write).
        l: u32,
        op0: u32,
        op1: u32,
        crn: u32,
        crm: u32,
        op2: u32,
        rt: u32,
    },
}

/// Why the independent decoder refused a word.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum A64DecodeRefusal {
    /// The word is in no instruction class this decoder models.
    NotModeled { word: u32 },
    /// The word lies in a modeled class but is UNALLOCATED or RESERVED there.
    Unallocated { word: u32, reason: &'static str },
}

impl std::fmt::Display for A64DecodeRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotModeled { word } => write!(f, "{word:#010x} is outside the modeled classes"),
            Self::Unallocated { word, reason } => {
                write!(f, "{word:#010x} is unallocated: {reason}")
            }
        }
    }
}

/// Bits `hi:lo` (inclusive) of `word`.
const fn field(word: u32, hi: u32, lo: u32) -> u32 {
    (word >> lo) & (u32::MAX >> (31 - (hi - lo)))
}

/// Decode one A64 instruction word into a modeled class.
///
/// Field positions and the unallocated rows come from the Arm ARM encoding
/// diagrams. Class selection tests every fixed bit of the class, so a word of
/// a neighbouring class never decodes as a modeled one.
pub fn decode_a64_value_word(w: u32) -> Result<A64ValueWord, A64DecodeRefusal> {
    let unallocated = |reason| Err(A64DecodeRefusal::Unallocated { word: w, reason });

    if let Some(decoded) = scalar::decode(w) {
        return decoded;
    }

    // Data processing -- immediate: Add/subtract (immediate), bits 28:23.
    if field(w, 28, 23) == 0b100010 {
        return Ok(A64ValueWord::AddSubImm {
            sf: field(w, 31, 31),
            op: field(w, 30, 30),
            s: field(w, 29, 29),
            sh: field(w, 22, 22),
            imm12: field(w, 21, 10),
            rn: field(w, 9, 5),
            rd: field(w, 4, 0),
        });
    }
    // Data processing -- immediate: Bitfield.
    if field(w, 28, 23) == 0b100110 {
        let (sf, opc, n) = (field(w, 31, 31), field(w, 30, 29), field(w, 22, 22));
        let (immr, imms) = (field(w, 21, 16), field(w, 15, 10));
        if opc == 0b11 {
            return unallocated("bitfield opc == 11");
        }
        if sf != n {
            return unallocated("bitfield N must equal sf");
        }
        if sf == 0 && (immr >> 5 != 0 || imms >> 5 != 0) {
            return unallocated("32-bit bitfield with immr<5> or imms<5> set");
        }
        return Ok(A64ValueWord::Bitfield {
            sf,
            opc,
            n,
            immr,
            imms,
            rn: field(w, 9, 5),
            rd: field(w, 4, 0),
        });
    }
    // Data processing -- register: Logical (shifted register), bits 28:24.
    if field(w, 28, 24) == 0b01010 {
        let (sf, imm6) = (field(w, 31, 31), field(w, 15, 10));
        if sf == 0 && imm6 >> 5 != 0 {
            return unallocated("32-bit logical shift amount above 31");
        }
        return Ok(A64ValueWord::LogicalShiftedReg {
            sf,
            opc: field(w, 30, 29),
            shift: field(w, 23, 22),
            n: field(w, 21, 21),
            rm: field(w, 20, 16),
            imm6,
            rn: field(w, 9, 5),
            rd: field(w, 4, 0),
        });
    }
    // Data processing -- register: Data-processing (3 source), bits 28:24.
    if field(w, 28, 24) == 0b11011 {
        let (sf, op54, op31, o0) = (
            field(w, 31, 31),
            field(w, 30, 29),
            field(w, 23, 21),
            field(w, 15, 15),
        );
        let allocated = op54 == 0
            && match op31 {
                0b000 => true,
                0b001 | 0b101 => sf == 1,
                0b010 | 0b110 => sf == 1 && o0 == 0,
                _ => false,
            };
        if !allocated {
            return unallocated("data-processing (3 source) row is unallocated");
        }
        return Ok(A64ValueWord::Dp3 {
            sf,
            op54,
            op31,
            rm: field(w, 20, 16),
            o0,
            ra: field(w, 14, 10),
            rn: field(w, 9, 5),
            rd: field(w, 4, 0),
        });
    }
    // Data processing -- register: Data-processing (1 source).
    if field(w, 30, 30) == 1 && field(w, 28, 21) == 0b1101_0110 {
        let (sf, s, opcode2, opcode) = (
            field(w, 31, 31),
            field(w, 29, 29),
            field(w, 20, 16),
            field(w, 15, 10),
        );
        if s != 0 || opcode2 != 0 || opcode > 0b000101 {
            return Err(A64DecodeRefusal::NotModeled { word: w });
        }
        if opcode == 0b000011 && sf == 0 {
            return unallocated("64-bit REV with sf == 0");
        }
        return Ok(A64ValueWord::Dp1 {
            sf,
            opcode,
            rn: field(w, 9, 5),
            rd: field(w, 4, 0),
        });
    }
    // Scalar floating point: bit 30 == 0, bits 28:24 == 11110, bit 21 == 1.
    if field(w, 30, 30) == 0 && field(w, 28, 24) == 0b11110 && field(w, 21, 21) == 1 {
        let (top, s, ftype) = (field(w, 31, 31), field(w, 29, 29), field(w, 23, 22));
        // FP data-processing (1 source): bits 14:10 == 10000.
        if field(w, 14, 10) == 0b10000 {
            if top != 0 || s != 0 {
                return unallocated("FP data-processing (1 source) with M or S set");
            }
            if ftype == 0b10 {
                return unallocated("FP data-processing (1 source) with ftype == 10");
            }
            // FCVT (between precisions): opcode 0001:opc, opc naming the
            // destination precision like ftype names the source's.
            let opcode = field(w, 20, 15);
            if opcode >> 2 == 0b0001 {
                let opc = opcode & 0b11;
                if opc == 0b10 {
                    if ftype == 0b01 {
                        // BFCVT (FEAT_BF16): a bfloat16 narrowing, not FCVT.
                        return Err(A64DecodeRefusal::NotModeled { word: w });
                    }
                    return unallocated("FCVT with opc == 10");
                }
                if opc == ftype {
                    return unallocated("FCVT to the operand's own precision");
                }
            }
            return Ok(A64ValueWord::FpDp1 {
                ftype,
                opcode: field(w, 20, 15),
                rn: field(w, 9, 5),
                rd: field(w, 4, 0),
            });
        }
        // Conversion between floating-point and integer: bits 15:10 == 0.
        if field(w, 15, 10) == 0 {
            let (rmode, opcode) = (field(w, 20, 19), field(w, 18, 16));
            if opcode >> 1 != 0b11 {
                // SCVTF/UCVTF/FCVT*: allocated conversions, not moves.
                return Err(A64DecodeRefusal::NotModeled { word: w });
            }
            if s != 0 {
                return unallocated("FMOV (general) with S set");
            }
            let allocated = matches!(
                (top, ftype, rmode),
                (0, 0b00, 0b00) | (1, 0b01, 0b00) | (_, 0b11, 0b00) | (1, 0b10, 0b01)
            );
            if !allocated {
                return unallocated(
                    "FMOV (general) register widths do not match: no FMOV moves between \
                     these integer and floating-point sizes",
                );
            }
            return Ok(A64ValueWord::FpIntMove {
                sf: top,
                ftype,
                rmode,
                to_general: opcode == 0b110,
                rn: field(w, 9, 5),
                rd: field(w, 4, 0),
            });
        }
    }
    // Data processing -- SIMD: Advanced SIMD three same, logical (opcode
    // 00011): bit 31 = 0, bits 28:24 = 01110, bit 21 = 1, bits 15:10 = 000111.
    if w & 0x9F20_FC00 == 0x0E20_1C00 {
        return Ok(A64ValueWord::SimdLogical {
            q: field(w, 30, 30),
            u: field(w, 29, 29),
            size: field(w, 23, 22),
            rm: field(w, 20, 16),
            rn: field(w, 9, 5),
            rd: field(w, 4, 0),
        });
    }
    // Branches, exception generating and system: system register move.
    if field(w, 31, 22) == 0b11_0101_0100 && field(w, 20, 20) == 1 {
        return Ok(A64ValueWord::SysRegMove {
            l: field(w, 21, 21),
            op0: 2 + field(w, 19, 19),
            op1: field(w, 18, 16),
            crn: field(w, 15, 12),
            crm: field(w, 11, 8),
            op2: field(w, 7, 5),
            rt: field(w, 4, 0),
        });
    }
    Err(A64DecodeRefusal::NotModeled { word: w })
}

// ===========================================================================
// Symbolic machine state and Arm ARM pseudo-code semantics
// ===========================================================================

/// The architectural register a decoded instruction writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum A64Dest {
    /// General-purpose register `X<n>` (n < 31); the value is all 64 bits.
    Gpr(u8),
    /// The stack pointer; the value is all 64 bits.
    Sp,
    /// Vector register `V<n>`; the value is all 128 bits.
    Fpr(u8),
    /// The zero register: the write is discarded.
    Discarded,
    /// A system register, named by its 16-bit `o0:op1:CRn:CRm:op2` key.
    SystemRegister(u16),
}

/// The architectural effect of one decoded instruction.
#[derive(Debug, Clone, PartialEq)]
pub struct A64Effect {
    pub dest: A64Dest,
    /// 64-bit for a general-purpose, SP or discarded write; 128-bit for `V<n>`.
    pub value: SmtExpr,
    /// Whether the instruction writes NZCV.
    pub writes_nzcv: bool,
}

/// Immediate fields an obligation quantifies over instead of taking the
/// word's concrete field value.
#[derive(Debug, Clone, Default)]
pub struct FieldOverrides {
    /// 12-bit `imm12` of Add/subtract (immediate).
    pub imm12: Option<SmtExpr>,
    /// 6-bit `immr` of Bitfield.
    pub immr: Option<SmtExpr>,
    /// 6-bit `imms` of Bitfield.
    pub imms: Option<SmtExpr>,
    /// The scalar source operand of a half-precision FCVT, standing for the
    /// low `bits` of `V<rn>` when the word reads that register at that width.
    pub fp_source: Option<FpSourceOverride>,
}

/// A symbolic scalar standing for the low `bits` of `V<rn>`.
#[derive(Debug, Clone)]
pub struct FpSourceOverride {
    pub rn: u32,
    pub bits: u32,
    pub value: SmtExpr,
}

/// Why a decoded word has no modeled semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum A64DenoteRefusal {
    /// Decoded, but outside the modeled instructions of its class.
    UnmodeledInstruction(&'static str),
    /// MRS/MSR of a system register absent from [`MODELED_SYSTEM_REGISTERS`].
    UnmodeledSystemRegister(u16),
}

impl std::fmt::Display for A64DenoteRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnmodeledInstruction(what) => write!(f, "unmodeled instruction: {what}"),
            Self::UnmodeledSystemRegister(key) => {
                write!(f, "unmodeled system register key {key:#06x}")
            }
        }
    }
}

/// `X<n>` as a 64-bit state variable.
fn xvar(n: u32) -> SmtExpr {
    // The spelled names, so a decode does not run the formatter per operand.
    const NAMES: [&str; 32] = [
        "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13",
        "x14", "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26",
        "x27", "x28", "x29", "x30", "x31",
    ];
    match NAMES.get(n as usize) {
        Some(name) => SmtExpr::var(*name, 64),
        None => SmtExpr::var(format!("x{n}"), 64),
    }
}

fn spvar() -> SmtExpr {
    SmtExpr::var("sp", 64)
}

fn vlo(n: u32) -> SmtExpr {
    SmtExpr::var(format!("v{n}_lo"), 64)
}

/// The low `bits` of `expr`.
fn low(expr: SmtExpr, bits: u32) -> SmtExpr {
    if expr.bv_width() == bits {
        expr
    } else {
        expr.extract(bits - 1, 0)
    }
}

/// `expr` zero-extended to `to` bits.
fn zext(expr: SmtExpr, to: u32) -> SmtExpr {
    let width = expr.bv_width();
    if width == to {
        expr
    } else {
        expr.zero_ext(to - width)
    }
}

/// A scalar of at most 64 bits placed in a 128-bit vector register with the
/// upper bits zero (`V[d] = ZeroExtend(value, 128)`).
fn v128_from_scalar(expr: SmtExpr) -> SmtExpr {
    SmtExpr::bv_const(0, 64).concat(zext(expr, 64))
}

fn all_ones(width: u32) -> SmtExpr {
    SmtExpr::bv_const(u64::MAX, width)
}

/// `X[n, datasize]` in a context where register 31 is the zero register.
fn read_gpr_zr(n: u32, datasize: u32) -> SmtExpr {
    if n == 31 {
        SmtExpr::bv_const(0, datasize)
    } else {
        low(xvar(n), datasize)
    }
}

/// `X[n, datasize]` in a context where register 31 is the stack pointer.
fn read_gpr_sp(n: u32, datasize: u32) -> SmtExpr {
    if n == 31 {
        low(spvar(), datasize)
    } else {
        low(xvar(n), datasize)
    }
}

fn gpr_dest_zr(d: u32) -> A64Dest {
    if d == 31 {
        A64Dest::Discarded
    } else {
        A64Dest::Gpr(d as u8)
    }
}

fn bv(value: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(value, width)
}

/// `ROR(x, r)` for a concrete `r` in `0..datasize`.
fn ror_const(x: SmtExpr, r: u32, datasize: u32) -> SmtExpr {
    x.clone()
        .bvlshr(bv(u64::from(r), datasize))
        .bvor(x.bvshl(bv(u64::from(datasize - r), datasize)))
}

/// `ShiftReg(x, shift_type, amount)` for a concrete amount.
fn shift_reg(x: SmtExpr, shift_type: u32, amount: u32, datasize: u32) -> SmtExpr {
    let amount_bv = bv(u64::from(amount), datasize);
    match shift_type {
        0b00 => x.bvshl(amount_bv),
        0b01 => x.bvlshr(amount_bv),
        0b10 => x.bvashr(amount_bv),
        _ => ror_const(x, amount, datasize),
    }
}

/// The modeled system-register file: name, and 16-bit `1:o0:op1:CRn:CRm:op2`
/// key as the MRS/MSR `systemreg` field (bit 15 is `op0<1>`, always 1).
pub const MODELED_SYSTEM_REGISTERS: &[(&str, u16)] = &[
    ("tpidr_el0", sysreg_key(3, 3, 13, 0, 2)),
    ("tpidrro_el0", sysreg_key(3, 3, 13, 0, 3)),
    ("tpidr_el1", sysreg_key(3, 0, 13, 0, 4)),
    ("nzcv", sysreg_key(3, 3, 4, 2, 0)),
    ("fpcr", sysreg_key(3, 3, 4, 4, 0)),
    ("fpsr", sysreg_key(3, 3, 4, 4, 1)),
    ("cntvct_el0", sysreg_key(3, 3, 14, 0, 2)),
];

/// The TPIDR_EL0 key: op0=3, op1=3, CRn=13, CRm=0, op2=2.
pub const TPIDR_EL0_KEY: u16 = sysreg_key(3, 3, 13, 0, 2);

/// Pack a system-register name tuple into its 16-bit instruction field.
pub const fn sysreg_key(op0: u16, op1: u16, crn: u16, crm: u16, op2: u16) -> u16 {
    (1 << 15) | ((op0 & 1) << 14) | (op1 << 11) | (crn << 7) | (crm << 3) | op2
}

/// `SysReg[key]` over the modeled file, as an SMT selection on the decoded
/// key: the value is the register the key names, through a real selection,
/// so a word naming a neighbouring register yields that register's value.
fn system_register_read(key: u16) -> Result<SmtExpr, A64DenoteRefusal> {
    if !MODELED_SYSTEM_REGISTERS
        .iter()
        .any(|&(_, entry)| entry == key)
    {
        return Err(A64DenoteRefusal::UnmodeledSystemRegister(key));
    }
    let decoded = bv(u64::from(key), 16);
    Ok(MODELED_SYSTEM_REGISTERS.iter().rev().fold(
        SmtExpr::var("sysreg_unmodeled", 64),
        |otherwise, &(name, entry)| {
            SmtExpr::ite(
                decoded.clone().eq_expr(bv(u64::from(entry), 16)),
                SmtExpr::var(name, 64),
                otherwise,
            )
        },
    ))
}

/// `DecodeBitMasks(N, imms, immr, FALSE)` for a bitfield of `datasize` bits
/// whose `N == sf` (the decoder rejects every other bitfield row), so the
/// element size equals the register size and no replication occurs.
///
/// Returns `(wmask, tmask, R, S)` as `datasize`-bit SMT terms. Concrete fields
/// produce constants; overridden fields produce the same pseudo-code over
/// symbolic terms (shifts by symbolic amounts, with the SMT rule that a shift
/// by at least the width yields zero doing the work of `Ones(datasize)`).
fn decode_bit_masks(
    immr: &Field,
    imms: &Field,
    datasize: u32,
) -> (SmtExpr, SmtExpr, SmtExpr, SmtExpr) {
    let levels = u64::from(datasize - 1);
    if let (Field::Concrete(immr), Field::Concrete(imms)) = (immr, imms) {
        let s = u64::from(*imms) & levels;
        let r = u64::from(*immr) & levels;
        let d = s.wrapping_sub(r) & levels;
        let ones = |count: u64| -> u64 {
            if count >= 64 {
                u64::MAX
            } else {
                (1u64 << count) - 1
            }
        };
        let width_mask = ones(u64::from(datasize));
        let welem = ones(s + 1);
        let wmask = if r == 0 {
            welem
        } else {
            ((welem >> r) | (welem << (u64::from(datasize) - r))) & width_mask
        };
        let tmask = ones(d + 1);
        return (
            bv(wmask, datasize),
            bv(tmask, datasize),
            bv(r, datasize),
            bv(s, datasize),
        );
    }
    let term = |f: &Field| zext(f.term(6), datasize).bvand(bv(levels, datasize));
    let (r, s) = (term(immr), term(imms));
    let one = bv(1, datasize);
    let ones = |count: SmtExpr| one.clone().bvshl(count).bvsub(one.clone());
    let d = s.clone().bvsub(r.clone()).bvand(bv(levels, datasize));
    let welem = ones(s.clone().bvadd(one.clone()));
    let wmask = welem
        .clone()
        .bvlshr(r.clone())
        .bvor(welem.bvshl(bv(u64::from(datasize), datasize).bvsub(r.clone())));
    let tmask = ones(d.bvadd(one.clone()));
    (wmask, tmask, r, s)
}

/// A decoded immediate field: the word's value, or a quantified term.
#[derive(Debug, Clone)]
enum Field {
    Concrete(u32),
    Symbolic(SmtExpr),
}

impl Field {
    fn pick(concrete: u32, symbolic: &Option<SmtExpr>) -> Self {
        match symbolic {
            Some(term) => Self::Symbolic(term.clone()),
            None => Self::Concrete(concrete),
        }
    }

    fn term(&self, width: u32) -> SmtExpr {
        match self {
            Self::Concrete(value) => bv(u64::from(*value), width),
            Self::Symbolic(term) => term.clone(),
        }
    }
}

/// Shared decoded ADD/SUB-immediate value step. Callers choose the source
/// state explicitly; the public generic denotation keeps its canonical names.
/// This preserves the same immediate, width and destination semantics.
pub(crate) fn denote_add_sub_immediate_from_operand(
    word: &A64ValueWord,
    fields: &FieldOverrides,
    operand1: SmtExpr,
) -> Result<A64Effect, A64DenoteRefusal> {
    let A64ValueWord::AddSubImm {
        sf,
        op,
        s,
        sh,
        imm12,
        rd,
        ..
    } = *word
    else {
        return Err(A64DenoteRefusal::UnmodeledInstruction(
            "not ADD/SUB immediate",
        ));
    };
    let datasize = 32 << sf;
    let mut imm = zext(Field::pick(imm12, &fields.imm12).term(12), datasize);
    if sh == 1 {
        imm = imm.bvshl(bv(12, datasize));
    }
    // AddWithCarry(op1, NOT(imm), 1) is op1 - imm modulo 2^datasize.
    let result = if op == 0 {
        operand1.bvadd(imm)
    } else {
        operand1.bvsub(imm)
    };
    let dest = match (rd, s) {
        (31, 0) => A64Dest::Sp,
        (31, _) => A64Dest::Discarded,
        (d, _) => A64Dest::Gpr(d as u8),
    };
    Ok(A64Effect {
        dest,
        value: zext(result, 64),
        writes_nzcv: s == 1,
    })
}

/// Give a decoded word its Arm ARM pseudo-code semantics.
///
/// `fields` replaces immediate fields by quantified terms; only
/// Add/subtract (immediate) and Bitfield read overrides.
pub fn denote_a64_value_word(
    word: &A64ValueWord,
    fields: &FieldOverrides,
) -> Result<A64Effect, A64DenoteRefusal> {
    match *word {
        A64ValueWord::LogicalImmediate { .. }
        | A64ValueWord::MoveWide { .. }
        | A64ValueWord::AddSubShiftedReg { .. } => scalar::denote(word),
        A64ValueWord::LogicalShiftedReg {
            sf,
            opc,
            shift,
            n,
            rm,
            imm6,
            rn,
            rd,
        } => {
            let datasize = 32 << sf;
            let operand1 = read_gpr_zr(rn, datasize);
            let mut operand2 = shift_reg(read_gpr_zr(rm, datasize), shift, imm6, datasize);
            if n == 1 {
                operand2 = operand2.bvxor(all_ones(datasize));
            }
            let result = match opc {
                0b01 => operand1.bvor(operand2),
                0b10 => operand1.bvxor(operand2),
                _ => operand1.bvand(operand2),
            };
            Ok(A64Effect {
                dest: gpr_dest_zr(rd),
                value: zext(result, 64),
                writes_nzcv: opc == 0b11,
            })
        }
        A64ValueWord::AddSubImm { sf, rn, .. } => {
            denote_add_sub_immediate_from_operand(word, fields, read_gpr_sp(rn, 32 << sf))
        }
        A64ValueWord::FpDp1 {
            ftype,
            opcode,
            rn,
            rd,
        } => {
            let esize = fp_size_bits(ftype);
            if opcode >> 2 == 0b0001 {
                return denote_fcvt(ftype, opcode & 0b11, rn, rd, fields);
            }
            let operand = low(vlo(rn), esize);
            let sign = 1u64 << (esize - 1);
            let result = match opcode {
                0b000000 => operand,
                0b000001 => operand.bvand(bv(!sign, esize)),
                0b000010 => operand.bvxor(bv(sign, esize)),
                _ => {
                    return Err(A64DenoteRefusal::UnmodeledInstruction(
                        "FP data-processing (1 source) other than FMOV/FABS/FNEG",
                    ));
                }
            };
            Ok(A64Effect {
                dest: A64Dest::Fpr(rd as u8),
                value: v128_from_scalar(result),
                writes_nzcv: false,
            })
        }
        A64ValueWord::FpIntMove {
            sf,
            ftype,
            rmode,
            to_general,
            rn,
            rd,
        } => {
            if rmode != 0 {
                return Err(A64DenoteRefusal::UnmodeledInstruction(
                    "FMOV to or from the upper half of a vector register",
                ));
            }
            let intsize = 32 << sf;
            let fltsize = fp_size_bits(ftype);
            if to_general {
                // intval = ZeroExtend(V[n, fltsize], intsize); X[d, intsize] = intval.
                let intval = zext(low(vlo(rn), fltsize), intsize);
                Ok(A64Effect {
                    dest: gpr_dest_zr(rd),
                    value: zext(intval, 64),
                    writes_nzcv: false,
                })
            } else {
                // fltval = X[n, intsize]<fltsize-1:0>; V[d] = ZeroExtend(fltval).
                let fltval = low(read_gpr_zr(rn, intsize), fltsize);
                Ok(A64Effect {
                    dest: A64Dest::Fpr(rd as u8),
                    value: v128_from_scalar(fltval),
                    writes_nzcv: false,
                })
            }
        }
        A64ValueWord::Dp3 {
            sf,
            op31,
            rm,
            o0,
            ra,
            rn,
            rd,
            ..
        } => {
            let product = match op31 {
                0b000 => {
                    let datasize = 32 << sf;
                    let product = read_gpr_zr(rn, datasize).bvmul(read_gpr_zr(rm, datasize));
                    let addend = read_gpr_zr(ra, datasize);
                    let result = if o0 == 0 {
                        addend.bvadd(product)
                    } else {
                        addend.bvsub(product)
                    };
                    return Ok(A64Effect {
                        dest: gpr_dest_zr(rd),
                        value: zext(result, 64),
                        writes_nzcv: false,
                    });
                }
                0b001 => read_gpr_zr(rn, 32)
                    .sign_ext(32)
                    .bvmul(read_gpr_zr(rm, 32).sign_ext(32)),
                0b101 => read_gpr_zr(rn, 32)
                    .zero_ext(32)
                    .bvmul(read_gpr_zr(rm, 32).zero_ext(32)),
                _ => {
                    return Err(A64DenoteRefusal::UnmodeledInstruction(
                        "high-half multiply (SMULH/UMULH)",
                    ));
                }
            };
            // The 32x32-bit product fits in 64 bits, so the 64-bit sum is exact.
            let addend = read_gpr_zr(ra, 64);
            let result = if o0 == 0 {
                addend.bvadd(product)
            } else {
                addend.bvsub(product)
            };
            Ok(A64Effect {
                dest: gpr_dest_zr(rd),
                value: result,
                writes_nzcv: false,
            })
        }
        A64ValueWord::Bitfield {
            sf,
            opc,
            immr,
            imms,
            rn,
            rd,
            ..
        } => {
            let datasize = 32 << sf;
            let immr = Field::pick(immr, &fields.immr);
            let imms = Field::pick(imms, &fields.imms);
            let (wmask, tmask, r, s) = decode_bit_masks(&immr, &imms, datasize);
            let dst = if opc == 0b01 {
                read_gpr_zr(rd, datasize)
            } else {
                bv(0, datasize)
            };
            let src = read_gpr_zr(rn, datasize);
            // ROR(src, R); for R == 0 the left shift by datasize is zero.
            let rotated = src.clone().bvlshr(r.clone()).bvor(
                src.clone()
                    .bvshl(bv(u64::from(datasize), datasize).bvsub(r)),
            );
            let not = |x: SmtExpr| x.bvxor(all_ones(datasize));
            let bot = dst
                .clone()
                .bvand(not(wmask.clone()))
                .bvor(rotated.bvand(wmask));
            let top = if opc == 0b00 {
                // Replicate(src<S>): 0 - ((src >> S) & 1).
                bv(0, datasize).bvsub(src.bvlshr(s).bvand(bv(1, datasize)))
            } else {
                dst
            };
            let result = top.bvand(not(tmask.clone())).bvor(bot.bvand(tmask));
            Ok(A64Effect {
                dest: gpr_dest_zr(rd),
                value: zext(result, 64),
                writes_nzcv: false,
            })
        }
        A64ValueWord::Dp1 { sf, opcode, rn, rd } => {
            let datasize = 32 << sf;
            let operand = read_gpr_zr(rn, datasize);
            let result = match opcode {
                0b000000 => reverse_bits(&operand, datasize),
                // REV16 / REV32 (and REV for sf == 0) / REV (sf == 1): reverse
                // the bytes inside each container of 16, 32 or 64 bits.
                0b000001 => reverse_bytes_in_containers(&operand, datasize, 16),
                0b000010 => reverse_bytes_in_containers(&operand, datasize, 32),
                0b000011 => reverse_bytes_in_containers(&operand, datasize, 64),
                _ => {
                    return Err(A64DenoteRefusal::UnmodeledInstruction(
                        "count-leading-zeros/sign bits (CLZ/CLS)",
                    ));
                }
            };
            Ok(A64Effect {
                dest: gpr_dest_zr(rd),
                value: zext(result, 64),
                writes_nzcv: false,
            })
        }
        A64ValueWord::SimdLogical {
            q,
            u,
            size,
            rm,
            rn,
            rd,
        } => {
            // Each 64-bit half separately: `operand1 op operand2` over V[n]
            // and V[m] (Arm ARM LogicalOp); a 64-bit (Q = 0) result writes
            // zeros to V[d]<127:64>.
            let not = |x: SmtExpr| x.bvxor(all_ones(64));
            let op: fn(SmtExpr, SmtExpr, &dyn Fn(SmtExpr) -> SmtExpr) -> SmtExpr = match (u, size) {
                (0, 0b00) => |a, b, _| a.bvand(b),
                (0, 0b01) => |a, b, not| a.bvand(not(b)),
                (0, 0b10) => |a, b, _| a.bvor(b),
                (0, 0b11) => |a, b, not| a.bvor(not(b)),
                (1, 0b00) => |a, b, _| a.bvxor(b),
                _ => {
                    return Err(A64DenoteRefusal::UnmodeledInstruction(
                        "BSL/BIT/BIF (they read the destination register)",
                    ));
                }
            };
            let half = |hi: bool, n: u32| {
                if hi {
                    SmtExpr::var(format!("v{n}_hi"), 64)
                } else {
                    vlo(n)
                }
            };
            let lo = op(half(false, rn), half(false, rm), &not);
            let hi = if q == 1 {
                op(half(true, rn), half(true, rm), &not)
            } else {
                bv(0, 64)
            };
            Ok(A64Effect {
                dest: A64Dest::Fpr(rd as u8),
                value: hi.concat(lo),
                writes_nzcv: false,
            })
        }
        A64ValueWord::SysRegMove {
            l,
            op0,
            op1,
            crn,
            crm,
            op2,
            rt,
        } => {
            let key = sysreg_key(op0 as u16, op1 as u16, crn as u16, crm as u16, op2 as u16);
            if l == 1 {
                Ok(A64Effect {
                    dest: gpr_dest_zr(rt),
                    value: system_register_read(key)?,
                    writes_nzcv: false,
                })
            } else {
                Ok(A64Effect {
                    dest: A64Dest::SystemRegister(key),
                    value: read_gpr_zr(rt, 64),
                    writes_nzcv: key == sysreg_key(3, 3, 4, 2, 0),
                })
            }
        }
    }
}

/// `FCVT` from the `ftype` precision to the `opc` precision: the Arm ARM
/// `FPConvert` transcription of [`crate::aarch64_fcvt_half`], written to the
/// whole vector register. Only the half-precision conversions are modeled.
fn denote_fcvt(
    ftype: u32,
    opc: u32,
    rn: u32,
    rd: u32,
    fields: &FieldOverrides,
) -> Result<A64Effect, A64DenoteRefusal> {
    use crate::aarch64_fcvt_half::{HalfConversion, IeeeFormat, arm_fpconvert};
    let conv = IeeeFormat::from_ftype(ftype)
        .zip(IeeeFormat::from_ftype(opc))
        .and_then(|(src, dst)| HalfConversion::from_formats(src, dst))
        .ok_or(A64DenoteRefusal::UnmodeledInstruction(
            "FCVT between single and double precision",
        ))?;
    let bits = conv.source().bits();
    let operand = match &fields.fp_source {
        Some(source) if source.rn == rn && source.bits == bits => source.value.clone(),
        _ => low(vlo(rn), bits),
    };
    Ok(A64Effect {
        dest: A64Dest::Fpr(rd as u8),
        value: v128_from_scalar(arm_fpconvert(conv, &operand)),
        writes_nzcv: false,
    })
}

/// Scalar FP element size for `ftype` (00 single, 01 double, 11 half). The
/// decoder rejects `ftype == 10` wherever it would reach this.
fn fp_size_bits(ftype: u32) -> u32 {
    match ftype {
        0b00 => 32,
        0b01 => 64,
        _ => 16,
    }
}

/// `result<i> = operand<datasize-1-i>` as a concatenation of single bits.
fn reverse_bits(operand: &SmtExpr, datasize: u32) -> SmtExpr {
    (1..datasize).fold(operand.clone().extract(0, 0), |acc, i| {
        acc.concat(operand.clone().extract(i, i))
    })
}

/// Reverse the bytes of every `container`-bit container (REV16/REV32/REV).
fn reverse_bytes_in_containers(operand: &SmtExpr, datasize: u32, container: u32) -> SmtExpr {
    let container = container.min(datasize);
    let bytes_per = container / 8;
    let mut result: Option<SmtExpr> = None;
    // Build from the most significant container downwards.
    for c in (0..datasize / container).rev() {
        for b in 0..bytes_per {
            // Output byte (bytes_per-1-b) of container c is input byte b.
            let base = c * container + b * 8;
            let byte = operand.clone().extract(base + 7, base);
            result = Some(match result {
                None => byte,
                Some(acc) => acc.concat(byte),
            });
        }
    }
    result.expect("at least one byte")
}

// ===========================================================================
// Exact bit-routing decision
// ===========================================================================

/// One bit of a routing: a constant or one named input bit. The name is shared
/// across a variable's bits, because ENC-5 builds routings per emitted word.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RouteBit {
    Zero,
    One,
    Input(std::sync::Arc<str>, u32),
}

/// Reduce `expr` to its exact per-bit routing (index 0 is the least
/// significant bit), or `None` when some bit is not a constant or a single
/// input bit (an arithmetic dependency, a negated input, a symbolic shift).
///
/// Every rule is an identity of bit-vector semantics — AND/OR/XOR with a
/// constant bit, shifts by constant amounts (a shift by at least the width
/// yields zero, as in SMT-LIB), `x + 0`, selection on a constant condition —
/// so two expressions with equal routings are equal for every assignment, and
/// unequal routings differ for some assignment (a constant bit against an
/// input bit, or two distinct input bits, can be driven apart).
pub fn exact_routing(expr: &SmtExpr) -> Option<Vec<RouteBit>> {
    let bits = routing(expr)?;
    // One shared name per variable, as the routing has always carried it.
    let mut names: Vec<(&str, std::sync::Arc<str>)> = Vec::new();
    Some(
        bits.iter()
            .map(|bit| match *bit {
                Bit::Zero => RouteBit::Zero,
                Bit::One => RouteBit::One,
                Bit::Input(name, b) => {
                    let shared = match names.iter().find(|(n, _)| *n == name) {
                        Some((_, shared)) => shared.clone(),
                        None => {
                            let shared: std::sync::Arc<str> = std::sync::Arc::from(name);
                            names.push((name, shared.clone()));
                            shared
                        }
                    };
                    RouteBit::Input(shared, b)
                }
            })
            .collect(),
    )
}

/// A routing bit whose input name borrows the expression's own variable name.
///
/// [`routing`] applies exactly the rules of [`exact_routing`] (which is now a
/// conversion of its result); bits compare by name content and index in both,
/// so every routing decision, equality and first mismatch is the same. ENC-5
/// decides a routing per emitted word, and the owned form allocated a shared
/// name per variable and paid an atomic reference-count update per bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bit<'a> {
    Zero,
    One,
    Input(&'a str, u32),
}

impl Bit<'_> {
    fn to_route_bit(self) -> RouteBit {
        match self {
            Bit::Zero => RouteBit::Zero,
            Bit::One => RouteBit::One,
            Bit::Input(name, b) => RouteBit::Input(std::sync::Arc::from(name), b),
        }
    }
}

fn routing(expr: &SmtExpr) -> Option<Vec<Bit<'_>>> {
    use Bit::{Input, One, Zero};
    fn binary<'a>(
        lhs: &'a SmtExpr,
        rhs: &'a SmtExpr,
        op: fn(Bit<'a>, Bit<'a>) -> Option<Bit<'a>>,
    ) -> Option<Vec<Bit<'a>>> {
        let (a, b) = (routing(lhs)?, routing(rhs)?);
        if a.len() != b.len() {
            return None;
        }
        a.iter().zip(&b).map(|(x, y)| op(*x, *y)).collect()
    }
    match expr {
        SmtExpr::Var { name, width } => {
            Some((0..*width).map(|b| Input(name.as_str(), b)).collect())
        }
        SmtExpr::BvConst { value, width } => Some(
            (0..*width)
                .map(|b| {
                    if b < 64 && (value >> b) & 1 == 1 {
                        One
                    } else {
                        Zero
                    }
                })
                .collect(),
        ),
        SmtExpr::Concat { hi, lo, .. } => {
            let mut bits = routing(lo)?;
            bits.extend(routing(hi)?);
            Some(bits)
        }
        SmtExpr::Extract {
            high, low, operand, ..
        } => {
            let bits = routing(operand)?;
            bits.get(*low as usize..=*high as usize).map(<[_]>::to_vec)
        }
        SmtExpr::ZeroExtend {
            operand,
            extra_bits,
            ..
        } => {
            let mut bits = routing(operand)?;
            bits.extend(std::iter::repeat_n(Zero, *extra_bits as usize));
            Some(bits)
        }
        SmtExpr::SignExtend {
            operand,
            extra_bits,
            ..
        } => {
            let mut bits = routing(operand)?;
            let sign = *bits.last()?;
            bits.extend(std::iter::repeat_n(sign, *extra_bits as usize));
            Some(bits)
        }
        SmtExpr::BvAnd { lhs, rhs, .. } => binary(lhs, rhs, |a, b| match (a, b) {
            (Zero, _) | (_, Zero) => Some(Zero),
            (One, x) | (x, One) => Some(x),
            (x, y) if x == y => Some(x),
            _ => None,
        }),
        SmtExpr::BvOr { lhs, rhs, .. } => binary(lhs, rhs, |a, b| match (a, b) {
            (One, _) | (_, One) => Some(One),
            (Zero, x) | (x, Zero) => Some(x),
            (x, y) if x == y => Some(x),
            _ => None,
        }),
        SmtExpr::BvXor { lhs, rhs, .. } => binary(lhs, rhs, |a, b| match (a, b) {
            (Zero, x) | (x, Zero) => Some(x),
            (One, One) => Some(Zero),
            (x, y) if x == y => Some(Zero),
            _ => None,
        }),
        SmtExpr::BvShl { lhs, rhs, width }
        | SmtExpr::BvLshr { lhs, rhs, width }
        | SmtExpr::BvAshr { lhs, rhs, width } => {
            let bits = routing(lhs)?;
            let amount = constant_of(&routing(rhs)?)?;
            let width = *width as usize;
            let amount = usize::try_from(amount).unwrap_or(usize::MAX);
            Some(
                (0..width)
                    .map(|i| match expr {
                        SmtExpr::BvShl { .. } => {
                            if amount < width && i >= amount {
                                bits[i - amount]
                            } else {
                                Zero
                            }
                        }
                        SmtExpr::BvLshr { .. } => {
                            if amount < width && i + amount < width {
                                bits[i + amount]
                            } else {
                                Zero
                            }
                        }
                        _ => {
                            if amount < width && i + amount < width {
                                bits[i + amount]
                            } else {
                                bits[width - 1]
                            }
                        }
                    })
                    .collect(),
            )
        }
        SmtExpr::BvAdd { lhs, rhs, width } | SmtExpr::BvSub { lhs, rhs, width } => {
            let (a, b) = (routing(lhs)?, routing(rhs)?);
            let is_zero = |bits: &[Bit<'_>]| bits.iter().all(|bit| *bit == Zero);
            if is_zero(&b) {
                return Some(a);
            }
            if matches!(expr, SmtExpr::BvAdd { .. }) && is_zero(&a) {
                return Some(b);
            }
            let (x, y) = (constant_of(&a)?, constant_of(&b)?);
            let folded = if matches!(expr, SmtExpr::BvAdd { .. }) {
                x.wrapping_add(y)
            } else {
                x.wrapping_sub(y)
            };
            Some(routing_of_constant(folded, *width))
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            if routing_bool(cond)? {
                routing(then_expr)
            } else {
                routing(else_expr)
            }
        }
        _ => None,
    }
}

fn routing_of_constant<'a>(value: u128, width: u32) -> Vec<Bit<'a>> {
    (0..width)
        .map(|b| {
            if b < 128 && (value >> b) & 1 == 1 {
                Bit::One
            } else {
                Bit::Zero
            }
        })
        .collect()
}

/// The value of an all-constant routing (at most 128 bits).
fn constant_of(bits: &[Bit<'_>]) -> Option<u128> {
    if bits.len() > 128 {
        return None;
    }
    bits.iter()
        .enumerate()
        .try_fold(0u128, |acc, (i, bit)| match bit {
            Bit::Zero => Some(acc),
            Bit::One => Some(acc | (1u128 << i)),
            Bit::Input(..) => None,
        })
}

/// A Boolean that folds to a constant through equalities of constant routings.
fn routing_bool(expr: &SmtExpr) -> Option<bool> {
    match expr {
        SmtExpr::BoolConst(value) => Some(*value),
        SmtExpr::Not { operand } => routing_bool(operand).map(|value| !value),
        SmtExpr::Eq { lhs, rhs } => {
            Some(constant_of(&routing(lhs)?)? == constant_of(&routing(rhs)?)?)
        }
        _ => None,
    }
}

/// The first bit where two routings disagree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoutingMismatch {
    pub bit: u32,
    pub intended: RouteBit,
    pub emitted: RouteBit,
}

/// Decide `intended == emitted` exactly, or `None` when either side is not a
/// pure routing.
pub fn exact_routing_equality(
    intended: &SmtExpr,
    emitted: &SmtExpr,
) -> Option<Result<(), RoutingMismatch>> {
    let (a, b) = (routing(intended)?, routing(emitted)?);
    if a.len() != b.len() {
        return Some(Err(RoutingMismatch {
            bit: a.len().min(b.len()) as u32,
            intended: RouteBit::Zero,
            emitted: RouteBit::Zero,
        }));
    }
    match a.iter().zip(&b).position(|(x, y)| x != y) {
        None => Some(Ok(())),
        Some(i) => Some(Err(RoutingMismatch {
            bit: i as u32,
            intended: a[i].to_route_bit(),
            emitted: b[i].to_route_bit(),
        })),
    }
}

// ===========================================================================
// Machine-IR intent
// ===========================================================================

/// A general-purpose register name as the machine IR spells it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GprName {
    Num(u8),
    Sp,
    Zr,
}

/// An operand as the intent reads it. Register identities come from the
/// register model's encoding ranges (`trust_cg_ir::aarch64_regs`), not from the
/// encoder's field tables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Operand {
    Gpr { width: u32, name: GprName },
    Fpr { bits: u32, num: u8 },
    Imm(i64),
}

fn operand(op: &MachOperand) -> Option<Operand> {
    let gpr = |width, name| Some(Operand::Gpr { width, name });
    match op {
        MachOperand::PReg(p) => {
            let e = p.encoding();
            match e {
                0..=30 => gpr(64, GprName::Num(e as u8)),
                31 => gpr(64, GprName::Sp),
                32..=62 => gpr(32, GprName::Num((e - 32) as u8)),
                63 => gpr(32, GprName::Sp),
                64..=95 => Some(Operand::Fpr {
                    bits: 128,
                    num: (e - 64) as u8,
                }),
                96..=127 => Some(Operand::Fpr {
                    bits: 64,
                    num: (e - 96) as u8,
                }),
                128..=159 => Some(Operand::Fpr {
                    bits: 32,
                    num: (e - 128) as u8,
                }),
                160 => gpr(64, GprName::Zr),
                161 => gpr(32, GprName::Zr),
                165..=196 => Some(Operand::Fpr {
                    bits: 16,
                    num: (e - 165) as u8,
                }),
                _ => None,
            }
        }
        MachOperand::Special(SpecialReg::SP) => gpr(64, GprName::Sp),
        MachOperand::Special(SpecialReg::XZR) => gpr(64, GprName::Zr),
        MachOperand::Special(SpecialReg::WZR) => gpr(32, GprName::Zr),
        MachOperand::Imm(value) => Some(Operand::Imm(*value)),
        _ => None,
    }
}

/// The register value a general-purpose name denotes, at `width` bits.
fn gpr_value(name: GprName, width: u32) -> SmtExpr {
    match name {
        GprName::Num(n) => low(xvar(u32::from(n)), width),
        GprName::Sp => low(spvar(), width),
        GprName::Zr => bv(0, width),
    }
}

fn gpr_dest(name: GprName) -> A64Dest {
    match name {
        GprName::Num(n) => A64Dest::Gpr(n),
        GprName::Sp => A64Dest::Sp,
        GprName::Zr => A64Dest::Discarded,
    }
}

/// The intent's spelling of a general-register write: zeros concatenated
/// above the value. The pseudo-code side spells the same write `ZeroExtend`,
/// so a register copy is never the X==X self-equality.
fn intent_gpr_write(value: SmtExpr) -> SmtExpr {
    let width = value.bv_width();
    if width == 64 {
        value
    } else {
        bv(0, 64 - width).concat(value)
    }
}

/// The intent's spelling of a scalar FP register write: `ZeroExtend` to 128
/// bits. The pseudo-code side concatenates a zero upper doubleword.
fn intent_fpr_write(value: SmtExpr) -> SmtExpr {
    let width = value.bv_width();
    value.zero_ext(128 - width)
}

/// The intent's read of the low `bits` of `V<n>`, through the whole 128-bit
/// register (the pseudo-code side reads the low doubleword directly).
fn intent_fpr_read(n: u8, bits: u32) -> SmtExpr {
    SmtExpr::var(format!("v{n}_hi"), 64)
        .concat(vlo(u32::from(n)))
        .extract(bits - 1, 0)
}

/// The 5-bit register field an intent requires for a name (31 for SP/ZR).
fn gpr_field(name: GprName) -> u32 {
    match name {
        GprName::Num(n) => u32::from(n),
        GprName::Sp | GprName::Zr => 31,
    }
}

/// How the per-instance check decides a word against an intent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64Decision {
    /// Both sides are pure bit routings, compared exactly.
    ExactRouting,
    /// The word must be an instance of `form`'s canonical captured word — the
    /// same class and fixed fields — with the intent's register and immediate
    /// fields. The form's registered value obligation carries the semantics.
    InstanceOf {
        form: A64ValueForm,
        rd: u32,
        rn: u32,
        rm: u32,
        imm12: u32,
    },
}

/// What one machine-IR instruction claims its word does.
#[derive(Debug, Clone, PartialEq)]
pub struct A64ValueIntent {
    /// The coverage-gate form this instance belongs to, if any. Instances
    /// outside every form (a zero-register source, say) are still decided.
    pub form: Option<A64ValueForm>,
    pub dest: A64Dest,
    /// 64-bit for a general-purpose/SP/discarded write, 128-bit for `V<n>`.
    pub value: SmtExpr,
    pub decision: A64Decision,
}

/// Why a word was not accepted for an instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum A64ValueCheckError {
    /// The instruction's shape is outside the modeled forms. No claim is made
    /// either way; ENC-5 keeps its structural verdict for such shapes.
    OutOfModel(String),
    /// The instruction names a transfer no single instruction of its opcode
    /// performs (for example an FMOV between a W register and a D register).
    /// Fails closed.
    IllFormed(String),
    /// The word does not denote the instruction's intent. Fails closed.
    Refuted(A64ValueRefutation),
}

impl std::fmt::Display for A64ValueCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfModel(why) => write!(f, "outside the decoded value model: {why}"),
            Self::IllFormed(why) => write!(f, "ill-formed instruction: {why}"),
            Self::Refuted(refutation) => write!(f, "{refutation}"),
        }
    }
}

/// A refutation and the reason class it was refuted for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct A64ValueRefutation {
    pub class: A64RefusalClass,
    pub detail: String,
}

impl std::fmt::Display for A64ValueRefutation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "refuted ({:?}): {}", self.class, self.detail)
    }
}

/// The reason class of a refutation. Negative controls name the class they
/// must be refuted for, so a control refuted for the wrong reason fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum A64RefusalClass {
    /// The written value differs for some register state.
    Value,
    /// The word writes a different register or register bank.
    Destination,
    /// The word writes NZCV and the intent does not.
    Flags,
    /// The word is unallocated or reserved in its class.
    Unallocated,
    /// The word is in no modeled class.
    NotDecoded,
    /// The word decodes to an instruction outside the modeled semantics.
    UnmodeledInstruction,
    /// The word names a system register outside the modeled file.
    UnmodeledSystemRegister,
}

fn refuted(class: A64RefusalClass, detail: impl Into<String>) -> A64ValueCheckError {
    A64ValueCheckError::Refuted(A64ValueRefutation {
        class,
        detail: detail.into(),
    })
}

fn out_of_model(why: impl Into<String>) -> A64ValueCheckError {
    A64ValueCheckError::OutOfModel(why.into())
}

fn ill_formed(why: impl Into<String>) -> A64ValueCheckError {
    A64ValueCheckError::IllFormed(why.into())
}

fn operands<const N: usize>(inst: &MachInst) -> Result<[Operand; N], A64ValueCheckError> {
    if inst.operands.len() != N {
        return Err(out_of_model(format!(
            "{:?} with {} operands (expected {N})",
            inst.opcode,
            inst.operands.len()
        )));
    }
    let mut out = [Operand::Imm(0); N];
    for (slot, op) in out.iter_mut().zip(&inst.operands) {
        *slot = operand(op).ok_or_else(|| out_of_model(format!("unmodeled operand {op:?}")))?;
    }
    Ok(out)
}

/// `concat(fill, a)` with `fill` all ones when `a` is negative: sign
/// extension of a 32-bit value spelled without a `sign_extend` node.
fn sign_extended_by_concat(a: SmtExpr) -> SmtExpr {
    let negative = a.clone().extract(31, 31).eq_expr(bv(1, 1));
    SmtExpr::ite(negative, bv(0xFFFF_FFFF, 32), bv(0, 32)).concat(a)
}

/// `(src[width-1:0]` inserted into `dst` at `lsb`) as a concatenation of the
/// three segments — the InsertBits splice, written without masks.
fn splice(dst: SmtExpr, src: SmtExpr, lsb: u32, width: u32, datasize: u32) -> SmtExpr {
    let mut result = src.extract(width - 1, 0);
    if lsb > 0 {
        result = result.concat(dst.clone().extract(lsb - 1, 0));
    }
    if lsb + width < datasize {
        result = dst.extract(datasize - 1, lsb + width).concat(result);
    }
    result
}

/// The SWAR bit-reversal butterfly the bit-reverse idiom recognizer matches:
/// swap adjacent 1-, 2-, 4-, 8-(, 16-)bit groups under masks, then rotate by
/// half the width. Structurally unrelated to the bit-by-bit RBIT semantics.
fn swar_bit_reverse(x: SmtExpr, datasize: u32) -> SmtExpr {
    const STEPS: [(u32, u64); 5] = [
        (1, 0x5555_5555_5555_5555),
        (2, 0x3333_3333_3333_3333),
        (4, 0x0f0f_0f0f_0f0f_0f0f),
        (8, 0x00ff_00ff_00ff_00ff),
        (16, 0x0000_ffff_0000_ffff),
    ];
    let half = datasize / 2;
    let mut x = x;
    for &(shift, mask) in STEPS.iter().filter(|&&(shift, _)| shift < half) {
        let (s, m) = (bv(u64::from(shift), datasize), bv(mask, datasize));
        x = x
            .clone()
            .bvlshr(s.clone())
            .bvand(m.clone())
            .bvor(x.bvand(m).bvshl(s));
    }
    let h = bv(u64::from(half), datasize);
    x.clone().bvlshr(h.clone()).bvor(x.bvshl(h))
}

// The intent is deliberately partial: keep the original supported arms and
// refusal together, while scalar copies avoid reserving every symbolic
// construction branch's debug frame. Each arm has one source of truth.
macro_rules! a64_value_intent_families {
    (
        $inst:ident, $opcode_alias:ident;
        $other:ident => $unsupported:expr;
        $(
            $family:ident [$($exact:ident)?] {
                $($pattern:pat => $body:block)*
            }
        )*
    ) => {
        /// Derive what `inst` claims its word writes.
        ///
        /// A register copy writes the source at the DESTINATION's width, the W write
        /// zero-extending (Arm ARM: a write to `Wd` clears `Xd[63:32]`, and a scalar
        /// FP write clears the rest of `V<d>`). Cross-class FMOV must pair W with S or
        /// X with D (or either with H); any other pairing names no FMOV and is
        /// ill-formed.
        pub fn a64_value_intent(
            $inst: &MachInst,
        ) -> Result<A64ValueIntent, A64ValueCheckError> {
            use AArch64Opcode as $opcode_alias;
            match $inst.opcode {
                $($($pattern => $family($inst),)*)*
                $other => $unsupported,
            }
        }

        $(
            #[inline(never)]
            fn $family($inst: &MachInst) -> Result<A64ValueIntent, A64ValueCheckError> {
                use AArch64Opcode as $opcode_alias;
                $(
                    let $exact = |form, dest, value| A64ValueIntent {
                        form,
                        dest,
                        value,
                        decision: A64Decision::ExactRouting,
                    };
                )?
                match $inst.opcode {
                    $($pattern => $body,)*
                    // A private routing mismatch retains the public refusal,
                    // not a panic or an extra accepted symbolic shape.
                    $other => $unsupported,
                }
            }
        )*
    };
}

a64_value_intent_families! {
    inst, O;
    other => Err(out_of_model(format!(
            "{other:?} is not a decoded value opcode"
        )));

    a64_intent_register_copy[exact] {
        O::MovR => {
            let [dst, src] = operands::<2>(inst)?;
            let Operand::Gpr { width, name: dname } = dst else {
                return Err(out_of_model(
                    "MOV destination is not a general-purpose register",
                ));
            };
            let Operand::Gpr { name: sname, .. } = src else {
                return Err(out_of_model("MOV source is not a general-purpose register"));
            };
            if dname == GprName::Sp && width == 32 {
                return Err(out_of_model("MOV to WSP"));
            }
            // A zero-register source (`MOV Rd, ZR`, the ORR of two zero
            // registers) writes zero; the backend emits it for a zero-sized
            // aggregate argument (`isel.rs`, `Copy Xn <- XZR`).
            let form = match (width, dname, sname) {
                (32, GprName::Num(_), GprName::Num(_)) => Some(A64ValueForm::MovW),
                (64, GprName::Num(_), GprName::Num(_)) => Some(A64ValueForm::MovX),
                (64, GprName::Num(_), GprName::Sp) => Some(A64ValueForm::MovXFromSp),
                (32, GprName::Num(_), GprName::Zr) => Some(A64ValueForm::MovWFromZr),
                (64, GprName::Num(_), GprName::Zr) => Some(A64ValueForm::MovXFromZr),
                _ => None,
            };
            Ok(exact(
                form,
                gpr_dest(dname),
                intent_gpr_write(gpr_value(sname, width)),
            ))
        }
        // The typed copies `lower_copies` emits after register allocation.
        // The OPCODE fixes the width (the encoder ignores the operands' W/X
        // views), so the intent reads only the register numbers from them.
    }
    a64_intent_typed_register_copy[exact] {
        O::MOVWrr | O::MOVXrr => {
            let [dst, src] = operands::<2>(inst)?;
            let Operand::Gpr { name: dname, .. } = dst else {
                return Err(out_of_model(
                    "typed MOV destination is not a general-purpose register",
                ));
            };
            let Operand::Gpr { name: sname, .. } = src else {
                return Err(out_of_model(
                    "typed MOV source is not a general-purpose register",
                ));
            };
            let width = if inst.opcode == O::MOVWrr { 32 } else { 64 };
            if width == 32 && (dname == GprName::Sp || sname == GprName::Sp) {
                return Err(out_of_model("MOVWrr naming WSP"));
            }
            // Register-to-register copies and a zero-register source (either
            // view: register 31 reads zero at both widths) are forms; SP and a
            // zero-register destination stay outside them (ENC-5 still
            // decides their words). `lower_copies` turns the zero-sized
            // aggregate argument's `Copy Xn <- XZR` into `MOVXrr Xn, XZR`.
            let form = match (width, dname, sname) {
                (32, GprName::Num(_), GprName::Num(_)) => Some(A64ValueForm::MovWrr),
                (64, GprName::Num(_), GprName::Num(_)) => Some(A64ValueForm::MovXrr),
                (32, GprName::Num(_), GprName::Zr) => Some(A64ValueForm::MovWrrFromZr),
                (64, GprName::Num(_), GprName::Zr) => Some(A64ValueForm::MovXrrFromZr),
                _ => None,
            };
            Ok(exact(
                form,
                gpr_dest(dname),
                intent_gpr_write(gpr_value(sname, width)),
            ))
        }
    }
    a64_intent_fp_register_copy[exact] {
        O::FmovFprFpr => {
            let [dst, src] = operands::<2>(inst)?;
            let (
                Operand::Fpr { bits, num: d },
                Operand::Fpr {
                    bits: src_bits,
                    num: n,
                },
            ) = (dst, src)
            else {
                return Err(out_of_model("FMOV (register) operands are not scalar FPRs"));
            };
            if bits == 128 || src_bits == 128 {
                return Err(out_of_model("Q-register copy (NeonOrrV is the Q move)"));
            }
            let form = match (bits, src_bits) {
                (32, 32) => Some(A64ValueForm::FmovS),
                (64, 64) => Some(A64ValueForm::FmovD),
                _ => None,
            };
            Ok(exact(
                form,
                A64Dest::Fpr(d),
                intent_fpr_write(intent_fpr_read(n, bits)),
            ))
        }
    }
    a64_intent_fp_to_general_copy[exact] {
        O::FmovFprGpr => {
            let [dst, src] = operands::<2>(inst)?;
            let (Operand::Gpr { width, name }, Operand::Fpr { bits, num: n }) = (dst, src) else {
                return Err(ill_formed(
                    "bank-direction mismatch: FMOV to a general register needs a GPR \
                     destination and an FPR source",
                ));
            };
            if name == GprName::Sp {
                return Err(ill_formed("FMOV cannot write SP: register 31 is XZR there"));
            }
            // The forms name numbered general registers only: `FMOV XZR, Dn`
            // discards its value and is left outside them. `FMOV Wd, Hn`
            // (FEAT_FP16) is emitted by the f16 select and i16/f16 bitcast
            // lowering; `FMOV Xd, Hn` is not emitted and stays outside.
            let numbered = matches!(name, GprName::Num(_));
            let form = match (width, bits) {
                (32, 32) if numbered => Some(A64ValueForm::FmovWFromS),
                (64, 64) if numbered => Some(A64ValueForm::FmovXFromD),
                (32, 16) if numbered => Some(A64ValueForm::FmovWFromH),
                (32, 32) | (64, 64) | (_, 16) => None,
                _ => {
                    return Err(ill_formed(format!(
                        "cross-class width mismatch: no FMOV moves a {bits}-bit FP register \
                         to a {width}-bit general register"
                    )));
                }
            };
            Ok(exact(
                form,
                gpr_dest(name),
                intent_gpr_write(intent_fpr_read(n, bits)),
            ))
        }
    }
    a64_intent_general_to_fp_copy[exact] {
        O::FmovGprFpr => {
            let [dst, src] = operands::<2>(inst)?;
            let (Operand::Fpr { bits, num: d }, Operand::Gpr { width, name }) = (dst, src) else {
                return Err(ill_formed(
                    "bank-direction mismatch: FMOV from a general register needs an FPR \
                     destination and a GPR source",
                ));
            };
            if name == GprName::Sp {
                return Err(ill_formed("FMOV cannot read SP: register 31 is XZR there"));
            }
            // The forms read numbered general registers only: `FMOV Dd, XZR`
            // (zeroing) is not emitted and is left outside them. `FMOV Hd, Wn`
            // (FEAT_FP16) is emitted by the f16 select, the i16/f16 bitcast
            // and f16 constant lowering; `FMOV Hd, Xn` is not and stays
            // outside.
            let numbered = matches!(name, GprName::Num(_));
            let form = match (bits, width) {
                (32, 32) if numbered => Some(A64ValueForm::FmovSFromW),
                (64, 64) if numbered => Some(A64ValueForm::FmovDFromX),
                (16, 32) if numbered => Some(A64ValueForm::FmovHFromW),
                (32, 32) | (64, 64) | (16, _) => None,
                _ => {
                    return Err(ill_formed(format!(
                        "cross-class width mismatch: no FMOV moves a {width}-bit general \
                         register to a {bits}-bit FP register"
                    )));
                }
            };
            Ok(exact(
                form,
                A64Dest::Fpr(d),
                intent_fpr_write(low(gpr_value(name, width), bits)),
            ))
        }
        // `ORR Vd.<T>, Vn.<T>, Vm.<T>`. With Vn == Vm it is the architectural
        // register move `MOV Vd.<T>, Vn.<T>`, which `lower_copies` emits for
        // every post-allocation H/S/D/Q copy (with the `.16B` selector for
        // H/S/D). The arrangement comes from a trailing `#0` (8B) / `#1` (16B)
        // selector, else from the destination's width. Only the 16B copy is
        // a form; a bitwise OR of two registers is not a copy.
    }
    a64_intent_vector_copy[exact] {
        O::NeonOrrV => {
            let (regs, selector) = match inst.operands.len() {
                3 => (operands::<3>(inst)?, None),
                4 => {
                    let [d, n, m, sel] = operands::<4>(inst)?;
                    let Operand::Imm(sel) = sel else {
                        return Err(out_of_model(
                            "ORR (vector) fourth operand is not a selector",
                        ));
                    };
                    ([d, n, m], Some(sel))
                }
                count => {
                    return Err(out_of_model(format!(
                        "ORR (vector) with {count} operands (expected 3, or 4 with a selector)"
                    )));
                }
            };
            let [
                Operand::Fpr { bits, num: d },
                Operand::Fpr { num: n, .. },
                Operand::Fpr { num: m, .. },
            ] = regs
            else {
                return Err(out_of_model(
                    "ORR (vector) operands are not SIMD&FP registers",
                ));
            };
            let full = match selector {
                Some(1) => true,
                Some(0) => false,
                Some(other) => {
                    return Err(out_of_model(format!(
                        "ORR (vector) arrangement selector #{other} (expected #0 or #1)"
                    )));
                }
                None => bits == 128,
            };
            if n != m {
                return Err(out_of_model(
                    "ORR (vector) of two different registers is a bitwise OR, not a copy",
                ));
            }
            let lo = vlo(u32::from(n));
            let value = if full {
                SmtExpr::var(format!("v{n}_hi"), 64).concat(lo)
            } else {
                bv(0, 64).concat(lo)
            };
            Ok(exact(
                full.then_some(A64ValueForm::MovV16B),
                A64Dest::Fpr(d),
                value,
            ))
        }
    }
    a64_intent_signed_long_multiply[] {
        O::Smull => {
            let [dst, lhs, rhs] = operands::<3>(inst)?;
            let (
                Operand::Gpr { width: 64, name: d },
                Operand::Gpr { name: n, .. },
                Operand::Gpr { name: m, .. },
            ) = (dst, lhs, rhs)
            else {
                return Err(ill_formed(
                    "SMULL writes a 64-bit general register from two general registers",
                ));
            };
            if [d, n, m].contains(&GprName::Sp) {
                return Err(ill_formed("SMULL cannot name SP: register 31 is XZR there"));
            }
            let value = sign_extended_by_concat(gpr_value(n, 32))
                .bvmul(sign_extended_by_concat(gpr_value(m, 32)));
            Ok(A64ValueIntent {
                form: Some(A64ValueForm::Smull),
                dest: gpr_dest(d),
                value,
                decision: A64Decision::InstanceOf {
                    form: A64ValueForm::Smull,
                    rd: gpr_field(d),
                    rn: gpr_field(n),
                    rm: gpr_field(m),
                    imm12: 0,
                },
            })
        }
    }
    a64_intent_bitfield_insert[exact] {
        O::Bfm => {
            let [dst, src, immr, imms] = operands::<4>(inst)?;
            let (
                Operand::Gpr { width, name: d },
                Operand::Gpr {
                    width: src_width,
                    name: n,
                },
                Operand::Imm(immr),
                Operand::Imm(imms),
            ) = (dst, src, immr, imms)
            else {
                return Err(out_of_model("BFM needs Rd, Rn, #immr, #imms"));
            };
            if width != src_width {
                return Err(ill_formed("BFM register widths differ"));
            }
            if d == GprName::Sp || n == GprName::Sp {
                return Err(ill_formed("BFM cannot name SP: register 31 is ZR there"));
            }
            let GprName::Num(_) = d else {
                return Err(out_of_model("BFM into the zero register"));
            };
            let datasize = i64::from(width);
            if !(0..datasize).contains(&immr) || !(0..datasize).contains(&imms) {
                return Err(ill_formed("BFM immediate outside the register"));
            }
            if immr != 0 && imms >= immr {
                return Err(out_of_model(
                    "BFM outside the bitfield-insert (BFI) family the lowering emits",
                ));
            }
            let (datasize, immr, imms) = (width, immr as u32, imms as u32);
            let lsb = (datasize - immr) % datasize;
            let field_width = imms + 1;
            let value = splice(
                gpr_value(d, datasize),
                gpr_value(n, datasize),
                lsb,
                field_width,
                datasize,
            );
            let form = if datasize == 32 {
                A64ValueForm::BfmInsertW
            } else {
                A64ValueForm::BfmInsertX
            };
            Ok(exact(Some(form), gpr_dest(d), intent_gpr_write(value)))
        }
    }
    a64_intent_reverse_bits[exact] {
        O::Rbit => {
            let [dst, src] = operands::<2>(inst)?;
            let (
                Operand::Gpr { width, name: d },
                Operand::Gpr {
                    width: src_width,
                    name: n,
                },
            ) = (dst, src)
            else {
                return Err(out_of_model("RBIT needs two general registers"));
            };
            if width != src_width {
                return Err(ill_formed("RBIT register widths differ"));
            }
            if d == GprName::Sp || n == GprName::Sp {
                return Err(ill_formed("RBIT cannot name SP: register 31 is ZR there"));
            }
            let form = if width == 32 {
                A64ValueForm::RbitW
            } else {
                A64ValueForm::RbitX
            };
            Ok(exact(
                Some(form),
                gpr_dest(d),
                intent_gpr_write(swar_bit_reverse(gpr_value(n, width), width)),
            ))
        }
    }
    a64_intent_shifted_immediate_add[] {
        O::AddRIShift12 => {
            let [dst, src, imm] = operands::<3>(inst)?;
            let (
                Operand::Gpr { width, name: d },
                Operand::Gpr {
                    width: src_width,
                    name: n,
                },
                Operand::Imm(imm),
            ) = (dst, src, imm)
            else {
                return Err(out_of_model("ADD (immediate) needs Rd, Rn, #imm12"));
            };
            if d == GprName::Zr || n == GprName::Zr {
                return Err(ill_formed(
                    "register 31 names SP in ADD (immediate); a zero register cannot be encoded",
                ));
            }
            if width != src_width {
                return Err(ill_formed("ADD (immediate) register widths differ"));
            }
            if width == 32 && d == GprName::Sp {
                return Err(out_of_model("ADD (immediate) into WSP"));
            }
            if !(0..=4095).contains(&imm) {
                return Err(ill_formed("ADD (immediate) imm12 outside 0..=4095"));
            }
            let form = if width == 32 {
                A64ValueForm::AddLsl12W
            } else {
                A64ValueForm::AddLsl12X
            };
            let value = intent_gpr_write(gpr_value(n, width).bvadd(bv((imm as u64) << 12, width)));
            Ok(A64ValueIntent {
                form: Some(form),
                dest: gpr_dest(d),
                value,
                decision: A64Decision::InstanceOf {
                    form,
                    rd: gpr_field(d),
                    rn: gpr_field(n),
                    rm: 0,
                    imm12: imm as u32,
                },
            })
        }
    }
    a64_intent_system_register_read[exact] {
        O::Mrs => {
            let [dst, key] = operands::<2>(inst)?;
            let (Operand::Gpr { width, name }, Operand::Imm(key)) = (dst, key) else {
                return Err(out_of_model("MRS needs Rt, #systemreg"));
            };
            if width != 64 || name == GprName::Sp {
                return Err(ill_formed("MRS writes a 64-bit general register or XZR"));
            }
            if key != i64::from(TPIDR_EL0_KEY) {
                return Err(out_of_model(format!(
                    "MRS of system register key {key:#x}; only TPIDR_EL0 is modeled"
                )));
            }
            Ok(exact(
                Some(A64ValueForm::MrsTpidrEl0),
                gpr_dest(name),
                SmtExpr::var("tpidr_el0", 64),
            ))
        }
    }
    a64_intent_half_conversion[] {
        O::FcvtHS | O::FcvtHD | O::FcvtSH | O::FcvtDH => {
            use crate::aarch64_fcvt_half::ieee_convert_format;
            let [dst, src] = operands::<2>(inst)?;
            let (
                Operand::Fpr { bits, num: d },
                Operand::Fpr {
                    bits: src_bits,
                    num: n,
                },
            ) = (dst, src)
            else {
                return Err(ill_formed("FCVT converts between scalar FP registers"));
            };
            let form = match inst.opcode {
                O::FcvtHS => A64ValueForm::FcvtSFromH,
                O::FcvtHD => A64ValueForm::FcvtDFromH,
                O::FcvtSH => A64ValueForm::FcvtHFromS,
                _ => A64ValueForm::FcvtHFromD,
            };
            let conv = form
                .half_conversion()
                .ok_or_else(|| out_of_model("FCVT form without a conversion"))?;
            if (src_bits, bits) != (conv.source().bits(), conv.destination().bits()) {
                return Err(ill_formed(format!(
                    "{:?} converts a {}-bit register to a {}-bit register, not {src_bits} to \
                     {bits}",
                    inst.opcode,
                    conv.source().bits(),
                    conv.destination().bits()
                )));
            }
            let value = intent_fpr_write(ieee_convert_format(conv, &intent_fpr_read(n, src_bits)));
            Ok(A64ValueIntent {
                form: Some(form),
                dest: A64Dest::Fpr(d),
                value,
                decision: A64Decision::InstanceOf {
                    form,
                    rd: u32::from(d),
                    rn: u32::from(n),
                    rm: 0,
                    imm12: 0,
                },
            })
        }
    }
}

// ===========================================================================
// Forms
// ===========================================================================

/// One emitted form of a decoded-value opcode. The coverage gate demands
/// every form of an opcode; the function verifier binds each concrete SMULL,
/// BFM, RBIT, `ADD #imm12, LSL #12` and MRS instruction to exactly one form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum A64ValueForm {
    /// `MOV Wd, Wn` (`ORR Wd, WZR, Wm`).
    MovW,
    /// `MOV Xd, Xn` (`ORR Xd, XZR, Xm`).
    MovX,
    /// `MOV Xd, SP` (`ADD Xd, SP, #0`).
    MovXFromSp,
    /// The typed post-allocation copy `MOVWrr Wd, Wn` (`ORR Wd, WZR, Wm`): the
    /// opcode fixes the 32-bit width whatever register view the allocator
    /// left on its operands.
    MovWrr,
    /// The typed post-allocation copy `MOVXrr Xd, Xn` (`ORR Xd, XZR, Xm`),
    /// 64 bits whatever the operand views.
    MovXrr,
    /// `MOV Wd, WZR` (`ORR Wd, WZR, WZR`): writes zero, Xd[63:32] cleared.
    MovWFromZr,
    /// `MOV Xd, XZR` (`ORR Xd, XZR, XZR`): writes zero.
    MovXFromZr,
    /// The typed `MOVWrr Wd, ZR` (`ORR Wd, WZR, WZR`) whatever the views.
    MovWrrFromZr,
    /// The typed `MOVXrr Xd, ZR` (`ORR Xd, XZR, XZR`) whatever the views;
    /// the zero-sized aggregate argument's register.
    MovXrrFromZr,
    /// `FMOV Sd, Sn`.
    FmovS,
    /// `FMOV Dd, Dn`.
    FmovD,
    /// `FMOV Wd, Sn`.
    FmovWFromS,
    /// `FMOV Xd, Dn`.
    FmovXFromD,
    /// `FMOV Sd, Wn`.
    FmovSFromW,
    /// `FMOV Dd, Xn`.
    FmovDFromX,
    /// `FMOV Wd, Hn` (FEAT_FP16): Hn's 16 bits zero-extended into Xd.
    FmovWFromH,
    /// `FMOV Hd, Wn` (FEAT_FP16): Wn's low 16 bits, Vd[127:16] zero.
    FmovHFromW,
    /// `MOV Vd.16B, Vn.16B` (`ORR Vd.16B, Vn.16B, Vn.16B`): all 128 bits of
    /// Vn, the move `lower_copies` emits for every H/S/D/Q copy.
    MovV16B,
    /// `SMULL Xd, Wn, Wm` (`SMADDL Xd, Wn, Wm, XZR`).
    Smull,
    /// `BFM Wd, Wn, #immr, #imms` in its bitfield-insert family.
    BfmInsertW,
    /// `BFM Xd, Xn, #immr, #imms` in its bitfield-insert family.
    BfmInsertX,
    /// `RBIT Wd, Wn`.
    RbitW,
    /// `RBIT Xd, Xn`.
    RbitX,
    /// `ADD Wd, Wn, #imm12, LSL #12`.
    AddLsl12W,
    /// `ADD Xd, Xn|SP, #imm12, LSL #12`.
    AddLsl12X,
    /// `MRS Xt, TPIDR_EL0`.
    MrsTpidrEl0,
    /// `FCVT Sd, Hn`: binary16 -> binary32, exact.
    FcvtSFromH,
    /// `FCVT Dd, Hn`: binary16 -> binary64, exact.
    FcvtDFromH,
    /// `FCVT Hd, Sn`: binary32 -> binary16, round to nearest even.
    FcvtHFromS,
    /// `FCVT Hd, Dn`: binary64 -> binary16, round to nearest even.
    FcvtHFromD,
}

impl A64ValueForm {
    /// Every form, in registration order.
    pub const ALL: &'static [Self] = &[
        Self::MovW,
        Self::MovX,
        Self::MovXFromSp,
        Self::MovWFromZr,
        Self::MovXFromZr,
        Self::MovWrr,
        Self::MovWrrFromZr,
        Self::MovXrr,
        Self::MovXrrFromZr,
        Self::FmovS,
        Self::FmovD,
        Self::FmovWFromS,
        Self::FmovXFromD,
        Self::FmovWFromH,
        Self::FmovSFromW,
        Self::FmovDFromX,
        Self::FmovHFromW,
        Self::MovV16B,
        Self::Smull,
        Self::BfmInsertW,
        Self::BfmInsertX,
        Self::RbitW,
        Self::RbitX,
        Self::AddLsl12W,
        Self::AddLsl12X,
        Self::MrsTpidrEl0,
        Self::FcvtSFromH,
        Self::FcvtDFromH,
        Self::FcvtHFromS,
        Self::FcvtHFromD,
    ];

    /// The half-precision conversion an FCVT form performs.
    pub fn half_conversion(self) -> Option<crate::aarch64_fcvt_half::HalfConversion> {
        use crate::aarch64_fcvt_half::HalfConversion as C;
        Some(match self {
            Self::FcvtSFromH => C::HalfToSingle,
            Self::FcvtDFromH => C::HalfToDouble,
            Self::FcvtHFromS => C::SingleToHalf,
            Self::FcvtHFromD => C::DoubleToHalf,
            _ => return None,
        })
    }

    /// The machine-IR opcode this form belongs to.
    pub fn opcode(self) -> AArch64Opcode {
        use AArch64Opcode as O;
        match self {
            Self::MovW | Self::MovX | Self::MovXFromSp | Self::MovWFromZr | Self::MovXFromZr => {
                O::MovR
            }
            Self::MovWrr | Self::MovWrrFromZr => O::MOVWrr,
            Self::MovXrr | Self::MovXrrFromZr => O::MOVXrr,
            Self::FmovS | Self::FmovD => O::FmovFprFpr,
            Self::FmovWFromS | Self::FmovXFromD | Self::FmovWFromH => O::FmovFprGpr,
            Self::FmovSFromW | Self::FmovDFromX | Self::FmovHFromW => O::FmovGprFpr,
            Self::MovV16B => O::NeonOrrV,
            Self::Smull => O::Smull,
            Self::BfmInsertW | Self::BfmInsertX => O::Bfm,
            Self::RbitW | Self::RbitX => O::Rbit,
            Self::AddLsl12W | Self::AddLsl12X => O::AddRIShift12,
            Self::MrsTpidrEl0 => O::Mrs,
            Self::FcvtSFromH => O::FcvtHS,
            Self::FcvtDFromH => O::FcvtHD,
            Self::FcvtHFromS => O::FcvtSH,
            Self::FcvtHFromD => O::FcvtDH,
        }
    }

    /// Lower-case query token, a unique substring of [`Self::obligation_name`].
    pub fn query(self) -> &'static str {
        match self {
            Self::MovW => "a64 decoded mov wd, wn",
            Self::MovX => "a64 decoded mov xd, xn",
            Self::MovXFromSp => "a64 decoded mov xd, sp",
            Self::MovWrr => "a64 decoded movwrr wd, wn",
            Self::MovXrr => "a64 decoded movxrr xd, xn",
            Self::MovWFromZr => "a64 decoded mov wd, wzr",
            Self::MovXFromZr => "a64 decoded mov xd, xzr",
            Self::MovWrrFromZr => "a64 decoded movwrr wd, zr",
            Self::MovXrrFromZr => "a64 decoded movxrr xd, zr",
            Self::FmovS => "a64 decoded fmov sd, sn",
            Self::FmovD => "a64 decoded fmov dd, dn",
            Self::FmovWFromS => "a64 decoded fmov wd, sn",
            Self::FmovXFromD => "a64 decoded fmov xd, dn",
            Self::FmovSFromW => "a64 decoded fmov sd, wn",
            Self::FmovDFromX => "a64 decoded fmov dd, xn",
            Self::FmovWFromH => "a64 decoded fmov wd, hn",
            Self::FmovHFromW => "a64 decoded fmov hd, wn",
            Self::MovV16B => "a64 decoded mov vd.16b, vn.16b",
            Self::Smull => "a64 decoded smull xd, wn, wm",
            Self::BfmInsertW => "a64 decoded bfm wd, wn insert",
            Self::BfmInsertX => "a64 decoded bfm xd, xn insert",
            Self::RbitW => "a64 decoded rbit wd, wn",
            Self::RbitX => "a64 decoded rbit xd, xn",
            Self::AddLsl12W => "a64 decoded add wd, wn, #imm12, lsl #12",
            Self::AddLsl12X => "a64 decoded add xd, xn, #imm12, lsl #12",
            Self::MrsTpidrEl0 => "a64 decoded mrs xt, tpidr_el0",
            Self::FcvtSFromH => "a64 decoded fcvt sd, hn",
            Self::FcvtDFromH => "a64 decoded fcvt dd, hn",
            Self::FcvtHFromS => "a64 decoded fcvt hd, sn",
            Self::FcvtHFromD => "a64 decoded fcvt hd, dn",
        }
    }

    /// The registered obligation's name.
    pub fn obligation_name(self) -> &'static str {
        match self {
            Self::MovW => {
                "A64 decoded MOV Wd, Wn (ORR Wd, WZR, Wm word) == Wn zero-extended: the W \
                 write clears Xd[63:32]"
            }
            Self::MovX => "A64 decoded MOV Xd, Xn (ORR Xd, XZR, Xm word) == Xn",
            Self::MovXFromSp => "A64 decoded MOV Xd, SP (ADD Xd, SP, #0 word) == SP",
            Self::MovWrr => {
                "A64 decoded MOVWrr Wd, Wn (ORR Wd, WZR, Wm word; the opcode fixes the W width) \
                 == Wn zero-extended: the W write clears Xd[63:32]"
            }
            Self::MovXrr => {
                "A64 decoded MOVXrr Xd, Xn (ORR Xd, XZR, Xm word; the opcode fixes the X width) \
                 == Xn"
            }
            Self::MovWFromZr => {
                "A64 decoded MOV Wd, WZR (ORR Wd, WZR, WZR word) == 0, the W write clears Xd[63:32]"
            }
            Self::MovXFromZr => "A64 decoded MOV Xd, XZR (ORR Xd, XZR, XZR word) == 0",
            Self::MovWrrFromZr => {
                "A64 decoded MOVWrr Wd, ZR (ORR Wd, WZR, WZR word; the opcode fixes the W width) \
                 == 0, the W write clears Xd[63:32]"
            }
            Self::MovXrrFromZr => {
                "A64 decoded MOVXrr Xd, ZR (ORR Xd, XZR, XZR word; the opcode fixes the X width) \
                 == 0"
            }
            Self::FmovS => "A64 decoded FMOV Sd, Sn word == Sn bits, Vd[127:32] zero",
            Self::FmovD => "A64 decoded FMOV Dd, Dn word == Dn bits, Vd[127:64] zero",
            Self::FmovWFromS => "A64 decoded FMOV Wd, Sn word == Sn bits, Xd[63:32] zero",
            Self::FmovXFromD => "A64 decoded FMOV Xd, Dn word == Dn bits",
            Self::FmovSFromW => "A64 decoded FMOV Sd, Wn word == Wn bits, Vd[127:32] zero",
            Self::FmovDFromX => "A64 decoded FMOV Dd, Xn word == Xn bits, Vd[127:64] zero",
            Self::FmovWFromH => {
                "A64 decoded FMOV Wd, Hn word (FEAT_FP16) == Hn bits, Xd[63:16] zero"
            }
            Self::FmovHFromW => {
                "A64 decoded FMOV Hd, Wn word (FEAT_FP16) == Wn[15:0], Vd[127:16] zero"
            }
            Self::MovV16B => {
                "A64 decoded MOV Vd.16B, Vn.16B (ORR Vd.16B, Vn.16B, Vn.16B word) == Vn, all 128 bits"
            }
            Self::Smull => {
                "A64 decoded SMULL Xd, Wn, Wm (SMADDL Xd, Wn, Wm, XZR word) == \
                 sext64(Wn) * sext64(Wm)"
            }
            Self::BfmInsertW => {
                "A64 decoded BFM Wd, Wn insert (immr = (32 - lsb) mod 32, imms = width - 1) == \
                 InsertBits(lsb, width), Xd[63:32] zero"
            }
            Self::BfmInsertX => {
                "A64 decoded BFM Xd, Xn insert (immr = (64 - lsb) mod 64, imms = width - 1) == \
                 InsertBits(lsb, width)"
            }
            Self::RbitW => "A64 decoded RBIT Wd, Wn word == SWAR bit reversal, Xd[63:32] zero",
            Self::RbitX => "A64 decoded RBIT Xd, Xn word == SWAR bit reversal",
            Self::AddLsl12W => {
                "A64 decoded ADD Wd, Wn, #imm12, LSL #12 word == Wn + imm12 * 4096, Xd[63:32] zero"
            }
            Self::AddLsl12X => "A64 decoded ADD Xd, Xn, #imm12, LSL #12 word == Xn + imm12 * 4096",
            Self::MrsTpidrEl0 => {
                "A64 decoded MRS Xt, TPIDR_EL0 word == the TPIDR_EL0 system register"
            }
            Self::FcvtSFromH => {
                "A64 decoded FCVT Sd, Hn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary16 -> binary32 convertFormat, exact, NaN quieted with its payload, \
                 Vd[127:32] zero"
            }
            Self::FcvtDFromH => {
                "A64 decoded FCVT Dd, Hn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary16 -> binary64 convertFormat, exact, NaN quieted with its payload, \
                 Vd[127:64] zero"
            }
            Self::FcvtHFromS => {
                "A64 decoded FCVT Hd, Sn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary32 -> binary16 convertFormat, roundTiesToEven, overflow to infinity, \
                 NaN quieted with its high payload, Vd[127:16] zero"
            }
            Self::FcvtHFromD => {
                "A64 decoded FCVT Hd, Dn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary64 -> binary16 convertFormat, roundTiesToEven, overflow to infinity, \
                 NaN quieted with its high payload, Vd[127:16] zero"
            }
        }
    }

    /// The proof category the obligation is registered under.
    pub fn category(self) -> ProofCategory {
        match self {
            Self::MovW
            | Self::MovX
            | Self::MovXFromSp
            | Self::MovWrr
            | Self::MovXrr
            | Self::MovWFromZr
            | Self::MovXFromZr
            | Self::MovWrrFromZr
            | Self::MovXrrFromZr
            | Self::BfmInsertW
            | Self::BfmInsertX
            | Self::RbitW
            | Self::RbitX => ProofCategory::BitwiseShift,
            // The ORR (vector) register copy registers beside the FMOV S/D
            // register copies: it is an FP/SIMD register move.
            Self::FmovS | Self::FmovD | Self::MovV16B => ProofCategory::FloatingPoint,
            Self::FmovWFromS
            | Self::FmovXFromD
            | Self::FmovSFromW
            | Self::FmovDFromX
            | Self::FmovWFromH
            | Self::FmovHFromW => ProofCategory::FpConversion,
            Self::Smull | Self::AddLsl12W | Self::AddLsl12X => ProofCategory::Arithmetic,
            Self::MrsTpidrEl0 => ProofCategory::AddressMode,
            Self::FcvtSFromH | Self::FcvtDFromH | Self::FcvtHFromS | Self::FcvtHFromD => {
                ProofCategory::FpConversion
            }
        }
    }

    /// The captured word the form's obligation is built from: the first
    /// corpus entry of this form.
    pub fn canonical(self) -> Option<&'static CapturedA64Word> {
        CAPTURED_A64_VALUE_WORDS
            .iter()
            .find(|entry| entry.form == self)
    }
}

/// The forms the coverage gate demands for an opcode, or `None` when the
/// opcode is not credited by decoded-word obligations.
pub fn a64_value_forms(opcode: AArch64Opcode) -> Option<&'static [A64ValueForm]> {
    use A64ValueForm as F;
    use AArch64Opcode as O;
    Some(match opcode {
        O::MovR => &[
            F::MovW,
            F::MovX,
            F::MovXFromSp,
            F::MovWFromZr,
            F::MovXFromZr,
        ],
        O::MOVWrr => &[F::MovWrr, F::MovWrrFromZr],
        O::MOVXrr => &[F::MovXrr, F::MovXrrFromZr],
        O::FmovFprFpr => &[F::FmovS, F::FmovD],
        O::FmovFprGpr => &[F::FmovWFromS, F::FmovXFromD, F::FmovWFromH],
        O::FmovGprFpr => &[F::FmovSFromW, F::FmovDFromX, F::FmovHFromW],
        O::NeonOrrV => &[F::MovV16B],
        O::Smull => &[F::Smull],
        O::Bfm => &[F::BfmInsertW, F::BfmInsertX],
        O::Rbit => &[F::RbitW, F::RbitX],
        O::AddRIShift12 => &[F::AddLsl12W, F::AddLsl12X],
        O::Mrs => &[F::MrsTpidrEl0],
        O::FcvtHS => &[F::FcvtSFromH],
        O::FcvtHD => &[F::FcvtDFromH],
        O::FcvtSH => &[F::FcvtHFromS],
        O::FcvtDH => &[F::FcvtHFromD],
        _ => return None,
    })
}

/// Opcodes the function verifier binds per instruction to their form's
/// registered obligation: every decoded-value opcode. A concrete instruction
/// binds only when its operands name one of the opcode's forms; any other
/// shape (a copy to SP or from the zero register, a half-precision or
/// cross-width FMOV, a malformed operand list) is refused and stays
/// `Unverified`, never an opcode-wide credit. The register copies were
/// credited as covered-elsewhere per instruction until L04-P11; they now need
/// their form's obligation like every other row here.
pub const A64_VALUE_OPCODES_BOUND_PER_INSTRUCTION: &[AArch64Opcode] = &[
    AArch64Opcode::MovR,
    AArch64Opcode::MOVWrr,
    AArch64Opcode::MOVXrr,
    AArch64Opcode::FmovFprFpr,
    AArch64Opcode::FmovFprGpr,
    AArch64Opcode::FmovGprFpr,
    AArch64Opcode::NeonOrrV,
    AArch64Opcode::Smull,
    AArch64Opcode::Bfm,
    AArch64Opcode::Rbit,
    AArch64Opcode::AddRIShift12,
    AArch64Opcode::Mrs,
    AArch64Opcode::FcvtHS,
    AArch64Opcode::FcvtHD,
    AArch64Opcode::FcvtSH,
    AArch64Opcode::FcvtDH,
];

// ===========================================================================
// Per-instance check (ENC-5)
// ===========================================================================

/// How a word was accepted for an instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64ValueVerdict {
    /// Exact bit-routing equality: the word writes the intended value for
    /// every register state.
    Exact,
    /// The word is an instance of this form; the form's registered value
    /// obligation carries the semantics.
    InstanceOf(A64ValueForm),
}

fn decode_refutation(refusal: A64DecodeRefusal) -> A64ValueCheckError {
    let class = match refusal {
        A64DecodeRefusal::NotModeled { .. } => A64RefusalClass::NotDecoded,
        A64DecodeRefusal::Unallocated { .. } => A64RefusalClass::Unallocated,
    };
    refuted(class, refusal.to_string())
}

fn denote_refutation(refusal: A64DenoteRefusal) -> A64ValueCheckError {
    let class = match refusal {
        A64DenoteRefusal::UnmodeledInstruction(_) => A64RefusalClass::UnmodeledInstruction,
        A64DenoteRefusal::UnmodeledSystemRegister(_) => A64RefusalClass::UnmodeledSystemRegister,
    };
    refuted(class, refusal.to_string())
}

/// Check that `word` is what `inst` claims, exactly.
///
/// This is the per-compile obligation ENC-5 runs on every emitted SMULL,
/// BFM, RBIT, `ADD #imm12, LSL #12`, MRS, MOV (register) and scalar FMOV.
/// Routing forms are decided for every register state; SMULL and the
/// shifted ADD must be an instance of their form's canonical word.
pub fn check_emitted_a64_value_word(
    inst: &MachInst,
    word: u32,
) -> Result<A64ValueVerdict, A64ValueCheckError> {
    let intent = a64_value_intent(inst)?;
    check_word_against_intent(&intent, word)
}

fn check_word_against_intent(
    intent: &A64ValueIntent,
    word: u32,
) -> Result<A64ValueVerdict, A64ValueCheckError> {
    let decoded = decode_a64_value_word(word).map_err(decode_refutation)?;
    if let A64Decision::InstanceOf {
        form,
        rd,
        rn,
        rm,
        imm12,
    } = intent.decision
    {
        let canonical = form
            .canonical()
            .ok_or_else(|| out_of_model(format!("{form:?} has no captured canonical word")))?;
        let canonical = decode_a64_value_word(canonical.word).map_err(decode_refutation)?;
        if let Some((class, detail)) = instance_mismatch(&canonical, &decoded, rd, rn, rm, imm12) {
            return Err(refuted(
                class,
                format!("not an instance of {form:?}: {detail}"),
            ));
        }
        return Ok(A64ValueVerdict::InstanceOf(form));
    }
    let effect =
        denote_a64_value_word(&decoded, &FieldOverrides::default()).map_err(denote_refutation)?;
    if effect.dest != intent.dest {
        return Err(refuted(
            A64RefusalClass::Destination,
            format!(
                "word writes {:?}, intent writes {:?}",
                effect.dest, intent.dest
            ),
        ));
    }
    if effect.writes_nzcv {
        return Err(refuted(A64RefusalClass::Flags, "word writes NZCV"));
    }
    if effect.dest == A64Dest::Discarded {
        return Ok(A64ValueVerdict::Exact);
    }
    match exact_routing_equality(&intent.value, &effect.value) {
        Some(Ok(())) => Ok(A64ValueVerdict::Exact),
        Some(Err(mismatch)) => Err(refuted(
            A64RefusalClass::Value,
            format!(
                "bit {} is {:?} in the intent but {:?} in the word",
                mismatch.bit, mismatch.intended, mismatch.emitted
            ),
        )),
        None => {
            // The word's effect is not a pure routing (it combines two
            // inputs, say). A counterexample refutes it; absent one, no
            // claim is made.
            let obligation = obligation_from_sides(
                "A64 decoded per-instance check".to_string(),
                intent.value.clone(),
                effect.value,
                Vec::new(),
            );
            match verify_by_evaluation_with_config(&obligation, &VerificationConfig::default()) {
                VerificationResult::Invalid { counterexample } => {
                    Err(refuted(A64RefusalClass::Value, counterexample))
                }
                _ => Err(out_of_model(
                    "equality is not decidable by exact routing and no counterexample was found",
                )),
            }
        }
    }
}

/// The first way `decoded` fails to be `canonical` with the intent's fields.
fn instance_mismatch(
    canonical: &A64ValueWord,
    decoded: &A64ValueWord,
    want_rd: u32,
    want_rn: u32,
    want_rm: u32,
    want_imm12: u32,
) -> Option<(A64RefusalClass, String)> {
    use A64RefusalClass::{Destination, Flags, Value};
    match (canonical, decoded) {
        (
            A64ValueWord::Dp3 {
                sf: csf,
                op54: c54,
                op31: c31,
                o0: co0,
                ra: cra,
                ..
            },
            A64ValueWord::Dp3 {
                sf,
                op54,
                op31,
                o0,
                ra,
                rd,
                rn,
                rm,
            },
        ) => {
            if (csf, c54, c31, co0, cra) != (sf, op54, op31, o0, ra) {
                return Some((
                    Value,
                    format!("sf/op54/op31/o0/Ra = {sf}/{op54}/{op31}/{o0}/{ra}"),
                ));
            }
            if *rd != want_rd {
                return Some((Destination, format!("Rd = {rd}, intent {want_rd}")));
            }
            if (*rn, *rm) != (want_rn, want_rm) {
                return Some((
                    Value,
                    format!("Rn/Rm = {rn}/{rm}, intent {want_rn}/{want_rm}"),
                ));
            }
            None
        }
        (
            A64ValueWord::AddSubImm {
                sf: csf,
                op: cop,
                s: cs,
                sh: csh,
                ..
            },
            A64ValueWord::AddSubImm {
                sf,
                op,
                s,
                sh,
                imm12,
                rn,
                rd,
            },
        ) => {
            if cs != s {
                return Some((Flags, format!("S = {s}")));
            }
            if (csf, cop, csh) != (sf, op, sh) {
                return Some((Value, format!("sf/op/sh = {sf}/{op}/{sh}")));
            }
            if *rd != want_rd {
                return Some((Destination, format!("Rd = {rd}, intent {want_rd}")));
            }
            if (*rn, *imm12) != (want_rn, want_imm12) {
                return Some((
                    Value,
                    format!("Rn/imm12 = {rn}/{imm12:#x}, intent {want_rn}/{want_imm12:#x}"),
                ));
            }
            None
        }
        (
            A64ValueWord::FpDp1 {
                ftype: cftype,
                opcode: copcode,
                ..
            },
            A64ValueWord::FpDp1 {
                ftype,
                opcode,
                rn,
                rd,
            },
        ) => {
            if (cftype, copcode) != (ftype, opcode) {
                return Some((Value, format!("ftype/opcode = {ftype:#04b}/{opcode:#08b}")));
            }
            if *rd != want_rd {
                return Some((Destination, format!("Rd = {rd}, intent {want_rd}")));
            }
            if *rn != want_rn {
                return Some((Value, format!("Rn = {rn}, intent {want_rn}")));
            }
            None
        }
        _ => Some((Value, format!("different instruction class {decoded:?}"))),
    }
}

// ===========================================================================
// Form obligations
// ===========================================================================

/// Every variable of `expr` with its width, in first-occurrence order.
fn collect_vars(expr: &SmtExpr, out: &mut Vec<(String, u32)>) {
    if let SmtExpr::Var { name, width } = expr {
        if !out.iter().any(|(existing, _)| existing == name) {
            out.push((name.clone(), *width));
        }
        return;
    }
    expr.for_each_child(&mut |child| collect_vars(child, out));
}

fn obligation_from_sides(
    name: String,
    source: SmtExpr,
    machine: SmtExpr,
    preconditions: Vec<SmtExpr>,
) -> ProofObligation {
    let mut inputs = Vec::new();
    collect_vars(&source, &mut inputs);
    collect_vars(&machine, &mut inputs);
    for precondition in &preconditions {
        collect_vars(precondition, &mut inputs);
    }
    ProofObligation {
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs,
        preconditions,
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// A deliberately wrong statement of a form's intent, used as a negative
/// control: the canonical word must refute it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64IntentMutation {
    /// SMULL claimed as the zero-extending UMULL product.
    SmullAsUnsigned,
    /// BFM claimed with `immr = lsb` instead of `(datasize - lsb) mod datasize`.
    BfmImmrEqualsLsb,
    /// The shifted ADD claimed without the `LSL #12`.
    AddWithoutShift,
    /// A W copy claimed to preserve `Xd[63:32]`.
    MovWKeepsUpperHalf,
    /// A half-precision FCVT claimed to round toward zero.
    FcvtRoundTowardZero,
    /// A half-precision FCVT claimed to round ties away from zero.
    FcvtRoundTiesAway,
    /// A half-precision FCVT claimed to return the default NaN (`FPCR.DN`).
    FcvtDefaultNan,
    /// A half-precision FCVT claimed to flush binary16 denormals (`FZ16`).
    FcvtFlushHalfDenormals,
    /// A half-precision FCVT claimed in the Arm alternative half-precision
    /// format (`FPCR.AHP`): a wrong binary16 FORMAT.
    FcvtAlternativeHalf,
}

impl A64IntentMutation {
    /// The IEEE claim an FCVT intent mutation states, or `None` for the
    /// mutations of other forms.
    fn fcvt_claim(self) -> Option<crate::aarch64_fcvt_half::IeeeClaim> {
        use crate::aarch64_fcvt_half::{ClaimNan, ClaimRounding, IeeeClaim};
        let correct = IeeeClaim::CORRECT;
        Some(match self {
            Self::FcvtRoundTowardZero => IeeeClaim {
                rounding: ClaimRounding::TowardZero,
                ..correct
            },
            Self::FcvtRoundTiesAway => IeeeClaim {
                rounding: ClaimRounding::TiesToAway,
                ..correct
            },
            Self::FcvtDefaultNan => IeeeClaim {
                nan: ClaimNan::Default,
                ..correct
            },
            Self::FcvtFlushHalfDenormals => IeeeClaim {
                flush_half_denormals: true,
                ..correct
            },
            Self::FcvtAlternativeHalf => IeeeClaim {
                alternative_half: true,
                ..correct
            },
            _ => return None,
        })
    }
}

/// Build `form`'s obligation for `word`, optionally against a mutated intent.
///
/// Routing and SMULL forms compare the canonical instruction's intent with
/// the decoded word. BFM quantifies over `(lsb, width)` and ADD over `imm12`:
/// the word supplies the class and fixed fields, and the immediate fields
/// become the isel formula's terms. A destination or flags difference is
/// refused structurally before any obligation exists.
pub fn a64_value_form_obligation_for(
    form: A64ValueForm,
    word: u32,
    mutation: Option<A64IntentMutation>,
) -> Result<ProofObligation, A64ValueCheckError> {
    let canonical = form
        .canonical()
        .ok_or_else(|| out_of_model(format!("{form:?} has no captured canonical word")))?;
    let intent = a64_value_intent(&canonical.inst())?;
    let decoded = decode_a64_value_word(word).map_err(decode_refutation)?;
    let name = form.obligation_name().to_string();
    let (source, overrides, preconditions) = match form {
        A64ValueForm::BfmInsertW | A64ValueForm::BfmInsertX => {
            bfm_symbolic_intent(canonical, mutation)?
        }
        A64ValueForm::AddLsl12W | A64ValueForm::AddLsl12X => {
            add_symbolic_intent(canonical, mutation)?
        }
        A64ValueForm::FcvtSFromH
        | A64ValueForm::FcvtDFromH
        | A64ValueForm::FcvtHFromS
        | A64ValueForm::FcvtHFromD => fcvt_symbolic_intent(form, canonical, mutation)?,
        A64ValueForm::Smull if mutation == Some(A64IntentMutation::SmullAsUnsigned) => {
            let [_, lhs, rhs] = operands::<3>(&canonical.inst())?;
            let (Operand::Gpr { name: n, .. }, Operand::Gpr { name: m, .. }) = (lhs, rhs) else {
                return Err(ill_formed("canonical SMULL operands"));
            };
            let zext32 = |x: SmtExpr| bv(0, 32).concat(x);
            (
                zext32(gpr_value(n, 32)).bvmul(zext32(gpr_value(m, 32))),
                FieldOverrides::default(),
                Vec::new(),
            )
        }
        A64ValueForm::MovW | A64ValueForm::MovWrr
            if mutation == Some(A64IntentMutation::MovWKeepsUpperHalf) =>
        {
            let [_, src] = operands::<2>(&canonical.inst())?;
            let Operand::Gpr { name, .. } = src else {
                return Err(ill_formed("canonical MOV operands"));
            };
            (gpr_value(name, 64), FieldOverrides::default(), Vec::new())
        }
        _ if mutation.is_some() => {
            return Err(out_of_model(format!(
                "intent mutation {mutation:?} does not apply to {form:?}"
            )));
        }
        _ => (intent.value.clone(), FieldOverrides::default(), Vec::new()),
    };
    let effect = denote_a64_value_word(&decoded, &overrides).map_err(denote_refutation)?;
    if effect.dest != intent.dest {
        return Err(refuted(
            A64RefusalClass::Destination,
            format!(
                "word writes {:?}, the form writes {:?}",
                effect.dest, intent.dest
            ),
        ));
    }
    if effect.writes_nzcv {
        return Err(refuted(A64RefusalClass::Flags, "word writes NZCV"));
    }
    Ok(obligation_from_sides(
        name,
        source,
        effect.value,
        preconditions,
    ))
}

/// `form`'s registered obligation, built from its canonical captured word.
pub fn a64_value_form_obligation(form: A64ValueForm) -> Option<ProofObligation> {
    let canonical = form.canonical()?;
    a64_value_form_obligation_for(form, canonical.word, None).ok()
}

/// Every form's registered obligation, in [`A64ValueForm::ALL`] order.
pub fn all_a64_value_decode_proofs() -> Vec<(ProofCategory, ProofObligation)> {
    A64ValueForm::ALL
        .iter()
        .filter_map(|&form| Some((form.category(), a64_value_form_obligation(form)?)))
        .collect()
}

type SymbolicIntent = (SmtExpr, FieldOverrides, Vec<SmtExpr>);

/// BFM over every bitfield-insert `(lsb, width)`: the source is the
/// InsertBits mask formula; the word's `immr`/`imms` fields become the isel
/// formula `immr = (datasize - lsb) mod datasize`, `imms = width - 1`.
fn bfm_symbolic_intent(
    canonical: &CapturedA64Word,
    mutation: Option<A64IntentMutation>,
) -> Result<SymbolicIntent, A64ValueCheckError> {
    let [dst, src, _, _] = operands::<4>(&canonical.inst())?;
    let (Operand::Gpr { width, name: d }, Operand::Gpr { name: n, .. }) = (dst, src) else {
        return Err(ill_formed("canonical BFM operands"));
    };
    let datasize = width;
    let index_bits = if datasize == 32 { 6 } else { 7 };
    let lsb = zext(SmtExpr::var("lsb", index_bits), datasize);
    let field_width = zext(SmtExpr::var("width", index_bits), datasize);
    let one = bv(1, datasize);
    let mask = one.clone().bvshl(field_width.clone()).bvsub(one.clone());
    let dst_value = gpr_value(d, datasize);
    let insert = dst_value
        .bvand(mask.clone().bvshl(lsb.clone()).bvxor(all_ones(datasize)))
        .bvor(gpr_value(n, datasize).bvand(mask).bvshl(lsb.clone()));
    let levels = bv(u64::from(datasize - 1), datasize);
    let immr_formula = match mutation {
        Some(A64IntentMutation::BfmImmrEqualsLsb) => lsb.clone().bvand(levels),
        None => bv(u64::from(datasize), datasize)
            .bvsub(lsb.clone())
            .bvand(levels),
        Some(other) => {
            return Err(out_of_model(format!(
                "intent mutation {other:?} does not apply to BFM"
            )));
        }
    };
    let overrides = FieldOverrides {
        immr: Some(immr_formula.extract(5, 0)),
        imms: Some(field_width.clone().bvsub(one).extract(5, 0)),
        ..FieldOverrides::default()
    };
    let preconditions = vec![
        bv(0, datasize).bvult(field_width.clone()),
        lsb.bvadd(field_width)
            .bvule(bv(u64::from(datasize), datasize)),
    ];
    Ok((intent_gpr_write(insert), overrides, preconditions))
}

/// `ADD #imm12, LSL #12` over every `imm12`: the source multiplies by 4096.
fn add_symbolic_intent(
    canonical: &CapturedA64Word,
    mutation: Option<A64IntentMutation>,
) -> Result<SymbolicIntent, A64ValueCheckError> {
    let [dst, src, _] = operands::<3>(&canonical.inst())?;
    let (Operand::Gpr { width, .. }, Operand::Gpr { name: n, .. }) = (dst, src) else {
        return Err(ill_formed("canonical ADD operands"));
    };
    let imm12 = SmtExpr::var("imm12", 12);
    let scale = match mutation {
        Some(A64IntentMutation::AddWithoutShift) => 1,
        None => 4096,
        Some(other) => {
            return Err(out_of_model(format!(
                "intent mutation {other:?} does not apply to ADD"
            )));
        }
    };
    let source = gpr_value(n, width).bvadd(zext(imm12.clone(), width).bvmul(bv(scale, width)));
    let overrides = FieldOverrides {
        imm12: Some(imm12),
        ..FieldOverrides::default()
    };
    Ok((intent_gpr_write(source), overrides, Vec::new()))
}

/// A half-precision FCVT over its whole source scalar: the intent is IEEE
/// `convertFormat` (or the mutated claim) of a fresh `bits`-wide variable,
/// which also stands for the word's source register when the word reads the
/// canonical register at the canonical width. The obligation's only input is
/// then that scalar, so the widening forms are evaluated exhaustively.
fn fcvt_symbolic_intent(
    form: A64ValueForm,
    canonical: &CapturedA64Word,
    mutation: Option<A64IntentMutation>,
) -> Result<SymbolicIntent, A64ValueCheckError> {
    use crate::aarch64_fcvt_half::{IeeeClaim, ieee_convert_format_with};
    let conv = form
        .half_conversion()
        .ok_or_else(|| out_of_model(format!("{form:?} is not an FCVT form")))?;
    let [_, src] = operands::<2>(&canonical.inst())?;
    let Operand::Fpr { num: n, .. } = src else {
        return Err(ill_formed("canonical FCVT operands"));
    };
    let claim = match mutation {
        None => IeeeClaim::CORRECT,
        Some(other) => other.fcvt_claim().ok_or_else(|| {
            out_of_model(format!(
                "intent mutation {other:?} does not apply to {form:?}"
            ))
        })?,
    };
    let bits = conv.source().bits();
    let scalar = SmtExpr::var(fcvt_source_name(conv, n), bits);
    let overrides = FieldOverrides {
        fp_source: Some(FpSourceOverride {
            rn: u32::from(n),
            bits,
            value: scalar.clone(),
        }),
        ..FieldOverrides::default()
    };
    Ok((
        intent_fpr_write(ieee_convert_format_with(conv, &scalar, claim)),
        overrides,
        Vec::new(),
    ))
}

/// The name of the symbolic source scalar of an FCVT obligation reading
/// `V<n>`: `h7`, `s7` or `d7`.
fn fcvt_source_name(conv: crate::aarch64_fcvt_half::HalfConversion, n: u8) -> String {
    let prefix = match conv.source().bits() {
        16 => 'h',
        32 => 's',
        _ => 'd',
    };
    format!("{prefix}{n}")
}

/// Evaluate both sides of an FCVT obligation on the structured boundary
/// battery of its conversion, every other input held at a fixed pattern. A
/// difference refutes for [`A64RefusalClass::Value`]. This reaches the exact
/// ties random sampling of a binary32/binary64 source almost never draws.
fn fcvt_battery_check(
    conv: crate::aarch64_fcvt_half::HalfConversion,
    source_name: &str,
    obligation: &ProofObligation,
) -> Result<usize, A64ValueCheckError> {
    use crate::smt::EvalEnv;
    let bits = conv.source().bits();
    let Some(source) = obligation
        .inputs
        .iter()
        .position(|(name, width)| *width == bits && name == source_name)
    else {
        return Err(out_of_model(
            "FCVT obligation without its source scalar input",
        ));
    };
    let mut env = EvalEnv::default();
    for (name, _) in &obligation.inputs {
        env.insert(name.clone(), 0x5A5A_5A5A_5A5A_5A5A);
    }
    let battery = crate::aarch64_fcvt_half::half_conversion_battery(conv);
    for &x in &battery {
        env.set_at(source, x);
        let intent = obligation.trust_ir_expr.try_eval(&env);
        let word = obligation.aarch64_expr.try_eval(&env);
        match (intent, word) {
            (Ok(intent), Ok(word)) if intent == word => {}
            (Ok(intent), Ok(word)) => {
                return Err(refuted(
                    A64RefusalClass::Value,
                    format!("source {x:#x}: intent {intent:?}, word {word:?}"),
                ));
            }
            (intent, word) => {
                return Err(out_of_model(format!(
                    "FCVT battery evaluation failed at {x:#x}: {intent:?} / {word:?}"
                )));
            }
        }
    }
    Ok(battery.len())
}

/// How a form obligation was accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64FormDecision {
    /// Exact routing equality, for every register state.
    Exact,
    /// Accepted by the evaluator (default: sampled, not a proof).
    Evaluated,
}

/// Decide a form obligation: exactly when both sides are routings,
/// otherwise by the evaluator. A counterexample refutes for [`A64RefusalClass::Value`].
pub fn decide_a64_value_form(
    form: A64ValueForm,
    word: u32,
    mutation: Option<A64IntentMutation>,
    config: &VerificationConfig,
) -> Result<A64FormDecision, A64ValueCheckError> {
    let obligation = a64_value_form_obligation_for(form, word, mutation)?;
    if let Some(conv) = form.half_conversion()
        && !conv.widens()
    {
        let canonical = form
            .canonical()
            .ok_or_else(|| out_of_model(format!("{form:?} has no captured canonical word")))?;
        let [_, src] = operands::<2>(&canonical.inst())?;
        let Operand::Fpr { num: n, .. } = src else {
            return Err(ill_formed("canonical FCVT operands"));
        };
        fcvt_battery_check(conv, &fcvt_source_name(conv, n), &obligation)?;
    }
    if obligation.preconditions.is_empty()
        && let Some(decision) =
            exact_routing_equality(&obligation.trust_ir_expr, &obligation.aarch64_expr)
    {
        return decision
            .map(|()| A64FormDecision::Exact)
            .map_err(|mismatch| {
                refuted(
                    A64RefusalClass::Value,
                    format!(
                        "bit {} is {:?} in the intent but {:?} in the word",
                        mismatch.bit, mismatch.intended, mismatch.emitted
                    ),
                )
            });
    }
    match verify_by_evaluation_with_config(&obligation, config) {
        VerificationResult::Valid => Ok(A64FormDecision::Evaluated),
        VerificationResult::Invalid { counterexample } => {
            Err(refuted(A64RefusalClass::Value, counterexample))
        }
        VerificationResult::Unknown { reason } => Err(out_of_model(format!(
            "evaluator returned Unknown: {reason}"
        ))),
    }
}

// ===========================================================================
// Negative controls and the coverage-gate credit hook
// ===========================================================================

/// How a negative control departs from the canonical form.
#[derive(Debug, Clone, Copy)]
pub enum A64ControlMutation {
    /// Replace the canonical word by a mutated word.
    Word(fn(u32) -> u32),
    /// Keep the word; state a wrong intent.
    Intent(A64IntentMutation),
}

/// One negative control: it must be refuted, for exactly `expected`.
#[derive(Debug, Clone, Copy)]
pub struct A64ValueControl {
    pub form: A64ValueForm,
    pub label: &'static str,
    pub mutation: A64ControlMutation,
    pub expected: A64RefusalClass,
}

/// Replace bits `hi:lo` of `word` with `value`.
const fn set_field(word: u32, hi: u32, lo: u32, value: u32) -> u32 {
    let mask = (u32::MAX >> (31 - (hi - lo))) << lo;
    (word & !mask) | ((value << lo) & mask)
}

/// The negative-control battery. Each form has at least one control refuted
/// for [`A64RefusalClass::Value`]; the credit hook requires every control to be
/// refuted for its stated class.
pub fn a64_value_controls() -> Vec<A64ValueControl> {
    use A64ControlMutation::{Intent, Word};
    use A64IntentMutation as M;
    use A64RefusalClass::{
        Destination, Flags, NotDecoded, Unallocated, UnmodeledInstruction, UnmodeledSystemRegister,
        Value,
    };
    use A64ValueForm as F;
    let c = |form, label, mutation, expected| A64ValueControl {
        form,
        label,
        mutation,
        expected,
    };
    vec![
        // MOV (register), W and X.
        c(
            F::MovW,
            "sf=1: an X-width ORR leaves Xd[63:32] = Xn[63:32] (W-write zero extension)",
            Word(|w| set_field(w, 31, 31, 1)),
            Value,
        ),
        c(
            F::MovW,
            "the W copy claimed to keep Xd[63:32]",
            Intent(M::MovWKeepsUpperHalf),
            Value,
        ),
        c(
            F::MovW,
            "Rn=W5 instead of WZR: ORR merges a second register",
            Word(|w| set_field(w, 9, 5, 5)),
            Value,
        ),
        c(
            F::MovW,
            "N=1: ORN writes the complement",
            Word(|w| set_field(w, 21, 21, 1)),
            Value,
        ),
        c(
            F::MovW,
            "LSL #1 shifts the source",
            Word(|w| set_field(w, 15, 10, 1)),
            Value,
        ),
        c(
            F::MovW,
            "opc=00: AND with WZR writes zero",
            Word(|w| set_field(w, 30, 29, 0b00)),
            Value,
        ),
        c(
            F::MovW,
            "Rm=W8: wrong source register",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovW,
            "Rd=W4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::MovW,
            "opc=11: ANDS writes NZCV",
            Word(|w| set_field(w, 30, 29, 0b11)),
            Flags,
        ),
        c(
            F::MovX,
            "sf=0: a W-width ORR clears Xd[63:32]",
            Word(|w| set_field(w, 31, 31, 0)),
            Value,
        ),
        c(
            F::MovX,
            "N=1: ORN writes the complement",
            Word(|w| set_field(w, 21, 21, 1)),
            Value,
        ),
        c(
            F::MovX,
            "Rd=X4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        // MOV Xd, SP: register 31 is SP only in ADD (immediate).
        c(
            F::MovXFromSp,
            "ORR Xd, XZR, X31: register 31 in ORR is XZR, not SP",
            Word(|w| 0xAA1F_03E0 | (w & 0x1F)),
            Value,
        ),
        c(
            F::MovXFromSp,
            "ADD #1",
            Word(|w| set_field(w, 21, 10, 1)),
            Value,
        ),
        c(
            F::MovXFromSp,
            "sf=0: a 32-bit ADD clears Xd[63:32]",
            Word(|w| set_field(w, 31, 31, 0)),
            Value,
        ),
        c(
            F::MovXFromSp,
            "S=1: ADDS writes NZCV",
            Word(|w| set_field(w, 29, 29, 1)),
            Flags,
        ),
        // The typed post-allocation copies: the opcode's width must be the
        // word's width whatever view the allocator left on the operands.
        c(
            F::MovWrr,
            "sf=1: an X-width ORR leaves Xd[63:32] = Xn[63:32] (MOVWrr fixes W)",
            Word(|w| set_field(w, 31, 31, 1)),
            Value,
        ),
        c(
            F::MovWrr,
            "the MOVWrr copy claimed to keep Xd[63:32]",
            Intent(M::MovWKeepsUpperHalf),
            Value,
        ),
        c(
            F::MovWrr,
            "Rn=W5 instead of WZR: ORR merges a second register",
            Word(|w| set_field(w, 9, 5, 5)),
            Value,
        ),
        c(
            F::MovWrr,
            "N=1: ORN writes the complement",
            Word(|w| set_field(w, 21, 21, 1)),
            Value,
        ),
        c(
            F::MovWrr,
            "Rm=W8: wrong source register",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovWrr,
            "Rd=W4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::MovWrr,
            "opc=11: ANDS writes NZCV",
            Word(|w| set_field(w, 30, 29, 0b11)),
            Flags,
        ),
        c(
            F::MovXrr,
            "sf=0: a W-width ORR clears Xd[63:32] (MOVXrr fixes X)",
            Word(|w| set_field(w, 31, 31, 0)),
            Value,
        ),
        c(
            F::MovXrr,
            "LSL #1 shifts the source",
            Word(|w| set_field(w, 15, 10, 1)),
            Value,
        ),
        c(
            F::MovXrr,
            "Rm=X8: wrong source register",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovXrr,
            "Rd=X4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::MovXrr,
            "opc=11: ANDS writes NZCV",
            Word(|w| set_field(w, 30, 29, 0b11)),
            Flags,
        ),
        c(
            F::MovWFromZr,
            "Rm=W8 instead of ZR: the word copies a register, not zero",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovWFromZr,
            "Rn=W5 instead of ZR: ORR merges a register into the zero",
            Word(|w| set_field(w, 9, 5, 5)),
            Value,
        ),
        c(
            F::MovWFromZr,
            "N=1: ORN of zero writes all ones",
            Word(|w| set_field(w, 21, 21, 1)),
            Value,
        ),
        c(
            F::MovWFromZr,
            "Rd=W4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::MovWFromZr,
            "opc=11: ANDS writes NZCV",
            Word(|w| set_field(w, 30, 29, 0b11)),
            Flags,
        ),
        c(
            F::MovXFromZr,
            "Rm=X8 instead of ZR: the word copies a register, not zero",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovXFromZr,
            "Rn=X5 instead of ZR: ORR merges a register into the zero",
            Word(|w| set_field(w, 9, 5, 5)),
            Value,
        ),
        c(
            F::MovXFromZr,
            "N=1: ORN of zero writes all ones",
            Word(|w| set_field(w, 21, 21, 1)),
            Value,
        ),
        c(
            F::MovXFromZr,
            "Rd=X4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::MovXFromZr,
            "opc=11: ANDS writes NZCV",
            Word(|w| set_field(w, 30, 29, 0b11)),
            Flags,
        ),
        c(
            F::MovWrrFromZr,
            "Rm=W8 instead of ZR: the word copies a register, not zero",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovWrrFromZr,
            "Rn=W5 instead of ZR: ORR merges a register into the zero",
            Word(|w| set_field(w, 9, 5, 5)),
            Value,
        ),
        c(
            F::MovWrrFromZr,
            "N=1: ORN of zero writes all ones",
            Word(|w| set_field(w, 21, 21, 1)),
            Value,
        ),
        c(
            F::MovWrrFromZr,
            "Rd=W4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::MovWrrFromZr,
            "opc=11: ANDS writes NZCV",
            Word(|w| set_field(w, 30, 29, 0b11)),
            Flags,
        ),
        c(
            F::MovXrrFromZr,
            "Rm=X8 instead of ZR: the word copies a register, not zero",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovXrrFromZr,
            "Rn=X5 instead of ZR: ORR merges a register into the zero",
            Word(|w| set_field(w, 9, 5, 5)),
            Value,
        ),
        c(
            F::MovXrrFromZr,
            "N=1: ORN of zero writes all ones",
            Word(|w| set_field(w, 21, 21, 1)),
            Value,
        ),
        c(
            F::MovXrrFromZr,
            "Rd=X4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::MovXrrFromZr,
            "opc=11: ANDS writes NZCV",
            Word(|w| set_field(w, 30, 29, 0b11)),
            Flags,
        ),
        c(
            F::FmovWFromH,
            "ftype=00: FMOV Wd, Sn moves 32 bits, not 16",
            Word(|w| set_field(w, 23, 22, 0b00)),
            Value,
        ),
        c(
            F::FmovWFromH,
            "Rn=H8: wrong source register",
            Word(|w| set_field(w, 9, 5, 8)),
            Value,
        ),
        c(
            F::FmovWFromH,
            "Rd=W4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::FmovWFromH,
            "opcode=111: FMOV Hd, Wn moves the other way",
            Word(|w| set_field(w, 18, 16, 0b111)),
            Destination,
        ),
        c(
            F::FmovHFromW,
            "ftype=00: FMOV Sd, Wn moves 32 bits, not 16",
            Word(|w| set_field(w, 23, 22, 0b00)),
            Value,
        ),
        c(
            F::FmovHFromW,
            "Rn=W8: wrong source register",
            Word(|w| set_field(w, 9, 5, 8)),
            Value,
        ),
        c(
            F::FmovHFromW,
            "Rd=H4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::FmovHFromW,
            "opcode=110: FMOV Wd, Hn moves the other way",
            Word(|w| set_field(w, 18, 16, 0b110)),
            Destination,
        ),
        c(
            F::MovV16B,
            "Rm=V8: ORR merges a second register",
            Word(|w| set_field(w, 20, 16, 8)),
            Value,
        ),
        c(
            F::MovV16B,
            "Rn=V8: ORR merges a second register",
            Word(|w| set_field(w, 9, 5, 8)),
            Value,
        ),
        c(
            F::MovV16B,
            "Q=0: the 8B move copies 64 bits and clears Vd[127:64]",
            Word(|w| set_field(w, 30, 30, 0)),
            Value,
        ),
        c(
            F::MovV16B,
            "size=11: ORN of a register with itself writes all ones",
            Word(|w| set_field(w, 23, 22, 0b11)),
            Value,
        ),
        c(
            F::MovV16B,
            "size=01: BIC of a register with itself writes zero",
            Word(|w| set_field(w, 23, 22, 0b01)),
            Value,
        ),
        c(
            F::MovV16B,
            "U=1, size=00: EOR of a register with itself writes zero",
            Word(|w| set_field(set_field(w, 29, 29, 1), 23, 22, 0b00)),
            Value,
        ),
        c(
            F::MovV16B,
            "Rd=V4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        // FMOV (register).
        c(
            F::FmovS,
            "ftype=01: FMOV Dd copies 64 bits",
            Word(|w| set_field(w, 23, 22, 0b01)),
            Value,
        ),
        c(
            F::FmovS,
            "ftype=11: FMOV Hd copies 16 bits",
            Word(|w| set_field(w, 23, 22, 0b11)),
            Value,
        ),
        c(
            F::FmovS,
            "FABS clears the sign bit",
            Word(|w| set_field(w, 20, 15, 0b000001)),
            Value,
        ),
        c(
            F::FmovS,
            "FNEG flips the sign bit",
            Word(|w| set_field(w, 20, 15, 0b000010)),
            Value,
        ),
        c(
            F::FmovS,
            "FSQRT is not a move",
            Word(|w| set_field(w, 20, 15, 0b000011)),
            UnmodeledInstruction,
        ),
        c(
            F::FmovS,
            "Rn=S8: wrong source register",
            Word(|w| set_field(w, 9, 5, 8)),
            Value,
        ),
        c(
            F::FmovS,
            "Rd=S4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::FmovD,
            "ftype=00: FMOV Sd drops Dn[63:32]",
            Word(|w| set_field(w, 23, 22, 0b00)),
            Value,
        ),
        c(
            F::FmovD,
            "FABS clears the sign bit",
            Word(|w| set_field(w, 20, 15, 0b000001)),
            Value,
        ),
        // FMOV (general), both directions: bank, direction and width.
        c(
            F::FmovWFromS,
            "opcode 111: FMOV Sd, Wn moves the other way",
            Word(|w| set_field(w, 18, 16, 0b111)),
            Destination,
        ),
        c(
            F::FmovWFromS,
            "ftype=11: FMOV Wd, Hn moves 16 bits",
            Word(|w| set_field(w, 23, 22, 0b11)),
            Value,
        ),
        c(
            F::FmovWFromS,
            "sf=1, ftype=01: FMOV Xd, Dn moves 64 bits",
            Word(|w| set_field(set_field(w, 31, 31, 1), 23, 22, 0b01)),
            Value,
        ),
        c(
            F::FmovWFromS,
            "sf=1 with ftype=00: no FMOV Xd, Sn exists (cross-class width)",
            Word(|w| set_field(w, 31, 31, 1)),
            Unallocated,
        ),
        c(
            F::FmovWFromS,
            "opcode 010: SCVTF converts, it does not move bits",
            Word(|w| set_field(w, 18, 16, 0b010)),
            NotDecoded,
        ),
        c(
            F::FmovXFromD,
            "opcode 111: FMOV Dd, Xn moves the other way",
            Word(|w| set_field(w, 18, 16, 0b111)),
            Destination,
        ),
        c(
            F::FmovXFromD,
            "sf=0, ftype=00: FMOV Wd, Sn moves 32 bits",
            Word(|w| set_field(set_field(w, 31, 31, 0), 23, 22, 0b00)),
            Value,
        ),
        c(
            F::FmovXFromD,
            "sf=0 with ftype=01: no FMOV Wd, Dn exists (cross-class width)",
            Word(|w| set_field(w, 31, 31, 0)),
            Unallocated,
        ),
        c(
            F::FmovSFromW,
            "opcode 110: FMOV Wd, Sn moves the other way",
            Word(|w| set_field(w, 18, 16, 0b110)),
            Destination,
        ),
        c(
            F::FmovSFromW,
            "ftype=11: FMOV Hd, Wn moves 16 bits",
            Word(|w| set_field(w, 23, 22, 0b11)),
            Value,
        ),
        c(
            F::FmovSFromW,
            "sf=1 with ftype=00: no FMOV Sd, Xn exists (cross-class width)",
            Word(|w| set_field(w, 31, 31, 1)),
            Unallocated,
        ),
        c(
            F::FmovDFromX,
            "opcode 110: FMOV Xd, Dn moves the other way",
            Word(|w| set_field(w, 18, 16, 0b110)),
            Destination,
        ),
        c(
            F::FmovDFromX,
            "sf=0, ftype=00: FMOV Sd, Wn moves 32 bits",
            Word(|w| set_field(set_field(w, 31, 31, 0), 23, 22, 0b00)),
            Value,
        ),
        c(
            F::FmovDFromX,
            "sf=0 with ftype=01: no FMOV Dd, Wn exists (cross-class width)",
            Word(|w| set_field(w, 31, 31, 0)),
            Unallocated,
        ),
        // SMULL: signed, widening, no accumulate.
        c(
            F::Smull,
            "U=1: the UMULL word zero-extends",
            Word(|w| set_field(w, 23, 23, 1)),
            Value,
        ),
        c(
            F::Smull,
            "SMULL claimed as the unsigned UMULL product (no inheritance)",
            Intent(M::SmullAsUnsigned),
            Value,
        ),
        c(
            F::Smull,
            "o0=1: SMSUBL negates the product",
            Word(|w| set_field(w, 15, 15, 1)),
            Value,
        ),
        c(
            F::Smull,
            "Ra=X5: SMADDL accumulates X5",
            Word(|w| set_field(w, 14, 10, 5)),
            Value,
        ),
        c(
            F::Smull,
            "op31=000: 64-bit MADD multiplies the full registers",
            Word(|w| set_field(w, 23, 21, 0b000)),
            Value,
        ),
        c(
            F::Smull,
            "sf=0: a 32-bit SMADDL is unallocated",
            Word(|w| set_field(w, 31, 31, 0)),
            Unallocated,
        ),
        c(
            F::Smull,
            "Rd=X4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        // BFM insert: read-modify-write, and the isel immediate formula.
        c(
            F::BfmInsertW,
            "opc=10: UBFM zeroes the bits BFM preserves",
            Word(|w| set_field(w, 30, 29, 0b10)),
            Value,
        ),
        c(
            F::BfmInsertW,
            "opc=00: SBFM sign-fills the bits BFM preserves",
            Word(|w| set_field(w, 30, 29, 0b00)),
            Value,
        ),
        c(
            F::BfmInsertW,
            "immr = lsb instead of (32 - lsb) mod 32",
            Intent(M::BfmImmrEqualsLsb),
            Value,
        ),
        c(
            F::BfmInsertW,
            "N=1 with sf=0 is reserved",
            Word(|w| set_field(w, 22, 22, 1)),
            Unallocated,
        ),
        c(
            F::BfmInsertW,
            "Rd=W4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::BfmInsertX,
            "opc=10: UBFM zeroes the bits BFM preserves",
            Word(|w| set_field(w, 30, 29, 0b10)),
            Value,
        ),
        c(
            F::BfmInsertX,
            "immr = lsb instead of (64 - lsb) mod 64",
            Intent(M::BfmImmrEqualsLsb),
            Value,
        ),
        c(
            F::BfmInsertX,
            "sf=0 with N=1 is reserved",
            Word(|w| set_field(w, 31, 31, 0)),
            Unallocated,
        ),
        // RBIT.
        c(
            F::RbitW,
            "opcode 000010: REV reverses bytes, not bits",
            Word(|w| set_field(w, 15, 10, 0b000010)),
            Value,
        ),
        c(
            F::RbitW,
            "opcode 000001: REV16 swaps bytes in halfwords",
            Word(|w| set_field(w, 15, 10, 0b000001)),
            Value,
        ),
        c(
            F::RbitW,
            "sf=1: a 64-bit RBIT reverses into the upper half",
            Word(|w| set_field(w, 31, 31, 1)),
            Value,
        ),
        c(
            F::RbitW,
            "opcode 000100: CLZ counts bits",
            Word(|w| set_field(w, 15, 10, 0b000100)),
            UnmodeledInstruction,
        ),
        c(
            F::RbitX,
            "opcode 000011: REV reverses bytes, not bits",
            Word(|w| set_field(w, 15, 10, 0b000011)),
            Value,
        ),
        c(
            F::RbitX,
            "sf=0: a 32-bit RBIT clears Xd[63:32]",
            Word(|w| set_field(w, 31, 31, 0)),
            Value,
        ),
        // ADD #imm12, LSL #12.
        c(
            F::AddLsl12W,
            "sh=0: the LSL #12 is dropped",
            Word(|w| set_field(w, 22, 22, 0)),
            Value,
        ),
        c(
            F::AddLsl12W,
            "the shifted ADD claimed without its LSL #12",
            Intent(M::AddWithoutShift),
            Value,
        ),
        c(
            F::AddLsl12W,
            "op=1: SUB",
            Word(|w| set_field(w, 30, 30, 1)),
            Value,
        ),
        c(
            F::AddLsl12W,
            "S=1: ADDS writes NZCV",
            Word(|w| set_field(w, 29, 29, 1)),
            Flags,
        ),
        c(
            F::AddLsl12W,
            "sf=1: a 64-bit ADD keeps the carry out of bit 31",
            Word(|w| set_field(w, 31, 31, 1)),
            Value,
        ),
        c(
            F::AddLsl12X,
            "sh=0: the LSL #12 is dropped",
            Word(|w| set_field(w, 22, 22, 0)),
            Value,
        ),
        c(
            F::AddLsl12X,
            "the shifted ADD claimed without its LSL #12",
            Intent(M::AddWithoutShift),
            Value,
        ),
        c(
            F::AddLsl12X,
            "sf=0: a 32-bit ADD clears Xd[63:32]",
            Word(|w| set_field(w, 31, 31, 0)),
            Value,
        ),
        c(
            F::AddLsl12X,
            "Rd=X4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        // MRS TPIDR_EL0: system-register selection.
        c(
            F::MrsTpidrEl0,
            "op2=3: TPIDRRO_EL0 is the read-only thread pointer",
            Word(|w| set_field(w, 7, 5, 3)),
            Value,
        ),
        c(
            F::MrsTpidrEl0,
            "op1=0, op2=4: TPIDR_EL1 is the kernel thread pointer",
            Word(|w| set_field(set_field(w, 18, 16, 0), 7, 5, 4)),
            Value,
        ),
        c(
            F::MrsTpidrEl0,
            "L=0: MSR writes the system register",
            Word(|w| set_field(w, 21, 21, 0)),
            Destination,
        ),
        c(
            F::MrsTpidrEl0,
            "CRn=12: a system register outside the modeled file",
            Word(|w| set_field(w, 15, 12, 12)),
            UnmodeledSystemRegister,
        ),
        c(
            F::MrsTpidrEl0,
            "Rt=X4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        // FCVT Sd, Hn: direction, destination format, the binary16 format
        // itself, NaN propagation and denormal handling.
        c(
            F::FcvtSFromH,
            "opc=01: FCVT Dd, Hn writes a binary64 (wrong destination format)",
            Word(|w| set_field(w, 16, 15, 0b01)),
            Value,
        ),
        c(
            F::FcvtSFromH,
            "ftype=00, opc=11: FCVT Hd, Sn converts the other way (wrong direction)",
            Word(|w| set_field(set_field(w, 23, 22, 0b00), 16, 15, 0b11)),
            Value,
        ),
        c(
            F::FcvtSFromH,
            "ftype=00: FCVT Sd, Sn to its own precision is unallocated",
            Word(|w| set_field(w, 23, 22, 0b00)),
            Unallocated,
        ),
        c(
            F::FcvtSFromH,
            "opcode 000000: FMOV Hd, Hn copies the bits instead of converting",
            Word(|w| set_field(w, 20, 15, 0)),
            Value,
        ),
        c(
            F::FcvtSFromH,
            "Rn=H8: wrong source register",
            Word(|w| set_field(w, 9, 5, 8)),
            Value,
        ),
        c(
            F::FcvtSFromH,
            "Rd=S4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::FcvtSFromH,
            "the default NaN claimed (FPCR.DN=1): the payload is propagated",
            Intent(M::FcvtDefaultNan),
            Value,
        ),
        c(
            F::FcvtSFromH,
            "binary16 denormals claimed flushed (FZ16): FCVT keeps them",
            Intent(M::FcvtFlushHalfDenormals),
            Value,
        ),
        c(
            F::FcvtSFromH,
            "the alternative half-precision format claimed (FPCR.AHP=1): wrong source format",
            Intent(M::FcvtAlternativeHalf),
            Value,
        ),
        // FCVT Dd, Hn.
        c(
            F::FcvtDFromH,
            "opc=00: FCVT Sd, Hn writes a binary32 (wrong destination format)",
            Word(|w| set_field(w, 16, 15, 0b00)),
            Value,
        ),
        c(
            F::FcvtDFromH,
            "ftype=01, opc=11: FCVT Hd, Dn converts the other way (wrong direction)",
            Word(|w| set_field(set_field(w, 23, 22, 0b01), 16, 15, 0b11)),
            Value,
        ),
        c(
            F::FcvtDFromH,
            "ftype=01: FCVT Dd, Dn to its own precision is unallocated",
            Word(|w| set_field(w, 23, 22, 0b01)),
            Unallocated,
        ),
        c(
            F::FcvtDFromH,
            "Rd=D4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        c(
            F::FcvtDFromH,
            "the default NaN claimed (FPCR.DN=1): the payload is propagated",
            Intent(M::FcvtDefaultNan),
            Value,
        ),
        c(
            F::FcvtDFromH,
            "binary16 denormals claimed flushed (FZ16): FCVT keeps them",
            Intent(M::FcvtFlushHalfDenormals),
            Value,
        ),
        c(
            F::FcvtDFromH,
            "the alternative half-precision format claimed (FPCR.AHP=1): wrong source format",
            Intent(M::FcvtAlternativeHalf),
            Value,
        ),
        // FCVT Hd, Sn: rounding direction, format and direction.
        c(
            F::FcvtHFromS,
            "round toward zero claimed: FCVT rounds to nearest, ties to even",
            Intent(M::FcvtRoundTowardZero),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "ties away from zero claimed: FCVT breaks ties to even",
            Intent(M::FcvtRoundTiesAway),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "the alternative half-precision format claimed (FPCR.AHP=1): wrong result format",
            Intent(M::FcvtAlternativeHalf),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "the default NaN claimed (FPCR.DN=1): the high payload is propagated",
            Intent(M::FcvtDefaultNan),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "binary16 denormal results claimed flushed (FZ16): FCVT keeps them",
            Intent(M::FcvtFlushHalfDenormals),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "ftype=11, opc=00: FCVT Sd, Hn converts the other way (wrong direction)",
            Word(|w| set_field(set_field(w, 23, 22, 0b11), 16, 15, 0b00)),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "ftype=01: FCVT Hd, Dn reads a binary64 (wrong source format)",
            Word(|w| set_field(w, 23, 22, 0b01)),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "opc=01: FCVT Dd, Sn widens to binary64, outside the half-precision model",
            Word(|w| set_field(w, 16, 15, 0b01)),
            UnmodeledInstruction,
        ),
        c(
            F::FcvtHFromS,
            "opc=00: FCVT Sd, Sn to its own precision is unallocated",
            Word(|w| set_field(w, 16, 15, 0b00)),
            Unallocated,
        ),
        c(
            F::FcvtHFromS,
            "ftype=01, opcode 000110: BFCVT Hd, Sn narrows to bfloat16 (FEAT_BF16)",
            Word(|w| set_field(set_field(w, 23, 22, 0b01), 20, 15, 0b000110)),
            NotDecoded,
        ),
        c(
            F::FcvtHFromS,
            "Rn=S8: wrong source register",
            Word(|w| set_field(w, 9, 5, 8)),
            Value,
        ),
        c(
            F::FcvtHFromS,
            "Rd=H4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
        // FCVT Hd, Dn.
        c(
            F::FcvtHFromD,
            "round toward zero claimed: FCVT rounds to nearest, ties to even",
            Intent(M::FcvtRoundTowardZero),
            Value,
        ),
        c(
            F::FcvtHFromD,
            "ties away from zero claimed: FCVT breaks ties to even",
            Intent(M::FcvtRoundTiesAway),
            Value,
        ),
        c(
            F::FcvtHFromD,
            "the alternative half-precision format claimed (FPCR.AHP=1): wrong result format",
            Intent(M::FcvtAlternativeHalf),
            Value,
        ),
        c(
            F::FcvtHFromD,
            "the default NaN claimed (FPCR.DN=1): the high payload is propagated",
            Intent(M::FcvtDefaultNan),
            Value,
        ),
        c(
            F::FcvtHFromD,
            "binary16 denormal results claimed flushed (FZ16): FCVT keeps them",
            Intent(M::FcvtFlushHalfDenormals),
            Value,
        ),
        c(
            F::FcvtHFromD,
            "ftype=11, opc=01: FCVT Dd, Hn converts the other way (wrong direction)",
            Word(|w| set_field(set_field(w, 23, 22, 0b11), 16, 15, 0b01)),
            Value,
        ),
        c(
            F::FcvtHFromD,
            "ftype=00: FCVT Hd, Sn reads a binary32 (wrong source format)",
            Word(|w| set_field(w, 23, 22, 0b00)),
            Value,
        ),
        c(
            F::FcvtHFromD,
            "opc=00: FCVT Sd, Dn narrows to binary32, outside the half-precision model",
            Word(|w| set_field(w, 16, 15, 0b00)),
            UnmodeledInstruction,
        ),
        c(
            F::FcvtHFromD,
            "opc=01: FCVT Dd, Dn to its own precision is unallocated",
            Word(|w| set_field(w, 16, 15, 0b01)),
            Unallocated,
        ),
        c(
            F::FcvtHFromD,
            "opcode 000110: BFCVT Hd, Sn narrows to bfloat16 (FEAT_BF16)",
            Word(|w| set_field(w, 20, 15, 0b000110)),
            NotDecoded,
        ),
        c(
            F::FcvtHFromD,
            "Rd=H4: wrong destination register",
            Word(|w| set_field(w, 4, 0, 4)),
            Destination,
        ),
    ]
}

/// What the credit hook established for one opcode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct A64ValueCredit {
    pub opcode: AArch64Opcode,
    /// Forms demanded for the opcode.
    pub forms: usize,
    /// Forms decided by exact routing (the rest are evaluator-accepted).
    pub exact_forms: usize,
    /// Captured words checked instance-by-instance.
    pub captured_words: usize,
    /// Negative controls refuted for their stated class.
    pub controls_refuted: usize,
}

/// The coverage-gate credit hook for a decoded-value opcode.
///
/// Refuses unless every demanded form has a canonical captured word whose
/// obligation holds, every captured word of those forms passes the
/// per-instance check as the form it is filed under, each form has a
/// Value-class negative control, and EVERY control of those forms is refuted
/// for its stated class. Refuting controls are a precondition of green.
pub fn a64_value_credit(opcode: AArch64Opcode) -> Result<A64ValueCredit, String> {
    // The production credit is a pure function of compiled-in data (the
    // captured corpus, the control battery and the default configuration), so
    // one evaluation per opcode per process is exact; every audit of the
    // AArch64 inventory would otherwise re-run the exhaustive FCVT sweeps.
    // Injected corpora and batteries go through the uncached
    // `a64_value_credit_with`.
    static CREDITS: std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashMap<AArch64Opcode, Result<A64ValueCredit, String>>>,
    > = std::sync::OnceLock::new();
    let cache = CREDITS.get_or_init(Default::default);
    if let Some(hit) = cache.lock().ok().and_then(|map| map.get(&opcode).cloned()) {
        return hit;
    }
    let credit = a64_value_credit_with(
        opcode,
        CAPTURED_A64_VALUE_WORDS,
        &a64_value_controls(),
        &VerificationConfig::default(),
    );
    if let Ok(mut map) = cache.lock() {
        map.insert(opcode, credit.clone());
    }
    credit
}

/// [`a64_value_credit`] over an injected corpus and battery, so a test can
/// hand the hook a stale word or a surviving control and watch it refuse.
pub fn a64_value_credit_with(
    opcode: AArch64Opcode,
    corpus: &[CapturedA64Word],
    controls: &[A64ValueControl],
    config: &VerificationConfig,
) -> Result<A64ValueCredit, String> {
    let forms = a64_value_forms(opcode)
        .ok_or_else(|| format!("{opcode:?} is not a decoded-value opcode"))?;
    let mut exact_forms = 0;
    for &form in forms {
        let canonical = corpus
            .iter()
            .find(|entry| entry.form == form)
            .ok_or_else(|| format!("{form:?} has no captured word"))?;
        if canonical.word != form.canonical().map_or(0, |entry| entry.word) {
            return Err(format!(
                "{form:?}: the injected corpus's canonical word {:#010x} is not the registered \
                 obligation's word",
                canonical.word
            ));
        }
        match decide_a64_value_form(form, canonical.word, None, config) {
            Ok(A64FormDecision::Exact) => exact_forms += 1,
            Ok(A64FormDecision::Evaluated) => {}
            Err(error) => return Err(format!("{form:?} obligation does not hold: {error}")),
        }
    }
    let mut captured_words = 0;
    for entry in corpus.iter().filter(|entry| forms.contains(&entry.form)) {
        let inst = entry.inst();
        let intent =
            a64_value_intent(&inst).map_err(|error| format!("captured {inst:?}: {error}"))?;
        if intent.form != Some(entry.form) {
            return Err(format!(
                "captured {inst:?} is filed as {:?} but its intent is {:?}",
                entry.form, intent.form
            ));
        }
        check_word_against_intent(&intent, entry.word)
            .map_err(|error| format!("captured {inst:?} = {:#010x}: {error}", entry.word))?;
        captured_words += 1;
    }
    let mut controls_refuted = 0;
    for &form in forms {
        let own: Vec<_> = controls
            .iter()
            .filter(|control| control.form == form)
            .collect();
        if !own
            .iter()
            .any(|control| control.expected == A64RefusalClass::Value)
        {
            return Err(format!("{form:?} has no Value-class negative control"));
        }
        let canonical = form
            .canonical()
            .ok_or_else(|| format!("{form:?} has no captured word"))?;
        for control in own {
            let outcome = match control.mutation {
                A64ControlMutation::Word(mutate) => {
                    decide_a64_value_form(form, mutate(canonical.word), None, config)
                }
                A64ControlMutation::Intent(mutation) => {
                    decide_a64_value_form(form, canonical.word, Some(mutation), config)
                }
            };
            match outcome {
                Err(A64ValueCheckError::Refuted(refutation))
                    if refutation.class == control.expected =>
                {
                    controls_refuted += 1;
                }
                other => {
                    return Err(format!(
                        "{form:?} control `{}` must be refuted for {:?}, got {other:?}",
                        control.label, control.expected
                    ));
                }
            }
        }
    }
    Ok(A64ValueCredit {
        opcode,
        forms: forms.len(),
        exact_forms,
        captured_words,
        controls_refuted,
    })
}

// ===========================================================================
// Function-verifier binding
// ===========================================================================

/// Number every virtual register operand as a physical register of its
/// class, so shape validation is the single [`a64_value_intent`] path for
/// pre- and post-allocation instructions. Each distinct virtual register gets
/// its own hardware number, below 31 (SP/ZR), that no physical operand of the
/// same bank (general-purpose, or SIMD&FP) uses: equal registers stay equal,
/// distinct ones distinct, and a virtual register never aliases a physical
/// operand of the same instruction.
fn with_virtual_registers_numbered(inst: &MachInst) -> Result<MachInst, A64ValueCheckError> {
    #[derive(Clone, Copy, PartialEq)]
    enum Bank {
        General,
        SimdFp,
    }
    let bank = |class: RegClass| match class {
        RegClass::Gpr64 | RegClass::Gpr32 => Some(Bank::General),
        RegClass::Fpr128 | RegClass::Fpr64 | RegClass::Fpr32 | RegClass::Fpr16 | RegClass::Fpr8 => {
            Some(Bank::SimdFp)
        }
        _ => None,
    };
    let mut used: Vec<(Bank, u16)> = inst
        .operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::PReg(p) => Some((
                bank(trust_cg_ir::aarch64_regs::preg_class(*p))?,
                u16::from(trust_cg_ir::aarch64_regs::hw_encoding(*p)),
            )),
            _ => None,
        })
        .collect();
    let mut seen: Vec<(VReg, u16)> = Vec::new();
    let mut operands = Vec::with_capacity(inst.operands.len());
    for op in &inst.operands {
        let MachOperand::VReg(v) = op else {
            operands.push(op.clone());
            continue;
        };
        let base = match v.class {
            RegClass::Gpr64 => 0,
            RegClass::Gpr32 => 32,
            RegClass::Fpr64 => 96,
            RegClass::Fpr32 => 128,
            RegClass::Fpr16 => 165,
            RegClass::Fpr128 => 64,
            other => return Err(out_of_model(format!("virtual register class {other:?}"))),
        };
        let class_bank = bank(v.class).expect("every numbered class has a bank");
        let n = match seen.iter().find(|(known, _)| known == v) {
            Some(&(_, n)) => n,
            None => {
                let n = (0..31u16)
                    .find(|n| !used.contains(&(class_bank, *n)))
                    .ok_or_else(|| out_of_model("too many registers"))?;
                used.push((class_bank, n));
                seen.push((*v, n));
                n
            }
        };
        operands.push(MachOperand::PReg(PReg::new(base + n)));
    }
    Ok(MachInst::new(inst.opcode, operands))
}

/// The decoded-value form a concrete instruction belongs to, for the
/// function verifier: `None` for other opcodes, `Some(None)` for a refused
/// shape (ill-formed or outside the modeled forms), `Some(Some(form))` when
/// it binds.
pub fn a64_value_bound_form(inst: &MachInst) -> Option<Option<A64ValueForm>> {
    if !A64_VALUE_OPCODES_BOUND_PER_INSTRUCTION.contains(&inst.opcode) {
        return None;
    }
    Some(
        with_virtual_registers_numbered(inst)
            .and_then(|concrete| a64_value_intent(&concrete))
            .ok()
            .and_then(|intent| intent.form),
    )
}

/// The lanewise obligation query of a NEON bitwise opcode (AND, ORR, EOR,
/// BIC, NOT), which states the operation over the whole 128-bit register:
/// the 16B arrangement. `None` for every other opcode.
pub fn neon_bitwise_16b_query(opcode: AArch64Opcode) -> Option<&'static str> {
    match opcode {
        AArch64Opcode::NeonAndV => Some("andv.16b lanewise-intent"),
        AArch64Opcode::NeonOrrV => Some("orrv.16b lanewise-intent"),
        AArch64Opcode::NeonEorV => Some("eorv.16b lanewise-intent"),
        AArch64Opcode::NeonBicV => Some("bicv.16b lanewise-intent"),
        AArch64Opcode::NeonNotV => Some("notv.16b lanewise-intent"),
        _ => None,
    }
}

/// `(Vd, Vn, Vm)` of a NEON bitwise instruction in the one shape its
/// lanewise obligation binds: three 128-bit (Q) operands and no selector
/// (two for NOT, with no `Vm`), which the encoder spells with `Q = 1`. An
/// ORR of one register with itself is the register copy, bound to
/// [`A64ValueForm::MovV16B`] instead. `None` for every other shape: the 8B
/// arrangement (`Q = 0`, what `V64` operands encode to) writes zero to the
/// upper half, which the 16B obligation does not state.
fn neon_bitwise_16b_registers(inst: &MachInst) -> Option<(u8, u8, Option<u8>)> {
    neon_bitwise_16b_query(inst.opcode)?;
    let concrete = with_virtual_registers_numbered(inst).ok()?;
    if inst.opcode == AArch64Opcode::NeonNotV {
        if inst.operands.len() != 2 {
            return None;
        }
        let Ok(
            [
                Operand::Fpr { bits: 128, num: d },
                Operand::Fpr { bits: 128, num: n },
            ],
        ) = operands::<2>(&concrete)
        else {
            return None;
        };
        return Some((d, n, None));
    }
    if inst.operands.len() != 3 {
        return None;
    }
    let Ok(
        [
            Operand::Fpr { bits: 128, num: d },
            Operand::Fpr { bits: 128, num: n },
            Operand::Fpr { bits: 128, num: m },
        ],
    ) = operands::<3>(&concrete)
    else {
        return None;
    };
    if inst.opcode == AArch64Opcode::NeonOrrV && n == m {
        return None;
    }
    Some((d, n, Some(m)))
}

/// The lanewise obligation query a NEON bitwise instruction binds, or `None`
/// when its opcode is not one or its shape is not the bound 16B shape.
pub fn neon_bitwise_16b_bound_query(inst: &MachInst) -> Option<&'static str> {
    neon_bitwise_16b_registers(inst)?;
    neon_bitwise_16b_query(inst.opcode)
}

/// Why a NEON AND/EOR/BIC/NOT instruction binds nothing: `None` for other
/// opcodes (ORR's refusals are [`a64_value_unbound_reason`]'s) and for the
/// bound 16B shape.
pub fn neon_bitwise_unbound_reason(inst: &MachInst) -> Option<String> {
    if inst.opcode == AArch64Opcode::NeonOrrV
        || neon_bitwise_16b_query(inst.opcode).is_none()
        || neon_bitwise_16b_registers(inst).is_some()
    {
        return None;
    }
    let parts: Vec<String> = inst.operands.iter().map(describe_operand).collect();
    Some(format!(
        "no bound shape for {:?} {}: only the 16B form (Q registers, no selector) binds its \
         lanewise obligation, which does not state the 8B arrangement; ENC-5 does not decide \
         this word",
        inst.opcode,
        if parts.is_empty() {
            "with no operands".to_owned()
        } else {
            parts.join(", ")
        }
    ))
}

/// ENC-5's check of a NEON bitwise word in the bound 16B shape: the
/// independent decoder must read the instruction's operation with `Q = 1`
/// and its own register numbers. `None` when `inst` is not that shape or
/// names a virtual register.
pub fn check_neon_bitwise_16b_word(inst: &MachInst, word: u32) -> Option<Result<(), String>> {
    if inst
        .operands
        .iter()
        .any(|op| matches!(op, MachOperand::VReg(_)))
    {
        return None;
    }
    let (d, n, m) = neon_bitwise_16b_registers(inst)?;
    let Some(m) = m else {
        // NOT (vector), Arm ARM C7.2.210: 0|Q|1|01110|00|10000|00101|10|Rn|Rd.
        if word & 0xBFFF_FC00 != 0x2E20_5800 {
            return Some(Err(format!("{word:#010x} is not NOT (vector)")));
        }
        let (q, rn, rd) = (field(word, 30, 30), field(word, 9, 5), field(word, 4, 0));
        return Some(if (q, rn, rd) == (1, u32::from(n), u32::from(d)) {
            Ok(())
        } else {
            Err(format!(
                "{word:#010x} decodes as NOT Q={q} V{rd}, V{rn}; expected Q=1 V{d}, V{n}"
            ))
        });
    };
    let (u, size) = match inst.opcode {
        AArch64Opcode::NeonAndV => (0, 0b00),
        AArch64Opcode::NeonBicV => (0, 0b01),
        AArch64Opcode::NeonOrrV => (0, 0b10),
        AArch64Opcode::NeonEorV => (1, 0b00),
        _ => return None,
    };
    let want = A64ValueWord::SimdLogical {
        q: 1,
        u,
        size,
        rm: u32::from(m),
        rn: u32::from(n),
        rd: u32::from(d),
    };
    Some(match decode_a64_value_word(word) {
        Ok(decoded) if decoded == want => Ok(()),
        Ok(decoded) => Err(format!(
            "{word:#010x} decodes as {decoded:?}, expected {want:?}"
        )),
        Err(refusal) => Err(refusal.to_string()),
    })
}

/// Why an instruction of a per-instruction decoded-value opcode binds no
/// form: `None` for other opcodes and for shapes that bind. The function
/// verifier reports this as the instruction's `Unverified` reason, so a
/// refused copy names its exact operand shape (for example `MOVXrr SP <- X1`
/// or `FmovFprGpr X0 <- H1`) instead of a generic missing mapping.
pub fn a64_value_unbound_reason(inst: &MachInst) -> Option<String> {
    if !A64_VALUE_OPCODES_BOUND_PER_INSTRUCTION.contains(&inst.opcode) {
        return None;
    }
    let shape = || {
        let parts: Vec<String> = inst.operands.iter().map(describe_operand).collect();
        match parts.as_slice() {
            [] => "with no operands".to_owned(),
            [dst, src] => format!("{dst} <- {src}"),
            _ => parts.join(", "),
        }
    };
    let intent = match with_virtual_registers_numbered(inst).and_then(|c| a64_value_intent(&c)) {
        Ok(intent) => intent,
        Err(error) => {
            return Some(format!(
                "no decoded-value form binds {:?} {}: the shape is outside the model ({error}); \
                 no registered obligation covers it",
                inst.opcode,
                shape()
            ));
        }
    };
    if intent.form.is_some() {
        return None;
    }
    Some(format!(
        "no decoded-value form binds {:?} {}: ENC-5 still decides its word, but no registered \
         obligation covers this shape",
        inst.opcode,
        shape()
    ))
}

/// An operand as a refusal reason spells it.
fn describe_operand(op: &MachOperand) -> String {
    let class_name = |class: RegClass| match class {
        RegClass::Gpr32 => "W",
        RegClass::Gpr64 => "X",
        RegClass::Fpr16 => "H",
        RegClass::Fpr32 => "S",
        RegClass::Fpr64 => "D",
        RegClass::Fpr128 => "Q",
        _ => "?",
    };
    match op {
        MachOperand::VReg(v) => format!("{}v{}", class_name(v.class), v.id),
        other => match operand(other) {
            Some(Operand::Gpr { width, name }) => {
                let x = width == 64;
                match name {
                    GprName::Num(n) => format!("{}{n}", if x { "X" } else { "W" }),
                    GprName::Sp => (if x { "SP" } else { "WSP" }).to_owned(),
                    GprName::Zr => (if x { "XZR" } else { "WZR" }).to_owned(),
                }
            }
            Some(Operand::Fpr { bits, num }) => {
                let prefix = match bits {
                    16 => "H",
                    32 => "S",
                    64 => "D",
                    _ => "Q",
                };
                format!("{prefix}{num}")
            }
            Some(Operand::Imm(value)) => format!("#{value}"),
            None => format!("{other:?}"),
        },
    }
}

// ===========================================================================
// Captured corpus
// ===========================================================================

/// An operand of a captured instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64Operand {
    X(u8),
    W(u8),
    Sp,
    Xzr,
    Wzr,
    /// XZR as the physical register (`PReg` 160), the spelling ISel uses.
    XzrReg,
    /// WZR as the physical register (`PReg` 161).
    WzrReg,
    H(u8),
    S(u8),
    D(u8),
    Q(u8),
    Imm(i64),
}

impl A64Operand {
    /// The machine-IR operand.
    pub fn mach(self) -> MachOperand {
        let preg = |base: u16, n: u8| MachOperand::PReg(PReg::new(base + u16::from(n)));
        match self {
            Self::X(n) => preg(0, n),
            Self::W(n) => preg(32, n),
            Self::Sp => MachOperand::Special(SpecialReg::SP),
            Self::Xzr => MachOperand::Special(SpecialReg::XZR),
            Self::Wzr => MachOperand::Special(SpecialReg::WZR),
            Self::XzrReg => MachOperand::PReg(PReg::new(160)),
            Self::WzrReg => MachOperand::PReg(PReg::new(161)),
            Self::H(n) => preg(165, n),
            Self::S(n) => preg(128, n),
            Self::D(n) => preg(96, n),
            Self::Q(n) => preg(64, n),
            Self::Imm(value) => MachOperand::Imm(value),
        }
    }
}

/// One instruction word captured from `trust-cg-codegen`'s AArch64 encoder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CapturedA64Word {
    pub form: A64ValueForm,
    pub operands: &'static [A64Operand],
    pub word: u32,
}

impl CapturedA64Word {
    /// The machine-IR instruction the encoder was given.
    pub fn inst(&self) -> MachInst {
        MachInst::new(
            self.form.opcode(),
            self.operands.iter().map(|op| op.mach()).collect(),
        )
    }
}

/// Words captured from `trust_cg_codegen::aarch64::encode::encode_instruction`.
/// The FIRST entry of each form is its canonical word, from which the
/// registered obligation is built. `coverage_gate_tests` and
/// `aarch64_value_decode_gate` re-encode every entry with the live encoder
/// and fail on any difference.
pub const CAPTURED_A64_VALUE_WORDS: &[CapturedA64Word] = {
    use A64Operand::{D, H, Imm, Q, S, Sp, W, Wzr, WzrReg, X, Xzr, XzrReg};
    use A64ValueForm as F;
    const fn e(form: A64ValueForm, operands: &'static [A64Operand], word: u32) -> CapturedA64Word {
        CapturedA64Word {
            form,
            operands,
            word,
        }
    }
    &[
        e(F::MovW, &[W(3), W(7)], 0x2A07_03E3),
        e(F::MovW, &[W(0), W(30)], 0x2A1E_03E0),
        e(F::MovX, &[X(3), X(7)], 0xAA07_03E3),
        e(F::MovX, &[X(30), X(0)], 0xAA00_03FE),
        e(F::MovX, &[X(19), X(19)], 0xAA13_03F3),
        e(F::MovXFromSp, &[X(3), Sp], 0x9100_03E3),
        e(F::MovXFromSp, &[X(29), Sp], 0x9100_03FD),
        e(F::MovWrr, &[W(3), W(7)], 0x2A07_03E3),
        // The allocator may leave X views on a MOVWrr: still the W form.
        e(F::MovWrr, &[X(3), X(7)], 0x2A07_03E3),
        e(F::MovWrr, &[W(30), W(0)], 0x2A00_03FE),
        e(F::MovXrr, &[X(3), X(7)], 0xAA07_03E3),
        // W views on a MOVXrr: still the X form.
        e(F::MovXrr, &[W(5), W(6)], 0xAA06_03E5),
        e(F::MovXrr, &[X(30), X(0)], 0xAA00_03FE),
        e(F::MovWFromZr, &[W(3), Wzr], 0x2A1F_03E3),
        e(F::MovWFromZr, &[W(30), WzrReg], 0x2A1F_03FE),
        e(F::MovXFromZr, &[X(3), Xzr], 0xAA1F_03E3),
        e(F::MovXFromZr, &[X(0), XzrReg], 0xAA1F_03E0),
        e(F::MovWrrFromZr, &[W(3), WzrReg], 0x2A1F_03E3),
        e(F::MovWrrFromZr, &[X(3), XzrReg], 0x2A1F_03E3),
        // The zero-sized aggregate argument: `MOVXrr Xn, XZR` (ISel's PReg).
        e(F::MovXrrFromZr, &[X(3), XzrReg], 0xAA1F_03E3),
        e(F::MovXrrFromZr, &[W(5), Wzr], 0xAA1F_03E5),
        e(F::MovXrrFromZr, &[X(7), Xzr], 0xAA1F_03E7),
        e(F::FmovS, &[S(3), S(7)], 0x1E20_40E3),
        e(F::FmovS, &[S(0), S(31)], 0x1E20_43E0),
        e(F::FmovD, &[D(3), D(7)], 0x1E60_40E3),
        e(F::FmovD, &[D(31), D(0)], 0x1E60_401F),
        e(F::FmovWFromS, &[W(3), S(7)], 0x1E26_00E3),
        e(F::FmovWFromS, &[W(30), S(0)], 0x1E26_001E),
        e(F::FmovXFromD, &[X(3), D(7)], 0x9E66_00E3),
        e(F::FmovXFromD, &[X(0), D(31)], 0x9E66_03E0),
        e(F::FmovSFromW, &[S(3), W(7)], 0x1E27_00E3),
        e(F::FmovSFromW, &[S(31), W(0)], 0x1E27_001F),
        e(F::FmovDFromX, &[D(3), X(7)], 0x9E67_00E3),
        e(F::FmovDFromX, &[D(0), X(30)], 0x9E67_03C0),
        e(F::FmovWFromH, &[W(3), H(7)], 0x1EE6_00E3),
        e(F::FmovWFromH, &[W(30), H(0)], 0x1EE6_001E),
        e(F::FmovHFromW, &[H(3), W(7)], 0x1EE7_00E3),
        e(F::FmovHFromW, &[H(31), W(0)], 0x1EE7_001F),
        e(F::MovV16B, &[Q(3), Q(7), Q(7)], 0x4EA7_1CE3),
        // The scalar copies `lower_copies` emits carry the #1 (16B) selector.
        e(F::MovV16B, &[D(0), D(31), D(31), Imm(1)], 0x4EBF_1FE0),
        e(F::MovV16B, &[S(5), S(6), S(6), Imm(1)], 0x4EA6_1CC5),
        e(F::MovV16B, &[H(1), H(2), H(2), Imm(1)], 0x4EA2_1C41),
        e(F::Smull, &[X(3), W(7), W(12)], 0x9B2C_7CE3),
        e(F::Smull, &[X(0), W(30), W(1)], 0x9B21_7FC0),
        e(F::BfmInsertW, &[W(3), W(7), Imm(24), Imm(4)], 0x3318_10E3),
        e(F::BfmInsertW, &[W(3), W(7), Imm(0), Imm(31)], 0x3300_7CE3),
        e(F::BfmInsertW, &[W(3), W(7), Imm(1), Imm(0)], 0x3301_00E3),
        e(F::BfmInsertX, &[X(3), X(7), Imm(56), Imm(4)], 0xB378_10E3),
        e(F::BfmInsertX, &[X(3), X(7), Imm(0), Imm(63)], 0xB340_FCE3),
        e(F::BfmInsertX, &[X(3), X(7), Imm(1), Imm(0)], 0xB341_00E3),
        e(F::RbitW, &[W(3), W(7)], 0x5AC0_00E3),
        e(F::RbitW, &[W(30), W(0)], 0x5AC0_001E),
        e(F::RbitX, &[X(3), X(7)], 0xDAC0_00E3),
        e(F::RbitX, &[X(0), X(30)], 0xDAC0_03C0),
        e(F::AddLsl12W, &[W(3), W(7), Imm(0x123)], 0x1144_8CE3),
        e(F::AddLsl12W, &[W(0), W(30), Imm(0)], 0x1140_03C0),
        e(F::AddLsl12X, &[X(3), X(7), Imm(0x123)], 0x9144_8CE3),
        e(F::AddLsl12X, &[X(3), Sp, Imm(1)], 0x9140_07E3),
        e(F::AddLsl12X, &[Sp, Sp, Imm(4095)], 0x917F_FFFF),
        e(
            F::MrsTpidrEl0,
            &[X(3), Imm(TPIDR_EL0_KEY as i64)],
            0xD53B_D043,
        ),
        e(
            F::MrsTpidrEl0,
            &[X(30), Imm(TPIDR_EL0_KEY as i64)],
            0xD53B_D05E,
        ),
        e(F::FcvtSFromH, &[S(3), H(7)], 0x1EE2_40E3),
        e(F::FcvtSFromH, &[S(0), H(31)], 0x1EE2_43E0),
        e(F::FcvtDFromH, &[D(3), H(7)], 0x1EE2_C0E3),
        e(F::FcvtDFromH, &[D(31), H(0)], 0x1EE2_C01F),
        e(F::FcvtHFromS, &[H(3), S(7)], 0x1E23_C0E3),
        e(F::FcvtHFromS, &[H(31), S(0)], 0x1E23_C01F),
        e(F::FcvtHFromD, &[H(3), D(7)], 0x1E63_C0E3),
        e(F::FcvtHFromD, &[H(0), D(31)], 0x1E63_C3E0),
    ]
};

// ===========================================================================
// CSET — decoded-word value obligations for the conditional-set alias
// ===========================================================================
//
// `CSET Rd, <cc>` is the architectural ALIAS for
// `CSINC Rd, ZR, ZR, invert(<cc>)`: it materialises a condition as the integer
// 0 or 1. It is the single most-emitted opcode with no proof mapping — the
// certificate lane rejected 62 of `library/core`'s 63 remaining roots on it —
// and `opcode_to_proof_query` refuses it on purpose, because a generic
// CMP+CSET template "does not establish this CSET's actual condition, carrier
// width, or reaching flag producer".
//
// This family establishes a DIFFERENT and strictly weaker statement than the
// source-bound bindings in `function_verifier`, and it is bound LAST so it can
// never displace one of them:
//
//   * what it claims: the instruction WORD the encoder emits for this form
//     writes, into the named destination register, exactly 1 when the
//     architectural condition holds and 0 when it does not, for every one of
//     the sixteen NZCV states.
//   * what it does NOT claim: which flag producer reaches this CSET, which
//     source operation its lowering completes, or that the condition is the
//     right one for that source operation. Those are the four facts the
//     `nzcv_consumer_source_bound_query` chain establishes, and a CSET that
//     binds there keeps citing the whole-sequence theorem it always cited.
//
// HOW THE TWO SIDES ARE COMPUTED DIFFERENTLY. The MACHINE side is obtained by
// DECODING the 32-bit word through `aarch64_csel_semantics`, an Arm ARM derived
// conditional-select decoder whose field extraction, `ConditionHolds` table and
// symbolic execution are checked against independent oracles (4096 accepted
// encodings with fixed-bit mutation controls; all 16 conditions x 16 NZCV
// against a hand-transcribed truth table). That decoder knows nothing about the
// CSET alias: it reports the raw `op`/`o2` variant, BOTH source registers and
// the RAW condition field, and its denotation applies the generic
// conditional-select pseudo-code — `ite(ConditionHolds(cond<3:0>), X[Rn],
// f(X[Rm]))` with `f` chosen by `op:o2`, where `ConditionHolds` is a switch on
// `cond<3:1>` with a `cond<0>` inversion. The INTENT side never mentions a
// field: it reads the machine-IR instruction's own condition MNEMONIC and takes
// its predicate from `crate::nzcv::eval_condition`, the per-mnemonic table
// (`HI => C & !Z`, `LE => Z | N != V`, ...), then writes 1/0. The alias's
// inversion, its two zero registers and its increment are therefore all
// LOAD-BEARING: dropping the inversion, reading a register other than ZR,
// or emitting a CSEL/CSINV/CSNEG in its place each REFUTE, and
// `a64_cset_controls` exercises every one of those.
//
// STRENGTH. The obligation's only free input is the four-bit packed NZCV, so
// `verify_by_evaluation_with_config` decides it EXHAUSTIVELY over all sixteen
// architectural flag states — complete for the declared domain, which for this
// obligation is the whole input space. That is a stronger discharge than the
// sampled `Statistical` acceptance the rest of this lane's arithmetic forms
// get. It remains an in-process evaluator decision, NOT a kernel-checked
// certificate and NOT a silicon differential.

/// One emitted form of `CSET`: a destination width and a condition code.
///
/// The alias is `AL`/`NV`-free by construction — neither complements the other,
/// which is why the encoder refuses a condition above 13
/// (`conditional_select_fields`'s `maximum`) — so the family is exactly the
/// fourteen ordinary conditions at each of the two widths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct A64CSetForm {
    /// Destination register width: 32 (`Wd`) or 64 (`Xd`).
    pub width: u32,
    /// The condition the MACHINE-IR instruction carries. The WORD carries its
    /// complement; that inversion is part of what the obligation checks.
    pub cc: AArch64CC,
    /// Lower-case registry query token, a unique substring of `name`. The
    /// walk's lookup is `name.to_lowercase().contains(query)` and does NOT
    /// lowercase the query.
    pub query: &'static str,
    /// The registered obligation's name.
    pub name: &'static str,
}

/// Every form, in registration order: the `Xd` family then the `Wd` family,
/// each in condition-encoding order.
pub const A64_CSET_FORMS: [A64CSetForm; 28] = [
    A64CSetForm {
        width: 64,
        cc: AArch64CC::EQ,
        query: "a64 decoded cset xd, eq",
        name: "A64 decoded CSET Xd, EQ (CSINC Xd, XZR, XZR, NE word) == ConditionHolds(EQ) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::NE,
        query: "a64 decoded cset xd, ne",
        name: "A64 decoded CSET Xd, NE (CSINC Xd, XZR, XZR, EQ word) == ConditionHolds(NE) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::HS,
        query: "a64 decoded cset xd, hs",
        name: "A64 decoded CSET Xd, HS (CSINC Xd, XZR, XZR, LO word) == ConditionHolds(HS) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::LO,
        query: "a64 decoded cset xd, lo",
        name: "A64 decoded CSET Xd, LO (CSINC Xd, XZR, XZR, HS word) == ConditionHolds(LO) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::MI,
        query: "a64 decoded cset xd, mi",
        name: "A64 decoded CSET Xd, MI (CSINC Xd, XZR, XZR, PL word) == ConditionHolds(MI) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::PL,
        query: "a64 decoded cset xd, pl",
        name: "A64 decoded CSET Xd, PL (CSINC Xd, XZR, XZR, MI word) == ConditionHolds(PL) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::VS,
        query: "a64 decoded cset xd, vs",
        name: "A64 decoded CSET Xd, VS (CSINC Xd, XZR, XZR, VC word) == ConditionHolds(VS) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::VC,
        query: "a64 decoded cset xd, vc",
        name: "A64 decoded CSET Xd, VC (CSINC Xd, XZR, XZR, VS word) == ConditionHolds(VC) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::HI,
        query: "a64 decoded cset xd, hi",
        name: "A64 decoded CSET Xd, HI (CSINC Xd, XZR, XZR, LS word) == ConditionHolds(HI) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::LS,
        query: "a64 decoded cset xd, ls",
        name: "A64 decoded CSET Xd, LS (CSINC Xd, XZR, XZR, HI word) == ConditionHolds(LS) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::GE,
        query: "a64 decoded cset xd, ge",
        name: "A64 decoded CSET Xd, GE (CSINC Xd, XZR, XZR, LT word) == ConditionHolds(GE) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::LT,
        query: "a64 decoded cset xd, lt",
        name: "A64 decoded CSET Xd, LT (CSINC Xd, XZR, XZR, GE word) == ConditionHolds(LT) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::GT,
        query: "a64 decoded cset xd, gt",
        name: "A64 decoded CSET Xd, GT (CSINC Xd, XZR, XZR, LE word) == ConditionHolds(GT) ? 1 : 0",
    },
    A64CSetForm {
        width: 64,
        cc: AArch64CC::LE,
        query: "a64 decoded cset xd, le",
        name: "A64 decoded CSET Xd, LE (CSINC Xd, XZR, XZR, GT word) == ConditionHolds(LE) ? 1 : 0",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::EQ,
        query: "a64 decoded cset wd, eq",
        name: "A64 decoded CSET Wd, EQ (CSINC Wd, WZR, WZR, NE word) \
         == ConditionHolds(EQ) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::NE,
        query: "a64 decoded cset wd, ne",
        name: "A64 decoded CSET Wd, NE (CSINC Wd, WZR, WZR, EQ word) \
         == ConditionHolds(NE) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::HS,
        query: "a64 decoded cset wd, hs",
        name: "A64 decoded CSET Wd, HS (CSINC Wd, WZR, WZR, LO word) \
         == ConditionHolds(HS) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::LO,
        query: "a64 decoded cset wd, lo",
        name: "A64 decoded CSET Wd, LO (CSINC Wd, WZR, WZR, HS word) \
         == ConditionHolds(LO) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::MI,
        query: "a64 decoded cset wd, mi",
        name: "A64 decoded CSET Wd, MI (CSINC Wd, WZR, WZR, PL word) \
         == ConditionHolds(MI) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::PL,
        query: "a64 decoded cset wd, pl",
        name: "A64 decoded CSET Wd, PL (CSINC Wd, WZR, WZR, MI word) \
         == ConditionHolds(PL) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::VS,
        query: "a64 decoded cset wd, vs",
        name: "A64 decoded CSET Wd, VS (CSINC Wd, WZR, WZR, VC word) \
         == ConditionHolds(VS) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::VC,
        query: "a64 decoded cset wd, vc",
        name: "A64 decoded CSET Wd, VC (CSINC Wd, WZR, WZR, VS word) \
         == ConditionHolds(VC) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::HI,
        query: "a64 decoded cset wd, hi",
        name: "A64 decoded CSET Wd, HI (CSINC Wd, WZR, WZR, LS word) \
         == ConditionHolds(HI) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::LS,
        query: "a64 decoded cset wd, ls",
        name: "A64 decoded CSET Wd, LS (CSINC Wd, WZR, WZR, HI word) \
         == ConditionHolds(LS) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::GE,
        query: "a64 decoded cset wd, ge",
        name: "A64 decoded CSET Wd, GE (CSINC Wd, WZR, WZR, LT word) \
         == ConditionHolds(GE) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::LT,
        query: "a64 decoded cset wd, lt",
        name: "A64 decoded CSET Wd, LT (CSINC Wd, WZR, WZR, GE word) \
         == ConditionHolds(LT) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::GT,
        query: "a64 decoded cset wd, gt",
        name: "A64 decoded CSET Wd, GT (CSINC Wd, WZR, WZR, LE word) \
         == ConditionHolds(GT) ? 1 : 0, Xd[63:32] zero",
    },
    A64CSetForm {
        width: 32,
        cc: AArch64CC::LE,
        query: "a64 decoded cset wd, le",
        name: "A64 decoded CSET Wd, LE (CSINC Wd, WZR, WZR, GT word) \
         == ConditionHolds(LE) ? 1 : 0, Xd[63:32] zero",
    },
];

impl A64CSetForm {
    /// The form a `(width, cc)` pair names, or `None` when the pair is outside
    /// the family.
    pub fn for_width_and_condition(width: u32, cc: AArch64CC) -> Option<Self> {
        A64_CSET_FORMS
            .iter()
            .copied()
            .find(|form| form.width == width && form.cc == cc)
    }

    /// The proof category. `Comparison` is where the integer comparison and
    /// conditional-select lowerings live; a conditional SET is one of those.
    pub fn category(self) -> ProofCategory {
        ProofCategory::Comparison
    }

    /// The instruction word the encoder emits for this form, with `Rd` = 0.
    pub fn word(self) -> u32 {
        cset_word(self.width, self.cc)
    }
}

/// The `CSET Rd, <cc>` instruction word for `Rd` = 0 at `width`, laid out
/// exactly as `trust_cg_codegen::aarch64::encode`'s `AArch64Opcode::CSet` arm
/// does — including the `cond ^ 1` alias inversion, `op2 = 01` (CSINC) and the
/// two zero registers.
///
/// `tests/aarch64_cset_value_decode.rs` re-encodes every form with the LIVE
/// encoder and fails on any difference, so this layout cannot drift into
/// describing an instruction the compiler does not emit. (That gate lives in
/// `tests/` because `trust-cg-codegen` is a dev-only dependency here — see the
/// note in `Cargo.toml`.)
pub fn cset_word(width: u32, cc: AArch64CC) -> u32 {
    let sf = u32::from(width == 64);
    let inverted = (cc as u32) ^ 1;
    // `sf op S 11010100 Rm cond op2 Rn Rd`, with op = 0, S = 0 and op2 = 01
    // (CSINC), Rm = Rn = 31 (ZR) and Rd = A64_CSET_WORD_RD = 0, whose field
    // contributes nothing and is therefore not written.
    (sf << 31)
        | (0b1101_0100 << 21)
        | (31 << 16)
        | (inverted << 12)
        | (0b01 << 10)
        | (31 << 5)
        | u32::from(A64_CSET_WORD_RD)
}

/// The destination register every form's word writes. The obligation is stated
/// for this register; the per-instance register binding is ENC-5's structural
/// `cset Rd` field check against the intent's own destination.
pub const A64_CSET_WORD_RD: u8 = 0;

/// The `AArch64CC` an ISel condition immediate names, or `None` outside the
/// fourteen the alias admits (`AL`/`NV` and any out-of-range value fail
/// closed).
pub fn cset_condition_from_encoding(encoding: i64) -> Option<AArch64CC> {
    Some(match encoding {
        0 => AArch64CC::EQ,
        1 => AArch64CC::NE,
        2 => AArch64CC::HS,
        3 => AArch64CC::LO,
        4 => AArch64CC::MI,
        5 => AArch64CC::PL,
        6 => AArch64CC::VS,
        7 => AArch64CC::VC,
        8 => AArch64CC::HI,
        9 => AArch64CC::LS,
        10 => AArch64CC::GE,
        11 => AArch64CC::LT,
        12 => AArch64CC::GT,
        13 => AArch64CC::LE,
        _ => return None,
    })
}

/// The free packed NZCV the machine side indexes: N, Z, C, V in bits 3..0.
fn cset_free_nzcv() -> SmtExpr {
    SmtExpr::var("nzcv", 4)
}

/// The same four architectural flags as the Boolean quadruple
/// [`crate::nzcv::eval_condition`]'s per-mnemonic table is written over.
///
/// This is the SECOND, INDEPENDENT spelling of the condition, and the reason
/// the obligation is not a restatement of itself: the intent side reaches its
/// predicate through the mnemonic table, the machine side through the decoded
/// word's raw `cond<3:0>` field and the Arm ARM `ConditionHolds` bit switch.
/// Neither is derived from the other, and the machine side never sees a
/// mnemonic.
fn cset_unpacked_nzcv() -> crate::nzcv::NzcvFlags {
    let bit = |index: u32| cset_free_nzcv().extract(index, index).eq_expr(bv(1, 1));
    crate::nzcv::NzcvFlags {
        n: bit(3),
        z: bit(2),
        c: bit(1),
        v: bit(0),
    }
}

/// A deliberately wrong statement of a CSET form's intent, used as a negative
/// control: the form's own word must refute it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64CSetIntentMutation {
    /// The polarity swapped: 0 when the condition holds, 1 when it does not.
    /// This is what the intent would say if the alias's inversion were applied
    /// on the WRONG side, so it must not be provable.
    PolaritySwapped,
    /// The condition ignored: always 1.
    AlwaysOne,
    /// The condition ignored: always 0.
    AlwaysZero,
}

/// The intent: what the machine-IR `CSet` claims its word writes, as the
/// complete 64-bit destination register (so the `Wd` form's clearing of
/// `Xd[63:32]` is part of the claim).
fn cset_intent_value(
    width: u32,
    cc: AArch64CC,
    mutation: Option<A64CSetIntentMutation>,
) -> SmtExpr {
    let flags = cset_unpacked_nzcv();
    let holds = crate::nzcv::eval_condition(cc, &flags);
    let (when_true, when_false) = match mutation {
        None => (1u64, 0u64),
        Some(A64CSetIntentMutation::PolaritySwapped) => (0, 1),
        Some(A64CSetIntentMutation::AlwaysOne) => (1, 1),
        Some(A64CSetIntentMutation::AlwaysZero) => (0, 0),
    };
    intent_gpr_write(SmtExpr::ite(
        holds,
        bv(when_true, width),
        bv(when_false, width),
    ))
}

/// Build `form`'s obligation from an instruction `word`, optionally against a
/// mutated intent. This is the per-form PRODUCER the corpus ratchet binds to.
///
/// Structural refusals come first, and are deliberately NOT value refutations:
///
///   * a word outside the conditional-select class, or unallocated in it
///     (`op2 = 1x`, `S = 1`) — [`A64RefusalClass::NotDecoded`];
///   * a word writing a register other than the form's `Rd`
///     — [`A64RefusalClass::Destination`];
///   * a word whose `sf` is not the form's width
///     — [`A64RefusalClass::Destination`]. The two widths' VALUES coincide (0
///     or 1, with `Xd[63:32]` clear either way), so a value-only obligation
///     cannot see the width; this check is what makes the width fail closed
///     HERE, and ENC-5's structural `cset sf` field check is the independent
///     per-compile guard.
///
/// Everything else — the alias inversion, both zero registers, the CSINC
/// increment, the condition itself — is decided by the VALUE, so a wrong
/// choice is a counterexample rather than a shape rejection.
pub fn a64_cset_form_obligation_for(
    form: A64CSetForm,
    word: u32,
    mutation: Option<A64CSetIntentMutation>,
) -> Result<ProofObligation, A64ValueCheckError> {
    const RD: u8 = A64_CSET_WORD_RD;
    let decoded = DecodedConditionalSelect::decode(word)
        .map_err(|error| refuted(A64RefusalClass::NotDecoded, error.to_string()))?;
    if decoded.width().bits() != form.width {
        return Err(refuted(
            A64RefusalClass::Destination,
            format!(
                "word writes a {}-bit destination, the form writes {}-bit",
                decoded.width().bits(),
                form.width
            ),
        ));
    }
    let (rd, _, _) = decoded.registers();
    if rd != RD {
        return Err(refuted(
            A64RefusalClass::Destination,
            format!("word writes register {rd}, the form writes register {RD}"),
        ));
    }
    let after = decoded.execute_symbolic(&SymbolicRegisterState::variables());
    let machine = after.register(usize::from(rd)).cloned().ok_or_else(|| {
        refuted(
            A64RefusalClass::Destination,
            "word discards its write (register 31)",
        )
    })?;
    Ok(obligation_from_sides(
        form.name.to_string(),
        cset_intent_value(form.width, form.cc, mutation),
        machine,
        Vec::new(),
    ))
}

/// Every form's registered obligation, in [`A64_CSET_FORMS`] order.
///
/// A form that fails to mint is a DEFECT, not a silent omission:
/// `a64_cset_family_is_complete` pins the length at 28 and the corpus ratchet
/// binds each row to this producer.
pub fn all_a64_cset_value_decode_proofs() -> Vec<(ProofCategory, ProofObligation)> {
    A64_CSET_FORMS
        .iter()
        .filter_map(|&form| {
            Some((
                form.category(),
                a64_cset_form_obligation_for(form, form.word(), None).ok()?,
            ))
        })
        .collect()
}

/// Decide a CSET form obligation by evaluation, reporting the STRENGTH the
/// evaluator's own policy assigns it. A counterexample refutes for
/// [`A64RefusalClass::Value`].
pub fn decide_a64_cset_form(
    form: A64CSetForm,
    word: u32,
    mutation: Option<A64CSetIntentMutation>,
    config: &VerificationConfig,
) -> Result<crate::verify::VerificationStrength, A64ValueCheckError> {
    let obligation = a64_cset_form_obligation_for(form, word, mutation)?;
    let strength =
        crate::verify::VerificationStrength::for_obligation_with_config(&obligation, config);
    match verify_by_evaluation_with_config(&obligation, config) {
        VerificationResult::Valid => Ok(strength),
        VerificationResult::Invalid { counterexample } => {
            Err(refuted(A64RefusalClass::Value, counterexample))
        }
        VerificationResult::Unknown { reason } => Err(out_of_model(format!(
            "evaluator returned Unknown: {reason}"
        ))),
    }
}

/// How a CSET negative control departs from its form.
#[derive(Debug, Clone, Copy)]
pub enum A64CSetControlMutation {
    /// Replace the form's word by a mutated word.
    Word(fn(u32) -> u32),
    /// Keep the word; state a wrong intent.
    Intent(A64CSetIntentMutation),
}

/// One negative control: it must be refuted, for exactly `expected`.
#[derive(Debug, Clone, Copy)]
pub struct A64CSetControl {
    pub form: A64CSetForm,
    pub label: &'static str,
    pub mutation: A64CSetControlMutation,
    pub expected: A64RefusalClass,
}

/// Move the word's condition field to a different, NON-complementary code.
///
/// `+2 mod 14` never lands on the original and never lands on its complement,
/// and all fourteen codes are distinct predicates over NZCV, so the mutated
/// word must denote something else.
fn cset_rotate_condition(word: u32) -> u32 {
    let cond = (word >> 12) & 0xF;
    set_field(word, 15, 12, (cond + 2) % 14)
}

/// The negative-control battery: fourteen controls for EVERY form.
///
/// Each names the exact fact it removes. A proof that cannot fail is not a
/// proof, so [`a64_cset_credit`] requires every one of these to be refuted for
/// its stated class before it reports any credit at all.
pub fn a64_cset_controls() -> Vec<A64CSetControl> {
    use A64CSetControlMutation::{Intent, Word};
    use A64CSetIntentMutation as M;
    use A64RefusalClass::{Destination, NotDecoded, Value};
    let mut out = Vec::with_capacity(A64_CSET_FORMS.len() * 14);
    for &form in &A64_CSET_FORMS {
        let c = |label, mutation, expected| A64CSetControl {
            form,
            label,
            mutation,
            expected,
        };
        out.extend([
            c(
                "alias inversion dropped: the word carries the machine-IR condition itself",
                Word(|w| w ^ (1 << 12)),
                Value,
            ),
            c(
                "condition replaced by a different, non-complementary code",
                Word(cset_rotate_condition),
                Value,
            ),
            c(
                "Rn = register 1 instead of ZR: the true arm reads a register",
                Word(|w| set_field(w, 9, 5, 1)),
                Value,
            ),
            c(
                "Rm = register 1 instead of ZR: the false arm increments a register",
                Word(|w| set_field(w, 20, 16, 1)),
                Value,
            ),
            c(
                "o2 = 0: a CSEL, whose false arm does not increment",
                Word(|w| set_field(w, 10, 10, 0)),
                Value,
            ),
            c(
                "op = 1: a CSINV, whose false arm is the complement",
                Word(|w| set_field(w, 30, 30, 1)),
                Value,
            ),
            c(
                "op = 1 and o2 = 1: a CSNEG, whose false arm is the negation",
                Word(|w| set_field(set_field(w, 30, 30, 1), 10, 10, 1)),
                Value,
            ),
            c(
                "Rn and Rm both = register 1: an ordinary conditional select",
                Word(|w| set_field(set_field(w, 9, 5, 1), 20, 16, 1)),
                Value,
            ),
            c(
                "the intent's polarity swapped",
                Intent(M::PolaritySwapped),
                Value,
            ),
            c(
                "the intent ignores the condition and is always 1",
                Intent(M::AlwaysOne),
                Value,
            ),
            c(
                "the intent ignores the condition and is always 0",
                Intent(M::AlwaysZero),
                Value,
            ),
            c(
                "sf flipped: the word writes the other destination width",
                Word(|w| w ^ (1 << 31)),
                Destination,
            ),
            c(
                "Rd = register 3: the word writes a different register",
                Word(|w| set_field(w, 4, 0, 3)),
                Destination,
            ),
            c(
                "bit 11 set: op2 = 1x is unallocated in the conditional-select class",
                Word(|w| set_field(w, 11, 11, 1)),
                NotDecoded,
            ),
        ]);
    }
    out
}

/// What the CSET battery established.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct A64CSetCredit {
    /// Forms whose obligation holds.
    pub forms: usize,
    /// Forms decided EXHAUSTIVELY over their whole input domain.
    pub exhaustive_forms: usize,
    /// Negative controls refuted for their stated class.
    pub controls_refuted: usize,
}

/// The credit hook for the CSET family.
///
/// Refuses unless EVERY form's obligation holds, every form has at least one
/// `Value`-class control, and EVERY control is refuted for its stated class.
pub fn a64_cset_credit() -> Result<A64CSetCredit, String> {
    a64_cset_credit_with(
        &A64_CSET_FORMS,
        &a64_cset_controls(),
        &VerificationConfig::default(),
    )
}

/// [`a64_cset_credit`] over an injected form list and battery, so a test can
/// hand the hook a surviving control and watch it refuse.
pub fn a64_cset_credit_with(
    forms: &[A64CSetForm],
    controls: &[A64CSetControl],
    config: &VerificationConfig,
) -> Result<A64CSetCredit, String> {
    let mut exhaustive_forms = 0;
    for &form in forms {
        match decide_a64_cset_form(form, form.word(), None, config) {
            Ok(crate::verify::VerificationStrength::Exhaustive) => exhaustive_forms += 1,
            Ok(_) => {}
            Err(error) => {
                return Err(format!(
                    "{:?} CSET {} obligation does not hold: {error}",
                    form.cc, form.width
                ));
            }
        }
    }
    let mut controls_refuted = 0;
    for &form in forms {
        let own: Vec<_> = controls
            .iter()
            .filter(|control| control.form == form)
            .collect();
        if !own
            .iter()
            .any(|control| control.expected == A64RefusalClass::Value)
        {
            return Err(format!(
                "CSET {:?}/{} has no Value-class negative control",
                form.cc, form.width
            ));
        }
        for control in own {
            let outcome = match control.mutation {
                A64CSetControlMutation::Word(mutate) => {
                    decide_a64_cset_form(form, mutate(form.word()), None, config)
                }
                A64CSetControlMutation::Intent(mutation) => {
                    decide_a64_cset_form(form, form.word(), Some(mutation), config)
                }
            };
            match outcome {
                Err(A64ValueCheckError::Refuted(refutation))
                    if refutation.class == control.expected =>
                {
                    controls_refuted += 1;
                }
                other => {
                    return Err(format!(
                        "CSET {:?}/{} control `{}` must be refuted for {:?}, got {other:?}",
                        form.cc, form.width, control.label, control.expected
                    ));
                }
            }
        }
    }
    Ok(A64CSetCredit {
        forms: forms.len(),
        exhaustive_forms,
        controls_refuted,
    })
}

/// The CSET form a concrete machine instruction belongs to.
///
/// `None` for any other opcode, for a shape the encoder would refuse, for a
/// zero-register or stack-pointer destination, and for a condition outside the
/// fourteen the alias admits — each of which keeps the instruction UNCOVERED
/// rather than crediting it a theorem about a different word.
pub fn a64_cset_bound_form(inst: &MachInst) -> Option<A64CSetForm> {
    if inst.opcode != AArch64Opcode::CSet {
        return None;
    }
    let concrete = with_virtual_registers_numbered(inst).ok()?;
    let [dst, cond] = operands::<2>(&concrete).ok()?;
    let Operand::Gpr {
        width,
        name: GprName::Num(_),
    } = dst
    else {
        return None;
    };
    let Operand::Imm(encoding) = cond else {
        return None;
    };
    A64CSetForm::for_width_and_condition(width, cset_condition_from_encoding(encoding)?)
}

#[cfg(test)]
#[path = "aarch64_value_decode_proofs_tests.rs"]
mod tests;
