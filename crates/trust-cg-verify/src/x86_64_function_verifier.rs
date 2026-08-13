// trust-cg-verify/x86_64_function_verifier.rs - x86-64 function-level verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Provides verify_x86_64_function(): given an X86ISelFunction, walk every
// instruction, map each X86Opcode to a proof obligation from the
// ProofDatabase, run the proof, and produce a FunctionVerificationReport
// with per-instruction results.
//
// Mirror of [`crate::function_verifier`] (AArch64). The two paths share
// the same [`InstructionVerificationResult`] cert shape so downstream
// proof-certificate emission in `trust-cg-codegen::compiler` is identical
// across targets.
//
// Part of #465.

//! x86-64 function-level verification pipeline.
//!
//! [`verify_x86_64_function`] walks an [`X86ISelFunction`] and verifies
//! each instruction against its corresponding x86-64 lowering proof
//! obligation from [`ProofDatabase`]. Produces a
//! [`FunctionVerificationReport`] (shared with the AArch64 path) so the
//! public proof-certificate API in `trust-cg-codegen` stays target-agnostic.
//!
//! # Example
//!
//! ```rust,no_run
//! use trust_cg_lower::x86_64_isel::X86ISelFunction;
//! use trust_cg_lower::function::Signature;
//! use trust_cg_verify::x86_64_function_verifier::verify_x86_64_function;
//!
//! let func = X86ISelFunction::new("example".to_string(),
//!                                 Signature { params: vec![], returns: vec![] });
//! let report = verify_x86_64_function(&func);
//! println!("Coverage: {:.1}%", report.coverage_percent());
//! ```

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::x86_64_regs::{EAX, EDX, RAX, RDX};
use trust_cg_ir::{X86CondCode, X86Opcode};
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand, X86ProofOrigin};

use crate::function_verifier::{
    FunctionVerificationReport, InstructionOpcode, InstructionReport, InstructionVerificationResult,
};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, VerificationConfig};
use crate::proof_database::{
    ProofCategory, ProofDatabase, X86_BITFIELD_REPRESENTATIVE_LSB,
    X86_BITFIELD_REPRESENTATIVE_TYPE_BITS, X86_BITFIELD_REPRESENTATIVE_WIDTH,
    X86_EXTRACT_BITS_I32_PROOF_QUERY, X86_INSERT_BITS_I32_PROOF_QUERY,
    X86_SEXTRACT_BITS_I32_PROOF_QUERY,
};
use crate::provenance_xcheck::{
    self, LirSourceIndex, OpClass, ProvenanceXCheckMode, X86_PROVENANCE_XCHECK_DEFAULT,
};
use crate::smt::SmtExpr;
use crate::verify::VerificationResult;
use crate::x86_64_semantics::X86OperandSize;

// ===========================================================================
// Phase-2 operand reconstruction (x86-64 ALU) — task #66 (mirror of AArch64/RISC-V)
// ===========================================================================
//
// The static x86-64 ALU lowering proofs (x86_64_lowering_proofs.rs) build BOTH
// sides of an obligation from the SAME symbolic vars (proof "x86_64: Iadd_I32 ->
// ADD r32,r32": trust_ir = encode_trust_ir_binop(Iadd) = a.bvadd(b); the
// "machine" side is encode_add_rr = the SAME a.bvadd(b)). Those are STRUCTURALLY
// equal X==X, so the strict gate (#61) correctly counts them ZERO — a wrong isel
// opcode could never refute them. x86-64 emittable coverage was therefore honestly
// 36/137 under the strict gate (the ALU/bitwise/shift/extend families all RED).
//
// This RECONSTRUCTS the machine side FROM THE REAL EMITTED INSTRUCTION at verify
// time, EXACTLY mirroring the proven AArch64 / RISC-V pattern
// (`function_verifier::reconstruct_alu_obligation`,
// `riscv_function_verifier::reconstruct_alu_obligation`). The source side is built
// from the INTENDED source op over shared symbols; the machine side is built from
// the REAL opcode's x86-64 semantics encoder wired to the REAL positional
// operands. The two agree IFF isel emitted a semantically correct instruction. If
// isel emitted SUB for an Iadd, the machine side is bvsub and the source side is
// bvadd => REFUTE. A non-commutative op (SUB/shifts) wired with swapped inputs =>
// REFUTE. THAT is the content the credit rule counts.
//
// ANTI-f81e45b: this path performs NO `name.contains` lookup. The opcode->source
// binding is a TYPED, EXHAUSTIVE match ([`x86_opcode_to_source_op`]); the operand
// binding uses a TYPED per-opcode positional schema. Asserted by
// `tests/reconstruction_x86.rs`.
//
// TCB note (updated by TV-2): the "intended source op" used by the
// reconstruction is still derived from the emitted opcode, but on the
// compiler cert path (`verify_with_lir_source`) it is now CROSS-CHECKED
// against the TV-1 lowering-provenance stamp resolved in the REPLAYED LIR
// function: the stamped source instruction must exist, its recomputed digest
// must match the stamp, and its op class must be able to contain the emitted
// opcode's class ([`crate::provenance_xcheck`]) — a mismatch fails closed
// (default ENFORCE on x86-64). "ISel intended Iadd when it emitted AddRR" is
// no longer assumed; it is checked at op-class granularity. What remains
// trusted: exact-operand identity binding (deferred to TV-3's pre-pass walk)
// and paths that verify without a replayed LIR function (plain `verify`).
//
// x86 TWO-ADDRESS NOTE: the x86 ISel emits ALU ops in a THREE-address pseudo form
// `[dst, src1, src2]` (pre-regalloc) exactly like AArch64/RISC-V, so the positional
// schema is the same. The ONE exception is the SHL/SHR/SAR register form
// (`ShlRR`/`ShrRR`/`SarRR`), emitted as `[dst, src1]` because the count lives in
// the implicit CL register, not an operand — that form binds the count to a fresh
// symbolic var (the runtime CL value) plus the load-bearing count<width
// precondition. The immediate shift forms (`ShlRI`/…) carry `[dst, src1, imm]`.

/// SOURCE operand-schema arity of a reconstructed x86-64 ALU instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum X86AluArity {
    /// `[dst, src1, src2]` / `[dst, src1, imm]` / `[dst, src1]` (RR shift, count
    /// in CL) — two value-producing source slots (the second may be implicit CL).
    Binary,
    /// `[dst, src]` — one value-producing source slot (Neg/Not/extends).
    Unary,
}

impl X86AluArity {
    fn as_u8(self) -> u8 {
        match self {
            X86AluArity::Binary => 2,
            X86AluArity::Unary => 1,
        }
    }
}

/// The intended trust_ir SOURCE op family for a reconstructable x86-64 opcode,
/// resolved by a TYPED EXHAUSTIVE match (NOT a string lookup). Mirrors
/// `function_verifier::SourceOp` / `riscv_function_verifier::RiscVSourceOp`.
///
/// `trust_cg_lower::instructions::Opcode` is `Clone + PartialEq` but not
/// `Copy`/`Eq`, so this enum mirrors those bounds.
#[derive(Debug, Clone, PartialEq)]
enum X86SourceOp {
    /// Binary trust_ir arithmetic (`encode_trust_ir_binop`): Iadd/Isub/Imul.
    /// Machine side is the matching x86 ADD/SUB/IMUL encoder.
    Binary(trust_cg_lower::instructions::Opcode),
    /// Binary trust_ir BITWISE (`encode_trust_ir_bitwise_binop`): Band/Bor/Bxor.
    /// Machine side is the x86 AND/OR/XOR encoder.
    Bitwise(trust_cg_lower::instructions::Opcode),
    /// Binary trust_ir SHIFT (`encode_trust_ir_shift`): Ishl/Ushr/Sshr. Machine
    /// side is the FAITHFUL (count-masked) x86 SHL/SHR/SAR encoder, paired with a
    /// LOAD-BEARING `count < width` precondition (#57). Covers both the
    /// register-count CL form (Shl/Shr/SarRR) and immediate-count form
    /// (Shl/Shr/SarRI).
    Shift(trust_cg_lower::instructions::Opcode),
    /// Unary integer negate (trust_ir `Ineg`), via `encode_trust_ir_neg`.
    Neg,
    /// Unary bitwise NOT (trust_ir `Bnot`), via `encode_trust_ir_bnot`.
    Not,
    /// Unary signed integer extension (trust_ir `Sextend`), width-changing from
    /// `from_bits` to the destination width. Machine side is `encode_movsx`.
    Sextend { from_bits: u32 },
    /// Unary unsigned integer extension (trust_ir `Uextend`), width-changing from
    /// `from_bits` to the destination width. Machine side is `encode_movzx`.
    Uextend { from_bits: u32 },

    // --- Scalar floating-point (SSE/SSE2) — XMM operands, FP-typed leaves ---
    /// Binary scalar FP value op (`Addsd/ss`/`Subsd/ss`/`Mulsd/ss`/`Divsd/ss`),
    /// via `encode_trust_ir_fp_binop`. Machine = `encode_fp_add_rr` etc. The FP
    /// width comes from the XMM operand class (Fpr32→F32, Fpr64→F64). A wrong FP
    /// opcode (Addsd↔Subsd) refutes; a swapped non-commutative wiring (Sub/Div)
    /// refutes under the wiring-preserving FP evaluator.
    FpBinary(trust_cg_lower::instructions::Opcode),
    /// Unary scalar FP square root (`Sqrtsd`/`Sqrtss`), via
    /// `encode_trust_ir_fsqrt`; machine = `encode_fp_sqrt`.
    FpSqrt,
    /// Scalar FP hardware MIN/MAX (`Minsd/ss`/`Maxsd/ss`). NOT IEEE minNum: the
    /// SECOND operand wins on unordered/equal. Source = `encode_trust_ir_fminsd_hw`/
    /// `_fmaxsd_hw`; machine = `encode_fp_minsd`/`encode_fp_maxsd`. Non-commutative
    /// (NaN/signed-zero asymmetry) — a swapped wiring refutes.
    FpMinMax { is_min: bool },
    /// Scalar FP UNORD compare-to-mask (`Cmpsd/ss` imm8=3). Result is a width-wide
    /// bitvector mask (all-ones iff either operand is NaN). Source =
    /// `encode_trust_ir_cmp_unord_mask`; machine = `encode_fp_cmp_unord_mask`.
    /// Only the UNORD predicate (imm=3) reconstructs; other imm values fail closed.
    FpCmpUnord,
    /// FP→FP format convert (`Cvtsd2ss` narrow / `Cvtss2sd` widen). Source =
    /// `encode_trust_ir_fp_format_convert` keyed on the DEST format; machine =
    /// `encode_cvtsd2ss`/`encode_cvtss2sd`. Wrong direction refutes (FPToFP eval).
    FpFormatConvert { to_bits: u32 },
    /// FP→signed-int convert. `truncating` selects RTZ (`Cvttsd2si`/`Cvttss2si`)
    /// vs RNE (`Cvtsd2si`/`Cvtss2si`). Source = the x86-ISA-faithful
    /// `encode_trust_ir_fcvt_to_sint_x86`(`_rne`) reference (RTZ/RNE, INTEGER-
    /// INDEFINITE on NaN/+-Inf/overflow — #99, NOT saturating); machine = the
    /// matching `encode_cvt*si` (also IntegerIndefinite). A truncating-for-
    /// rounding mismatch refutes for a non-integral input.
    FpToSint { truncating: bool },
    /// signed-int→FP convert (`Cvtsi2sd`/`Cvtsi2ss`). The source is a BITVECTOR
    /// (sign-extended GPR64), so it is carried in `inputs` and verified by the
    /// standard BV evaluator. Source = `encode_trust_ir_fcvt_from_sint`; machine =
    /// `encode_cvtsi2sd`/`encode_cvtsi2ss`.
    SintToFp { to_bits: u32 },

    // --- Bit-manipulation (BMI/SSE4.2) — GPR operands, BV leaves ---
    /// Population count (`Popcnt`). Source = `encode_trust_ir_ctpop`; machine =
    /// `encode_popcnt`. Popcnt-for-Tzcnt refutes.
    Popcnt,
    /// Count-trailing-zeros (`Tzcnt`, defined zero=width). Source =
    /// `encode_trust_ir_cttz`; machine = `encode_tzcnt`.
    Tzcnt,
    /// Count-leading-zeros (`Lzcnt`, defined zero=width). Source =
    /// `encode_trust_ir_ctlz`; machine = `encode_lzcnt`.
    Lzcnt,
    /// Bit-scan-forward (`Bsf`): index of lowest set bit; coincides with TZCNT for
    /// nonzero inputs. Carries a LOAD-BEARING `src != 0` precondition (BSF(0) is
    /// architecturally undefined). Source = `encode_trust_ir_cttz`; machine =
    /// `encode_bsf`.
    Bsf,
    /// Bit-scan-reverse (`Bsr`): index of highest set bit `(width-1)-Ctlz`; carries
    /// a LOAD-BEARING `src != 0` precondition. Source = `encode_trust_ir_bsr_nonzero`;
    /// machine = `encode_bsr`.
    Bsr,
    /// x86 effective-address computation (LEA): `base + index*scale + disp`. The
    /// SOURCE side is the trust_ir integer composition (`Iadd`/`Imul` over the
    /// address components via `encode_trust_ir_binop`); the MACHINE side is the
    /// INDEPENDENT x86 `encode_lea_*` encoder (a different module). So the
    /// obligation is a GENUINE reconstruction — a buggy effective-address encoder
    /// refutes — exactly the "faithful independent EA encoder" the degenerate
    /// X==X LEA proofs (#62) were retracted pending. `has_index` distinguishes
    /// plain `Lea [base+disp]` (`MemAddr`) from SIB `LeaSib [base+index*scale+disp]`
    /// (`SibMemAddr`). RIP-relative `LeaRip` keeps its relocation proof.
    EffectiveAddress { has_index: bool },

    // --- Register copy (bit-preserving identity) — to-100% scalar batch ---
    /// GPR register-to-register copy (`MovRR`/`MovRR32`): a bit-preserving
    /// identity (`dst = src`). Source = trust_ir identity; machine =
    /// `encode_mov_rr` (also identity). A wrong opcode bound here uses a
    /// DIFFERENT machine encoder (e.g. `encode_neg`/`encode_not`) and REFUTES —
    /// see the wrong-machine-encoder refutation test. Operates over BV leaves.
    CopyGpr,
    /// XMM SCALAR register-to-register copy (`MovssRR`/`MovsdRR`): a
    /// bit-preserving scalar identity. Source = trust_ir identity over an FP
    /// leaf; machine = `encode_mov_rr` (identity). Width from the XMM class.
    CopyXmm,

    // --- Three-operand IMUL r,r/m,imm (signed multiply by a constant) ---
    /// `ImulRRI` (`dst = src * sign_extend(imm)`, wrapping low half). Source =
    /// `encode_trust_ir_binop(Imul, src, imm_const)`; machine = `encode_imul_rri`.
    /// Width-polymorphic (Gpr32/Gpr64 dest); a wrong imm injected at the builder
    /// refutes. NON-commutative in the sense that the imm is fixed, but the
    /// multiply is commutative so an operand swap is not observable (documented).
    ImulImm,

    // --- SSE4.1 scalar round-to-integral (ROUNDSD/ROUNDSS), mode-poly via imm8 ---
    /// `Roundsd`/`Roundss imm8`. The imm8[1:0] rounding-select picks
    /// floor(RTN)/ceil(RTP)/trunc(RTZ); the round-to-nearest mode (00) is never
    /// emitted (fail closed). Source = `encode_trust_ir_ffloor/fceil/ftrunc`
    /// (RTN/RTP/RTZ); machine = `encode_fp_round` with the SAME imm8. The native
    /// FP evaluator faithfully models all three rounding modes
    /// (`FPRoundToIntegral` -> `f64::floor/ceil/trunc`), so a wrong mode
    /// (floor-for-ceil) DIVERGES on a non-integral input (0.5/-0.5/PI) ⇒ REFUTE.
    Round,

    // --- SSE2/SSE4.1 PACKED INTEGER (lane-wise over the 128-bit XMM) ---
    /// LANE-WISE packed integer ARITHMETIC (`PADD{B,W,D,Q}`/`PSUB{B,W,D,Q}`/
    /// `PMULLW`/`PMULLD`). The two XMM operands are 128-bit vectors (carried as two
    /// 64-bit halves each); the MACHINE side is the real packed encoder
    /// (`encode_paddd` = `map_lanes_binary(...bvadd)` at the element width fixed by
    /// the opcode) and the SOURCE side is the trust_ir scalar op `map_lanes`-applied
    /// at the SAME arrangement (`encode_trust_ir_lanewise_binop`). A wrong lane op
    /// (PADD-for-PSUB) diverges in every lane, and a wrong lane WIDTH (i16x8 vs
    /// i32x4) crosses the carry/borrow boundary at the wrong place ⇒ REFUTE.
    PackedIntBinary {
        op: trust_cg_lower::instructions::Opcode,
        arrangement: crate::smt::VectorArrangement,
    },
    /// LANE-WISE packed integer COMPARE-MASK (`PCMPEQ{B,W,D,Q}`/`PCMPGT{B,W,D,Q}`).
    /// Each lane yields an all-ones/all-zero mask. MACHINE = `encode_pcmpeqb` etc;
    /// SOURCE = `encode_trust_ir_lanewise_cmp_mask` at the SAME arrangement. A wrong
    /// predicate (Eq-for-Sgt) or wrong lane width ⇒ REFUTE.
    PackedIntCmp {
        cond: trust_cg_lower::instructions::IntCC,
        arrangement: crate::smt::VectorArrangement,
    },
    /// FULL-WIDTH packed BITWISE (`PAND`/`POR`/`PXOR`/`PANDN`; `ANDPS`/`ANDPD` =
    /// FP-domain AND). Bitwise ops are lane-independent, so the full-width SmtExpr op
    /// IS the lane-wise reconstruction. MACHINE = `encode_pand`/`encode_pandn` etc;
    /// SOURCE = `encode_trust_ir_v128_bitwise`. A wrong op (PAND-for-PXOR) or the
    /// PANDN operand-complement asymmetry ((~a)&b vs a&(~b)) ⇒ REFUTE.
    PackedV128Bitwise(trust_cg_lower::instructions::Opcode),
    /// HORIZONTAL packed byte sum-of-absolute-differences (`PSADBW xmm, xmm`) —
    /// the ONE x86 op the verifier models across-lanes rather than lane-wise.
    /// MACHINE = `encode_psadbw` (`Σ_{i in group} |a.byte_i - b.byte_i|` into each
    /// of two u64 lanes); SOURCE = `encode_trust_ir_byte_sad` (the same reduction
    /// spec, independently written). A wrong emitted opcode reconstructs to a
    /// different (e.g. lane-wise PADDB) machine expression and REFUTES. The
    /// vectorizer emits it only as `PSADBW data, 0` (its byte-sum tier), where
    /// `|x-0| = x`; that operand fact is the vectorizer's construction-time
    /// responsibility, exactly like every recognizer's loop-equivalence — this
    /// per-instruction obligation certifies the general SAD semantic.
    PsadbwByteSad,

    // --- MEMORY loads/stores (genuine effective-address reconstruction) ---
    /// Integer/FP memory LOAD (`MovRM8/16/32/(64)`, `MovssRM`/`MovsdRM`). The
    /// SOURCE side is `MemLoad(ir_ea, load_bits, unsigned)` where `ir_ea` is the
    /// trust_ir effective-address composition (`base [+ index*scale] + disp` via
    /// `encode_trust_ir_binop`); the MACHINE side is `MemLoad(machine_ea, ...)`
    /// where `machine_ea` is the INDEPENDENT x86 `encode_lea_*` effective-address
    /// encoder over the SAME real operands. The deterministic [`SmtExpr::MemLoad`]
    /// memory model makes `load(ea_m) == load(ea_ir) <=> ea_m == ea_ir`, so a
    /// wrong base/index/scale/disp REFUTES (a different EA reads a different value),
    /// and `load_bits` participating in the value makes a wrong access width REFUTE.
    /// `load_bits` is fixed by the opcode; the dest register class fixes the
    /// result width. x86 plain MOV loads are zero-fill (no sign-extension), exactly
    /// like the trust_ir Load of a sub-register value — so `signed = false`.
    MemLoad { load_bits: u32 },
    /// Integer/FP memory STORE (`MovMR8/16/32/(64)`, `MovssMR`/`MovsdMR`). Operand
    /// shape `[MemAddr/SibMemAddr, value]`. The obligation equates
    /// `concat(machine_ea, value)` with `concat(ir_ea, value)`: a wrong EA REFUTES
    /// (the address half differs) AND the value half ties the stored register to
    /// the IR store value (a dropped/swapped value would diverge). Same independent
    /// EA encoders as the load family.
    MemStore { store_bits: u32 },

    // --- PACKED 128-bit XMM memory MOVES (MOVDQU/MOVDQA RM/MR) ---
    /// Whole-XMM 128-bit memory LOAD (`MovdquRM`/`MovdqaRM`: `xmm <- [ea]`),
    /// emitted for a whole-`Fpr128` reload/spill of a 128-bit vector value.
    /// Modeled as TWO 64-bit halves at effective addresses `ea` (low 64 bits) and
    /// `ea+8` (high 64 bits) — LITTLE-ENDIAN, so `value[63:0]` are the 8 bytes at
    /// `ea` and `value[127:64]` are the 8 bytes at `ea+8`. Both halves reuse the
    /// PROVEN scalar effective-address machinery: the SOURCE addresses are the
    /// trust_ir `encode_trust_ir_binop` composition (`ea`, `ea+8`) and the MACHINE
    /// addresses the INDEPENDENT x86 `encode_lea_*` EA (`ea`, `ea+8`). The
    /// deterministic [`SmtExpr::MemLoad`] model makes a wrong base/index/scale/disp
    /// (a wrong EA), a SWAPPED half (low/high addresses exchanged), or a wrong half
    /// OFFSET (`ea+16` for `ea+8`) read different bytes ⇒ REFUTE; a wrong access
    /// WIDTH (a 32-bit half) diverges in the value ⇒ REFUTE. `aligned` = `MOVDQA`
    /// (SSE `MOVDQA` #GP-faults on a non-16-aligned `ea`), which carries the HONEST
    /// precondition `ea % 16 == 0`; `MOVDQU` (unaligned) carries no such
    /// precondition. The alignment assumption is modeled ONLY as a precondition and
    /// never weakens the value equality (a bad/unaligned access cannot be credited
    /// — see the `movdqa_*_alignment_*` refutation tests).
    V128MemLoad { aligned: bool },
    /// Whole-XMM 128-bit memory STORE (`MovdquMR`/`MovdqaMR`: `[ea] <- xmm`).
    /// Operand shape `[MemAddr/SibMemAddr, value_xmm]`. Modeled as TWO 64-bit half
    /// stores: `value[63:0]` to `[ea]` and `value[127:64]` to `[ea+8]`
    /// (little-endian). Each half's observable folds the stored value half with the
    /// deterministic address hash of its target slot (`half_val + load(slot_ea)`,
    /// per-64-bit so no carry crosses the half boundary): a wrong EA loads a
    /// different address hash ⇒ REFUTE, a SWAPPED half puts the wrong value at a
    /// slot ⇒ REFUTE (the halves are independent fresh leaves), a dropped/wrong
    /// value half diverges ⇒ REFUTE. `aligned` carries the same `ea % 16 == 0`
    /// precondition semantics as the load.
    V128MemStore { aligned: bool },

    // --- MEMORY-source ALU (reg OP load(ea)) ---
    /// Register-memory ALU (`AddRM`/`SubRM`/`CmpRM`/`ImulRM`): `dst = reg OP
    /// load(ea)`. The SOURCE side is `trust_ir(reg OP MemLoad(ir_ea))`; the MACHINE
    /// side is `x86(reg OP MemLoad(machine_ea))` with the REAL ALU encoder and the
    /// independent EA encoder. A wrong ALU opcode (Add-for-Sub) REFUTES (different
    /// arithmetic), and a wrong EA REFUTES (different loaded operand). `CmpRM`
    /// produces the SUB-difference (the value whose flags CMP sets); a wrong
    /// predicate maps to a different difference and REFUTES. `ImulRM` is the
    /// register-memory signed multiply `dst = reg * load(ea)` (low half, wrapping).
    MemAlu {
        op: trust_cg_lower::instructions::Opcode,
    },

    // --- IN-PLACE increment/decrement over a symbolic pre-value ---
    /// In-place `Inc`/`Dec` (`dst = pre +/- 1`). The SOURCE side is the trust_ir
    /// `Iadd`/`Isub` of a FRESH symbolic pre-value leaf with `1`; the MACHINE side
    /// is the x86 `encode_add_rr`/`encode_sub_rr` of the SAME pre-value with `1`.
    /// Inc-as-Dec (or vice versa) maps `pre + 1` against `pre - 1`, which diverge
    /// for every pre-value ⇒ REFUTE.
    InPlaceIncDec { is_inc: bool },

    // --- DIVISION (implicit RDX:RAX dividend) ---
    /// `Idiv`/`Div`: the divisor is the single explicit operand; the dividend is
    /// the IMPLICIT double-width `RDX:RAX` set up by a prior `CDQ`/`CQO`
    /// (sign-extend) or `XOR edx,edx` (zero-extend) plus a `MOV` of the value
    /// into `RAX`. We model the dividend as a FRESH single-width `recon_rax` leaf
    /// EXTENDED to double width on the machine side — SIGNED (`signed=true`,
    /// `IDIV`: `sext(rax, 2W)` = the CDQ/CQO step) or UNSIGNED (`Div`:
    /// `zext(rax, 2W)`). The machine quotient is `trunc(sdiv/udiv(dividend_2W,
    /// ext(divisor, 2W)), W)` and the machine remainder is the matching
    /// `srem/urem`; the obligation equates `concat(quotient, remainder)` against
    /// the trust_ir single-width `Sdiv/Srem` (signed) or `Udiv/Urem` (unsigned)
    /// of `(rax, divisor)`. PRECONDITION: divisor != 0 AND no signed overflow
    /// (`!(rax == INT_MIN && divisor == -1)`). An IDIV-emitted-as-DIV bug
    /// (sext-vs-zext / sdiv-vs-udiv) DIVERGES on a NEGATIVE dividend ⇒ REFUTE.
    Division { signed: bool },

    // --- CONDITIONAL MOVE (implicit RFLAGS condition) ---
    /// `Cmovcc`/`Cmovcc32`: `dst = cc ? src : dst_old`. The select condition is
    /// the IMPLICIT RFLAGS of a prior `CMP a, b`, NOT an operand. We model it as a
    /// genuine CMP+CMOV PAIR: the MACHINE side is
    /// `ite(eval_int_condition(cc, flags_of(a, b)), src, dst_old)` (the textbook
    /// hardware cc formula over the CMP flags); the SOURCE side is
    /// `ite(icmp(intcc_for(cc), a, b), src, dst_old)`. The cc comes from the real
    /// `CondCode` operand. A WRONG cc (E-for-NE, L-for-GE) produces the
    /// COMPLEMENTARY boolean over the same `(a, b)` ⇒ the selects pick different
    /// operands ⇒ REFUTE. The condition is a DISTINCT formula per cc (never a
    /// single abstract boolean), so the ccs are not vacuously equivalent.
    CondMove,

    // --- SSE/SSE2 PACKED FLOATING-POINT (per-lane, FP-typed) ---
    /// LANE-WISE packed FP binary (`ADDPS/SUBPS/MULPS/DIVPS` = 4×binary32;
    /// `ADDPD/SUBPD/MULPD/DIVPD` = 2×binary64). The packed op is N independent
    /// identical scalar FP ops, so one representative FP lane witnesses the full
    /// vector (mirrors the existing scalar `FpBinary` reconstruction). MACHINE =
    /// `encode_packed_fp_add_lane` etc; SOURCE = `encode_trust_ir_fp_binop` at the
    /// lane width fixed by the opcode (PS=F32, PD=F64). A wrong op (ADDPS-for-SUBPS)
    /// DIVERGES under the FP evaluator ⇒ REFUTE.
    PackedFpBinary {
        op: trust_cg_lower::instructions::Opcode,
        /// Lane width in bits: 32 (PS / binary32) or 64 (PD / binary64).
        lane_bits: u32,
    },
}

/// Resolve the INTENDED trust_ir source op + operand schema for a reconstructable
/// x86-64 opcode via a TYPED, EXHAUSTIVE match — NOT a string lookup
/// (anti-f81e45b). Mirrors `function_verifier::opcode_to_source_op`.
///
/// Reconstructable set (the ALU/bitwise/shift/extend families):
/// - ALU:     `AddRR`/`AddRI`->Iadd, `SubRR`/`SubRI`->Isub, `ImulRR`->Imul,
///   `Neg`->Ineg
/// - BITWISE: `AndRR`/`AndRI`->Band, `OrRR`/`OrRI`->Bor, `XorRR`/`XorRI`->Bxor,
///   `Not`->Bnot
/// - SHIFTS:  `ShlRR`/`ShlRI`->Ishl, `ShrRR`/`ShrRI`->Ushr, `SarRR`/`SarRI`->Sshr
/// - EXTENDS: `Movzx`(I8)->Uextend, `MovzxW`(I16)->Uextend; `MovsxB`(I8)->Sextend,
///   `MovsxW`(I16)->Sextend, `Movsx`(MOVSXD, I32)->Sextend
///
/// The destination width is taken from the destination register in
/// [`reconstruct_alu_obligation`]; for the extends the SOURCE width (`from_bits`)
/// is fixed by the opcode (byte/word/dword) and the destination width (`to_bits`)
/// is the dst register width.
///
/// Returns `None` for every NON-reconstructable opcode, so the caller leaves
/// those on their existing path unchanged. Wildcard-free over the reconstructable
/// arms; falls through to `None` for the rest.
fn x86_opcode_to_source_op(opcode: X86Opcode) -> Option<(X86SourceOp, X86AluArity)> {
    use crate::smt::VectorArrangement as VA;
    use X86Opcode as O;
    use trust_cg_lower::instructions::{IntCC, Opcode};
    match opcode {
        // ---- Integer ALU ----
        O::AddRR | O::AddRI => Some((X86SourceOp::Binary(Opcode::Iadd), X86AluArity::Binary)),
        O::SubRR | O::SubRI => Some((X86SourceOp::Binary(Opcode::Isub), X86AluArity::Binary)),
        O::ImulRR => Some((X86SourceOp::Binary(Opcode::Imul), X86AluArity::Binary)),
        O::Neg => Some((X86SourceOp::Neg, X86AluArity::Unary)),

        // ---- Bitwise (commutative And/Or/Xor; unary Not) ----
        O::AndRR | O::AndRI => Some((X86SourceOp::Bitwise(Opcode::Band), X86AluArity::Binary)),
        O::OrRR | O::OrRI => Some((X86SourceOp::Bitwise(Opcode::Bor), X86AluArity::Binary)),
        O::XorRR | O::XorRI => Some((X86SourceOp::Bitwise(Opcode::Bxor), X86AluArity::Binary)),
        O::Not => Some((X86SourceOp::Not, X86AluArity::Unary)),

        // ---- Shifts — load-bearing count<width precond (#57) ----
        O::ShlRR | O::ShlRI => Some((X86SourceOp::Shift(Opcode::Ishl), X86AluArity::Binary)),
        O::ShrRR | O::ShrRI => Some((X86SourceOp::Shift(Opcode::Ushr), X86AluArity::Binary)),
        O::SarRR | O::SarRI => Some((X86SourceOp::Shift(Opcode::Sshr), X86AluArity::Binary)),

        // ---- Extends (unary, width-changing). from_bits fixed by the opcode. ----
        O::Movzx => Some((X86SourceOp::Uextend { from_bits: 8 }, X86AluArity::Unary)),
        O::MovzxW => Some((X86SourceOp::Uextend { from_bits: 16 }, X86AluArity::Unary)),
        O::MovsxB => Some((X86SourceOp::Sextend { from_bits: 8 }, X86AluArity::Unary)),
        O::MovsxW => Some((X86SourceOp::Sextend { from_bits: 16 }, X86AluArity::Unary)),
        // MOVSXD r64, r/m32: always i32 -> i64.
        O::Movsx => Some((X86SourceOp::Sextend { from_bits: 32 }, X86AluArity::Unary)),

        // ---- Scalar FP binary value ops (commutative: Add/Mul; non-comm: Sub/Div) ----
        O::Addsd | O::Addss => Some((X86SourceOp::FpBinary(Opcode::Fadd), X86AluArity::Binary)),
        O::Subsd | O::Subss => Some((X86SourceOp::FpBinary(Opcode::Fsub), X86AluArity::Binary)),
        O::Mulsd | O::Mulss => Some((X86SourceOp::FpBinary(Opcode::Fmul), X86AluArity::Binary)),
        O::Divsd | O::Divss => Some((X86SourceOp::FpBinary(Opcode::Fdiv), X86AluArity::Binary)),

        // ---- Scalar FP unary sqrt ----
        O::Sqrtsd | O::Sqrtss => Some((X86SourceOp::FpSqrt, X86AluArity::Unary)),

        // ---- Scalar FP hardware MIN/MAX (non-commutative: src wins on NaN/eq) ----
        O::Minsd | O::Minss => Some((X86SourceOp::FpMinMax { is_min: true }, X86AluArity::Binary)),
        O::Maxsd | O::Maxss => Some((X86SourceOp::FpMinMax { is_min: false }, X86AluArity::Binary)),

        // ---- Scalar FP UNORD compare-to-mask (imm8=3 only) ----
        O::Cmpsd | O::Cmpss => Some((X86SourceOp::FpCmpUnord, X86AluArity::Binary)),

        // ---- FP<->FP format casts ----
        O::Cvtsd2ss => Some((
            X86SourceOp::FpFormatConvert { to_bits: 32 },
            X86AluArity::Unary,
        )),
        O::Cvtss2sd => Some((
            X86SourceOp::FpFormatConvert { to_bits: 64 },
            X86AluArity::Unary,
        )),

        // ---- FP->signed-int: BOTH the TRUNCATING (RTZ) CVTT* and the
        // ROUND-TO-NEAREST-EVEN (RNE) CVTSD2SI/CVTSS2SI forms are reconstructed.
        //
        // The evaluator FAITHFULLY models the rounding mode of `FPToSBv` (smt.rs
        // `try_eval`: round per `rm`) AND, for the x86 CVT[T]*2SI machine encoders,
        // the x86 INTEGER-INDEFINITE out-of-range semantics (#99: NaN/+-Inf/
        // overflow -> 0x80..0, NOT saturating). So:
        //   * CVTT* (truncating: true)  -> source x86 `fp.to_sbv(RTZ, indef)` ==
        //     machine RTZ;
        //   * CVTSD2SI/CVTSS2SI (false) -> source x86 `fp.to_sbv(RNE, indef)` ==
        //     machine RNE.
        // A truncating-for-rounding lowering bug (CVTT bound where CVT was intended,
        // or vice versa) DIVERGES on a non-integral tie input (1.5 -> RTZ 1 vs
        // RNE 2) ⇒ REFUTE.
        O::Cvttsd2si | O::Cvttss2si => Some((
            X86SourceOp::FpToSint { truncating: true },
            X86AluArity::Unary,
        )),
        O::Cvtsd2si | O::Cvtss2si => Some((
            X86SourceOp::FpToSint { truncating: false },
            X86AluArity::Unary,
        )),

        // ---- signed-int->FP (source is a sign-extended GPR64 bitvector) ----
        O::Cvtsi2sd => Some((X86SourceOp::SintToFp { to_bits: 64 }, X86AluArity::Unary)),
        O::Cvtsi2ss => Some((X86SourceOp::SintToFp { to_bits: 32 }, X86AluArity::Unary)),

        // ---- Bit-manipulation (GPR operands) ----
        O::Popcnt => Some((X86SourceOp::Popcnt, X86AluArity::Unary)),
        O::Tzcnt => Some((X86SourceOp::Tzcnt, X86AluArity::Unary)),
        O::Lzcnt => Some((X86SourceOp::Lzcnt, X86AluArity::Unary)),
        O::Bsf => Some((X86SourceOp::Bsf, X86AluArity::Unary)),
        O::Bsr => Some((X86SourceOp::Bsr, X86AluArity::Unary)),

        // ---- Effective address (LEA): base[+index*scale]+disp ----
        // Plain LEA carries one register source (base); SIB LEA carries two
        // (base, index). The address-mode operand is read in
        // `reconstruct_alu_obligation` BEFORE the Unary/Binary register-operand
        // dispatch. `LeaRip` (RIP-relative) is NOT here — it keeps its relocation
        // proof.
        O::Lea => Some((
            X86SourceOp::EffectiveAddress { has_index: false },
            X86AluArity::Unary,
        )),
        O::LeaSib => Some((
            X86SourceOp::EffectiveAddress { has_index: true },
            X86AluArity::Binary,
        )),

        // ---- Register copy (bit-preserving identity) ----
        O::MovRR | O::MovRR32 => Some((X86SourceOp::CopyGpr, X86AluArity::Unary)),
        O::MovssRR | O::MovsdRR => Some((X86SourceOp::CopyXmm, X86AluArity::Unary)),

        // ---- Three-operand IMUL r,r/m,imm ----
        O::ImulRRI => Some((X86SourceOp::ImulImm, X86AluArity::Binary)),

        // ---- SSE4.1 scalar round-to-integral (mode-poly via imm8) ----
        O::Roundsd | O::Roundss => Some((X86SourceOp::Round, X86AluArity::Unary)),

        // ---- SSE2/SSE4.1 packed integer ARITHMETIC (lane-wise, element width
        //      fixed by the opcode: B=i8x16, W=i16x8, D=i32x4, Q=i64x2) ----
        O::Paddb => Some((pack_arith(Opcode::Iadd, VA::B16), X86AluArity::Binary)),
        O::Paddw => Some((pack_arith(Opcode::Iadd, VA::H8), X86AluArity::Binary)),
        O::Paddd => Some((pack_arith(Opcode::Iadd, VA::S4), X86AluArity::Binary)),
        O::Paddq => Some((pack_arith(Opcode::Iadd, VA::D2), X86AluArity::Binary)),
        O::Psubb => Some((pack_arith(Opcode::Isub, VA::B16), X86AluArity::Binary)),
        O::Psubw => Some((pack_arith(Opcode::Isub, VA::H8), X86AluArity::Binary)),
        O::Psubd => Some((pack_arith(Opcode::Isub, VA::S4), X86AluArity::Binary)),
        O::Psubq => Some((pack_arith(Opcode::Isub, VA::D2), X86AluArity::Binary)),
        // Low-half packed multiply (signed/unsigned agree mod 2^lane).
        O::Pmullw => Some((pack_arith(Opcode::Imul, VA::H8), X86AluArity::Binary)),
        O::Pmulld => Some((pack_arith(Opcode::Imul, VA::S4), X86AluArity::Binary)),
        O::Psadbw => Some((X86SourceOp::PsadbwByteSad, X86AluArity::Binary)),

        // ---- SSE2/SSE4.1 packed integer COMPARE-MASK (Eq / signed-Gt) ----
        O::Pcmpeqb => Some((pack_cmp(IntCC::Equal, VA::B16), X86AluArity::Binary)),
        O::Pcmpeqw => Some((pack_cmp(IntCC::Equal, VA::H8), X86AluArity::Binary)),
        O::Pcmpeqd => Some((pack_cmp(IntCC::Equal, VA::S4), X86AluArity::Binary)),
        O::Pcmpeqq => Some((pack_cmp(IntCC::Equal, VA::D2), X86AluArity::Binary)),
        O::Pcmpgtb => Some((
            pack_cmp(IntCC::SignedGreaterThan, VA::B16),
            X86AluArity::Binary,
        )),
        O::Pcmpgtw => Some((
            pack_cmp(IntCC::SignedGreaterThan, VA::H8),
            X86AluArity::Binary,
        )),
        O::Pcmpgtd => Some((
            pack_cmp(IntCC::SignedGreaterThan, VA::S4),
            X86AluArity::Binary,
        )),
        O::Pcmpgtq => Some((
            pack_cmp(IntCC::SignedGreaterThan, VA::D2),
            X86AluArity::Binary,
        )),

        // ---- Full-width packed BITWISE (lane-independent) ----
        O::Pand => Some((
            X86SourceOp::PackedV128Bitwise(Opcode::Band),
            X86AluArity::Binary,
        )),
        O::Por => Some((
            X86SourceOp::PackedV128Bitwise(Opcode::Bor),
            X86AluArity::Binary,
        )),
        O::Pxor => Some((
            X86SourceOp::PackedV128Bitwise(Opcode::Bxor),
            X86AluArity::Binary,
        )),
        O::Pandn => Some((
            X86SourceOp::PackedV128Bitwise(Opcode::BandNot),
            X86AluArity::Binary,
        )),
        // ANDPS/ANDPD: the SAME 128-bit AND PAND computes, FP-domain encoded
        // (select_fabs sign-mask clear). Lane-independent bitwise AND.
        O::Andps | O::Andpd => Some((
            X86SourceOp::PackedV128Bitwise(Opcode::Band),
            X86AluArity::Binary,
        )),

        // ---- SSE/SSE2 packed FLOATING-POINT (per-lane: PS=F32, PD=F64) ----
        O::Addps => Some((pack_fp(Opcode::Fadd, 32), X86AluArity::Binary)),
        O::Subps => Some((pack_fp(Opcode::Fsub, 32), X86AluArity::Binary)),
        O::Mulps => Some((pack_fp(Opcode::Fmul, 32), X86AluArity::Binary)),
        O::Divps => Some((pack_fp(Opcode::Fdiv, 32), X86AluArity::Binary)),
        O::Addpd => Some((pack_fp(Opcode::Fadd, 64), X86AluArity::Binary)),
        O::Subpd => Some((pack_fp(Opcode::Fsub, 64), X86AluArity::Binary)),
        O::Mulpd => Some((pack_fp(Opcode::Fmul, 64), X86AluArity::Binary)),
        O::Divpd => Some((pack_fp(Opcode::Fdiv, 64), X86AluArity::Binary)),

        // ---- MEMORY loads: width fixed by the opcode (8/16/32/64; FP 32/64) ----
        O::MovRM8 => Some((X86SourceOp::MemLoad { load_bits: 8 }, X86AluArity::Unary)),
        O::MovRM16 => Some((X86SourceOp::MemLoad { load_bits: 16 }, X86AluArity::Unary)),
        O::MovRM32 => Some((X86SourceOp::MemLoad { load_bits: 32 }, X86AluArity::Unary)),
        O::MovRM => Some((X86SourceOp::MemLoad { load_bits: 64 }, X86AluArity::Unary)),
        // Scaled-index 64-bit LOAD `mov r64, [base+index*scale+disp]`. Same
        // MemLoad proof as MovRM — the shared `x86_reconstruct_effective_address`
        // already reconstructs the `SibMemAddr` EA (`base + index*scale + disp`)
        // on both the IR and INDEPENDENT machine encoders, so a wrong
        // base/index/scale/disp REFUTES. The OPCODE (not the operand shape) fixes
        // load_bits = 64 (MovRMSib is the REX.W 64-bit MOV load only).
        O::MovRMSib => Some((X86SourceOp::MemLoad { load_bits: 64 }, X86AluArity::Unary)),
        // 8-bit SIB sibling: load_bits = 8, fixed by the OPCODE exactly as for
        // MovRM8. Same shared SibMemAddr EA reconstruction as MovRMSib.
        O::MovRM8Sib => Some((X86SourceOp::MemLoad { load_bits: 8 }, X86AluArity::Unary)),
        // 32-bit SIB sibling: same shared SibMemAddr EA reconstruction, the
        // OPCODE fixes load_bits = 32 (no REX.W).
        O::MovRM32Sib => Some((X86SourceOp::MemLoad { load_bits: 32 }, X86AluArity::Unary)),
        O::MovssRM => Some((X86SourceOp::MemLoad { load_bits: 32 }, X86AluArity::Unary)),
        O::MovsdRM => Some((X86SourceOp::MemLoad { load_bits: 64 }, X86AluArity::Unary)),
        // Scalar-FP SIB loads: the COMPOSITION of the two cases above. The EA
        // comes from the same shared `x86_reconstruct_effective_address` that
        // proves MovRMSib (so a wrong base/index/scale/disp REFUTES), and the
        // loaded value is the same MemLoad obligation that proves MovsdRM /
        // MovssRM. The OPCODE fixes the width: 64 for sd, 32 for ss.
        O::MovsdRMSib => Some((X86SourceOp::MemLoad { load_bits: 64 }, X86AluArity::Unary)),
        O::MovssRMSib => Some((X86SourceOp::MemLoad { load_bits: 32 }, X86AluArity::Unary)),

        // ---- MEMORY stores: width fixed by the opcode ----
        O::MovMR8 => Some((X86SourceOp::MemStore { store_bits: 8 }, X86AluArity::Binary)),
        O::MovMR16 => Some((
            X86SourceOp::MemStore { store_bits: 16 },
            X86AluArity::Binary,
        )),
        O::MovMR32 => Some((
            X86SourceOp::MemStore { store_bits: 32 },
            X86AluArity::Binary,
        )),
        O::MovMR => Some((
            X86SourceOp::MemStore { store_bits: 64 },
            X86AluArity::Binary,
        )),
        // Scaled-index 64-bit STORE `mov [base+index*scale+disp], r64`. Same
        // MemStore proof as MovMR — `x86_reconstruct_effective_address` handles
        // the `SibMemAddr` EA, and the obligation ties the stored register to the
        // IR store value while a wrong EA REFUTES. store_bits = 64 (REX.W only).
        O::MovMRSib => Some((
            X86SourceOp::MemStore { store_bits: 64 },
            X86AluArity::Binary,
        )),
        // 32-bit SIB sibling: store_bits = 32, same SibMemAddr EA model.
        O::MovMR32Sib => Some((
            X86SourceOp::MemStore { store_bits: 32 },
            X86AluArity::Binary,
        )),
        // 8-bit SIB sibling: store_bits = 8, same SibMemAddr EA model. This is
        // the byte-array store that had no indexed form at all before.
        O::MovMR8Sib => Some((X86SourceOp::MemStore { store_bits: 8 }, X86AluArity::Binary)),
        O::MovssMR => Some((
            X86SourceOp::MemStore { store_bits: 32 },
            X86AluArity::Binary,
        )),
        O::MovsdMR => Some((
            X86SourceOp::MemStore { store_bits: 64 },
            X86AluArity::Binary,
        )),

        // ---- PACKED 128-bit XMM memory MOVES: two 64-bit halves at ea / ea+8 ----
        // MOVDQU (unaligned) vs MOVDQA (aligned) differ ONLY in the aligned flag,
        // which carries the honest `ea % 16 == 0` precondition on the aligned form.
        O::MovdquRM => Some((
            X86SourceOp::V128MemLoad { aligned: false },
            X86AluArity::Unary,
        )),
        O::MovdqaRM => Some((
            X86SourceOp::V128MemLoad { aligned: true },
            X86AluArity::Unary,
        )),
        O::MovdquMR => Some((
            X86SourceOp::V128MemStore { aligned: false },
            X86AluArity::Binary,
        )),
        O::MovdqaMR => Some((
            X86SourceOp::V128MemStore { aligned: true },
            X86AluArity::Binary,
        )),

        // ---- MEMORY-source ALU: reg OP load(ea) ----
        O::AddRM => Some((
            X86SourceOp::MemAlu { op: Opcode::Iadd },
            X86AluArity::Binary,
        )),
        O::SubRM => Some((
            X86SourceOp::MemAlu { op: Opcode::Isub },
            X86AluArity::Binary,
        )),
        // CmpRM's observable value is the SUB difference (the value CMP's flags
        // reflect): a wrong predicate maps to a different difference and refutes.
        O::CmpRM => Some((
            X86SourceOp::MemAlu { op: Opcode::Isub },
            X86AluArity::Binary,
        )),

        // Register-memory signed multiply `dst = reg * load(ea)` (low half).
        // The SIB sibling shares the identical value semantics; only the EA
        // shape differs, and `x86_reconstruct_effective_address` models both.
        O::ImulRM | O::ImulRMSib => Some((
            X86SourceOp::MemAlu { op: Opcode::Imul },
            X86AluArity::Binary,
        )),

        // ---- IN-PLACE increment / decrement ----
        O::Inc => Some((
            X86SourceOp::InPlaceIncDec { is_inc: true },
            X86AluArity::Unary,
        )),
        O::Dec => Some((
            X86SourceOp::InPlaceIncDec { is_inc: false },
            X86AluArity::Unary,
        )),

        // ---- DIVISION (implicit RDX:RAX dividend) ----
        O::Idiv => Some((X86SourceOp::Division { signed: true }, X86AluArity::Unary)),
        O::Div => Some((X86SourceOp::Division { signed: false }, X86AluArity::Unary)),

        // ---- CONDITIONAL MOVE (implicit RFLAGS condition) ----
        O::Cmovcc | O::Cmovcc32 => Some((X86SourceOp::CondMove, X86AluArity::Binary)),

        // All non-reconstructable opcodes keep their existing DB-substring path.
        _ => None,
    }
}

/// Compact constructor for a packed-integer-arithmetic source op.
fn pack_arith(
    op: trust_cg_lower::instructions::Opcode,
    arrangement: crate::smt::VectorArrangement,
) -> X86SourceOp {
    X86SourceOp::PackedIntBinary { op, arrangement }
}

/// Compact constructor for a packed-integer-compare-mask source op.
fn pack_cmp(
    cond: trust_cg_lower::instructions::IntCC,
    arrangement: crate::smt::VectorArrangement,
) -> X86SourceOp {
    X86SourceOp::PackedIntCmp { cond, arrangement }
}

/// Compact constructor for a packed-FP-binary source op.
fn pack_fp(op: trust_cg_lower::instructions::Opcode, lane_bits: u32) -> X86SourceOp {
    X86SourceOp::PackedFpBinary { op, lane_bits }
}

/// TV-2: the DEFINITE semantic [`OpClass`] of an emitted x86-64 instruction,
/// derived from the SAME typed [`x86_opcode_to_source_op`] binding the cert's
/// reconstruction path uses — or `None` when the instruction carries no
/// definite class (unmapped opcodes, and universal lowering GLUE that any
/// source may legitimately emit: register copies, extends of narrow carriers,
/// plain loads/stores for spill/staging traffic, LEA address materialization,
/// and the `XOR r,r` / `PXOR x,x` zero idioms).
///
/// `None` exempts the instruction from the class-consistency half of the
/// provenance cross-check only; the attribution-integrity half (dangling
/// coordinates / digest mismatch) still applies to every stamped instruction.
fn x86_emitted_op_class(inst: &X86ISelInst) -> Option<OpClass> {
    // Zero idiom: XOR/PXOR of a register with itself materializes 0 — that
    // is constant-materialization glue, not a semantic Bxor claim.
    if matches!(inst.opcode, X86Opcode::XorRR | X86Opcode::Pxor)
        && inst.operands.len() == 3
        && inst.operands[1] == inst.operands[2]
    {
        return None;
    }

    let (source_op, _) = x86_opcode_to_source_op(inst.opcode)?;
    let int_binop_class = |op: &trust_cg_lower::instructions::Opcode| -> Option<OpClass> {
        use trust_cg_lower::instructions::Opcode as LirOp;
        match op {
            LirOp::Iadd => Some(OpClass::IntAdd),
            LirOp::Isub => Some(OpClass::IntSub),
            LirOp::Imul => Some(OpClass::IntMul),
            _ => None,
        }
    };
    match &source_op {
        X86SourceOp::Binary(op) | X86SourceOp::MemAlu { op } => int_binop_class(op),
        X86SourceOp::Bitwise(_) | X86SourceOp::Not => Some(OpClass::Bitwise),
        X86SourceOp::Shift(_) => Some(OpClass::Shift),
        X86SourceOp::Neg => Some(OpClass::IntNeg),
        // Universal glue: exempt from the class check (never from integrity).
        X86SourceOp::Sextend { .. }
        | X86SourceOp::Uextend { .. }
        | X86SourceOp::EffectiveAddress { .. }
        | X86SourceOp::CopyGpr
        | X86SourceOp::CopyXmm
        | X86SourceOp::MemLoad { .. }
        | X86SourceOp::MemStore { .. }
        // Whole-XMM 128-bit spill/reload moves are data-movement GLUE any source
        // may legitimately emit (like the scalar load/store family) — exempt from
        // the class-consistency check, never from attribution integrity.
        | X86SourceOp::V128MemLoad { .. }
        | X86SourceOp::V128MemStore { .. } => None,
        X86SourceOp::FpBinary(_)
        | X86SourceOp::FpSqrt
        | X86SourceOp::FpMinMax { .. }
        | X86SourceOp::Round => Some(OpClass::FpArith),
        X86SourceOp::FpCmpUnord => Some(OpClass::FpCmp),
        X86SourceOp::FpFormatConvert { .. }
        | X86SourceOp::FpToSint { .. }
        | X86SourceOp::SintToFp { .. } => Some(OpClass::FpConvert),
        X86SourceOp::Popcnt
        | X86SourceOp::Tzcnt
        | X86SourceOp::Lzcnt
        | X86SourceOp::Bsf
        | X86SourceOp::Bsr => Some(OpClass::BitCount),
        X86SourceOp::ImulImm => Some(OpClass::IntMul),
        X86SourceOp::PackedIntBinary { .. }
        | X86SourceOp::PackedIntCmp { .. }
        | X86SourceOp::PsadbwByteSad => Some(OpClass::VecInt),
        X86SourceOp::PackedV128Bitwise(_) => Some(OpClass::VecBitwise),
        X86SourceOp::PackedFpBinary { .. } => Some(OpClass::VecFp),
        X86SourceOp::InPlaceIncDec { is_inc } => Some(if *is_inc {
            OpClass::IntAdd
        } else {
            OpClass::IntSub
        }),
        X86SourceOp::Division { .. } => Some(OpClass::IntDiv),
        X86SourceOp::CondMove => Some(OpClass::Select),
    }
}

/// Width in bits of a register-bearing [`X86ISelOperand`]. Returns `None` for a
/// non-register operand (immediate/symbol/memory/etc. — the caller treats an
/// immediate slot separately, and anything else fails the reconstruction closed).
fn x86_operand_reg_width_bits(op: &X86ISelOperand) -> Option<u32> {
    match op {
        X86ISelOperand::VReg(v) => Some(v.class.size_bits()),
        X86ISelOperand::PReg(p) => {
            if p.is_gpr64() {
                Some(64)
            } else if p.is_gpr32() {
                Some(32)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Map a width in bits to an [`X86OperandSize`] (informational; width is carried
/// by the [`SmtExpr`] sorts, exactly as the encoders read `_size`). Treats
/// anything other than 32 as 64-domain for labeling.
fn x86_width_to_operand_size(width: u32) -> X86OperandSize {
    match width {
        32 => X86OperandSize::S32,
        _ => X86OperandSize::S64,
    }
}

/// Scalar FP WIDTH (32 for SS / single, 64 for SD / double) of an XMM operand,
/// taken from the [`RegClass`] of the ISel-level VReg. Returns `None` for a
/// non-FP / non-VReg operand (a post-regalloc XMM `PReg` is 128-bit and does NOT
/// carry the scalar-lane width, so it fails closed — the ISel-level
/// reconstruction operates on VRegs whose class is `Fpr32`/`Fpr64`).
fn x86_fp_scalar_width(op: &X86ISelOperand) -> Option<u32> {
    match op {
        X86ISelOperand::VReg(v) => match v.class {
            RegClass::Fpr32 => Some(32),
            RegClass::Fpr64 => Some(64),
            _ => None,
        },
        _ => None,
    }
}

/// `(eb, sb)` IEEE-754 exponent/significand pair for a scalar FP width.
fn x86_fp_format(width: u32) -> Option<(u32, u32)> {
    match width {
        32 => Some((8, 24)),
        64 => Some((11, 53)),
        _ => None,
    }
}

/// The [`X86FPSize`] for a scalar FP width.
fn x86_fp_size(width: u32) -> Option<crate::x86_64_semantics::X86FPSize> {
    use crate::x86_64_semantics::X86FPSize;
    match width {
        32 => Some(X86FPSize::Single),
        64 => Some(X86FPSize::Double),
        _ => None,
    }
}

/// Map a width in bits to a trust_ir [`Type`]. The trust_ir ALU/bitwise/shift
/// encoders carry width in the operand `SmtExpr` sorts and ignore the `Type`
/// parameter (it is `_ty`), so this is a faithful descriptor. `None` for an
/// unsupported width (fails the reconstruction closed).
fn x86_width_to_type(width: u32) -> Option<trust_cg_lower::types::Type> {
    use trust_cg_lower::types::Type;
    match width {
        8 => Some(Type::I8),
        16 => Some(Type::I16),
        32 => Some(Type::I32),
        64 => Some(Type::I64),
        _ => None,
    }
}

/// Reconstruct a lowering [`ProofObligation`] for a reconstructable x86-64
/// instruction directly FROM THE REAL EMITTED INSTRUCTION (task #66). Mirrors
/// `function_verifier::reconstruct_alu_obligation` /
/// `riscv_function_verifier::reconstruct_alu_obligation`.
///
/// Returns `None` (caller falls back to the existing path) for any
/// non-reconstructable opcode or any instruction whose operand shape does not
/// match the typed per-opcode schema (fail-closed: a malformed instruction is NOT
/// silently credited).
///
/// # What it does
///
/// 1. Resolves the INTENDED source op + arity via the TYPED exhaustive
///    [`x86_opcode_to_source_op`] (no string lookup).
/// 2. Reads `inst.operands` POSITIONALLY using the typed schema. Binary:
///    `[dst, src1, src2]` (RR) / `[dst, src1, imm]` (RI) / `[dst, src1]` (RR
///    shift, count in implicit CL). Unary: `[dst, src]`. Each register source
///    binds to a fresh symbolic var at the operand width; an immediate slot binds
///    to a `bv_const`; the implicit shift count binds to a fresh symbol.
/// 3. Builds `trust_ir_expr` from the INTENDED source op over the shared syms and
///    the machine side from the REAL opcode's x86 encoder, wired EXACTLY as
///    emitted (`src1` first, `src2`/imm/count second).
/// 4. Tags the obligation [`MachineSideProvenance::Reconstructed`].
///
/// SHIFTS additionally carry a LOAD-BEARING `count < width` precondition (#57):
/// the machine side is the FAITHFUL hardware-count-masked encoder
/// (`encode_shl_rr_masked` etc.) and the source side is the plain-`bvshl`
/// trust_ir encoder. In range the mask is the identity so they agree; out of
/// range the masked machine side and the clamp-to-0 source side DIVERGE, so the
/// precondition is genuinely required (strip it and a shift by `width` refutes).
/// x86 shifts >= width are themselves count-masked/UB, so scoping them out is
/// faithful. EXTENDS are width-CHANGING: the source occupies the low `from_bits`
/// of its register and both sides extend that `from_bits`-wide symbol to the dst
/// width; a MOVZX-for-Sextend (or vice versa) refutes for a negative source.
pub fn reconstruct_alu_obligation(inst: &X86ISelInst) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{
        encode_trust_ir_binop, encode_trust_ir_bitwise_binop, encode_trust_ir_bnot,
        encode_trust_ir_neg, encode_trust_ir_shift,
    };
    use crate::x86_64_semantics::{
        encode_add_rr, encode_and_rr, encode_imul_rr, encode_neg, encode_not, encode_or_rr,
        encode_sar_rr_masked, encode_shl_rr_masked, encode_shr_rr_masked, encode_sub_rr,
        encode_xor_rr,
    };

    let (source_op, arity) = x86_opcode_to_source_op(inst.opcode)?;

    // Destination is always operand slot 0 and fixes the operation width.
    let dst = inst.operands.first()?;
    let from_opcode = format!("{:?}", inst.opcode);

    // Extends are width-CHANGING and handled separately (the dst width is the
    // to_bits, the source occupies the low from_bits of its register). The
    // FP-scalar and bit-manip families have their OWN operand schemas (XMM FP-typed
    // leaves; the BV bit-count leaves; the cross int/fp conversions), dispatched to
    // dedicated builders BEFORE the generic same-width integer GPR logic below.
    match &source_op {
        X86SourceOp::Sextend { from_bits } => {
            return reconstruct_x86_extend(inst, *from_bits, true, from_opcode, arity);
        }
        X86SourceOp::Uextend { from_bits } => {
            return reconstruct_x86_extend(inst, *from_bits, false, from_opcode, arity);
        }
        X86SourceOp::FpBinary(op) => {
            return reconstruct_x86_fp_binary(inst, op, from_opcode);
        }
        X86SourceOp::FpSqrt => {
            return reconstruct_x86_fp_sqrt(inst, from_opcode);
        }
        X86SourceOp::FpMinMax { is_min } => {
            return reconstruct_x86_fp_minmax(inst, *is_min, from_opcode);
        }
        X86SourceOp::FpCmpUnord => {
            return reconstruct_x86_fp_cmp_unord(inst, from_opcode);
        }
        X86SourceOp::FpFormatConvert { to_bits } => {
            return reconstruct_x86_fp_format_convert(inst, *to_bits, from_opcode);
        }
        X86SourceOp::FpToSint { truncating } => {
            return reconstruct_x86_fp_to_sint(inst, *truncating, from_opcode);
        }
        X86SourceOp::SintToFp { to_bits } => {
            return reconstruct_x86_sint_to_fp(inst, *to_bits, from_opcode);
        }
        X86SourceOp::Popcnt
        | X86SourceOp::Tzcnt
        | X86SourceOp::Lzcnt
        | X86SourceOp::Bsf
        | X86SourceOp::Bsr => {
            return reconstruct_x86_bit_count(inst, &source_op, from_opcode);
        }
        X86SourceOp::EffectiveAddress { has_index } => {
            // LEA reads an ADDRESS-MODE operand (MemAddr / SibMemAddr), not the
            // [dst, src1, src2] register schema, so it is handled before the
            // Unary/Binary dispatch.
            return reconstruct_x86_lea(inst, *has_index, from_opcode);
        }
        X86SourceOp::CopyGpr => {
            return reconstruct_x86_copy_gpr(inst, from_opcode);
        }
        X86SourceOp::CopyXmm => {
            return reconstruct_x86_copy_xmm(inst, from_opcode);
        }
        X86SourceOp::ImulImm => {
            return reconstruct_x86_imul_imm(inst, from_opcode);
        }
        X86SourceOp::Round => {
            return reconstruct_x86_round(inst, from_opcode);
        }
        X86SourceOp::PackedIntBinary { op, arrangement } => {
            return reconstruct_x86_packed_int_binary(inst, op, *arrangement, from_opcode);
        }
        X86SourceOp::PackedIntCmp { cond, arrangement } => {
            return reconstruct_x86_packed_int_cmp(inst, cond, *arrangement, from_opcode);
        }
        X86SourceOp::PackedV128Bitwise(op) => {
            return reconstruct_x86_packed_v128_bitwise(inst, op, from_opcode);
        }
        X86SourceOp::PsadbwByteSad => {
            return reconstruct_x86_psadbw(inst, from_opcode);
        }
        X86SourceOp::PackedFpBinary { op, lane_bits } => {
            return reconstruct_x86_packed_fp_binary(inst, op, *lane_bits, from_opcode);
        }
        X86SourceOp::MemLoad { load_bits } => {
            // An ATOMIC-origin MOV (volatile/atomic load) keeps its stronger
            // AtomicLoad proof (which models the x86-TSO ordering), NOT a plain
            // value-load reconstruction. Fail closed here so the verifier falls
            // through to `proof_origin_to_proof_query`. The gate sees only the
            // opcode (no origin) and credits the plain-load reconstruction.
            if inst.proof_origin.is_some() {
                return None;
            }
            return reconstruct_x86_mem_load(inst, *load_bits, from_opcode);
        }
        X86SourceOp::MemStore { store_bits } => {
            if inst.proof_origin.is_some() {
                return None;
            }
            return reconstruct_x86_mem_store(inst, *store_bits, from_opcode);
        }
        X86SourceOp::V128MemLoad { aligned } => {
            // A proof-origin move (e.g. a hypothetical atomic 128-bit access) keeps
            // its stronger origin proof; fail closed here so the verifier routes to
            // `proof_origin_to_proof_query`. Plain spill/reload moves reconstruct.
            if inst.proof_origin.is_some() {
                return None;
            }
            return reconstruct_x86_v128_mem_load(inst, *aligned, from_opcode);
        }
        X86SourceOp::V128MemStore { aligned } => {
            if inst.proof_origin.is_some() {
                return None;
            }
            return reconstruct_x86_v128_mem_store(inst, *aligned, from_opcode);
        }
        X86SourceOp::MemAlu { op } => {
            return reconstruct_x86_mem_alu(inst, op, from_opcode);
        }
        X86SourceOp::InPlaceIncDec { is_inc } => {
            return reconstruct_x86_inc_dec(inst, *is_inc, from_opcode);
        }
        X86SourceOp::Division { signed } => {
            return reconstruct_x86_division(inst, *signed, from_opcode);
        }
        X86SourceOp::CondMove => {
            return reconstruct_x86_cond_move(inst, from_opcode);
        }
        _ => {}
    }

    let dst_width = x86_operand_reg_width_bits(dst)?;
    let size = x86_width_to_operand_size(dst_width);
    let ty = x86_width_to_type(dst_width)?;

    match arity {
        X86AluArity::Unary => {
            // Typed positional schema: [dst, src]. (Neg/Not.)
            if inst.operands.len() != 2 {
                return None;
            }
            let src = &inst.operands[1];
            if x86_operand_reg_width_bits(src)? != dst_width {
                return None;
            }
            let sym = SmtExpr::var("recon_src", dst_width);
            let (trust_ir_expr, machine_expr, label): (SmtExpr, SmtExpr, &str) = match &source_op {
                X86SourceOp::Neg => (
                    encode_trust_ir_neg(ty, sym.clone()),
                    encode_neg(size, sym.clone()),
                    "Ineg",
                ),
                X86SourceOp::Not => (
                    encode_trust_ir_bnot(ty, sym.clone()),
                    encode_not(size, sym.clone()),
                    "Bnot",
                ),
                // Binary/extend families never reach the unary arm here.
                _ => return None,
            };
            Some(ProofObligation {
                name: format!(
                    "RECONSTRUCTED x86_64 {}_{} -> {:?} (real-operand)",
                    label, dst_width, inst.opcode
                ),
                trust_ir_expr,
                aarch64_expr: machine_expr,
                inputs: vec![("recon_src".to_string(), dst_width)],
                preconditions: vec![],
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
                machine_side_provenance: MachineSideProvenance::Reconstructed {
                    from_opcode,
                    arity: arity.as_u8(),
                },
            })
        }
        X86AluArity::Binary => {
            // The RR shift form is `[dst, src1]` (count in implicit CL); every
            // other binary form is `[dst, src1, src2|imm]`.
            let is_rr_shift = matches!(
                inst.opcode,
                X86Opcode::ShlRR | X86Opcode::ShrRR | X86Opcode::SarRR
            );
            if is_rr_shift {
                if inst.operands.len() != 2 {
                    return None;
                }
            } else if inst.operands.len() != 3 {
                return None;
            }

            // src1 must be a register at the destination width; bind to a fresh sym.
            let src1 = &inst.operands[1];
            if x86_operand_reg_width_bits(src1)? != dst_width {
                return None;
            }
            let sym1 = SmtExpr::var("recon_src1", dst_width);

            // src2: register (RR), immediate (RI), or implicit CL (RR shift).
            let (sym2, src2_is_declared_input): (SmtExpr, bool) = if is_rr_shift {
                // Implicit CL count: a fresh symbol (the runtime shift amount).
                (SmtExpr::var("recon_src2", dst_width), true)
            } else {
                match &inst.operands[2] {
                    X86ISelOperand::Imm(imm) => {
                        let raw = (*imm as i128) as u128;
                        let masked = (raw as u64) & crate::smt::mask(u64::MAX, dst_width);
                        (SmtExpr::bv_const(masked, dst_width), false)
                    }
                    reg => {
                        if x86_operand_reg_width_bits(reg)? != dst_width {
                            return None;
                        }
                        (SmtExpr::var("recon_src2", dst_width), true)
                    }
                }
            };

            // SOURCE side: the INTENDED trust_ir op over shared syms. Shifts add a
            // LOAD-BEARING count<width precondition (#57).
            let mut preconditions: Vec<SmtExpr> = vec![];
            let (trust_ir_expr, source_label): (SmtExpr, String) = match &source_op {
                X86SourceOp::Binary(op) => (
                    encode_trust_ir_binop(op, ty, sym1.clone(), sym2.clone()),
                    format!("{op:?}"),
                ),
                X86SourceOp::Bitwise(op) => (
                    encode_trust_ir_bitwise_binop(op, ty, sym1.clone(), sym2.clone()),
                    format!("{op:?}"),
                ),
                X86SourceOp::Shift(op) => {
                    // LOAD-BEARING precondition (#57): count (src2/CL/imm) < width.
                    // In range the hardware mask is the identity; out of range the
                    // faithful masked machine side diverges from the clamp-to-0
                    // trust_ir side, so this precondition is genuinely required for
                    // the obligation to discharge Valid. x86 shifts >= width are
                    // count-masked/UB.
                    preconditions.push(
                        sym2.clone()
                            .bvult(SmtExpr::bv_const(dst_width as u64, dst_width)),
                    );
                    (
                        encode_trust_ir_shift(op, ty, sym1.clone(), sym2.clone()),
                        format!("{op:?}"),
                    )
                }
                // Unary/extend families never reach the binary arm.
                _ => return None,
            };

            // MACHINE side: the REAL opcode's x86 encoder, wired EXACTLY as emitted
            // (src1 first, src2/imm/count second). For a non-commutative op
            // (Sub/shifts) a swap of the source slots changes the result => refutes.
            // Shifts use the FAITHFUL count-masked encoder.
            let machine_expr = match inst.opcode {
                X86Opcode::AddRR | X86Opcode::AddRI => {
                    encode_add_rr(size, sym1.clone(), sym2.clone())
                }
                X86Opcode::SubRR | X86Opcode::SubRI => {
                    encode_sub_rr(size, sym1.clone(), sym2.clone())
                }
                X86Opcode::ImulRR => encode_imul_rr(size, sym1.clone(), sym2.clone()),
                X86Opcode::AndRR | X86Opcode::AndRI => {
                    encode_and_rr(size, sym1.clone(), sym2.clone())
                }
                X86Opcode::OrRR | X86Opcode::OrRI => encode_or_rr(size, sym1.clone(), sym2.clone()),
                X86Opcode::XorRR | X86Opcode::XorRI => {
                    encode_xor_rr(size, sym1.clone(), sym2.clone())
                }
                X86Opcode::ShlRR | X86Opcode::ShlRI => {
                    encode_shl_rr_masked(size, sym1.clone(), sym2.clone())
                }
                X86Opcode::ShrRR | X86Opcode::ShrRI => {
                    encode_shr_rr_masked(size, sym1.clone(), sym2.clone())
                }
                X86Opcode::SarRR | X86Opcode::SarRI => {
                    encode_sar_rr_masked(size, sym1.clone(), sym2.clone())
                }
                // Unreachable: x86_opcode_to_source_op only returned Binary for the
                // arms above. Fail closed rather than panic.
                _ => return None,
            };

            // Only register/CL sources become declared SMT inputs; an immediate is
            // a constant and is NOT declared.
            let mut inputs = vec![("recon_src1".to_string(), dst_width)];
            if src2_is_declared_input {
                inputs.push(("recon_src2".to_string(), dst_width));
            }

            Some(ProofObligation {
                name: format!(
                    "RECONSTRUCTED x86_64 {}_{} -> {:?} (real-operand)",
                    source_label, dst_width, inst.opcode
                ),
                trust_ir_expr,
                aarch64_expr: machine_expr,
                inputs,
                preconditions,
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
                machine_side_provenance: MachineSideProvenance::Reconstructed {
                    from_opcode,
                    arity: arity.as_u8(),
                },
            })
        }
    }
}

/// The immediate-baked binary/shift RI opcodes whose whole WIDTH family PROOF-5
/// covers with a single PARAMETRIC (free-immediate) rule. Their RR siblings
/// share the SAME machine encoder (`AddRI`/`AddRR` → `encode_add_rr`, etc.), so
/// the free-immediate obligation is byte-identical to the RR-form reconstruction
/// — one committed tier-0 row credits the RR instance AND every RI immediate.
const fn is_parametric_imm_binary_opcode(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::AddRI
            | X86Opcode::SubRI
            | X86Opcode::AndRI
            | X86Opcode::OrRI
            | X86Opcode::XorRI
            | X86Opcode::ShlRI
            | X86Opcode::ShrRI
            | X86Opcode::SarRI
    )
}

/// PROOF-5: the CANONICAL (parametric) reconstruction obligation used for the
/// tier-0 verdict lookup. For the immediate-baked binary/shift RI families the
/// baked immediate is FREED to a fresh same-width register so the reconstruction
/// binds it to a symbolic variable — the negated equivalence then holds for ALL
/// immediates (forall-imm; still QF_BV, no quantifier), and the shift
/// `count < width` precondition rides symbolically over that free variable. For
/// every immediate-free family the instance obligation is already stable per
/// (family, width), so its reconstruction IS its canonical form.
///
/// Drift-free by construction: goes through the SAME
/// [`reconstruct_alu_obligation`] as an RR instance, so the per-compile lookup
/// reproduces exactly what the offline regen recorded.
pub(crate) fn canonical_reconstruct_obligation(inst: &X86ISelInst) -> Option<ProofObligation> {
    // ImulRRI (3-operand `IMUL r,r,imm`): unlike the Add/Sub/shift RI families
    // (whose RI and RR forms share ONE encoder + one reconstruct arm so freeing
    // the immediate in place suffices), the ImulRRI instance is built by
    // `reconstruct_x86_imul_imm` which DEMANDS an `Imm` operand. So we must both
    // free the immediate AND retarget the opcode to `ImulRR`, synthesizing a
    // reg*reg multiply. Because `encode_imul_rri` now reduces to
    // `encode_imul_rr(size, src, bv_const(imm))` (ONE multiply encoder), the RRI
    // instance is a literal substitution instance of the reg*reg proof: the
    // synthesized ImulRR reconstruction is byte-identical SMT2 to the committed
    // `Imul_{32,64} -> ImulRR` tier-0 row — no new row, no regen. Any width/shape
    // it cannot synthesize falls back to the baked instance (a lookup miss ->
    // live discharge -> sound).
    if inst.opcode == X86Opcode::ImulRRI && inst.operands.len() == 3 {
        use trust_cg_ir::regs::VReg;
        let dst_width = x86_operand_reg_width_bits(inst.operands.first()?)?;
        let class = match dst_width {
            32 => RegClass::Gpr32,
            64 => RegClass::Gpr64,
            _ => return reconstruct_alu_obligation(inst),
        };
        // Low-half src*sext(imm) is a substitution instance of the reg*reg
        // ImulRR proof (both encoders reduce to bvmul); byte-identical SMT2 to
        // the committed `Imul_{32,64} -> ImulRR` row -> no new row, no regen.
        let rr = X86ISelInst::new(
            X86Opcode::ImulRR,
            vec![
                inst.operands[0].clone(),
                inst.operands[1].clone(),
                X86ISelOperand::VReg(VReg::new(u32::MAX, class)),
            ],
        );
        return reconstruct_alu_obligation(&rr).or_else(|| reconstruct_alu_obligation(inst));
    }
    if is_parametric_imm_binary_opcode(inst.opcode) && inst.operands.len() == 3 {
        use trust_cg_ir::regs::VReg;
        let dst_width = x86_operand_reg_width_bits(inst.operands.first()?)?;
        let class = match dst_width {
            32 => RegClass::Gpr32,
            64 => RegClass::Gpr64,
            // Only 32/64-bit GPR reconstructions exist (there is no Gpr16 class),
            // so leave any other width on its instance form.
            _ => return reconstruct_alu_obligation(inst),
        };
        let mut synth = inst.clone();
        synth.operands[2] = X86ISelOperand::VReg(VReg::new(u32::MAX, class));
        // Fall back to the instance obligation if the freed form fails to
        // reconstruct (the lookup just misses — sound).
        return reconstruct_alu_obligation(&synth).or_else(|| reconstruct_alu_obligation(inst));
    }
    reconstruct_alu_obligation(inst)
}

/// PROOF-5: the finite set of x86 CANONICAL (parametric) reconstruction
/// obligations to prove offline into tier-0 — the hot integer ALU / bitwise /
/// shift / neg / not surface at BOTH emitted GPR widths (32 and 64). One
/// obligation per (family, width); the RI instances at compile time canonicalize
/// (via [`canonical_reconstruct_obligation`]) to the byte-identical RR-form
/// obligation, so a single row is the PARAMETRIC proof for the whole width
/// family. Other reconstructable families (LEA effective-address, FP, division,
/// packed, …) are left to the per-compile live-solver credit (division stays a
/// tracked statistical-fallback exemption — the same solver-hard class PROOF-4
/// exempts).
pub fn enumerate_reconstruct_tier0_obligations() -> Vec<ProofObligation> {
    use trust_cg_ir::regs::VReg;
    let mut out: Vec<ProofObligation> = Vec::new();
    let add = |inst: X86ISelInst, out: &mut Vec<ProofObligation>| {
        if let Some(ob) = reconstruct_alu_obligation(&inst)
            && !out.iter().any(|x| x == &ob)
        {
            out.push(ob);
        }
    };
    for &class in &[RegClass::Gpr32, RegClass::Gpr64] {
        let r = |id: u32| X86ISelOperand::VReg(VReg::new(id, class));
        // Binary register ALU: [dst, src1, src2] — both sources free.
        for op in [
            X86Opcode::AddRR,
            X86Opcode::SubRR,
            X86Opcode::ImulRR,
            X86Opcode::AndRR,
            X86Opcode::OrRR,
            X86Opcode::XorRR,
        ] {
            add(X86ISelInst::new(op, vec![r(0), r(1), r(2)]), &mut out);
        }
        // Shifts RR: [dst, src1] — count in implicit CL (free), count<width precond.
        for op in [X86Opcode::ShlRR, X86Opcode::ShrRR, X86Opcode::SarRR] {
            add(X86ISelInst::new(op, vec![r(0), r(1)]), &mut out);
        }
        // Unary Neg/Not: [dst, src].
        for op in [X86Opcode::Neg, X86Opcode::Not] {
            add(X86ISelInst::new(op, vec![r(0), r(1)]), &mut out);
        }
    }
    // Width-CHANGING / width-fixed immediate-free families (one representative
    // each — the width is fixed by the opcode): sign/zero extends + register
    // copies. Their obligations are stable per opcode, so a representative row
    // credits every instance.
    for op in [
        X86Opcode::Movzx,
        X86Opcode::MovzxW,
        X86Opcode::MovsxB,
        X86Opcode::MovsxW,
        X86Opcode::Movsx,
        X86Opcode::MovRR,
        X86Opcode::MovRR32,
    ] {
        if let Some(inst) = representative_reconstructable_inst(op) {
            add(inst, &mut out);
        }
    }
    out
}

/// Reconstruct a genuine effective-address obligation for `Lea`/`LeaSib` from the
/// REAL emitted addressing-mode operand. SOURCE = the trust_ir integer
/// composition `base + index*scale + disp` (built from `encode_trust_ir_binop`
/// `Iadd`/`Imul`); MACHINE = the INDEPENDENT x86 `encode_lea_*` encoder. Two
/// independently-implemented encoders (trust_ir vs x86) over the SAME real
/// operands ⇒ a buggy effective-address encoder refutes (exactly as `AddRR`'s
/// reconstruction refutes a wrong add encoder); the `Reconstructed` provenance is
/// what credits it as genuine (NOT the degenerate X==X LEA proofs retracted in
/// #62). Returns `None` (fall through to fail-closed) for any non-register
/// base/index, a width mismatch, or a non-LEA addressing operand — never a
/// vacuous pass.
fn reconstruct_x86_lea(
    inst: &X86ISelInst,
    has_index: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{encode_lea_base_disp, encode_lea_base_index_scale_disp};
    use trust_cg_lower::instructions::Opcode;

    let dst = inst.operands.first()?;
    let dst_width = x86_operand_reg_width_bits(dst)?;
    let ty = x86_width_to_type(dst_width)?;
    let addr = inst.operands.get(1)?;

    // A LEA base/index is an ADDRESS VALUE bound to one symbolic var: the
    // obligation (`addr_value [+ index*scale] + disp == encode_lea(...)`) is the
    // same whatever the base IS, so the base KIND only gates which shapes we
    // admit. A register base/index must match the address (dst) width; a
    // StackSlot is a frame-relative pointer (64-bit, the common `lea r64,[slot]`
    // for &local). Any OTHER base kind (symbol/RIP/nested) fails closed — never a
    // vacuous pass; those LEAs stay on their relocation/DB path.
    fn lea_addr_operand_ok(op: &X86ISelOperand, addr_width: u32) -> bool {
        match op {
            X86ISelOperand::VReg(_) | X86ISelOperand::PReg(_) => {
                x86_operand_reg_width_bits(op) == Some(addr_width)
            }
            X86ISelOperand::StackSlot(_) => addr_width == 64,
            _ => false,
        }
    }

    if has_index {
        // SIB LEA: `[dst, SibMemAddr { base, index, scale, disp }]`.
        let X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } = addr
        else {
            return None;
        };
        if !lea_addr_operand_ok(base, dst_width) || !lea_addr_operand_ok(index, dst_width) {
            return None;
        }
        let sym_base = SmtExpr::var("recon_base", dst_width);
        let sym_index = SmtExpr::var("recon_index", dst_width);
        let scale_const = SmtExpr::bv_const(*scale as u64, dst_width);
        // i32 displacement is sign-extended to the address width (mirrors the
        // `encode_lea_*` `disp as u64` over the same width).
        let disp_const = SmtExpr::bv_const((*disp as i64) as u64, dst_width);
        // SOURCE: base + index*scale + disp via trust_ir Iadd/Imul.
        let scaled =
            encode_trust_ir_binop(&Opcode::Imul, ty.clone(), sym_index.clone(), scale_const);
        let base_plus = encode_trust_ir_binop(&Opcode::Iadd, ty.clone(), sym_base.clone(), scaled);
        let trust_ir_expr = encode_trust_ir_binop(&Opcode::Iadd, ty, base_plus, disp_const);
        // MACHINE: the independent x86 effective-address encoder.
        let machine_expr =
            encode_lea_base_index_scale_disp(sym_base, sym_index, *scale as u32, *disp as i64);
        Some(ProofObligation {
            name: format!(
                "RECONSTRUCTED x86_64 EffectiveAddress_{} -> {:?} (base+index*scale+disp, real-operand)",
                dst_width, inst.opcode
            ),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: vec![
                ("recon_base".to_string(), dst_width),
                ("recon_index".to_string(), dst_width),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode,
                arity: 2,
            },
        })
    } else {
        // Plain LEA: `[dst, MemAddr { base, disp }]`.
        let X86ISelOperand::MemAddr { base, disp } = addr else {
            return None;
        };
        if !lea_addr_operand_ok(base, dst_width) {
            return None;
        }
        let sym_base = SmtExpr::var("recon_base", dst_width);
        let disp_const = SmtExpr::bv_const((*disp as i64) as u64, dst_width);
        // SOURCE: base + disp via trust_ir Iadd.
        let trust_ir_expr = encode_trust_ir_binop(&Opcode::Iadd, ty, sym_base.clone(), disp_const);
        // MACHINE: the independent x86 effective-address encoder.
        let machine_expr = encode_lea_base_disp(sym_base, *disp as i64, dst_width);
        Some(ProofObligation {
            name: format!(
                "RECONSTRUCTED x86_64 EffectiveAddress_{} -> {:?} (base+disp, real-operand)",
                dst_width, inst.opcode
            ),
            trust_ir_expr,
            aarch64_expr: machine_expr,
            inputs: vec![("recon_base".to_string(), dst_width)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode,
                arity: 1,
            },
        })
    }
}

// ===========================================================================
// MEMORY load/store + memory-ALU + in-place Inc/Dec reconstruction (task #76).
//
// The memory families reconstruct the GENUINE effective address from the REAL
// emitted addressing operand using the SAME two independent encoders LEA uses:
//   * SOURCE EA  = trust_ir integer composition `base [+ index*scale] + disp`
//                  (`encode_trust_ir_binop` Iadd/Imul) — the trust_ir module.
//   * MACHINE EA = the x86 `encode_lea_*` effective-address encoder — the x86
//                  module. A buggy address-mode lowering (wrong scale/disp/
//                  base/index) builds a DIFFERENT machine EA.
// The deterministic [`SmtExpr::MemLoad`] memory model turns an EA difference into
// a loaded-VALUE difference (`load(ea) deterministic fn of ea`), so a wrong EA
// REFUTES; `load_bits`/signedness participate in the value, so a wrong access
// width / sign REFUTES. This is strictly STRONGER than the AArch64/RISC-V
// load/store disposition (those are allowlisted-OUT as "covered by the memory
// family, not a per-instruction value proof"): here we VERIFY the real addressing
// arithmetic per instruction, exactly the faithful independent EA encoder the
// degenerate X==X memory proofs (#62) were retracted pending.
// ===========================================================================

/// Width in bits of the effective ADDRESS for an x86 memory operand. x86-64
/// addresses are 64-bit; the base/index registers are 64-bit GPRs (or a 64-bit
/// frame-relative stack slot). Returns `None` for an addressing shape we do not
/// model (symbol/RIP/nested/const-pool) — fail closed, no vacuous pass.
const X86_ADDR_WIDTH: u32 = 64;

/// A register base/index must be a 64-bit GPR; a `StackSlot` is a 64-bit
/// frame-relative pointer. Mirrors `reconstruct_x86_lea::lea_addr_operand_ok`.
fn mem_addr_base_ok(op: &X86ISelOperand) -> bool {
    match op {
        X86ISelOperand::VReg(_) | X86ISelOperand::PReg(_) => {
            x86_operand_reg_width_bits(op) == Some(X86_ADDR_WIDTH)
        }
        X86ISelOperand::StackSlot(_) => true,
        _ => false,
    }
}

/// Build the `(ir_ea, machine_ea, addr_inputs)` triple for an x86 addressing
/// operand (`MemAddr` plain `[base+disp]` or `SibMemAddr` `[base+index*scale+disp]`).
///
/// * `ir_ea`      = trust_ir composition via `encode_trust_ir_binop` (Iadd/Imul).
/// * `machine_ea` = the INDEPENDENT x86 `encode_lea_*` encoder over the SAME
///   real `base`/`index`/`scale`/`disp` operands.
/// * `addr_inputs` = the fresh symbolic address-register leaves (declared SMT
///   inputs), at the 64-bit address width.
///
/// Returns `None` (fail closed) for any non-modeled base/index shape. The base
/// symbol is named `recon_base`, the index `recon_index`, so the load/store/ALU
/// builders share one address namespace.
type ReconstructedEffectiveAddress = (SmtExpr, SmtExpr, Vec<(String, u32)>);

fn x86_reconstruct_effective_address(
    addr: &X86ISelOperand,
) -> Option<ReconstructedEffectiveAddress> {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{encode_lea_base_disp, encode_lea_base_index_scale_disp};
    use trust_cg_lower::instructions::Opcode;

    let w = X86_ADDR_WIDTH;
    let ty = x86_width_to_type(w)?;
    match addr {
        X86ISelOperand::MemAddr { base, disp } => {
            if !mem_addr_base_ok(base) {
                return None;
            }
            let sym_base = SmtExpr::var("recon_base", w);
            let disp_const = SmtExpr::bv_const((*disp as i64) as u64, w);
            let ir_ea = encode_trust_ir_binop(&Opcode::Iadd, ty, sym_base.clone(), disp_const);
            let machine_ea = encode_lea_base_disp(sym_base, *disp as i64, w);
            Some((ir_ea, machine_ea, vec![("recon_base".to_string(), w)]))
        }
        X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } => {
            if !mem_addr_base_ok(base) || !mem_addr_base_ok(index) {
                return None;
            }
            let sym_base = SmtExpr::var("recon_base", w);
            let sym_index = SmtExpr::var("recon_index", w);
            let scale_const = SmtExpr::bv_const(*scale as u64, w);
            let disp_const = SmtExpr::bv_const((*disp as i64) as u64, w);
            let scaled =
                encode_trust_ir_binop(&Opcode::Imul, ty.clone(), sym_index.clone(), scale_const);
            let base_plus =
                encode_trust_ir_binop(&Opcode::Iadd, ty.clone(), sym_base.clone(), scaled);
            let ir_ea = encode_trust_ir_binop(&Opcode::Iadd, ty, base_plus, disp_const);
            let machine_ea =
                encode_lea_base_index_scale_disp(sym_base, sym_index, *scale as u32, *disp as i64);
            Some((
                ir_ea,
                machine_ea,
                vec![
                    ("recon_base".to_string(), w),
                    ("recon_index".to_string(), w),
                ],
            ))
        }
        _ => None,
    }
}

/// Reconstruct a memory LOAD (`MovRM8/16/32/(64)`, `MovssRM`/`MovsdRM`). Schema:
/// `[dst_reg, MemAddr/SibMemAddr]`. SOURCE = `MemLoad(ir_ea, load_bits, unsigned,
/// result_width)`; MACHINE = `MemLoad(machine_ea, load_bits, unsigned,
/// result_width)`. `result_width` is the dest register width. A wrong EA (built
/// by a buggy address-mode lowering) reads a different value ⇒ REFUTE; a wrong
/// `load_bits` (8-for-32) diverges in the value ⇒ REFUTE.
fn reconstruct_x86_mem_load(
    inst: &X86ISelInst,
    load_bits: u32,
    from_opcode: String,
) -> Option<ProofObligation> {
    if inst.operands.len() != 2 {
        return None;
    }
    // Dest register width: GPR (Gpr32/Gpr64) for integer loads, XMM scalar
    // (Fpr32/Fpr64) for FP loads. The dest holds the zero-filled access value.
    let dst = inst.operands.first()?;
    let result_width = x86_operand_reg_width_bits(dst).or_else(|| x86_fp_scalar_width(dst))?;
    if load_bits > result_width {
        return None;
    }
    let (ir_ea, machine_ea, inputs) = x86_reconstruct_effective_address(&inst.operands[1])?;

    // x86 plain MOV loads are zero-fill (no sign-extension): the trust_ir Load of
    // a sub-register value zero-extends into its register, so signed = false.
    let trust_ir_expr = SmtExpr::mem_load(ir_ea, load_bits, false, result_width);
    let machine_expr = SmtExpr::mem_load(machine_ea, load_bits, false, result_width);

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 Load_{load_bits}->{result_width} -> {:?} (real-EA, real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct a memory STORE (`MovMR8/16/32/(64)`, `MovssMR`/`MovsdMR`). Schema:
/// `[MemAddr/SibMemAddr, value_reg]`. The obligation equates
/// `concat(machine_ea, value)` with `concat(ir_ea, value)`: the ADDRESS half
/// REFUTES on a wrong EA, and the VALUE half ties the stored register to the IR
/// store value (a swapped/dropped value diverges). `store_bits` is the access
/// width fixed by the opcode; the value leaf is the (truncated) store width.
fn reconstruct_x86_mem_store(
    inst: &X86ISelInst,
    store_bits: u32,
    from_opcode: String,
) -> Option<ProofObligation> {
    if inst.operands.len() != 2 {
        return None;
    }
    let (ir_ea, machine_ea, mut inputs) = x86_reconstruct_effective_address(&inst.operands[0])?;

    // The stored value register: a GPR (integer) or XMM scalar (FP). Bind the low
    // `store_bits` of the value to a fresh leaf so a wrong store WIDTH would carry
    // a different value half. The value half is bit-identical on both sides (the
    // store writes exactly the register value), so this fixes the (ea, value)
    // PAIR — the address half is what the EA reconstruction refutes.
    let value = &inst.operands[1];
    let val_width = x86_operand_reg_width_bits(value).or_else(|| x86_fp_scalar_width(value))?;
    let leaf_bits = store_bits.min(val_width);
    let sym_value = SmtExpr::var("recon_value", leaf_bits);
    inputs.push(("recon_value".to_string(), leaf_bits));

    // SOURCE / MACHINE: concat(ea, value). EA differs => refute; value differs =>
    // refute. The EA halves are the two independent encoders (LEA vs trust_ir).
    let trust_ir_expr = ir_ea.concat(sym_value.clone());
    let machine_expr = machine_ea.concat(sym_value);

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 Store_{store_bits} -> {:?} (real-EA+value, real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    })
}

/// Width in bits of a whole-XMM 128-bit operand: an ISel-level `Fpr128` VReg or a
/// post-regalloc XMM `PReg` (either is 128 bits). Returns `None` (fail closed) for
/// any other operand — a non-128-bit destination/value on a packed move is a
/// malformed instruction and must NOT be silently credited. Kept LOCAL to the
/// packed-move reconstruction so the shared `x86_operand_reg_width_bits` (which
/// intentionally rejects XMM registers for the scalar families) is unchanged.
fn x86_v128_reg_width(op: &X86ISelOperand) -> Option<u32> {
    match op {
        X86ISelOperand::VReg(v) if v.class.size_bits() == 128 => Some(128),
        X86ISelOperand::PReg(p) if p.is_xmm() => Some(128),
        _ => None,
    }
}

/// The 16-byte-alignment precondition `ea % 16 == 0` on an effective address,
/// modeled as `(ea & 15) == 0`. Carried ONLY by the aligned MOVDQA forms (which
/// #GP-fault on a non-16-aligned address); MOVDQU carries no such precondition.
fn x86_ea_16byte_aligned(ea: SmtExpr) -> SmtExpr {
    ea.bvand(SmtExpr::bv_const(15, X86_ADDR_WIDTH))
        .eq_expr(SmtExpr::bv_const(0, X86_ADDR_WIDTH))
}

/// Reconstruct a whole-XMM 128-bit memory LOAD (`MovdquRM`/`MovdqaRM`:
/// `xmm128 <- [ea]`). Schema: `[dst_xmm128, MemAddr/SibMemAddr]`. The 128-bit
/// value is modeled as TWO 64-bit halves at `ea` (low) and `ea+8` (high),
/// LITTLE-ENDIAN — `value[63:0]` = the 8 bytes at `ea`, `value[127:64]` = the 8
/// bytes at `ea+8`:
///
/// * SOURCE  = `concat(load(ir_ea + 8, 64), load(ir_ea, 64))`,
/// * MACHINE = `concat(load(machine_ea + 8, 64), load(machine_ea, 64))`,
///
/// where `ir_ea` is the trust_ir EA composition and `machine_ea` the INDEPENDENT
/// x86 `encode_lea_*` EA over the SAME base/index/scale/disp. The deterministic
/// [`SmtExpr::MemLoad`] model makes a wrong EA (base/index/scale/disp), a SWAPPED
/// half, a wrong half OFFSET (`ea+16` for `ea+8`), or a wrong access WIDTH read
/// different bytes ⇒ REFUTE. For the aligned form (`aligned == true`, MOVDQA) the
/// honest `ea % 16 == 0` precondition is attached; it never weakens the value
/// equality (the two halves are read from the SAME independent-encoder addresses).
fn reconstruct_x86_v128_mem_load(
    inst: &X86ISelInst,
    aligned: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    if inst.operands.len() != 2 {
        return None;
    }
    // The destination must be a whole 128-bit XMM (Fpr128 VReg or XMM PReg).
    let dst = inst.operands.first()?;
    if x86_v128_reg_width(dst)? != 128 {
        return None;
    }
    let (ir_ea, machine_ea, inputs) = x86_reconstruct_effective_address(&inst.operands[1])?;

    let eight = SmtExpr::bv_const(8, X86_ADDR_WIDTH);
    let ir_ea_hi = ir_ea.clone().bvadd(eight.clone());
    let machine_ea_hi = machine_ea.clone().bvadd(eight);

    // Low half at ea, high half at ea+8; little-endian => high 64 bits are the
    // UPPER concat operand.
    let lo_src = SmtExpr::mem_load(ir_ea.clone(), 64, false, 64);
    let hi_src = SmtExpr::mem_load(ir_ea_hi, 64, false, 64);
    let lo_mac = SmtExpr::mem_load(machine_ea, 64, false, 64);
    let hi_mac = SmtExpr::mem_load(machine_ea_hi, 64, false, 64);
    let trust_ir_expr = hi_src.concat(lo_src);
    let machine_expr = hi_mac.concat(lo_mac);

    // MOVDQA carries the honest 16-byte-alignment precondition on ea; MOVDQU does
    // not. The precondition documents the well-defined domain of the aligned move
    // WITHOUT weakening the value equality.
    let preconditions = if aligned {
        vec![x86_ea_16byte_aligned(ir_ea)]
    } else {
        vec![]
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 V128Load128{} -> {:?} (two 64-bit halves at ea/ea+8, real-EA)",
            if aligned { " [aligned ea%16==0]" } else { "" },
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct a whole-XMM 128-bit memory STORE (`MovdquMR`/`MovdqaMR`:
/// `[ea] <- xmm128`). Schema: `[MemAddr/SibMemAddr, value_xmm128]`. Modeled as TWO
/// 64-bit half stores: `value[63:0]` to `[ea]` and `value[127:64]` to `[ea+8]`
/// (little-endian). Each half's OBSERVABLE folds the stored value half with the
/// deterministic address hash `load(slot_ea)` of its target slot, folded
/// PER-64-BIT (`half_val bvadd load(slot_ea)`, so no carry crosses the half
/// boundary):
///
/// * SOURCE  = `concat(hi_val + load(ir_ea + 8),  lo_val + load(ir_ea))`,
/// * MACHINE = `concat(hi_val + load(machine_ea + 8), lo_val + load(machine_ea))`.
///
/// A wrong EA loads a different address hash ⇒ REFUTE; a SWAPPED half puts the
/// wrong value half at a slot ⇒ REFUTE (`lo_val`/`hi_val` are independent fresh
/// leaves); a dropped/wrong value half diverges ⇒ REFUTE. The two value halves are
/// bound as SEPARATE 64-bit leaves (`recon_value_lo`/`recon_value_hi`) so the
/// obligation has 3+ inputs and routes to the per-input-width multi-sampler
/// (avoiding the single-width masking of a mixed-width 2-input obligation). The
/// aligned form carries the `ea % 16 == 0` precondition.
fn reconstruct_x86_v128_mem_store(
    inst: &X86ISelInst,
    aligned: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    if inst.operands.len() != 2 {
        return None;
    }
    // The stored value must be a whole 128-bit XMM (Fpr128 VReg or XMM PReg).
    let value = &inst.operands[1];
    if x86_v128_reg_width(value)? != 128 {
        return None;
    }
    let (ir_ea, machine_ea, mut inputs) = x86_reconstruct_effective_address(&inst.operands[0])?;

    // Two independent 64-bit value-half leaves (low = bytes at ea, high = bytes at
    // ea+8). Bound as inputs so a swapped/dropped/wrong half refutes.
    let lo_val = SmtExpr::var("recon_value_lo", 64);
    let hi_val = SmtExpr::var("recon_value_hi", 64);
    inputs.push(("recon_value_lo".to_string(), 64));
    inputs.push(("recon_value_hi".to_string(), 64));

    let eight = SmtExpr::bv_const(8, X86_ADDR_WIDTH);
    let ir_ea_hi = ir_ea.clone().bvadd(eight.clone());
    let machine_ea_hi = machine_ea.clone().bvadd(eight);

    // Per-slot observable = value_half + load(slot_ea): binds BOTH the value half
    // and its target address (load(ea) is a deterministic bijection of ea) into a
    // single 64-bit quantity, folded per-half so no carry crosses the boundary.
    let lo_obs_src = lo_val
        .clone()
        .bvadd(SmtExpr::mem_load(ir_ea.clone(), 64, false, 64));
    let hi_obs_src = hi_val
        .clone()
        .bvadd(SmtExpr::mem_load(ir_ea_hi, 64, false, 64));
    let lo_obs_mac = lo_val.bvadd(SmtExpr::mem_load(machine_ea, 64, false, 64));
    let hi_obs_mac = hi_val.bvadd(SmtExpr::mem_load(machine_ea_hi, 64, false, 64));
    let trust_ir_expr = hi_obs_src.concat(lo_obs_src);
    let machine_expr = hi_obs_mac.concat(lo_obs_mac);

    let preconditions = if aligned {
        vec![x86_ea_16byte_aligned(ir_ea)]
    } else {
        vec![]
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 V128Store128{} -> {:?} (two 64-bit halves at ea/ea+8, real-EA+value)",
            if aligned { " [aligned ea%16==0]" } else { "" },
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    })
}

/// Reconstruct a memory-source ALU op (`AddRM`/`SubRM`/`CmpRM`): `dst = reg OP
/// load(ea)`. Schema: `[reg, MemAddr/SibMemAddr]`. SOURCE =
/// `trust_ir(reg OP MemLoad(ir_ea))`; MACHINE = `x86(reg OP MemLoad(machine_ea))`
/// via the REAL ALU encoder and the independent EA encoder. A wrong ALU opcode
/// (Add-for-Sub) REFUTES (different arithmetic); a wrong EA REFUTES (different
/// loaded operand). The full ALU width is the register width.
fn reconstruct_x86_mem_alu(
    inst: &X86ISelInst,
    op: &trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{encode_add_rr, encode_imul_rr, encode_sub_rr};

    if inst.operands.len() != 2 {
        return None;
    }
    let reg = inst.operands.first()?;
    let width = x86_operand_reg_width_bits(reg)?;
    let size = x86_width_to_operand_size(width);
    let ty = x86_width_to_type(width)?;

    let (ir_ea, machine_ea, mut inputs) = x86_reconstruct_effective_address(&inst.operands[1])?;

    // The register operand: a fresh leaf at the ALU width.
    let sym_reg = SmtExpr::var("recon_reg", width);
    inputs.insert(0, ("recon_reg".to_string(), width));

    // The memory operand is `load(ea)` at the ALU width (full register-width
    // access for the RM ALU form), zero-filled.
    let ir_mem = SmtExpr::mem_load(ir_ea, width, false, width);
    let machine_mem = SmtExpr::mem_load(machine_ea, width, false, width);

    let trust_ir_expr = encode_trust_ir_binop(op, ty, sym_reg.clone(), ir_mem);
    let machine_expr = match inst.opcode {
        X86Opcode::AddRM => encode_add_rr(size, sym_reg.clone(), machine_mem),
        // SubRM and CmpRM both compute `reg - load(ea)` (CmpRM's flags reflect
        // exactly this difference); a wrong ALU mapping refutes against the source.
        X86Opcode::SubRM | X86Opcode::CmpRM => encode_sub_rr(size, sym_reg.clone(), machine_mem),
        // ImulRM: `dst = reg * load(ea)` (low half, wrapping). The multiply is
        // commutative so operand order is not observable, but a wrong op
        // (Imul-for-Add) refutes and a wrong EA (different loaded factor) refutes.
        // ImulRMSib is value-identical; its SIB EA feeds `machine_mem` via
        // `x86_reconstruct_effective_address`'s SibMemAddr arm, so a wrong
        // base/index/scale/disp likewise refutes.
        X86Opcode::ImulRM | X86Opcode::ImulRMSib => {
            encode_imul_rr(size, sym_reg.clone(), machine_mem)
        }
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 {op:?}RM_{width} -> {:?} (reg OP load(real-EA), real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    })
}

/// Reconstruct an in-place `Inc`/`Dec` (`dst = pre +/- 1`). Schema: `[dst]` (the
/// destination IS the source — read-modify-write of a single register over a
/// FRESH symbolic pre-value leaf). SOURCE = trust_ir `Iadd`/`Isub` of the
/// pre-value with `1`; MACHINE = x86 `encode_add_rr`/`encode_sub_rr` of the SAME
/// pre-value with `1`. Inc-as-Dec maps `pre + 1` vs `pre - 1` ⇒ REFUTE.
fn reconstruct_x86_inc_dec(
    inst: &X86ISelInst,
    is_inc: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::{encode_add_rr, encode_sub_rr};
    use trust_cg_lower::instructions::Opcode;

    if inst.operands.len() != 1 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_operand_reg_width_bits(dst)?;
    let size = x86_width_to_operand_size(width);
    let ty = x86_width_to_type(width)?;

    // Fresh symbolic PRE-value (the register's value before the in-place update).
    let pre = SmtExpr::var("recon_pre", width);
    let one = SmtExpr::bv_const(1, width);

    let (trust_ir_expr, machine_expr) = if is_inc {
        (
            encode_trust_ir_binop(&Opcode::Iadd, ty, pre.clone(), one.clone()),
            encode_add_rr(size, pre.clone(), one),
        )
    } else {
        (
            encode_trust_ir_binop(&Opcode::Isub, ty, pre.clone(), one.clone()),
            encode_sub_rr(size, pre.clone(), one),
        )
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 {}_{width} -> {:?} (pre {} 1, real-operand)",
            if is_inc { "Inc" } else { "Dec" },
            inst.opcode,
            if is_inc { "+" } else { "-" },
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_pre".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct an integer DIVISION (`Idiv`/`Div`) from the real emitted
/// instruction. The single explicit operand is the DIVISOR; the dividend is the
/// IMPLICIT double-width `RDX:RAX` (set up by `CDQ`/`CQO`/`XOR edx,edx` + a `MOV`
/// of the value into `RAX`). Schema: `[divisor_reg]`.
///
/// We model the dividend as a FRESH single-width `recon_rax` leaf and the divisor
/// as a FRESH `recon_divisor` leaf at the operand width `W`. The MACHINE side is
/// the genuine x86 IDIV/DIV double-width arithmetic:
///   - dividend_2W = `sext(rax, 2W)` (IDIV, the CDQ/CQO step) or `zext(rax, 2W)`
///     (DIV, the zero-fill of RDX),
///   - divisor_2W  = `sext/zext(divisor, 2W)`,
///   - quotient    = `trunc(sdiv/udiv(dividend_2W, divisor_2W), W)` (the value
///     IDIV/DIV leaves in RAX),
///   - remainder   = `trunc(srem/urem(...), W)` (the value left in RDX).
///     The SOURCE side is the trust_ir single-width `Sdiv/Srem` (signed) or
///     `Udiv/Urem` (unsigned) of `(rax, divisor)`. The obligation equates
///     `concat(quotient, remainder)` so BOTH the quotient and the remainder are tied.
///
/// PRECONDITION (load-bearing): `divisor != 0` AND, for the SIGNED form, NO
/// signed overflow (`!(rax == INT_MIN && divisor == -1)`) — exactly the inputs
/// the ISel guard sequence (CMP rhs,-1 + CMOVE) excludes before the IDIV can
/// raise `#DE`. An IDIV-emitted-as-DIV (or vice-versa) bug differs ONLY in
/// sext-vs-zext / sdiv-vs-udiv, which DIVERGES on a NEGATIVE dividend ⇒ REFUTE.
fn reconstruct_x86_division(
    inst: &X86ISelInst,
    signed: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    // Schema: a single DIVISOR register operand (the dividend is implicit RDX:RAX).
    if inst.operands.len() != 1 {
        return None;
    }
    let divisor_op = inst.operands.first()?;
    let width = x86_operand_reg_width_bits(divisor_op)?;
    // Double width: 2W. For W=64 this is 128 (the evaluator's BvSDiv/BvUDiv now
    // model 128-bit division), the widest the model supports.
    let dwidth = width.checked_mul(2)?;
    if dwidth > 128 {
        return None;
    }
    let ty = x86_width_to_type(width)?;

    // Fresh leaves for the implicit dividend (RAX) and the explicit divisor.
    let rax = SmtExpr::var("recon_rax", width);
    let divisor = SmtExpr::var("recon_divisor", width);

    // Extend both to the double width per the signedness (sext for IDIV, zext for
    // DIV). `extra = dwidth - width`.
    let extra = dwidth - width;
    let (dividend_2w, divisor_2w) = if signed {
        (rax.clone().sign_ext(extra), divisor.clone().sign_ext(extra))
    } else {
        (rax.clone().zero_ext(extra), divisor.clone().zero_ext(extra))
    };

    // MACHINE quotient + remainder at the double width, truncated to W.
    let (machine_q_2w, machine_r_2w) = if signed {
        let q = dividend_2w.clone().bvsdiv(divisor_2w.clone());
        // srem composed as `a - (a / b) * b`, mirroring trust_ir_semantics.
        let r = dividend_2w
            .clone()
            .bvsub(q.clone().bvmul(divisor_2w.clone()));
        (q, r)
    } else {
        let q = dividend_2w.clone().bvudiv(divisor_2w.clone());
        let r = dividend_2w
            .clone()
            .bvsub(q.clone().bvmul(divisor_2w.clone()));
        (q, r)
    };
    let machine_q = machine_q_2w.extract(width - 1, 0);
    let machine_r = machine_r_2w.extract(width - 1, 0);
    // FAITHFUL x86 IDIV/DIV semantics: a zero divisor raises #DE (divide error) —
    // the instruction TRAPS and produces NO defined result. We model that with a
    // TrapIfZero wrapper guarded on the divisor, so the machine side is POISON at
    // divisor == 0 (unequal to trust_ir's defined div-by-zero contract value). This
    // makes the `divisor != 0` precondition genuinely LOAD-BEARING in the native
    // evaluator: WITH the precondition the trap point is excluded (Valid); WITHOUT
    // it (the fault-5a mutation) the divisor==0 sample yields Poison ≠ sentinel ⇒
    // the obligation REFUTES (closes the D survivor, #79). AArch64 SDIV/UDIV return
    // 0 and trust_ir has its own contract — only x86 traps, so only this side is
    // wrapped.
    let machine_expr = machine_q.concat(machine_r).trap_if_zero(divisor.clone());

    // SOURCE side: the trust_ir single-width quotient + remainder. Mirrors
    // `encode_trust_ir_binop` (Srem = a - sdiv(a,b)*b at single width).
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;
    let (q_op, r_op) = if signed {
        (Opcode::Sdiv, Opcode::Srem)
    } else {
        (Opcode::Udiv, Opcode::Urem)
    };
    let ir_q = encode_trust_ir_binop(&q_op, ty.clone(), rax.clone(), divisor.clone());
    let ir_r = encode_trust_ir_binop(&r_op, ty, rax.clone(), divisor.clone());
    let trust_ir_expr = ir_q.concat(ir_r);

    // PRECONDITIONS: divisor != 0; and (signed) no INT_MIN / -1 overflow.
    let zero = SmtExpr::bv_const(0, width);
    let mut preconditions = vec![divisor.clone().eq_expr(zero).not_expr()];
    if signed {
        let int_min = SmtExpr::bv_const(1u64 << (width - 1), width);
        let neg_one = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
        let overflow = rax
            .clone()
            .eq_expr(int_min)
            .and_expr(divisor.clone().eq_expr(neg_one));
        preconditions.push(overflow.not_expr());
    }

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 {}_{width} -> {:?} (quotient:remainder, sext/zext dividend)",
            if signed { "Sdiv/Srem" } else { "Udiv/Urem" },
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![
            ("recon_rax".to_string(), width),
            ("recon_divisor".to_string(), width),
        ],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct a CONDITIONAL MOVE (`Cmovcc`/`Cmovcc32`) from the real emitted
/// instruction. The select condition is the IMPLICIT RFLAGS of a prior
/// `CMP a, b`, NOT an operand. Schema: `[dst, src, CondCode(cc)]` where `dst` is
/// also the FALSE value (read-modify-write).
///
/// We model it as a genuine CMP+CMOV PAIR over fresh leaves:
///   - `a`/`b`  : the two compared values (the implicit CMP operands),
///   - `src`    : the value moved when the condition holds,
///   - `dst_old`: the prior value of `dst` (kept when the condition is false).
///     The MACHINE side is `ite(eval_int_condition(cc, flags_of(a, b)), src,
/// dst_old)` — the textbook hardware cc formula over the genuine CMP flags. The
///     SOURCE side is `ite(icmp(intcc_for(cc), a, b), src, dst_old)`. With the
///     matching `(cc, intcc)` pair these AGREE; a WRONG cc (E-for-NE, L-for-GE)
///     yields the COMPLEMENTARY boolean over the same `(a, b)` ⇒ the selects pick
///     different operands ⇒ REFUTE.
fn reconstruct_x86_cond_move(inst: &X86ISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::x86_64_semantics::{encode_int_cmp_flags, eval_int_condition};

    // Schema: [dst, src, CondCode(cc)].
    if inst.operands.len() != 3 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_operand_reg_width_bits(dst)?;
    let src = &inst.operands[1];
    if x86_operand_reg_width_bits(src)? != width {
        return None;
    }
    let cc = match &inst.operands[2] {
        X86ISelOperand::CondCode(cc) => *cc,
        _ => return None,
    };
    // Map the x86 condition code back to the trust_ir integer predicate it
    // implements. A cc with no integer-predicate analogue (O/S/P-family,
    // never used by a value select) fails closed.
    let intcc = x86cc_to_intcc(cc)?;
    let ty = x86_width_to_type(width)?;

    // Fresh leaves: the two CMP operands, the moved-in source, and the prior dst.
    let a = SmtExpr::var("recon_cmp_a", width);
    let b = SmtExpr::var("recon_cmp_b", width);
    let sym_src = SmtExpr::var("recon_src", width);
    let sym_dst = SmtExpr::var("recon_dst", width);

    // MACHINE: ite(cc over flags_of(a, b), src, dst_old).
    let flags = encode_int_cmp_flags(width, a.clone(), b.clone());
    let machine_cond = eval_int_condition(cc, &flags);
    let machine_expr = SmtExpr::ite(machine_cond, sym_src.clone(), sym_dst.clone());

    // SOURCE: ite(icmp(intcc, a, b) == 1, src, dst_old). encode_trust_ir_icmp
    // returns a 1-bit bitvector (bv1 if true), so compare to bv1(1).
    let ir_pred = encode_trust_ir_icmp(&intcc, ty, a.clone(), b.clone());
    let ir_cond = ir_pred.eq_expr(SmtExpr::bv_const(1, 1));
    let trust_ir_expr = SmtExpr::ite(ir_cond, sym_src.clone(), sym_dst.clone());

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 Select_{width} ({cc:?}) -> {:?} (CMP+CMOV pair, real cc)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![
            ("recon_cmp_a".to_string(), width),
            ("recon_cmp_b".to_string(), width),
            ("recon_src".to_string(), width),
            ("recon_dst".to_string(), width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    })
}

/// Map an x86 condition code to the trust_ir integer predicate it implements
/// (the inverse of `trust_cg_lower::x86_64_isel::x86cc_from_intcc`). Returns
/// `None` for condition codes with no integer-comparison analogue (the
/// overflow/sign/parity family), which a value-producing CMOVcc never uses.
fn x86cc_to_intcc(cc: X86CondCode) -> Option<trust_cg_lower::instructions::IntCC> {
    use trust_cg_lower::instructions::IntCC;
    Some(match cc {
        X86CondCode::E => IntCC::Equal,
        X86CondCode::NE => IntCC::NotEqual,
        X86CondCode::L => IntCC::SignedLessThan,
        X86CondCode::GE => IntCC::SignedGreaterThanOrEqual,
        X86CondCode::G => IntCC::SignedGreaterThan,
        X86CondCode::LE => IntCC::SignedLessThanOrEqual,
        X86CondCode::B => IntCC::UnsignedLessThan,
        X86CondCode::AE => IntCC::UnsignedGreaterThanOrEqual,
        X86CondCode::A => IntCC::UnsignedGreaterThan,
        X86CondCode::BE => IntCC::UnsignedLessThanOrEqual,
        // O/NO/S/NS/P/NP have no integer-comparison predicate analogue.
        _ => return None,
    })
}

/// Reconstruct a width-CHANGING extend obligation (`Movzx`/`MovzxW`/`MovsxB`/
/// `MovsxW`/`Movsx`) from the real emitted instruction. Mirrors
/// `function_verifier::reconstruct_extend`.
///
/// The source value occupies the low `from_bits` of its register; we model it as
/// a `from_bits`-wide fresh symbol so the obligation reasons over exactly the bits
/// the extend reads. The trust_ir side (`encode_trust_ir_sextend`/`uextend`) and
/// the x86 side (`encode_movsx`/`encode_movzx`) both extend that `from_bits`-wide
/// symbol to the `to_bits`-wide destination. They agree IFF isel chose the right
/// sign/zero extension of the right source width: a MOVZX-for-Sextend (or vice
/// versa) yields a different result for a negative source ⇒ REFUTE.
fn reconstruct_x86_extend(
    inst: &X86ISelInst,
    from_bits: u32,
    signed: bool,
    from_opcode: String,
    arity: X86AluArity,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{encode_trust_ir_sextend, encode_trust_ir_uextend};
    use crate::x86_64_semantics::{encode_movsx, encode_movzx};

    // Typed positional schema: [dst, src].
    if inst.operands.len() != 2 {
        return None;
    }
    // Destination register width fixes to_bits (must strictly exceed from_bits).
    let to_bits = x86_operand_reg_width_bits(inst.operands.first()?)?;
    if to_bits <= from_bits {
        return None;
    }
    // Source register must hold at least the from_bits source value.
    let src = &inst.operands[1];
    if x86_operand_reg_width_bits(src)? < from_bits {
        return None;
    }

    // Model the source as a from_bits-wide symbol (the bits the extend reads).
    let sym = SmtExpr::var("recon_src", from_bits);
    let trust_ir_expr = if signed {
        encode_trust_ir_sextend(from_bits, to_bits, sym.clone())
    } else {
        encode_trust_ir_uextend(from_bits, to_bits, sym.clone())
    };
    // The x86 encoders read the FULL source register; build a to_bits-wide source
    // register whose low from_bits are `sym` (the rest is don't-care: the encoder
    // extracts the low from_bits before extending), so the machine side reasons
    // over exactly the from_bits-wide symbol the trust_ir side does. `to_bits >
    // from_bits` is guaranteed above, so the widen is always well-formed.
    let src_reg = sym.clone().zero_ext(to_bits - from_bits);
    let machine_expr = if signed {
        encode_movsx(from_bits, to_bits, src_reg)
    } else {
        encode_movzx(from_bits, to_bits, src_reg)
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 {}extend_{}_to_{} -> {:?} (real-operand)",
            if signed { "S" } else { "U" },
            from_bits,
            to_bits,
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_src".to_string(), from_bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: arity.as_u8(),
        },
    })
}

// ===========================================================================
// Scalar FP + bit-manip reconstruction builders.
//
// FP-only obligations carry their operands as NAMED FP leaves (`recon_a`/
// `recon_b`) in `fp_inputs` so the WIRING-PRESERVING FP evaluator
// (`verify_fp_reconstructed_by_evaluation`) substitutes per-leaf into BOTH sides
// — a swapped non-commutative wiring (Subsd/Divsd) genuinely diverges. The
// int->FP and bit-count families take a BITVECTOR source leaf in `inputs` (the
// standard BV evaluator).
// ===========================================================================

/// Reconstruct a binary scalar FP value op (`Addsd/ss`/`Subsd/ss`/`Mulsd/ss`/
/// `Divsd/ss`). Schema: `[dst, a, b]`, all XMM (Fpr32/Fpr64) of the SAME width.
fn reconstruct_x86_fp_binary(
    inst: &X86ISelInst,
    op: &trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{
        encode_fp_add_rr, encode_fp_div_rr, encode_fp_mul_rr, encode_fp_sub_rr,
    };

    if inst.operands.len() != 3 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_fp_scalar_width(dst)?;
    if x86_fp_scalar_width(&inst.operands[1])? != width
        || x86_fp_scalar_width(&inst.operands[2])? != width
    {
        return None;
    }
    let (eb, sb) = x86_fp_format(width)?;
    let fpsize = x86_fp_size(width)?;
    let ty = if width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);

    let trust_ir_expr = encode_trust_ir_fp_binop(op, ty, a.clone(), b.clone());
    let machine_expr = match inst.opcode {
        X86Opcode::Addsd | X86Opcode::Addss => encode_fp_add_rr(fpsize, a.clone(), b.clone()),
        X86Opcode::Subsd | X86Opcode::Subss => encode_fp_sub_rr(fpsize, a.clone(), b.clone()),
        X86Opcode::Mulsd | X86Opcode::Mulss => encode_fp_mul_rr(fpsize, a.clone(), b.clone()),
        X86Opcode::Divsd | X86Opcode::Divss => encode_fp_div_rr(fpsize, a.clone(), b.clone()),
        _ => return None,
    };
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 {op:?}_F{width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
        ],
        vec![],
        from_opcode,
        X86AluArity::Binary,
    ))
}

/// Reconstruct a unary scalar FP sqrt (`Sqrtsd`/`Sqrtss`). Schema: `[dst, a]`.
fn reconstruct_x86_fp_sqrt(inst: &X86ISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fsqrt;
    use crate::x86_64_semantics::encode_fp_sqrt;

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_fp_scalar_width(dst)?;
    if x86_fp_scalar_width(&inst.operands[1])? != width {
        return None;
    }
    let (eb, sb) = x86_fp_format(width)?;
    let fpsize = x86_fp_size(width)?;
    let ty = if width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", width);
    let trust_ir_expr = encode_trust_ir_fsqrt(ty, a.clone());
    let machine_expr = match inst.opcode {
        X86Opcode::Sqrtsd | X86Opcode::Sqrtss => encode_fp_sqrt(fpsize, a.clone()),
        _ => return None,
    };
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 Fsqrt_F{width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![("recon_a".to_string(), eb, sb)],
        vec![],
        from_opcode,
        X86AluArity::Unary,
    ))
}

/// Reconstruct scalar FP hardware MIN/MAX (`Minsd/ss`/`Maxsd/ss`). Schema:
/// `[dst, a, b]`. NON-commutative (the SECOND operand wins on unordered/equal),
/// so a swapped wiring refutes under the wiring-preserving FP evaluator.
fn reconstruct_x86_fp_minmax(
    inst: &X86ISelInst,
    is_min: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{encode_trust_ir_fmaxsd_hw, encode_trust_ir_fminsd_hw};
    use crate::x86_64_semantics::{encode_fp_maxsd, encode_fp_minsd};

    if inst.operands.len() != 3 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_fp_scalar_width(dst)?;
    if x86_fp_scalar_width(&inst.operands[1])? != width
        || x86_fp_scalar_width(&inst.operands[2])? != width
    {
        return None;
    }
    let (eb, sb) = x86_fp_format(width)?;
    let ty = if width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);
    let (trust_ir_expr, machine_expr) = if is_min {
        (
            encode_trust_ir_fminsd_hw(ty, a.clone(), b.clone()),
            encode_fp_minsd(a.clone(), b.clone()),
        )
    } else {
        (
            encode_trust_ir_fmaxsd_hw(ty, a.clone(), b.clone()),
            encode_fp_maxsd(a.clone(), b.clone()),
        )
    };
    // Guard the opcode family matches the requested is_min (fail closed otherwise).
    match (is_min, inst.opcode) {
        (true, X86Opcode::Minsd | X86Opcode::Minss)
        | (false, X86Opcode::Maxsd | X86Opcode::Maxss) => {}
        _ => return None,
    }
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 F{}_F{width} -> {:?} (real-operand)",
            if is_min { "min" } else { "max" },
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
        ],
        vec![],
        from_opcode,
        X86AluArity::Binary,
    ))
}

/// Reconstruct a scalar FP UNORD compare-to-mask (`Cmpsd`/`Cmpss` imm8=3).
/// Schema: `[dst, a, b, imm]`. ONLY the UNORD predicate (imm=3) reconstructs;
/// any other imm fails closed. The result is a width-wide bitvector mask, so
/// `fp_results_equal` compares the `Bv` results directly.
fn reconstruct_x86_fp_cmp_unord(
    inst: &X86ISelInst,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_cmp_unord_mask;
    use crate::x86_64_semantics::encode_fp_cmp_unord_mask;

    if inst.operands.len() != 4 {
        return None;
    }
    // The imm8 predicate MUST be 3 (CMP_UNORD_Q); anything else is not modeled.
    match &inst.operands[3] {
        X86ISelOperand::Imm(3) => {}
        _ => return None,
    }
    let dst = inst.operands.first()?;
    let width = x86_fp_scalar_width(dst)?;
    if x86_fp_scalar_width(&inst.operands[1])? != width
        || x86_fp_scalar_width(&inst.operands[2])? != width
    {
        return None;
    }
    let (eb, sb) = x86_fp_format(width)?;
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);
    let trust_ir_expr = encode_trust_ir_cmp_unord_mask(width, a.clone(), b.clone());
    let machine_expr = match inst.opcode {
        X86Opcode::Cmpsd | X86Opcode::Cmpss => {
            encode_fp_cmp_unord_mask(width, a.clone(), b.clone())
        }
        _ => return None,
    };
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 FcmpUnord_F{width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
        ],
        vec![],
        from_opcode,
        X86AluArity::Binary,
    ))
}

/// Reconstruct an FP→FP format cast (`Cvtsd2ss` narrow / `Cvtss2sd` widen).
/// Schema: `[dst, a]`, both XMM of DIFFERING widths. Wrong direction refutes
/// (the source side is keyed on the DEST format; the FPToFP evaluator preserves
/// it). The single FP leaf is `recon_a` at the SOURCE width.
fn reconstruct_x86_fp_format_convert(
    inst: &X86ISelInst,
    to_bits: u32,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fp_format_convert;
    use crate::x86_64_semantics::{encode_cvtsd2ss, encode_cvtss2sd};

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let dst_width = x86_fp_scalar_width(dst)?;
    let src_width = x86_fp_scalar_width(&inst.operands[1])?;
    if dst_width != to_bits || src_width == to_bits {
        return None;
    }
    let (src_eb, src_sb) = x86_fp_format(src_width)?;
    let (to_eb, to_sb) = x86_fp_format(to_bits)?;
    let a = SmtExpr::var("recon_a", src_width);
    let trust_ir_expr = encode_trust_ir_fp_format_convert(to_eb, to_sb, a.clone());
    let machine_expr = match inst.opcode {
        X86Opcode::Cvtsd2ss => encode_cvtsd2ss(a.clone()),
        X86Opcode::Cvtss2sd => encode_cvtss2sd(a.clone()),
        _ => return None,
    };
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 F{}_F{src_width}_to_F{to_bits} -> {:?} (real-operand)",
            if to_bits > src_width {
                "promote"
            } else {
                "demote"
            },
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![("recon_a".to_string(), src_eb, src_sb)],
        vec![],
        from_opcode,
        X86AluArity::Unary,
    ))
}

/// Reconstruct an FP→signed-int convert. Schema: `[dst(GPR), a(XMM)]`. BOTH the
/// TRUNCATING (RTZ) `Cvttsd2si`/`Cvttss2si` and the ROUND-TO-NEAREST-EVEN (RNE)
/// `Cvtsd2si`/`Cvtss2si` forms are reconstructed against the x86-ISA-faithful
/// reference: the evaluator models the rounding mode of `fp.to_sbv` (round per
/// `rm`) AND the x86 INTEGER-INDEFINITE out-of-range behaviour (#99: NaN/+-Inf/
/// overflow -> 0x80..0, NOT saturating). A truncating-for-rounding lowering bug
/// DIVERGES on a non-integral tie input (1.5 -> RTZ 1 vs RNE 2) ⇒ REFUTE.
///
///   * `truncating == true`  -> CVTT*, source RTZ (`encode_trust_ir_fcvt_to_sint_x86`);
///   * `truncating == false` -> CVT*, source RNE (`encode_trust_ir_fcvt_to_sint_x86_rne`).
fn reconstruct_x86_fp_to_sint(
    inst: &X86ISelInst,
    truncating: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{
        encode_trust_ir_fcvt_to_sint_x86, encode_trust_ir_fcvt_to_sint_x86_rne,
    };
    use crate::x86_64_semantics::{
        encode_cvtsd2si, encode_cvtss2si, encode_cvttsd2si, encode_cvttss2si,
    };

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    // dst is the INTEGER result (GPR); the source is an XMM FP register.
    let int_width = x86_operand_reg_width_bits(dst)?;
    if int_width != 32 && int_width != 64 {
        return None;
    }
    let fp_width = x86_fp_scalar_width(&inst.operands[1])?;
    let (eb, sb) = x86_fp_format(fp_width)?;
    let a = SmtExpr::var("recon_a", fp_width);
    // SOURCE side: the x86-ISA-faithful reference matches the opcode's rounding
    // mode (RTZ for CVTT*, RNE for CVT*) AND the x86 out-of-range semantics
    // (INTEGER-INDEFINITE on NaN / +-Inf / overflow — #99, NOT the saturating
    // AArch64/wasm/RISC-V FcvtToInt). A wrong rounding mode on either side still
    // refutes (1.5 -> RTZ 1 vs RNE 2); the out-of-range edge inputs now match the
    // x86 machine encoder bit-for-bit.
    let trust_ir_expr = if truncating {
        encode_trust_ir_fcvt_to_sint_x86(int_width, a.clone())
    } else {
        encode_trust_ir_fcvt_to_sint_x86_rne(int_width, a.clone())
    };
    let machine_expr = match inst.opcode {
        X86Opcode::Cvttsd2si => encode_cvttsd2si(int_width, a.clone()),
        X86Opcode::Cvttss2si => encode_cvttss2si(int_width, a.clone()),
        X86Opcode::Cvtsd2si => encode_cvtsd2si(int_width, a.clone()),
        X86Opcode::Cvtss2si => encode_cvtss2si(int_width, a.clone()),
        _ => return None,
    };
    let label = if truncating {
        "FcvtTruncToSint"
    } else {
        "FcvtRneToSint"
    };
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 {label}_I{int_width}_F{fp_width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![("recon_a".to_string(), eb, sb)],
        vec![],
        from_opcode,
        X86AluArity::Unary,
    ))
}

/// Reconstruct a signed-int→FP convert (`Cvtsi2sd`/`Cvtsi2ss`). Schema:
/// `[dst(XMM), src(GPR64)]`. The source is a BITVECTOR (the ISel sign-extends a
/// narrower operand to 64 bits first), so it is carried in `inputs` and verified
/// by the standard BV evaluator over the real integer range. The machine encoder
/// interprets the source as SIGNED.
fn reconstruct_x86_sint_to_fp(
    inst: &X86ISelInst,
    to_bits: u32,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fcvt_from_sint;
    use crate::x86_64_semantics::{X86CvtIntWidth, encode_cvtsi2sd, encode_cvtsi2ss};

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let dst_fp_width = x86_fp_scalar_width(dst)?;
    if dst_fp_width != to_bits {
        return None;
    }
    let (eb, sb) = x86_fp_format(to_bits)?;
    // Source is a GPR; the ISel always widens to a 64-bit signed integer.
    let int_width = x86_operand_reg_width_bits(&inst.operands[1])?;
    let cvt_width = match int_width {
        32 => X86CvtIntWidth::I32,
        64 => X86CvtIntWidth::I64,
        _ => return None,
    };
    let a = SmtExpr::var("recon_src", int_width);
    let trust_ir_expr = encode_trust_ir_fcvt_from_sint(eb, sb, a.clone());
    let machine_expr = match inst.opcode {
        X86Opcode::Cvtsi2sd => encode_cvtsi2sd(cvt_width, a.clone()),
        X86Opcode::Cvtsi2ss => encode_cvtsi2ss(cvt_width, a.clone()),
        _ => return None,
    };
    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 FcvtFromSint_F{to_bits}_I{int_width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_src".to_string(), int_width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: X86AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct a bit-count op (`Popcnt`/`Tzcnt`/`Lzcnt`/`Bsf`/`Bsr`). Schema:
/// `[dst, src]`, both GPR of the SAME width. The source is a BV leaf in `inputs`
/// (standard BV evaluator). `Bsf`/`Bsr` carry a LOAD-BEARING `src != 0`
/// precondition (the zero input is architecturally undefined). A wrong bit-count
/// opcode (Popcnt-for-Tzcnt) diverges for almost every input ⇒ REFUTE.
fn reconstruct_x86_bit_count(
    inst: &X86ISelInst,
    source_op: &X86SourceOp,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{
        encode_trust_ir_bsr_nonzero, encode_trust_ir_ctlz, encode_trust_ir_ctpop,
        encode_trust_ir_cttz,
    };
    use crate::x86_64_semantics::{
        encode_bsf, encode_bsr, encode_lzcnt, encode_popcnt, encode_tzcnt,
    };

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_operand_reg_width_bits(dst)?;
    if x86_operand_reg_width_bits(&inst.operands[1])? != width {
        return None;
    }
    if width != 32 && width != 64 {
        return None;
    }
    let a = SmtExpr::var("recon_src", width);
    let nonzero = a.clone().eq_expr(SmtExpr::bv_const(0, width)).not_expr();
    let (trust_ir_expr, machine_expr, preconditions, label): (
        SmtExpr,
        SmtExpr,
        Vec<SmtExpr>,
        &str,
    ) = match (source_op, inst.opcode) {
        (X86SourceOp::Popcnt, X86Opcode::Popcnt) => (
            encode_trust_ir_ctpop(a.clone()),
            encode_popcnt(a.clone()),
            vec![],
            "Ctpop",
        ),
        (X86SourceOp::Tzcnt, X86Opcode::Tzcnt) => (
            encode_trust_ir_cttz(a.clone()),
            encode_tzcnt(a.clone()),
            vec![],
            "Cttz",
        ),
        (X86SourceOp::Lzcnt, X86Opcode::Lzcnt) => (
            encode_trust_ir_ctlz(a.clone()),
            encode_lzcnt(a.clone()),
            vec![],
            "Ctlz",
        ),
        (X86SourceOp::Bsf, X86Opcode::Bsf) => (
            encode_trust_ir_cttz(a.clone()),
            encode_bsf(a.clone()),
            vec![nonzero],
            "Bsf",
        ),
        (X86SourceOp::Bsr, X86Opcode::Bsr) => (
            encode_trust_ir_bsr_nonzero(a.clone()),
            encode_bsr(a.clone()),
            vec![nonzero],
            "Bsr",
        ),
        _ => return None,
    };
    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 {label}_{width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_src".to_string(), width)],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: X86AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct a GPR register-to-register copy (`MovRR`/`MovRR32`). Schema:
/// `[dst, src]`, both GPR of the SAME width. The copy is a bit-preserving
/// identity: source = the symbol itself (trust_ir copy = identity); machine =
/// `encode_mov_rr` (also identity). The non-vacuity is the SAME as for the
/// reconstructed ALU ops — the machine side is built from the REAL opcode's
/// encoder, so binding a non-copy opcode here (`encode_neg`/`encode_not`) would
/// REFUTE (proved by the wrong-machine-encoder refutation test). The source is a
/// BV leaf in `inputs` (standard BV evaluator).
fn reconstruct_x86_copy_gpr(inst: &X86ISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::x86_64_semantics::encode_mov_rr;

    // Typed positional schema: [dst, src].
    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_operand_reg_width_bits(dst)?;
    if x86_operand_reg_width_bits(&inst.operands[1])? != width {
        return None;
    }
    let size = x86_width_to_operand_size(width);
    let sym = SmtExpr::var("recon_src", width);
    // trust_ir copy is the identity; machine MOV r,r is the identity. (A wrong
    // opcode bound here would use a different machine encoder — see the
    // wrong-machine-encoder refutation test.)
    let trust_ir_expr = sym.clone();
    let machine_expr = encode_mov_rr(size, sym.clone());
    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 Copy_{width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_src".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: X86AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct an XMM SCALAR register-to-register copy (`MovssRR`/`MovsdRR`).
/// Schema: `[dst, src]`, both XMM (Fpr32/Fpr64) of the SAME width. The copy is a
/// bit-preserving scalar identity, carried as a NAMED FP leaf (`recon_a`) in
/// `fp_inputs` so the wiring-preserving FP evaluator substitutes it into both
/// sides. Source = identity; machine = `encode_mov_rr` (identity).
fn reconstruct_x86_copy_xmm(inst: &X86ISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::x86_64_semantics::encode_mov_rr;

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_fp_scalar_width(dst)?;
    if x86_fp_scalar_width(&inst.operands[1])? != width {
        return None;
    }
    let (eb, sb) = x86_fp_format(width)?;
    let size = x86_width_to_operand_size(width);
    let a = SmtExpr::var("recon_a", width);
    let trust_ir_expr = a.clone();
    let machine_expr = encode_mov_rr(size, a.clone());
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 Copy_F{width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![("recon_a".to_string(), eb, sb)],
        vec![],
        from_opcode,
        X86AluArity::Unary,
    ))
}

/// Reconstruct a three-operand `IMUL r,r/m,imm` (`ImulRRI`). Schema:
/// `[dst, src, Imm(imm)]`, dst+src GPR of the SAME width. `dst = src *
/// sign_extend(imm)` (wrapping low half). Source =
/// `encode_trust_ir_binop(Imul, src, imm_const)`; machine = `encode_imul_rri`.
/// Width-polymorphic via the dst register class. A wrong imm injected at the
/// builder refutes; the multiply is commutative so an operand swap is not
/// observable (documented).
fn reconstruct_x86_imul_imm(inst: &X86ISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::x86_64_semantics::encode_imul_rri;
    use trust_cg_lower::instructions::Opcode;

    // Typed positional schema: [dst, src, Imm].
    if inst.operands.len() != 3 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_operand_reg_width_bits(dst)?;
    if x86_operand_reg_width_bits(&inst.operands[1])? != width {
        return None;
    }
    let ty = x86_width_to_type(width)?;
    let size = x86_width_to_operand_size(width);
    let imm = match &inst.operands[2] {
        X86ISelOperand::Imm(imm) => *imm,
        _ => return None,
    };
    let src = SmtExpr::var("recon_src", width);
    // SOURCE: Imul(src, imm-as-width-const). The IMUL imm is sign-extended to the
    // operand width by the hardware; mask the i64 to the operand width so the
    // source constant matches the machine `encode_imul_rri` (which builds a
    // width-wide bv_const from the SAME imm).
    let imm_masked = (imm as u64) & crate::smt::mask(u64::MAX, width);
    let imm_const = SmtExpr::bv_const(imm_masked, width);
    let trust_ir_expr = encode_trust_ir_binop(&Opcode::Imul, ty, src.clone(), imm_const);
    let machine_expr = encode_imul_rri(size, src.clone(), imm);
    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED x86_64 Imul_{width}_Imm({imm}) -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_src".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: X86AluArity::Binary.as_u8(),
        },
    })
}

/// Reconstruct an SSE4.1 scalar round-to-integral (`Roundsd`/`Roundss imm8`).
/// Schema: `[dst, src, Imm(imm8)]`, dst+src XMM of the SAME width. The
/// imm8[1:0] rounding-select picks the mode:
///   01 = floor (RTN), 10 = ceil (RTP), 11 = trunc (RTZ).
/// The round-to-nearest mode (00) is never emitted by the backend, so it fails
/// closed (returns `None`). Source = `encode_trust_ir_ffloor/fceil/ftrunc`
/// (RTN/RTP/RTZ); machine = `encode_fp_round` with the SAME imm8. The native FP
/// evaluator faithfully models all three rounding modes (`FPRoundToIntegral` ->
/// `f64::floor/ceil/trunc`), so a wrong mode (floor-for-ceil) DIVERGES on a
/// non-integral input (0.5/-0.5/PI) ⇒ REFUTE. The single FP leaf is `recon_a`.
fn reconstruct_x86_round(inst: &X86ISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{
        encode_trust_ir_fceil, encode_trust_ir_ffloor, encode_trust_ir_ftrunc,
    };
    use crate::x86_64_semantics::encode_fp_round;

    // Typed positional schema: [dst, src, Imm(imm8)].
    if inst.operands.len() != 3 {
        return None;
    }
    let dst = inst.operands.first()?;
    let width = x86_fp_scalar_width(dst)?;
    if x86_fp_scalar_width(&inst.operands[1])? != width {
        return None;
    }
    // Opcode fixes the width (Roundss=F32, Roundsd=F64).
    let opcode_width = match inst.opcode {
        X86Opcode::Roundss => 32,
        X86Opcode::Roundsd => 64,
        _ => return None,
    };
    if width != opcode_width {
        return None;
    }
    let imm8 = match &inst.operands[2] {
        X86ISelOperand::Imm(imm) => *imm as u8,
        _ => return None,
    };
    let (eb, sb) = x86_fp_format(width)?;
    let fpsize = x86_fp_size(width)?;
    let ty = if width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", width);
    // SOURCE: the trust_ir round op selected by imm8[1:0] (RTN/RTP/RTZ). The
    // round-to-nearest mode (00) is never emitted; fail closed so a stray
    // RNE-encoded ROUND cannot be silently credited.
    let (trust_ir_expr, mode_label) = match imm8 & 0b11 {
        0b01 => (encode_trust_ir_ffloor(ty, a.clone()), "floor"),
        0b10 => (encode_trust_ir_fceil(ty, a.clone()), "ceil"),
        0b11 => (encode_trust_ir_ftrunc(ty, a.clone()), "trunc"),
        _ => return None,
    };
    // MACHINE: ROUNDSD/ROUNDSS with the SAME imm8 (decodes the same mode).
    let machine_expr = encode_fp_round(fpsize, imm8, a.clone());
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 Round_{mode_label}_F{width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![("recon_a".to_string(), eb, sb)],
        vec![],
        from_opcode,
        X86AluArity::Unary,
    ))
}

// ---------------------------------------------------------------------------
// SSE2/SSE4.1 PACKED INTEGER lane-wise reconstruction
// ---------------------------------------------------------------------------

/// Build a 128-bit packed operand pair as two 64-bit halves each (the eval env
/// values are u64, so a 128-bit vector is carried as `<name>_lo`/`<name>_hi`).
fn x86_v128_operand(name: &str) -> SmtExpr {
    SmtExpr::var(format!("{name}_hi"), 64).concat(SmtExpr::var(format!("{name}_lo"), 64))
}

/// The four 64-bit-half input descriptors for a two-operand 128-bit packed op.
fn x86_v128_binary_inputs() -> Vec<(String, u32)> {
    vec![
        ("recon_a_lo".to_string(), 64),
        ("recon_a_hi".to_string(), 64),
        ("recon_b_lo".to_string(), 64),
        ("recon_b_hi".to_string(), 64),
    ]
}

/// Both XMM operands of `inst` (slots 1 + 2) must be 128-bit (Fpr128) VRegs.
fn x86_two_xmm128_operands(inst: &X86ISelInst) -> bool {
    inst.operands.len() == 3
        && (1..=2).all(|i| {
            matches!(
                inst.operands.get(i),
                Some(X86ISelOperand::VReg(v)) if v.class == RegClass::Fpr128
            )
        })
}

/// Reconstruct a LANE-WISE packed integer ARITHMETIC op (PADD*/PSUB*/PMULLW/
/// PMULLD). Schema: `[dst_xmm, a_xmm, b_xmm]`, all 128-bit. The MACHINE side is the
/// real packed encoder at the element width fixed by the opcode; the SOURCE side is
/// the trust_ir scalar op `map_lanes`-applied at the SAME arrangement. A wrong lane
/// op (PADD-for-PSUB) or wrong lane width (i16x8 vs i32x4) REFUTES.
fn reconstruct_x86_packed_int_binary(
    inst: &X86ISelInst,
    op: &trust_cg_lower::instructions::Opcode,
    arrangement: crate::smt::VectorArrangement,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_lanewise_binop;
    use crate::x86_64_semantics::{
        encode_paddb, encode_paddd, encode_paddq, encode_paddw, encode_pmulld, encode_pmullw,
        encode_psubb, encode_psubd, encode_psubq, encode_psubw,
    };

    if !x86_two_xmm128_operands(inst) {
        return None;
    }
    let a = x86_v128_operand("recon_a");
    let b = x86_v128_operand("recon_b");

    // MACHINE: decode the REAL opcode to its packed encoder.
    let machine_expr = match inst.opcode {
        X86Opcode::Paddb => encode_paddb(a.clone(), b.clone()),
        X86Opcode::Paddw => encode_paddw(a.clone(), b.clone()),
        X86Opcode::Paddd => encode_paddd(a.clone(), b.clone()),
        X86Opcode::Paddq => encode_paddq(a.clone(), b.clone()),
        X86Opcode::Psubb => encode_psubb(a.clone(), b.clone()),
        X86Opcode::Psubw => encode_psubw(a.clone(), b.clone()),
        X86Opcode::Psubd => encode_psubd(a.clone(), b.clone()),
        X86Opcode::Psubq => encode_psubq(a.clone(), b.clone()),
        X86Opcode::Pmullw => encode_pmullw(a.clone(), b.clone()),
        X86Opcode::Pmulld => encode_pmulld(a.clone(), b.clone()),
        _ => return None,
    };
    // SOURCE: the trust_ir scalar op map_lanes-applied at the SAME arrangement.
    let trust_ir_expr = encode_trust_ir_lanewise_binop(op, arrangement, a, b);

    Some(x86_packed_obligation(
        format!(
            "RECONSTRUCTED x86_64 packed {op:?} -> {:?} (v128 lane-wise)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        from_opcode,
    ))
}

/// Reconstruct the HORIZONTAL byte sum-of-absolute-differences op (`PSADBW`).
/// Schema: `[dst_xmm, a_xmm, b_xmm]`, all 128-bit. MACHINE = `encode_psadbw`
/// (the real horizontal SAD encoder); SOURCE = `encode_trust_ir_byte_sad` (the
/// independently-written SAD spec). A wrong emitted opcode (e.g. lane-wise
/// PADDB/PSUBB) reconstructs to a different machine expression and REFUTES — the
/// Reconstructed provenance is what credits this obligation non-degenerate even
/// though a correct lowering reconstructs to `sad == sad` (same rule as the
/// lane-wise packed family and the bit-count reductions).
fn reconstruct_x86_psadbw(inst: &X86ISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_byte_sad;
    use crate::x86_64_semantics::encode_psadbw;

    if !x86_two_xmm128_operands(inst) {
        return None;
    }
    let a = x86_v128_operand("recon_a");
    let b = x86_v128_operand("recon_b");

    let machine_expr = match inst.opcode {
        X86Opcode::Psadbw => encode_psadbw(a.clone(), b.clone()),
        _ => return None,
    };
    let trust_ir_expr = encode_trust_ir_byte_sad(a, b);

    Some(x86_packed_obligation(
        format!(
            "RECONSTRUCTED x86_64 byte-SAD -> {:?} (v128 horizontal)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        from_opcode,
    ))
}

/// Reconstruct a LANE-WISE packed integer COMPARE-MASK op (PCMPEQ*/PCMPGT*).
/// Schema: `[dst_xmm, a_xmm, b_xmm]`, all 128-bit. The MACHINE side is the real
/// packed compare encoder; the SOURCE side is the trust_ir lane-wise compare-mask
/// at the SAME arrangement. A wrong predicate (Eq-for-Sgt) or wrong lane width
/// REFUTES.
fn reconstruct_x86_packed_int_cmp(
    inst: &X86ISelInst,
    cond: &trust_cg_lower::instructions::IntCC,
    arrangement: crate::smt::VectorArrangement,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_lanewise_cmp_mask;
    use crate::x86_64_semantics::{
        encode_pcmpeqb, encode_pcmpeqd, encode_pcmpeqq, encode_pcmpeqw, encode_pcmpgtb,
        encode_pcmpgtd, encode_pcmpgtq, encode_pcmpgtw,
    };

    if !x86_two_xmm128_operands(inst) {
        return None;
    }
    let a = x86_v128_operand("recon_a");
    let b = x86_v128_operand("recon_b");

    let machine_expr = match inst.opcode {
        X86Opcode::Pcmpeqb => encode_pcmpeqb(a.clone(), b.clone()),
        X86Opcode::Pcmpeqw => encode_pcmpeqw(a.clone(), b.clone()),
        X86Opcode::Pcmpeqd => encode_pcmpeqd(a.clone(), b.clone()),
        X86Opcode::Pcmpeqq => encode_pcmpeqq(a.clone(), b.clone()),
        X86Opcode::Pcmpgtb => encode_pcmpgtb(a.clone(), b.clone()),
        X86Opcode::Pcmpgtw => encode_pcmpgtw(a.clone(), b.clone()),
        X86Opcode::Pcmpgtd => encode_pcmpgtd(a.clone(), b.clone()),
        X86Opcode::Pcmpgtq => encode_pcmpgtq(a.clone(), b.clone()),
        _ => return None,
    };
    let trust_ir_expr = encode_trust_ir_lanewise_cmp_mask(cond, arrangement, a, b);

    Some(x86_packed_obligation(
        format!(
            "RECONSTRUCTED x86_64 packed Icmp_{cond:?} -> {:?} (v128 lane-wise)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        from_opcode,
    ))
}

/// Reconstruct a FULL-WIDTH packed BITWISE op (PAND/POR/PXOR/PANDN; ANDPS/ANDPD).
/// Bitwise is lane-independent, so the full-width SmtExpr op IS the lane-wise
/// reconstruction. Schema: `[dst_xmm, a_xmm, b_xmm]`, all 128-bit. A wrong op
/// (PAND-for-PXOR) or the PANDN operand-complement asymmetry REFUTES.
fn reconstruct_x86_packed_v128_bitwise(
    inst: &X86ISelInst,
    op: &trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_v128_bitwise;
    use crate::x86_64_semantics::{encode_pand, encode_pandn, encode_por, encode_pxor};

    if !x86_two_xmm128_operands(inst) {
        return None;
    }
    let a = x86_v128_operand("recon_a");
    let b = x86_v128_operand("recon_b");

    let machine_expr = match inst.opcode {
        // ANDPS/ANDPD compute the same 128-bit AND as PAND (FP-domain encoded).
        X86Opcode::Pand | X86Opcode::Andps | X86Opcode::Andpd => encode_pand(a.clone(), b.clone()),
        X86Opcode::Por => encode_por(a.clone(), b.clone()),
        X86Opcode::Pxor => encode_pxor(a.clone(), b.clone()),
        // PANDN = (~a) & b — the FIRST operand is complemented.
        X86Opcode::Pandn => encode_pandn(a.clone(), b.clone()),
        _ => return None,
    };
    let trust_ir_expr = encode_trust_ir_v128_bitwise(op, a, b);

    Some(x86_packed_obligation(
        format!(
            "RECONSTRUCTED x86_64 V128 {op:?} -> {:?} (full-width bitwise)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        from_opcode,
    ))
}

/// Build a packed-INTEGER reconstructed [`ProofObligation`] over the four 64-bit-
/// half BV inputs (the multi-input random evaluator builds full 128-bit operands
/// by concatenation; 128-bit `concat`/`extract`/`bvadd` are evaluated natively).
fn x86_packed_obligation(
    name: String,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
    from_opcode: String,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: x86_v128_binary_inputs(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    }
}

/// Reconstruct a LANE-WISE packed FP binary op (ADDPS/SUBPS/MULPS/DIVPS = 4×f32;
/// ADDPD/SUBPD/MULPD/DIVPD = 2×f64). The packed op is N independent identical
/// scalar FP ops, so one representative FP lane (FP-typed leaves) witnesses the
/// full-vector value equivalence — exactly as the scalar `reconstruct_x86_fp_binary`
/// proves one Addsd lane. The lane width is fixed by the opcode (PS=32, PD=64); a
/// wrong op (ADDPS-for-SUBPS) DIVERGES under the FP evaluator ⇒ REFUTE.
fn reconstruct_x86_packed_fp_binary(
    inst: &X86ISelInst,
    op: &trust_cg_lower::instructions::Opcode,
    lane_bits: u32,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::x86_64_semantics::{
        encode_packed_fp_add_lane, encode_packed_fp_div_lane, encode_packed_fp_mul_lane,
        encode_packed_fp_sub_lane,
    };

    // Schema: [dst_xmm, a_xmm, b_xmm]. The packed XMM operands are 128-bit Fpr128;
    // the per-lane reconstruction uses an FP-typed leaf at the lane width.
    if !x86_two_xmm128_operands(inst) {
        return None;
    }
    let (eb, sb) = x86_fp_format(lane_bits)?;
    let fpsize = x86_fp_size(lane_bits)?;
    let ty = if lane_bits == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", lane_bits);
    let b = SmtExpr::var("recon_b", lane_bits);

    let trust_ir_expr = encode_trust_ir_fp_binop(op, ty, a.clone(), b.clone());
    let machine_expr = match inst.opcode {
        X86Opcode::Addps | X86Opcode::Addpd => encode_packed_fp_add_lane(fpsize, a, b),
        X86Opcode::Subps | X86Opcode::Subpd => encode_packed_fp_sub_lane(fpsize, a, b),
        X86Opcode::Mulps | X86Opcode::Mulpd => encode_packed_fp_mul_lane(fpsize, a, b),
        X86Opcode::Divps | X86Opcode::Divpd => encode_packed_fp_div_lane(fpsize, a, b),
        _ => return None,
    };
    Some(x86_fp_obligation(
        format!(
            "RECONSTRUCTED x86_64 packed {op:?}_F{lane_bits} -> {:?} (per-lane)",
            inst.opcode
        ),
        trust_ir_expr,
        machine_expr,
        vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
        ],
        vec![],
        from_opcode,
        X86AluArity::Binary,
    ))
}

/// Build an FP-only reconstructed [`ProofObligation`] (operands carried as named
/// FP leaves in `fp_inputs`, verified by the wiring-preserving FP evaluator).
#[allow(clippy::too_many_arguments)]
fn x86_fp_obligation(
    name: String,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
    fp_inputs: Vec<(String, u32, u32)>,
    preconditions: Vec<SmtExpr>,
    from_opcode: String,
    arity: X86AluArity,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![],
        preconditions,
        fp_inputs,
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: arity.as_u8(),
        },
    }
}

/// Build a REPRESENTATIVE [`X86ISelInst`] for a reconstructable x86-64 opcode,
/// with fresh register operands in the typed positional schema the reconstructor
/// expects. Returns `None` for any opcode not in [`x86_opcode_to_source_op`].
/// Mirrors `function_verifier::representative_reconstructable_inst`.
///
/// This is the opcode-complete entry point the COVERAGE GATE uses: the gate has
/// only an opcode, so it synthesizes a representative instance, reconstructs the
/// obligation, and credits the opcode COVERED iff that obligation discharges
/// `Valid`. The representative is the GENERIC 64-bit register form, except the
/// extends (which take a narrower source / wider dest fixed by the opcode) and the
/// RR shift form (`[dst, src1]`, count implicit in CL).
pub fn representative_reconstructable_inst(opcode: X86Opcode) -> Option<X86ISelInst> {
    use trust_cg_ir::regs::VReg;

    let (source_op, arity) = x86_opcode_to_source_op(opcode)?;
    let r64 = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64));
    let r32 = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32));
    // XMM scalar VRegs carry the lane width in the RegClass (Fpr64 = SD/double,
    // Fpr32 = SS/single), exactly as the ISel emits scalar FP ops pre-regalloc.
    let xd = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr64));
    let xs = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr32));
    // Is this opcode the single-precision (SS) form of its family?
    let is_ss = matches!(
        opcode,
        X86Opcode::Addss
            | X86Opcode::Subss
            | X86Opcode::Mulss
            | X86Opcode::Divss
            | X86Opcode::Sqrtss
            | X86Opcode::Minss
            | X86Opcode::Maxss
            | X86Opcode::Cmpss
            | X86Opcode::Cvtss2si
            | X86Opcode::Cvttss2si
            | X86Opcode::Cvtsi2ss
            | X86Opcode::Roundss
            | X86Opcode::MovssRR
    );
    let xfp = |id: u32| if is_ss { xs(id) } else { xd(id) };

    let operands = match &source_op {
        // Extends widen a narrower source into a wider dest. MOVSXD is i32->i64;
        // byte/word forms read a 32-bit source register (low byte/word) into a
        // 64-bit dest (the encoder always sets REX.W).
        X86SourceOp::Sextend { from_bits: 32 } => vec![r64(0), r32(1)],
        X86SourceOp::Sextend { .. } | X86SourceOp::Uextend { .. } => vec![r64(0), r32(1)],

        // ---- Scalar FP families (XMM operands) ----
        // Binary FP value ops + min/max: [dst, a, b], all XMM same width.
        X86SourceOp::FpBinary(_) | X86SourceOp::FpMinMax { .. } => vec![xfp(0), xfp(1), xfp(2)],
        // Unary sqrt: [dst, a].
        X86SourceOp::FpSqrt => vec![xfp(0), xfp(1)],
        // Compare-to-mask: [dst, a, b, imm=3].
        X86SourceOp::FpCmpUnord => vec![xfp(0), xfp(1), xfp(2), X86ISelOperand::Imm(3)],
        // FP->FP cast: [dst(to), src(from)]. Cvtsd2ss narrows D->S; Cvtss2sd widens.
        X86SourceOp::FpFormatConvert { to_bits: 32 } => vec![xs(0), xd(1)],
        X86SourceOp::FpFormatConvert { .. } => vec![xd(0), xs(1)],
        // FP->signed-int: [dst(GPR64), src(XMM)].
        X86SourceOp::FpToSint { .. } => vec![r64(0), xfp(1)],
        // signed-int->FP: [dst(XMM), src(GPR64)].
        X86SourceOp::SintToFp { .. } => vec![xfp(0), r64(1)],

        // ---- Bit-count (GPR operands): [dst, src]. ----
        X86SourceOp::Popcnt
        | X86SourceOp::Tzcnt
        | X86SourceOp::Lzcnt
        | X86SourceOp::Bsf
        | X86SourceOp::Bsr => vec![r64(0), r64(1)],

        // LEA: an ADDRESS-MODE operand, NOT plain registers. Plain Lea is
        // [dst, MemAddr{base,disp}]; SIB LeaSib is [dst, SibMemAddr{base,index,..}].
        // A representative scale=1/disp=0 exercises the reconstruction path
        // (a wrong EA encoder still refutes — see the reconstruction_x86 tests).
        // Matched BEFORE the Unary arm because plain Lea uses Unary arity.
        X86SourceOp::EffectiveAddress { has_index: false } => {
            vec![
                r64(0),
                X86ISelOperand::MemAddr {
                    base: Box::new(r64(1)),
                    disp: 0,
                },
            ]
        }
        X86SourceOp::EffectiveAddress { has_index: true } => {
            vec![
                r64(0),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(r64(1)),
                    index: Box::new(r64(2)),
                    scale: 1,
                    disp: 0,
                },
            ]
        }
        // ---- GPR register copy: [dst, src]. ----
        X86SourceOp::CopyGpr => vec![r64(0), r64(1)],
        // ---- XMM scalar register copy: [dst, src]. ----
        X86SourceOp::CopyXmm => vec![xfp(0), xfp(1)],
        // ---- 3-operand IMUL: [dst, src, Imm]. ----
        X86SourceOp::ImulImm => vec![r64(0), r64(1), X86ISelOperand::Imm(42)],
        // ---- ROUNDSD/ROUNDSS: [dst, src, Imm(imm8)]. Representative = floor
        //      (imm8[1:0]=01). `reconstruction_discharges_valid` additionally
        //      requires ALL THREE modes (floor/ceil/trunc) to discharge.
        X86SourceOp::Round => vec![xfp(0), xfp(1), X86ISelOperand::Imm(0b01)],

        // ---- SSE2/SSE4.1 packed integer + full-width bitwise + packed FP:
        //      [dst_xmm, a_xmm, b_xmm], all 128-bit Fpr128 (the ISel packed XMM
        //      operand class). The per-lane FP reconstruction reads the lane width
        //      from the opcode, not the register class, so Fpr128 is correct for
        //      both the integer and FP packed families. ----
        X86SourceOp::PackedIntBinary { .. }
        | X86SourceOp::PackedIntCmp { .. }
        | X86SourceOp::PackedV128Bitwise(_)
        | X86SourceOp::PsadbwByteSad
        | X86SourceOp::PackedFpBinary { .. } => {
            let xv = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr128));
            vec![xv(0), xv(1), xv(2)]
        }

        // ---- MEMORY load: [dst_reg, MemAddr{base, disp}]. The dest class fixes
        //      the result width; FP loads use an XMM scalar dest. A representative
        //      base+disp=0 exercises the EA reconstruction (a wrong EA still
        //      refutes — see the reconstruction_x86 memory refutation tests). ----
        X86SourceOp::MemLoad { .. } => {
            // MovRMSib is the 64-bit SIB load `mov r64, [base+index*scale+disp]`:
            // a 64-bit dest and a SibMemAddr operand (scale=1/disp=0 is a valid
            // representative; a wrong EA still refutes). Plain-MemAddr loads keep
            // their opcode-fixed dest width and MemAddr operand.
            if matches!(
                opcode,
                X86Opcode::MovRMSib
                    | X86Opcode::MovRM32Sib
                    | X86Opcode::MovsdRMSib
                    | X86Opcode::MovssRMSib
                    | X86Opcode::MovRM8Sib
            ) {
                // The SIB loads share the SibMemAddr operand shape; only the
                // destination register class differs (GPR64 / GPR32 / XMM-f64 /
                // XMM-f32), and that is what fixes the load width.
                let dst = match opcode {
                    // I8/I16/I32 all map to Gpr32 (`reg_class_for_type`), so the
                    // 8-bit SIB load's dest VReg is a 32-bit GPR exactly as
                    // MovRM8's is; the LOAD WIDTH is fixed by the opcode, not by
                    // the register class.
                    X86Opcode::MovRM32Sib | X86Opcode::MovRM8Sib => r32(0),
                    X86Opcode::MovsdRMSib => xd(0),
                    X86Opcode::MovssRMSib => xs(0),
                    _ => r64(0),
                };
                return Some(X86ISelInst::new(
                    opcode,
                    vec![
                        dst,
                        X86ISelOperand::SibMemAddr {
                            base: Box::new(r64(1)),
                            index: Box::new(r64(2)),
                            scale: 1,
                            disp: 0,
                        },
                    ],
                ));
            }
            let dst = if matches!(opcode, X86Opcode::MovssRM) {
                xs(0)
            } else if matches!(opcode, X86Opcode::MovsdRM) {
                xd(0)
            } else if matches!(opcode, X86Opcode::MovRM) {
                r64(0)
            } else {
                // MovRM8/16/32: the dest VReg is a 32-bit GPR (reg_class_for_type
                // maps I8/I16/I32 -> Gpr32).
                r32(0)
            };
            vec![
                dst,
                X86ISelOperand::MemAddr {
                    base: Box::new(r64(1)),
                    disp: 0,
                },
            ]
        }
        // ---- MEMORY store: [MemAddr{base, disp}, value_reg]. ----
        X86SourceOp::MemStore { .. } => {
            // MovMRSib is the 64-bit SIB store `mov [base+index*scale+disp], r64`:
            // a SibMemAddr operand and a 64-bit value register.
            if matches!(
                opcode,
                X86Opcode::MovMRSib | X86Opcode::MovMR32Sib | X86Opcode::MovMR8Sib
            ) {
                // As for the loads: I8/I32 both live in a Gpr32 VReg, and the
                // STORE WIDTH is fixed by the opcode.
                let val = if matches!(opcode, X86Opcode::MovMR32Sib | X86Opcode::MovMR8Sib) {
                    r32(2)
                } else {
                    r64(2)
                };
                return Some(X86ISelInst::new(
                    opcode,
                    vec![
                        X86ISelOperand::SibMemAddr {
                            base: Box::new(r64(0)),
                            index: Box::new(r64(1)),
                            scale: 1,
                            disp: 0,
                        },
                        val,
                    ],
                ));
            }
            let value = if matches!(opcode, X86Opcode::MovssMR) {
                xs(1)
            } else if matches!(opcode, X86Opcode::MovsdMR) {
                xd(1)
            } else if matches!(opcode, X86Opcode::MovMR) {
                r64(1)
            } else {
                r32(1)
            };
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(r64(0)),
                    disp: 0,
                },
                value,
            ]
        }
        // ---- PACKED 128-bit XMM LOAD: [dst_xmm128, MemAddr{base, disp}]. The
        //      whole-XMM dest is a 128-bit Fpr128 VReg (the ISel-level class of a
        //      packed value); a representative base+disp=0 exercises the two-half
        //      EA reconstruction (a wrong EA / swapped half / wrong offset still
        //      refutes — see the reconstruction_x86 packed-move refutation tests). --
        X86SourceOp::V128MemLoad { .. } => {
            let x128 = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr128));
            vec![
                x128(0),
                X86ISelOperand::MemAddr {
                    base: Box::new(r64(1)),
                    disp: 0,
                },
            ]
        }
        // ---- PACKED 128-bit XMM STORE: [MemAddr{base, disp}, value_xmm128]. ----
        X86SourceOp::V128MemStore { .. } => {
            let x128 = |id: u32| X86ISelOperand::VReg(VReg::new(id, RegClass::Fpr128));
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(r64(0)),
                    disp: 0,
                },
                x128(1),
            ]
        }
        // ---- MEMORY-source ALU: [reg, MemAddr{base, disp}]. ----
        // ImulRMSib is the SIB member of the family: its representative must
        // carry a SibMemAddr (the pipeline's SIB-opcode integrity guard
        // rejects a MemAddr-shaped ImulRMSib), mirroring the MovRMSib
        // MemLoad special case above.
        X86SourceOp::MemAlu { .. } => {
            if matches!(opcode, X86Opcode::ImulRMSib) {
                return Some(X86ISelInst::new(
                    opcode,
                    vec![
                        r64(0),
                        X86ISelOperand::SibMemAddr {
                            base: Box::new(r64(1)),
                            index: Box::new(r64(2)),
                            scale: 1,
                            disp: 0,
                        },
                    ],
                ));
            }
            vec![
                r64(0),
                X86ISelOperand::MemAddr {
                    base: Box::new(r64(1)),
                    disp: 0,
                },
            ]
        }
        // ---- IN-PLACE Inc/Dec: [dst] (read-modify-write of one register). ----
        X86SourceOp::InPlaceIncDec { .. } => vec![r64(0)],

        // ---- DIVISION: [divisor_reg] (dividend/quotient/remainder are implicit
        //      RDX:RAX). A 32-bit divisor keeps the double-width 2W = 64 within the
        //      evaluator's native 64-bit fast path; 64-bit also works via the
        //      128-bit BvSDiv/BvUDiv evaluator. ----
        X86SourceOp::Division { .. } => vec![r32(0)],

        // ---- CONDITIONAL MOVE: [dst, src, CondCode]. dst is also the FALSE
        //      value (read-modify-write). The representative cc is E (equal); the
        //      gate additionally requires every emitted cc to discharge (see
        //      representative_reconstructable_insts). ----
        X86SourceOp::CondMove => vec![r64(0), r64(1), X86ISelOperand::CondCode(X86CondCode::E)],

        // Unary Neg/Not: [dst, src].
        _ if arity == X86AluArity::Unary => vec![r64(0), r64(1)],
        // RR shift form: [dst, src1] (count in implicit CL).
        _ if matches!(
            opcode,
            X86Opcode::ShlRR | X86Opcode::ShrRR | X86Opcode::SarRR
        ) =>
        {
            vec![r64(0), r64(1)]
        }
        // Binary register form: [dst, src1, src2].
        _ => vec![r64(0), r64(1), r64(2)],
    };
    Some(X86ISelInst::new(opcode, operands))
}

/// Representative reconstructable instances the COVERAGE GATE must verify for
/// `opcode`. For an ordinary opcode this is the single
/// [`representative_reconstructable_inst`]. For the MODE-POLYMORPHIC SSE4.1 round
/// opcodes (`Roundsd`/`Roundss`) it is ALL THREE emitted rounding modes
/// (floor=01, ceil=10, trunc=11): the gate sees only the opcode, so to credit it
/// COVERED every mode that the backend can emit must reconstruct-and-discharge —
/// no mode may ship silently unproven. (The round-to-nearest mode 00 is never
/// emitted and is deliberately NOT required.) The per-instruction walk verifies
/// each emitted ROUND with its actual imm8; this gate-level set is the
/// opcode-only coverage analogue.
fn representative_reconstructable_insts(opcode: X86Opcode) -> Vec<X86ISelInst> {
    use trust_cg_ir::regs::VReg;
    match opcode {
        X86Opcode::Roundsd | X86Opcode::Roundss => {
            let class = if opcode == X86Opcode::Roundss {
                RegClass::Fpr32
            } else {
                RegClass::Fpr64
            };
            let xfp = |id: u32| X86ISelOperand::VReg(VReg::new(id, class));
            [0b01_i64, 0b10, 0b11]
                .into_iter()
                .map(|imm8| {
                    X86ISelInst::new(opcode, vec![xfp(0), xfp(1), X86ISelOperand::Imm(imm8)])
                })
                .collect()
        }
        // CMOVcc is condition-POLYMORPHIC: each integer condition code is a
        // DISTINCT flag formula, so the gate must verify that EVERY value-select
        // cc discharges (not just the representative E). This forces a wrong cc
        // formula to be caught at the gate, not only in the targeted refutation
        // tests. The class fixes the operand width (Gpr64 for Cmovcc, Gpr32 for
        // Cmovcc32); a wrong-cc would diverge under `eval_int_condition`.
        X86Opcode::Cmovcc | X86Opcode::Cmovcc32 => {
            let class = if opcode == X86Opcode::Cmovcc32 {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            let reg = |id: u32| X86ISelOperand::VReg(VReg::new(id, class));
            [
                X86CondCode::E,
                X86CondCode::NE,
                X86CondCode::L,
                X86CondCode::GE,
                X86CondCode::G,
                X86CondCode::LE,
                X86CondCode::B,
                X86CondCode::AE,
                X86CondCode::A,
                X86CondCode::BE,
            ]
            .into_iter()
            .map(|cc| X86ISelInst::new(opcode, vec![reg(0), reg(1), X86ISelOperand::CondCode(cc)]))
            .collect()
        }
        _ => representative_reconstructable_inst(opcode)
            .into_iter()
            .collect(),
    }
}

/// Does the representative reconstructed obligation(s) for `opcode` discharge
/// `Valid` under `config`? Used by the COVERAGE GATE to CREDIT a reconstructable
/// x86-64 opcode as covered. Mirrors
/// `function_verifier::reconstruction_discharges_valid`.
///
/// Returns `false` (NOT covered) for any opcode that is not reconstructable, has
/// no representative instance, fails to reconstruct, is not tagged Reconstructed,
/// or whose reconstructed obligation does not discharge `Valid` — the exact dual
/// `is_reconstructed() && Valid` criterion the per-instruction walk uses. For the
/// mode-polymorphic round opcodes EVERY emitted mode must discharge (see
/// [`representative_reconstructable_insts`]).
pub fn reconstruction_discharges_valid(opcode: X86Opcode, config: &VerificationConfig) -> bool {
    let insts = representative_reconstructable_insts(opcode);
    if insts.is_empty() {
        return false;
    }
    insts.iter().all(|inst| {
        let Some(obligation) = reconstruct_alu_obligation(inst) else {
            return false;
        };
        // Routed through the shared CONTENT-keyed memo (PROOF-2): sound by
        // construction (the key embeds the full obligation, so representative
        // instances with different baked operands never share a verdict) and
        // skips re-sweeping the same representative obligation per compile.
        obligation.is_reconstructed()
            && matches!(
                crate::lowering_proof::memoized_verify_by_evaluation(&obligation, config),
                VerificationResult::Valid
            )
    })
}

// ---------------------------------------------------------------------------
// CT-7: shared big-stack pre-pass pool
// ---------------------------------------------------------------------------

/// Minimum instruction count before the per-instruction verdict PRE-PASS
/// fans out; below this, pool dispatch overhead exceeds the win and the
/// walk stays on the calling thread exactly as before.
const PREPASS_PAR_MIN_INSTS: usize = 16;

/// Stack size for the pre-pass worker threads. MUST match the dedicated
/// verifier-thread stack the callers already provide
/// (`run_on_proof_verifier_stack`, 32 MiB): per-instruction discharge
/// recurses over SMT expression trees, which overflows a default-size rayon
/// worker stack on deep obligations.
const PREPASS_STACK_SIZE: usize = 32 * 1024 * 1024;

/// The process-wide rayon pool for the per-instruction verdict pre-pass.
///
/// ONE shared pool (not per-call): the per-FUNCTION cert lane in
/// trust-cg-codegen already fans out across its own bounded pool, and every
/// one of those workers runs a pre-pass — a per-call pool would multiply
/// thread counts. `install` from multiple threads concurrently is supported
/// (their jobs interleave in the shared queue), so total pre-pass threads
/// stay bounded by this pool's size. Sized to the host's available
/// parallelism, bounded by an EXPLICIT `TRUST_CG_MAX_PARALLELISM` (the same
/// operator knob `trust_cg_codegen::resource_limits` honors; duplicated here
/// by name because trust-cg-verify sits BELOW trust-cg-codegen in the crate
/// graph). `None` when the host resolves to a single worker (fall back to
/// the sequential walk) or the pool fails to build (never fail a compile
/// over a thread-pool error — the serial walk is always available).
fn verifier_prepass_pool() -> Option<&'static rayon::ThreadPool> {
    static POOL: std::sync::OnceLock<Option<rayon::ThreadPool>> = std::sync::OnceLock::new();
    POOL.get_or_init(|| {
        let available = std::thread::available_parallelism().map_or(1, usize::from);
        let workers = match std::env::var("TRUST_CG_MAX_PARALLELISM")
            .ok()
            .as_deref()
            .and_then(|value| value.trim().parse::<usize>().ok())
            .filter(|value| *value > 0)
        {
            Some(explicit) => explicit.min(available).max(1),
            None => available,
        };
        if workers < 2 {
            return None;
        }
        rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .stack_size(PREPASS_STACK_SIZE)
            .thread_name(|idx| format!("trust-cg-x86-prepass-{idx}"))
            .build()
            .ok()
    })
    .as_ref()
}

/// The pre-pass pool IF fanning out `item_count` instructions is worthwhile.
///
/// BENCH-8: `None` (serial walk) when the opt-in reconstructed-obligation
/// LIVE solver route is armed — a fanned-out STAGE-2 discharge could
/// otherwise spawn z3 from multiple pool workers at once. This mirrors the
/// cert-lane posture in trust-cg-codegen (`compile_x86_64` keeps the
/// per-function lane serial when the route is armed); the default posture
/// (route OFF, or a solver-absent host such as the rustc bridge) is
/// unaffected.
fn verifier_prepass_pool_for_items(item_count: usize) -> Option<&'static rayon::ThreadPool> {
    if item_count < PREPASS_PAR_MIN_INSTS {
        return None;
    }
    if crate::verdict_db::reconstructed_live_solver_enabled() {
        return None;
    }
    verifier_prepass_pool()
}

// ---------------------------------------------------------------------------
// CT-8: three-stage per-instruction discharge (obligation descriptors)
// ---------------------------------------------------------------------------

/// CT-8 STAGE-1 output: one instruction's BASE-verdict plan, with obligation
/// CONSTRUCTION (pure, cheap) split from obligation DISCHARGE (the sweep /
/// tier-0 / DB work behind [`X86DischargeKey`]).
enum X86BaseVerdictPlan {
    /// The verdict needs no discharge at all: trap-skips, pseudos, and
    /// opcodes with no proof mapping.
    Ready(InstructionVerificationResult),
    /// The verdict is the discharge of `key` — computed once per DISTINCT
    /// key in STAGE 2, reused by every instruction that maps to it in
    /// STAGE 3.
    Discharge(X86DischargeKey),
}

/// CT-8: CONTENT key of one BASE-verdict discharge.
///
/// [`X86FunctionVerifier::discharge_key_verdict`] is a deterministic pure
/// function of `(&self, key)` — the key carries EVERYTHING the discharge
/// depends on besides the shared immutable verifier state (the
/// [`ProofDatabase`], the [`VerificationConfig`], the process-wide
/// compute-once verdict memo, and the committed tier-0 verdict DB) — so equal
/// keys are GUARANTEED equal verdicts and the STAGE-2 dedupe may discharge
/// each distinct key exactly once. `Eq`/`Hash` are structural (via
/// [`ProofObligation`]'s content-complete derives — the PROOF-2 memo-key
/// discipline): two keys differing anywhere in content occupy distinct
/// entries, so the dedupe can never conflate different obligations.
#[derive(PartialEq, Eq, Hash)]
enum X86DischargeKey {
    /// Static-DB path ([`X86FunctionVerifier::resolve_db_proof`]): resolve
    /// `(category, query)` against the immutable [`ProofDatabase`] and
    /// discharge the found row (or report Unverified on no match).
    Db {
        category: ProofCategory,
        query: String,
    },
    /// Reconstruction path (PHASE-2, task #66): discharge the RECONSTRUCTED
    /// `instance` obligation, preferring its PARAMETRIC `canonical` form for
    /// the tier-0 lookup (see
    /// `lowering_proof::discharge_reconstructed_obligation`). Boxed: the
    /// obligations are large relative to the `Db` arm.
    Recon {
        instance: Box<ProofObligation>,
        canonical: Box<ProofObligation>,
    },
}

// ---------------------------------------------------------------------------
// X86FunctionVerifier
// ---------------------------------------------------------------------------

/// Verifier that maps X86ISelFunction instructions to proof obligations.
pub struct X86FunctionVerifier {
    db: ProofDatabase,
    config: VerificationConfig,
}

impl X86FunctionVerifier {
    /// The proof categories this verifier can ever consult.
    ///
    /// Every `X86DischargeKey::Db` this verifier builds carries
    /// `ProofCategory::X8664Lowering` (see `x86_base_verdict_plan` and
    /// `resolve_db_proof`), so the other ~1300 obligations in a full
    /// `ProofDatabase` were constructed and never read. Building only these
    /// cuts the bridge's compile memory materially: `ProofDatabase::new()`
    /// materializes 1841 `SmtExpr` trees and is the bulk of the gap against
    /// LLVM (153 MB vs 70 MB; with proofs off the bridge is at parity, 71 MB).
    ///
    /// This is a MEMORY decision, not a verification one: `for_categories`
    /// yields the same obligations, in the same order, that `new()` would have
    /// for these categories — asserted per category by
    /// `for_categories_matches_full_database`. If this verifier ever needs
    /// another category, add it here; omitting one degrades an instruction to
    /// `Unverified` (fail closed), never to a false pass.
    const CONSULTED_CATEGORIES: &'static [ProofCategory] = &[ProofCategory::X8664Lowering];

    /// Create a new x86-64 function verifier with default configuration.
    pub fn new() -> Self {
        Self {
            db: ProofDatabase::for_categories(Self::CONSULTED_CATEGORIES),
            config: VerificationConfig::default(),
        }
    }

    /// Create a new x86-64 function verifier with a custom configuration.
    pub fn with_config(config: VerificationConfig) -> Self {
        Self {
            db: ProofDatabase::for_categories(Self::CONSULTED_CATEGORIES),
            config,
        }
    }

    /// Map an x86-64 opcode to a proof search substring.
    ///
    /// Returns `Some(name_substring)` for opcodes covered by
    /// [`crate::x86_64_lowering_proofs::all_x86_64_proofs`], or `None`
    /// for opcodes that have no registered lowering proof (e.g. `Jmp`,
    /// `Push`, `Pop`).
    ///
    /// The substring is matched (case-sensitive) against the proof
    /// obligation `name` field, which follows the canonical form
    /// `"x86_64: Iadd_I32 -> ADD r32,r32"` etc.
    ///
    /// Keying on the trust_ir operation (`Iadd_I`, `Isub_I`, …) rather than
    /// the x86 mnemonic lets a single opcode query match both 32- and
    /// 64-bit variants — the function verifier does not currently track
    /// per-instruction width, and the proof database carries both
    /// widths under the same `X8664Lowering` category.
    pub fn opcode_to_proof_query(opcode: X86Opcode) -> Option<&'static str> {
        use X86Opcode::*;
        match opcode {
            // Integer arithmetic
            AddRR | AddRI | AddRM | Inc => Some("Iadd_I"),
            SubRR | SubRI | SubRM | Dec => Some("Isub_I"),
            ImulRR | ImulRM | ImulRMSib => Some("Imul_I"),
            // 3-operand IMUL r,r/m,imm is WIDTH-POLYMORPHIC: the GEP path emits
            // it with a Gpr64 destination (IMUL r64), other paths with Gpr32.
            // The per-instruction verifier uses `width_polymorphic_extend_imul_
            // query` (keyed on the dst RegClass) for the width-correct proof;
            // this opcode-only string is just one representative width and is
            // consumed by the coverage gate, which requires BOTH the i32 and i64
            // IMUL-imm proofs to exist+discharge.
            ImulRRI => Some("Imul_I32_Imm"),
            Neg => Some("Neg_I"),

            // i128 carry-chain high limb. ADC computes `a_hi + b_hi + CF` and
            // SBB computes `a_hi - b_hi - borrow`, reading the flag the prior
            // low-half ADD/SUB set. Each binds to a faithful 65-bit
            // carry/borrow proof whose trust-ir spec is the high 64 bits of the
            // full 128-bit sum/difference (see x86_64_lowering_proofs
            // `proof_x86_adc_i128_hi` / `proof_x86_sbb_i128_hi`). The low limb
            // is the ordinary AddRR/SubRR, already mapped above.
            AdcRR => Some("Iadd_I128 hi -> ADC"),
            SbbRR => Some("Isub_I128 hi -> SBB"),

            // Division (signed / unsigned)
            Idiv => Some("Sdiv_I"),
            Div => Some("Udiv_I"),

            // Logical / bitwise
            AndRR | AndRI => Some("Band_I"),
            OrRR | OrRI => Some("Bor_I"),
            XorRR | XorRI => Some("Bxor_I"),
            Not => Some("Bnot_I"),

            // Shifts
            // ROL is grouped here because it shares the C1/D3 encoding family,
            // but it is NOT a shift: it wraps bits round instead of discarding
            // them, so it binds to its own `RotL_I*` proofs.
            RolRI => Some("RotL_I"),
            ShlRR | ShlRI => Some("Ishl_I"),
            ShrRR | ShrRI => Some("Ushr_I"),
            SarRR | SarRI => Some("Sshr_I"),

            // Compare (RFLAGS-setting; the comparison proofs cover the
            // CMP + Setcc/Jcc composition via the Icmp_* registry entries).
            CmpRR | CmpRI | CmpRI8 | CmpRM => Some("Icmp_"),
            TestRR | TestRI | TestRM => Some("Icmp_"),

            // Setcc consumes RFLAGS from a prior CMP; tie it to the
            // comparison proofs so the per-instruction walk records a
            // cert for the Setcc boolean materialization.
            Setcc => Some("Icmp_"),
            Cmovcc => Some("CMOVcc bitwise select"),
            Cmovcc32 => Some("CMOVcc32 bitwise select"),

            // Control transfer. These proofs cover the control target
            // component; ABI return placement, stack effects, unwind, and
            // relocation proof rows are tracked separately.
            //
            // DIRECT call only. A direct `Call` materializes its target via the
            // symbol-relocation lane (R_X86_64_PLT32 / BRANCH26), which is what
            // actually witnesses the branch target, so the per-instruction row
            // is legitimately backed elsewhere.
            // Direct call: its only mapped proof was the degenerate "CALL branches
            // to target" X==X (retracted in #62). No value-proof; FailClosedAllowlisted
            // in classify_x86 (the CFG edge + PLT32 reloc cover the target).
            Call => None,
            // INDIRECT calls (`CallR` = call-register, `CallM` = call-memory)
            // have NO named callee symbol to refine against — the address is a
            // runtime SSA value. The only per-instruction "proof" available is
            // the `target == target` tautology in
            // `x86_64_lowering_proofs::proof_x86_call_branches_to_target`, which
            // witnesses nothing about the branch target. Reporting that as
            // `Verified` is a forged label. We therefore report the indirect
            // forms `Unverified`, exactly mirroring the already-honest AArch64
            // posture (`opcode_to_proof_query(Blr) == None`). The real
            // indirect-call target-materialization (no-clobber of the operand
            // register through to the branch) is owned by the regalloc
            // translation-validator lane, not this per-instruction lane.
            CallR | CallM => None,
            // RET / JMP: their only mapped proofs were degenerate X==X (retracted
            // in #62). No value-proof; FailClosedAllowlisted in classify_x86.
            Ret => None,
            Jmp => None,
            // Jcc consumes RFLAGS from a prior CMP/TEST; the registered
            // Icmp_* composition proofs cover the CMP + Jcc condition
            // semantics, exactly as they do for Setcc below.
            Jcc => Some("Icmp_"),

            // Memory moves (loads/stores). Atomic-origin MOVs are routed to
            // the AtomicLoad/AtomicStore proofs by `proof_origin_to_proof_query`
            // BEFORE this opcode-level fallback fires, so these rows cover the
            // plain (non-atomic) effective-address load/store lowerings.
            MovRM8 => Some("Load_I8 -> MOV r8,[r64+disp32]"),
            MovRM16 => Some("Load_I16 -> MOV r16,[r64+disp32]"),
            MovRM32 => Some("Load_I32 -> MOV r32,[r64+disp32]"),
            MovRM => Some("Load_I64 -> MOV r64,[r64+disp32]"),
            MovMR8 => Some("Store_I8 -> MOV [r64+disp32],r8"),
            MovMR16 => Some("Store_I16 -> MOV [r64+disp32],r16"),
            MovMR32 => Some("Store_I32 -> MOV [r64+disp32],r32"),
            MovMR => Some("Store_I64 -> MOV [r64+disp32],r64"),

            // Plain LEA (base + disp): its only mapped proof was the degenerate
            // "base+disp32 -> LEA" effective-address X==X (retracted in #62). No
            // value-proof; FailClosedAllowlisted in classify_x86. (LeaSib/LeaRip
            // keep their genuine per-instance/relocation proofs.)
            Lea => None,

            // RIP-relative symbol-address materialization. Both opcodes only
            // ever take a `Symbol(name)` operand (see x86_64_isel
            // `select_global_ref` / `select_extern_ref`), so the opcode alone
            // determines the relocation provenance:
            //   LeaRip    -> Mach-O X86_64_RELOC_SIGNED / ELF R_X86_64_PC32
            //                (in-module symbol address S + A)
            //   MovRipRel -> Mach-O X86_64_RELOC_GOT_LOAD / ELF R_X86_64_GOTPCREL
            //                (GOT slot G + A holding &S; the load is opaque)
            // These proofs compose the per-instruction RIP-relative effective
            // address with the proven SIGNED/GOT_LOAD relocation displacements.
            LeaRip => Some("LeaRip Symbol -> RIP_next + SIGNED disp32 == S + A"),
            MovRipRel => Some("MovRipRel Symbol -> RIP_next + GOT_LOAD disp32 == G + A"),

            // SSE scalar floating point
            Addsd => Some("Fadd_F64"),
            Subsd => Some("Fsub_F64"),
            Mulsd => Some("Fmul_F64"),
            Divsd => Some("Fdiv_F64"),
            Addss => Some("Fadd_F32"),
            Subss => Some("Fsub_F32"),
            Mulss => Some("Fmul_F32"),
            Divss => Some("Fdiv_F32"),
            // Scalar square root (SQRTSD/SQRTSS), emitted for the sqrtf64/sqrtf32
            // intrinsic via Opcode::Fsqrt.
            Sqrtsd => Some("Fsqrt_F64"),
            Sqrtss => Some("Fsqrt_F32"),

            // Scalar min/max + UNORD compare-to-mask (Rust f{32,64}::min/max
            // NaN-away idiom). Each binds to the faithful per-instruction proof
            // that models the EXACT SDM hardware semantics (MINSD = src on
            // unordered/equal; CMPSD imm8=3 = isNaN mask) — NOT IEEE fp.min.
            // The surrounding NaN-away XOR-blend uses the proven PXOR/PAND.
            Minsd => Some("Fmin_F64 -> MINSD"),
            Maxsd => Some("Fmax_F64 -> MAXSD"),
            Minss => Some("Fmin_F32 -> MINSS"),
            Maxss => Some("Fmax_F32 -> MAXSS"),
            Cmpsd => Some("CMPSD_UNORD_F64"),
            Cmpss => Some("CMPSS_UNORD_F32"),

            // SSE/SSE2 packed floating-point arithmetic. Each ties to its
            // per-lane lowering proof registered by `all_x86_64_proofs`.
            Addps => Some("V4F32Fadd"),
            Subps => Some("V4F32Fsub"),
            Mulps => Some("V4F32Fmul"),
            Divps => Some("V4F32Fdiv"),
            Addpd => Some("V2F64Fadd"),
            Subpd => Some("V2F64Fsub"),
            Mulpd => Some("V2F64Fmul"),
            Divpd => Some("V2F64Fdiv"),

            // SSE scalar floating-point conversions (CVT* family). These tie
            // each conversion opcode to its modeled-vs-trust_ir equivalence
            // proof registered by `all_x86_64_fp_conversion_proofs`.
            Cvtsi2sd => Some("FcvtFromInt_F64"),
            Cvtsi2ss => Some("FcvtFromInt_F32"),
            Cvttsd2si => Some("FcvtToInt_I64_F64"),
            Cvttss2si => Some("FcvtToInt_I64_F32"),
            Cvtsd2si => Some("CVTSD2SI_RNE"),
            Cvtss2si => Some("CVTSS2SI_RNE"),
            Cvtsd2ss => Some("FPTrunc_F32_F64 -> CVTSD2SS"),
            Cvtss2sd => Some("FPExt_F64_F32 -> CVTSS2SD"),

            // SSE scalar FP COMPARE (UCOMISS/UCOMISD). A UCOMIS that is part of
            // a recognized UCOMIS+SETcc sequence is bound to the EXACT
            // condition-specific Fcmp proof by `fcmp_sequence_to_proof_query`
            // (which runs BEFORE this opcode-level fallback). A STANDALONE /
            // bare UCOMIS (feeding a Jcc branch, or a SETcc whose MOVZX shape
            // the sequence recognizer does not match) falls through to here. It
            // writes ZF/PF/CF from the unordered FP comparison; the registered
            // width-correct `Fcmp_*` composition proofs cover the UCOMIS+SETcc
            // condition semantics, EXACTLY as bare integer `CmpRR`/`Setcc`/`Jcc`
            // map to `Icmp_`. This is a faithful flag-compare cert (not a fake
            // tautology — the Fcmp proofs are real UCOMIS-flag equivalences); a
            // representative-condition Fcmp proof at the correct width is bound.
            Ucomiss => Some("Fcmp_Eq_F32 -> x86_64 UCOMISS"),
            Ucomisd => Some("Fcmp_Eq_F64 -> x86_64 UCOMISD"),

            // PXOR (128-bit bitwise XOR). Emitted in the scalar FP-NEG sign idiom
            // (`select_fneg`: `Pxor dst, src, sign_mask` flips the IEEE sign bit
            // — x86-64 has no scalar XORPS/XORPD), as well as XMM zeroing and the
            // vector lane. The registered `V128 Bxor -> PXOR` proof is a faithful
            // FULL-WIDTH bitwise-XOR identity (`encode_pxor` = 128-bit `a ^ b`);
            // because XOR is bitwise/lane-independent, this directly certifies the
            // scalar low-lane sign-flip (`src_low ^ mask_low`) AND the zeroing
            // form (`a ^ a == 0`). Not a fake tautology — a real XOR equivalence.
            Pxor => Some("V128 Bxor -> PXOR xmm,xmm"),

            // SSE2/SSE4.1 packed-integer family. Each opcode below binds to a
            // WIDTH/LANE-EXACT lowering proof registered by `all_x86_64_proofs`
            // whose ENTIRE machine-side expression is that single instruction —
            // never a different-width or multi-instruction proof. The bindings
            // (and the per-opcode soundness rationale) live in
            // `packed_to_proof_query`, the single source of truth shared with the
            // coverage gate. Opcodes WITHOUT a faithful single-instruction proof
            // (PANDN, the q-lane SSE4.1/4.2 compares, shuffle/pack/mask-extract/
            // multiply) are deliberately omitted here and stay allowlisted.
            Pand | Por | Paddb | Paddw | Paddd | Paddq | Psubb | Psubw | Psubd | Psubq
            | Pcmpeqb | Pcmpeqw | Pcmpeqd | Pcmpgtb | Pcmpgtw | Pcmpgtd | Pslld | Psrld | Psrad
            | Psllq | Psrlq | Pmuludq | Andpd | Andps => Self::packed_to_proof_query(opcode),

            // Bit-manipulation instructions (POPCNT/TZCNT/LZCNT/BSF/BSR). Each
            // ties to its modeled bitvector-semantics proof.
            Popcnt => Some("Ctpop_"),
            Tzcnt => Some("Cttz_I64 -> TZCNT"),
            Lzcnt => Some("Ctlz_I64 -> LZCNT"),
            Bsf => Some("Cttz_I64 (nonzero) -> BSF"),
            Bsr => Some("BSR_I64 (nonzero)"),

            // Zero / sign extension (MOVZX/MOVSX). The discharged proofs are
            // named "Uextend_I*_to_I*" / "Sextend_I*_to_I*" (the trust-ir
            // opcode), not "Movzx_*"/"Movsx_*".
            //
            // SOUNDNESS / WIDTH-POLYMORPHISM: the byte/word MOVSX/MOVZX opcodes
            // (`Movzx`, `MovzxW`, `MovsxB`, `MovsxW`) are emitted for BOTH a
            // 32-bit and a 64-bit destination, and the x86 encoder ALWAYS sets
            // REX.W for these forms (encode.rs -> `MOVSX/MOVZX r64`). The
            // opcode-only string below is a single REPRESENTATIVE width and is
            // NOT used by the per-instruction verifier for these opcodes — that
            // path uses `width_polymorphic_extend_imul_query`, which keys on the
            // destination RegClass and selects the width-correct proof. Both the
            // i32 AND i64 byte/word extends now live under
            // `ProofCategory::X8664Lowering` (the x86-specific REX.W
            // `proof_x86_mov{sx,zx}_{8,16}_to_{32,64}` proofs). The coverage gate
            // requires BOTH the i32 and i64 proofs. `Movsx` (MOVSXD) is the one
            // exception: it always encodes i32->i64, so its opcode-only
            // `Sextend_I32_to_I64` string is already width-correct.
            Movzx => Some("Uextend_I8"),
            MovzxW => Some("Uextend_I16_to_I32"),
            MovsxB => Some("Sextend_I8_to_I32"),
            MovsxW => Some("Sextend_I16_to_I32"),
            Movsx => Some("Sextend_I32_to_I64"),

            // MovRI: its only mapped proof was the degenerate "MOV r,imm
            // materializes constant" const==const X==X (retracted in #62). No
            // value-proof; FailClosedAllowlisted in classify_x86. (MovRR/MovRR32
            // keep their GENUINE bit-identity Copy proofs.)
            MovRI => None,
            MovRR => Some("Copy_I64 -> MOV r64,r64 preserves bits"),
            MovRR32 => Some("Copy_I32 -> MOV r32,r32 preserves bits"),

            // GPR <-> XMM scalar bit transfers used by FP select lowering.
            MovdToXmm => Some("MOVD xmm,r32 preserves bits"),
            MovdFromXmm => Some("MOVD r32,xmm preserves bits"),
            MovqToXmm => Some("MOVQ xmm,r64 preserves bits"),
            MovqFromXmm => Some("MOVQ r64,xmm preserves bits"),

            // SSE scalar-FP MOVE / COPY / load / store / constant-pool-load (#65).
            // MOVSS/MOVSD reg-reg copy is a scalar bit-IDENTITY; the memory
            // forms map to the f32/f64-width Load_F*/Store_F* memory proofs; the
            // RIP-relative forms map to the const-pool effective-address proof.
            // The Movss/Movsd width is fixed by the opcode (single vs double),
            // so the opcode alone determines the width-correct proof.
            MovssRR => Some("Copy_F32 -> MOVSS xmm,xmm preserves scalar bits"),
            MovsdRR => Some("Copy_F64 -> MOVSD xmm,xmm preserves scalar bits"),
            MovssRM => Some("Load_F32 -> MOVSS xmm,[r64+disp32]"),
            MovsdRM => Some("Load_F64 -> MOVSD xmm,[r64+disp32]"),
            MovssMR => Some("Store_F32 -> MOVSS [r64+disp32],xmm"),
            MovsdMR => Some("Store_F64 -> MOVSD [r64+disp32],xmm"),
            MovssRipRel => Some("MovssRipRel -> RIP_next + disp32 == C (f32 const-pool addr)"),
            MovsdRipRel => Some("MovsdRipRel -> RIP_next + disp32 == C (f64 const-pool addr)"),

            // Atomic RMW CAS-loop pseudos. The verifier uses the op-kind
            // immediate when present; these are representative fallback
            // queries for synthetic tests or malformed operand lists.
            AtomicRmwCasLoop => Some("AtomicRmwCasLoop_Add_I"),
            AtomicRmwCasLoop8 => Some("AtomicRmwCasLoop8_Add_I8"),
            AtomicRmwCasLoop16 => Some("AtomicRmwCasLoop16_Add_I16"),

            // Opcodes with no lowering-proof coverage yet: memory moves without
            // proof-origin metadata, stack manipulation, calls, branches, SSE
            // conversions, bit-manip, and xchg/cmpxchg. These land as
            // Unverified in the per-instruction report; a cert is not produced.
            _ => None,
        }
    }

    fn atomic_rmw_cas_loop_op_name(kind: i64) -> Option<&'static str> {
        match kind {
            0 => Some("Add"),
            1 => Some("Sub"),
            2 => Some("And"),
            3 => Some("Or"),
            4 => Some("Xor"),
            5 => Some("Xchg"),
            6 => Some("Max"),
            7 => Some("Min"),
            8 => Some("UMax"),
            9 => Some("UMin"),
            _ => None,
        }
    }

    fn atomic_rmw_cas_loop_generic_width(inst: &X86ISelInst) -> Option<&'static str> {
        let Some(X86ISelOperand::VReg(vreg)) = inst.operands.first() else {
            return None;
        };
        match vreg.class {
            RegClass::Gpr32 => Some("I32"),
            RegClass::Gpr64 => Some("I64"),
            _ => None,
        }
    }

    fn proof_origin_to_proof_query(inst: &X86ISelInst) -> Option<&'static str> {
        match (inst.proof_origin, inst.opcode) {
            (Some(X86ProofOrigin::AtomicLoad), X86Opcode::MovRM8) => Some("AtomicLoad_I8"),
            (Some(X86ProofOrigin::AtomicLoad), X86Opcode::MovRM16) => Some("AtomicLoad_I16"),
            (Some(X86ProofOrigin::AtomicLoad), X86Opcode::MovRM32) => Some("AtomicLoad_I32"),
            (Some(X86ProofOrigin::AtomicLoad), X86Opcode::MovRM) => Some("AtomicLoad_I64"),
            (Some(X86ProofOrigin::AtomicStore), X86Opcode::MovMR8) => Some("AtomicStore_I8"),
            (Some(X86ProofOrigin::AtomicStore), X86Opcode::MovMR16) => Some("AtomicStore_I16"),
            (Some(X86ProofOrigin::AtomicStore), X86Opcode::MovMR32) => Some("AtomicStore_I32"),
            (Some(X86ProofOrigin::AtomicStore), X86Opcode::MovMR) => Some("AtomicStore_I64"),
            // SLICE 3 (fences). The SeqCst fence lowers to MFENCE and binds a
            // GENUINE single-thread-identity proof: MFENCE writes no register and
            // no memory (`proof_x86_mfence_single_thread_identity`). This is a
            // real data-flow obligation over symbolic register/memory state, NOT
            // a #62 const==const tautology. Acquire/Release/AcqRel fences emit
            // ZERO instructions on x86 TSO, so they never reach here (nothing to
            // prove). The cross-thread ORDERING that MFENCE also provides is a
            // separate Intel-SDM architectural axiom, deliberately not an SMT
            // proof — see the coverage-gate reason string.
            (Some(X86ProofOrigin::FenceSeqCst), X86Opcode::Mfence) => {
                Some("x86_64: SeqCst fence -> MFENCE single-thread identity")
            }
            _ => None,
        }
    }

    fn is_register_operand(operand: &X86ISelOperand) -> bool {
        matches!(operand, X86ISelOperand::VReg(_) | X86ISelOperand::PReg(_))
    }

    fn lea_to_proof_query(inst: &X86ISelInst) -> Option<&'static str> {
        let X86Opcode::LeaSib = inst.opcode else {
            return None;
        };
        let [
            _,
            X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            },
        ] = inst.operands.as_slice()
        else {
            return None;
        };
        if !Self::is_register_operand(base) || !Self::is_register_operand(index) {
            return None;
        }

        // #62 retraction: the scaled (×2/4/8) and displaced (+disp32) SIB-LEA
        // effective-address proofs were degenerate X==X (the EA expression was the
        // SAME on both sides; no independent address-mode encoder) and were
        // removed. Only the no-scale, no-displacement "base+index -> LEA
        // r64,[r64+r64]" proof was GENUINE and remains; every other SIB-LEA shape
        // now has no value-proof (None -> Unverified), pending a faithful
        // independent effective-address encoder.
        if *disp == 0 && *scale == 1 {
            Some("base+index -> LEA r64,[r64+r64]")
        } else {
            None
        }
    }

    /// Map an SSE2/SSE4.1 packed-integer opcode to its WIDTH/LANE-EXACT lowering
    /// proof query. The single source of truth for the packed bindings; both the
    /// per-instruction verifier (`opcode_to_proof_query`) and the coverage gate
    /// (`coverage_gate::classify_x86` -> EmittableNeedsProof path) route through
    /// here, so a packed opcode can never be classified emittable yet bound to a
    /// mismatched proof.
    ///
    /// SOUNDNESS (the iron rule): every binding is to a registered proof whose
    /// ENTIRE machine-side expression is exactly the single named instruction at
    /// exactly the encoded element width/lane count. A wrong-width or
    /// multi-instruction proof is NEVER returned (that would let a miscompiled
    /// packed op pass against an unrelated obligation).
    ///
    ///   * Bitwise PAND/POR are full-width 128-bit `a & b` / `a | b`
    ///     (`encode_pand`/`encode_por`); the registered `V128 Band/Bor` proofs
    ///     model exactly that one instruction. (PXOR is bound separately above;
    ///     PANDN = `(~a) & b` has NO registered proof and stays allowlisted.)
    ///   * PADD{B,W,D,Q}/PSUB{B,W,D,Q} bind to the lane-exact add/sub proof for
    ///     the element width THAT opcode encodes — PADDW->i16x8, PADDD->i32x4,
    ///     PADDQ->i64x2, PADDB->i8x16 (and symmetrically PSUB) — whose entire
    ///     machine side is the single PADD/PSUB.
    ///   * PCMPEQ{B,W,D}/PCMPGT{B,W,D} bind to the lane-exact `Icmp_Eq`/`Icmp_Sgt`
    ///     compare-mask proof at that width. Those two conditions are the only
    ///     ones whose whole lowering IS the single PCMPEQ/PCMPGT (every other
    ///     IntCC composes extra PXOR/POR/swaps). PCMPEQ/PCMPGT ALWAYS compute the
    ///     per-lane equal / signed-greater mask of their two operands regardless
    ///     of surrounding context, so this is a faithful per-instruction
    ///     equivalence even when the instruction is a component of a larger
    ///     compare sequence (the all-ones idiom `PCMPEQD x,x` is likewise
    ///     certified — every lane equals itself). The SSE4.1/4.2 q-lane forms
    ///     (PCMPEQQ/PCMPGTQ) are out of the requested subset and stay allowlisted.
    ///   * PSLLD/PSRLD/PSRAD bind to the uniform-IMMEDIATE shift proof
    ///     (`encode_pslld_imm`/`encode_psrld_imm`/`encode_psrad_imm`). The x86
    ///     lowerer emits these opcodes ONLY with an `Imm` count
    ///     (`select_v4i32_shift_imm`); the variable-count path scalarizes to GPR
    ///     shifts instead, so the immediate proof is faithful for every emitted
    ///     instance.
    fn packed_to_proof_query(opcode: X86Opcode) -> Option<&'static str> {
        use X86Opcode::*;
        match opcode {
            // Full-width 128-bit bitwise (lane-independent). ANDPS/ANDPD are the
            // FP-domain encodings of the same 128-bit AND PAND computes; emitted
            // by `select_fabs` for the f32/f64 sign-mask-clear (fabs) idiom.
            Pand => Some("V128 Band -> PAND xmm,xmm"),
            Por => Some("V128 Bor -> POR xmm,xmm"),
            Andpd => Some("V128 Band -> ANDPD xmm,xmm"),
            Andps => Some("V128 Band -> ANDPS xmm,xmm"),

            // Lane-exact packed add / sub (element width fixed by the opcode).
            Paddb => Some("V16I8Add -> PADDB"),
            Paddw => Some("V8I16Add -> PADDW"),
            Paddd => Some("V4I32Add -> PADDD"),
            Paddq => Some("V2I64Add -> PADDQ"),
            Psubb => Some("V16I8Sub -> PSUBB"),
            Psubw => Some("V8I16Sub -> PSUBW"),
            Psubd => Some("V4I32Sub -> PSUBD"),
            Psubq => Some("V2I64Sub -> PSUBQ"),

            // Lane-exact packed equal / signed-greater compare masks. Only the
            // Eq / Sgt conditions are single-instruction lowerings.
            Pcmpeqb => Some("V16I8Icmp_Eq -> PCMPEQB"),
            Pcmpeqw => Some("V8I16Icmp_Eq -> PCMPEQW"),
            Pcmpeqd => Some("V4I32Icmp_Eq -> PCMPEQD"),
            Pcmpgtb => Some("V16I8Icmp_Sgt -> PCMPGTB"),
            Pcmpgtw => Some("V8I16Icmp_Sgt -> PCMPGTW"),
            Pcmpgtd => Some("V4I32Icmp_Sgt -> PCMPGTD"),

            // Uniform-immediate packed dword shifts (the only form emitted).
            Pslld => Some("V4I32 Ishl uniform immediate -> PSLLD"),
            Psrld => Some("V4I32 Ushr uniform immediate -> PSRLD"),
            Psrad => Some("V4I32 Sshr uniform immediate -> PSRAD"),

            // Uniform-immediate packed qword shifts (the only form emitted —
            // by the SSE2 vectorizer's packed 64-bit multiply compose).
            Psllq => Some("V2I64 Ishl uniform immediate -> PSLLQ"),
            Psrlq => Some("V2I64 Ushr uniform immediate -> PSRLQ"),

            // Even-dword widening unsigned multiply, faithfully modeled as the
            // same-width i64x2 lane op `lo32(a) * lo32(b)` (see
            // `proof_x86_v2i64_umul_lo32_pmuludq`).
            Pmuludq => Some("V2I64 even-dword widening Umul -> PMULUDQ"),

            // No faithful single-instruction proof: leave unbound (allowlisted).
            _ => None,
        }
    }

    fn low_mask(width: u32) -> u64 {
        if width >= 64 {
            u64::MAX
        } else {
            (1_u64 << width) - 1
        }
    }

    fn imm_operand(inst: &X86ISelInst, operand_idx: usize) -> Option<i64> {
        let Some(X86ISelOperand::Imm(value)) = inst.operands.get(operand_idx) else {
            return None;
        };
        Some(*value)
    }

    fn operand_eq(inst: &X86ISelInst, lhs_idx: usize, other: &X86ISelInst, rhs_idx: usize) -> bool {
        inst.operands.get(lhs_idx) == other.operands.get(rhs_idx)
    }

    fn matches_extract_bits_i32_sequence(insts: &[X86ISelInst], start: usize) -> bool {
        let Some([shift, mask, and]) = insts.get(start..start + 3) else {
            return false;
        };

        shift.opcode == X86Opcode::ShrRI
            && Self::imm_operand(shift, 2) == Some(i64::from(X86_BITFIELD_REPRESENTATIVE_LSB))
            && mask.opcode == X86Opcode::MovRI
            && Self::imm_operand(mask, 1).map(|imm| imm as u64)
                == Some(Self::low_mask(u32::from(X86_BITFIELD_REPRESENTATIVE_WIDTH)))
            && and.opcode == X86Opcode::AndRR
            && Self::operand_eq(and, 1, shift, 0)
            && Self::operand_eq(and, 2, mask, 0)
    }

    fn matches_sextract_bits_i32_sequence(insts: &[X86ISelInst], start: usize) -> bool {
        let Some([shift_left, shift_right]) = insts.get(start..start + 2) else {
            return false;
        };

        let field_end = u32::from(X86_BITFIELD_REPRESENTATIVE_LSB)
            + u32::from(X86_BITFIELD_REPRESENTATIVE_WIDTH);
        let left = X86_BITFIELD_REPRESENTATIVE_TYPE_BITS - field_end;
        let right =
            X86_BITFIELD_REPRESENTATIVE_TYPE_BITS - u32::from(X86_BITFIELD_REPRESENTATIVE_WIDTH);

        shift_left.opcode == X86Opcode::ShlRI
            && Self::imm_operand(shift_left, 2) == Some(i64::from(left))
            && shift_right.opcode == X86Opcode::SarRI
            && Self::imm_operand(shift_right, 2) == Some(i64::from(right))
            && Self::operand_eq(shift_right, 1, shift_left, 0)
    }

    fn matches_insert_bits_i32_sequence(insts: &[X86ISelInst], start: usize) -> bool {
        let Some(
            [
                clear_mask,
                preserved,
                low_mask,
                insert_low,
                inserted,
                result,
            ],
        ) = insts.get(start..start + 6)
        else {
            return false;
        };

        let low_mask_value = Self::low_mask(u32::from(X86_BITFIELD_REPRESENTATIVE_WIDTH));
        let type_mask = Self::low_mask(X86_BITFIELD_REPRESENTATIVE_TYPE_BITS);
        let field_mask = low_mask_value << u32::from(X86_BITFIELD_REPRESENTATIVE_LSB);
        let clear_mask_value = type_mask & !field_mask;

        clear_mask.opcode == X86Opcode::MovRI
            && Self::imm_operand(clear_mask, 1).map(|imm| imm as u64) == Some(clear_mask_value)
            && preserved.opcode == X86Opcode::AndRR
            && Self::operand_eq(preserved, 2, clear_mask, 0)
            && low_mask.opcode == X86Opcode::MovRI
            && Self::imm_operand(low_mask, 1).map(|imm| imm as u64) == Some(low_mask_value)
            && insert_low.opcode == X86Opcode::AndRR
            && Self::operand_eq(insert_low, 2, low_mask, 0)
            && inserted.opcode == X86Opcode::ShlRI
            && Self::imm_operand(inserted, 2) == Some(i64::from(X86_BITFIELD_REPRESENTATIVE_LSB))
            && Self::operand_eq(inserted, 1, insert_low, 0)
            && result.opcode == X86Opcode::OrRR
            && Self::operand_eq(result, 1, preserved, 0)
            && Self::operand_eq(result, 2, inserted, 0)
    }

    fn sequence_contains(start: usize, len: usize, inst_idx: usize) -> bool {
        start <= inst_idx && inst_idx < start + len
    }

    /// Return the representative x86 bitfield proof query for a lowered
    /// instruction sequence containing `inst_idx`.
    ///
    /// This deliberately recognizes only the L68 representative i32 window.
    /// Other bitfield windows continue to fall back to per-opcode component
    /// proofs until the verifier carries enough typed bitfield metadata to
    /// choose a width/window-specific whole-pattern proof.
    pub fn bitfield_sequence_to_proof_query(
        insts: &[X86ISelInst],
        inst_idx: usize,
    ) -> Option<&'static str> {
        if inst_idx >= insts.len() {
            return None;
        }

        let min_start = inst_idx.saturating_sub(5);
        for start in min_start..=inst_idx {
            if Self::sequence_contains(start, 6, inst_idx)
                && Self::matches_insert_bits_i32_sequence(insts, start)
            {
                return Some(X86_INSERT_BITS_I32_PROOF_QUERY);
            }
            if Self::sequence_contains(start, 3, inst_idx)
                && Self::matches_extract_bits_i32_sequence(insts, start)
            {
                return Some(X86_EXTRACT_BITS_I32_PROOF_QUERY);
            }
            if Self::sequence_contains(start, 2, inst_idx)
                && Self::matches_sextract_bits_i32_sequence(insts, start)
            {
                return Some(X86_SEXTRACT_BITS_I32_PROOF_QUERY);
            }
        }

        None
    }

    fn has_registered_x86_proof(&self, query: &str) -> bool {
        self.db
            .by_category(ProofCategory::X8664Lowering)
            .iter()
            .any(|p| p.obligation.name.contains(query))
    }

    fn registered_bitfield_sequence_proof_query(
        &self,
        insts: &[X86ISelInst],
        inst_idx: usize,
    ) -> Option<&'static str> {
        let query = Self::bitfield_sequence_to_proof_query(insts, inst_idx)?;
        self.has_registered_x86_proof(query).then_some(query)
    }

    fn fcmp_ty_suffix(opcode: X86Opcode) -> Option<&'static str> {
        match opcode {
            X86Opcode::Ucomiss => Some("F32"),
            X86Opcode::Ucomisd => Some("F64"),
            _ => None,
        }
    }

    fn setcc_cond(inst: &X86ISelInst) -> Option<X86CondCode> {
        if inst.opcode != X86Opcode::Setcc {
            return None;
        }
        let Some(X86ISelOperand::CondCode(cc)) = inst.operands.get(1) else {
            return None;
        };
        Some(*cc)
    }

    fn single_fcmp_name(cc: X86CondCode) -> Option<&'static str> {
        match cc {
            X86CondCode::NE => Some("NE"),
            X86CondCode::A => Some("GT"),
            X86CondCode::AE => Some("GE"),
            X86CondCode::NP => Some("Ord"),
            X86CondCode::P => Some("Uno"),
            X86CondCode::B => Some("ULT"),
            X86CondCode::BE => Some("ULE"),
            _ => None,
        }
    }

    fn ordered_fcmp_name(cc: X86CondCode) -> Option<&'static str> {
        match cc {
            X86CondCode::E => Some("Eq"),
            X86CondCode::B => Some("LT"),
            X86CondCode::BE => Some("LE"),
            _ => None,
        }
    }

    fn unordered_or_fcmp_name(cc: X86CondCode) -> Option<&'static str> {
        match cc {
            X86CondCode::E => Some("UEQ"),
            X86CondCode::NE => Some("UNE"),
            X86CondCode::A => Some("UGT"),
            X86CondCode::AE => Some("UGE"),
            _ => None,
        }
    }

    fn fcmp_query_for_sequence_at(insts: &[X86ISelInst], start: usize) -> Option<(usize, String)> {
        let cmp = insts.get(start)?;
        let ty = Self::fcmp_ty_suffix(cmp.opcode)?;

        if let Some([set_main, mov_main, set_parity, mov_parity, combine]) =
            insts.get(start + 1..start + 6)
            && let (Some(main_cc), Some(parity_cc)) =
                (Self::setcc_cond(set_main), Self::setcc_cond(set_parity))
        {
            let main_mov_matches = mov_main.opcode == X86Opcode::Movzx
                && Self::operand_eq(mov_main, 0, set_main, 0)
                && Self::operand_eq(mov_main, 1, set_main, 0);
            let parity_mov_matches = mov_parity.opcode == X86Opcode::Movzx
                && Self::operand_eq(mov_parity, 0, set_parity, 0)
                && Self::operand_eq(mov_parity, 1, set_parity, 0);
            let combine_matches = Self::operand_eq(combine, 0, set_main, 0)
                && Self::operand_eq(combine, 1, set_main, 0)
                && Self::operand_eq(combine, 2, set_parity, 0);

            if main_mov_matches
                && parity_mov_matches
                && combine_matches
                && combine.opcode == X86Opcode::AndRR
                && parity_cc == X86CondCode::NP
            {
                let name = Self::ordered_fcmp_name(main_cc)?;
                return Some((6, format!("Fcmp_{name}_{ty}")));
            }

            if main_mov_matches
                && parity_mov_matches
                && combine_matches
                && combine.opcode == X86Opcode::OrRR
                && parity_cc == X86CondCode::P
            {
                let name = Self::unordered_or_fcmp_name(main_cc)?;
                return Some((6, format!("Fcmp_{name}_{ty}")));
            }
        }

        let Some([set_main, mov_main]) = insts.get(start + 1..start + 3) else {
            return None;
        };
        let main_cc = Self::setcc_cond(set_main)?;
        if mov_main.opcode == X86Opcode::Movzx
            && Self::operand_eq(mov_main, 0, set_main, 0)
            && Self::operand_eq(mov_main, 1, set_main, 0)
        {
            let name = Self::single_fcmp_name(main_cc)?;
            return Some((3, format!("Fcmp_{name}_{ty}")));
        }

        None
    }

    /// Return the x86 FP-compare proof query for an emitted
    /// `UCOMIS{S,D} + SETcc` sequence containing `inst_idx`.
    pub fn fcmp_sequence_to_proof_query(insts: &[X86ISelInst], inst_idx: usize) -> Option<String> {
        if inst_idx >= insts.len() {
            return None;
        }

        let min_start = inst_idx.saturating_sub(5);
        for start in min_start..=inst_idx {
            let Some((len, query)) = Self::fcmp_query_for_sequence_at(insts, start) else {
                continue;
            };
            if Self::sequence_contains(start, len, inst_idx) {
                return Some(query);
            }
        }

        None
    }

    fn division_result_query(
        opcode: X86Opcode,
        copy_opcode: X86Opcode,
        result: &X86ISelOperand,
    ) -> Option<&'static str> {
        match (opcode, copy_opcode, result) {
            (X86Opcode::Idiv, X86Opcode::MovRR, X86ISelOperand::PReg(RAX)) => Some("Sdiv_I64"),
            (X86Opcode::Idiv, X86Opcode::MovRR32, X86ISelOperand::PReg(EAX)) => Some("Sdiv_I32"),
            (X86Opcode::Idiv, X86Opcode::MovRR, X86ISelOperand::PReg(RDX)) => Some("Srem_I64"),
            (X86Opcode::Idiv, X86Opcode::MovRR32, X86ISelOperand::PReg(EDX)) => Some("Srem_I32"),
            (X86Opcode::Div, X86Opcode::MovRR, X86ISelOperand::PReg(RAX)) => Some("Udiv_I64"),
            (X86Opcode::Div, X86Opcode::MovRR32, X86ISelOperand::PReg(EAX)) => Some("Udiv_I32"),
            (X86Opcode::Div, X86Opcode::MovRR, X86ISelOperand::PReg(RDX)) => Some("Urem_I64"),
            (X86Opcode::Div, X86Opcode::MovRR32, X86ISelOperand::PReg(EDX)) => Some("Urem_I32"),
            _ => None,
        }
    }

    fn division_setup_matches(
        copy_in: &X86ISelInst,
        setup: &X86ISelInst,
        div_opcode: X86Opcode,
        copy_opcode: X86Opcode,
    ) -> bool {
        let acc = match copy_opcode {
            X86Opcode::MovRR => RAX,
            X86Opcode::MovRR32 => EAX,
            _ => return false,
        };
        let rem = match copy_opcode {
            X86Opcode::MovRR => RDX,
            X86Opcode::MovRR32 => EDX,
            _ => return false,
        };

        if copy_in.opcode != copy_opcode
            || copy_in.operands.first() != Some(&X86ISelOperand::PReg(acc))
        {
            return false;
        }

        match div_opcode {
            X86Opcode::Idiv => {
                setup.operands.is_empty()
                    && setup.opcode
                        == match copy_opcode {
                            X86Opcode::MovRR => X86Opcode::Cqo,
                            X86Opcode::MovRR32 => X86Opcode::Cdq,
                            _ => return false,
                        }
            }
            X86Opcode::Div => {
                setup.opcode == X86Opcode::XorRR
                    && setup.operands.as_slice()
                        == [
                            X86ISelOperand::PReg(rem),
                            X86ISelOperand::PReg(rem),
                            X86ISelOperand::PReg(rem),
                        ]
            }
            _ => false,
        }
    }

    fn division_query_for_sequence_at(
        insts: &[X86ISelInst],
        start: usize,
    ) -> Option<(usize, String)> {
        let copy_in = insts.get(start)?;
        let setup = insts.get(start + 1)?;
        let div = insts.get(start + 2)?;
        let copy_out = insts.get(start + 3)?;
        if !matches!(div.opcode, X86Opcode::Idiv | X86Opcode::Div) {
            return None;
        }
        if !matches!(copy_out.opcode, X86Opcode::MovRR | X86Opcode::MovRR32) {
            return None;
        }
        if !Self::division_setup_matches(copy_in, setup, div.opcode, copy_out.opcode) {
            return None;
        }
        let result_reg = copy_out.operands.get(1)?;
        let query = Self::division_result_query(div.opcode, copy_out.opcode, result_reg)?;
        Some((4, query.to_string()))
    }

    /// Return the quotient or remainder proof query for a lowered x86
    /// `DIV`/`IDIV` sequence containing `inst_idx`.
    ///
    /// This only binds certificates for the complete ISel sequence that sets
    /// up the implicit dividend registers matching the proof model.
    pub fn division_sequence_to_proof_query(
        insts: &[X86ISelInst],
        inst_idx: usize,
    ) -> Option<String> {
        if inst_idx >= insts.len() {
            return None;
        }

        let min_start = inst_idx.saturating_sub(3);
        for start in min_start..=inst_idx {
            let Some((len, query)) = Self::division_query_for_sequence_at(insts, start) else {
                continue;
            };
            if Self::sequence_contains(start, len, inst_idx) {
                return Some(query);
            }
        }

        None
    }

    /// Map an individual x86-64 instruction to the best proof search substring.
    ///
    /// Most opcodes only need the opcode-level mapping. `AtomicRmwCasLoop*`
    /// pseudos carry the trust_ir RMW operation as operand 3, so reading the
    /// immediate here lets proof reports distinguish Add/Sub/And/Or/Xor/Xchg.
    pub fn instruction_to_proof_query(inst: &X86ISelInst) -> Option<String> {
        if let Some(query) = Self::proof_origin_to_proof_query(inst) {
            return Some(query.to_string());
        }
        // FAIL CLOSED on mismatched provenance: an instruction TAGGED with a
        // proof origin must bind through that origin's proof table above. If
        // it did not (e.g. an `AtomicLoad` origin on a store opcode), the
        // lowering's own provenance is inconsistent — falling through to the
        // plain opcode-level mapping below would hand a mis-tagged atomic
        // access an ordinary load/store cert and mask the inconsistency.
        if inst.proof_origin.is_some() {
            return None;
        }
        if let Some(query) = Self::lea_to_proof_query(inst) {
            return Some(query.to_string());
        }

        // SETcc materializing a parity condition consumes PF, not the
        // signed/unsigned comparison flags. Route P/NP to the dedicated parity
        // proofs so the per-instruction cert reflects the real PF semantics.
        if let Some(cc) = Self::setcc_cond(inst) {
            match cc {
                X86CondCode::P => return Some("CMP+SETcc_P_I32".to_string()),
                X86CondCode::NP => return Some("CMP+SETcc_NP_I32".to_string()),
                _ => {}
            }
        }

        match inst.opcode {
            X86Opcode::AtomicRmwCasLoop
            | X86Opcode::AtomicRmwCasLoop8
            | X86Opcode::AtomicRmwCasLoop16 => {
                let Some(X86ISelOperand::Imm(kind)) = inst.operands.get(3) else {
                    return Self::opcode_to_proof_query(inst.opcode).map(str::to_string);
                };
                let Some(op_name) = Self::atomic_rmw_cas_loop_op_name(*kind) else {
                    return Self::opcode_to_proof_query(inst.opcode).map(str::to_string);
                };
                let query = match inst.opcode {
                    X86Opcode::AtomicRmwCasLoop => {
                        if let Some(width) = Self::atomic_rmw_cas_loop_generic_width(inst) {
                            format!("AtomicRmwCasLoop_{op_name}_{width}")
                        } else {
                            format!("AtomicRmwCasLoop_{op_name}_I")
                        }
                    }
                    X86Opcode::AtomicRmwCasLoop8 => {
                        format!("AtomicRmwCasLoop8_{op_name}_I8")
                    }
                    X86Opcode::AtomicRmwCasLoop16 => {
                        format!("AtomicRmwCasLoop16_{op_name}_I16")
                    }
                    _ => unreachable!(),
                };
                Some(query)
            }
            // LOCK CMPXCHG (compare_exchange) [slice 4] is WIDTH-POLYMORPHIC: the
            // source (desired) register class picks i32/i64. `select_cmpxchg`
            // emits `Cmpxchg desired_reg, [addr]`, so operand 0's class is the
            // width. Bind the width-correct REPRESENTATIVE proof — the "returns
            // old value" obligation (the instruction's result IS the old value in
            // RAX, exactly as the CAS-loop binds its returns-old proof). The
            // conditional-store and success-flag facets are ALSO gate-required at
            // both widths (see `x86_width_polymorphic_proofs`), so no facet ships
            // unproven. If the width cannot be resolved, stay Unverified (fail
            // closed) rather than guess a width.
            X86Opcode::Cmpxchg => {
                let width = Self::atomic_rmw_cas_loop_generic_width(inst)?;
                Some(format!("Cmpxchg_{width} returns old value"))
            }
            // Width-polymorphic byte/word MOVSX/MOVZX and 3-operand IMUL must
            // NOT fall back to the opcode-level (fixed i32-width) query: the
            // encoded width is determined by the destination register, and a
            // fixed-width binding would re-introduce the i32-proof-for-i64-op
            // unsoundness this fix removes. `width_polymorphic_extend_imul_query`
            // is the authoritative path (it disambiguates by dst class); if that
            // could not resolve a width here, the instruction stays Unverified
            // (fail closed) rather than bind a guessed width.
            X86Opcode::Movzx
            | X86Opcode::MovzxW
            | X86Opcode::MovsxB
            | X86Opcode::MovsxW
            | X86Opcode::ImulRRI => {
                Self::width_polymorphic_extend_imul_query(inst).map(|(_, query)| query.to_string())
            }
            // BtRI is width+bit-polymorphic: bind the EXACT (width, k) BT-CF
            // proof from the instruction's register class + immediate. No fixed
            // opcode-level fallback (that would verify a different bit/width).
            X86Opcode::BtRI => Self::bt_to_proof_query(inst),
            // One-operand widening MUL is width-polymorphic (Gpr32/Gpr64 source);
            // bind the width-correct low-half (value) proof.
            X86Opcode::Mul => Self::mul_to_proof_query(inst),
            // SSE4.1 scalar round-to-integral is MODE-polymorphic: the SAME
            // ROUNDSD/ROUNDSS opcode realizes floor/ceil/trunc via the imm8[1:0]
            // rounding-select. Bind the EXACT (width, mode) proof from the
            // opcode (Roundss=F32, Roundsd=F64) and the immediate. No fixed
            // opcode-level fallback — that would certify a different rounding
            // direction than the one the instruction actually encodes.
            X86Opcode::Roundsd | X86Opcode::Roundss => Self::round_to_proof_query(inst),
            _ => Self::opcode_to_proof_query(inst.opcode).map(str::to_string),
        }
    }

    /// Bind the width-and-mode-correct round-to-integral proof for a ROUNDSD/
    /// ROUNDSS instruction. The proof name distinguishes the trust_ir op
    /// (`FFloor`/`FCeil`/`FTrunc`) and the FP width (`_F32`/`_F64`), matching the
    /// proofs registered by `all_x86_64_proofs`. The mode comes from imm8[1:0]
    /// (01=floor, 10=ceil, 11=trunc); the round-to-nearest mode (00) is never
    /// emitted by the backend, so it fails closed (returns None -> Unverified).
    fn round_to_proof_query(inst: &X86ISelInst) -> Option<String> {
        let width = match inst.opcode {
            X86Opcode::Roundss => "F32",
            X86Opcode::Roundsd => "F64",
            _ => return None,
        };
        // imm8 is the third ISel operand: [dst, src, Imm(imm8)].
        let imm = Self::imm_operand(inst, 2)?;
        let op = match imm & 0b11 {
            0b01 => "FFloor",
            0b10 => "FCeil",
            0b11 => "FTrunc",
            // 0b00 = round-to-nearest: not emitted by the backend. Fail closed.
            _ => return None,
        };
        Some(format!("{op}_{width}"))
    }

    /// Destination [`RegClass`] of an instruction's first operand, when it is a
    /// register. Used to disambiguate width-polymorphic opcodes (MOVSX/MOVZX,
    /// 3-operand IMUL) whose encoded width is determined by the destination.
    fn dst_reg_class(inst: &X86ISelInst) -> Option<RegClass> {
        match inst.operands.first()? {
            X86ISelOperand::VReg(vreg) => Some(vreg.class),
            X86ISelOperand::PReg(preg) => {
                if preg.is_gpr64() {
                    Some(RegClass::Gpr64)
                } else if preg.is_gpr32() {
                    Some(RegClass::Gpr32)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Return the i128 carry-chain proof query for an emitted ADD+ADC / SUB+SBB
    /// 128-bit add/sub sequence containing `inst_idx`.
    ///
    /// SOUNDNESS: the carry/borrow flag from the low-half `ADD`/`SUB` is consumed
    /// by the high-half `ADC`/`SBB` through the IMPLICIT EFLAGS.CF, so the two
    /// instructions must be ADJACENT (no intervening flag-clobbering instruction
    /// may sit between them). The recognizer therefore matches ONLY a window
    /// where `ADC` (resp. `SBB`) immediately follows `ADD` (resp. `SUB`) at
    /// `start`/`start+1`. The composition proof (`encode_add_adc_i128` /
    /// `encode_sub_sbb_i128`) models the whole 2-instruction value, so binding it
    /// to both members of the adjacent pair is exactly the obligation those
    /// instructions discharge. A standalone `ADD`/`SUB` (plain i64 arithmetic)
    /// does NOT match — its successor is not the matching carry opcode — so it
    /// keeps its ordinary reconstructed `Iadd`/`Isub` cert via the operand-
    /// reconstruction path. A standalone `ADC`/`SBB` not preceded by the matching
    /// `ADD`/`SUB` does not match either and stays Unverified (fail closed) rather
    /// than receiving an unjustified carry-chain cert.
    pub fn i128_carry_chain_sequence_to_proof_query(
        insts: &[X86ISelInst],
        inst_idx: usize,
    ) -> Option<String> {
        if inst_idx >= insts.len() {
            return None;
        }
        // The pair is two instructions; inst_idx is either the low op (start) or
        // the high carry op (start + 1). Try both candidate starts.
        let min_start = inst_idx.saturating_sub(1);
        for start in min_start..=inst_idx {
            let Some(query) = Self::i128_carry_chain_query_for_pair_at(insts, start) else {
                continue;
            };
            if Self::sequence_contains(start, 2, inst_idx) {
                return Some(query);
            }
        }
        None
    }

    /// If `insts[start]` / `insts[start + 1]` form an i128 carry-chain pair
    /// (`ADD`+`ADC` or `SUB`+`SBB`, both register-register), return its proof
    /// query. The opcode of the second instruction must be the carry partner of
    /// the first, and both destinations must be GPR64 registers (the low and high
    /// halves of the i128 pair). The returned query substring matches the
    /// registered composition proof names
    /// (`x86_64: Iadd_I128 -> ADD lo; ADC hi` / `... Isub_I128 -> SUB lo; SBB hi`).
    fn i128_carry_chain_query_for_pair_at(insts: &[X86ISelInst], start: usize) -> Option<String> {
        let low = insts.get(start)?;
        let high = insts.get(start + 1)?;
        let query = match (low.opcode, high.opcode) {
            (X86Opcode::AddRR, X86Opcode::AdcRR) => "Iadd_I128 -> ADD lo; ADC hi",
            (X86Opcode::SubRR, X86Opcode::SbbRR) => "Isub_I128 -> SUB lo; SBB hi",
            _ => return None,
        };
        // Both halves must be 64-bit register destinations (the i128 GPR pair).
        let low_dst = Self::dst_reg_class(low)?;
        let high_dst = Self::dst_reg_class(high)?;
        if low_dst != RegClass::Gpr64 || high_dst != RegClass::Gpr64 {
            return None;
        }
        Some(query.to_string())
    }

    /// SOUNDNESS: MOVSX/MOVZX byte/word and 3-operand IMUL are *width-
    /// polymorphic* — the SAME opcode is emitted for both a 32-bit and a 64-bit
    /// destination, and the x86 encoder ALWAYS sets REX.W for the byte/word
    /// MOVSX/MOVZX forms (encode.rs `MovsxB`/`MovsxW`/`MovzxW`/`Movzx` ->
    /// `MOVSX/MOVZX r64`, and `ImulRRI` -> `IMUL r64` in the GEP path). A fixed
    /// i32 query (the previous `Sextend_I8_to_I32` / `Imul_I32_Imm`) therefore
    /// verified a DIFFERENT operation than the one encoded: an i64-MOVSX/IMUL
    /// bug would pass against an i32 proof. The verifier HAS the instruction, so
    /// it disambiguates by the destination register class and selects the proof
    /// for the width that is actually encoded.
    ///
    /// All byte/word MOVSX/MOVZX widths — including the REX.W r64 forms — now
    /// bind x86-specific proofs under [`ProofCategory::X8664Lowering`]
    /// (`proof_x86_mov{sx,zx}_{8,16}_to_{32,64}` in `x86_64_lowering_proofs`,
    /// modeled directly against `encode_movsx`/`encode_movzx` with the encoded
    /// `to_width`). Previously the i64 byte/word forms were attributed to the
    /// AArch64-mnemonic [`ProofCategory::ExtensionTruncation`] rows (SXTB/UXTH);
    /// the dedicated X8664Lowering proofs replace that so the discharged proof is
    /// x86-specific and width-correct. The returned category is therefore always
    /// `X8664Lowering` for these extends.
    fn width_polymorphic_extend_imul_query(
        inst: &X86ISelInst,
    ) -> Option<(ProofCategory, &'static str)> {
        let class = Self::dst_reg_class(inst)?;
        let is64 = match class {
            RegClass::Gpr64 => true,
            RegClass::Gpr32 => false,
            // Unknown destination width: fail closed (no width-correct binding).
            _ => return None,
        };
        match inst.opcode {
            // MOVZX r{32,64}, r/m8. Both widths are x86-specific REX.W r64 /
            // r32 MOVZX proofs under X8664Lowering (proof_x86_movzx_8_to_{32,64}).
            X86Opcode::Movzx => Some(if is64 {
                (ProofCategory::X8664Lowering, "Uextend_I8_to_I64")
            } else {
                (ProofCategory::X8664Lowering, "Uextend_I8_to_I32")
            }),
            // MOVZX r{32,64}, r/m16. The i64 form now has an x86-specific
            // `-> MOVZX r64,r/m16` proof under X8664Lowering
            // (proof_x86_movzx_16_to_64), so bind that instead of the
            // AArch64-mnemonic ExtensionTruncation row.
            X86Opcode::MovzxW => Some(if is64 {
                (ProofCategory::X8664Lowering, "Uextend_I16_to_I64")
            } else {
                (ProofCategory::X8664Lowering, "Uextend_I16_to_I32")
            }),
            // MOVSX r{32,64}, r/m8. The i64 form now has an x86-specific
            // `-> MOVSX r64,r/m8` proof under X8664Lowering
            // (proof_x86_movsx_8_to_64).
            X86Opcode::MovsxB => Some(if is64 {
                (ProofCategory::X8664Lowering, "Sextend_I8_to_I64")
            } else {
                (ProofCategory::X8664Lowering, "Sextend_I8_to_I32")
            }),
            // MOVSX r{32,64}, r/m16. The i64 form now has an x86-specific
            // `-> MOVSX r64,r/m16` proof under X8664Lowering
            // (proof_x86_movsx_16_to_64).
            X86Opcode::MovsxW => Some(if is64 {
                (ProofCategory::X8664Lowering, "Sextend_I16_to_I64")
            } else {
                (ProofCategory::X8664Lowering, "Sextend_I16_to_I32")
            }),
            // 3-operand IMUL r{32,64}, r/m, imm.
            X86Opcode::ImulRRI => Some(if is64 {
                (ProofCategory::X8664Lowering, "Imul_I64_Imm")
            } else {
                (ProofCategory::X8664Lowering, "Imul_I32_Imm")
            }),
            _ => None,
        }
    }

    /// SOUNDNESS: `BtRI %src, #k` is *width- AND bit-polymorphic* — the x86
    /// AND/CMP/Jcc→BT/Jcc peephole emits it at the AND's register class (Gpr32
    /// or Gpr64) with the static bit index `k = imm.trailing_zeros()` of the
    /// erased power-of-two AND mask. The instruction carries both: the source
    /// register's class fixes the operand width, and operand 1 is the `Imm(k)`.
    /// So the verifier disambiguates by `(width, k)` and binds the EXACT
    /// `BtRI_I{32,64}#k` proof (`proof_x86_bt_cf_for_width_bit`), refusing to
    /// fall back to any fixed-width/fixed-bit query. If the width or bit cannot
    /// be resolved (or `k` is out of range for the width), the instruction stays
    /// Unverified (fail closed) rather than binding a guessed instance.
    fn bt_to_proof_query(inst: &X86ISelInst) -> Option<String> {
        let X86Opcode::BtRI = inst.opcode else {
            return None;
        };
        // Width from the source register class (operand 0).
        let width: u32 = match inst.operands.first()? {
            X86ISelOperand::VReg(vreg) => match vreg.class {
                RegClass::Gpr32 => 32,
                RegClass::Gpr64 => 64,
                _ => return None,
            },
            X86ISelOperand::PReg(preg) => {
                if preg.is_gpr64() {
                    64
                } else if preg.is_gpr32() {
                    32
                } else {
                    return None;
                }
            }
            _ => return None,
        };
        // Static bit index from the immediate operand (operand 1).
        let X86ISelOperand::Imm(k) = inst.operands.get(1)? else {
            return None;
        };
        let k = *k;
        if k < 0 || k as u32 >= width {
            return None;
        }
        let ty_name = if width == 64 { "I64" } else { "I32" };
        Some(format!("BtRI_{ty_name}#{k} "))
    }

    /// SOUNDNESS: one-operand `MUL src` (`RDX:RAX = RAX * src`) is width-
    /// polymorphic — the unsigned widening/overflow multiply ISel
    /// (`CheckedUmul`) emits it for both a Gpr32 and a Gpr64 source. The source
    /// register's class (operand 0) fixes the width, so the verifier binds the
    /// width-correct low-half proof (`Umul_I{32,64} (low half RAX)`), which is
    /// the product VALUE the lowering consumes; the high-half (RDX) overflow
    /// proof is registered and required by the coverage gate. Fails closed if
    /// the width cannot be resolved.
    fn mul_to_proof_query(inst: &X86ISelInst) -> Option<String> {
        let X86Opcode::Mul = inst.opcode else {
            return None;
        };
        let class = Self::dst_reg_class(inst)?; // operand 0 is the source reg.
        match class {
            RegClass::Gpr64 => Some("Umul_I64 (low half RAX)".to_string()),
            RegClass::Gpr32 => Some("Umul_I32 (low half RAX)".to_string()),
            _ => None,
        }
    }

    fn trap_skip_reason(opcode: X86Opcode) -> Option<&'static str> {
        match opcode {
            X86Opcode::Ud2 => Some("x86-64 trap instruction"),
            _ => None,
        }
    }

    /// PHASE-2 OPERAND RECONSTRUCTION (x86-64, task #66), CONSTRUCTION half:
    /// build the reconstructed-obligation discharge key for `inst` from the
    /// REAL emitted opcode+operands. Mirrors
    /// `FunctionVerifier::try_reconstruct_pilot` /
    /// `RiscVFunctionVerifier::try_reconstruct` (there still fused with the
    /// discharge; split here so the CT-8 three-stage pre-pass can dedupe
    /// keys BEFORE discharging).
    ///
    /// `None` when the opcode is NOT reconstructable, or the instruction has
    /// no reconstructable operand shape (e.g. a structural 2-address
    /// AddRI/RSP cleanup, or a memory-form operand). The caller falls
    /// through to the existing DB-substring path unchanged.
    ///
    /// The discharge half is [`Self::discharge_reconstructed`]; its credit
    /// rule keys on [`ProofObligation::is_reconstructed`], never on a
    /// `name.contains` lookup — the binding is a typed exhaustive opcode
    /// match plus a typed positional operand schema (anti-f81e45b; asserted
    /// by `tests/reconstruction_x86.rs`).
    fn reconstruct_discharge_key(&self, inst: &X86ISelInst) -> Option<X86DischargeKey> {
        // Not a reconstructable opcode at all -> leave on the existing path.
        x86_opcode_to_source_op(inst.opcode)?;
        // Reconstructable opcode but no reconstructable operand shape -> fall through.
        let instance = reconstruct_alu_obligation(inst)?;
        // PROOF-5 / TV-9 (B2): the `canonical` obligation frees the immediate
        // for the immediate-baked RI families so one parametric tier-0 row
        // covers the whole width family; for every immediate-free family the
        // canonical form is byte-identical to the instance.
        let canonical = canonical_reconstruct_obligation(inst).unwrap_or_else(|| instance.clone());
        Some(X86DischargeKey::Recon {
            instance: Box::new(instance),
            canonical: Box::new(canonical),
        })
    }

    /// PHASE-2 OPERAND RECONSTRUCTION, DISCHARGE half (see
    /// [`Self::reconstruct_discharge_key`]).
    ///
    /// - `Verified { degenerate: false, .. }` when the reconstructed
    ///   obligation discharges `Valid`. Credited (`degenerate: false`)
    ///   because its provenance is `Reconstructed` — the machine side came
    ///   from the REAL instruction, so a wrong opcode/wiring would have
    ///   refuted, even though a *correct* commutative lowering reconstructs
    ///   to `bvadd == bvadd`.
    /// - `Failed { .. }` when the reconstructed obligation REFUTES (wrong
    ///   isel opcode/wiring). This is the content of the mechanism.
    ///
    /// PROOF-5 / TV-9 (B2): prefers a PARAMETRIC/tier-0 candidate after live
    /// solver revalidation (or a live fallback verdict on a miss) and credits
    /// it `Formal` (SolverProven) instead of the 100k-sample Statistical sweep;
    /// a tier-0 miss with a solver present routes to the live solver (refute →
    /// fail closed; inconclusive → statistical fallback); a solver-absent
    /// host keeps the honest Statistical label. Crediting is MONOTONE — never
    /// weaker than the previous sweep.
    fn discharge_reconstructed(
        &self,
        instance: &ProofObligation,
        canonical: &ProofObligation,
    ) -> InstructionVerificationResult {
        let (vresult, strength) = crate::lowering_proof::discharge_reconstructed_obligation(
            instance,
            canonical,
            &self.config,
        );
        match vresult {
            VerificationResult::Valid => {
                debug_assert!(
                    instance.is_reconstructed(),
                    "reconstruct_alu_obligation must tag Reconstructed provenance"
                );
                InstructionVerificationResult::Verified {
                    proof_name: instance.name.clone(),
                    category: ProofCategory::X8664Lowering,
                    strength,
                    // Credited: a reconstructed obligation is the genuine
                    // (non-degenerate) credit even when structurally X==X.
                    degenerate: !instance.is_reconstructed(),
                }
            }
            VerificationResult::Invalid { counterexample } => {
                InstructionVerificationResult::Failed {
                    proof_name: instance.name.clone(),
                    detail: counterexample,
                }
            }
            VerificationResult::Unknown { reason } => InstructionVerificationResult::Failed {
                proof_name: instance.name.clone(),
                detail: format!("Unknown: {reason}"),
            },
        }
    }

    /// CT-8 STAGE-2 kernel: discharge ONE distinct [`X86DischargeKey`].
    ///
    /// PURITY/DETERMINISM: a deterministic pure function of `(&self, key)` —
    /// `Db` resolves against the immutable [`ProofDatabase`] and discharges
    /// through the process-wide compute-once verdict memo / tier-0 verdict
    /// DB; `Recon` discharges the key's own obligations the same way. No
    /// verifier state is mutated, so a key's verdict is IDENTICAL no matter
    /// which worker computes it, how many times, or in what order — the
    /// STAGE-2 dedupe (each distinct key discharged exactly once, the
    /// verdict cloned to every instruction that maps to it) is therefore
    /// result-identical to the fused per-instruction walk. FAILED verdicts
    /// flow through unchanged (and stay memoized fail-closed in the eval
    /// memo).
    fn discharge_key_verdict(&self, key: &X86DischargeKey) -> InstructionVerificationResult {
        match key {
            X86DischargeKey::Db { category, query } => self.resolve_db_proof(*category, query),
            X86DischargeKey::Recon {
                instance,
                canonical,
            } => self.discharge_reconstructed(instance, canonical),
        }
    }

    /// Resolve a static-DB proof by `(category, query)` and discharge it. Shared
    /// by the sequence-recognizer branch and the generic opcode-level branch of
    /// [`Self::verify`]. The x86 verifier matches case-SENSITIVELY
    /// (`name.contains`); STRICT proven-honesty (task #61) is applied at the TALLY
    /// via the `degenerate` flag — a degenerate X==X proof is recorded as a binding
    /// but credited ZERO in the genuine counts.
    fn resolve_db_proof(
        &self,
        category: ProofCategory,
        query: &str,
    ) -> InstructionVerificationResult {
        let candidates = self.db.by_category(category);
        let proof = candidates
            .iter()
            .find(|p| p.obligation.name.contains(query));

        match proof {
            Some(cp) => {
                // PROOF-4 B1: prefer a tier-0 candidate after live revalidation
                // over the statistical sweep for >8-bit registry obligations
                // (stronger). A miss keeps the existing sweep, so no
                // program that compiled before can regress. `strength` reflects
                // reality — `Formal` on a tier-0 hit, else the sweep's strength.
                let (vresult, strength) = crate::lowering_proof::discharge_registry_obligation(
                    &cp.obligation,
                    &self.config,
                );
                match vresult {
                    VerificationResult::Valid => InstructionVerificationResult::Verified {
                        proof_name: cp.obligation.name.clone(),
                        category,
                        strength,
                        degenerate: cp.obligation.is_degenerate(),
                    },
                    VerificationResult::Invalid { counterexample } => {
                        InstructionVerificationResult::Failed {
                            proof_name: cp.obligation.name.clone(),
                            detail: counterexample,
                        }
                    }
                    VerificationResult::Unknown { reason } => {
                        InstructionVerificationResult::Failed {
                            proof_name: cp.obligation.name.clone(),
                            detail: format!("Unknown: {}", reason),
                        }
                    }
                }
            }
            None => InstructionVerificationResult::Unverified {
                reason: format!(
                    "no x86-64 proof matching '{}' in category {}",
                    query,
                    category.name()
                ),
            },
        }
    }

    /// Verify every instruction in an x86-64 ISel function.
    ///
    /// Walks `func.block_order` (not the `blocks` HashMap) to preserve
    /// deterministic emission order across runs. Pseudo-ops (Phi,
    /// StackAlloc, Nop) are reported as `Skipped`.
    ///
    /// After the per-instruction proof walk, runs the carrier-hygiene invariant
    /// ([`crate::carrier_hygiene::check_function`]) over the same function and
    /// FAILS CLOSED on any violation — see [`Self::apply_carrier_hygiene`].
    ///
    /// This entry point has NO replayed LIR function, so the TV-2 provenance
    /// cross-check cannot run here; the compiler cert path uses
    /// [`Self::verify_with_lir_source`] instead.
    pub fn verify(&self, func: &X86ISelFunction) -> FunctionVerificationReport {
        self.verify_with_lir_source(func, None)
    }

    /// [`Self::verify`], plus the TV-2 lowering-provenance cross-check when
    /// the EXACT LIR function that was handed to instruction selection is
    /// supplied (see [`crate::provenance_xcheck`]).
    ///
    /// Every emitted instruction whose provenance is
    /// [`trust_cg_ir::provenance::LoweringProvenance::SourceInst`] is checked
    /// against the replayed LIR: the stamped coordinates must resolve, the
    /// recorded digest must match, and the emitted opcode's definite class
    /// (when it has one) must be a plausible constituent of the claimed
    /// source instruction's lowering. In ENFORCE mode (the x86-64 default) a
    /// mismatch demotes the instruction's result to `Failed`, so the cert is
    /// `verified:false` and the compile fails closed. Synthetic/Unattributed
    /// instructions are exempt. Mode override: `TCG_PROVENANCE_XCHECK`.
    pub fn verify_with_lir_source(
        &self,
        func: &X86ISelFunction,
        lir_source: Option<&trust_cg_lower::Function>,
    ) -> FunctionVerificationReport {
        self.verify_with_lir_source_and_mode(
            func,
            lir_source,
            provenance_xcheck::provenance_xcheck_mode(X86_PROVENANCE_XCHECK_DEFAULT),
        )
    }

    /// CT-8 STAGE 1: construct the BASE-verdict PLAN for
    /// `insts[block_inst_idx]` — the pure, cheap obligation-DESCRIPTOR half
    /// of the sequence-recognizer / operand-reconstruction / static-DB
    /// pipeline, WITHOUT discharging anything. The composition with the
    /// discharge ([`Self::base_instruction_result`]) computes the BASE
    /// verdict: the result BEFORE the TV-2 provenance cross-check and the
    /// carrier-hygiene demotion (both stream-level, kept sequential).
    ///
    /// PURITY (CT-7/CT-8): the plan is a deterministic function of `(&self,
    /// insts, block_inst_idx)` alone — the recognizers and the
    /// reconstruction read the instruction window and the shared immutable
    /// verifier state, mutating nothing. That is what makes the three-stage
    /// PRE-PASS in [`Self::verify_with_lir_source_and_mode`] safe to fan out
    /// across a rayon pool, and the STAGE-2 dedupe sound at all (equal keys
    /// ⇒ equal verdicts; see [`X86DischargeKey`]).
    fn base_instruction_plan(
        &self,
        insts: &[X86ISelInst],
        block_inst_idx: usize,
    ) -> X86BaseVerdictPlan {
        let inst = &insts[block_inst_idx];
        if let Some(reason) = Self::trap_skip_reason(inst.opcode) {
            X86BaseVerdictPlan::Ready(InstructionVerificationResult::Skipped {
                reason: reason.to_string(),
            })
        } else if inst.opcode.is_pseudo() {
            X86BaseVerdictPlan::Ready(InstructionVerificationResult::Skipped {
                reason: format!("{:?} is a pseudo-instruction", inst.opcode),
            })
        } else if let Some((category, query)) =
            // Whole-pattern SEQUENCE recognizers run FIRST so a MOVZX that
            // is part of a recognized bitfield/division/fcmp window keeps
            // its whole-sequence cert (and is NOT mis-credited by the
            // standalone-extend reconstruction below). These all live under
            // the single X8664Lowering category.
            self
                .registered_bitfield_sequence_proof_query(insts, block_inst_idx)
                .map(|q| (ProofCategory::X8664Lowering, q.to_string()))
                .or_else(|| {
                    Self::division_sequence_to_proof_query(insts, block_inst_idx)
                        .map(|q| (ProofCategory::X8664Lowering, q))
                })
                .or_else(|| {
                    Self::fcmp_sequence_to_proof_query(insts, block_inst_idx)
                        .map(|q| (ProofCategory::X8664Lowering, q))
                })
                .or_else(|| {
                    // i128 carry-chain (ADD+ADC / SUB+SBB) whole-value
                    // composition. Recognized HERE (a whole-pattern
                    // sequence recognizer, before the standalone-operand
                    // reconstruction below) so an adjacent ADD+ADC /
                    // SUB+SBB GPR64 pair binds the 128-bit composition
                    // proof. A standalone ADD/SUB (no matching carry
                    // successor) does NOT match and falls through to its
                    // ordinary reconstructed Iadd/Isub cert; a standalone
                    // ADC/SBB stays Unverified (fail closed).
                    Self::i128_carry_chain_sequence_to_proof_query(insts, block_inst_idx)
                        .map(|q| (ProofCategory::X8664Lowering, q))
                })
        {
            X86BaseVerdictPlan::Discharge(X86DischargeKey::Db { category, query })
        } else if let Some(key) = self.reconstruct_discharge_key(inst) {
            // PHASE-2 OPERAND RECONSTRUCTION (x86-64, task #66).
            //
            // The reconstructable ALU/bitwise/shift/extend opcodes with a
            // real operand shape are routed through reconstruction BEFORE
            // the static-DB path. The machine side is rebuilt from the REAL
            // emitted opcode+operands, so a wrong isel choice (e.g. SUB for
            // Iadd, SHL for Ushr, MOVZX for Sextend) or wrong operand wiring
            // on a non-commutative op (SUB/shifts) REFUTES at discharge.
            // Credited Verified IFF `is_reconstructed() && Valid`.
            //
            // `reconstruct_discharge_key` returns `None` when the opcode is
            // not reconstructable OR the instruction does not carry a
            // reconstructable operand shape (a structural 2-address
            // AddRI/RSP cleanup, a memory-form operand, the width-
            // polymorphic ImulRRI which keeps its both-widths gate, etc.);
            // the existing DB-substring path below then runs unchanged.
            X86BaseVerdictPlan::Discharge(key)
        } else if let Some((category, query)) =
            // A STANDALONE width-polymorphic MOVSX/MOVZX/IMUL disambiguates
            // by the destination register class so the proof's width matches
            // the ENCODED width (see `width_polymorphic_extend_imul_query`).
            // The remaining fallbacks all live under the single
            // X8664Lowering category. (The reconstructable ALU/bitwise/shift
            // and byte/word extends were already credited above; this path
            // now backs only ImulRRI and the opcodes outside the
            // reconstructable set.)
            Self::width_polymorphic_extend_imul_query(inst)
                .map(|(cat, q)| (cat, q.to_string()))
                .or_else(|| {
                    Self::instruction_to_proof_query(inst)
                        .map(|q| (ProofCategory::X8664Lowering, q))
                })
        {
            X86BaseVerdictPlan::Discharge(X86DischargeKey::Db { category, query })
        } else {
            X86BaseVerdictPlan::Ready(InstructionVerificationResult::Unverified {
                reason: format!("no proof mapping for x86-64 opcode {:?}", inst.opcode),
            })
        }
    }

    /// Compute the BASE verification result for `insts[block_inst_idx]`:
    /// the STAGE-1 plan composed with its immediate discharge. This is the
    /// SERIAL path's per-instruction walk (and the reference semantics for
    /// the pooled three-stage pre-pass, which computes exactly
    /// `plan → dedupe → discharge → assemble` instead).
    fn base_instruction_result(
        &self,
        insts: &[X86ISelInst],
        block_inst_idx: usize,
    ) -> InstructionVerificationResult {
        match self.base_instruction_plan(insts, block_inst_idx) {
            X86BaseVerdictPlan::Ready(result) => result,
            X86BaseVerdictPlan::Discharge(key) => self.discharge_key_verdict(&key),
        }
    }

    /// Mode-explicit body of [`Self::verify_with_lir_source`] (tests inject
    /// the mode directly to stay independent of ambient env vars).
    fn verify_with_lir_source_and_mode(
        &self,
        func: &X86ISelFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        xcheck_mode: ProvenanceXCheckMode,
    ) -> FunctionVerificationReport {
        // TV-2: index the replayed LIR function. A name mismatch means the
        // caller mis-zipped functions — loudly report and run without the
        // cross-check rather than judging stamps against the wrong spec.
        let lir_index: Option<LirSourceIndex> = match xcheck_mode {
            ProvenanceXCheckMode::Off => None,
            _ => lir_source.and_then(|lir| {
                if lir.name == func.name {
                    Some(LirSourceIndex::build(lir))
                } else {
                    eprintln!(
                        "[TCG-PROVENANCE-XCHECK-WARN] arch=x86_64 fn={} replayed LIR function \
                         name mismatch (got `{}`): provenance cross-check skipped",
                        func.name, lir.name
                    );
                    None
                }
            }),
        };
        let mut attributed_count: usize = 0;
        let mut synthetic_count: usize = 0;
        let mut mismatch_count: usize = 0;

        let mut instructions: Vec<InstructionReport> = Vec::new();
        // Per global instruction index, the source `(block.0, within-block index)`
        // so a carrier-hygiene violation (reported per block + in-block index)
        // can be mapped back to the global report entry it must demote.
        let mut inst_locations: Vec<(u32, usize)> = Vec::new();
        let mut inst_idx: usize = 0;

        // CT-7/CT-8 PRE-PASS: compute every instruction's BASE verdict up
        // front. For non-trivial functions this fans out across the shared
        // big-stack verifier pool in THREE stages (the S5 scoping note's
        // restructure):
        //
        //   STAGE 1 (parallel, indexed): construct per-instruction obligation
        //     DESCRIPTORS (`base_instruction_plan`) — pure and cheap, no
        //     discharge.
        //   STAGE 2 (serial dedupe + parallel discharge): collect the
        //     DISTINCT [`X86DischargeKey`] set in first-occurrence order and
        //     discharge each key EXACTLY ONCE (`with_max_len(1)`: one key per
        //     stolen task). This kills the obligation-DISCOVERY convoy the
        //     flat per-instruction fanout had: there, every worker marched
        //     the same few keys in walk order, so all but one PARKED on the
        //     same in-flight compute-once memo cell while undiscovered keys
        //     sat idle — the lane flatlined at the distinct-obligation sweep
        //     CHAIN (~sum of sweeps) regardless of pool width. Here no worker
        //     parks on another's in-flight key within a function: the
        //     distinct keys are all in flight CONCURRENTLY (~max of sweeps).
        //   STAGE 3 (parallel, indexed): assemble the per-instruction
        //     verdicts from the discharged slots.
        //
        // DETERMINISM: `flat` enumerates (block, inst) in exactly the walk
        // order below; STAGE 1 and STAGE 3 are indexed
        // `par_iter().map().collect()`s (result `i` lands at slot `i`), and a
        // STAGE-2 verdict is a deterministic pure function of key CONTENT
        // (see `discharge_key_verdict`) — so verdict content and order are
        // identical to the serial walk regardless of thread schedule. The
        // TV-2 cross-check, tallies, and report assembly stay sequential
        // below.
        let flat: Vec<(&[X86ISelInst], usize)> = func
            .block_order
            .iter()
            .filter_map(|block_id| func.blocks.get(block_id))
            .flat_map(|block| (0..block.insts.len()).map(move |i| (block.insts.as_slice(), i)))
            .collect();
        let base_results: Vec<InstructionVerificationResult> = if let Some(pool) =
            verifier_prepass_pool_for_items(flat.len())
        {
            pool.install(|| {
                use rayon::prelude::*;
                // STAGE 1: per-instruction obligation descriptors.
                let plans: Vec<X86BaseVerdictPlan> = flat
                    .par_iter()
                    .map(|&(insts, i)| self.base_instruction_plan(insts, i))
                    .collect();
                // STAGE 2a (serial, cheap): the distinct key set in
                // first-occurrence order + each plan's slot binding.
                let mut key_slots: std::collections::HashMap<&X86DischargeKey, usize> =
                    std::collections::HashMap::new();
                let mut distinct: Vec<&X86DischargeKey> = Vec::new();
                let mut plan_slots: Vec<Option<usize>> = Vec::with_capacity(plans.len());
                for plan in &plans {
                    plan_slots.push(match plan {
                        X86BaseVerdictPlan::Ready(_) => None,
                        X86BaseVerdictPlan::Discharge(key) => {
                            Some(*key_slots.entry(key).or_insert_with(|| {
                                distinct.push(key);
                                distinct.len() - 1
                            }))
                        }
                    });
                }
                // STAGE 2b: discharge each DISTINCT key exactly once,
                // one key per work item.
                let discharged: Vec<InstructionVerificationResult> = distinct
                    .par_iter()
                    .with_max_len(1)
                    .map(|key| self.discharge_key_verdict(key))
                    .collect();
                // STAGE 3: assemble (indexed, order-stable).
                plans
                    .par_iter()
                    .zip(plan_slots.par_iter())
                    .map(|(plan, slot)| match (plan, slot) {
                        (X86BaseVerdictPlan::Ready(result), _) => result.clone(),
                        (X86BaseVerdictPlan::Discharge(_), Some(slot)) => discharged[*slot].clone(),
                        (X86BaseVerdictPlan::Discharge(_), None) => {
                            unreachable!("STAGE 2a assigned a slot to every Discharge plan")
                        }
                    })
                    .collect()
            })
        } else {
            flat.iter()
                .map(|&(insts, i)| self.base_instruction_result(insts, i))
                .collect()
        };
        let mut base_results = base_results.into_iter();

        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for (block_inst_idx, inst) in block.insts.iter().enumerate() {
                let result = base_results
                    .next()
                    .expect("pre-pass enumerated exactly the walked instructions");

                // TV-2: cross-check the TV-1 provenance stamp against the
                // replayed LIR function. Runs for EVERY stamped instruction
                // (including Skipped pseudos/trap carriers — a misattributed
                // stamp is a misattribution regardless of the proof verdict).
                let result = if let Some(index) = lir_index.as_ref() {
                    if inst.lowering_provenance.is_source_attributed() {
                        attributed_count += 1;
                    } else {
                        synthetic_count += 1;
                    }
                    match provenance_xcheck::cross_check_inst(
                        &inst.lowering_provenance,
                        x86_emitted_op_class(inst),
                        &format!("{:?}", inst.opcode),
                        index,
                    ) {
                        Some(mismatch) => {
                            mismatch_count += 1;
                            provenance_xcheck::record_provenance_xcheck_hit(
                                "x86_64",
                                &func.name,
                                inst_idx,
                                &mismatch,
                                xcheck_mode,
                            );
                            if xcheck_mode == ProvenanceXCheckMode::Enforce {
                                InstructionVerificationResult::Failed {
                                    proof_name: "provenance-crosscheck (TV-2)".to_string(),
                                    detail: mismatch.detail,
                                }
                            } else {
                                result
                            }
                        }
                        None => result,
                    }
                } else {
                    result
                };

                instructions.push(InstructionReport {
                    inst_index: inst_idx,
                    opcode: InstructionOpcode::X86_64(inst.opcode),
                    result,
                });
                inst_locations.push((block_id.0, block_inst_idx));
                inst_idx += 1;
            }
        }

        if lir_index.is_some() {
            provenance_xcheck::trace_function_summary(
                "x86_64",
                &func.name,
                attributed_count,
                synthetic_count,
                mismatch_count,
            );
        }

        Self::apply_carrier_hygiene(func, &mut instructions, &inst_locations);

        FunctionVerificationReport {
            function_name: func.name.clone(),
            instructions,
        }
    }

    /// Run the carrier-hygiene invariant over the emitted function and FAIL
    /// CLOSED on any violation.
    ///
    /// MISCOMPILE #51/#66 lived downstream of the SMT-verified per-instruction
    /// lowerings: each `SAR`/`IDIV`/`SHR`/`DIV` lowering is correct *given a
    /// correctly-extended operand*, but nothing in the per-instruction walk above
    /// checks the operand actually was extended. The bug is a property of the
    /// instruction *stream*, so this runs [`crate::carrier_hygiene::check_function`]
    /// over the whole [`X86ISelFunction`] and demotes every offending
    /// instruction's report to `Failed` — making `all_verified()` false and
    /// surfacing the violation, exactly as a failed proof obligation would.
    ///
    /// # Soundness gate
    ///
    /// The checker is seeded from the per-VReg nominal-width map ISel records
    /// (`X86ISelFunction::vreg_nominal_widths()`); that map is the load-bearing
    /// fact distinguishing a narrow (i8/i16) value with dirty high carrier bits
    /// from a value that fills its carrier. A function with NO recorded widths
    /// did not pass through the width-recording ISel selection path (every real
    /// ISel function records at least its GPR-carrier defs, and the
    /// narrow-divisor/shiftee extension helpers record their extended VRegs), so
    /// it carries no ground truth to check against and the gate is skipped. This
    /// is sound: such width-less functions are synthetic (hand-built proof-binding
    /// fixtures), never production codegen — production ISel output always carries
    /// the width map, so the invariant always runs on real emitted code. Running
    /// the fail-closed checker against an empty map would instead reject every
    /// hand-built wide-reader fixture as "unknown width", which is a false
    /// positive against non-codegen input, not a real miscompile.
    fn apply_carrier_hygiene(
        func: &X86ISelFunction,
        instructions: &mut [InstructionReport],
        inst_locations: &[(u32, usize)],
    ) {
        // No width metadata => not a width-recording ISel function => nothing to
        // check against. See the soundness note above.
        if func.vreg_nominal_widths().is_empty() {
            return;
        }

        let nominal = crate::carrier_hygiene::NominalWidths::from_value_type_widths(
            func.vreg_nominal_widths(),
        );
        let report = crate::carrier_hygiene::check_function(func, &nominal);
        if report.is_clean() {
            return;
        }

        for violation in &report.violations {
            // Map the (block.0, within-block index) the violation carries to the
            // global report index, then demote that instruction to `Failed`.
            if let Some(global_idx) = inst_locations
                .iter()
                .position(|&(b, i)| b == violation.block && i == violation.inst_index)
            {
                instructions[global_idx].result = InstructionVerificationResult::Failed {
                    proof_name: "carrier-hygiene invariant".to_string(),
                    detail: violation.detail.clone(),
                };
            } else {
                // FAIL-CLOSED: the violation's (block, inst_index) did not map to
                // any global report index. The mapping is expected to always
                // succeed for production ISel output (the verdict loop populated
                // `inst_locations` from the same walk), so this is latent — but
                // a real carrier-hygiene violation that cannot be placed must NOT
                // be silently dropped (which would leave the offending
                // instruction at its prior Verified/Unverified verdict). Demote a
                // fallback instruction to Failed so the function cannot pass
                // verification on the strength of an unplaceable miscompile-class
                // violation.
                if let Some(last) = instructions.last_mut() {
                    last.result = InstructionVerificationResult::Failed {
                        proof_name: "carrier-hygiene invariant (unmapped)".to_string(),
                        detail: format!(
                            "carrier-hygiene violation at bb{} inst{} could not be mapped to a \
                             report index ({}); failing closed",
                            violation.block, violation.inst_index, violation.detail
                        ),
                    };
                }
                // An empty `instructions` slice means there is no instruction to
                // demote; such a function has nothing to emit and cannot carry a
                // hygiene violation in the first place.
            }
        }
    }
}

impl Default for X86FunctionVerifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience: verify an [`X86ISelFunction`] using default configuration.
///
/// This is the primary entry point for x86-64 function-level verification.
/// Mirrors [`crate::function_verifier::verify_function`] for AArch64.
pub fn verify_x86_64_function(func: &X86ISelFunction) -> FunctionVerificationReport {
    X86FunctionVerifier::new().verify(func)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    // Test-only DIRECT (unmemoized) eval: these tests deliberately assert the
    // RAW evaluator's verdict on registered DB obligations — routing them
    // through the shared PROOF-2 memo would let a cache hit stand in for the
    // evaluation under test. Production code paths in this file go through
    // `crate::lowering_proof::memoized_verify_by_evaluation` only.
    use crate::lowering_proof::verify_by_evaluation_with_config;
    use trust_cg_ir::X86Opcode;
    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::x86_64_isel::{X86ISelBlock, X86ISelInst, X86ISelOperand};

    fn make_func_with_opcodes(opcodes: &[X86Opcode]) -> X86ISelFunction {
        let insts: Vec<_> = opcodes
            .iter()
            .copied()
            .map(|op| X86ISelInst::new(op, vec![]))
            .collect();
        make_func_with_insts(insts)
    }

    #[test]
    fn emitted_opcode_inventory_reports_target_typed_x86_uncovered_opcode() {
        // Xchg is a representative still-unmapped opcode (Jmp, the previous
        // representative, now carries its control-target proof).
        let report = verify_x86_64_function(&make_func_with_opcodes(&[X86Opcode::Xchg]));
        let inventory = report.emitted_opcode_inventory();
        let uncovered = inventory.uncovered_non_pseudo_opcodes();

        assert_eq!(uncovered.len(), 1);
        assert_eq!(
            uncovered[0].opcode,
            crate::function_verifier::InstructionOpcode::X86_64(X86Opcode::Xchg)
        );
        assert_eq!(
            uncovered[0].status,
            crate::function_verifier::OpcodeInventoryStatus::Unverified
        );
        let reason = inventory
            .promotion_rejection_reason()
            .expect("uncovered x86 opcode should reject promotion");
        assert!(reason.contains("x86_64::Xchg"), "{reason}");
        assert!(!reason.contains("AArch64::Nop"), "{reason}");
    }

    fn make_func_with_insts(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            "test".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        let block_id = Block(0);
        func.ensure_block(block_id);
        let block: &mut X86ISelBlock = func.blocks.get_mut(&block_id).unwrap();
        block.insts.extend(insts);
        func
    }

    fn atomic_rmw_cas_loop_inst(opcode: X86Opcode, kind: i64, class: RegClass) -> X86ISelInst {
        X86ISelInst::new(
            opcode,
            vec![
                X86ISelOperand::VReg(VReg::new(0, class)),
                X86ISelOperand::Imm(0),
                X86ISelOperand::Imm(0),
                X86ISelOperand::Imm(kind),
            ],
        )
    }

    fn gpr32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn gpr64(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn extract_bits_i32_sequence() -> Vec<X86ISelInst> {
        vec![
            X86ISelInst::new(
                X86Opcode::ShrRI,
                vec![
                    gpr32(1),
                    gpr32(0),
                    X86ISelOperand::Imm(i64::from(X86_BITFIELD_REPRESENTATIVE_LSB)),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![gpr32(2), X86ISelOperand::Imm((1_i64 << 13) - 1)],
            ),
            X86ISelInst::new(X86Opcode::AndRR, vec![gpr32(3), gpr32(1), gpr32(2)]),
        ]
    }

    fn sextract_bits_i32_sequence() -> Vec<X86ISelInst> {
        vec![
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![gpr32(1), gpr32(0), X86ISelOperand::Imm(12)],
            ),
            X86ISelInst::new(
                X86Opcode::SarRI,
                vec![gpr32(2), gpr32(1), X86ISelOperand::Imm(19)],
            ),
        ]
    }

    fn insert_bits_i32_sequence() -> Vec<X86ISelInst> {
        vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![gpr32(2), X86ISelOperand::Imm(0xfff0_007f)],
            ),
            X86ISelInst::new(X86Opcode::AndRR, vec![gpr32(3), gpr32(0), gpr32(2)]),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![gpr32(4), X86ISelOperand::Imm((1_i64 << 13) - 1)],
            ),
            X86ISelInst::new(X86Opcode::AndRR, vec![gpr32(5), gpr32(1), gpr32(4)]),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![
                    gpr32(6),
                    gpr32(5),
                    X86ISelOperand::Imm(i64::from(X86_BITFIELD_REPRESENTATIVE_LSB)),
                ],
            ),
            X86ISelInst::new(X86Opcode::OrRR, vec![gpr32(7), gpr32(3), gpr32(6)]),
        ]
    }

    fn fcmp_f64_ge_sequence() -> Vec<X86ISelInst> {
        vec![
            X86ISelInst::new(X86Opcode::Ucomisd, vec![gpr32(0), gpr32(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![gpr32(2), X86ISelOperand::CondCode(X86CondCode::AE)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![gpr32(2), gpr32(2)]),
        ]
    }

    fn fcmp_f32_uge_sequence() -> Vec<X86ISelInst> {
        vec![
            X86ISelInst::new(X86Opcode::Ucomiss, vec![gpr32(0), gpr32(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![gpr32(2), X86ISelOperand::CondCode(X86CondCode::AE)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![gpr32(2), gpr32(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![gpr32(3), X86ISelOperand::CondCode(X86CondCode::P)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![gpr32(3), gpr32(3)]),
            X86ISelInst::new(X86Opcode::OrRR, vec![gpr32(2), gpr32(2), gpr32(3)]),
        ]
    }

    fn div_result_sequence(
        div_opcode: X86Opcode,
        copy_opcode: X86Opcode,
        result_reg: trust_cg_ir::x86_64_regs::X86PReg,
    ) -> Vec<X86ISelInst> {
        let (acc, rem, lhs, divisor, dst) = match copy_opcode {
            X86Opcode::MovRR32 => (EAX, EDX, gpr32(0), gpr32(1), gpr32(2)),
            X86Opcode::MovRR => (RAX, RDX, gpr64(0), gpr64(1), gpr64(2)),
            _ => panic!("division test copy opcode must be MovRR or MovRR32"),
        };

        let setup = match div_opcode {
            X86Opcode::Idiv => X86ISelInst::new(
                match copy_opcode {
                    X86Opcode::MovRR32 => X86Opcode::Cdq,
                    X86Opcode::MovRR => X86Opcode::Cqo,
                    _ => unreachable!(),
                },
                vec![],
            ),
            X86Opcode::Div => X86ISelInst::new(
                X86Opcode::XorRR,
                vec![
                    X86ISelOperand::PReg(rem),
                    X86ISelOperand::PReg(rem),
                    X86ISelOperand::PReg(rem),
                ],
            ),
            _ => panic!("division test opcode must be Div or Idiv"),
        };

        vec![
            X86ISelInst::new(copy_opcode, vec![X86ISelOperand::PReg(acc), lhs]),
            setup,
            X86ISelInst::new(div_opcode, vec![divisor]),
            X86ISelInst::new(copy_opcode, vec![dst, X86ISelOperand::PReg(result_reg)]),
        ]
    }

    #[test]
    fn empty_function_has_100_percent_coverage() {
        let func = X86ISelFunction::new(
            "empty".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        let report = verify_x86_64_function(&func);
        assert_eq!(report.total(), 0);
        assert_eq!(report.coverage_percent(), 100.0);
    }

    #[test]
    fn addrr_is_verified() {
        let func = make_func_with_opcodes(&[X86Opcode::AddRR]);
        let report = verify_x86_64_function(&func);
        assert_eq!(report.total(), 1);
        assert_eq!(
            report.verified_count(),
            1,
            "AddRR should match Iadd_I proof; report was {}",
            report
        );
    }

    #[test]
    fn nop_is_skipped() {
        let func = make_func_with_opcodes(&[X86Opcode::Nop]);
        let report = verify_x86_64_function(&func);
        assert_eq!(report.skipped_count(), 1);
    }

    #[test]
    fn ud2_trap_is_skipped() {
        let func = make_func_with_opcodes(&[X86Opcode::Ud2]);
        let report = verify_x86_64_function(&func);
        assert_eq!(report.total(), 1);
        assert_eq!(report.skipped_count(), 1);
        assert_eq!(report.unverified_count(), 0);
        assert_eq!(report.coverage_percent(), 100.0);
    }

    #[test]
    fn ret_is_unverified_after_control_transfer_proof_retraction() {
        // #62: the degenerate "x86_64: RET branches to stack return address" X==X
        // was RETRACTED, so RET has no per-instruction value-proof now (Unverified;
        // the CFG/return-address edge is covered by the Branch/relocation family).
        let func = make_func_with_opcodes(&[X86Opcode::Ret]);
        let report = verify_x86_64_function(&func);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 1);
        assert_eq!(
            report.instructions[0].opcode,
            InstructionOpcode::X86_64(X86Opcode::Ret)
        );
    }

    #[test]
    fn mixed_ops_get_counted_correctly() {
        let func = make_func_with_opcodes(&[
            X86Opcode::AddRR, // verified (Iadd_I)
            X86Opcode::SubRR, // verified (Isub_I)
            X86Opcode::Nop,   // skipped
            X86Opcode::Ud2,   // skipped trap
            X86Opcode::Ret,   // unverified (#62: RET control-transfer X==X retracted)
        ]);
        let report = verify_x86_64_function(&func);
        assert_eq!(report.total(), 5);
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.skipped_count(), 2);
        assert_eq!(report.unverified_count(), 1);
    }

    // ----------------------------------------------------------------------
    // RESIDUAL A: carrier-hygiene is wired into the LIVE verification path.
    // ----------------------------------------------------------------------
    //
    // Previously `carrier_hygiene::check_function` was dead code reachable only
    // from its own integration tests. These tests prove the LIVE
    // `verify_x86_64_function` path now (a) rejects a dirtied-narrow IDIV
    // divisor as `Failed` (closing #51/#66 downstream of the per-instruction
    // proofs), (b) does NOT false-reject a correctly sign-extended divisor, and
    // (c) leaves width-less synthetic functions untouched (the sound gate).

    fn vreg32(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr32)
    }

    /// Build a single-block x86 ISel function from `insts`, with the per-VReg
    /// nominal widths the verifier seeds the carrier-hygiene checker from. A
    /// non-empty width map is what marks the function as real (width-recording)
    /// ISel output the live gate runs over.
    fn make_func_with_widths(insts: Vec<X86ISelInst>, widths: &[(VReg, u32)]) -> X86ISelFunction {
        let mut func = make_func_with_insts(insts);
        for &(v, w) in widths {
            func.vreg_nominal_widths.insert(v, w);
        }
        func
    }

    #[test]
    fn live_path_rejects_dirty_narrow_idiv_divisor() {
        // i8 divisor dirtied by a 32-bit NEG, fed straight to IDIV with NO
        // sign-extension — the #51 divisor miscompile. The per-instruction proof
        // walk discharges every opcode (Neg, Idiv) in isolation; only the
        // carrier-hygiene invariant over the stream catches the missing extend.
        let v0 = vreg32(0); // i8 seed
        let div = vreg32(1); // dirty i8 divisor (NEG result)
        let q = vreg32(2); // quotient
        let func = make_func_with_widths(
            vec![
                X86ISelInst::new(
                    X86Opcode::MovRI,
                    vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
                ),
                // NEG dirties the high carrier of the narrow i8 value.
                X86ISelInst::new(
                    X86Opcode::Neg,
                    vec![X86ISelOperand::VReg(div), X86ISelOperand::VReg(v0)],
                ),
                // IDIV reads `div` SIGNED across the full 32-bit carrier.
                X86ISelInst::new(
                    X86Opcode::Idiv,
                    vec![X86ISelOperand::VReg(q), X86ISelOperand::VReg(div)],
                ),
            ],
            &[(v0, 8), (div, 8), (q, 8)],
        );

        let report = verify_x86_64_function(&func);
        assert!(
            !report.all_verified(),
            "the LIVE verifier path must FAIL a dirtied-narrow IDIV divisor (#51); report:\n{report}"
        );
        assert_eq!(
            report.failed_count(),
            1,
            "exactly the IDIV must be demoted to Failed; report:\n{report}"
        );
        let failed = report.failed_instructions();
        assert_eq!(
            failed[0].opcode,
            InstructionOpcode::X86_64(X86Opcode::Idiv),
            "the carrier-hygiene failure must land on the IDIV consuming the dirty divisor"
        );
        match &failed[0].result {
            InstructionVerificationResult::Failed { proof_name, detail } => {
                assert_eq!(proof_name, "carrier-hygiene invariant");
                assert!(
                    detail.contains("#51"),
                    "detail should reference the historical miscompile class: {detail}"
                );
            }
            other => panic!("expected Failed, got {other:?}"),
        }
    }

    #[test]
    fn live_path_accepts_sign_extended_idiv_divisor() {
        // The fix shape: MOVSX sign-extends the narrow divisor before IDIV. The
        // carrier-hygiene check must NOT false-reject this (no narrow hazard).
        let v0 = vreg32(0);
        let ext = vreg32(1); // MOVSX result: clean SignExt(8)
        let q = vreg32(2);
        let func = make_func_with_widths(
            vec![
                X86ISelInst::new(
                    X86Opcode::MovRI,
                    vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(-3)],
                ),
                // sign_extend_narrow_operand(I8) -> MOVSXB : SignExt(8).
                X86ISelInst::new(
                    X86Opcode::MovsxB,
                    vec![X86ISelOperand::VReg(ext), X86ISelOperand::VReg(v0)],
                ),
                X86ISelInst::new(
                    X86Opcode::Idiv,
                    vec![X86ISelOperand::VReg(q), X86ISelOperand::VReg(ext)],
                ),
            ],
            &[(v0, 8), (ext, 8), (q, 8)],
        );

        let report = verify_x86_64_function(&func);
        assert_eq!(
            report.failed_count(),
            0,
            "a MOVSX-extended IDIV divisor must NOT be flagged by carrier-hygiene; report:\n{report}"
        );
    }

    #[test]
    fn live_path_skips_carrier_hygiene_without_width_metadata() {
        // A width-less synthetic function (no ISel width recording) carries no
        // ground truth for the narrow-carrier check; the gate is skipped so the
        // hand-built proof-binding fixtures (and the existing 102 tests) keep
        // their behavior. Same dirty-narrow IDIV as above, but with NO widths.
        let v0 = vreg32(0);
        let div = vreg32(1);
        let q = vreg32(2);
        let func = make_func_with_insts(vec![
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Neg,
                vec![X86ISelOperand::VReg(div), X86ISelOperand::VReg(v0)],
            ),
            X86ISelInst::new(
                X86Opcode::Idiv,
                vec![X86ISelOperand::VReg(q), X86ISelOperand::VReg(div)],
            ),
        ]);
        assert!(
            func.vreg_nominal_widths().is_empty(),
            "precondition: this fixture records no widths"
        );

        let report = verify_x86_64_function(&func);
        assert_eq!(
            report.failed_count(),
            0,
            "carrier-hygiene must be skipped on width-less synthetic functions; report:\n{report}"
        );
    }

    /// Regression: x86-64 INDIRECT calls (`CallR` = call-register, `CallM` =
    /// call-memory) must report `Unverified` (`opcode_to_proof_query == None`),
    /// NOT be forge-`Verified` by the `target == target` tautology in
    /// `proof_x86_call_branches_to_target`. This mirrors the already-honest
    /// AArch64 `Blr => None` posture (asserted by the sibling
    /// `function_verifier.rs` test). A DIRECT `Call` stays covered — its target
    /// is witnessed by the symbol-relocation lane, not the tautology.
    #[test]
    fn indirect_calls_are_not_verified_against_tautology() {
        assert!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::CallR).is_none(),
            "indirect call-register must be Unverified, not tautology-Verified"
        );
        assert!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::CallM).is_none(),
            "indirect call-memory must be Unverified, not tautology-Verified"
        );
        assert!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Call).is_none(),
            "direct call: degenerate 'CALL branches to target' X==X retracted (#62) -> None"
        );
    }

    #[test]
    fn opcode_query_coverage() {
        // Sanity: core integer arithmetic has a proof query.
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::AddRR),
            Some("Iadd_I")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::SubRR),
            Some("Isub_I")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Cmovcc),
            Some("CMOVcc bitwise select")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Cmovcc32),
            Some("CMOVcc32 bitwise select")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovdToXmm),
            Some("MOVD xmm,r32 preserves bits")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovdFromXmm),
            Some("MOVD r32,xmm preserves bits")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovqToXmm),
            Some("MOVQ xmm,r64 preserves bits")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovqFromXmm),
            Some("MOVQ r64,xmm preserves bits")
        );
        // MovRI: degenerate "MOV r,imm materializes constant" X==X retracted (#62).
        assert!(X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovRI).is_none());
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovRR),
            Some("Copy_I64 -> MOV r64,r64 preserves bits")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovRR32),
            Some("Copy_I32 -> MOV r32,r32 preserves bits")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::AtomicRmwCasLoop),
            Some("AtomicRmwCasLoop_Add_I")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::AtomicRmwCasLoop8),
            Some("AtomicRmwCasLoop8_Add_I8")
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::AtomicRmwCasLoop16),
            Some("AtomicRmwCasLoop16_Add_I16")
        );
        // Plain (non-atomic) memory moves and plain LEA now bind their
        // effective-address Load_/Store_/LEA proofs at the opcode level; the
        // atomic-origin variants are routed FIRST by
        // `proof_origin_to_proof_query` and mismatched provenance fails
        // closed in `instruction_to_proof_query`.
        for (opcode, query) in [
            (X86Opcode::MovRM8, "Load_I8 -> MOV r8,[r64+disp32]"),
            (X86Opcode::MovRM16, "Load_I16 -> MOV r16,[r64+disp32]"),
            (X86Opcode::MovRM32, "Load_I32 -> MOV r32,[r64+disp32]"),
            (X86Opcode::MovRM, "Load_I64 -> MOV r64,[r64+disp32]"),
            (X86Opcode::MovMR8, "Store_I8 -> MOV [r64+disp32],r8"),
            (X86Opcode::MovMR16, "Store_I16 -> MOV [r64+disp32],r16"),
            (X86Opcode::MovMR32, "Store_I32 -> MOV [r64+disp32],r32"),
            (X86Opcode::MovMR, "Store_I64 -> MOV [r64+disp32],r64"),
        ] {
            assert_eq!(
                X86FunctionVerifier::opcode_to_proof_query(opcode),
                Some(query),
                "{opcode:?} should bind its effective-address memory proof"
            );
        }
        // Plain LEA: degenerate "base+disp32 -> LEA" effective-address X==X
        // retracted (#62) -> None.
        assert!(X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Lea).is_none());
        // Mfence (fence provenance) and LeaSib (per-instance scale/disp) still
        // need operand/provenance metadata, so the opcode-only mapping is None.
        for opcode in [X86Opcode::Mfence, X86Opcode::LeaSib] {
            assert_eq!(
                X86FunctionVerifier::opcode_to_proof_query(opcode),
                None,
                "{opcode:?} should require operand/provenance metadata, not opcode-only proof binding"
            );
        }
        // LeaRip / MovRipRel now bind their RIP-relative symbol-address proofs
        // at the opcode level: both only ever carry a `Symbol` operand, so the
        // opcode alone fixes the relocation provenance (SIGNED vs GOT_LOAD).
        // These compose with the proven Mach-O SIGNED / GOT_LOAD relocation
        // displacements (the per-RELOCATION proofs) to materialize S + A.
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::LeaRip),
            Some("LeaRip Symbol -> RIP_next + SIGNED disp32 == S + A"),
            "LeaRip should bind its RIP-relative symbol-address (SIGNED) proof"
        );
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::MovRipRel),
            Some("MovRipRel Symbol -> RIP_next + GOT_LOAD disp32 == G + A"),
            "MovRipRel should bind its RIP-relative GOT-slot (GOT_LOAD) proof"
        );
        // Call / Ret / Jmp: degenerate control-flow X==X retracted (#62) -> None.
        assert!(X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Call).is_none());
        assert!(X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Ret).is_none());
        assert!(X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Jmp).is_none());
        assert_eq!(
            X86FunctionVerifier::opcode_to_proof_query(X86Opcode::Ud2),
            None
        );

        // (#65) SSE scalar-FP MOVE / COPY / load / store / const-pool-load,
        // FP-compare, and the FP-NEG PXOR sign idiom now bind opcode-level
        // proofs (formerly None -> "no proof mapping" -> m68/m69 fail-closed).
        for (opcode, query) in [
            (
                X86Opcode::MovssRR,
                "Copy_F32 -> MOVSS xmm,xmm preserves scalar bits",
            ),
            (
                X86Opcode::MovsdRR,
                "Copy_F64 -> MOVSD xmm,xmm preserves scalar bits",
            ),
            (X86Opcode::MovssRM, "Load_F32 -> MOVSS xmm,[r64+disp32]"),
            (X86Opcode::MovsdRM, "Load_F64 -> MOVSD xmm,[r64+disp32]"),
            (X86Opcode::MovssMR, "Store_F32 -> MOVSS [r64+disp32],xmm"),
            (X86Opcode::MovsdMR, "Store_F64 -> MOVSD [r64+disp32],xmm"),
            (
                X86Opcode::MovssRipRel,
                "MovssRipRel -> RIP_next + disp32 == C (f32 const-pool addr)",
            ),
            (
                X86Opcode::MovsdRipRel,
                "MovsdRipRel -> RIP_next + disp32 == C (f64 const-pool addr)",
            ),
            (X86Opcode::Ucomiss, "Fcmp_Eq_F32 -> x86_64 UCOMISS"),
            (X86Opcode::Ucomisd, "Fcmp_Eq_F64 -> x86_64 UCOMISD"),
            (X86Opcode::Pxor, "V128 Bxor -> PXOR xmm,xmm"),
        ] {
            assert_eq!(
                X86FunctionVerifier::opcode_to_proof_query(opcode),
                Some(query),
                "{opcode:?} should bind its float-move/compare/sign-idiom proof"
            );
        }

        // SOUNDNESS: every #65 float-move/compare/sign-idiom query must resolve
        // to a REGISTERED, DISCHARGING proof in the ProofDatabase (the exact
        // lookup the per-instruction verifier performs). A typo'd query would
        // bind nothing and the opcode would silently fall back to Unverified.
        let db = ProofDatabase::new();
        let candidates = db.by_category(ProofCategory::X8664Lowering);
        for opcode in [
            X86Opcode::MovssRR,
            X86Opcode::MovsdRR,
            X86Opcode::MovssRM,
            X86Opcode::MovsdRM,
            X86Opcode::MovssMR,
            X86Opcode::MovsdMR,
            X86Opcode::MovssRipRel,
            X86Opcode::MovsdRipRel,
            X86Opcode::Ucomiss,
            X86Opcode::Ucomisd,
            X86Opcode::Pxor,
        ] {
            let query = X86FunctionVerifier::opcode_to_proof_query(opcode)
                .unwrap_or_else(|| panic!("{opcode:?} must have a proof query"));
            let proof = candidates
                .iter()
                .find(|p| p.obligation.name.contains(query))
                .unwrap_or_else(|| {
                    panic!("{opcode:?} query {query:?} matched no registered X8664Lowering proof")
                });
            assert!(
                matches!(
                    verify_by_evaluation_with_config(
                        &proof.obligation,
                        &VerificationConfig::default()
                    ),
                    VerificationResult::Valid
                ),
                "{opcode:?} proof {:?} must discharge",
                proof.obligation.name
            );
        }
    }

    #[test]
    fn atomic_load_store_fence_opcodes_verify_with_registered_proofs() {
        let inst_queries = [
            (
                X86ISelInst::new(X86Opcode::MovRM8, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I8",
            ),
            (
                X86ISelInst::new(X86Opcode::MovRM16, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I16",
            ),
            (
                X86ISelInst::new(X86Opcode::MovRM32, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I32",
            ),
            (
                X86ISelInst::new(X86Opcode::MovRM, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I64",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR8, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I8",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR16, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I16",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR32, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I32",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I64",
            ),
            // SLICE 3: the SeqCst fence lowers to MFENCE and binds a GENUINE
            // single-thread-identity proof (replaces the retracted #62
            // const==const tautology). Acquire/Release/AcqRel fences emit ZERO
            // instructions on x86 TSO, so no MFENCE for them and nothing to
            // verify.
            (
                X86ISelInst::new(X86Opcode::Mfence, vec![])
                    .with_proof_origin(X86ProofOrigin::FenceSeqCst),
                "x86_64: SeqCst fence -> MFENCE single-thread identity",
            ),
        ];
        let func =
            make_func_with_insts(inst_queries.iter().map(|(inst, _)| inst.clone()).collect());
        let report = verify_x86_64_function(&func);

        assert_eq!(report.total(), inst_queries.len());
        assert_eq!(
            report.verified_count(),
            inst_queries.len(),
            "atomic load/store opcodes should all verify; report was {report}"
        );
        assert_eq!(
            report.unverified_count(),
            0,
            "atomic load/store opcodes should not report stale gaps; report was {report}"
        );

        for (idx, (inst, query)) in inst_queries.iter().enumerate() {
            match &report.instructions[idx].result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert!(
                        matches!(*category, ProofCategory::X8664Lowering),
                        "{:?} should verify against an x86-64 lowering proof",
                        inst.opcode
                    );
                    assert!(
                        proof_name.contains(query),
                        "{:?} verified with unexpected proof {proof_name:?}",
                        inst.opcode
                    );
                }
                result => panic!(
                    "registered atomic proof query {query:?} for {:?} should verify; got {result:?}",
                    inst.opcode
                ),
            }
        }
    }

    /// An emitted adjacent i128 carry-chain pair (`ADD lo; ADC hi` GPR64) must
    /// bind the WHOLE-value composition proof (`Iadd_I128 -> ADD lo; ADC hi`) on
    /// BOTH members and discharge it — proving the wiring genuinely COVERS the
    /// 128-bit add (not just compiles). Mirrors `select_i128_add`'s emission.
    #[test]
    fn i128_add_adc_pair_binds_composition_proof_and_verifies() {
        // dst_lo = lo_a + lo_b ; dst_hi = hi_a + hi_b + CF
        let insts = vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![gpr64(0), gpr64(1), gpr64(2)]),
            X86ISelInst::new(X86Opcode::AdcRR, vec![gpr64(3), gpr64(4), gpr64(5)]),
        ];
        let report = verify_x86_64_function(&make_func_with_insts(insts));
        assert_eq!(report.total(), 2);
        assert_eq!(
            report.verified_count(),
            2,
            "both ADD and ADC of an i128 pair must verify; report was {report}"
        );
        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert!(matches!(*category, ProofCategory::X8664Lowering));
                    assert!(
                        proof_name.contains("Iadd_I128 -> ADD lo; ADC hi"),
                        "i128 carry-chain member bound unexpected proof {proof_name:?}"
                    );
                }
                result => panic!("i128 ADD+ADC pair member should verify; got {result:?}"),
            }
        }
    }

    /// Same as above for the i128 SUB+SBB carry-chain pair.
    #[test]
    fn i128_sub_sbb_pair_binds_composition_proof_and_verifies() {
        let insts = vec![
            X86ISelInst::new(X86Opcode::SubRR, vec![gpr64(0), gpr64(1), gpr64(2)]),
            X86ISelInst::new(X86Opcode::SbbRR, vec![gpr64(3), gpr64(4), gpr64(5)]),
        ];
        let report = verify_x86_64_function(&make_func_with_insts(insts));
        assert_eq!(report.verified_count(), 2, "report was {report}");
        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified { proof_name, .. } => assert!(
                    proof_name.contains("Isub_I128 -> SUB lo; SBB hi"),
                    "i128 carry-chain member bound unexpected proof {proof_name:?}"
                ),
                result => panic!("i128 SUB+SBB pair member should verify; got {result:?}"),
            }
        }
    }

    /// SOUNDNESS NEGATIVE: a STANDALONE `ADC` (no preceding matching `ADD`) must
    /// NOT receive the i128 composition cert — its high-half proof would be
    /// unjustified without the low-half partner that sets CF. The carry-chain
    /// recognizer requires the adjacent pair, so a lone ADC stays unmatched by it
    /// and never binds `Iadd_I128 -> ADD lo; ADC hi`.
    #[test]
    fn standalone_adc_does_not_bind_i128_composition_proof() {
        // A lone ADC preceded by an unrelated MovRI (not an AddRR partner).
        let insts = vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![gpr64(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::AdcRR, vec![gpr64(1), gpr64(2), gpr64(3)]),
        ];
        let report = verify_x86_64_function(&make_func_with_insts(insts));
        // The carry-chain recognizer must not fire: the ADC's only candidate
        // pair-start is the MovRI, which is not an AddRR. So the lone ADC is NOT
        // credited via the composition proof.
        let adc_report = &report.instructions[1];
        if let InstructionVerificationResult::Verified { proof_name, .. } = &adc_report.result {
            assert!(
                !proof_name.contains("ADD lo; ADC hi"),
                "standalone ADC must not bind the i128 composition proof; bound {proof_name}"
            );
        }
    }

    #[test]
    fn ordinary_mov_memory_opcodes_bind_memory_proofs_never_atomic_ones() {
        let opcodes = [
            X86Opcode::MovRM8,
            X86Opcode::MovRM16,
            X86Opcode::MovRM32,
            X86Opcode::MovRM,
            X86Opcode::MovMR8,
            X86Opcode::MovMR16,
            X86Opcode::MovMR32,
            X86Opcode::MovMR,
            X86Opcode::Mfence,
        ];
        let report = verify_x86_64_function(&make_func_with_opcodes(&opcodes));
        assert_eq!(report.total(), opcodes.len());
        // Plain (origin-less) loads/stores bind the Load_/Store_ effective-
        // address memory proofs; Mfence still requires fence provenance.
        assert_eq!(
            report.verified_count(),
            opcodes.len() - 1,
            "plain loads/stores should bind their memory proofs; report was {report}"
        );
        assert_eq!(
            report.unverified_count(),
            1,
            "MFENCE without fence proof-origin must stay unverified; report was {report}"
        );
        // The original safety property, preserved: a generic MOV must NEVER
        // silently bind an ATOMIC proof without proof-origin metadata.
        for inst_report in &report.instructions {
            if let InstructionVerificationResult::Verified { proof_name, .. } = &inst_report.result
            {
                assert!(
                    !proof_name.contains("Atomic") && !proof_name.contains("Fence"),
                    "origin-less {} must not bind an atomic/fence proof; bound {proof_name}",
                    inst_report.opcode
                );
            }
        }
    }

    #[test]
    fn mismatched_atomic_proof_origin_does_not_bind_memory_mov_query() {
        for inst in [
            X86ISelInst::new(X86Opcode::MovMR, vec![])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::MovRM, vec![])
                .with_proof_origin(X86ProofOrigin::AtomicStore),
            X86ISelInst::new(X86Opcode::MovRM, vec![])
                .with_proof_origin(X86ProofOrigin::FenceSeqCst),
            X86ISelInst::new(X86Opcode::Mfence, vec![])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
        ] {
            assert_eq!(X86FunctionVerifier::instruction_to_proof_query(&inst), None);
        }
    }

    #[test]
    fn atomic_rmw_cas_loop_instruction_queries_use_op_kind() {
        assert_eq!(
            X86FunctionVerifier::instruction_to_proof_query(&atomic_rmw_cas_loop_inst(
                X86Opcode::AtomicRmwCasLoop,
                2,
                RegClass::Gpr64
            )),
            Some("AtomicRmwCasLoop_And_I64".to_string())
        );
        assert_eq!(
            X86FunctionVerifier::instruction_to_proof_query(&atomic_rmw_cas_loop_inst(
                X86Opcode::AtomicRmwCasLoop8,
                5,
                RegClass::Gpr32
            )),
            Some("AtomicRmwCasLoop8_Xchg_I8".to_string())
        );
        assert_eq!(
            X86FunctionVerifier::instruction_to_proof_query(&atomic_rmw_cas_loop_inst(
                X86Opcode::AtomicRmwCasLoop16,
                4,
                RegClass::Gpr32
            )),
            Some("AtomicRmwCasLoop16_Xor_I16".to_string())
        );
    }

    #[test]
    fn bitfield_sequence_queries_use_prepared_names() {
        let extract = extract_bits_i32_sequence();
        for idx in 0..extract.len() {
            assert_eq!(
                X86FunctionVerifier::bitfield_sequence_to_proof_query(&extract, idx),
                Some(X86_EXTRACT_BITS_I32_PROOF_QUERY),
                "extract sequence index {idx} should use prepared query"
            );
        }

        let sextract = sextract_bits_i32_sequence();
        for idx in 0..sextract.len() {
            assert_eq!(
                X86FunctionVerifier::bitfield_sequence_to_proof_query(&sextract, idx),
                Some(X86_SEXTRACT_BITS_I32_PROOF_QUERY),
                "signed extract sequence index {idx} should use prepared query"
            );
        }

        let insert = insert_bits_i32_sequence();
        for idx in 0..insert.len() {
            assert_eq!(
                X86FunctionVerifier::bitfield_sequence_to_proof_query(&insert, idx),
                Some(X86_INSERT_BITS_I32_PROOF_QUERY),
                "insert sequence index {idx} should use prepared query"
            );
        }
    }

    #[test]
    fn bitfield_sequence_query_ignores_other_windows() {
        let mut extract = extract_bits_i32_sequence();
        extract[0].operands[2] = X86ISelOperand::Imm(4);

        assert_eq!(
            X86FunctionVerifier::bitfield_sequence_to_proof_query(&extract, 2),
            None,
            "non-representative bitfield windows should keep opcode-level fallback"
        );
    }

    #[test]
    fn fcmp_sequence_queries_use_fcmp_proof_names() {
        let ge = fcmp_f64_ge_sequence();
        for idx in 0..ge.len() {
            assert_eq!(
                X86FunctionVerifier::fcmp_sequence_to_proof_query(&ge, idx),
                Some("Fcmp_GE_F64".to_string()),
                "F64 GE sequence index {idx} should bind to the FP compare proof"
            );
        }

        let uge = fcmp_f32_uge_sequence();
        for idx in 0..uge.len() {
            assert_eq!(
                X86FunctionVerifier::fcmp_sequence_to_proof_query(&uge, idx),
                Some("Fcmp_UGE_F32".to_string()),
                "F32 UGE sequence index {idx} should bind to the unordered FP compare proof"
            );
        }
    }

    #[test]
    fn division_sequence_queries_distinguish_quotient_and_remainder() {
        let udiv32 = div_result_sequence(X86Opcode::Div, X86Opcode::MovRR32, EAX);
        for idx in 0..udiv32.len() {
            assert_eq!(
                X86FunctionVerifier::division_sequence_to_proof_query(&udiv32, idx),
                Some("Udiv_I32".to_string()),
                "Udiv_I32 sequence index {idx} should bind to the quotient proof"
            );
        }

        let urem32 = div_result_sequence(X86Opcode::Div, X86Opcode::MovRR32, EDX);
        for idx in 0..urem32.len() {
            assert_eq!(
                X86FunctionVerifier::division_sequence_to_proof_query(&urem32, idx),
                Some("Urem_I32".to_string()),
                "Urem_I32 sequence index {idx} should bind to the remainder proof"
            );
        }

        let srem64 = div_result_sequence(X86Opcode::Idiv, X86Opcode::MovRR, RDX);
        for idx in 0..srem64.len() {
            assert_eq!(
                X86FunctionVerifier::division_sequence_to_proof_query(&srem64, idx),
                Some("Srem_I64".to_string()),
                "Srem_I64 sequence index {idx} should bind to the remainder proof"
            );
        }
    }

    #[test]
    fn division_sequence_queries_require_full_dividend_setup_and_width_match() {
        let tail_only = vec![
            X86ISelInst::new(X86Opcode::Div, vec![gpr32(0)]),
            X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![gpr32(1), X86ISelOperand::PReg(EDX)],
            ),
        ];
        for idx in 0..tail_only.len() {
            assert_eq!(
                X86FunctionVerifier::division_sequence_to_proof_query(&tail_only, idx),
                None,
                "a DIV tail without RDX:EAX setup must not be certified"
            );
        }

        let wrong_setup = vec![
            X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![X86ISelOperand::PReg(EAX), gpr32(0)],
            ),
            X86ISelInst::new(
                X86Opcode::XorRR,
                vec![
                    X86ISelOperand::PReg(RDX),
                    X86ISelOperand::PReg(RDX),
                    X86ISelOperand::PReg(RDX),
                ],
            ),
            X86ISelInst::new(X86Opcode::Div, vec![gpr32(1)]),
            X86ISelInst::new(
                X86Opcode::MovRR32,
                vec![gpr32(2), X86ISelOperand::PReg(EDX)],
            ),
        ];
        for idx in 0..wrong_setup.len() {
            assert_eq!(
                X86FunctionVerifier::division_sequence_to_proof_query(&wrong_setup, idx),
                None,
                "a 32-bit DIV must zero EDX, not RDX, before certification"
            );
        }

        let mismatched_copy = vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RAX), gpr64(0)]),
            X86ISelInst::new(X86Opcode::Cqo, vec![]),
            X86ISelInst::new(X86Opcode::Idiv, vec![gpr64(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![gpr64(2), X86ISelOperand::PReg(EDX)]),
        ];
        for idx in 0..mismatched_copy.len() {
            assert_eq!(
                X86FunctionVerifier::division_sequence_to_proof_query(&mismatched_copy, idx),
                None,
                "a 64-bit result copy from EDX must not bind to an I64 proof"
            );
        }
    }

    #[test]
    fn atomic_rmw_cas_loop_opcodes_verify_with_registered_proofs() {
        let func = make_func_with_insts(vec![
            atomic_rmw_cas_loop_inst(X86Opcode::AtomicRmwCasLoop, 0, RegClass::Gpr64),
            atomic_rmw_cas_loop_inst(X86Opcode::AtomicRmwCasLoop8, 5, RegClass::Gpr32),
            atomic_rmw_cas_loop_inst(X86Opcode::AtomicRmwCasLoop16, 4, RegClass::Gpr32),
        ]);
        let report = verify_x86_64_function(&func);
        assert_eq!(report.total(), 3);
        assert_eq!(
            report.verified_count(),
            3,
            "AtomicRmwCasLoop proofs should cover generic, byte, and word pseudos; report was {report}"
        );
        assert_eq!(report.unverified_count(), 0);
    }

    #[test]
    fn new_x86_queries_have_registered_proofs() {
        let db = ProofDatabase::new();
        let candidates = db.by_category(ProofCategory::X8664Lowering);

        for opcode in [
            X86Opcode::Cmovcc,
            X86Opcode::Cmovcc32,
            X86Opcode::MovdToXmm,
            X86Opcode::MovdFromXmm,
            X86Opcode::MovqToXmm,
            X86Opcode::MovqFromXmm,
            // #62: MovRI / Call / Ret degenerate X==X proofs retracted (now None);
            // they are tested as Unverified/allowlisted elsewhere.
            X86Opcode::MovRR,
            X86Opcode::MovRR32,
            X86Opcode::AtomicRmwCasLoop,
            X86Opcode::AtomicRmwCasLoop8,
            X86Opcode::AtomicRmwCasLoop16,
            // SSE FP conversions.
            X86Opcode::Cvtsi2sd,
            X86Opcode::Cvtsi2ss,
            X86Opcode::Cvttsd2si,
            X86Opcode::Cvttss2si,
            X86Opcode::Cvtsd2si,
            X86Opcode::Cvtss2si,
            X86Opcode::Cvtsd2ss,
            X86Opcode::Cvtss2sd,
            // Bit-manipulation.
            X86Opcode::Popcnt,
            X86Opcode::Tzcnt,
            X86Opcode::Lzcnt,
            X86Opcode::Bsf,
            X86Opcode::Bsr,
        ] {
            let query = X86FunctionVerifier::opcode_to_proof_query(opcode)
                .expect("new opcode must map to a proof query");
            assert!(
                candidates.iter().any(|p| p.obligation.name.contains(query)),
                "missing x86-64 proof matching {query:?} for {opcode:?}"
            );
        }

        for (inst, query) in [
            (
                X86ISelInst::new(
                    X86Opcode::LeaSib,
                    vec![
                        gpr64(0),
                        X86ISelOperand::SibMemAddr {
                            base: Box::new(gpr64(1)),
                            index: Box::new(gpr64(2)),
                            // #62: only the no-scale/no-disp SIB-LEA has a GENUINE
                            // proof; the scaled/displaced shapes were retracted.
                            scale: 1,
                            disp: 0,
                        },
                    ],
                ),
                "base+index -> LEA r64,[r64+r64]",
            ),
            (
                X86ISelInst::new(X86Opcode::MovRM8, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I8",
            ),
            (
                X86ISelInst::new(X86Opcode::MovRM16, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I16",
            ),
            (
                X86ISelInst::new(X86Opcode::MovRM32, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I32",
            ),
            (
                X86ISelInst::new(X86Opcode::MovRM, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicLoad),
                "AtomicLoad_I64",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR8, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I8",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR16, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I16",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR32, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I32",
            ),
            (
                X86ISelInst::new(X86Opcode::MovMR, vec![])
                    .with_proof_origin(X86ProofOrigin::AtomicStore),
                "AtomicStore_I64",
            ),
            // #62 retraction: the "Fence_* -> MFENCE" const proofs were removed,
            // so Mfence no longer binds a per-instruction value-proof here.
        ] {
            let actual_query = X86FunctionVerifier::instruction_to_proof_query(&inst)
                .expect("proof-origin instruction must map to a proof query");
            assert_eq!(actual_query, query);
            assert!(
                candidates.iter().any(|p| p.obligation.name.contains(query)),
                "missing x86-64 proof matching {query:?} for {:?}",
                inst.opcode
            );
        }
    }

    #[test]
    fn movrr_and_leasib_instructions_verify_with_registered_proofs() {
        let func = make_func_with_insts(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![]),
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![
                    gpr64(0),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(gpr64(1)),
                        index: Box::new(gpr64(2)),
                        // #62: only the no-scale/no-disp SIB-LEA keeps a GENUINE proof.
                        scale: 1,
                        disp: 0,
                    },
                ],
            ),
        ]);
        let report = verify_x86_64_function(&func);

        assert_eq!(report.total(), 3);
        assert_eq!(
            report.verified_count(),
            3,
            "MOVRR copies and the no-scale/no-disp LEASIB opcode should have registered proofs; report was {report}"
        );
        assert_eq!(report.unverified_count(), 0);
    }

    #[test]
    fn lea_shapes_are_reconstruction_verified_with_real_ea_operands() {
        let func = make_func_with_insts(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    gpr64(0),
                    X86ISelOperand::MemAddr {
                        base: Box::new(gpr64(1)),
                        disp: 8,
                    },
                ],
            ),
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![
                    gpr64(2),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(gpr64(3)),
                        index: Box::new(gpr64(4)),
                        scale: 2,
                        disp: 8,
                    },
                ],
            ),
            X86ISelInst::new(
                X86Opcode::LeaRip,
                vec![gpr64(5), X86ISelOperand::Symbol("global".to_string())],
            ),
        ]);
        let report = verify_x86_64_function(&func);

        assert_eq!(report.total(), 3);
        // The plain LEA [base+disp] and the scaled/displaced SIB-LEA are now
        // RECONSTRUCTED: the machine side is rebuilt from the real EA encoder over
        // fresh symbolic base/index, and a wrong scale/disp refutes (see the
        // inject-wrong-scale/disp refutation tests). The retracted degenerate X==X
        // EA "proofs" are no longer relied on. All three verify (LeaRip via its
        // genuine RIP-relative SIGNED symbol-address proof).
        assert_eq!(report.verified_count(), 3, "report was {report}");
        assert_eq!(report.unverified_count(), 0, "report was {report}");
        match &report.instructions[0].result {
            InstructionVerificationResult::Verified { proof_name, .. } => assert!(
                proof_name.contains("RECONSTRUCTED x86_64 EffectiveAddress")
                    && proof_name.contains("base+disp"),
                "plain LEA [base+disp] must be reconstruction-verified; bound {proof_name}"
            ),
            other => panic!("plain LEA [base+disp] should reconstruct-verify; got {other:?}"),
        }
        match &report.instructions[1].result {
            InstructionVerificationResult::Verified { proof_name, .. } => assert!(
                proof_name.contains("RECONSTRUCTED x86_64 EffectiveAddress")
                    && proof_name.contains("base+index*scale+disp"),
                "scaled/displaced SIB LEA must be reconstruction-verified; bound {proof_name}"
            ),
            other => panic!("scaled SIB LEA should reconstruct-verify; got {other:?}"),
        }
        // LeaRip is PROVEN-promotable: it composes the per-instruction RIP-relative
        // effective address with the proven SIGNED relocation displacement to
        // materialize the in-module symbol address S + A.
        match &report.instructions[2].result {
            InstructionVerificationResult::Verified { proof_name, .. } => assert!(
                proof_name.contains("LeaRip Symbol -> RIP_next + SIGNED disp32 == S + A"),
                "LeaRip should bind its RIP-relative SIGNED symbol-address proof; bound {proof_name}"
            ),
            other => panic!("LeaRip should verify (RIP-relative proof registered); got {other:?}"),
        }
    }

    #[test]
    fn movriprel_symbol_verifies_with_registered_got_load_proof() {
        let func = make_func_with_insts(vec![X86ISelInst::new(
            X86Opcode::MovRipRel,
            vec![
                gpr64(0),
                X86ISelOperand::Symbol("extern_global".to_string()),
            ],
        )]);
        let report = verify_x86_64_function(&func);

        assert_eq!(report.total(), 1);
        assert_eq!(report.verified_count(), 1, "report was {report}");
        match &report.instructions[0].result {
            InstructionVerificationResult::Verified { proof_name, .. } => assert!(
                proof_name.contains("MovRipRel Symbol -> RIP_next + GOT_LOAD disp32 == G + A"),
                "MovRipRel should bind its RIP-relative GOT_LOAD proof; bound {proof_name}"
            ),
            other => panic!("MovRipRel should verify (GOT_LOAD proof registered); got {other:?}"),
        }
    }

    #[test]
    fn riprel_symbol_negative_controls_refute() {
        use crate::lowering_proof::verify_by_evaluation;
        use crate::verify::VerificationResult;
        // A LeaRip whose disp is mis-encoded (ABSOLUTE not RIP-relative, or the
        // wrong reference end) must REFUTE — proving the positive proofs are
        // real equivalences and the RIP-relative provenance is load-bearing,
        // not a tautological `x == x` admission.
        for obligation in crate::x86_64_lowering_proofs::x86_64_riprel_symbol_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "RIP-relative negative control '{}' should REFUTE (a wrong RIP encoding must be \
                 rejected), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn fcmp_and_remainder_sequences_verify_with_registered_proofs() {
        let func = make_func_with_insts(
            fcmp_f64_ge_sequence()
                .into_iter()
                .chain(div_result_sequence(X86Opcode::Div, X86Opcode::MovRR32, EDX))
                .chain(div_result_sequence(X86Opcode::Idiv, X86Opcode::MovRR, RDX))
                .collect(),
        );
        let report = verify_x86_64_function(&func);
        assert_eq!(
            report.unverified_count(),
            0,
            "FP compare and remainder sequences should have registered proofs; report was {report}"
        );
        assert_eq!(
            report.verified_count(),
            report.total(),
            "all emitted sequence instructions should be covered; report was {report}"
        );

        for idx in 3..7 {
            match &report.instructions[idx].result {
                InstructionVerificationResult::Verified { proof_name, .. } => assert!(
                    proof_name.contains("Urem_I32"),
                    "division sequence index {idx} should use Urem_I32 proof, got {proof_name}"
                ),
                other => panic!("division sequence index {idx} should verify, got {other:?}"),
            }
        }
        for idx in 7..11 {
            match &report.instructions[idx].result {
                InstructionVerificationResult::Verified { proof_name, .. } => assert!(
                    proof_name.contains("Srem_I64"),
                    "division sequence index {idx} should use Srem_I64 proof, got {proof_name}"
                ),
                other => panic!("division sequence index {idx} should verify, got {other:?}"),
            }
        }
    }

    fn single_inst_proof(inst: X86ISelInst) -> (String, ProofCategory) {
        let report = verify_x86_64_function(&make_func_with_insts(vec![inst.clone()]));
        match &report.instructions[0].result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                ..
            } => (proof_name.clone(), *category),
            other => panic!("{:?} should verify; got {other:?}", inst.opcode),
        }
    }

    /// SOUNDNESS REGRESSION (reviewer scenario): the byte/word MOVSX/MOVZX
    /// opcodes encode i*->i64 (REX.W) yet the verifier previously queried only
    /// the i32 proof, so an i64-MOVSX/MOVZX bug would pass against an i32 proof.
    /// With a Gpr64 destination the verifier MUST bind the i64-width proof; with
    /// a Gpr32 destination it must bind the i32-width proof.
    ///
    /// POST-#66: these extends now route through OPERAND RECONSTRUCTION (which
    /// rebuilds the machine side from the real `MOVSX/MOVZX` operands). The
    /// width-correctness invariant is PRESERVED — the reconstructed obligation
    /// embeds the encoded `to_bits` from the destination register class, so a
    /// Gpr64 dst reconstructs `…_to_64` and a Gpr32 dst `…_to_32`. We assert the
    /// reconstructed width-correct binding (a wrong-width or wrong-sign extend
    /// would refute under reconstruction, per tests/reconstruction_x86.rs).
    #[test]
    fn movsx_movzx_bind_width_correct_proof_by_dst_class() {
        // 64-bit destinations -> i64-width (to_64) reconstructed extension.
        for (opcode, want) in [
            (X86Opcode::MovsxB, "Sextend_8_to_64"),
            (X86Opcode::MovsxW, "Sextend_16_to_64"),
            (X86Opcode::Movzx, "Uextend_8_to_64"),
            (X86Opcode::MovzxW, "Uextend_16_to_64"),
        ] {
            let (proof_name, _) =
                single_inst_proof(X86ISelInst::new(opcode, vec![gpr64(0), gpr32(1)]));
            assert!(
                proof_name.contains("RECONSTRUCTED") && proof_name.contains(want),
                "{opcode:?} with Gpr64 dst must reconstruct {want:?} (to_64 = encoded width), got {proof_name}"
            );
            assert!(
                !proof_name.contains("to_32"),
                "{opcode:?} with Gpr64 dst must NOT bind an i32 extension proof, got {proof_name}"
            );
        }

        // 32-bit destinations -> i32-width (to_32) reconstructed extension. (The
        // byte/word source occupies a Gpr32 register; the dst is Gpr32.)
        for (opcode, want) in [
            (X86Opcode::MovsxB, "Sextend_8_to_32"),
            (X86Opcode::MovsxW, "Sextend_16_to_32"),
            (X86Opcode::Movzx, "Uextend_8_to_32"),
            (X86Opcode::MovzxW, "Uextend_16_to_32"),
        ] {
            let (proof_name, _) =
                single_inst_proof(X86ISelInst::new(opcode, vec![gpr32(0), gpr32(1)]));
            assert!(
                proof_name.contains("RECONSTRUCTED") && proof_name.contains(want),
                "{opcode:?} with Gpr32 dst must reconstruct {want:?}, got {proof_name}"
            );
        }
    }

    /// SOUNDNESS REGRESSION (reviewer scenario): the GEP path emits 3-operand
    /// IMUL with a Gpr64 destination (IMUL r64). ImulRRI is now RECONSTRUCTED
    /// from the real operands: the reconstruction reads the dst register width, so
    /// the obligation is genuinely width-correct (a 64-bit IMUL-imm bug would
    /// refute against the 64-bit source `Imul`). The bound proof is the
    /// width-tagged reconstruction, NOT the degenerate `Imul_I*_Imm` DB proof.
    #[test]
    fn imul_rri_binds_width_correct_proof_by_dst_class() {
        let (i64_name, category) = single_inst_proof(X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![gpr64(0), gpr64(1), X86ISelOperand::Imm(42)],
        ));
        assert_eq!(category, ProofCategory::X8664Lowering);
        assert!(
            i64_name.contains("RECONSTRUCTED")
                && i64_name.contains("Imul_64")
                && i64_name.contains("ImulRRI"),
            "ImulRRI with Gpr64 dst (the GEP path) must bind the width-64 reconstruction, \
             got {i64_name}"
        );

        let (i32_name, _) = single_inst_proof(X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![gpr32(0), gpr32(1), X86ISelOperand::Imm(42)],
        ));
        assert!(
            i32_name.contains("RECONSTRUCTED") && i32_name.contains("Imul_32"),
            "ImulRRI with Gpr32 dst must bind the width-32 reconstruction, got {i32_name}"
        );
    }

    /// RESIDUAL B (post-#66): the i64 byte/word MOVSX/MOVZX extends now resolve via
    /// OPERAND RECONSTRUCTION, which the verifier categorizes under `X8664Lowering`
    /// (the x86-specific lowering category). The reconstructed obligation is built
    /// from the real `MOVSX/MOVZX` operands and embeds the encoded `to_64` width,
    /// so the cert is attributed to an x86-specific, width-correct reconstruction
    /// of the instruction it encodes (a wrong-width/sign extend would refute).
    #[test]
    fn i64_byte_word_extend_resolves_in_x86_lowering_category() {
        for opcode in [
            X86Opcode::MovsxB,
            X86Opcode::MovsxW,
            X86Opcode::Movzx,
            X86Opcode::MovzxW,
        ] {
            let (proof_name, category) =
                single_inst_proof(X86ISelInst::new(opcode, vec![gpr64(0), gpr32(1)]));
            assert_eq!(
                category,
                ProofCategory::X8664Lowering,
                "{opcode:?} i64 extend should resolve under the x86 X8664Lowering category"
            );
            // And it must be the width-correct reconstruction of the real opcode.
            assert!(
                proof_name.contains("RECONSTRUCTED")
                    && proof_name.contains("to_64")
                    && proof_name.contains(&format!("{opcode:?}")),
                "{opcode:?} i64 extend must bind the reconstructed to_64 obligation, got {proof_name}"
            );
        }
    }

    /// Width-polymorphic MOVSX/MOVZX/IMUL must fail CLOSED when the destination
    /// width cannot be determined (no register dst operand): they must not fall
    /// back to the fixed-width opcode query, which would re-introduce the
    /// i32-proof-for-i64-op unsoundness.
    #[test]
    fn width_polymorphic_extend_imul_fails_closed_without_dst_class() {
        for opcode in [
            X86Opcode::MovsxB,
            X86Opcode::MovsxW,
            X86Opcode::Movzx,
            X86Opcode::MovzxW,
            X86Opcode::ImulRRI,
        ] {
            assert_eq!(
                X86FunctionVerifier::instruction_to_proof_query(&X86ISelInst::new(opcode, vec![])),
                None,
                "{opcode:?} without a typed dst must not bind a fixed-width proof"
            );
            let report = verify_x86_64_function(&make_func_with_opcodes(&[opcode]));
            assert_eq!(
                report.unverified_count(),
                1,
                "{opcode:?} without a typed dst must stay Unverified (fail closed)"
            );
        }
    }

    // =======================================================================
    // TV-2: provenance cross-check (see crate::provenance_xcheck)
    // =======================================================================

    use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};
    use trust_cg_lower::instructions::{Instruction, Opcode as LirOpcode, Value};
    use trust_cg_lower::types::Type;

    /// LIR function named `test` (matching `make_func_with_insts`) with block
    /// 0 = `[Iconst, Iadd, Imul, Return]`.
    fn tv2_lir_function() -> trust_cg_lower::Function {
        let mut lir = trust_cg_lower::Function::new(
            "test",
            Signature {
                params: vec![Type::I64, Type::I64],
                returns: vec![Type::I64],
            },
        );
        let block = Block(0);
        lir.block_order.push(block);
        lir.blocks.insert(
            block,
            trust_cg_lower::function::BasicBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: LirOpcode::Iconst {
                            ty: Type::I64,
                            imm: 7,
                        },
                        args: vec![],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: LirOpcode::Iadd,
                        args: vec![Value(0), Value(2)],
                        results: vec![Value(3)],
                    },
                    Instruction {
                        opcode: LirOpcode::Imul,
                        args: vec![Value(3), Value(1)],
                        results: vec![Value(4)],
                    },
                    Instruction {
                        opcode: LirOpcode::Return,
                        args: vec![Value(4)],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        lir
    }

    /// A faithful TV-1 stamp for the LIR instruction at `(block, index)`.
    fn tv2_stamp(lir: &trust_cg_lower::Function, block: u32, index: u32) -> LoweringProvenance {
        let inst = &lir.blocks[&Block(block)].instructions[index as usize];
        LoweringProvenance::SourceInst {
            id: SourceInstId { block, index },
            digest: inst.lowering_digest(),
            trust_ir_inst: None,
        }
    }

    /// An `ADD dst, a, b` instruction carrying the given provenance stamp.
    fn tv2_add_rr_with_stamp(stamp: LoweringProvenance) -> X86ISelInst {
        let mut inst = X86ISelInst::new(X86Opcode::AddRR, vec![gpr64(0), gpr64(1), gpr64(2)]);
        inst.lowering_provenance = stamp;
        inst
    }

    /// An `IMUL dst, a, b` instruction carrying the given provenance stamp.
    fn tv2_imul_rr_with_stamp(stamp: LoweringProvenance) -> X86ISelInst {
        let mut inst = X86ISelInst::new(X86Opcode::ImulRR, vec![gpr64(0), gpr64(1), gpr64(2)]);
        inst.lowering_provenance = stamp;
        inst
    }

    fn tv2_provenance_failure(report: &FunctionVerificationReport) -> bool {
        report.instructions.iter().any(|r| {
            matches!(
                &r.result,
                InstructionVerificationResult::Failed { proof_name, .. }
                    if proof_name == "provenance-crosscheck (TV-2)"
            )
        })
    }

    /// PINNED TV-2 REFUTATION (gate rollout protocol step c): an `IMUL` whose
    /// stamp claims it lowers the `Iadd` at (0,1) — the digest is genuinely
    /// the Iadd's, so only the op-class cross-check can catch it — must FAIL
    /// CLOSED through the DEFAULT public entry point (x86-64 default mode is
    /// ENFORCE). This test fails if the cross-check is commented out or its
    /// default is weakened.
    ///
    /// NB: "an ADD stamped as from an Imul" is deliberately NOT the refutation
    /// example. The i128 multiply expansion (`select_i128_mul`) legitimately
    /// emits partial-product ADDs stamped with the Imul anchor, so
    /// `compatible(IntMul, IntAdd)` holds and an ADD cannot serve as a wrong
    /// source for a multiply here (the warn-only corpus run surfaced 82 such
    /// benign emissions). The unambiguously-wrong direction is an integer
    /// MULTIPLY emitted while lowering an integer ADD — `!compatible(IntAdd,
    /// IntMul)`, no add lowering ever needs a multiply.
    #[test]
    fn tv2_imul_stamped_as_iadd_fails_closed_by_default() {
        let lir = tv2_lir_function();
        let func = make_func_with_insts(vec![tv2_imul_rr_with_stamp(tv2_stamp(&lir, 0, 1))]);
        let report = X86FunctionVerifier::new().verify_with_lir_source(&func, Some(&lir));
        assert!(
            tv2_provenance_failure(&report),
            "an IMUL stamped as lowering an Iadd must fail the provenance cross-check: {:?}",
            report.instructions
        );
        assert!(!report.all_verified());
    }

    /// Same wrong stamp, explicit warn-only mode: the mismatch is COUNTED and
    /// reported but no verdict is demoted (§2.4 phase-a telemetry behavior).
    #[test]
    fn tv2_wrong_stamp_warn_mode_counts_without_demoting() {
        let lir = tv2_lir_function();
        let func = make_func_with_insts(vec![tv2_imul_rr_with_stamp(tv2_stamp(&lir, 0, 1))]);
        let hits_before = crate::provenance_xcheck::provenance_xcheck_hit_count();
        let report = X86FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Warn,
        );
        assert!(
            !tv2_provenance_failure(&report),
            "warn-only mode must not demote verdicts"
        );
        assert!(
            crate::provenance_xcheck::provenance_xcheck_hit_count() > hits_before,
            "warn-only mode must still count the mismatch"
        );
    }

    /// A faithful stamp (the ADD really lowers the Iadd at (0,1)) passes the
    /// cross-check in enforce mode — no false fail-closed.
    #[test]
    fn tv2_faithful_stamp_passes_enforce() {
        let lir = tv2_lir_function();
        let func = make_func_with_insts(vec![tv2_add_rr_with_stamp(tv2_stamp(&lir, 0, 1))]);
        let report = X86FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(
            !tv2_provenance_failure(&report),
            "a faithful stamp must pass: {:?}",
            report.instructions
        );
    }

    /// A stamp whose digest does not match the instruction at its coordinates
    /// (points at the Iconst, carries the Imul's digest) fails closed.
    #[test]
    fn tv2_digest_mismatch_fails_closed() {
        let lir = tv2_lir_function();
        let imul_digest = lir.blocks[&Block(0)].instructions[2].lowering_digest();
        let stamp = LoweringProvenance::SourceInst {
            id: SourceInstId { block: 0, index: 0 },
            digest: imul_digest,
            trust_ir_inst: None,
        };
        let func = make_func_with_insts(vec![tv2_add_rr_with_stamp(stamp)]);
        let report = X86FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(tv2_provenance_failure(&report));
    }

    /// A stamp pointing at coordinates that do not exist in the replayed LIR
    /// function (a dangling attribution) fails closed.
    #[test]
    fn tv2_dangling_stamp_fails_closed() {
        let lir = tv2_lir_function();
        let stamp = LoweringProvenance::SourceInst {
            id: SourceInstId { block: 9, index: 9 },
            digest: SourceInstDigest::compute("Iadd", 2, 1),
            trust_ir_inst: None,
        };
        let func = make_func_with_insts(vec![tv2_add_rr_with_stamp(stamp)]);
        let report = X86FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(tv2_provenance_failure(&report));
    }

    /// Synthetic/Unattributed instructions (pass-created, prologue/ABI glue)
    /// are exempt from the cross-check by contract.
    #[test]
    fn tv2_unattributed_insts_are_exempt() {
        let lir = tv2_lir_function();
        // Default X86ISelInst provenance is UNATTRIBUTED.
        let func = make_func_with_insts(vec![X86ISelInst::new(
            X86Opcode::AddRR,
            vec![gpr64(0), gpr64(1), gpr64(2)],
        )]);
        let report = X86FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(!tv2_provenance_failure(&report));
    }

    /// Without a replayed LIR function the cross-check cannot run and plain
    /// `verify` behaves exactly as before (no verdict change).
    #[test]
    fn tv2_no_lir_source_means_no_crosscheck() {
        let lir = tv2_lir_function();
        let func = make_func_with_insts(vec![tv2_add_rr_with_stamp(tv2_stamp(&lir, 0, 2))]);
        let report = X86FunctionVerifier::new().verify(&func);
        assert!(!tv2_provenance_failure(&report));
    }
}
