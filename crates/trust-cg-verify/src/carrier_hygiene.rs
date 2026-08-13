// trust-cg-verify/carrier_hygiene.rs - carrier-hygiene invariant checker (P1.2)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: MISCOMPILE #51 (SAR/IDIV need sign-ext of a dirty narrow operand)
// Reference: MISCOMPILE #66 (SHR/unsigned-DIV need zero-ext of a dirty narrow operand)
// Reference: trust-cg-lower/src/x86_64_isel.rs::select_div / select_shift
//            (the ISel sites whose sign_extend_narrow_operand /
//             zero_extend_narrow_operand calls this checker re-derives)

//! Carrier-hygiene invariant checker for the x86-64 ISel machine IR.
//!
//! # The invariant
//!
//! Sub-32-bit integer values (`i8`/`i16`) live in 32-bit GPR *carriers* on
//! x86-64. The ISA has no native 8/16-bit arithmetic encoding for most
//! operations, so the pipeline runs them at the 32-bit carrier width. After a
//! 32-bit `NOT`/`NEG`/`SUB`/`ADD` of such a value, the **high carrier bits are
//! DIRTY** — e.g. `!8u8` lowers to `notl` and leaves `0xFFFFFFF7`, whose top 24
//! bits are 1, not the zero/​sign-extension of the true `i8` value `0xF7`.
//!
//! Most consumers only read back the low `width` bits, so dirty high bits never
//! reach the result. But a handful of x86 instructions read the *entire* 32-bit
//! carrier even when the program value is narrower:
//!
//!   * `SAR`/`IDIV` interpret the carrier as a **sign-extended** value. Feeding
//!     them a zero-extended-then-dirtied carrier silently miscompiles signed
//!     `>>` / `/` / `%` (MISCOMPILE #51).
//!   * `SHR`/`DIV` interpret the carrier as a **zero-extended** value. Feeding
//!     them a dirtied carrier shifts/divides garbage high bits (MISCOMPILE #66:
//!     `!8u8 >> 3 == 0xFE`, not `0x1E`; `65528u16 % 7 == 3`, not `1`).
//!
//! The ISel fix (`sign_extend_narrow_operand` / `zero_extend_narrow_operand`)
//! inserts a `MOVSX`/`MOVZX` immediately before the consumer so the carrier is
//! provably extended. This module turns that ISel *precondition* into a checked
//! *invariant over the emitted machine IR*: a forward abstract interpretation
//! computes, for every VReg, what is provably true about its high carrier bits,
//! and a check pass asserts that every wide-reading consumer's source operand is
//! in the lattice state its semantics require.
//!
//! # Width-aware extension proofs
//!
//! A proof is not merely *that* the carrier was extended but *from which width*.
//! A `MOVSX r, r/m16` (`SignExt(16)`) sign-extends bit 15 — it preserves bits
//! `8..=15` verbatim, which for an `i8` consumer are *garbage* (the dirty high
//! bits of the i8). So a `SignExt(16)` does **not** satisfy an `i8` (8-bit)
//! consumer. The acceptance test is width-aware: a proven extension at width `w`
//! satisfies a consumer of nominal width `n` only when `w <= n` (the proven
//! clean region `[w, carrier)` then covers the region `[n, carrier)` the
//! consumer reads, with the correct polarity). See [`HighBits`].
//!
//! # Why machine IR, not trust_ir
//!
//! MISCOMPILE #51/#66 lived *downstream* of the SMT-verified per-instruction
//! lowering core: the individual `SarRI`/`Idiv` lowerings were each provably
//! correct *given a correctly-extended operand*, but nothing checked that the
//! operand actually was extended. The bug is a property of the instruction
//! *stream*, so the checker must run over the stream (`X86ISelFunction`), not
//! over isolated `ProofObligation`s.
//!
//! # Placement
//!
//! Lives in `trust-cg-verify` (not `trust-cg-ir`/`trust-cg-codegen`) because it
//! is a verification checker analogous to `x86_64_function_verifier`, and
//! `trust-cg-verify` already depends on both `trust-cg-lower` (the
//! `X86ISelInst`/`X86ISelFunction` types) and `trust-cg-ir` (the `X86Opcode`
//! surface). No new dependency edge is introduced.
//!
//! # Wiring status
//!
//! This checker is **wired into the live production verification path**
//! (`x86_64_function_verifier::verify`). After the per-instruction proof walk,
//! the verifier runs [`check_function`] over the same [`X86ISelFunction`],
//! seeded with [`NominalWidths::from_value_type_widths`] from the per-VReg
//! nominal-width map ISel records during selection and exposes via
//! `X86ISelFunction::vreg_nominal_widths()`. Any [`CarrierHygieneViolation`]
//! demotes the offending instruction's report to `Failed`, so the function
//! fails closed (`all_verified()` becomes false) — the invariant now runs on
//! emitted code, not just from these standalone integration tests.
//!
//! Callers MUST supply a complete width map: an operand absent from the map is
//! treated as a possibly-narrow value and checked fail-closed (see
//! [`NominalWidths::width_of`]), never silently blessed. ISel records the width
//! of every GPR-carrier def (including the MOVSX/MOVZX-extended divisor/shiftee
//! and the signed-division CMOV scratch divisor) so the genuine, correctly
//! extended wide-reader operands are not false-rejected.

use std::collections::{HashMap, HashSet};

use trust_cg_ir::regs::VReg;

/// A fast, deterministic hasher for `VReg`-keyed dataflow maps. The carrier
/// hygiene fixpoint clones/joins/compares a `VReg -> HighBits` map per block
/// visit over a function that can lower to hundreds of blocks; the default
/// SipHash (`RandomState`) on the small `VReg` key dominated that inner loop
/// (~half of a proofs-off compile). This is the standard rustc-hash / FxHash
/// mix — a rotate-xor-multiply per written word. It changes only hashing SPEED
/// and (unlike the randomly-seeded default) makes iteration order DETERMINISTIC;
/// the map CONTENTS, every `get`, the union-meet `join_into`, and map equality
/// are byte-identical, so the checker's verdict is unchanged.
#[derive(Default)]
struct FxHasher {
    hash: u64,
}
const FX_SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;
impl FxHasher {
    #[inline]
    fn add(&mut self, i: u64) {
        self.hash = (self.hash.rotate_left(5) ^ i).wrapping_mul(FX_SEED);
    }
}
impl std::hash::Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.add(b as u64);
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    #[inline]
    fn write_i8(&mut self, i: i8) {
        self.add(i as u64);
    }
    #[inline]
    fn write_i16(&mut self, i: i16) {
        self.add(i as u64);
    }
    #[inline]
    fn write_i32(&mut self, i: i32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_i64(&mut self, i: i64) {
        self.add(i as u64);
    }
    #[inline]
    fn write_isize(&mut self, i: isize) {
        self.add(i as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}
/// `VReg -> HighBits` dataflow map keyed by the fast deterministic hasher above.
type BitsMap = std::collections::HashMap<VReg, HighBits, std::hash::BuildHasherDefault<FxHasher>>;
use trust_cg_ir::x86_64_ops::X86Opcode;

use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

// ---------------------------------------------------------------------------
// High-bits lattice
// ---------------------------------------------------------------------------

/// Abstract description of a carrier register's high bits at a program point.
///
/// The carrier is always a 32- or 64-bit GPR. `width` records the *meaningful*
/// low-bit width whose extension is proven; bits at and above `width` are known
/// to be the zero/sign extension of bit `width-1` (for `ZeroExt`/`SignExt`) or
/// both extensions simultaneously (for `Full`).
///
/// Lattice order (⊑ = "is at least as precise as"; `Top` is least precise):
///
/// ```text
///                 Top  (Dirty / unknown high bits)
///                /  \
///      ZeroExt(w)    SignExt(w)
///                \  /
///               Full(w)        (bits >= w are simultaneously the zero AND the
///                               sign extension; for w == carrier the whole
///                               carrier is the value)
/// ```
///
/// `Full(w)` is the meet of `ZeroExt(w)` and `SignExt(w)`: bits `>= w` are *both*
/// zero and equal to bit `w-1` (which therefore forces bit `w-1` itself to 0 when
/// `w < carrier`, i.e. a non-negative value occupying the low `w-1` bits; for
/// `w == carrier` the relation is vacuous so any carrier value qualifies — the
/// "whole carrier is the value" case). A `Full(w)` consequently satisfies *both*
/// a signed and an unsigned consumer of any nominal width `n >= w`.
///
/// The join (meet-towards-Top used at control-flow merges) of two unequal
/// non-`Top` states is `Top`, except that `Full(w)` refines to whichever of
/// `ZeroExt`/`SignExt` the other branch proved (a value that is both zero- and
/// sign-extended to `w` is trivially still the weaker of the two).
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub enum HighBits {
    /// High bits are dirty or unknown. No extension is proven.
    Top,
    /// Bits `>= width` are all zero (logical zero-extension of a `width`-bit value).
    ZeroExt(u32),
    /// Bits `>= width` replicate bit `width-1` (arithmetic sign-extension).
    SignExt(u32),
    /// Bits `>= width` are simultaneously the zero AND the sign extension; for
    /// `width == carrier` the whole carrier is the value. This is the lattice
    /// meet of `ZeroExt(width)` and `SignExt(width)`.
    Full(u32),
}

impl HighBits {
    /// Does this state prove the operand is zero-extended for a consumer that
    /// reads the full carrier as an unsigned value (e.g. `SHR`/`DIV`)?
    ///
    /// `nominal` is the consumer's nominal value width (the number of meaningful
    /// low bits); `carrier` is the physical carrier width (32/64). The proof is
    /// width-aware: a `ZeroExt(w)` (bits `>= w` are zero) satisfies an `n`-bit
    /// consumer iff `w <= n`, because only then does the proven-clean region
    /// `[w, carrier)` cover the region `[n, carrier)` the consumer reads. A
    /// `ZeroExt(16)` therefore does NOT satisfy an `i8` consumer — bits `8..=15`
    /// are unconstrained by the proof and would be read as garbage.
    fn proves_zero_extended(self, nominal: u32, carrier: u32) -> bool {
        match self {
            HighBits::ZeroExt(w) | HighBits::Full(w) => w <= nominal && w <= carrier,
            _ => false,
        }
    }

    /// Does this state prove the operand is sign-extended for a consumer that
    /// reads the full carrier as a signed value (e.g. `SAR`/`IDIV`)?
    ///
    /// Width-aware mirror of [`proves_zero_extended`](Self::proves_zero_extended):
    /// a `SignExt(w)` satisfies an `n`-bit consumer iff `w <= n`. A `SignExt(16)`
    /// feeding an `i8` consumer is rejected — it sign-extends bit 15, leaving the
    /// i8's dirty bits `8..=15` in place rather than the sign of bit 7.
    fn proves_sign_extended(self, nominal: u32, carrier: u32) -> bool {
        match self {
            HighBits::SignExt(w) | HighBits::Full(w) => w <= nominal && w <= carrier,
            _ => false,
        }
    }

    /// Conservative control-flow join (move towards `Top`).
    fn join(self, other: HighBits) -> HighBits {
        use HighBits::*;
        match (self, other) {
            (a, b) if a == b => a,
            // Full(w) is simultaneously zero- and sign-extended to w, so it
            // refines to the other branch's narrower proof when widths agree.
            (Full(w), ZeroExt(z)) | (ZeroExt(z), Full(w)) if w == z => ZeroExt(z),
            (Full(w), SignExt(s)) | (SignExt(s), Full(w)) if w == s => SignExt(s),
            _ => Top,
        }
    }
}

// ---------------------------------------------------------------------------
// Violation reporting
// ---------------------------------------------------------------------------

/// Which extension a wide-reading consumer requires of its source operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub enum RequiredExtension {
    /// Consumer reads the full carrier as unsigned (`SHR`/`DIV`): needs zero-ext.
    Zero,
    /// Consumer reads the full carrier as signed (`SAR`/`IDIV`): needs sign-ext.
    Sign,
}

/// A single carrier-hygiene violation: a wide-reading consumer whose source
/// operand is not provably in the lattice state its semantics require.
///
/// `Serialize` is derived purely for the AI-usability diagnostics layer
/// (`crate::diag`): it lets a fail-closed event emit its typed fields as JSON.
/// The derive is additive — it changes no field and no gate decision. The
/// `opcode`/`operand` fields hold `trust-cg-ir` types that do not derive
/// `Serialize`, so they are rendered through their stable `Debug` form (e.g.
/// `"Idiv"`, `"v12"`) via `serialize_with`; everything else serializes directly.
#[derive(Debug, Clone, PartialEq, serde::Serialize)]
pub struct CarrierHygieneViolation {
    /// Block in which the violating instruction lives (`X86ISelBlock` key id).
    pub block: u32,
    /// Index of the violating instruction within its block's `insts` vector.
    pub inst_index: usize,
    /// The consuming opcode (e.g. `Idiv`, `SarRI`, `Div`, `ShrRR`).
    #[serde(serialize_with = "serialize_via_debug")]
    pub opcode: X86Opcode,
    /// The source operand VReg whose carrier hygiene could not be proven.
    #[serde(serialize_with = "serialize_via_debug")]
    pub operand: VReg,
    /// The extension the consumer's semantics require.
    pub required: RequiredExtension,
    /// The lattice state actually proven for `operand` at this point.
    pub actual: HighBits,
    /// Human-readable explanation referencing the historical miscompile class.
    pub detail: String,
}

/// Serialize any `Debug` value as its `Debug` string. Used for the `trust-cg-ir`
/// `X86Opcode`/`VReg` fields of [`CarrierHygieneViolation`], which do not derive
/// `Serialize` themselves; their `Debug` form is the stable textual identity the
/// diagnostics layer needs. Diagnostics-only — never on a codegen path.
fn serialize_via_debug<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
where
    T: std::fmt::Debug,
    S: serde::Serializer,
{
    serializer.serialize_str(&format!("{value:?}"))
}

/// The result of running the carrier-hygiene checker over a function.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct CarrierHygieneReport {
    /// Function name, for diagnostics.
    pub function: String,
    /// Every detected violation, in block-order / instruction-order.
    pub violations: Vec<CarrierHygieneViolation>,
}

impl CarrierHygieneReport {
    /// True iff no violations were found (the invariant holds for the function).
    pub fn is_clean(&self) -> bool {
        self.violations.is_empty()
    }

    /// Number of violations found.
    pub fn violation_count(&self) -> usize {
        self.violations.len()
    }
}

// ---------------------------------------------------------------------------
// Operand helpers
// ---------------------------------------------------------------------------

/// Extract the VReg from an operand, if it is a (possibly memory-base) register.
///
/// We only track VReg lattice state; PRegs, immediates, blocks, symbols, and
/// stack slots are not part of the narrow-carrier dataflow. Memory operands
/// load a fresh value whose width is dictated by the load opcode, handled in
/// the transfer function — here we just surface the directly-named VReg.
fn operand_vreg(op: &X86ISelOperand) -> Option<VReg> {
    match op {
        X86ISelOperand::VReg(v) => Some(*v),
        _ => None,
    }
}

/// Extract the immediate from an operand, if it is one.
fn operand_imm(op: &X86ISelOperand) -> Option<i64> {
    match op {
        X86ISelOperand::Imm(n) => Some(*n),
        _ => None,
    }
}

/// Carrier width (in bits) of a destination VReg, inferred from its `RegClass`.
///
/// `Gpr32` carriers are 32 bits (the home of i8/i16/i32); `Gpr64` are 64.
/// FP/vector classes have no narrow-carrier concern and report 0.
fn carrier_width(v: VReg) -> u32 {
    use trust_cg_ir::regs::RegClass;
    match v.class {
        RegClass::Gpr32 => 32,
        RegClass::Gpr64 => 64,
        _ => 0,
    }
}

/// The nominal value width (8/16/32/64 bits) of each VReg.
///
/// This is the **load-bearing input** that makes the checker sound. The
/// post-ISel machine IR cannot distinguish an `i8` from an `i32`: both live in a
/// `Gpr32` carrier (`RegClass::Gpr32`), so an `i8 NEG` and an `i32 NEG` are the
/// same `X86Opcode::Neg` over a `Gpr32` VReg. Only the *narrow* one leaves dirty
/// high bits that a wide-reading consumer must not see. The narrow width is a
/// fact ISel knows (it records each GPR-carrier def's nominal source width via
/// `X86ISelFunction::record_vreg_nominal_width`), so the checker is seeded with
/// it rather than inventing it.
///
/// Build with [`NominalWidths::from_value_type_widths`] from the ISel
/// `VReg -> nominal-bit-width` map exposed by
/// `X86ISelFunction::vreg_nominal_widths()`. VRegs absent from the map are
/// treated **conservatively as possibly-narrow** (their width is *unknown*): a
/// wide-reading consumer of an untracked operand is checked fail-closed rather
/// than blessed (see [`width_of`](Self::width_of)). This is the sound default —
/// a missing width must never be read as "this value fills its carrier".
#[derive(Debug, Clone, Default)]
pub struct NominalWidths {
    widths: HashMap<VReg, u32>,
}

impl NominalWidths {
    /// Construct from a precomputed `VReg -> nominal-bit-width` map.
    pub fn new(widths: HashMap<VReg, u32>) -> Self {
        Self { widths }
    }

    /// Construct from an ISel `VReg -> nominal-bit-width` map.
    ///
    /// This is the production seeding path. ISel records each defined
    /// GPR-carrier VReg's NOMINAL source width (8/16/32/64) — `I8 -> 8`,
    /// `I16 -> 16`, `B1|I32 -> 32`, `I64|I128 -> 64` — on the emitted
    /// `X86ISelFunction` via `record_vreg_nominal_width`, and exposes it through
    /// `X86ISelFunction::vreg_nominal_widths()`. ISel pre-filters non-GPR-carrier
    /// types (floats, vectors, aggregates) out of that map — they are not part of
    /// the narrow-carrier dataflow and have no wide-reader hazard — so the map's
    /// values are already exactly the nominal widths the checker needs; an absent
    /// VReg is *unknown* and is checked fail-closed if it ever reaches a wide
    /// reader (see [`width_of`](Self::width_of)).
    ///
    /// Takes the map by reference (it lives on the borrowed `X86ISelFunction`),
    /// matching the signature `X86ISelFunction::vreg_nominal_widths()` exposes.
    pub fn from_value_type_widths(widths: &HashMap<VReg, u32>) -> Self {
        Self {
            widths: widths.clone(),
        }
    }

    /// Record one VReg's nominal width (8/16/32/64).
    pub fn insert(&mut self, v: VReg, bits: u32) {
        self.widths.insert(v, bits);
    }

    /// Nominal width of `v`, or `None` when the width is not tracked.
    ///
    /// An unknown width is **not** silently treated as the carrier width:
    /// defaulting an untracked operand to its full carrier width would claim it
    /// is *not* narrow and bless a possibly-dirty live-in / scratch value
    /// feeding `IDIV`/`SAR`/`DIV`/`SHR` (a false negative — the unsound
    /// direction). Callers checking a wide reader treat `None` as fail-closed
    /// (see [`check_function`]).
    fn width_of(&self, v: VReg) -> Option<u32> {
        self.widths.get(&v).copied()
    }

    /// True iff `v` is *known* to fill its full 32/64-bit carrier — a genuine
    /// `i32`-in-Gpr32 / `i64`-in-Gpr64 value with no narrow-carrier hazard. An
    /// unknown width returns `false` (conservatively possibly-narrow).
    fn is_genuine_wide(&self, v: VReg) -> bool {
        let carrier = carrier_width(v);
        carrier != 0 && matches!(self.width_of(v), Some(n) if n >= carrier)
    }
}

// ---------------------------------------------------------------------------
// Transfer function: opcode -> destination lattice state
// ---------------------------------------------------------------------------

/// True when `opcode`'s operand 0 is a *destination* the checker should track.
///
/// Several x86 opcodes carry a register in operand 0 that is a SOURCE, not a
/// def: single-operand `IDIV`/`DIV`/`MUL` (the explicit operand is the
/// divisor/multiplicand), `CMP`/`TEST` (both operands are read), and `PUSH`.
/// Treating their operand 0 as a definition would overwrite the real lattice
/// state of a clean source value (e.g. corrupting a clean divisor to `Top`).
/// Branches, returns, calls and `CDQ`/`CQO` define no tracked GPR via operand 0
/// either. Everything else (`MOV`/`ADD`/`NEG`/shifts/`CMOV`/`SETcc`/`LEA`/loads/
/// extensions) does define operand 0.
fn defines_operand0_dest(opcode: X86Opcode) -> bool {
    !matches!(
        opcode,
        // Single-operand arithmetic whose operand 0 is a read source.
        X86Opcode::Idiv
            | X86Opcode::Div
            | X86Opcode::Mul
            // Flag-setting compares/tests read both operands, define no GPR.
            | X86Opcode::CmpRR
            | X86Opcode::CmpRI
            | X86Opcode::CmpRI8
            | X86Opcode::CmpRM
            | X86Opcode::TestRR
            | X86Opcode::TestRI
            | X86Opcode::TestRM
            // Operand 0 is a read source / no GPR def.
            | X86Opcode::Push
            // Implicit-register results (RDX:RAX), no operand-0 def.
            | X86Opcode::Cdq
            | X86Opcode::Cqo
            // Control flow defines no GPR.
            | X86Opcode::Jmp
            | X86Opcode::Jcc
            | X86Opcode::Ret
            | X86Opcode::Call
            | X86Opcode::CallR
            | X86Opcode::CallM
    )
}

/// Lattice state of a `MOV r, imm` materialization of nominal width `nominal`
/// into a carrier of width `carrier`.
///
/// A constant defines the whole carrier deterministically, so its hygiene can be
/// read off the immediate. For a non-narrow destination (`nominal >= carrier`)
/// the constant fills its carrier: `Full(carrier)`. For a narrow destination we
/// inspect the bits at/above `nominal`:
///   * all zero AND sign bit (bit `nominal-1`) zero => `Full(nominal)` (both)
///   * all zero, sign bit set                       => `ZeroExt(nominal)`
///   * all equal to the (set) sign bit              => `SignExt(nominal)`
///   * otherwise (value does not fit width nominal) => `Top` (fail-closed)
///
/// Modeling the immediate precisely removes a false positive: ISel's signed-div
/// overflow guard materializes the constant `1` and `CMOV`s it into the divisor;
/// without immediate precision the `1` is `Top` and poisons the divisor's join.
fn mov_imm_state(imm: i64, nominal: u32, carrier: u32) -> HighBits {
    if carrier == 0 {
        return HighBits::Top;
    }
    if nominal >= carrier {
        return HighBits::Full(carrier);
    }
    let carrier_mask: u64 = if carrier >= 64 {
        u64::MAX
    } else {
        (1u64 << carrier) - 1
    };
    let cv = (imm as u64) & carrier_mask;
    // The bits at/above the nominal width: [nominal, carrier). (nominal <
    // carrier here, so this region is non-empty.)
    let high_field_mask = carrier_mask >> nominal;
    let high = (cv >> nominal) & high_field_mask;
    let sign_bit = (cv >> (nominal - 1)) & 1;

    let zero_ok = high == 0;
    // Sign extension: bits [nominal, carrier) all replicate bit nominal-1.
    let sign_ok = if sign_bit == 1 {
        high == high_field_mask
    } else {
        high == 0
    };

    match (zero_ok, sign_ok) {
        (true, true) => HighBits::Full(nominal),
        (true, false) => HighBits::ZeroExt(nominal),
        (false, true) => HighBits::SignExt(nominal),
        (false, false) => HighBits::Top,
    }
}

/// Zero-extension upper bound proven by `state`: the width `w` such that bits
/// `>= w` are known zero, if any. Used to model bitwise-AND zero narrowing.
fn zero_ext_bound(state: HighBits) -> Option<u32> {
    match state {
        HighBits::ZeroExt(w) | HighBits::Full(w) => Some(w),
        _ => None,
    }
}

/// Compute the lattice state of the destination produced by `inst`.
///
/// `state` is the *incoming* per-VReg lattice (operands are read from it).
/// Returns `None` for instructions that do not define a tracked GPR VReg
/// destination (stores, branches, compares, single-operand div/mul, FP/vector
/// ops, etc.).
///
/// The classification mirrors the real x86-64 ISel semantics:
///
///   * Explicit extension moves (`MOVZX`/`MOVSX`/`MOVSXD`) produce a *clean*
///     `ZeroExt`/`SignExt` carrier — these are precisely the instructions
///     `zero_extend_narrow_operand` / `sign_extend_narrow_operand` emit to
///     repair a dirty operand. They are primary producers of a proof.
///   * `MOV r32, r32` (`MovRR32`) zero-extends into the 64-bit register, so a
///     64-bit destination is `ZeroExt(32)`; a 32-bit destination is a plain copy
///     that *propagates* the source's proof (it preserves the low 32 bits).
///   * 32/64-bit-wide ALU ops (`ADD`/`SUB`/`NEG`/`NOT`/`OR`/`XOR`/shifts/mul)
///     write the *whole* carrier as a function of their inputs; the result fills
///     the carrier (`Full(width)`) for a genuine wide value but does NOT prove a
///     *narrow* extension. This is exactly why `!8u8` (a 32-bit `NOT`) is dirty
///     for an i8 consumer.
///   * `CMOV` reads operand 0 (its prior value) and the explicit source operand
///     and writes one of them, so its def is the JOIN of those two states.
///   * `AND` with an immediate mask whose set bits lie within a low width zeroes
///     everything above, proving a zero-extension; `AND` of two zero-extended
///     operands stays zero-extended.
///   * `MOV r64, r64` (`MovRR`) copies the source's proven state through.
///
/// The `nominal` widths decide whether a wide ALU op dirties: for a value whose
/// nominal width is *narrower than (or unknown relative to)* its carrier, a
/// 32-bit ALU op leaves dirty high bits (`Top`); for a genuine 32/64-bit value
/// it fills the carrier cleanly (`Full(width)`).
fn transfer(
    inst: &X86ISelInst,
    state: &BitsMap,
    nominal: &NominalWidths,
) -> Option<(VReg, HighBits)> {
    if !defines_operand0_dest(inst.opcode) {
        return None;
    }
    let dst = inst.operands.first().and_then(operand_vreg)?;
    let width = carrier_width(dst);
    if width == 0 {
        return None; // FP/vector dst: not a narrow-carrier GPR.
    }
    // A wide ALU op cleanly fills the carrier ONLY for a value known to be as
    // wide as its carrier; a narrow value OR a value of unknown width is
    // conservatively dirty (`Top`) — never assume a wide-clean fill.
    let alu_result = if nominal.is_genuine_wide(dst) {
        HighBits::Full(width)
    } else {
        HighBits::Top
    };

    let src_state = |idx: usize| -> HighBits {
        inst.operands
            .get(idx)
            .and_then(operand_vreg)
            .and_then(|v| state.get(&v).copied())
            .unwrap_or(HighBits::Top)
    };

    let new = match inst.opcode {
        // --- Explicit extension moves: clean ext proofs. ---
        // MOVZX r, r/m8  -> low 8 bits zero-extended.
        X86Opcode::Movzx => HighBits::ZeroExt(8),
        // MOVZX r, r/m16 -> low 16 bits zero-extended.
        X86Opcode::MovzxW => HighBits::ZeroExt(16),
        // MOVSX r, r/m8  -> low 8 bits sign-extended.
        X86Opcode::MovsxB => HighBits::SignExt(8),
        // MOVSX r, r/m16 -> low 16 bits sign-extended.
        X86Opcode::MovsxW => HighBits::SignExt(16),
        // MOVSXD r64, r/m32 -> low 32 bits sign-extended into 64.
        X86Opcode::Movsx => HighBits::SignExt(32),

        // MOV r32, r32: into a 64-bit destination it zero-extends bits 32..63,
        // proving `ZeroExt(32)`; into a 32-bit destination it is a plain copy
        // that preserves the low 32 bits and so PROPAGATES the source's proof
        // (an extension proved on the source survives the copy).
        X86Opcode::MovRR32 => {
            if width == 64 {
                HighBits::ZeroExt(32)
            } else {
                src_state(1)
            }
        }

        // MOV r64, r64 copies the operand's proof through.
        X86Opcode::MovRR => src_state(1),

        // CMOV writes either operand 0 (its prior value, the "false" arm built
        // by a preceding MOV) or the explicit source operand 1; the result is
        // the JOIN of those two states. Reading operand 0's prior state is what
        // recovers the divisor's proof through ISel's signed-div overflow guard.
        X86Opcode::Cmovcc | X86Opcode::Cmovcc32 => {
            let prior = state.get(&dst).copied().unwrap_or(HighBits::Top);
            prior.join(src_state(1))
        }

        // Loads define exactly the loaded width with the documented extension.
        // 8/16/32-bit narrow loads zero-fill the rest of the carrier; the
        // wide load fills the whole 64-bit carrier.
        X86Opcode::MovRM8 => HighBits::ZeroExt(8),
        X86Opcode::MovRM16 => HighBits::ZeroExt(16),
        X86Opcode::MovRM32 => HighBits::ZeroExt(32),
        X86Opcode::MovRM | X86Opcode::MovRMSib | X86Opcode::MovRipRel => HighBits::Full(width),

        // AND can PROVE a zero-extension:
        //   * AND r, imm: bits where the immediate is 0 become 0. If the mask's
        //     set bits lie within the low `k` bits, bits >= k are zeroed =>
        //     ZeroExt(k). This is `v & 0xFF` proving ZeroExt(8).
        //   * AND r, r: if either operand has bits >= k zero, the result has
        //     bits >= k zero => ZeroExt(min over the known bounds).
        // If no zero-bound can be derived, fall back to the ALU split.
        X86Opcode::AndRI => {
            // Real ISel emits AndRI as [dst, src, Imm] (x86_64_isel.rs:5144),
            // so the mask immediate is operand index 2, not 1 (index 1 is src).
            let mask = inst.operands.get(2).and_then(operand_imm).unwrap_or(-1);
            let carrier_mask: u64 = if width >= 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            };
            let masked = (mask as u64) & carrier_mask;
            // Bits at/above `k` are zero in the result (the mask clears them).
            let k = (64 - masked.leading_zeros()).min(width);
            // Intersect with any zero-bound the source already proved (tighter).
            match zero_ext_bound(src_state(1)) {
                Some(sb) => HighBits::ZeroExt(k.min(sb)),
                None => HighBits::ZeroExt(k),
            }
        }
        X86Opcode::AndRR => match (zero_ext_bound(src_state(1)), zero_ext_bound(src_state(2))) {
            (Some(a), Some(b)) => HighBits::ZeroExt(a.min(b)),
            (Some(a), None) | (None, Some(a)) => HighBits::ZeroExt(a),
            (None, None) => alu_result,
        },

        // --- Wide ALU ops: dirty the high bits of a NARROW value. ---
        // These run at 32/64-bit carrier width. For a genuine 32/64-bit value
        // they cleanly fill the carrier (`Full(width)`); for a narrower (or
        // unknown-width) value they smear into bits above the type width,
        // leaving the carrier DIRTY (`Top`) — exactly the #51/#66 hazard.
        X86Opcode::AddRR
        | X86Opcode::AddRI
        | X86Opcode::AddRM
        | X86Opcode::SubRR
        | X86Opcode::SubRI
        | X86Opcode::SubRM
        | X86Opcode::Neg
        | X86Opcode::Not
        | X86Opcode::Inc
        | X86Opcode::Dec
        | X86Opcode::ImulRR
        | X86Opcode::ImulRRI
        | X86Opcode::ImulRM
        | X86Opcode::OrRR
        | X86Opcode::OrRI
        | X86Opcode::XorRR
        | X86Opcode::XorRI
        | X86Opcode::ShlRR
        | X86Opcode::ShlRI
        | X86Opcode::ShrRR
        | X86Opcode::ShrRI
        | X86Opcode::SarRR
        | X86Opcode::SarRI
        | X86Opcode::Lea
        | X86Opcode::LeaSib
        | X86Opcode::LeaRip
        | X86Opcode::Setcc => alu_result,

        // MOV immediate: model the immediate precisely against the nominal width
        // (see `mov_imm_state`). A constant clean to its width is blessed; one
        // that does not fit fails closed to `Top`.
        X86Opcode::MovRI => {
            let imm = inst.operands.get(1).and_then(operand_imm).unwrap_or(0);
            let n = nominal.width_of(dst).unwrap_or(width);
            mov_imm_state(imm, n, width)
        }

        // Any other dst-defining opcode (bit-manip, GPR<->XMM transfer, etc.):
        // be conservative — use the ALU split (narrow/unknown => dirty).
        _ => alu_result,
    };

    Some((dst, new))
}

// ---------------------------------------------------------------------------
// Consumer classification: which ops read the full carrier of a narrow value
// ---------------------------------------------------------------------------

/// If `opcode` reads its source operand across the *entire* carrier (so a
/// narrow value must be extended), return the required extension and the
/// operand index that is the wide-read source.
///
/// These are exactly the consumers the ISel guards with
/// `sign_extend_narrow_operand` / `zero_extend_narrow_operand`:
///
///   * `IDIV`, `SAR` (RR/RI): the divisor / shiftee is interpreted SIGNED
///     across the carrier (#51).
///   * `DIV`, `SHR` (RR/RI): interpreted UNSIGNED across the carrier (#66).
///
/// For `IDIV`/`DIV` the divisor (the single explicit register operand) is the
/// wide-read source. For the shift forms the shiftee is operand 1
/// (`[dst, src, count]`).
fn wide_read(opcode: X86Opcode) -> Option<(RequiredExtension, WideOperandSel)> {
    match opcode {
        // IDIV r/m32 — divisor read signed; dividend is the implicit EDX:EAX
        // built by CDQ, so the *explicit* operand is the wide-read divisor.
        X86Opcode::Idiv => Some((RequiredExtension::Sign, WideOperandSel::Last)),
        // DIV r/m32 — divisor read unsigned.
        X86Opcode::Div => Some((RequiredExtension::Zero, WideOperandSel::Last)),
        // SAR reads the shiftee signed (replicates the sign bit). Operand 1.
        X86Opcode::SarRR | X86Opcode::SarRI => {
            Some((RequiredExtension::Sign, WideOperandSel::ShiftSrc))
        }
        // SHR reads the shiftee unsigned (shifts in zeros). Operand 1.
        X86Opcode::ShrRR | X86Opcode::ShrRI => {
            Some((RequiredExtension::Zero, WideOperandSel::ShiftSrc))
        }
        _ => None,
    }
}

/// Which operand of a wide-reading consumer is the carrier-sensitive source.
#[derive(Debug, Clone, Copy)]
enum WideOperandSel {
    /// The single explicit register operand (DIV/IDIV divisor): the last VReg.
    Last,
    /// The shiftee of a shift instruction: operand index 1 (`[dst, src, cnt]`).
    ShiftSrc,
}

impl WideOperandSel {
    fn pick(self, inst: &X86ISelInst) -> Option<VReg> {
        match self {
            WideOperandSel::Last => inst.operands.iter().rev().find_map(operand_vreg),
            WideOperandSel::ShiftSrc => inst.operands.get(1).and_then(operand_vreg),
        }
    }
}

/// Width (in bits) confined by an AND-immediate-style mask: the number of low
/// bits that can be set in the masked result, i.e. `64 - leading_zeros(mask)`
/// of the carrier-masked value (`0` for a zero mask).
fn masked_low_width(mask: u64, carrier: u32) -> u32 {
    let carrier_mask: u64 = if carrier >= 64 {
        u64::MAX
    } else {
        (1u64 << carrier) - 1
    };
    let m = mask & carrier_mask;
    if m == 0 { 0 } else { 64 - m.leading_zeros() }
}

/// Resolve the constant low-bit mask applied to `result_vreg` by the next
/// AND-mask in `rest` (the instructions following the wide-read in its block),
/// if any. Recognizes the two bitfield-extract masking shapes ISel emits:
///
///   * `AND result, imm`        (`AndRI [dst, result, Imm(mask)]`)
///   * `MOV maskreg, imm` then `AND result, maskreg` (`AndRR [dst, result,
///     maskreg]`) — `emit_and_mask`'s `emit_mask_value` + `AndRR` shape.
///
/// Returns the kept low-bit width, or `None` when `result_vreg` is not the
/// operand of a recognizable immediate AND-mask. Conservative: an unrecognized
/// or non-immediate consumer yields `None` (the wide-read is then checked
/// normally, fail-closed).
fn mask_width_applied_to(result_vreg: VReg, carrier: u32, rest: &[X86ISelInst]) -> Option<u32> {
    // Track MovRI-materialized immediates so an `AndRR` against a mask register
    // can be resolved to its constant.
    let mut imm_regs: HashMap<VReg, i64> = HashMap::new();
    for inst in rest {
        match inst.opcode {
            X86Opcode::MovRI => {
                if let (Some(d), Some(v)) = (
                    inst.operands.first().and_then(operand_vreg),
                    inst.operands.get(1).and_then(operand_imm),
                ) {
                    imm_regs.insert(d, v);
                }
            }
            X86Opcode::AndRI => {
                // AndRI [dst, src, Imm(mask)] (matches ISel's AndRI shape).
                if inst.operands.get(1).and_then(operand_vreg) == Some(result_vreg)
                    && let Some(mask) = inst.operands.get(2).and_then(operand_imm)
                {
                    return Some(masked_low_width(mask as u64, carrier));
                }
            }
            X86Opcode::AndRR => {
                // AndRR [dst, src, maskreg] where maskreg was a MovRI immediate.
                let src1 = inst.operands.get(1).and_then(operand_vreg);
                let src2 = inst.operands.get(2).and_then(operand_vreg);
                let (other, used) = if src1 == Some(result_vreg) {
                    (src2, true)
                } else if src2 == Some(result_vreg) {
                    (src1, true)
                } else {
                    (None, false)
                };
                if used {
                    if let Some(mreg) = other
                        && let Some(&mask) = imm_regs.get(&mreg)
                    {
                        return Some(masked_low_width(mask as u64, carrier));
                    }
                    // Used by an AND but the mask is not a resolvable constant:
                    // stop scanning (the result has been consumed) — return None.
                    return None;
                }
            }
            _ => {}
        }
    }
    None
}

/// True when a wide-read SHIFT (`ShrRI`/`SarRI`, immediate count) is rendered
/// harmless by a downstream AND-mask — the bitfield-extract idiom — so a dirty
/// narrow source is NOT a miscompile and must not be flagged.
///
/// # Why this is sound (not a hole)
///
/// The narrow-carrier hazard is that a wide-reading shift drags the source's
/// DIRTY high carrier bits (positions `>= nominal_src`) down into bits the
/// result's consumer observes. ISel's bitfield-extract lowering shifts the field
/// to the bottom (`SHR src, lsb`) and then **AND-masks** the result to the field
/// width `w` (`emit_and_mask`). The masked result keeps only bits `[0, w)`,
/// which after a right shift by `lsb` are exactly `src[lsb .. lsb+w]`. When
/// `lsb + w <= nominal_src` those kept bits all originate from the source's own
/// true value `[0, nominal_src)` — the dirty bits `[nominal_src, carrier)` are
/// shifted to positions `>= nominal_src - lsb >= w` and the mask clears them.
/// `validate_bitfield_range` guarantees `lsb + width <= type_bits` in ISel, so
/// this is exactly the extract idiom; the predicate re-derives the inequality
/// from the emitted stream rather than trusting it.
///
/// Conservative in every direction: it applies ONLY to immediate-count shifts
/// (`ShrRI`/`SarRI`) whose result is consumed by a *recognizable constant* AND
/// mask with `lsb + masked_width <= nominal_src`. A divisor (`IDIV`/`DIV`), a
/// register-count shift, an unmasked shift, a non-constant mask, or an unknown
/// source width all yield `false` — the wide-read is then checked normally
/// (fail-closed). A masked extract over an i32/i64 source is already
/// `is_genuine_wide` and never reaches here.
fn wide_read_neutralized_by_mask(
    inst: &X86ISelInst,
    src: VReg,
    carrier: u32,
    nominal: &NominalWidths,
    iselblock: &X86ISelBlock,
    inst_index: usize,
) -> bool {
    // Only the immediate-count shift forms participate in the extract idiom.
    let count = match inst.opcode {
        X86Opcode::ShrRI | X86Opcode::SarRI => match inst.operands.get(2).and_then(operand_imm) {
            Some(c) if (0..i64::from(carrier)).contains(&c) => c as u32,
            _ => return false,
        },
        _ => return false,
    };
    // Need the source's nominal width to bound the field; unknown => fail-closed.
    let Some(nominal_src) = nominal.width_of(src) else {
        return false;
    };
    // The shift result is operand 0; find the mask applied to it downstream.
    let Some(dst) = inst.operands.first().and_then(operand_vreg) else {
        return false;
    };
    let rest = &iselblock.insts[inst_index + 1..];
    let Some(masked_width) = mask_width_applied_to(dst, carrier, rest) else {
        return false;
    };
    // SOUNDNESS: the dirty shift result must be SOLE-USED by that mask. If `dst`
    // is read as a source by any OTHER instruction in the block, its dirty high
    // bits could leak through that unmasked use while this carve-out suppressed
    // the violation — so fall back to the normal (fail-closed) width check. The
    // current bitfield-extract lowering reads the shift result exactly once (the
    // mask), so this never false-rejects valid code; it only future-proofs
    // against a dual-use lowering. (Intra-block, matching this carve-out's scope:
    // a cross-block use of `dst` is out of scope, as is any pre-mask redef.)
    let src_uses = rest
        .iter()
        .filter(|i| {
            i.operands
                .iter()
                .skip(1)
                .filter_map(operand_vreg)
                .any(|r| r == dst)
        })
        .count();
    if src_uses != 1 {
        return false;
    }
    // Kept bits are src[count .. count + masked_width]; safe iff they lie wholly
    // within the source's true value [0, nominal_src).
    count + masked_width <= nominal_src
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

/// Apply every instruction's transfer to `state` in order (a forward pass over
/// one block), leaving `state` as the block's exit lattice. A definition
/// overwrites the prior state of its VReg (straight-line code: the latest def
/// dominates subsequent uses within the block).
fn run_block_transfers(insts: &[X86ISelInst], state: &mut BitsMap, nominal: &NominalWidths) {
    for inst in insts {
        if let Some((dst, new)) = transfer(inst, state, nominal) {
            state.insert(dst, new);
        }
    }
}

/// Join `src` into `dst` (per-VReg, towards `Top`). A VReg present in only one
/// side is moved to `Top`: on the path where it is absent it is undefined /
/// possibly-dirty, so the merge cannot prove any extension for it. Returns true
/// iff `dst` changed.
fn join_into(dst: &mut BitsMap, src: &BitsMap) -> bool {
    // UNION-MEET join. A vreg ABSENT from one side is bottom (⊥) — "no information
    // on this path": either the value is not live/defined there, or, during the
    // fixpoint, its dataflow fact has not yet propagated around a back-edge. ⊥ is
    // the identity for join, so an absent key NEVER demotes the other side. A vreg
    // PRESENT with `Top` is genuine unknown (e.g. a 32-bit NEG of a narrow value)
    // and still meets to `Top`.
    //
    // The previous semantics treated absent as `Top`. Because the lattice only
    // moves towards `Top`, that PERMANENTLY demoted any value defined-and-clean on
    // every real path but not yet propagated around a loop back-edge — e.g. a
    // loop-invariant sign-extended narrow divisor that LICM hoists into the
    // preheader, then read by an IDIV in the loop body (CARRIER-051): correct at
    // O0 (no hoist; the MOVSX sits in the consumer's block) but false-rejected
    // fail-closed at O2/O3. Soundness is preserved: every real path that leaves a
    // USED value dirty records it present=`Top`, so it still meets to `Top`; an
    // absent key is dead/undefined on that path, and well-formed machine code
    // defines every used vreg on all paths reaching the use.
    let mut changed = false;
    for (v, incoming) in src.iter() {
        match dst.get(v).copied() {
            Some(cur) => {
                let merged = cur.join(*incoming);
                if merged != cur {
                    dst.insert(*v, merged);
                    changed = true;
                }
            }
            None => {
                dst.insert(*v, *incoming);
                changed = true;
            }
        }
    }
    changed
}

/// Run the carrier-hygiene invariant over an x86-64 ISel function.
///
/// Performs a forward abstract interpretation to a **fixpoint**:
///
///   1. Compute each block's predecessor set from the CFG `successors`.
///   2. Iterate a worklist: a block's entry state is the join over its
///      predecessors' exit states; transfer through the block yields its exit;
///      when an exit changes, re-enqueue the successors. The join only moves
///      towards `Top`, so the lattice has finite height and iteration converges.
///      This is what catches a **loop-carried** dirty value: a latch that
///      redefines a value dirty flows that `Top` back to the header through the
///      back-edge, demoting the header's entry state on a later iteration — a
///      single forward sweep would miss it.
///   3. A final pass replays each block from its fixpoint entry state and, at
///      every wide-reading consumer (`IDIV`/`DIV`/`SAR`/`SHR`) whose source is
///      not a *genuine* full-carrier value, checks the operand's proven state
///      against the required (width-aware) extension.
///
/// An operand of unknown nominal width is checked fail-closed: it is not assumed
/// to fill its carrier (see [`NominalWidths::width_of`]). Genuine 32/64-bit
/// operands are never flagged — there is no narrow-carrier hazard when the value
/// fills its carrier.
///
/// See [`NominalWidths`] for why the width map is required for soundness.
pub fn check_function(func: &X86ISelFunction, nominal: &NominalWidths) -> CarrierHygieneReport {
    let mut report = CarrierHygieneReport {
        function: func.name.clone(),
        violations: Vec::new(),
    };

    // Fast path: the narrow-carrier dataflow can only ever REPORT a violation at a
    // wide read whose source is NOT genuine-wide (a narrow or unknown carrier).
    // A function with no such site — e.g. all-32/64-bit arithmetic — is trivially
    // clean, yet the worklist fixpoint below (which clones/joins/compares a
    // per-block `VReg -> HighBits` map and is superlinear on a many-block
    // function) would do all that work only to find nothing. Scan for a potential
    // site first, in O(insts); if none exists there is provably no violation and
    // we return the empty report without running the fixpoint. The predicate is
    // EXACTLY the checker's own violation precondition below, minus the
    // mask-neutralized refinement — which can only REMOVE sites, so skipping
    // strictly when there are ZERO sites is conservative and sound.
    let has_potential_site = func.block_order.iter().any(|&block| {
        func.blocks.get(&block).is_some_and(|iselblock| {
            iselblock.insts.iter().any(|inst| {
                if let Some((_, sel)) = wide_read(inst.opcode)
                    && let Some(src) = sel.pick(inst)
                {
                    return carrier_width(src) != 0 && !nominal.is_genuine_wide(src);
                }
                false
            })
        })
    });
    if !has_potential_site {
        return report;
    }

    // --- Predecessor map from CFG successors. ---
    let mut preds: HashMap<Block, Vec<Block>> = HashMap::new();
    for &block in &func.block_order {
        preds.entry(block).or_default();
    }
    for &block in &func.block_order {
        if let Some(iselblock) = func.blocks.get(&block) {
            for &succ in &iselblock.successors {
                preds.entry(succ).or_default().push(block);
            }
        }
    }

    // --- Worklist fixpoint over block exit states. ---
    let mut block_exit: HashMap<Block, BitsMap> = HashMap::new();
    let mut block_entry: HashMap<Block, BitsMap> = HashMap::new();
    for &block in &func.block_order {
        block_exit.insert(block, BitsMap::default());
        block_entry.insert(block, BitsMap::default());
    }

    let mut worklist: Vec<Block> = func.block_order.clone();
    let mut in_worklist: HashSet<Block> = func.block_order.iter().copied().collect();

    while let Some(block) = worklist.pop() {
        in_worklist.remove(&block);
        let Some(iselblock) = func.blocks.get(&block) else {
            continue;
        };

        // entry = join over predecessor exits (empty if no predecessors). The join
        // (`join_into`) is union-meet: a vreg ABSENT from a predecessor's exit is
        // bottom (no information on that path / not yet propagated around a back
        // edge), the identity for join — so a loop-invariant value hoisted into the
        // preheader is not demoted to `Top` by the still-empty back-edge exit.
        let mut entry: BitsMap = BitsMap::default();
        if let Some(pred_list) = preds.get(&block) {
            for &p in pred_list {
                if let Some(pexit) = block_exit.get(&p) {
                    join_into(&mut entry, pexit);
                }
            }
        }
        block_entry.insert(block, entry.clone());

        // exit = transfer through the block from entry.
        let mut exit = entry;
        run_block_transfers(&iselblock.insts, &mut exit, nominal);

        let changed = block_exit.get(&block) != Some(&exit);
        if changed {
            block_exit.insert(block, exit);
            for &succ in &iselblock.successors {
                if in_worklist.insert(succ) {
                    worklist.push(succ);
                }
            }
        }
    }

    // --- Final CHECK pass using fixpoint entry states. ---
    for &block in &func.block_order {
        let Some(iselblock) = func.blocks.get(&block) else {
            continue;
        };
        let mut state = block_entry.get(&block).cloned().unwrap_or_default();

        for (inst_index, inst) in iselblock.insts.iter().enumerate() {
            // 1) CHECK: a wide-reading consumer over a non-genuine-wide operand
            //    must see a proven (width-aware) extension.
            if let Some((required, sel)) = wide_read(inst.opcode)
                && let Some(src) = sel.pick(inst)
            {
                let carrier = carrier_width(src);
                // A genuine 32/64-bit value fills its carrier: no hazard.
                // Everything else — narrow OR unknown width — is checked.
                if carrier != 0
                    && !nominal.is_genuine_wide(src)
                    && !wide_read_neutralized_by_mask(
                        inst, src, carrier, nominal, iselblock, inst_index,
                    )
                {
                    // Use the known nominal width; an unknown width is
                    // fail-closed by requiring a proof down to width 1, which
                    // essentially only a full-carrier-clean value could meet.
                    let n = nominal.width_of(src).unwrap_or(1);
                    let actual = state.get(&src).copied().unwrap_or(HighBits::Top);
                    let ok = match required {
                        RequiredExtension::Zero => actual.proves_zero_extended(n, carrier),
                        RequiredExtension::Sign => actual.proves_sign_extended(n, carrier),
                    };
                    if !ok {
                        // Diagnostic aid: the in-block instruction that last
                        // DEFINES the offending operand (or a note that it is
                        // defined in a predecessor / was rewritten by a later
                        // pass). This is what makes a carrier violation
                        // actionable — it points at the producer that should
                        // have carried (or whose rewrite dropped) the extension.
                        let producer = iselblock.insts[..inst_index]
                            .iter()
                            .rev()
                            .find(|i| i.operands.first().and_then(operand_vreg) == Some(src))
                            .map(|i| format!("defined in this block by {:?}", i.opcode))
                            .unwrap_or_else(|| {
                                "not defined in this block (entered from a predecessor or \
                                     rewritten by a later operand-coalescing pass)"
                                    .to_string()
                            });
                        let nominal_note = match nominal.width_of(src) {
                            Some(w) => format!("recorded nominal width i{w}"),
                            None => "NO recorded nominal width (treated as unknown)".to_string(),
                        };
                        report.violations.push(CarrierHygieneViolation {
                            block: block.0,
                            inst_index,
                            opcode: inst.opcode,
                            operand: src,
                            required,
                            actual,
                            detail: format!(
                                "{} [operand {src:?}: {producer}; {nominal_note}]",
                                violation_detail(inst.opcode, required, actual)
                            ),
                        });
                    }
                }
            }

            // 2) TRANSFER: update the lattice for this instruction's def. Within
            //    a block, the latest def dominates subsequent uses, so we
            //    OVERWRITE (matching `run_block_transfers`). Cross-block merges
            //    — including loop back-edges — are handled by the fixpoint's
            //    join into each block's entry state, not here.
            if let Some((dst, new)) = transfer(inst, &state, nominal) {
                state.insert(dst, new);
            }
        }
    }

    report
}

fn violation_detail(opcode: X86Opcode, required: RequiredExtension, actual: HighBits) -> String {
    let (ext, miscompile) = match required {
        RequiredExtension::Sign => (
            "sign-extended",
            "#51 (SAR/IDIV consuming a dirty narrow carrier)",
        ),
        RequiredExtension::Zero => (
            "zero-extended",
            "#66 (SHR/unsigned-DIV consuming a dirty narrow carrier)",
        ),
    };
    format!(
        "{opcode:?} reads its source across the full 32/64-bit carrier and \
         requires a {ext} operand (covering the value's full nominal width), but \
         the operand's proven carrier state is {actual:?}. A 32-bit NOT/NEG/SUB \
         of a narrow (i8/i16) value leaves dirty high bits; a MOVSX/MOVZX from \
         too WIDE a width leaves the narrow value's own dirty bits in place; \
         without a correctly-widthed MOV{sx} the consumer reads garbage. Insert \
         sign_extend_narrow_operand / zero_extend_narrow_operand before this \
         instruction. Historical miscompile: {miscompile}.",
        sx = match required {
            RequiredExtension::Sign => "SX",
            RequiredExtension::Zero => "ZX",
        }
    )
}
