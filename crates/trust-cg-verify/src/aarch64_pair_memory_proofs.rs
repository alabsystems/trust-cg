// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Per-instruction proof coverage for the AArch64 PAIR memory family:
//! `STP`/`LDP` in the signed-offset, pre-index and post-index forms
//! (`StpRI`, `LdpRI`, `StpPreIndex`, `LdpPostIndex`, and the two Q-only
//! post-index aliases `NeonStpQPost`/`NeonLdpQPost`).
//!
//! # What this module is for
//!
//! `function_verifier::opcode_to_proof_query` deliberately returns `None` for
//! every pair opcode, and `coverage_gate::aarch64_deferred_value_op_reason`
//! named the exact gap this module closes: an *"authenticated
//! operand/width/address and source-memory binding for both transfers and any
//! base writeback"*. Opcode identity alone genuinely cannot authenticate a
//! pair access — the transfer width comes from the register class of operand
//! 0, the address from operand 2 plus a BYTE immediate, and whether the base
//! is written back from the addressing mode. Nothing about that is knowable
//! without the operands, which is why the broad `("load", Memory)` /
//! `("store", Memory)` queries must never be reused here.
//!
//! This module supplies what that reason names, per EMITTED INSTRUCTION: a
//! reconstructed obligation ([`MachineSideProvenance::Reconstructed`]) built
//! from the real opcode and the real positional operands, asserting that the
//! architectural pair access denoted by the instruction's own ENCODED WORD
//! agrees with the scalarized two-access-plus-base-update denotation of the
//! same operands.
//!
//! # The theorem
//!
//! For an admitted instruction with transfer registers `Rt`, `Rt2`, base `Xn`,
//! element width `n` bytes and byte offset `off`, the obligation asserts the
//! conjunction of:
//!
//! * **both transfers land at the intended addresses.** For a STORE, the
//!   memory image after the machine's pair store is compared, byte by byte at
//!   an enumerated probe set, with the image after the two INDEPENDENT scalar
//!   stores the pair is a fusion of: `Rt` at `Xn + s0` and `Rt2` at
//!   `Xn + s0 + n`, where `s0` is `off` for the offset/pre-index forms and `0`
//!   for post-index. For a LOAD, memory is seeded with the intended lane
//!   payloads at those same two addresses and the machine's two loaded values
//!   must equal the payload of the lane its DECODED destination field names.
//! * **the base register is written back by exactly the immediate** — `Xn`
//!   after the access equals `Xn + off` for pre-index and post-index, and
//!   equals `Xn` unchanged for the signed-offset form.
//!
//! The probe set brackets the intended footprint (a guard byte below lane 0
//! and above lane 1), so a machine access that is displaced, mis-scaled, wider
//! or narrower than intended writes or reads a probed byte the scalarized
//! intent does not, and the obligation is REFUTED.
//!
//! # Where the refutation power comes from
//!
//! The two sides are not the same builder applied twice. The intent side is
//! built from the instruction's OPERANDS. The machine side is built from the
//! fields of the 32-bit word the instruction encodes to, recovered by
//! [`decode_pair_memory_word`] — an independent Arm DDI0602 C4.1 load/store
//! pair decode. The encode step is lossy in exactly the places that carry the
//! hazards this family has:
//!
//! * `imm7` is seven signed bits of SCALED offset, so a byte offset whose
//!   quotient does not fit round-trips to a different offset (the same
//!   truncation `encoder_oob_fail_closed.rs` pins for the encoder's `as i8`);
//! * the element width is NOT carried — it is re-derived from `(opc, V)`, and
//!   `opc = 0b10` means 8-byte X when `V = 0` but 16-byte Q when `V = 1`, so a
//!   size confusion changes both transfer addresses. A bank confusion at an
//!   EQUAL width (W/S, X/D) changes no address and no byte; it is refused
//!   instead, because the decoded word then transfers registers of the other
//!   register file;
//! * the addressing mode is a two-bit field, so a mode confusion changes the
//!   effective address, the writeback, or both;
//! * `Rt`, `Rt2` and `Rn` are separate five-bit fields, so a transposition
//!   between them (the encoder's own call passes them in the order
//!   `rt2, rn, rt`) routes a lane payload to the wrong address or names a
//!   different base register.
//!
//! Every one of those is refuted rather than refused; the negative controls in
//! this module's tests exercise each by injecting a mutated word through
//! [`pair_memory_obligation_from_word`]. `tests/aarch64_pair_memory_wrong_theorems.rs`
//! runs the same seam over every single-bit corruption and every multi-field
//! defect of 330 admitted shapes at the compiler's sample budget: each defect
//! is refused or refuted, except a mode change of a zero-offset shape, which
//! is architecturally equivalent.
//!
//! # What it does NOT establish
//!
//! * It does not bind the instruction to a SOURCE store/load: like every other
//!   reconstruction-arm obligation (see
//!   `lowering_proof::discharge_reconstructed_obligation`), the symbolic lane
//!   and base inputs are fresh, not the checked source values. The claim is
//!   that THIS emitted pair access denotes what its operands say, not that its
//!   operands are the ones the source asked for.
//! * It does not run the codegen encoder. [`pair_memory_word`] is an
//!   independent re-derivation of the field layout inside this crate
//!   (`trust-cg-verify` does not depend on `trust-cg-codegen`). That the two
//!   agree on every admitted shape is a separate, measured fact, pinned by
//!   `crates/trust-cg-codegen/tests/aarch64_pair_memory_decode.rs`.
//! * It does not cover a pair instruction whose operands are still virtual, or
//!   whose load destination is the zero register: those are REFUSED (no
//!   credit), not credited.
//! * The discharge is by evaluation, so its strength is `Statistical` unless a
//!   committed certificate or a live formal route upgrades it, exactly as for
//!   every other 64-bit-addressed obligation in the lane.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use trust_cg_ir::RegClass;
use trust_cg_ir::aarch64_regs::{SP, WSP, WZR, XZR, preg_class};
use trust_cg_ir::regs::SpecialReg;
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand};

// ---------------------------------------------------------------------------
// Addressing mode
// ---------------------------------------------------------------------------

/// Addressing mode of a pair memory access, as the opcode fixes it.
///
/// Field values are the Arm DDI0602 C4.1 load/store-pair encoding-class bits
/// at `[24:23]`. `0b00` is the non-temporal (`STNP`/`LDNP`) class, which this
/// backend never emits and which this module refuses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairMode {
    /// `[Xn, #imm]` — access at `Xn + imm`, base unchanged.
    Offset,
    /// `[Xn, #imm]!` — access at `Xn + imm`, base becomes `Xn + imm`.
    PreIndex,
    /// `[Xn], #imm` — access at `Xn`, base becomes `Xn + imm`.
    PostIndex,
}

impl PairMode {
    fn field(self) -> u32 {
        match self {
            Self::PostIndex => 0b01,
            Self::Offset => 0b10,
            Self::PreIndex => 0b11,
        }
    }

    fn from_field(bits: u32) -> Option<Self> {
        match bits {
            0b01 => Some(Self::PostIndex),
            0b10 => Some(Self::Offset),
            0b11 => Some(Self::PreIndex),
            _ => None,
        }
    }

    /// Byte displacement from the base at which the FIRST transfer happens.
    fn access_displacement(self, offset: i64) -> i64 {
        match self {
            Self::Offset | Self::PreIndex => offset,
            Self::PostIndex => 0,
        }
    }

    /// Byte displacement written back into the base register.
    fn writeback_displacement(self, offset: i64) -> i64 {
        match self {
            Self::Offset => 0,
            Self::PreIndex | Self::PostIndex => offset,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Offset => "offset",
            Self::PreIndex => "pre",
            Self::PostIndex => "post",
        }
    }
}

// ---------------------------------------------------------------------------
// Operand-shape admission (independent re-derivation of the encoder contract)
// ---------------------------------------------------------------------------

/// The shape of one admitted pair memory instruction.
///
/// This is an INDEPENDENT re-derivation of the contract
/// `trust_cg_codegen::aarch64::encode::pair_memory_descriptor` enforces; the
/// verify crate does not depend on the codegen crate and must not take the
/// encoder's word for what it admitted. It is deliberately NARROWER in two
/// places, both fail-closed:
///
/// * a still-virtual operand is refused (the encoder tolerates an unresolved
///   `Gpr64` virtual base before register allocation; a proof needs the
///   allocated register);
/// * a LOAD into the zero register is refused (architecturally legal and
///   pointless — the destination is discarded, so there is no loaded value to
///   state a theorem about).
///
/// A STORE from the zero register IS admitted; its transfer reads as all-zero
/// bytes, which the value model below encodes exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PairMemoryIntent {
    /// The emitted opcode this shape came from.
    pub opcode: AArch64Opcode,
    /// True for the load direction (`LDP`), false for the store (`STP`).
    pub load: bool,
    /// Addressing mode the opcode fixes.
    pub mode: PairMode,
    /// Bytes transferred per lane: 4, 8 or 16.
    pub element_bytes: u32,
    /// The `V` bit: true when the transfer registers are SIMD/FP.
    pub simd: bool,
    /// BYTE offset carried by the instruction (the encoder scales it).
    pub offset: i64,
    /// Five-bit hardware field of the first transfer register.
    pub rt: u8,
    /// Five-bit hardware field of the second transfer register.
    pub rt2: u8,
    /// Five-bit hardware field of the base register (31 is SP here).
    pub rn: u8,
    /// Per-slot: the transfer operand is the zero register.
    zero_transfer: [bool; 2],
}

impl PairMemoryIntent {
    /// Whether transfer slot `slot` (0 or 1) is the zero register (a store of
    /// all-zero bytes; loads into the zero register are refused).
    pub fn zero_transfer(self, slot: usize) -> bool {
        self.zero_transfer.get(slot).copied().unwrap_or(false)
    }

    /// Raw `opc` field for this element width and bank.
    pub(crate) fn opc(self) -> u32 {
        match (self.simd, self.element_bytes) {
            (false, 4) => 0b00,
            (false, 8) => 0b10,
            (true, 4) => 0b00,
            (true, 8) => 0b01,
            (true, 16) => 0b10,
            // `pair_memory_intent` yields no other (bank, width) combination.
            _ => unreachable!("unadmitted pair element width"),
        }
    }

    /// Scaled `imm7` this offset encodes to, if it fits the signed field.
    fn imm7(self) -> Option<i32> {
        let scale = i64::from(self.element_bytes);
        if self.offset % scale != 0 {
            return None;
        }
        let scaled = self.offset / scale;
        (-64..=63).contains(&scaled).then_some(scaled as i32)
    }
}

/// Element width in bytes for a pair transfer register class, or `None` when
/// the class cannot appear in a pair transfer slot.
fn transfer_element_bytes(class: RegClass) -> Option<(u32, bool)> {
    match class {
        RegClass::Gpr32 => Some((4, false)),
        RegClass::Gpr64 => Some((8, false)),
        RegClass::Fpr32 => Some((4, true)),
        RegClass::Fpr64 => Some((8, true)),
        RegClass::Fpr128 => Some((16, true)),
        _ => None,
    }
}

/// Resolve one transfer operand to `(class, hw field, is-zero-register)`.
///
/// `SP`/`WSP` are refused: field 31 in a pair transfer slot is the zero
/// register, never the stack pointer — the same split
/// `encode::pair_operand_class` enforces. A virtual register is refused
/// (this lane credits allocated instructions only).
fn transfer_operand(operand: &MachOperand) -> Option<(RegClass, u8, bool)> {
    match operand {
        MachOperand::PReg(p) if *p == SP || *p == WSP => None,
        MachOperand::PReg(p) if *p == XZR => Some((RegClass::Gpr64, 31, true)),
        MachOperand::PReg(p) if *p == WZR => Some((RegClass::Gpr32, 31, true)),
        MachOperand::PReg(p) => {
            let class = preg_class(*p);
            transfer_element_bytes(class)?;
            Some((class, p.hw_enc(), false))
        }
        MachOperand::Special(SpecialReg::XZR) => Some((RegClass::Gpr64, 31, true)),
        MachOperand::Special(SpecialReg::WZR) => Some((RegClass::Gpr32, 31, true)),
        _ => None,
    }
}

/// Resolve the base operand to its five-bit field.
///
/// `XZR` is refused (field 31 in a memory base slot is SP, not the zero
/// register), mirroring `encode::memory_base_hw`; a virtual base is refused.
fn base_operand(operand: &MachOperand) -> Option<u8> {
    match operand {
        MachOperand::PReg(p) if preg_class(*p) == RegClass::Gpr64 && *p != XZR => Some(p.hw_enc()),
        MachOperand::Special(SpecialReg::SP) => Some(31),
        _ => None,
    }
}

/// Admit one emitted pair memory instruction, or refuse it.
///
/// Refusal is total: an instruction this returns `None` for earns NO proof
/// credit anywhere in this module.
pub fn pair_memory_intent(inst: &MachInst) -> Option<PairMemoryIntent> {
    use AArch64Opcode as A;
    let (load, mode, q_only) = match inst.opcode {
        A::StpRI => (false, PairMode::Offset, false),
        A::LdpRI => (true, PairMode::Offset, false),
        A::StpPreIndex => (false, PairMode::PreIndex, false),
        A::LdpPostIndex => (true, PairMode::PostIndex, false),
        A::NeonLdpQPost => (true, PairMode::PostIndex, true),
        A::NeonStpQPost => (false, PairMode::PostIndex, true),
        _ => return None,
    };
    if !(3..=4).contains(&inst.operands.len()) {
        return None;
    }

    let (class0, rt, zero0) = transfer_operand(inst.operands.first()?)?;
    let (class1, rt2, zero1) = transfer_operand(inst.operands.get(1)?)?;
    if class0 != class1 {
        return None;
    }
    if q_only && class0 != RegClass::Fpr128 {
        return None;
    }
    let (element_bytes, simd) = transfer_element_bytes(class0)?;

    let rn = base_operand(inst.operands.get(2)?)?;
    // The base slot spells SP with field 31; `base_operand` already refused
    // every other register that could reach field 31 there.

    let offset = match inst.operands.get(3) {
        None => 0,
        Some(MachOperand::Imm(value)) => *value,
        Some(_) => return None,
    };
    let scale = i64::from(element_bytes);
    if offset % scale != 0 || !(-64..=63).contains(&(offset / scale)) {
        return None;
    }

    // Arm DDI0602: duplicate LDP destination fields are constrained
    // unpredictable. The encoder refuses them; so does this admission.
    if load && rt == rt2 {
        return None;
    }
    // A discarded load destination has no value to state a theorem about.
    if load && (zero0 || zero1) {
        return None;
    }
    // GPR writeback forbids transfer/base overlap except when the base is SP.
    let base_is_sp = rn == 31;
    if mode != PairMode::Offset
        && matches!(class0, RegClass::Gpr32 | RegClass::Gpr64)
        && !base_is_sp
        && (rt == rn || rt2 == rn)
    {
        return None;
    }

    let intent = PairMemoryIntent {
        opcode: inst.opcode,
        load,
        mode,
        element_bytes,
        simd,
        offset,
        rt,
        rt2,
        rn,
        zero_transfer: [zero0, zero1],
    };
    // Every admitted shape must encode; `imm7` re-checks the scaled range the
    // offset test above established, so this cannot refuse in practice and is
    // kept as a fail-closed backstop rather than an `unwrap`.
    intent.imm7()?;
    Some(intent)
}

// ---------------------------------------------------------------------------
// Independent encode / decode of the pair word
// ---------------------------------------------------------------------------

/// Encode an admitted pair intent to its 32-bit word.
///
/// Arm DDI0602 C4.1, load/store pair:
///
/// ```text
/// opc(2) | 101 | V(1) | 0  | mode(2) | L(1) | imm7(7) | Rt2(5) | Rn(5) | Rt(5)
///  31:30 | 29:27| 26  | 25 |  24:23  |  22  |  21:15  | 14:10  |  9:5  |  4:0
/// ```
///
/// This is a deliberate re-derivation inside `trust-cg-verify`, independent of
/// `trust_cg_codegen::aarch64::encoding_mem::encode_ldp_stp`. Agreement of the
/// two on every admitted shape is a measured cross-check, not an assumption.
pub fn pair_memory_word(intent: &PairMemoryIntent) -> Option<u32> {
    let imm7 = intent.imm7()?;
    if intent.rt > 31 || intent.rt2 > 31 || intent.rn > 31 {
        return None;
    }
    let mut word: u32 = 0;
    word |= intent.opc() << 30;
    word |= 0b101 << 27;
    word |= u32::from(intent.simd) << 26;
    word |= intent.mode.field() << 23;
    word |= u32::from(intent.load) << 22;
    word |= ((imm7 as u32) & 0x7f) << 15;
    word |= u32::from(intent.rt2) << 10;
    word |= u32::from(intent.rn) << 5;
    word |= u32::from(intent.rt);
    Some(word)
}

/// The architectural content of a decoded pair memory word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodedPairMemory {
    /// `L` bit: true for the load direction.
    pub load: bool,
    /// Addressing mode from `[24:23]`.
    pub mode: PairMode,
    /// Element width re-derived from `(opc, V)`, in bytes.
    pub element_bytes: u32,
    /// `V` bit.
    pub simd: bool,
    /// BYTE offset: the sign-extended `imm7` times the element width.
    pub offset: i64,
    /// `Rt` field.
    pub rt: u8,
    /// `Rt2` field.
    pub rt2: u8,
    /// `Rn` field.
    pub rn: u8,
}

/// Element width named by `(opc, V)`.
///
/// `opc = 0b01` with `V = 0` is `LDPSW` (a sign-extending 32-bit pair load,
/// which this backend never emits and whose loaded value is not a plain
/// transfer) and `opc = 0b11` is unallocated; both are refused. Note that
/// `opc = 0b10` is 8 bytes for `V = 0` and 16 for `V = 1` — the width is NOT
/// recoverable from `opc` alone.
fn decoded_element_bytes(opc: u32, simd: bool) -> Option<u32> {
    match (simd, opc) {
        (false, 0b00) => Some(4),
        (false, 0b10) => Some(8),
        (true, 0b00) => Some(4),
        (true, 0b01) => Some(8),
        (true, 0b10) => Some(16),
        _ => None,
    }
}

/// Decode a 32-bit word as an Arm DDI0602 C4.1 load/store pair, or refuse.
///
/// Bit 25 is a fixed zero of every load/store class (the top-level `op1`
/// field `[28:25]` is `x1x0` for loads and stores). A word with bits
/// `[29:27] = 101` and bit 25 set is in the data-processing (register) or
/// scalar FP/SIMD data-processing group, not a pair, so it is refused.
pub fn decode_pair_memory_word(word: u32) -> Option<DecodedPairMemory> {
    if (word >> 27) & 0b111 != 0b101 || (word >> 25) & 1 != 0 {
        return None;
    }
    let opc = word >> 30;
    let simd = (word >> 26) & 1 == 1;
    let mode = PairMode::from_field((word >> 23) & 0b11)?;
    let load = (word >> 22) & 1 == 1;
    let element_bytes = decoded_element_bytes(opc, simd)?;
    let raw_imm7 = ((word >> 15) & 0x7f) as i32;
    // Sign-extend the seven-bit field before scaling.
    let imm7 = if raw_imm7 & 0x40 != 0 {
        raw_imm7 - 128
    } else {
        raw_imm7
    };
    Some(DecodedPairMemory {
        load,
        mode,
        element_bytes,
        simd,
        offset: i64::from(imm7) * i64::from(element_bytes),
        rt: (word & 0x1f) as u8,
        rt2: ((word >> 10) & 0x1f) as u8,
        rn: ((word >> 5) & 0x1f) as u8,
    })
}

// ---------------------------------------------------------------------------
// SMT value model
// ---------------------------------------------------------------------------

/// Symbolic name of the base register's value on entry.
const BASE_INPUT: &str = "pair_base";
/// Symbolic name of the untouched-memory byte.
const SEED_INPUT: &str = "pair_mem_seed";

/// Address `base + disp`, with the constant folded and `disp == 0` left bare.
fn addr(base: &E, disp: i64) -> E {
    if disp == 0 {
        base.clone()
    } else {
        base.clone().bvadd(E::bv_const(disp as u64, 64))
    }
}

/// The slot whose symbolic value a transfer slot reads.
///
/// A STORE may name the SAME register in both transfer slots (the encoder
/// permits a repeated source; only duplicate LOAD destinations are
/// constrained-unpredictable). Both lanes then carry ONE value, so slot 1
/// must share slot 0's symbolic input rather than get an independent one —
/// otherwise the model would demand two different payloads from one register.
fn value_slot(intent: &PairMemoryIntent, slot: usize) -> usize {
    if slot == 1 && intent.rt2 == intent.rt {
        0
    } else {
        slot
    }
}

/// Byte `index` of transfer slot `slot`.
///
/// A lane wider than 64 bits (the Q pair) is carried as two 64-bit inputs, so
/// no symbolic input ever exceeds the evaluator's 64-bit variable width. A
/// zero-register STORE source contributes constant zero bytes.
fn transfer_byte(intent: &PairMemoryIntent, slot: usize, index: u32) -> E {
    if intent.zero_transfer[slot] {
        return E::bv_const(0, 8);
    }
    let slot = value_slot(intent, slot);
    let half = if index < 8 { "lo" } else { "hi" };
    let width = if intent.element_bytes >= 8 { 64 } else { 32 };
    let name = if intent.element_bytes > 8 {
        format!("pair_slot{slot}_{half}")
    } else {
        format!("pair_slot{slot}")
    };
    let bit = (index % 8) * 8;
    E::var(name, width).extract(bit + 7, bit)
}

/// Symbolic name of the base register a DECODED `Rn` names when it is not the
/// instruction's base operand.
const OTHER_BASE_INPUT: &str = "pair_decoded_other_base";

/// The declared inputs this obligation's value model reads.
fn model_inputs(intent: &PairMemoryIntent) -> Vec<(String, u32)> {
    let mut inputs = vec![(BASE_INPUT.to_string(), 64)];
    for slot in 0..2 {
        // A zero-register transfer contributes constants, and a repeated
        // store source shares slot 0's input; declare neither twice.
        if intent.zero_transfer[slot] || value_slot(intent, slot) != slot {
            continue;
        }
        if intent.element_bytes > 8 {
            inputs.push((format!("pair_slot{slot}_lo"), 64));
            inputs.push((format!("pair_slot{slot}_hi"), 64));
        } else {
            inputs.push((
                format!("pair_slot{slot}"),
                if intent.element_bytes >= 8 { 64 } else { 32 },
            ));
        }
    }
    inputs.push((SEED_INPUT.to_string(), 8));
    inputs
}

/// Byte-addressed store list, oldest first: `(address, byte value)`.
type ByteStores = Vec<(E, E)>;

/// Exact McCarthy read-over-write of a byte store list.
///
/// Stores are supplied oldest-to-newest, so the last matching store is the
/// outermost `ite` and wins, exactly as an SMT array `store` chain does. This
/// is the same scalar expansion `memory_proofs::qf_bv_select_after_stores`
/// uses, kept local so no array-sorted term enters the obligation (the
/// evaluation lane this obligation is discharged on cannot interpret one).
fn select_after(stores: &ByteStores, query: &E, seed: &E) -> E {
    let mut selected = seed.clone();
    for (store_addr, store_value) in stores {
        selected = E::ite(
            query.clone().eq_expr(store_addr.clone()),
            store_value.clone(),
            selected,
        );
    }
    selected
}

/// Byte indices probed inside one lane.
///
/// For a lane of at most eight bytes every byte is probed. A sixteen-byte (Q)
/// lane probes its first two and last two bytes: the within-lane
/// little-endian decomposition is the SAME construction on both sides of this
/// obligation and is not what it is here to check, while every hazard it does
/// check — a displaced effective address, a mis-scaled offset, a wrong element
/// width, a transposed transfer field — moves the first or the last byte of a
/// lane, and the two guard bytes bracketing the footprint catch an access that
/// is wider than intended.
fn probe_indices(element_bytes: u32) -> Vec<i64> {
    if element_bytes <= 8 {
        (0..i64::from(element_bytes)).collect()
    } else {
        let last = i64::from(element_bytes) - 1;
        vec![0, 1, last - 1, last]
    }
}

/// Which transfer slot a decoded five-bit field names, if any.
///
/// Resolution is positional and first-match, so an instruction whose two
/// transfer slots share a hardware field (only possible for a STORE, where the
/// encoder permits a repeated source) resolves to slot 0 for both — correct,
/// because the two lanes then carry the same value.
fn slot_of_field(intent: &PairMemoryIntent, field: u8) -> Option<usize> {
    if field == intent.rt {
        Some(0)
    } else if field == intent.rt2 {
        Some(1)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Obligation construction
// ---------------------------------------------------------------------------

/// Reconstruct the pair-memory obligation for one emitted instruction.
///
/// Returns `None` — no credit — when the instruction is not an admitted pair
/// shape, when its word does not decode, or when the decoded direction or
/// register bank disagrees with the operands'. A direction disagreement cannot
/// be stated as a value equality (a store has no loaded value and a load has
/// no stored byte), and a bank disagreement names registers the operands do
/// not, so both are refused here rather than refuted; the negative controls
/// `decoded_direction_flip_is_refused` and
/// `register_bank_flip_at_equal_width_is_refused` pin that.
pub fn pair_memory_obligation(inst: &MachInst) -> Option<ProofObligation> {
    pair_memory_obligation_and_word(inst).map(|(obligation, _)| obligation)
}

/// [`pair_memory_obligation`] together with the word it judges (the word
/// [`pair_memory_word`] re-derives from the instruction). The function
/// verifier hands that word to the Formal-only bound-memory rule, which
/// requires the certified FORM to be the form of this word
/// ([`crate::bound_memory_authority`]).
pub fn pair_memory_obligation_and_word(inst: &MachInst) -> Option<(ProofObligation, u32)> {
    let intent = pair_memory_intent(inst)?;
    let word = pair_memory_word(&intent)?;
    build_obligation(&intent, word).map(|obligation| (obligation, word))
}

/// [`pair_memory_obligation`] with the encoded word supplied by the caller.
///
/// Test-only seam for the negative controls: hand it a MUTATED word and the
/// resulting obligation must be REFUTED by the evaluation lane (or refused,
/// for a direction flip). Production callers use [`pair_memory_obligation`],
/// which always encodes the word from the instruction itself.
#[doc(hidden)]
pub fn pair_memory_obligation_from_word(inst: &MachInst, word: u32) -> Option<ProofObligation> {
    let intent = pair_memory_intent(inst)?;
    build_obligation(&intent, word)
}

fn build_obligation(intent: &PairMemoryIntent, word: u32) -> Option<ProofObligation> {
    let decoded = decode_pair_memory_word(word)?;
    if decoded.load != intent.load {
        return None;
    }
    // The decoded transfer fields are matched to the operands by register
    // NUMBER below (`slot_of_field`). A word whose `V` bit names the other
    // register file transfers registers the intent never mentions (`S1` is not
    // `W1`). At an equal element width (W/S, X/D) nothing in the byte model
    // observes that, so it is refused, as for an unnamed transfer field. A
    // bank change that also changes the width (X/Q) moves the lanes and is
    // refuted below (`wrong_element_width_is_refuted`).
    if decoded.simd != intent.simd && decoded.element_bytes == intent.element_bytes {
        return None;
    }

    let base = E::var(BASE_INPUT, 64);
    let seed = E::var(SEED_INPUT, 8);

    // Intent side: the scalarized two-access sequence the pair is a fusion of,
    // both displacements measured from the ORIGINAL base.
    let intent_n = i64::from(intent.element_bytes);
    let intent_s0 = intent.mode.access_displacement(intent.offset);
    let intent_s1 = intent_s0 + intent_n;
    let intent_lane_disp = [intent_s0, intent_s1];

    // Machine side: the architectural pair access denoted by the decoded word.
    let mach_n = i64::from(decoded.element_bytes);
    let mach_s0 = decoded.mode.access_displacement(decoded.offset);
    let mach_s1 = mach_s0 + mach_n;
    let mach_lane_disp = [mach_s0, mach_s1];
    // The machine's base register is whatever `Rn` names. When that is not the
    // instruction's base operand the access uses an UNRELATED register, modelled
    // as a fresh unconstrained input so the addresses genuinely differ.
    let base_matches = decoded.rn == intent.rn;
    let mach_base = if base_matches {
        base.clone()
    } else {
        E::var(OTHER_BASE_INPUT, 64)
    };

    let mut conjuncts: Vec<E> = Vec::new();

    if intent.load {
        // Seed memory with the payload the scalarized intent expects to find at
        // each lane address.
        let mut seeded: ByteStores = Vec::new();
        for (slot, disp) in intent_lane_disp.into_iter().enumerate() {
            for k in 0..intent_n {
                seeded.push((addr(&base, disp + k), transfer_byte(intent, slot, k as u32)));
            }
        }
        // Each machine transfer must deliver, to the register its decoded field
        // names, exactly that lane's intended payload.
        for (transfer, field) in [(0usize, decoded.rt), (1usize, decoded.rt2)] {
            let Some(dest_slot) = slot_of_field(intent, field) else {
                // The decoded field names a register that is neither transfer
                // operand: the load would write somewhere the intent never
                // mentions. Refuse rather than model an unnamed destination.
                return None;
            };
            let probed = probe_indices(intent.element_bytes.max(decoded.element_bytes));
            for k in probed {
                // Bytes the machine access does not transfer, and bytes the
                // named register does not have, are modelled as zero so a
                // width disagreement is observable rather than silent.
                let loaded = if k < mach_n {
                    select_after(
                        &seeded,
                        &addr(&mach_base, mach_lane_disp[transfer] + k),
                        &seed,
                    )
                } else {
                    E::bv_const(0, 8)
                };
                let expected = if k < intent_n {
                    transfer_byte(intent, dest_slot, k as u32)
                } else {
                    E::bv_const(0, 8)
                };
                conjuncts.push(loaded.eq_expr(expected));
            }
        }
    } else {
        // Intent side: two INDEPENDENT scalar stores at the lane addresses.
        let mut intent_mem: ByteStores = Vec::new();
        for (slot, disp) in intent_lane_disp.into_iter().enumerate() {
            for k in 0..intent_n {
                intent_mem.push((addr(&base, disp + k), transfer_byte(intent, slot, k as u32)));
            }
        }
        // Machine side: the decoded pair store, whose lane payloads come from
        // the registers its decoded fields name.
        let mut mach_mem: ByteStores = Vec::new();
        for (transfer, disp) in mach_lane_disp.into_iter().enumerate() {
            let field = if transfer == 0 {
                decoded.rt
            } else {
                decoded.rt2
            };
            let Some(source_slot) = slot_of_field(intent, field) else {
                // The decoded field names neither transfer operand: the store
                // would take its payload from a register the intent never
                // mentions. Refuse rather than model an unnamed source.
                return None;
            };
            for k in 0..mach_n {
                let byte = if k < intent_n {
                    transfer_byte(intent, source_slot, k as u32)
                } else {
                    E::bv_const(0, 8)
                };
                mach_mem.push((addr(&mach_base, disp + k), byte));
            }
        }
        // Probe the intended footprint plus one guard byte on each side, and
        // the machine footprint, so a store that lands anywhere the intent does
        // not is observed at one of the probes.
        let mut probes: Vec<E> = Vec::new();
        let push = |probes: &mut Vec<E>, address: E| {
            if !probes.contains(&address) {
                probes.push(address);
            }
        };
        push(&mut probes, addr(&base, intent_s0 - 1));
        for disp in intent_lane_disp {
            for k in probe_indices(intent.element_bytes) {
                push(&mut probes, addr(&base, disp + k));
            }
        }
        push(&mut probes, addr(&base, intent_s1 + intent_n));
        for disp in mach_lane_disp {
            for k in probe_indices(decoded.element_bytes) {
                push(&mut probes, addr(&mach_base, disp + k));
            }
        }
        for probe in &probes {
            conjuncts.push(
                select_after(&intent_mem, probe, &seed)
                    .eq_expr(select_after(&mach_mem, probe, &seed)),
            );
        }
    }

    // The base register after the access: written back by exactly the
    // immediate for the indexed forms, unchanged for the signed-offset form.
    let intent_writeback = addr(&base, intent.mode.writeback_displacement(intent.offset));
    let mach_writeback = addr(
        &mach_base,
        decoded.mode.writeback_displacement(decoded.offset),
    );
    conjuncts.push(intent_writeback.eq_expr(mach_writeback));

    let mut machine_side = conjuncts.pop()?;
    while let Some(next) = conjuncts.pop() {
        machine_side = next.and_expr(machine_side);
    }

    let mut inputs = model_inputs(intent);
    if !base_matches {
        inputs.push((OTHER_BASE_INPUT.to_string(), 64));
    }

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED PairMemory_{}_{}_{}B_off{} -> {:?} \
             (real-operand, decoded-word: both transfers and base writeback)",
            if intent.load { "LDP" } else { "STP" },
            intent.mode.label(),
            intent.element_bytes,
            intent.offset,
            intent.opcode,
        ),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: machine_side,
        inputs,
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: format!("{:?}", intent.opcode),
            // Two transfer lanes: the source schema this fusion scalarizes to.
            arity: 2,
        },
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::{VerificationConfig, discharge_reconstructed_obligation};
    use crate::verify::VerificationResult;
    use trust_cg_ir::aarch64_regs::PReg;

    /// Small but edge-inclusive sample budget: the 36-point edge battery plus
    /// this many random tuples. Every refutation below is found by the edge
    /// battery or within a handful of samples.
    fn config() -> VerificationConfig {
        VerificationConfig::with_sample_count(256)
    }

    fn p(encoding: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(encoding))
    }

    fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, operands)
    }

    fn verdict(obligation: &ProofObligation) -> VerificationResult {
        discharge_reconstructed_obligation(obligation, obligation, &config()).0
    }

    fn is_valid(obligation: &ProofObligation) -> bool {
        matches!(verdict(obligation), VerificationResult::Valid)
    }

    fn is_refuted(obligation: &ProofObligation) -> bool {
        matches!(verdict(obligation), VerificationResult::Invalid { .. })
    }

    /// `STP X29, X30, [SP, #-16]!` — main's leaf frame prologue.
    fn frame_save() -> MachInst {
        inst(
            AArch64Opcode::StpPreIndex,
            vec![
                p(29),
                p(30),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(-16),
            ],
        )
    }

    /// `LDP X29, X30, [SP], #16` — main's leaf frame epilogue.
    fn frame_restore() -> MachInst {
        inst(
            AArch64Opcode::LdpPostIndex,
            vec![
                p(29),
                p(30),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(16),
            ],
        )
    }

    // -- admission + discharge ---------------------------------------------

    #[test]
    fn frame_prologue_and_epilogue_earn_nondegenerate_reconstructed_credit() {
        for instruction in [frame_save(), frame_restore()] {
            let obligation = pair_memory_obligation(&instruction)
                .unwrap_or_else(|| panic!("{instruction:?} must be admitted"));
            assert!(
                obligation.is_reconstructed(),
                "{instruction:?}: machine side must carry Reconstructed provenance"
            );
            assert!(
                !obligation.is_degenerate(),
                "{instruction:?}: obligation must not be an X==X identity"
            );
            assert!(
                is_valid(&obligation),
                "{instruction:?}: {:?}",
                verdict(&obligation)
            );
        }
    }

    /// Every well-formed pair shape the encoder admits — six opcodes, five
    /// transfer banks, four bases, the extreme and zero scaled offsets —
    /// discharges. This is the shape set the frame prologue/epilogue and the
    /// callee-save stores actually emit.
    #[test]
    fn every_well_formed_pair_shape_discharges() {
        let mut checked = 0usize;
        let mut failures: Vec<String> = Vec::new();
        for opcode in PAIR_OPCODES {
            let q_only = matches!(
                opcode,
                AArch64Opcode::NeonLdpQPost | AArch64Opcode::NeonStpQPost
            );
            for (bank, element) in [(0u16, 8i64), (32, 4), (128, 4), (96, 8), (64, 16)] {
                if q_only && bank != 64 {
                    continue;
                }
                for base in [p(3), p(29), MachOperand::Special(SpecialReg::SP), p(31)] {
                    for scaled in [-64i64, -1, 0, 1, 63] {
                        let operands = vec![
                            p(bank + 1),
                            p(bank + 2),
                            base.clone(),
                            MachOperand::Imm(scaled * element),
                        ];
                        let instruction = inst(opcode, operands);
                        let Some(obligation) = pair_memory_obligation(&instruction) else {
                            failures.push(format!("{instruction:?}: refused"));
                            continue;
                        };
                        checked += 1;
                        if !is_valid(&obligation) {
                            failures.push(format!("{instruction:?}: {:?}", verdict(&obligation)));
                        }
                    }
                }
            }
        }
        assert_eq!(checked, 440, "shape corpus size changed");
        assert!(
            failures.is_empty(),
            "{} well-formed shapes did not discharge; first 8: {:#?}",
            failures.len(),
            &failures[..failures.len().min(8)]
        );
    }

    /// A three-operand pair instruction is the legal zero-offset form.
    #[test]
    fn three_operand_zero_offset_form_is_admitted() {
        let instruction = inst(AArch64Opcode::StpRI, vec![p(1), p(2), p(3)]);
        let intent = pair_memory_intent(&instruction).expect("3-operand form is legal");
        assert_eq!(intent.offset, 0);
        assert!(is_valid(&pair_memory_obligation(&instruction).unwrap()));
    }

    /// A STORE may repeat its source register; the zero register is a legal
    /// store source and contributes constant zero bytes.
    #[test]
    fn duplicate_and_zero_register_store_sources_are_admitted() {
        for operands in [
            vec![p(1), p(1), p(3), MachOperand::Imm(0)],
            vec![
                MachOperand::Special(SpecialReg::XZR),
                p(2),
                p(3),
                MachOperand::Imm(0),
            ],
            vec![
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::Special(SpecialReg::XZR),
                p(3),
                MachOperand::Imm(0),
            ],
        ] {
            let instruction = inst(AArch64Opcode::StpRI, operands);
            let obligation = pair_memory_obligation(&instruction)
                .unwrap_or_else(|| panic!("{instruction:?} must be admitted"));
            assert!(is_valid(&obligation), "{instruction:?}");
        }
    }

    // -- refusal controls (no credit, and no widened admission) -------------

    const PAIR_OPCODES: [AArch64Opcode; 6] = [
        AArch64Opcode::StpRI,
        AArch64Opcode::LdpRI,
        AArch64Opcode::StpPreIndex,
        AArch64Opcode::LdpPostIndex,
        AArch64Opcode::NeonLdpQPost,
        AArch64Opcode::NeonStpQPost,
    ];

    #[test]
    fn malformed_pair_shapes_are_refused_outright() {
        let cases: Vec<(&str, AArch64Opcode, Vec<MachOperand>)> = vec![
            ("no operands", AArch64Opcode::StpRI, vec![]),
            ("one operand", AArch64Opcode::StpRI, vec![p(1)]),
            (
                "five operands",
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(0), MachOperand::Imm(0)],
            ),
            (
                "register where the immediate belongs",
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), p(4)],
            ),
            (
                "SP as a transfer register",
                AArch64Opcode::StpRI,
                vec![p(31), p(2), p(3), MachOperand::Imm(0)],
            ),
            (
                "WSP as a transfer register",
                AArch64Opcode::StpRI,
                vec![p(33), p(63), p(3), MachOperand::Imm(0)],
            ),
            (
                "mismatched transfer classes",
                AArch64Opcode::StpRI,
                vec![p(1), p(33), p(3), MachOperand::Imm(0)],
            ),
            (
                "32-bit base",
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(35), MachOperand::Imm(0)],
            ),
            (
                "XZR base",
                AArch64Opcode::StpRI,
                vec![
                    p(1),
                    p(2),
                    MachOperand::Special(SpecialReg::XZR),
                    MachOperand::Imm(0),
                ],
            ),
            (
                "misaligned offset",
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(1)],
            ),
            (
                "offset past the signed scaled imm7 window",
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(64 * 8)],
            ),
            (
                "virtual transfer register",
                AArch64Opcode::StpRI,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, RegClass::Gpr64)),
                    p(2),
                    p(3),
                    MachOperand::Imm(0),
                ],
            ),
            (
                "duplicate load destinations",
                AArch64Opcode::LdpRI,
                vec![p(1), p(1), p(3), MachOperand::Imm(0)],
            ),
            (
                "zero-register load destination",
                AArch64Opcode::LdpRI,
                vec![
                    MachOperand::Special(SpecialReg::XZR),
                    p(2),
                    p(3),
                    MachOperand::Imm(0),
                ],
            ),
            (
                "writeback base overlaps a GPR transfer",
                AArch64Opcode::StpPreIndex,
                vec![p(3), p(2), p(3), MachOperand::Imm(-16)],
            ),
            (
                "Q-only alias with a non-Q bank",
                AArch64Opcode::NeonStpQPost,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
        ];
        let mut wrong = Vec::new();
        for (why, opcode, operands) in cases {
            let instruction = inst(opcode, operands);
            if pair_memory_intent(&instruction).is_some() {
                wrong.push(format!("{why}: {instruction:?}"));
            }
        }
        assert!(wrong.is_empty(), "admitted malformed shapes: {wrong:#?}");
    }

    #[test]
    fn non_pair_opcodes_are_not_touched() {
        for opcode in [
            AArch64Opcode::StrRI,
            AArch64Opcode::LdrRI,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::AddRI,
        ] {
            let instruction = inst(opcode, vec![p(1), p(2), p(3), MachOperand::Imm(0)]);
            assert!(
                pair_memory_intent(&instruction).is_none(),
                "{opcode:?} is not a pair opcode"
            );
        }
    }

    // -- encode / decode ----------------------------------------------------

    #[test]
    fn encode_decode_round_trips_every_admitted_shape() {
        let mut checked = 0usize;
        for opcode in PAIR_OPCODES {
            let q_only = matches!(
                opcode,
                AArch64Opcode::NeonLdpQPost | AArch64Opcode::NeonStpQPost
            );
            for (bank, element) in [(0u16, 8i64), (32, 4), (128, 4), (96, 8), (64, 16)] {
                if q_only && bank != 64 {
                    continue;
                }
                for scaled in [-64i64, -3, 0, 5, 63] {
                    let instruction = inst(
                        opcode,
                        vec![
                            p(bank + 1),
                            p(bank + 2),
                            p(3),
                            MachOperand::Imm(scaled * element),
                        ],
                    );
                    let intent = pair_memory_intent(&instruction).expect("admitted");
                    let word = pair_memory_word(&intent).expect("encodable");
                    let decoded = decode_pair_memory_word(word).expect("decodable");
                    assert_eq!(decoded.load, intent.load, "{instruction:?}");
                    assert_eq!(decoded.mode, intent.mode, "{instruction:?}");
                    assert_eq!(
                        decoded.element_bytes, intent.element_bytes,
                        "{instruction:?}"
                    );
                    assert_eq!(decoded.simd, intent.simd, "{instruction:?}");
                    assert_eq!(decoded.offset, intent.offset, "{instruction:?}");
                    assert_eq!(decoded.rt, intent.rt, "{instruction:?}");
                    assert_eq!(decoded.rt2, intent.rt2, "{instruction:?}");
                    assert_eq!(decoded.rn, intent.rn, "{instruction:?}");
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 110, "round-trip corpus size changed");
    }

    /// The four words the encoder's own pin table records for
    /// `[W1, W2, X2, #0]` (`pipeline.rs` regalloc projection). Field layout
    /// agreement with the codegen encoder is checked exhaustively by
    /// `crates/trust-cg-codegen/tests/aarch64_pair_memory_decode.rs`; these
    /// four are the in-crate anchor so a field-placement slip here is caught
    /// without the cross-crate test.
    #[test]
    fn known_encoder_words_match() {
        for (opcode, expected) in [
            (AArch64Opcode::StpRI, 0x2900_0440u32),
            (AArch64Opcode::LdpRI, 0x2940_0440),
            (AArch64Opcode::StpPreIndex, 0x2980_0440),
            (AArch64Opcode::LdpPostIndex, 0x28c0_0440),
        ] {
            let instruction = inst(opcode, vec![p(32), p(33), p(2), MachOperand::Imm(0)]);
            let intent = pair_memory_intent(&instruction).expect("admitted");
            assert_eq!(
                pair_memory_word(&intent),
                Some(expected),
                "{opcode:?} word mismatch"
            );
        }
    }

    #[test]
    fn non_pair_and_reserved_words_do_not_decode() {
        // LDPSW (V=0, opc=0b01) and the unallocated opc=0b11 rows.
        assert!(decode_pair_memory_word(0x6940_0440).is_none(), "LDPSW");
        assert!(decode_pair_memory_word(0xe940_0440).is_none(), "opc=0b11");
        // The non-temporal (STNP/LDNP) encoding class, mode = 0b00.
        assert!(decode_pair_memory_word(0x2800_0440).is_none(), "STNP");
        // Not a load/store-pair encoding class at all.
        assert!(decode_pair_memory_word(0xd503_201f).is_none(), "NOP");
    }

    // -- negative controls: the refutations that give the theorem its force --

    /// Rebuild the obligation from a MUTATED word and require a refutation.
    fn control(instruction: &MachInst, mutate: impl Fn(u32) -> u32, why: &str) {
        let intent = pair_memory_intent(instruction).expect("admitted");
        let word = pair_memory_word(&intent).expect("encodable");
        let mutated = mutate(word);
        assert_ne!(mutated, word, "{why}: control did not change the word");
        let obligation = pair_memory_obligation_from_word(instruction, mutated)
            .unwrap_or_else(|| panic!("{why}: control must build an obligation, not refuse"));
        assert!(
            is_refuted(&obligation),
            "{why}: mutated word {mutated:#010x} was NOT refuted ({:?})",
            verdict(&obligation)
        );
    }

    #[test]
    fn transposed_transfer_fields_are_refuted() {
        for instruction in [
            frame_save(),
            frame_restore(),
            inst(
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
            inst(
                AArch64Opcode::LdpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(-8)],
            ),
        ] {
            control(
                &instruction,
                |w| {
                    let rt = w & 0x1f;
                    let rt2 = (w >> 10) & 0x1f;
                    (w & !0x7c1f) | (rt << 10) | rt2
                },
                "Rt/Rt2 transposed",
            );
        }
    }

    #[test]
    fn wrong_base_field_is_refuted() {
        control(
            &inst(
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
            |w| (w & !(0x1f << 5)) | (7 << 5),
            "Rn names a different register",
        );
    }

    #[test]
    fn lost_or_added_writeback_is_refuted() {
        // Pre-index demoted to plain signed offset: the base is not updated.
        control(
            &frame_save(),
            |w| (w & !(0b11 << 23)) | (0b10 << 23),
            "pre-index writeback dropped",
        );
        // Signed offset promoted to pre-index: the base is updated when the
        // intent says it must not be.
        control(
            &inst(
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
            |w| (w & !(0b11 << 23)) | (0b11 << 23),
            "writeback added to the offset form",
        );
        // Post-index demoted to signed offset: both the access address and the
        // writeback move.
        control(
            &frame_restore(),
            |w| (w & !(0b11 << 23)) | (0b10 << 23),
            "post-index access folded into the address",
        );
        // Pre-index read as post-index: the access happens at the old base.
        control(
            &frame_save(),
            |w| (w & !(0b11 << 23)) | (0b01 << 23),
            "pre-index read as post-index",
        );
    }

    #[test]
    fn mis_scaled_immediate_is_refuted() {
        for instruction in [
            frame_save(),
            frame_restore(),
            inst(
                AArch64Opcode::LdpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
        ] {
            control(
                &instruction,
                |w| w.wrapping_add(1 << 15),
                "imm7 off by one scaled unit",
            );
        }
    }

    #[test]
    fn wrong_element_width_is_refuted() {
        // V flipped on an X pair: opc = 0b10 is re-read as a 16-byte Q pair,
        // so both transfer addresses and the second lane's base move.
        control(
            &inst(
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
            |w| w | (1 << 26),
            "X pair re-read as Q",
        );
        // opc narrowed on an X pair: 0b10 -> 0b00 re-reads it as a 4-byte W
        // pair, halving the lane spacing and the offset scale.
        control(
            &inst(
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
            |w| w & !(0b11 << 30),
            "X pair re-read as W",
        );
        // D pair re-read as S: opc 0b01 -> 0b00 with V still set.
        control(
            &inst(
                AArch64Opcode::LdpRI,
                vec![p(97), p(98), p(3), MachOperand::Imm(16)],
            ),
            |w| w & !(0b11 << 30),
            "D pair re-read as S",
        );
    }

    /// A direction flip cannot be stated as a value equality — a store has no
    /// loaded value and a load has no stored byte — so it is REFUSED (no
    /// credit) rather than refuted.
    #[test]
    fn decoded_direction_flip_is_refused() {
        for instruction in [frame_save(), frame_restore()] {
            let intent = pair_memory_intent(&instruction).expect("admitted");
            let word = pair_memory_word(&intent).expect("encodable");
            assert!(
                pair_memory_obligation_from_word(&instruction, word ^ (1 << 22)).is_none(),
                "{instruction:?}: an L-bit flip must refuse, never credit"
            );
        }
    }

    /// A `V` flip at an equal element width (W <-> S, X <-> D) moves no address
    /// and no byte, so the byte model cannot observe it; the decoded word names
    /// registers of the other register file, and the obligation is refused.
    /// Before this check the evaluation accepted all 240 such W/X/S/D defects
    /// of `tests/aarch64_pair_memory_wrong_theorems.rs`.
    #[test]
    fn register_bank_flip_at_equal_width_is_refused() {
        for instruction in [
            frame_save(),
            frame_restore(),
            inst(
                AArch64Opcode::StpRI,
                vec![p(33), p(34), p(3), MachOperand::Imm(8)],
            ),
            inst(
                AArch64Opcode::LdpRI,
                vec![p(97), p(98), p(3), MachOperand::Imm(-8)],
            ),
            inst(
                AArch64Opcode::StpRI,
                vec![p(129), p(130), p(3), MachOperand::Imm(4)],
            ),
        ] {
            let intent = pair_memory_intent(&instruction).expect("admitted");
            let word = pair_memory_word(&intent).expect("encodable");
            // Same width, other bank: (opc 10, V 0) X <-> (opc 01, V 1) D, and
            // (opc 00, V 0) W <-> (opc 00, V 1) S.
            let other_bank = match (word >> 30, (word >> 26) & 1) {
                (0b10, 0) => (word & !(0b11 << 30)) | (0b01 << 30) | (1 << 26),
                (0b01, 1) => (word & !((0b11 << 30) | (1 << 26))) | (0b10 << 30),
                (0b00, _) => word ^ (1 << 26),
                _ => unreachable!("no Q pair in this list"),
            };
            let decoded = decode_pair_memory_word(other_bank).expect("still a pair word");
            assert_eq!(decoded.element_bytes, intent.element_bytes);
            assert_ne!(decoded.simd, intent.simd);
            assert!(
                pair_memory_obligation_from_word(&instruction, other_bank).is_none(),
                "{instruction:?}: bank flip {other_bank:#010x} must refuse, never hold"
            );
        }
    }

    /// Bit 25 is a fixed zero of every load/store class; a word with it set is
    /// a data-processing instruction, not a pair. Before this check the decoder
    /// ignored it and the evaluation accepted all 330 such defects of
    /// `tests/aarch64_pair_memory_wrong_theorems.rs` (the fields it does read
    /// were unchanged).
    #[test]
    fn a_word_with_bit_25_set_is_not_a_pair() {
        for instruction in [frame_save(), frame_restore()] {
            let intent = pair_memory_intent(&instruction).expect("admitted");
            let word = pair_memory_word(&intent).expect("encodable");
            assert_eq!(word & (1 << 25), 0, "the encoder never sets bit 25");
            assert!(decode_pair_memory_word(word | (1 << 25)).is_none());
            assert!(pair_memory_obligation_from_word(&instruction, word | (1 << 25)).is_none());
        }
        // `ADDS X0, X1, X2` (add/subtract, shifted register, S = 1) has bits
        // [29:27] = 101 and bit 25 = 1.
        assert!(decode_pair_memory_word(0xab02_0020).is_none());
    }

    /// A decoded transfer field naming neither transfer operand is refused:
    /// the access would touch a register the intent never mentions.
    #[test]
    fn unnamed_transfer_field_is_refused() {
        let instruction = inst(
            AArch64Opcode::StpRI,
            vec![p(1), p(2), p(3), MachOperand::Imm(16)],
        );
        let intent = pair_memory_intent(&instruction).expect("admitted");
        let word = pair_memory_word(&intent).expect("encodable");
        // Rt := x9, which is neither transfer operand.
        assert!(pair_memory_obligation_from_word(&instruction, (word & !0x1f) | 9).is_none());
    }

    /// An unmutated word must NOT be refuted — otherwise the controls above
    /// would pass for the wrong reason.
    #[test]
    fn unmutated_words_are_not_refuted() {
        for instruction in [
            frame_save(),
            frame_restore(),
            inst(
                AArch64Opcode::StpRI,
                vec![p(1), p(2), p(3), MachOperand::Imm(16)],
            ),
            inst(
                AArch64Opcode::LdpRI,
                vec![p(97), p(98), p(3), MachOperand::Imm(-8)],
            ),
        ] {
            let intent = pair_memory_intent(&instruction).expect("admitted");
            let word = pair_memory_word(&intent).expect("encodable");
            let obligation =
                pair_memory_obligation_from_word(&instruction, word).expect("obligation");
            assert!(is_valid(&obligation), "{instruction:?}");
        }
    }
}
