// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Reference: Arm DDI0602 (2025-03) LDP/STP general and SIMD/FP
//            (shared decode "LoadStorePair"), and
//            crates/trust-cg-codegen/src/aarch64/encode.rs `encode_pair_memory`.
//
// Hand re-derivation of the archived trust-cg commit 7af30f92d
// (`pair_memory_proofs.rs`, never merged) beside this tree's per-instruction
// pair lane (`aarch64_pair_memory_proofs`). The form theorems and the binder
// are that commit's; what changed is how they are consumed.

//! Operand-bound AArch64 pair-memory (`STP`/`LDP`) FORM theorems: the formal
//! credit route for pair rows.
//!
//! # Why this module exists
//!
//! Owner ruling 2026-09-29: a pair `LDP`/`STP` row earns instruction credit
//! ONLY from a formal proof, never from statistical sampling.
//!
//! [`crate::aarch64_pair_memory_proofs`] builds one obligation per emitted
//! instruction from its CONCRETE decoded word. That obligation is the lane's
//! refutation power (a displaced, mis-scaled, mis-sized, transposed or
//! writeback-losing word refutes), but it cannot carry a formal proof: with a
//! concrete offset every address is `base + constant`, AY's rewriter closes a
//! correct instance before the bit-blaster runs (so no DRAT certificate can
//! be minted over it), and its Alethe self-check was rejected for all 70
//! distinct faithful instances measured on 2026-09-29. There are also more
//! concrete instances (every scaled `imm7`, bank and mode) than any committed
//! certificate set could carry.
//!
//! This module supplies one theorem per concrete architectural FORM —
//! `(STP|LDP) x (signed-offset|pre-index|post-index) x register bank x
//! element width` — quantified over every admitted offset, and a binder that
//! maps a concrete emitted [`MachInst`] to exactly one form (or refuses). A
//! form theorem states, for ALL base values, ALL admitted offsets, ALL
//! transfer register values and ALL memory contents:
//!
//! * STP: the byte at every address `q` after the instruction (both stored
//!   slots, little-endian, and every other byte unchanged), and the base
//!   register after the instruction (writeback or unchanged);
//! * LDP: every byte `j` of both destination registers (the loaded element
//!   bytes, and the architectural zero-extension of the register above the
//!   element width: W→X clears 63:32, S/D→V clears 127:element), and the base
//!   register after the instruction.
//!
//! # The two sides
//!
//! * **Machine side** follows the Arm pseudocode from the ENCODED fields: the
//!   encoder's 7-bit field `imm7 = (off / dbytes)<6:0>`, the decoder's
//!   `offset = SignExtend(imm7, 64) << scale`, `address = (postindex ? X[n] :
//!   X[n] + offset)`, one write of `2*dbytes` bytes at `address` (or one read
//!   of both elements), and `X[n] = X[n] + offset` exactly when `wback`.
//! * **Intent side** is the validated pair intent the MachIR carries
//!   (`[Rt, Rt2, Xn|SP, #off]` with the literal byte offset): two INDEPENDENT
//!   scalar transfers — a store (or load) of element 1 at `S` composed with a
//!   store (or load) of element 2 at `S + dbytes` — plus the intended base
//!   update `S = base + off` for pre-index / signed-offset and `base + off`
//!   after a post-index access.
//!
//! The two sides share no address, byte-extraction or composition
//! subexpression (the machine side decodes `imm7` and extracts bytes by a
//! variable shift; the intent side adds the literal offset and extracts bytes
//! from a constant-index table), so the obligation is structurally
//! non-degenerate and every mutation in [`PairMachineMutation`] refutes.
//!
//! # Memory encoding (pure QF_BV, no arrays)
//!
//! * STP is observed through a free query address `q` and its free original
//!   byte `m`: the post-state byte at `q` is a read-over-write `ite` chain.
//!   Quantifying over `q` covers every byte of the 2^64 address space, so the
//!   frame condition ("changes no other byte") is part of the theorem.
//! * LDP reads a free single-point memory `M(x) = ite(x == p, c, d)`. This is
//!   complete for the stated equality: each observed register byte is a single
//!   memory read (or constant zero), and two reads `M(a)`, `M(b)` agree for all
//!   `(p, c, d)` iff `a == b` (choose `p = a`, `c != d`); a read never equals
//!   the constant zero for all `d`. So any address, element-order, slot-order
//!   or zero-extension difference is a counterexample.
//!
//! The combined post-state is projected through a free selector `sel`:
//! `ite(sel == 0, obs0, ite(sel == 1, obs1, base'))`, so one equality over all
//! `sel` is exactly the conjunction of the component equalities.
//!
//! # What binds a concrete instruction to a form
//!
//! [`bind_pair_memory_instruction`] is an INDEPENDENT reimplementation of the
//! pair admission contract (it shares no code with the encoder's descriptor):
//! physical W/X/ZR or S/D/Q transfers of one bank and width, a canonical X/SP
//! base, an aligned signed scaled `imm7` offset, distinct LDP destinations,
//! no GPR transfer/base overlap under writeback, Q-only aliases carrying Q
//! registers. It additionally REFUSES a signed-offset GPR LDP that overwrites
//! its own base, because the bound register model keeps the base value there.
//! The selected theorem is quantified over every operand VALUE and over every
//! admitted offset `k * dbytes` (signed 7-bit `k`); the binder checks that the
//! concrete offset lies in exactly that set.
//!
//! The walk additionally requires this binding to AGREE, field for field, with
//! [`crate::aarch64_pair_memory_proofs::pair_memory_intent`] (the lane's own
//! admission), requires that lane's concrete-word obligation to have run and
//! held, and requires the word it judged to decode to this binding
//! ([`decode_pair_memory_binding`]); see [`crate::bound_memory_authority`]. The emitted word is bound to
//! these MachIR fields by the independent strict AArch64 decode check
//! (`trust-cg-codegen` `decode_check`, pair arm), which re-derives
//! opc/V/L/mode/imm7/Rt/Rt2/Rn from the bytes and enforces by default. That
//! gate, not this module, is the byte-level authority.
//!
//! # Authority
//!
//! A form theorem is credited only by a committed certificate that the
//! independent checker replays in this process
//! ([`crate::bound_memory_authority`]). The evaluation sweep is never
//! consulted for it: sampling is structurally blind to the free query byte and
//! single-point memory these theorems quantify over (the default 100k sampler
//! accepted 93 of 143 deliberately wrong theorems of this shape, measured
//! 2026-09-15 and again 2026-09-29).
//!
//! # Claim boundary
//!
//! These are INSTRUCTION-semantics obligations. They do not claim that a
//! frame restore reloads what an earlier prologue saved, that SP stays
//! aligned, or that a data load reads initialized memory; those remain frame
//! layout / memory-safety obligations of their own. Registers other than
//! `Rt`, `Rt2` and `Rn` are untouched by the Arm pseudocode and are not
//! modelled. Faults, asynchronous aborts, atomicity and tagged addresses are
//! outside the model.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, SpecialReg};

// ---------------------------------------------------------------------------
// Forms
// ---------------------------------------------------------------------------

/// Direction of the two element transfers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PairTransfer {
    /// `STP`: store both registers.
    Store,
    /// `LDP`: load both registers.
    Load,
}

/// Arm pair addressing mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PairAddressing {
    /// `[Xn|SP, #off]`: access at `base + off`, no writeback.
    SignedOffset,
    /// `[Xn|SP, #off]!`: access at `base + off`, then `Xn = base + off`.
    PreIndex,
    /// `[Xn|SP], #off`: access at `base`, then `Xn = base + off`.
    PostIndex,
}

/// Register bank of both transfers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PairRegisterBank {
    /// W/X/ZR transfers into 64-bit general-purpose registers.
    Gpr,
    /// S/D/Q transfers into 128-bit SIMD&FP registers.
    Fpr,
}

/// One concrete architectural pair form. Only the 21 forms in
/// [`PAIR_MEMORY_FORMS`] carry a theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PairMemoryForm {
    /// Store or load.
    pub transfer: PairTransfer,
    /// Addressing mode.
    pub addressing: PairAddressing,
    /// Register bank.
    pub bank: PairRegisterBank,
    /// Element width in bytes (`dbytes`): 4 or 8 for GPR, 4, 8 or 16 for FPR.
    pub element_bytes: u32,
}

const fn form(
    transfer: PairTransfer,
    addressing: PairAddressing,
    bank: PairRegisterBank,
    element_bytes: u32,
) -> PairMemoryForm {
    PairMemoryForm {
        transfer,
        addressing,
        bank,
        element_bytes,
    }
}

use PairAddressing::{PostIndex as POST, PreIndex as PRE, SignedOffset as OFF};
use PairRegisterBank::{Fpr as FPR, Gpr as GPR};
use PairTransfer::{Load as LDP, Store as STP};

/// Every pair form reachable from the six pair opcodes, with its unique,
/// lowercase form query: STP signed-offset and pre-index, LDP
/// signed-offset and post-index in all five banks/widths, plus the Q-only STP
/// post-index alias (the Q-only LDP post-index alias shares the canonical
/// `ldp.post.fpr.w16` form). Each query is a substring of exactly one form
/// theorem name (see [`PairMemoryForm::proof_name`]); the trailing `]` keeps
/// `w4]` distinct from any longer tag. Architecturally legal but never emitted
/// forms (GPR/S/D STP post-index, any LDP pre-index) are deliberately absent:
/// no instruction can bind them, so they carry no theorem.
pub const PAIR_MEMORY_FORMS: [(PairMemoryForm, &str); 21] = [
    (form(STP, OFF, GPR, 4), "pairmem[stp.offset.gpr.w4]"),
    (form(STP, OFF, GPR, 8), "pairmem[stp.offset.gpr.w8]"),
    (form(STP, OFF, FPR, 4), "pairmem[stp.offset.fpr.w4]"),
    (form(STP, OFF, FPR, 8), "pairmem[stp.offset.fpr.w8]"),
    (form(STP, OFF, FPR, 16), "pairmem[stp.offset.fpr.w16]"),
    (form(STP, PRE, GPR, 4), "pairmem[stp.pre.gpr.w4]"),
    (form(STP, PRE, GPR, 8), "pairmem[stp.pre.gpr.w8]"),
    (form(STP, PRE, FPR, 4), "pairmem[stp.pre.fpr.w4]"),
    (form(STP, PRE, FPR, 8), "pairmem[stp.pre.fpr.w8]"),
    (form(STP, PRE, FPR, 16), "pairmem[stp.pre.fpr.w16]"),
    (form(STP, POST, FPR, 16), "pairmem[stp.post.fpr.w16]"),
    (form(LDP, OFF, GPR, 4), "pairmem[ldp.offset.gpr.w4]"),
    (form(LDP, OFF, GPR, 8), "pairmem[ldp.offset.gpr.w8]"),
    (form(LDP, OFF, FPR, 4), "pairmem[ldp.offset.fpr.w4]"),
    (form(LDP, OFF, FPR, 8), "pairmem[ldp.offset.fpr.w8]"),
    (form(LDP, OFF, FPR, 16), "pairmem[ldp.offset.fpr.w16]"),
    (form(LDP, POST, GPR, 4), "pairmem[ldp.post.gpr.w4]"),
    (form(LDP, POST, GPR, 8), "pairmem[ldp.post.gpr.w8]"),
    (form(LDP, POST, FPR, 4), "pairmem[ldp.post.fpr.w4]"),
    (form(LDP, POST, FPR, 8), "pairmem[ldp.post.fpr.w8]"),
    (form(LDP, POST, FPR, 16), "pairmem[ldp.post.fpr.w16]"),
];

impl PairMemoryForm {
    /// The unique form query for this form, or `None` for an illegal
    /// (bank, width) combination.
    pub fn query(&self) -> Option<&'static str> {
        PAIR_MEMORY_FORMS
            .iter()
            .find(|(candidate, _)| candidate == self)
            .map(|(_, query)| *query)
    }

    /// Bytes of the destination/source register (`X` = 8, `V` = 16).
    pub fn register_bytes(&self) -> u32 {
        match self.bank {
            PairRegisterBank::Gpr => 8,
            PairRegisterBank::Fpr => 16,
        }
    }

    fn scale_log2(&self) -> u32 {
        match self.element_bytes {
            4 => 2,
            8 => 3,
            16 => 4,
            other => panic!("illegal pair element width {other}"),
        }
    }

    fn register_letter(&self) -> &'static str {
        match (self.bank, self.element_bytes) {
            (PairRegisterBank::Gpr, 4) => "W",
            (PairRegisterBank::Gpr, 8) => "X",
            (PairRegisterBank::Fpr, 4) => "S",
            (PairRegisterBank::Fpr, 8) => "D",
            (PairRegisterBank::Fpr, 16) => "Q",
            _ => "?",
        }
    }

    /// Form theorem name. Its lowercase form contains [`Self::query`].
    pub fn proof_name(&self) -> String {
        let query = self.query().expect("proof_name requires a legal pair form");
        // Recover the original bracket spelling from the lowercase query.
        let tag = &query["pairmem".len()..];
        let r = self.register_letter();
        let w = self.element_bytes;
        let (mnemonic, scalar) = match self.transfer {
            PairTransfer::Store => ("STP", "STR"),
            PairTransfer::Load => ("LDP", "LDR"),
        };
        let (address, access, base) = match self.addressing {
            PairAddressing::SignedOffset => ("[Xn|SP, #off]", "S=Xn+off", "Xn unchanged"),
            PairAddressing::PreIndex => ("[Xn|SP, #off]!", "S=Xn+off", "Xn'=Xn+off"),
            PairAddressing::PostIndex => ("[Xn|SP], #off", "S=Xn", "Xn'=Xn+off"),
        };
        let effect = match self.transfer {
            PairTransfer::Store => "every other byte unchanged",
            PairTransfer::Load => "destinations zero-extended",
        };
        format!(
            "PairMem{tag}: {mnemonic} {r}t, {r}t2, {address} == {scalar} {r}t,[{access}]; \
             {scalar} {r}t2,[S+{w}]; {base}; {effect} (imm7 decode, operand-bound)"
        )
    }
}

/// The form for an `(opcode, bank, element width)` triple, or `None` when the
/// opcode is not a pair opcode or the combination is illegal for it.
pub fn pair_form_for(
    opcode: AArch64Opcode,
    bank: PairRegisterBank,
    element_bytes: u32,
) -> Option<PairMemoryForm> {
    let (transfer, addressing, q_only) = pair_opcode_shape(opcode)?;
    if q_only && (bank != PairRegisterBank::Fpr || element_bytes != 16) {
        return None;
    }
    let candidate = form(transfer, addressing, bank, element_bytes);
    candidate.query().map(|_| candidate)
}

fn pair_opcode_shape(opcode: AArch64Opcode) -> Option<(PairTransfer, PairAddressing, bool)> {
    use AArch64Opcode as O;
    Some(match opcode {
        O::StpRI => (STP, OFF, false),
        O::LdpRI => (LDP, OFF, false),
        O::StpPreIndex => (STP, PRE, false),
        O::LdpPostIndex => (LDP, POST, false),
        O::NeonStpQPost => (STP, POST, true),
        O::NeonLdpQPost => (LDP, POST, true),
        _ => return None,
    })
}

/// True for the six opcodes that encode Arm LoadStorePair.
pub fn is_pair_memory_opcode(opcode: AArch64Opcode) -> bool {
    pair_opcode_shape(opcode).is_some()
}

// ---------------------------------------------------------------------------
// Obligation construction
// ---------------------------------------------------------------------------

/// A deliberate defect injected into the MACHINE side only. Used by the
/// refutation controls; production obligations use [`PairMachineMutation::None`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PairMachineMutation {
    /// The faithful machine semantics.
    None,
    /// `Rt` and `Rt2` exchanged (both transfers).
    SwapTransfers,
    /// Pre/signed-offset access at the unindexed base, or post-index access at
    /// the indexed address.
    WrongAddressingMode,
    /// Decoder shifts `SignExtend(imm7)` by `scale + 1`.
    WrongScale,
    /// Access address displaced by one element (`off + dbytes`).
    OffsetPlusElement,
    /// Writeback dropped (pre/post) or invented (signed offset).
    WritebackFlipped,
    /// LDP writes the element into the register without clearing the bytes
    /// above the element width (only applicable when element < register).
    NoZeroExtend,
    /// STP writes `dbytes + 1` bytes of the first element.
    ExtraStoredByte,
    /// Elements transferred big-endian.
    BigEndian,
}

impl PairMachineMutation {
    /// Every defect the refutation controls exercise.
    pub const DEFECTS: [PairMachineMutation; 8] = [
        PairMachineMutation::SwapTransfers,
        PairMachineMutation::WrongAddressingMode,
        PairMachineMutation::WrongScale,
        PairMachineMutation::OffsetPlusElement,
        PairMachineMutation::WritebackFlipped,
        PairMachineMutation::NoZeroExtend,
        PairMachineMutation::ExtraStoredByte,
        PairMachineMutation::BigEndian,
    ];

    fn applies_to(self, form: &PairMemoryForm) -> bool {
        match self {
            PairMachineMutation::NoZeroExtend => {
                form.transfer == PairTransfer::Load && form.element_bytes < form.register_bytes()
            }
            PairMachineMutation::ExtraStoredByte => form.transfer == PairTransfer::Store,
            _ => true,
        }
    }
}

fn c64(value: u64) -> SmtExpr {
    SmtExpr::bv_const(value, 64)
}

/// A register value as 64-bit limbs (`hi` only for 128-bit SIMD&FP stores).
#[derive(Clone)]
struct RegisterLimbs {
    lo: SmtExpr,
    hi: Option<SmtExpr>,
}

/// Machine byte extraction: `(v >> (k * 8))<7:0>` over limbs.
fn machine_register_byte(value: &RegisterLimbs, k: SmtExpr) -> SmtExpr {
    let lo = value
        .lo
        .clone()
        .bvlshr(k.clone().bvshl(c64(3)))
        .extract(7, 0);
    match &value.hi {
        None => lo,
        Some(hi) => SmtExpr::ite(
            k.clone().bvult(c64(8)),
            lo,
            hi.clone()
                .bvlshr(k.bvsub(c64(8)).bvshl(c64(3)))
                .extract(7, 0),
        ),
    }
}

/// Intent byte extraction: a constant-index table of fixed `extract`s.
fn intent_register_byte(value: &RegisterLimbs, k: SmtExpr, element_bytes: u32) -> SmtExpr {
    let mut table = SmtExpr::bv_const(0, 8);
    for index in (0..element_bytes).rev() {
        let limb = if index < 8 {
            value.lo.clone()
        } else {
            value
                .hi
                .clone()
                .expect("16-byte element requires a high limb")
        };
        let bit = (index % 8) * 8;
        table = SmtExpr::ite(
            k.clone().eq_expr(c64(u64::from(index))),
            limb.extract(bit + 7, bit),
            table,
        );
    }
    table
}

/// Machine and intent addresses and base post-states.
struct Addresses {
    machine_access: SmtExpr,
    machine_base_after: SmtExpr,
    intent_access: SmtExpr,
    intent_base_after: SmtExpr,
}

fn addresses(
    form: &PairMemoryForm,
    base: &SmtExpr,
    off: &SmtExpr,
    mutation: PairMachineMutation,
) -> Addresses {
    let scale = form.scale_log2();
    // Encoder field: imm7 = (off / dbytes)<6:0>. `off` is built as
    // `SignExtend(k) * dbytes`, so it is aligned by construction and the
    // encoder's truncating division equals this arithmetic shift.
    let imm7 = off.clone().bvashr(c64(u64::from(scale))).extract(6, 0);
    let decode_shift = if mutation == PairMachineMutation::WrongScale {
        scale + 1
    } else {
        scale
    };
    // Decoder: offset = SignExtend(imm7, 64) << scale.
    let decoded_offset = imm7.sign_ext(57).bvshl(c64(u64::from(decode_shift)));
    let indexed = base.clone().bvadd(decoded_offset);
    // Arm: address = postindex ? X[n] : X[n] + offset. The defect swaps the
    // two choices.
    let access_at_base =
        (form.addressing == POST) != (mutation == PairMachineMutation::WrongAddressingMode);
    let mut machine_access = if access_at_base {
        base.clone()
    } else {
        indexed.clone()
    };
    if mutation == PairMachineMutation::OffsetPlusElement {
        machine_access = machine_access.bvadd(c64(u64::from(form.element_bytes)));
    }
    let wback = form.addressing != OFF;
    let wback = if mutation == PairMachineMutation::WritebackFlipped {
        !wback
    } else {
        wback
    };
    let machine_base_after = if wback { indexed } else { base.clone() };

    // Intent: the literal byte offset, never the imm7 round trip.
    let intent_indexed = base.clone().bvadd(off.clone());
    let intent_access = if form.addressing == POST {
        base.clone()
    } else {
        intent_indexed.clone()
    };
    let intent_base_after = if form.addressing == OFF {
        base.clone()
    } else {
        intent_indexed
    };
    Addresses {
        machine_access,
        machine_base_after,
        intent_access,
        intent_base_after,
    }
}

fn store_limbs(name: &str, form: &PairMemoryForm) -> (RegisterLimbs, Vec<(String, u32)>) {
    let lo_name = format!("{name}_lo");
    let mut inputs = vec![(lo_name.clone(), 64)];
    let hi = (form.element_bytes > 8).then(|| {
        let hi_name = format!("{name}_hi");
        inputs.push((hi_name.clone(), 64));
        SmtExpr::var(hi_name, 64)
    });
    (
        RegisterLimbs {
            lo: SmtExpr::var(lo_name, 64),
            hi,
        },
        inputs,
    )
}

/// Build the obligation for `form` with the given machine-side `mutation`.
/// Returns `None` for an illegal form or a mutation that does not apply.
pub fn proof_pair_memory_form_with_mutation(
    form: &PairMemoryForm,
    mutation: PairMachineMutation,
) -> Option<ProofObligation> {
    form.query()?;
    if mutation != PairMachineMutation::None && !mutation.applies_to(form) {
        return None;
    }
    let w = form.element_bytes;
    let w64 = c64(u64::from(w));
    let base = SmtExpr::var("pair_base", 64);
    // The admitted byte offsets are exactly `k * dbytes` for a signed 7-bit
    // `k` (aligned, -64*dbytes ..= 63*dbytes). Quantifying over `k` covers
    // precisely that set with no range/alignment preconditions, so the solver
    // never has to rediscover the admission arithmetic. The intent side still
    // uses the literal byte offset; the machine side still re-derives the
    // encoder's `imm7 = (off / dbytes)<6:0>` from that byte offset.
    let scaled = SmtExpr::var("pair_imm7", 7);
    let off = scaled.sign_ext(57).bvmul(w64.clone());
    let sel = SmtExpr::var("pair_sel", 8);
    let mut inputs = vec![
        ("pair_base".to_string(), 64),
        ("pair_imm7".to_string(), 7),
        ("pair_sel".to_string(), 8),
    ];
    let mut preconditions = Vec::new();
    let addr = addresses(form, &base, &off, mutation);
    let sel_is = |value: u64| sel.clone().eq_expr(SmtExpr::bv_const(value, 8));

    let (intent, machine) = match form.transfer {
        PairTransfer::Store => {
            let (rt, rt_inputs) = store_limbs("pair_rt", form);
            let (rt2, rt2_inputs) = store_limbs("pair_rt2", form);
            inputs.extend(rt_inputs);
            inputs.extend(rt2_inputs);
            let q = SmtExpr::var("pair_q", 64);
            let m = SmtExpr::var("pair_m", 8);
            inputs.push(("pair_q".to_string(), 64));
            inputs.push(("pair_m".to_string(), 8));

            // Machine: one 2*dbytes write at the decoded access address.
            let rel = q.clone().bvsub(addr.machine_access.clone());
            let first_len = if mutation == PairMachineMutation::ExtraStoredByte {
                c64(u64::from(w) + 1)
            } else {
                w64.clone()
            };
            let in_first = rel.clone().bvult(first_len);
            let rel2 = rel.clone().bvsub(w64.clone());
            let in_second = rel2.clone().bvult(w64.clone());
            let (first, second) = if mutation == PairMachineMutation::SwapTransfers {
                (&rt2, &rt)
            } else {
                (&rt, &rt2)
            };
            let order = |k: SmtExpr| {
                if mutation == PairMachineMutation::BigEndian {
                    c64(u64::from(w) - 1).bvsub(k)
                } else {
                    k
                }
            };
            let machine_byte = SmtExpr::ite(
                in_first,
                machine_register_byte(first, order(rel)),
                SmtExpr::ite(
                    in_second,
                    machine_register_byte(second, order(rel2)),
                    m.clone(),
                ),
            );

            // Intent: STR Rt,[S]; then STR Rt2,[S+dbytes] (outermost store last).
            let slot1 = addr.intent_access.clone();
            let slot2 = addr.intent_access.clone().bvadd(w64.clone());
            let d1 = q.clone().bvsub(slot1);
            let after_first = SmtExpr::ite(
                d1.clone().bvult(w64.clone()),
                intent_register_byte(&rt, d1, w),
                m,
            );
            let d2 = q.bvsub(slot2);
            let intent_byte = SmtExpr::ite(
                d2.clone().bvult(w64.clone()),
                intent_register_byte(&rt2, d2, w),
                after_first,
            );

            (
                SmtExpr::ite(sel_is(0), intent_byte.zero_ext(56), addr.intent_base_after),
                SmtExpr::ite(
                    sel_is(0),
                    machine_byte.zero_ext(56),
                    addr.machine_base_after,
                ),
            )
        }
        PairTransfer::Load => {
            let p = SmtExpr::var("pair_p", 64);
            let c = SmtExpr::var("pair_c", 8);
            let d = SmtExpr::var("pair_d", 8);
            let j = SmtExpr::var("pair_j", 8);
            inputs.push(("pair_p".to_string(), 64));
            inputs.push(("pair_c".to_string(), 8));
            inputs.push(("pair_d".to_string(), 8));
            inputs.push(("pair_j".to_string(), 8));
            preconditions.push(
                j.clone()
                    .bvult(SmtExpr::bv_const(u64::from(form.register_bytes()), 8)),
            );
            let memory =
                |address: SmtExpr| SmtExpr::ite(address.eq_expr(p.clone()), c.clone(), d.clone());
            let jz = j.clone().zero_ext(56);

            // Machine: data = Mem[address, dbytes]; data2 = Mem[address+dbytes,
            // dbytes]; register byte j = ZeroExtend(data)<8j+7:8j>.
            let (slot1, slot2) = if mutation == PairMachineMutation::SwapTransfers {
                (
                    addr.machine_access.clone().bvadd(w64.clone()),
                    addr.machine_access.clone(),
                )
            } else {
                (
                    addr.machine_access.clone(),
                    addr.machine_access.clone().bvadd(w64.clone()),
                )
            };
            let index = if mutation == PairMachineMutation::BigEndian {
                c64(u64::from(w) - 1).bvsub(jz.clone())
            } else {
                jz.clone()
            };
            let in_element = j.bvult(SmtExpr::bv_const(u64::from(w), 8));
            let machine_register = |slot: SmtExpr| {
                let read = memory(slot.bvadd(index.clone()));
                if mutation == PairMachineMutation::NoZeroExtend {
                    read
                } else {
                    SmtExpr::ite(in_element.clone(), read, SmtExpr::bv_const(0, 8))
                }
            };
            let machine_r1 = machine_register(slot1);
            let machine_r2 = machine_register(slot2);

            // Intent: LDR Rt,[S] and LDR Rt2,[S+dbytes] as little-endian
            // assembled scalars, zero-extended to the register, then byte j.
            let assemble = |start: SmtExpr, from: u32, count: u32| {
                let mut value = memory(start.clone().bvadd(c64(u64::from(from))));
                for k in 1..count {
                    let byte = memory(start.clone().bvadd(c64(u64::from(from + k))));
                    value = byte.concat(value);
                }
                value
            };
            let intent_register = |slot: SmtExpr| {
                let lo_bytes = w.min(8);
                let lo = assemble(slot.clone(), 0, lo_bytes);
                let lo = if lo_bytes < 8 {
                    lo.zero_ext((8 - lo_bytes) * 8)
                } else {
                    lo
                };
                let lo_byte = lo.bvlshr(jz.clone().bvshl(c64(3))).extract(7, 0);
                if form.register_bytes() == 8 {
                    return lo_byte;
                }
                let hi = if w == 16 {
                    assemble(slot, 8, 8)
                } else {
                    c64(0)
                };
                SmtExpr::ite(
                    jz.clone().bvult(c64(8)),
                    lo_byte,
                    hi.bvlshr(jz.clone().bvsub(c64(8)).bvshl(c64(3)))
                        .extract(7, 0),
                )
            };
            let intent_r1 = intent_register(addr.intent_access.clone());
            let intent_r2 = intent_register(addr.intent_access.clone().bvadd(w64.clone()));

            (
                SmtExpr::ite(
                    sel_is(0),
                    intent_r1.zero_ext(56),
                    SmtExpr::ite(sel_is(1), intent_r2.zero_ext(56), addr.intent_base_after),
                ),
                SmtExpr::ite(
                    sel_is(0),
                    machine_r1.zero_ext(56),
                    SmtExpr::ite(sel_is(1), machine_r2.zero_ext(56), addr.machine_base_after),
                ),
            )
        }
    };

    let name = if mutation == PairMachineMutation::None {
        form.proof_name()
    } else {
        format!("{} [refutation control: {mutation:?}]", form.proof_name())
    };
    Some(ProofObligation {
        name,
        trust_ir_expr: intent,
        aarch64_expr: machine,
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    })
}

/// The faithful obligation for `form` (`None` for an illegal form).
pub fn proof_pair_memory_form(form: &PairMemoryForm) -> Option<ProofObligation> {
    proof_pair_memory_form_with_mutation(form, PairMachineMutation::None)
}

/// All 21 faithful pair-memory form obligations, in [`PAIR_MEMORY_FORMS`] order.
pub fn all_pair_memory_form_proofs() -> Vec<ProofObligation> {
    PAIR_MEMORY_FORMS
        .iter()
        .map(|(form, _)| proof_pair_memory_form(form).expect("table forms are legal"))
        .collect()
}

// ---------------------------------------------------------------------------
// Instruction binding
// ---------------------------------------------------------------------------

/// A concrete pair instruction bound to exactly one form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PairMemoryBinding {
    /// The architectural form whose theorem this instruction instantiates.
    pub form: PairMemoryForm,
    /// `Rt` register field (31 is ZR for GPR, a real register for FPR).
    pub rt_field: u32,
    /// `Rt2` register field.
    pub rt2_field: u32,
    /// `Rn` field (31 is SP).
    pub base_field: u32,
    /// Literal byte offset (zero for the three-operand spelling).
    pub offset: i64,
}

impl PairMemoryBinding {
    /// The unique form query for the bound form.
    pub fn query(&self) -> &'static str {
        self.form
            .query()
            .expect("a binding only ever carries a legal form")
    }
}

/// Transfer operand identity: (bank, element bytes, field). Physical
/// registers only; SP/WSP are never transfers; FP field 31 is a real register.
fn transfer_identity(operand: &MachOperand) -> Option<(PairRegisterBank, u32, u32)> {
    match operand {
        MachOperand::PReg(reg) => match reg.encoding() {
            e @ 0..=30 => Some((GPR, 8, u32::from(e))),
            e @ 32..=62 => Some((GPR, 4, u32::from(e - 32))),
            e @ 64..=95 => Some((FPR, 16, u32::from(e - 64))),
            e @ 96..=127 => Some((FPR, 8, u32::from(e - 96))),
            e @ 128..=159 => Some((FPR, 4, u32::from(e - 128))),
            160 => Some((GPR, 8, 31)),
            161 => Some((GPR, 4, 31)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((GPR, 8, 31)),
        MachOperand::Special(SpecialReg::WZR) => Some((GPR, 4, 31)),
        _ => None,
    }
}

/// Bind a concrete emitted pair instruction to its form, or explain the
/// refusal. The admission rules are reimplemented here independently of the
/// encoder; see the module documentation for the claim boundary.
pub fn bind_pair_memory_instruction(inst: &MachInst) -> Result<PairMemoryBinding, String> {
    let Some((transfer, addressing, q_only)) = pair_opcode_shape(inst.opcode) else {
        return Err(format!("{:?} is not a pair-memory opcode", inst.opcode));
    };
    let (t, t2, base, offset) = match inst.operands.as_slice() {
        [t, t2, base] => (t, t2, base, 0),
        [t, t2, base, MachOperand::Imm(offset)] => (t, t2, base, *offset),
        _ => {
            return Err(
                "pair memory requires exactly [Rt, Rt2, Xn|SP] or [Rt, Rt2, Xn|SP, #imm]".into(),
            );
        }
    };
    let (Some((bank, element_bytes, rt_field)), Some((bank2, element_bytes2, rt2_field))) =
        (transfer_identity(t), transfer_identity(t2))
    else {
        return Err(
            "pair transfers must be physical W/X/ZR or S/D/Q registers (never SP/WSP or unresolved)"
                .into(),
        );
    };
    if (bank, element_bytes) != (bank2, element_bytes2) {
        return Err("pair transfers must share one register bank and width".into());
    }
    if q_only && (bank != FPR || element_bytes != 16) {
        return Err("NEON Q-pair alias requires two Q registers".into());
    }
    let base_field = match base {
        MachOperand::PReg(reg) if reg.encoding() <= 31 => u32::from(reg.encoding()),
        MachOperand::Special(SpecialReg::SP) => 31,
        _ => return Err("pair base must be a canonical X register or SP".into()),
    };
    let scale = i64::from(element_bytes);
    if offset % scale != 0 || !(-64..=63).contains(&(offset / scale)) {
        return Err(format!(
            "pair offset {offset} must be a multiple of {scale} within signed scaled imm7"
        ));
    }
    if transfer == LDP && rt_field == rt2_field {
        return Err("pair load destinations must be distinct (duplicate is unpredictable)".into());
    }
    let gpr_base_alias =
        bank == GPR && base_field != 31 && (rt_field == base_field || rt2_field == base_field);
    if gpr_base_alias && addressing != OFF {
        return Err("GPR pair writeback base overlaps a transfer (unpredictable)".into());
    }
    if gpr_base_alias && transfer == LDP {
        return Err(
            "signed-offset GPR pair load overwrites its own base; the bound register model keeps \
             the base value, so this instruction is refused rather than mis-modelled"
                .into(),
        );
    }
    let form = form(transfer, addressing, bank, element_bytes);
    if form.query().is_none() {
        return Err(format!("no legal pair form for {form:?}"));
    }
    Ok(PairMemoryBinding {
        form,
        rt_field,
        rt2_field,
        base_field,
        offset,
    })
}

/// Bind a pair row for CREDIT: [`bind_pair_memory_instruction`] must bind it
/// AND the per-instruction lane
/// ([`crate::aarch64_pair_memory_proofs::pair_memory_intent`]) must admit it,
/// with every field agreeing (direction, addressing mode, bank, element width,
/// byte offset and the `Rt`/`Rt2`/`Rn` fields). The two admissions are written
/// independently; a disagreement is refused, never resolved in either's
/// favour.
pub fn bind_admitted_pair_instruction(inst: &MachInst) -> Result<PairMemoryBinding, String> {
    let binding = bind_pair_memory_instruction(inst)?;
    let Some(intent) = crate::aarch64_pair_memory_proofs::pair_memory_intent(inst) else {
        return Err(
            "the per-instruction pair lane does not admit this instruction (virtual operand or \
             discarded load destination)"
                .into(),
        );
    };
    use crate::aarch64_pair_memory_proofs::PairMode;
    let mode_agrees = matches!(
        (binding.form.addressing, intent.mode),
        (OFF, PairMode::Offset) | (PRE, PairMode::PreIndex) | (POST, PairMode::PostIndex)
    );
    let agrees = mode_agrees
        && intent.load == (binding.form.transfer == LDP)
        && intent.simd == (binding.form.bank == FPR)
        && intent.element_bytes == binding.form.element_bytes
        && intent.offset == binding.offset
        && u32::from(intent.rt) == binding.rt_field
        && u32::from(intent.rt2) == binding.rt2_field
        && u32::from(intent.rn) == binding.base_field;
    if !agrees {
        return Err(format!(
            "the form binder ({binding:?}) and the per-instruction lane ({intent:?}) disagree"
        ));
    }
    Ok(binding)
}

/// The binding a load/store-pair WORD denotes, decoded from its bits (Arm DDI
/// 0487 C4.1: `opc | 101 | V | 0 | mode | L | imm7 | Rt2 | Rn | Rt`), or
/// `None` when the word is not an instance of a pair form that carries a
/// theorem.
///
/// Stricter than [`crate::aarch64_pair_memory_proofs::decode_pair_memory_word`]:
/// bit 25 must be zero (with it set the word is not in the load/store-pair
/// class) and the decoded form must be one of [`PAIR_MEMORY_FORMS`]. The
/// Formal-only bound-memory rule ([`crate::bound_memory_authority`]) requires
/// this to equal, field for field, the binding of the instruction whose
/// concrete-word obligation judged the word: the certificate proves the form
/// of the word the row's refutation check held on, not a form chosen from the
/// operands alone.
pub fn decode_pair_memory_binding(word: u32) -> Option<PairMemoryBinding> {
    use crate::aarch64_pair_memory_proofs::PairMode;
    if (word >> 25) & 1 != 0 {
        return None;
    }
    let decoded = crate::aarch64_pair_memory_proofs::decode_pair_memory_word(word)?;
    let addressing = match decoded.mode {
        PairMode::Offset => OFF,
        PairMode::PreIndex => PRE,
        PairMode::PostIndex => POST,
    };
    let bound = form(
        if decoded.load { LDP } else { STP },
        addressing,
        if decoded.simd { FPR } else { GPR },
        decoded.element_bytes,
    );
    bound.query()?;
    Some(PairMemoryBinding {
        form: bound,
        rt_field: u32::from(decoded.rt),
        rt2_field: u32::from(decoded.rt2),
        base_field: u32::from(decoded.rn),
        offset: decoded.offset,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// In-process refutation search
// ---------------------------------------------------------------------------

fn grid_eval(expr: &SmtExpr, env: &crate::smt::EvalEnv) -> crate::smt::EvalResult {
    expr.try_eval(env).expect("pair obligation must evaluate")
}

fn grid_preconditions_hold(ob: &ProofObligation, env: &crate::smt::EvalEnv) -> bool {
    ob.preconditions.iter().all(|p| grid_eval(p, env).as_bool())
}

/// Deterministic structured grid around both the intent and the machine
/// access addresses: every slot byte, both neighbours, extreme offsets and
/// a wrapping base. Returns the first disagreeing point.
///
/// `None` is NOT evidence that a form theorem holds (only a replayed
/// certificate is): it is the in-process refutation search the machine
/// defects ([`PairMachineMutation::DEFECTS`]) must not survive.
pub fn grid_counterexample(ob: &ProofObligation, form: &PairMemoryForm) -> Option<String> {
    let w = i64::from(form.element_bytes);
    let bases = [0x0000_7fff_f000_1000u64, 0, u64::MAX - 5];
    let offsets = [-64 * w, -3 * w, -w, 0, w, 2 * w, 63 * w];
    let window = |start: u64| -> Vec<u64> {
        (-(3 * w)..(5 * w))
            .map(|delta| start.wrapping_add(delta as u64))
            .collect()
    };
    for &base in &bases {
        for &off in &offsets {
            let mut probes = window(base.wrapping_add(off as u64));
            probes.extend(window(base));
            probes.extend(window(base.wrapping_add((2 * off) as u64)));
            for &probe in &probes {
                let sels: &[u64] = match form.transfer {
                    PairTransfer::Store => &[0, 1],
                    PairTransfer::Load => &[0, 1, 2],
                };
                for &sel in sels {
                    let js: Vec<u64> = match form.transfer {
                        PairTransfer::Store => vec![0],
                        PairTransfer::Load => (0..u64::from(form.register_bytes())).collect(),
                    };
                    for j in js {
                        let mut env = crate::smt::EvalEnv::default();
                        env.insert("pair_base".into(), base);
                        env.insert("pair_imm7".into(), ((off / w) as u64) & 0x7f);
                        env.insert("pair_sel".into(), sel);
                        env.insert("pair_rt_lo".into(), 0x0807_0605_0403_0201);
                        env.insert("pair_rt_hi".into(), 0x100f_0e0d_0c0b_0a09);
                        env.insert("pair_rt2_lo".into(), 0x2827_2625_2423_2221);
                        env.insert("pair_rt2_hi".into(), 0x302f_2e2d_2c2b_2a29);
                        env.insert("pair_q".into(), probe);
                        env.insert("pair_m".into(), 0xaa);
                        env.insert("pair_p".into(), probe);
                        env.insert("pair_c".into(), 0x5a);
                        env.insert("pair_d".into(), 0xc3);
                        env.insert("pair_j".into(), j);
                        if !grid_preconditions_hold(ob, &env) {
                            continue;
                        }
                        let intent = grid_eval(&ob.trust_ir_expr, &env);
                        let machine = grid_eval(&ob.aarch64_expr, &env);
                        if intent != machine {
                            return Some(format!(
                                "base={base:#x} off={off} probe={probe:#x} sel={sel} j={j}: \
                                 intent={intent:?} machine={machine:?}"
                            ));
                        }
                    }
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::PReg;
    use trust_cg_ir::aarch64_regs::{
        D8, D9, SP, V1, V2, W1, W2, WSP, X0, X1, X2, X19, X20, X29, X30, XZR,
    };

    #[test]
    fn twenty_one_forms_have_unique_queries_names_and_are_non_degenerate() {
        let proofs = all_pair_memory_form_proofs();
        assert_eq!(proofs.len(), 21);
        let mut names = std::collections::BTreeSet::new();
        for ((form, query), proof) in PAIR_MEMORY_FORMS.iter().zip(&proofs) {
            assert!(!proof.is_degenerate(), "{} is X==X", proof.name);
            assert!(names.insert(proof.name.clone()), "duplicate {}", proof.name);
            assert_eq!(*query, query.to_lowercase());
            let matching = proofs
                .iter()
                .filter(|other| other.name.to_lowercase().contains(query))
                .count();
            assert_eq!(matching, 1, "{query} must select exactly one form theorem");
            assert_eq!(form.query(), Some(*query));
        }
    }

    #[test]
    fn every_faithful_form_agrees_on_the_structured_grid() {
        for (form, _) in PAIR_MEMORY_FORMS {
            let ob = proof_pair_memory_form(&form).unwrap();
            assert_eq!(grid_counterexample(&ob, &form), None, "{}", ob.name);
        }
    }

    #[test]
    fn every_applicable_machine_defect_is_refuted_on_the_grid() {
        let mut applied = 0;
        for (form, _) in PAIR_MEMORY_FORMS {
            for mutation in PairMachineMutation::DEFECTS {
                let Some(ob) = proof_pair_memory_form_with_mutation(&form, mutation) else {
                    assert!(
                        !mutation.applies_to(&form),
                        "{form:?} {mutation:?} must build"
                    );
                    continue;
                };
                applied += 1;
                assert!(
                    grid_counterexample(&ob, &form).is_some(),
                    "{form:?}: defect {mutation:?} was NOT refuted"
                );
            }
        }
        // 21 forms x 6 universal defects + 11 STP extra-byte forms + 6 LDP
        // narrow zero-extension forms (W, S and D below their register width).
        assert_eq!(applied, 21 * 6 + 11 + 6);
    }

    /// A live AY run is never AUTHORITY here (only a committed certificate is,
    /// `crate::bound_memory_authority`); this test pins that AY never refutes
    /// a faithful form and does refute representative defects.
    ///
    /// Measured on AY 0.13.0 (2026-09-15): every faithful form solves `unsat`
    /// in ~0.2 s, but its Alethe certificate carried one unproved step. That
    /// incompleteness surfaces as "incomplete AY proof certificate" /
    /// "unusable AY proof evidence" or the resident server's
    /// `:reason-unknown (incomplete self-check-rejected)`. Under heavy shared
    /// solver load a form can also hit the deadline; a `Timeout` is a
    /// scheduling fact, never evidence either way.
    ///
    /// The test therefore demands: no faithful form is ever refuted or errors;
    /// a faithful verdict is `Verified`, an incomplete certificate, or a
    /// timeout; at least one form must actually be decided (so an all-timeout
    /// host cannot pass vacuously); and every representative defect yields a
    /// genuine solver counterexample.
    #[test]
    fn pair_obligations_never_refute_and_defects_refute_with_ay_when_available() {
        if !crate::ay_bridge::ay_available() {
            eprintln!(
                "SKIP (unqualified): AY + independent checker unavailable: {:?}",
                crate::ay_bridge::proof_toolchain_unavailable_reason()
            );
            return;
        }
        let config = crate::ay_bridge::AYConfig::default();
        let mut failures = Vec::new();
        let mut decided = 0usize;
        for (form, _) in PAIR_MEMORY_FORMS {
            let ob = proof_pair_memory_form(&form).unwrap();
            match crate::ay_bridge::verify_with_ay(&ob, &config) {
                crate::ay_bridge::AYResult::Verified => decided += 1,
                crate::ay_bridge::AYResult::Unknown(reason)
                    if reason.contains("incomplete AY proof certificate")
                        || reason.contains("unusable AY proof evidence")
                        || reason.contains("incomplete self-check-rejected") =>
                {
                    decided += 1;
                }
                crate::ay_bridge::AYResult::Timeout => {}
                other => failures.push(format!("{}: {other:?}", ob.name)),
            }
        }
        if decided == 0 {
            failures.push(
                "no faithful pair form was decided by the solver (all timed out); the \
                 non-refutation leg would be vacuous"
                    .to_string(),
            );
        }
        // Three representative defects per direction, formally refuted.
        for (form, defects) in [
            (
                form(STP, PRE, GPR, 8),
                vec![
                    PairMachineMutation::WrongScale,
                    PairMachineMutation::SwapTransfers,
                    PairMachineMutation::WritebackFlipped,
                    PairMachineMutation::OffsetPlusElement,
                ],
            ),
            (
                form(LDP, POST, GPR, 4),
                vec![
                    PairMachineMutation::WrongAddressingMode,
                    PairMachineMutation::NoZeroExtend,
                    PairMachineMutation::SwapTransfers,
                ],
            ),
        ] {
            for mutation in defects {
                let ob = proof_pair_memory_form_with_mutation(&form, mutation).unwrap();
                let result = crate::ay_bridge::verify_with_ay(&ob, &config);
                if !matches!(result, crate::ay_bridge::AYResult::CounterExample(_)) {
                    failures.push(format!(
                        "{}: expected counterexample, got {result:?}",
                        ob.name
                    ));
                }
            }
        }
        assert!(failures.is_empty(), "{failures:#?}");
    }

    /// Measurement aid: `PAIR_MEM_SMT2_DIR=<dir> cargo test -- --ignored
    /// dump_pair_memory_smt2` writes each form's exact AY query.
    #[test]
    #[ignore]
    fn dump_pair_memory_smt2() {
        let Some(dir) = std::env::var_os("PAIR_MEM_SMT2_DIR") else {
            return;
        };
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        let config = crate::ay_bridge::AYConfig::default();
        for (form, query) in PAIR_MEMORY_FORMS {
            let tag = query.trim_start_matches("pairmem[").trim_end_matches(']');
            let ob = proof_pair_memory_form(&form).unwrap();
            std::fs::write(
                dir.join(format!("{tag}.smt2")),
                crate::ay_bridge::generate_smt2_query(&ob, &config),
            )
            .unwrap();
            for mutation in PairMachineMutation::DEFECTS {
                if let Some(ob) = proof_pair_memory_form_with_mutation(&form, mutation) {
                    std::fs::write(
                        dir.join(format!("{tag}.{mutation:?}.smt2")),
                        crate::ay_bridge::generate_smt2_query(&ob, &config),
                    )
                    .unwrap();
                }
            }
        }
    }

    fn pair(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, operands)
    }

    fn p(reg: PReg) -> MachOperand {
        MachOperand::PReg(reg)
    }

    #[test]
    fn frame_prologue_and_epilogue_pairs_bind_to_exact_forms() {
        use AArch64Opcode as O;
        let sp = MachOperand::Special(SpecialReg::SP);
        let cases = [
            // stp x20, x19, [sp, #-32]!
            (
                pair(
                    O::StpPreIndex,
                    vec![p(X20), p(X19), sp.clone(), MachOperand::Imm(-32)],
                ),
                "pairmem[stp.pre.gpr.w8]",
                (20, 19, 31, -32),
            ),
            // stp x29, x30, [sp, #16]
            (
                pair(
                    O::StpRI,
                    vec![p(X29), p(X30), sp.clone(), MachOperand::Imm(16)],
                ),
                "pairmem[stp.offset.gpr.w8]",
                (29, 30, 31, 16),
            ),
            // ldp x29, x30, [sp, #16]
            (
                pair(O::LdpRI, vec![p(X29), p(X30), p(SP), MachOperand::Imm(16)]),
                "pairmem[ldp.offset.gpr.w8]",
                (29, 30, 31, 16),
            ),
            // ldp x20, x19, [sp], #32
            (
                pair(
                    O::LdpPostIndex,
                    vec![p(X20), p(X19), sp.clone(), MachOperand::Imm(32)],
                ),
                "pairmem[ldp.post.gpr.w8]",
                (20, 19, 31, 32),
            ),
            // ldp d8, d9, [x29, #-16]
            (
                pair(O::LdpRI, vec![p(D8), p(D9), p(X29), MachOperand::Imm(-16)]),
                "pairmem[ldp.offset.fpr.w8]",
                (8, 9, 29, -16),
            ),
            // stp w1, w2, [x0]  (three-operand zero offset)
            (
                pair(O::StpRI, vec![p(W1), p(W2), p(X0)]),
                "pairmem[stp.offset.gpr.w4]",
                (1, 2, 0, 0),
            ),
            // stp q1, q2, [sp], #-1024 (Q-only alias, minimum offset)
            (
                pair(
                    O::NeonStpQPost,
                    vec![p(V1), p(V2), sp.clone(), MachOperand::Imm(-1024)],
                ),
                "pairmem[stp.post.fpr.w16]",
                (1, 2, 31, -1024),
            ),
            // stp xzr, x1, [x2, #504] (ZR store, maximum X offset)
            (
                pair(O::StpRI, vec![p(XZR), p(X1), p(X2), MachOperand::Imm(504)]),
                "pairmem[stp.offset.gpr.w8]",
                (31, 1, 2, 504),
            ),
            // stp x1, x1, [x2] (duplicate store source is legal)
            (
                pair(O::StpRI, vec![p(X1), p(X1), p(X2)]),
                "pairmem[stp.offset.gpr.w8]",
                (1, 1, 2, 0),
            ),
            // stp x2, x1, [x2, #8] (non-writeback store of the base value)
            (
                pair(O::StpRI, vec![p(X2), p(X1), p(X2), MachOperand::Imm(8)]),
                "pairmem[stp.offset.gpr.w8]",
                (2, 1, 2, 8),
            ),
        ];
        for (inst, query, (rt, rt2, rn, off)) in cases {
            let binding = bind_pair_memory_instruction(&inst)
                .unwrap_or_else(|why| panic!("{inst:?} must bind: {why}"));
            assert_eq!(binding.query(), query, "{inst:?}");
            assert_eq!(
                (
                    binding.rt_field,
                    binding.rt2_field,
                    binding.base_field,
                    binding.offset
                ),
                (rt, rt2, rn, off),
                "{inst:?}"
            );
            // The bound offset lies in the theorem's quantified offset set
            // `{k * dbytes : k in -64..=63}`.
            let w = i64::from(binding.form.element_bytes);
            assert!(binding.offset % w == 0 && (-64..=63).contains(&(binding.offset / w)));
        }
    }

    #[test]
    fn malformed_aliased_and_unpredictable_pairs_refuse() {
        use AArch64Opcode as O;
        use trust_cg_ir::RegClass;
        use trust_cg_ir::regs::VReg;
        let sp = MachOperand::Special(SpecialReg::SP);
        let imm = MachOperand::Imm;
        let refused = [
            ("operand-less", pair(O::StpPreIndex, vec![])),
            ("one operand", pair(O::StpRI, vec![p(X1)])),
            (
                "five operands",
                pair(O::StpRI, vec![p(X1), p(X2), p(X0), imm(0), imm(0)]),
            ),
            (
                "register offset",
                pair(O::LdpRI, vec![p(X1), p(X2), p(X0), p(X19)]),
            ),
            (
                "SP transfer",
                pair(O::StpRI, vec![p(SP), p(X2), p(X0), imm(0)]),
            ),
            (
                "WSP transfer",
                pair(O::StpRI, vec![p(X1), p(WSP), p(X0), imm(0)]),
            ),
            (
                "unresolved vreg",
                pair(
                    O::StpRI,
                    vec![
                        MachOperand::VReg(VReg::new(7, RegClass::Gpr64)),
                        p(X2),
                        p(X0),
                        imm(0),
                    ],
                ),
            ),
            (
                "mixed width",
                pair(O::StpRI, vec![p(X1), p(W2), p(X0), imm(0)]),
            ),
            (
                "mixed bank",
                pair(O::StpRI, vec![p(X1), p(D9), p(X0), imm(0)]),
            ),
            ("W base", pair(O::StpRI, vec![p(X1), p(X2), p(W1), imm(0)])),
            (
                "XZR base",
                pair(O::StpRI, vec![p(X1), p(X2), p(XZR), imm(0)]),
            ),
            (
                "misaligned",
                pair(O::StpRI, vec![p(X1), p(X2), sp.clone(), imm(4)]),
            ),
            (
                "above imm7",
                pair(O::StpRI, vec![p(X1), p(X2), sp.clone(), imm(512)]),
            ),
            (
                "below imm7",
                pair(O::StpRI, vec![p(W1), p(W2), sp.clone(), imm(-260)]),
            ),
            (
                "non-Q alias",
                pair(O::NeonLdpQPost, vec![p(D8), p(D9), sp.clone(), imm(16)]),
            ),
            (
                "duplicate load",
                pair(O::LdpRI, vec![p(X1), p(X1), sp.clone(), imm(0)]),
            ),
            (
                "duplicate ZR load",
                pair(O::LdpRI, vec![p(XZR), p(XZR), sp.clone(), imm(0)]),
            ),
            (
                "pre writeback alias",
                pair(O::StpPreIndex, vec![p(X0), p(X1), p(X0), imm(-16)]),
            ),
            (
                "post writeback alias",
                pair(O::LdpPostIndex, vec![p(X1), p(X0), p(X0), imm(16)]),
            ),
            (
                "load overwrites base",
                pair(O::LdpRI, vec![p(X0), p(X1), p(X0), imm(16)]),
            ),
            ("not a pair", pair(O::LdrRI, vec![p(X0), p(X1), imm(0)])),
        ];
        for (label, inst) in refused {
            assert!(
                bind_pair_memory_instruction(&inst).is_err(),
                "{label}: {inst:?} must refuse"
            );
        }
        // Boundary controls: the exact imm7 limits bind.
        for (inst, form_query) in [
            (
                pair(O::StpRI, vec![p(X1), p(X2), sp.clone(), imm(-512)]),
                "pairmem[stp.offset.gpr.w8]",
            ),
            (
                pair(O::StpRI, vec![p(W1), p(W2), sp.clone(), imm(252)]),
                "pairmem[stp.offset.gpr.w4]",
            ),
            // FP transfers never alias the GPR base, even with equal numbers.
            (
                pair(O::LdpRI, vec![p(D8), p(D9), p(X29 /* field 29 */), imm(0)]),
                "pairmem[ldp.offset.fpr.w8]",
            ),
        ] {
            assert_eq!(
                bind_pair_memory_instruction(&inst).map(|b| b.query()),
                Ok(form_query)
            );
        }
    }

    #[test]
    fn opcode_form_table_is_exact() {
        use AArch64Opcode as O;
        assert_eq!(pair_form_for(O::NeonLdpQPost, FPR, 8), None);
        assert_eq!(pair_form_for(O::StpRI, GPR, 16), None);
        assert_eq!(pair_form_for(O::LdrRI, GPR, 8), None);
        assert_eq!(
            pair_form_for(O::NeonLdpQPost, FPR, 16).and_then(|f| f.query()),
            Some("pairmem[ldp.post.fpr.w16]")
        );
        for opcode in [
            O::StpRI,
            O::LdpRI,
            O::StpPreIndex,
            O::LdpPostIndex,
            O::NeonLdpQPost,
            O::NeonStpQPost,
        ] {
            assert!(is_pair_memory_opcode(opcode));
        }
    }
}
