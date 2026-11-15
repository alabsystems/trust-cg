// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Reference: Arm DDI 0487 (K.a) C6.2 LDAR/LDARB/LDARH, STLR/STLRB/STLRH,
//            CAS/CASB/CASH, SWP/SWPB/SWPH, LDADD/LDCLR/LDEOR/LDSET/LDSMAX/
//            LDSMIN/LDUMAX/LDUMIN (and their A/AL/L and B/H variants), the
//            `MemAtomic`/`MemAtomicCompareAndSwap` pseudocode, and C4.1.94
//            "Atomic memory operations" / C4.1.66 "Load/store ordered" /
//            "Compare and swap" encoding classes.

//! Operand-bound AArch64 single-instruction atomic FORM theorems
//! (ledger `X-OPCODES-P2`, `L04-P1`).
//!
//! # Why this module exists
//!
//! The 46 LSE and acquire/release atomic opcode rows (`LDAR{,B,H}`,
//! `STLR{,B,H}`, `CAS{,A,AL,L}`, `SWP{,A,AL,L}` and the 32 `LD<op>` forms) had
//! no faithful obligation: the registered atomic theorems
//! ([`crate::atomic_proofs`]) are single-facet (`LDADD_I32: mem[addr] = old +
//! operand` at one width) or were retracted as degenerate (`returns old
//! value`), and `SWP`/min/max carried no mapping. Each such instruction
//! performs ONE read-modify-write of `bytes` bytes at `X[n]`: it returns the
//! old value AND leaves a new value in memory, at the access width the `size`
//! field names, with the ordering its `A`/`R` bits name.
//!
//! This module states the VALUE and MEMORY effect of every emitted width of
//! every such opcode as one FORM theorem per `(operation, width)`: 12
//! operations x 4 widths = 48 forms ([`ATOMIC_MEMORY_FORMS`]). The ordering
//! bits do not change the value semantics, so the four orderings of an
//! operation share its form theorem; the ordering facet is the memory-order
//! table of ledger `L03-P3` ([`crate::aarch64_memory_order`]), which decides
//! from the emitted words that each C11/Rust ordering request is met.
//!
//! # The two sides
//!
//! For ALL base addresses, ALL register values (`X[s]`, `X[t]`), ALL memory
//! contents of the accessed window and ALL other memory:
//!
//! * **Machine side** follows the Arm pseudocode of the form: the address is
//!   `X[n]`; `data = Mem[address, bytes]` is read byte by byte at
//!   `address + k` and assembled little-endian by OR-ing positioned bytes;
//!   `value = X[s]<8*bytes-1:0>` and the `MemAtomic` case analysis computes
//!   `result` at the access width (`data + value`, `data AND NOT value`,
//!   `SInt(data) > SInt(value) ? data : value`, ...); a compare-and-swap writes
//!   `X[t]<..>` only when `data == X[s]<..>`; the store is ONE range write of
//!   `bytes` bytes, observed at a free query address `q` through a
//!   variable-shift byte extraction; the register write is
//!   `ZeroExtend(data, 64)` (a W write clears bits 63:32), observed at a
//!   symbolic byte `j < 8` as `Mem[address + j]` below the access width and
//!   zero above it (the scalar load forms' per-byte reading of a
//!   little-endian load; a whole-register comparison is closed by AY's
//!   rewriter before it bit-blasts, which would leave the certificate without
//!   content).
//! * **Intent side** is the machine-IR operand intent: the old value is
//!   assembled with `concat` from reads at constant offsets (register byte `j`
//!   is the zero-extended old value shifted right by `8 j`), the new value is
//!   computed on 64-bit extended operands (`zext(old) + value`, a signed
//!   maximum as `sext(old) >= sext(value)`, ...) and truncated, and the store
//!   is a chain of `bytes` single-byte stores at constant offsets with
//!   constant-index byte extraction.
//!
//! The two sides share no operation, comparison, byte extraction or store
//! subexpression, so every obligation is structurally non-degenerate, and
//! every applicable [`AtomicMachineMutation`] refutes.
//!
//! # Memory encoding (pure QF_BV, no arrays)
//!
//! The pre-state memory is the chain-of-points function
//! `M(x) = ite(x == base, b0, ite(x == base+1, b1, ... ite(x == base+w-1,
//! b_{w-1}, m)))` over free bytes `b_k` and a free byte `m`. It is complete
//! for the stated equality: the faithful instruction reads only the `w` bytes
//! at `base` and the observation reads the byte at `q`, so for any concrete
//! memory `mu` and query `q` the choice `b_k = mu(base + k)`, `m = mu(q)` makes
//! `M` agree with `mu` on every byte either side of the theorem reads (the `w`
//! window addresses are distinct modulo 2^64 because `w <= 8`). Unlike the
//! single-point memory of the scalar load forms
//! ([`crate::aarch64_scalar_memory_proofs`]) it lets every window byte vary
//! at once, which a read-modify-write needs: the new value's byte `k` depends
//! on every lower byte (carries) or on all of them (comparisons).
//!
//! # Binding and authority
//!
//! [`bind_atomic_instruction`] re-implements the encoder's admission (it
//! shares no code with `trust-cg-codegen`): the opcode fixes the operation and
//! the ordering bits; the width is the opcode's (`LDARB`), the access-size
//! immediate (narrow LSE and CAS), or the result (LSE) / compare (CAS) /
//! transfer (LDAR/STLR) register's class; the base is an X register or SP.
//! It refuses a load-type destination that is the zero register (the
//! `ST<op>` aliases: no value is returned and the acquire is dropped), a
//! zero-register CAS compare/result register (conservatively, as the
//! memory-order table does), mismatched register classes and malformed
//! arities. [`atomic_word`] re-derives the word from the binding with this
//! module's own encoder, and [`decode_atomic_word`] decodes a word back to a
//! binding independently of both. The emitted word is tied to the binding by
//! the enforced independent decode check (ENC-5, `trust-cg-codegen`
//! `decode_check`) through
//! [`crate::aarch64_atomic_effect::check_emitted_atomic_word`].
//!
//! Credit is Formal-only, exactly as for the scalar and pair memory forms
//! ([`crate::bound_memory_authority`]): an atomic row is credited only when its
//! in-process word judgement ([`crate::aarch64_atomic_effect`]) held, the form
//! of that word is the bound form, and the exact query of the form theorem has
//! a committed certificate (`verdict_db/atomic_memory_certs/`) that the
//! vendored independent checker replays in this process. Sampling is never
//! evidence for these theorems.
//!
//! # Claim boundary
//!
//! Single-thread VALUE and MEMORY effect of one instruction. Not stated here:
//! single-copy atomicity of the access and its ordering against other
//! threads (the architecture's guarantee for a naturally aligned access, and
//! the `L03-P3` mapping table), alignment (an unaligned atomic access may
//! fault), memory attributes, faults, tagged addresses, the `ST<op>` aliases
//! (refused), and that the instruction implements a SOURCE operation (the
//! binding is to the machine-IR operands only).

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand, SpecialReg};

// ===========================================================================
// Forms
// ===========================================================================

/// The operation one atomic instruction performs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AtomicOp {
    /// `LDAR{B,H,}`: load-acquire, no memory write.
    LoadAcquire,
    /// `STLR{B,H,}`: store-release, no register write.
    StoreRelease,
    /// `CAS{A}{L}{B,H,}`: compare-and-swap; `X[s]` receives the old value.
    Cas,
    /// `SWP{A}{L}{B,H,}`: exchange.
    Swp,
    /// `LDADD`: `old + value`.
    Add,
    /// `LDCLR`: `old AND NOT value`.
    Clr,
    /// `LDEOR`: `old EOR value`.
    Eor,
    /// `LDSET`: `old OR value`.
    Set,
    /// `LDSMAX`: signed maximum.
    Smax,
    /// `LDSMIN`: signed minimum.
    Smin,
    /// `LDUMAX`: unsigned maximum.
    Umax,
    /// `LDUMIN`: unsigned minimum.
    Umin,
}

impl AtomicOp {
    /// Every operation, in table order.
    pub const ALL: [AtomicOp; 12] = [
        AtomicOp::LoadAcquire,
        AtomicOp::StoreRelease,
        AtomicOp::Cas,
        AtomicOp::Swp,
        AtomicOp::Add,
        AtomicOp::Clr,
        AtomicOp::Eor,
        AtomicOp::Set,
        AtomicOp::Smax,
        AtomicOp::Smin,
        AtomicOp::Umax,
        AtomicOp::Umin,
    ];

    /// Lower-case mnemonic stem used in form queries.
    pub const fn stem(self) -> &'static str {
        match self {
            Self::LoadAcquire => "ldar",
            Self::StoreRelease => "stlr",
            Self::Cas => "cas",
            Self::Swp => "swp",
            Self::Add => "ldadd",
            Self::Clr => "ldclr",
            Self::Eor => "ldeor",
            Self::Set => "ldset",
            Self::Smax => "ldsmax",
            Self::Smin => "ldsmin",
            Self::Umax => "ldumax",
            Self::Umin => "ldumin",
        }
    }

    /// Whether the instruction writes a register with the old value.
    pub const fn returns_old(self) -> bool {
        !matches!(self, Self::StoreRelease)
    }

    /// Whether the instruction may write memory.
    pub const fn writes_memory(self) -> bool {
        !matches!(self, Self::LoadAcquire)
    }

    /// The LSE `(o3, opc)` encoding of an `LD<op>`/`SWP` operation.
    pub const fn lse_bits(self) -> Option<(u32, u32)> {
        Some(match self {
            Self::Add => (0, 0b000),
            Self::Clr => (0, 0b001),
            Self::Eor => (0, 0b010),
            Self::Set => (0, 0b011),
            Self::Smax => (0, 0b100),
            Self::Smin => (0, 0b101),
            Self::Umax => (0, 0b110),
            Self::Umin => (0, 0b111),
            Self::Swp => (1, 0b000),
            _ => return None,
        })
    }
}

/// One concrete architectural atomic form: operation and access width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AtomicForm {
    /// The operation.
    pub op: AtomicOp,
    /// Accessed bytes: 1, 2, 4 or 8.
    pub bytes: u32,
}

const fn form(op: AtomicOp, bytes: u32) -> AtomicForm {
    AtomicForm { op, bytes }
}

use AtomicOp::{
    Add as ADD, Cas as CAS, Clr as CLR, Eor as EOR, LoadAcquire as LDAR, Set as SET, Smax as SMAX,
    Smin as SMIN, StoreRelease as STLR, Swp as SWP, Umax as UMAX, Umin as UMIN,
};

/// Every atomic form some emitted opcode can express, with its unique
/// lowercase form query. Each query is a substring of exactly one form
/// theorem name; the closing `]` keeps `w1]` distinct from any longer tag.
pub const ATOMIC_MEMORY_FORMS: [(AtomicForm, &str); 48] = [
    (form(LDAR, 1), "atomicmem[ldar.w1]"),
    (form(LDAR, 2), "atomicmem[ldar.w2]"),
    (form(LDAR, 4), "atomicmem[ldar.w4]"),
    (form(LDAR, 8), "atomicmem[ldar.w8]"),
    (form(STLR, 1), "atomicmem[stlr.w1]"),
    (form(STLR, 2), "atomicmem[stlr.w2]"),
    (form(STLR, 4), "atomicmem[stlr.w4]"),
    (form(STLR, 8), "atomicmem[stlr.w8]"),
    (form(CAS, 1), "atomicmem[cas.w1]"),
    (form(CAS, 2), "atomicmem[cas.w2]"),
    (form(CAS, 4), "atomicmem[cas.w4]"),
    (form(CAS, 8), "atomicmem[cas.w8]"),
    (form(SWP, 1), "atomicmem[swp.w1]"),
    (form(SWP, 2), "atomicmem[swp.w2]"),
    (form(SWP, 4), "atomicmem[swp.w4]"),
    (form(SWP, 8), "atomicmem[swp.w8]"),
    (form(ADD, 1), "atomicmem[ldadd.w1]"),
    (form(ADD, 2), "atomicmem[ldadd.w2]"),
    (form(ADD, 4), "atomicmem[ldadd.w4]"),
    (form(ADD, 8), "atomicmem[ldadd.w8]"),
    (form(CLR, 1), "atomicmem[ldclr.w1]"),
    (form(CLR, 2), "atomicmem[ldclr.w2]"),
    (form(CLR, 4), "atomicmem[ldclr.w4]"),
    (form(CLR, 8), "atomicmem[ldclr.w8]"),
    (form(EOR, 1), "atomicmem[ldeor.w1]"),
    (form(EOR, 2), "atomicmem[ldeor.w2]"),
    (form(EOR, 4), "atomicmem[ldeor.w4]"),
    (form(EOR, 8), "atomicmem[ldeor.w8]"),
    (form(SET, 1), "atomicmem[ldset.w1]"),
    (form(SET, 2), "atomicmem[ldset.w2]"),
    (form(SET, 4), "atomicmem[ldset.w4]"),
    (form(SET, 8), "atomicmem[ldset.w8]"),
    (form(SMAX, 1), "atomicmem[ldsmax.w1]"),
    (form(SMAX, 2), "atomicmem[ldsmax.w2]"),
    (form(SMAX, 4), "atomicmem[ldsmax.w4]"),
    (form(SMAX, 8), "atomicmem[ldsmax.w8]"),
    (form(SMIN, 1), "atomicmem[ldsmin.w1]"),
    (form(SMIN, 2), "atomicmem[ldsmin.w2]"),
    (form(SMIN, 4), "atomicmem[ldsmin.w4]"),
    (form(SMIN, 8), "atomicmem[ldsmin.w8]"),
    (form(UMAX, 1), "atomicmem[ldumax.w1]"),
    (form(UMAX, 2), "atomicmem[ldumax.w2]"),
    (form(UMAX, 4), "atomicmem[ldumax.w4]"),
    (form(UMAX, 8), "atomicmem[ldumax.w8]"),
    (form(UMIN, 1), "atomicmem[ldumin.w1]"),
    (form(UMIN, 2), "atomicmem[ldumin.w2]"),
    (form(UMIN, 4), "atomicmem[ldumin.w4]"),
    (form(UMIN, 8), "atomicmem[ldumin.w8]"),
];

impl AtomicForm {
    /// The unique form query, or `None` for a width no form has.
    pub fn query(&self) -> Option<&'static str> {
        ATOMIC_MEMORY_FORMS
            .iter()
            .find(|(candidate, _)| candidate == self)
            .map(|(_, query)| *query)
    }

    fn mnemonic(&self) -> String {
        let suffix = match self.bytes {
            1 => "B Wt",
            2 => "H Wt",
            4 => " Wt",
            _ => " Xt",
        };
        let stem = self.op.stem().to_ascii_uppercase();
        match self.op {
            AtomicOp::Cas => format!("{stem}{} (Rs=cmp/old, Rt=new)", &suffix[..suffix.len() - 3]),
            AtomicOp::LoadAcquire | AtomicOp::StoreRelease => format!("{stem}{suffix}"),
            _ => format!("{stem}{} (Rs=value, Rt=old)", &suffix[..suffix.len() - 3]),
        }
    }

    /// Form theorem name. Its lowercase form contains [`Self::query`].
    pub fn proof_name(&self) -> String {
        let query = self
            .query()
            .expect("proof_name requires a legal atomic form");
        let tag = &query["atomicmem".len()..];
        let w = self.bytes;
        let effect = match self.op {
            AtomicOp::LoadAcquire => {
                format!("Rt = ZeroExtend({w} LE bytes at Xn); memory unchanged")
            }
            AtomicOp::StoreRelease => {
                format!("{w} LE bytes of Rt at Xn, every other byte unchanged")
            }
            AtomicOp::Cas => format!(
                "Rs = ZeroExtend(old); {w} LE bytes of Rt at Xn iff old == Rs<{}:0>",
                8 * w - 1
            ),
            AtomicOp::Swp => format!("Rt = ZeroExtend(old); {w} LE bytes of Rs at Xn"),
            op => format!(
                "Rt = ZeroExtend(old); {w} LE bytes of old {} Rs<{}:0> at Xn",
                op.stem().trim_start_matches("ld"),
                8 * w - 1
            ),
        };
        format!(
            "AtomicMem{tag}: {} [Xn|SP] == {effect} (Arm MemAtomic, operand-bound)",
            self.mnemonic()
        )
    }
}

/// The 48 faithful atomic form obligations, in table order.
pub fn all_atomic_memory_proofs() -> Vec<ProofObligation> {
    ATOMIC_MEMORY_FORMS
        .iter()
        .map(|(form, _)| proof_atomic_form(form).expect("table forms are legal"))
        .collect()
}

/// The faithful obligation for `form` (`None` for an illegal form).
pub fn proof_atomic_form(form: &AtomicForm) -> Option<ProofObligation> {
    proof_atomic_form_with_mutation(form, AtomicMachineMutation::None)
}

// ===========================================================================
// Obligation construction
// ===========================================================================

/// A deliberate defect injected into the MACHINE side only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AtomicMachineMutation {
    /// The faithful machine semantics.
    None,
    /// The operation is replaced by a near neighbour: `ADD` subtracts, `CLR`
    /// ANDs, `EOR` ORs, `SET` EORs, `CAS` succeeds on inequality, `STLR`
    /// stores the complement.
    WrongOperation,
    /// The two operands of the operation are exchanged (`value AND NOT data`
    /// for `CLR`; `SWP` writes the old value back; `CAS` compares with `X[t]`
    /// and writes `X[s]`).
    OperandsSwapped,
    /// A signed min/max compares unsigned, or the reverse.
    SignednessSwapped,
    /// A maximum computes the minimum, or the reverse.
    MaxMinSwapped,
    /// One byte fewer is read and written.
    ShortAccess,
    /// A writing form writes one byte beyond the access width.
    ExtraStoredByte,
    /// Bytes are read and written big-endian.
    BigEndian,
    /// The access is at `X[n] + 1`.
    OffsetPlusOne,
    /// The returned old value is sign-extended instead of zero-extended.
    SignExtendResult,
    /// The register receives the NEW value instead of the old one.
    ReturnsResult,
    /// A writing form leaves memory unchanged.
    NoWrite,
    /// A compare-and-swap writes `X[t]` whatever the comparison.
    WriteOnFailure,
    /// A narrow compare-and-swap compares the whole 64-bit `X[s]` with the
    /// zero-extended old value.
    CompareFullRegister,
}

impl AtomicMachineMutation {
    /// Every defect the refutation controls exercise.
    pub const DEFECTS: [AtomicMachineMutation; 13] = [
        AtomicMachineMutation::WrongOperation,
        AtomicMachineMutation::OperandsSwapped,
        AtomicMachineMutation::SignednessSwapped,
        AtomicMachineMutation::MaxMinSwapped,
        AtomicMachineMutation::ShortAccess,
        AtomicMachineMutation::ExtraStoredByte,
        AtomicMachineMutation::BigEndian,
        AtomicMachineMutation::OffsetPlusOne,
        AtomicMachineMutation::SignExtendResult,
        AtomicMachineMutation::ReturnsResult,
        AtomicMachineMutation::NoWrite,
        AtomicMachineMutation::WriteOnFailure,
        AtomicMachineMutation::CompareFullRegister,
    ];

    /// Whether this defect changes the semantics of `form`.
    pub fn applies_to(self, form: &AtomicForm) -> bool {
        use AtomicMachineMutation as M;
        let op = form.op;
        let minmax = matches!(op, SMAX | SMIN | UMAX | UMIN);
        match self {
            M::None | M::OffsetPlusOne => true,
            M::WrongOperation => matches!(op, ADD | CLR | EOR | SET | CAS | STLR),
            M::OperandsSwapped => matches!(op, CLR | SWP | CAS | STLR),
            M::SignednessSwapped | M::MaxMinSwapped => minmax,
            M::ShortAccess | M::BigEndian => form.bytes > 1,
            M::ExtraStoredByte | M::NoWrite => op.writes_memory(),
            M::SignExtendResult => op.returns_old() && form.bytes < 8,
            M::ReturnsResult => op.returns_old() && op.writes_memory(),
            M::WriteOnFailure => op == CAS,
            M::CompareFullRegister => op == CAS && form.bytes < 8,
        }
    }
}

/// Input names of every form theorem (a subset per form).
pub const BASE: &str = "amem_base";
/// The register operand `X[s]` (64 bits; the value, or CAS's comparison).
pub const RS: &str = "amem_rs";
/// The register operand `X[t]` (64 bits; STLR's data, or CAS's new value).
pub const RT: &str = "amem_rt";
/// The memory query address.
pub const Q: &str = "amem_q";
/// The memory byte outside the window.
pub const M: &str = "amem_m";
/// The observation selector (`0`: register byte `j`, else the byte at `q`).
pub const SEL: &str = "amem_sel";
/// The observed register byte (`j < 8`).
pub const J: &str = "amem_j";

/// Name of window byte `k`.
pub fn window_byte(k: u32) -> String {
    format!("amem_b{k}")
}

fn c64(value: u64) -> E {
    E::bv_const(value, 64)
}

fn mask(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// Build the obligation for `form` with the given machine-side `mutation`.
/// Returns `None` for an illegal form or a mutation that does not apply.
pub fn proof_atomic_form_with_mutation(
    form: &AtomicForm,
    mutation: AtomicMachineMutation,
) -> Option<ProofObligation> {
    use AtomicMachineMutation as Mu;
    form.query()?;
    if !mutation.applies_to(form) {
        return None;
    }
    let w = form.bytes;
    let bits = 8 * w;
    let op = form.op;

    let mut inputs: Vec<(String, u32)> = Vec::new();
    let mut input = |name: &str, width: u32| {
        inputs.push((name.to_string(), width));
        E::var(name, width)
    };
    let base = input(BASE, 64);
    let window: Vec<E> = (0..w).map(|k| input(&window_byte(k), 8)).collect();
    let m = input(M, 8);
    let q = input(Q, 64);
    let rs = (op != STLR).then(|| input(RS, 64));
    let rt = matches!(op, STLR | CAS).then(|| input(RT, 64));
    let sel = op.returns_old().then(|| input(SEL, 8));
    let j = op.returns_old().then(|| input(J, 8));

    // The pre-state memory: the chain of window points over `m`.
    let memory = |address: E| {
        let mut value = m.clone();
        for k in (0..w).rev() {
            value = E::ite(
                address
                    .clone()
                    .eq_expr(base.clone().bvadd(c64(u64::from(k)))),
                window[k as usize].clone(),
                value,
            );
        }
        value
    };

    // ---------------------------------------------------------------- machine
    let width_read = match mutation {
        Mu::ShortAccess => w - 1,
        _ => w,
    };
    let address = if mutation == Mu::OffsetPlusOne {
        base.clone().bvadd(c64(1))
    } else {
        base.clone()
    };
    // data = Mem[address, w]: byte k at bits 8k+7:8k, OR of positioned bytes.
    let mut data = E::bv_const(0, bits);
    for k in 0..width_read {
        let source = if mutation == Mu::BigEndian {
            w - 1 - k
        } else {
            k
        };
        let byte = memory(address.clone().bvadd(c64(u64::from(source))));
        let wide = if bits > 8 {
            byte.zero_ext(bits - 8)
        } else {
            byte
        };
        let placed = if k > 0 {
            wide.bvshl(E::bv_const(u64::from(8 * k), bits))
        } else {
            wide
        };
        data = data.bvor(placed);
    }
    let low = |register: &E| register.clone().extract(bits - 1, 0);
    let value = rs.as_ref().map(low);
    let new_value = rt.as_ref().map(low);
    let ones = E::bv_const(mask(bits), bits);
    // `MemAtomic` / `MemAtomicCompareAndSwap`: the result written back, and
    // whether a write happens (`None`: always).
    let (result, written): (Option<E>, Option<E>) = match op {
        LDAR => (None, None),
        STLR => {
            let stored = match mutation {
                Mu::WrongOperation => new_value.clone().expect("STLR has Rt").bvxor(ones.clone()),
                Mu::OperandsSwapped => low(&base),
                _ => new_value.clone().expect("STLR has Rt"),
            };
            (Some(stored), None)
        }
        CAS => {
            let (compare_with, new) = if mutation == Mu::OperandsSwapped {
                (new_value.clone(), value.clone())
            } else {
                (value.clone(), new_value.clone())
            };
            let (compare_with, new) = (compare_with.expect("CAS"), new.expect("CAS"));
            let equal = if mutation == Mu::CompareFullRegister {
                rs.clone()
                    .expect("CAS has Rs")
                    .eq_expr(data.clone().zero_ext(64 - bits))
            } else {
                data.clone().eq_expr(compare_with)
            };
            let success = if mutation == Mu::WrongOperation {
                equal.not_expr()
            } else {
                equal
            };
            let written = (mutation != Mu::WriteOnFailure).then_some(success);
            (Some(new), written)
        }
        _ => {
            let v = value.clone().expect("LSE operation has Rs");
            let (a, b) = if mutation == Mu::OperandsSwapped {
                (v.clone(), data.clone())
            } else {
                (data.clone(), v.clone())
            };
            let compare = |signed: bool, x: E, y: E| {
                // `SInt(x) > SInt(y)` / `UInt(x) > UInt(y)`.
                if signed { x.bvsgt(y) } else { x.bvugt(y) }
            };
            let flip_sign = mutation == Mu::SignednessSwapped;
            let flip_max = mutation == Mu::MaxMinSwapped;
            let result = match op {
                SWP => b,
                ADD if mutation == Mu::WrongOperation => a.bvsub(b),
                ADD => a.bvadd(b),
                CLR if mutation == Mu::WrongOperation => a.bvand(b),
                CLR => a.bvand(b.bvxor(ones.clone())),
                EOR if mutation == Mu::WrongOperation => a.bvor(b),
                EOR => a.bvxor(b),
                SET if mutation == Mu::WrongOperation => a.bvxor(b),
                SET => a.bvor(b),
                SMAX | SMIN | UMAX | UMIN => {
                    let signed = matches!(op, SMAX | SMIN) != flip_sign;
                    let maximum = matches!(op, SMAX | UMAX) != flip_max;
                    let greater = compare(signed, a.clone(), b.clone());
                    if maximum {
                        E::ite(greater, a, b)
                    } else {
                        E::ite(greater, b, a)
                    }
                }
                LDAR | STLR | CAS => unreachable!("handled above"),
            };
            (Some(result), None)
        }
    };
    let result = if mutation == Mu::NoWrite {
        None
    } else {
        result
    };
    // Memory after, at `q`: one range write of `w` bytes at `address`.
    let machine_memory = match &result {
        None => memory(q.clone()),
        Some(result) => {
            let length = match mutation {
                Mu::ExtraStoredByte => w + 1,
                Mu::ShortAccess => w - 1,
                _ => w,
            };
            let relative = q.clone().bvsub(address.clone());
            let index = if mutation == Mu::BigEndian {
                c64(u64::from(w) - 1).bvsub(relative.clone())
            } else {
                relative.clone()
            };
            // An extra stored byte (`ExtraStoredByte`) reads past the value,
            // where the 64-bit source holds zero.
            let source = if bits < 64 {
                result.clone().zero_ext(64 - bits)
            } else {
                result.clone()
            };
            let byte = source.bvlshr(index.bvshl(c64(3))).extract(7, 0);
            let write = E::ite(
                relative.bvult(c64(u64::from(length))),
                byte,
                memory(q.clone()),
            );
            match &written {
                None => write,
                Some(condition) => E::ite(condition.clone(), write, memory(q.clone())),
            }
        }
    };
    // The register, byte `j`: `ZeroExtend(data, 64)` read byte-wise, so byte
    // `j` is `Mem[address + j]` below the access width and zero above it.
    let machine_register = j.as_ref().map(|j| {
        let jz = j.clone().zero_ext(56);
        let below = j.clone().bvult(E::bv_const(u64::from(width_read), 8));
        if mutation == Mu::ReturnsResult {
            let returned = match (&result, &written) {
                (Some(result), Some(condition)) => {
                    E::ite(condition.clone(), result.clone(), data.clone())
                }
                (Some(result), None) => result.clone(),
                (None, _) => data.clone(),
            };
            let returned = if bits < 64 {
                returned.zero_ext(64 - bits)
            } else {
                returned
            };
            return returned.bvlshr(jz.bvshl(c64(3))).extract(7, 0);
        }
        let index = if mutation == Mu::BigEndian {
            c64(u64::from(w) - 1).bvsub(jz.clone())
        } else {
            jz
        };
        let byte = memory(address.clone().bvadd(index));
        let fill = if mutation == Mu::SignExtendResult {
            let top = memory(address.clone().bvadd(c64(u64::from(width_read) - 1)));
            E::ite(
                top.extract(7, 7).eq_expr(E::bv_const(1, 1)),
                E::bv_const(0xFF, 8),
                E::bv_const(0, 8),
            )
        } else {
            E::bv_const(0, 8)
        };
        E::ite(below, byte, fill)
    });

    // ----------------------------------------------------------------- intent
    // The old value: concatenated reads at constant offsets from the base.
    let mut old = memory(base.clone());
    for k in 1..w {
        old = memory(base.clone().bvadd(c64(u64::from(k)))).concat(old);
    }
    let old64 = if bits < 64 {
        old.clone().zero_ext(64 - bits)
    } else {
        old.clone()
    };
    let truncate = |value: E| {
        if bits < 64 {
            value.extract(bits - 1, 0)
        } else {
            value
        }
    };
    let zext64 = |value: E| {
        if bits < 64 {
            value.zero_ext(64 - bits)
        } else {
            value
        }
    };
    let sext64 = |value: E| {
        if bits < 64 {
            value.sign_ext(64 - bits)
        } else {
            value
        }
    };
    // The operand's low `w` bytes, as a 64-bit number.
    let operand = |register: &E| {
        if bits < 64 {
            register.clone().bvand(c64(mask(bits)))
        } else {
            register.clone()
        }
    };
    let intent_new: Option<E> = match op {
        LDAR => None,
        STLR => Some(truncate(rt.clone().expect("STLR has Rt"))),
        CAS => {
            let success = old64.clone().eq_expr(operand(rs.as_ref().expect("CAS")));
            Some(E::ite(
                success,
                truncate(rt.clone().expect("CAS has Rt")),
                old.clone(),
            ))
        }
        SWP => Some(truncate(rs.clone().expect("SWP has Rs"))),
        _ => {
            let r = rs.clone().expect("LSE operation has Rs");
            let all_ones = c64(u64::MAX);
            Some(truncate(match op {
                ADD => old64.clone().bvadd(r),
                CLR => old64.clone().bvand(r.bvxor(all_ones)),
                EOR => old64.clone().bvxor(r),
                SET => old64.clone().bvor(r),
                SMAX | SMIN => {
                    let mine = sext64(old.clone());
                    let theirs = sext64(truncate(r.clone()));
                    let keep_old = if op == SMAX {
                        mine.bvsge(theirs)
                    } else {
                        mine.bvsle(theirs)
                    };
                    E::ite(keep_old, old64.clone(), operand(&r))
                }
                UMAX | UMIN => {
                    let theirs = operand(&r);
                    let keep_old = if op == UMAX {
                        old64.clone().bvuge(theirs.clone())
                    } else {
                        old64.clone().bvule(theirs.clone())
                    };
                    E::ite(keep_old, old64.clone(), theirs)
                }
                _ => unreachable!("handled above"),
            }))
        }
    };
    // Memory after, at `q`: `w` single-byte stores at constant offsets.
    let intent_memory = match &intent_new {
        None => memory(q.clone()),
        Some(new) => {
            let mut after = memory(q.clone());
            for k in 0..w {
                after = E::ite(
                    q.clone().eq_expr(base.clone().bvadd(c64(u64::from(k)))),
                    new.clone().extract(8 * k + 7, 8 * k),
                    after,
                );
            }
            after
        }
    };
    // The register, byte `j`: the zero-extended old value shifted right by
    // `8 j`.
    let intent_register = j.as_ref().map(|j| {
        zext64(old.clone())
            .bvlshr(j.clone().zero_ext(56).bvshl(c64(3)))
            .extract(7, 0)
    });
    let mut preconditions = Vec::new();
    if let Some(j) = &j {
        preconditions.push(j.clone().bvult(E::bv_const(8, 8)));
    }

    let (intent, machine) = match (intent_register, machine_register, &sel) {
        (Some(intent_register), Some(machine_register), Some(sel)) => {
            let first = sel.clone().eq_expr(E::bv_const(0, 8));
            (
                E::ite(first.clone(), intent_register, intent_memory),
                E::ite(first, machine_register, machine_memory),
            )
        }
        // STLR: the byte at `q` only.
        (None, None, _) => (intent_memory, machine_memory),
        _ => unreachable!("intent and machine observe the same locations"),
    };

    let name = if mutation == Mu::None {
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
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::MemoryModel),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    })
}

// ===========================================================================
// Instruction binding
// ===========================================================================

/// A concrete atomic instruction bound to exactly one form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtomicBinding {
    /// The form whose theorem this instruction instantiates.
    pub form: AtomicForm,
    /// The `A` bit (`L` for CAS, set for LDAR): acquire.
    pub acquire: bool,
    /// The `R` bit (`o0` for CAS, set for STLR): release.
    pub release: bool,
    /// `Rs` field (31 is ZR); `None` for LDAR/STLR.
    pub rs: Option<u32>,
    /// `Rt` field (31 is ZR).
    pub rt: u32,
    /// `Rn` field (31 is SP).
    pub rn: u32,
}

impl AtomicBinding {
    /// The unique form query of the bound form.
    pub fn query(&self) -> &'static str {
        self.form
            .query()
            .expect("a binding only ever carries a legal form")
    }
}

/// How an opcode fixes its operation, ordering and width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AtomicOpcodeShape {
    /// The operation.
    pub op: AtomicOp,
    /// The `A` bit the opcode encodes.
    pub acquire: bool,
    /// The `R` bit the opcode encodes.
    pub release: bool,
    /// A width the opcode itself fixes (`LDARB`, `STLRH`), else `None`.
    pub fixed_bytes: Option<u32>,
}

/// The shape of an atomic opcode, or `None` for any other opcode.
pub fn atomic_opcode_shape(opcode: O) -> Option<AtomicOpcodeShape> {
    let shape = |op, acquire, release, fixed_bytes| AtomicOpcodeShape {
        op,
        acquire,
        release,
        fixed_bytes,
    };
    let lse = |op, a, r| shape(op, a, r, None);
    Some(match opcode {
        O::Ldar => shape(LDAR, true, false, None),
        O::Ldarb => shape(LDAR, true, false, Some(1)),
        O::Ldarh => shape(LDAR, true, false, Some(2)),
        O::Stlr => shape(STLR, false, true, None),
        O::Stlrb => shape(STLR, false, true, Some(1)),
        O::Stlrh => shape(STLR, false, true, Some(2)),
        O::Cas => lse(CAS, false, false),
        O::Casa => lse(CAS, true, false),
        O::Casal => lse(CAS, true, true),
        O::Casl => lse(CAS, false, true),
        O::Swp => lse(SWP, false, false),
        O::Swpa => lse(SWP, true, false),
        O::Swpal => lse(SWP, true, true),
        O::Swpl => lse(SWP, false, true),
        O::Ldadd => lse(ADD, false, false),
        O::Ldadda => lse(ADD, true, false),
        O::Ldaddal => lse(ADD, true, true),
        O::Ldaddl => lse(ADD, false, true),
        O::Ldclr => lse(CLR, false, false),
        O::Ldclra => lse(CLR, true, false),
        O::Ldclral => lse(CLR, true, true),
        O::Ldclrl => lse(CLR, false, true),
        O::Ldeor => lse(EOR, false, false),
        O::Ldeora => lse(EOR, true, false),
        O::Ldeoral => lse(EOR, true, true),
        O::Ldeorl => lse(EOR, false, true),
        O::Ldset => lse(SET, false, false),
        O::Ldseta => lse(SET, true, false),
        O::Ldsetal => lse(SET, true, true),
        O::Ldsetl => lse(SET, false, true),
        O::Ldsmax => lse(SMAX, false, false),
        O::Ldsmaxa => lse(SMAX, true, false),
        O::Ldsmaxal => lse(SMAX, true, true),
        O::Ldsmaxl => lse(SMAX, false, true),
        O::Ldsmin => lse(SMIN, false, false),
        O::Ldsmina => lse(SMIN, true, false),
        O::Ldsminal => lse(SMIN, true, true),
        O::Ldsminl => lse(SMIN, false, true),
        O::Ldumax => lse(UMAX, false, false),
        O::Ldumaxa => lse(UMAX, true, false),
        O::Ldumaxal => lse(UMAX, true, true),
        O::Ldumaxl => lse(UMAX, false, true),
        O::Ldumin => lse(UMIN, false, false),
        O::Ldumina => lse(UMIN, true, false),
        O::Lduminal => lse(UMIN, true, true),
        O::Lduminl => lse(UMIN, false, true),
        _ => return None,
    })
}

/// True for the 46 single-instruction atomic opcodes this module binds.
pub fn is_atomic_memory_opcode(opcode: O) -> bool {
    atomic_opcode_shape(opcode).is_some()
}

/// Every atomic opcode, in a fixed order.
pub const ATOMIC_MEMORY_OPCODES: [O; 46] = [
    O::Ldar,
    O::Ldarb,
    O::Ldarh,
    O::Stlr,
    O::Stlrb,
    O::Stlrh,
    O::Cas,
    O::Casa,
    O::Casal,
    O::Casl,
    O::Swp,
    O::Swpa,
    O::Swpal,
    O::Swpl,
    O::Ldadd,
    O::Ldadda,
    O::Ldaddal,
    O::Ldaddl,
    O::Ldclr,
    O::Ldclra,
    O::Ldclral,
    O::Ldclrl,
    O::Ldeor,
    O::Ldeora,
    O::Ldeoral,
    O::Ldeorl,
    O::Ldset,
    O::Ldseta,
    O::Ldsetal,
    O::Ldsetl,
    O::Ldsmax,
    O::Ldsmaxa,
    O::Ldsmaxal,
    O::Ldsmaxl,
    O::Ldsmin,
    O::Ldsmina,
    O::Ldsminal,
    O::Ldsminl,
    O::Ldumax,
    O::Ldumaxa,
    O::Ldumaxal,
    O::Ldumaxl,
    O::Ldumin,
    O::Ldumina,
    O::Lduminal,
    O::Lduminl,
];

/// The access widths the encoder can emit for `opcode` (its legal forms), or
/// `None` for a non-atomic opcode. `LDAR`/`STLR` take W or X transfers
/// (4 or 8 bytes) and their `B`/`H` opcodes fix 1 or 2; every LSE and CAS
/// opcode takes all four widths (the narrow ones through the access-size
/// immediate).
pub fn atomic_opcode_forms(opcode: O) -> Option<Vec<AtomicForm>> {
    let shape = atomic_opcode_shape(opcode)?;
    let widths: &[u32] = match (shape.op, shape.fixed_bytes) {
        (_, Some(1)) => &[1],
        (_, Some(2)) => &[2],
        (LDAR | STLR, _) => &[4, 8],
        _ => &[1, 2, 4, 8],
    };
    Some(
        widths
            .iter()
            .map(|&bytes| AtomicForm {
                op: shape.op,
                bytes,
            })
            .collect(),
    )
}

/// A representative instruction of `opcode` at `bytes`, in the operand shape
/// the selector emits: `[Rt, Xn]` for LDAR/STLR (a W transfer below 8 bytes),
/// `[Rs, Rt, Xn]` for the LSE and CAS opcodes at 4 and 8 bytes (W or X
/// registers), and `[Ws, Wt, Xn, #size]` with the access-size immediate at 1
/// and 2 bytes. `None` when `opcode` cannot be emitted at `bytes`. Register
/// numbers are `rs`, `rt`, `rn` (0..=30; `rn` 31 is SP).
pub fn representative_instruction(
    opcode: O,
    bytes: u32,
    rs: u16,
    rt: u16,
    rn: u16,
) -> Option<MachInst> {
    use trust_cg_ir::PReg;
    let forms = atomic_opcode_forms(opcode)?;
    if !forms.iter().any(|form| form.bytes == bytes) {
        return None;
    }
    let gpr = |n: u16| MachOperand::PReg(PReg::new(if bytes == 8 { n } else { 32 + n }));
    let base = if rn == 31 {
        MachOperand::Special(SpecialReg::SP)
    } else {
        MachOperand::PReg(PReg::new(rn))
    };
    let shape = atomic_opcode_shape(opcode)?;
    let operands = match shape.op {
        AtomicOp::LoadAcquire | AtomicOp::StoreRelease => vec![gpr(rt), base],
        _ => {
            let mut operands = vec![gpr(rs), gpr(rt), base];
            match bytes {
                1 => operands.push(MachOperand::Imm(0)),
                2 => operands.push(MachOperand::Imm(1)),
                _ => {}
            }
            operands
        }
    };
    Some(MachInst::new(opcode, operands))
}

/// A general-purpose register operand: `(view bytes, field)`; field 31 is the
/// zero register (SP is not a GPR transfer).
fn gpr(operand: &MachOperand) -> Option<(u32, u32)> {
    match operand {
        MachOperand::PReg(reg) => match reg.encoding() {
            e @ 0..=30 => Some((8, u32::from(e))),
            e @ 32..=62 => Some((4, u32::from(e - 32))),
            160 => Some((8, 31)),
            161 => Some((4, 31)),
            _ => None,
        },
        MachOperand::Special(SpecialReg::XZR) => Some((8, 31)),
        MachOperand::Special(SpecialReg::WZR) => Some((4, 31)),
        _ => None,
    }
}

/// The base: an X register or SP (field 31).
fn base_register(operand: &MachOperand) -> Option<u32> {
    match operand {
        MachOperand::PReg(reg) if reg.encoding() <= 31 => Some(u32::from(reg.encoding())),
        MachOperand::Special(SpecialReg::SP) => Some(31),
        _ => None,
    }
}

/// Bind a concrete atomic instruction to its form, or explain the refusal.
/// `Err` for a malformed or refused shape of an atomic opcode; the opcode
/// must be one of [`ATOMIC_MEMORY_OPCODES`].
pub fn bind_atomic_instruction(inst: &MachInst) -> Result<AtomicBinding, String> {
    let Some(shape) = atomic_opcode_shape(inst.opcode) else {
        return Err(format!(
            "{:?} is not a single-instruction atomic opcode",
            inst.opcode
        ));
    };
    let base_refusal = "atomic base must be an X register or SP";
    let (rs, rt, rn, bytes) = match shape.op {
        LDAR | STLR => {
            let [t, n] = inst.operands.as_slice() else {
                return Err(format!("{:?} requires exactly [Rt, Xn|SP]", inst.opcode));
            };
            let (view, rt) = gpr(t).ok_or("LDAR/STLR transfer must be a W/X/ZR register")?;
            let rn = base_register(n).ok_or(base_refusal)?;
            (None, rt, rn, shape.fixed_bytes.unwrap_or(view))
        }
        _ => {
            let (s, t, n, size) = match inst.operands.as_slice() {
                [s, t, n] => (s, t, n, None),
                [s, t, n, MachOperand::Imm(size)] => (s, t, n, Some(*size)),
                _ => {
                    return Err(format!(
                        "{:?} requires exactly [Rs, Rt, Xn|SP] or [Rs, Rt, Xn|SP, #size]",
                        inst.opcode
                    ));
                }
            };
            let (s_view, rs) = gpr(s).ok_or("atomic Rs must be a W/X/ZR register")?;
            let (t_view, rt) = gpr(t).ok_or("atomic Rt must be a W/X/ZR register")?;
            let rn = base_register(n).ok_or(base_refusal)?;
            let bytes = match size {
                Some(0) => 1,
                Some(1) => 2,
                Some(other) => {
                    return Err(format!(
                        "atomic access-size immediate must be 0 (byte) or 1 (half), got {other}"
                    ));
                }
                None => {
                    if s_view != t_view {
                        return Err(
                            "atomic Rs and Rt must name the same register width when no \
                             access-size immediate is given"
                                .into(),
                        );
                    }
                    if shape.op == CAS { s_view } else { t_view }
                }
            };
            (Some(rs), rt, rn, bytes)
        }
    };
    if shape.op != STLR && shape.op != CAS && rt == 31 {
        return Err(
            "a load-type atomic into the zero register is the ST<op> alias (no value is \
             returned and the acquire is dropped); it is refused"
                .into(),
        );
    }
    if shape.op == CAS && rs == Some(31) {
        return Err(
            "a compare-and-swap whose compare/result register is the zero register is refused \
             (its old value is discarded)"
                .into(),
        );
    }
    let form = AtomicForm {
        op: shape.op,
        bytes,
    };
    if form.query().is_none() {
        return Err(format!("no legal atomic form for {form:?}"));
    }
    Ok(AtomicBinding {
        form,
        acquire: shape.acquire,
        release: shape.release,
        rs,
        rt,
        rn,
    })
}

fn size_field(bytes: u32) -> u32 {
    match bytes {
        1 => 0b00,
        2 => 0b01,
        4 => 0b10,
        _ => 0b11,
    }
}

/// The word of `binding`, from this module's own encoder (Arm DDI 0487
/// C4.1.94 and the "Load/store ordered" and "Compare and swap" classes):
///
/// ```text
/// size 001000 1 1 0 11111 1 11111 Rn Rt     LDAR
/// size 001000 1 0 0 11111 1 11111 Rn Rt     STLR
/// size 001000 1 L 1 Rs   o0 11111 Rn Rt     CAS   (L = acquire, o0 = release)
/// size 111000 A R 1 Rs   o3 opc 00 Rn Rt    LD<op>/SWP
/// ```
pub fn atomic_word(binding: &AtomicBinding) -> u32 {
    let size = size_field(binding.form.bytes) << 30;
    let tail = (binding.rn << 5) | binding.rt;
    let a = u32::from(binding.acquire);
    let r = u32::from(binding.release);
    match binding.form.op {
        LDAR => size | 0x08DF_FC00 | tail,
        STLR => size | 0x089F_FC00 | tail,
        CAS => size | 0x08A0_7C00 | (a << 22) | (binding.rs.unwrap_or(31) << 16) | (r << 15) | tail,
        op => {
            let (o3, opc) = op.lse_bits().expect("LSE operation");
            size | 0x3820_0000
                | (a << 23)
                | (r << 22)
                | (binding.rs.unwrap_or(31) << 16)
                | (o3 << 15)
                | (opc << 12)
                | tail
        }
    }
}

/// The binding a word denotes, decoded from its bits independently of
/// [`bind_atomic_instruction`] and [`atomic_word`], or `None` when the word is
/// not an instance of an attributable atomic form (another class, `LDAPR`,
/// the LORegion `LDLAR`/`STLLR`, an exclusive, `CASP`, an `ST<op>` alias or a
/// zero-register CAS compare register).
pub fn decode_atomic_word(word: u32) -> Option<AtomicBinding> {
    let bit = |n: u32| (word >> n) & 1;
    let bits = |hi: u32, lo: u32| (word >> lo) & ((1 << (hi - lo + 1)) - 1);
    let bytes = 1u32 << bits(31, 30);
    let rs = bits(20, 16);
    let rt = bits(4, 0);
    let rn = bits(9, 5);
    if bits(29, 24) == 0b00_1000 {
        // `size 001000 o2 L o1 Rs o0 Rt2 Rn Rt`.
        let (o2, l, o1, o0) = (bit(23), bit(22), bit(21), bit(15));
        if bits(14, 10) != 0b1_1111 {
            return None;
        }
        let (op, acquire, release, rs) = match (o2, o1) {
            (1, 0) => {
                if rs != 0b1_1111 || o0 != 1 {
                    return None;
                }
                if l == 1 {
                    (LDAR, true, false, None)
                } else {
                    (STLR, false, true, None)
                }
            }
            (1, 1) => {
                if rs == 31 {
                    return None;
                }
                (CAS, l == 1, o0 == 1, Some(rs))
            }
            _ => return None,
        };
        if op == LDAR && rt == 31 {
            return None;
        }
        return Some(AtomicBinding {
            form: AtomicForm { op, bytes },
            acquire,
            release,
            rs,
            rt,
            rn,
        });
    }
    // `size 111 0 00 A R 1 Rs o3 opc 00 Rn Rt`.
    if word & 0x3F20_0C00 == 0x3820_0000 {
        let op = match (bit(15), bits(14, 12)) {
            (0, 0b000) => ADD,
            (0, 0b001) => CLR,
            (0, 0b010) => EOR,
            (0, 0b011) => SET,
            (0, 0b100) => SMAX,
            (0, 0b101) => SMIN,
            (0, 0b110) => UMAX,
            (0, 0b111) => UMIN,
            (1, 0b000) => SWP,
            _ => return None,
        };
        if rt == 31 {
            return None;
        }
        return Some(AtomicBinding {
            form: AtomicForm { op, bytes },
            acquire: bit(23) == 1,
            release: bit(22) == 1,
            rs: Some(rs),
            rt,
            rn,
        });
    }
    None
}

/// One distinct exact atomic form query (every atomic form is its own).
#[derive(Debug, Clone)]
pub struct CertifiableAtomicQuery {
    /// Certificate filename in `verdict_db/atomic_memory_certs/`.
    pub file: String,
    /// The form theorem's name.
    pub form: String,
    /// The form theorem.
    pub obligation: ProofObligation,
}

/// Every atomic form theorem with its certificate filename, in table order.
pub fn certifiable_atomic_queries() -> Vec<CertifiableAtomicQuery> {
    ATOMIC_MEMORY_FORMS
        .iter()
        .map(|(form, query)| {
            let tag = query
                .trim_start_matches("atomicmem[")
                .trim_end_matches(']')
                .replace('.', "_");
            let obligation = proof_atomic_form(form).expect("table forms are legal");
            CertifiableAtomicQuery {
                file: format!("atomicmem_{tag}.lratcert"),
                form: obligation.name.clone(),
                obligation,
            }
        })
        .collect()
}

/// A deliberately WRONG atomic theorem wearing a faithful form's name (the
/// machine side returns the new value instead of the old one). The
/// certificate consumer must refuse it: its exact query is not the faithful
/// one.
pub fn representative_wrong_atomic_theorem() -> ProofObligation {
    let form = AtomicForm { op: ADD, bytes: 8 };
    let mut wrong = proof_atomic_form_with_mutation(&form, AtomicMachineMutation::ReturnsResult)
        .expect("ReturnsResult applies to LDADD");
    wrong.name = form.proof_name();
    wrong
}

// ===========================================================================
// In-process refutation of a form theorem over a structured grid
// ===========================================================================

/// One assignment of every input of an atomic form theorem.
fn grid_points(form: &AtomicForm) -> Vec<Vec<(String, u64)>> {
    let w = form.bytes;
    let bits = 8 * w;
    let bases = [0x1000u64, 0xFFFF_FFFF_FFFF_FFFC, 0x7FFF_FFFF_FFFF_FFFD];
    // Window contents as little-endian values: zero, all ones, the sign
    // boundaries, and two irregular patterns.
    let sign = 1u64 << (bits - 1);
    let windows = [
        0u64,
        mask(bits),
        sign,
        sign - 1,
        0x8877_6655_4433_2211 & mask(bits),
        0x0123_4567_89AB_CDEF & mask(bits),
    ];
    let operands = [
        0u64,
        1,
        u64::MAX,
        sign,
        sign - 1,
        0xF0F0_0F0F_A5A5_5A5A,
        0x0000_0001_0000_0001,
    ];
    let mut points = Vec::new();
    for &base in &bases {
        for &window in &windows {
            for &rs in &operands {
                // `rt` is also tried equal to the window, and `rs` equal to the
                // window (CAS success) with garbage above the access width.
                for rt in [rs.rotate_left(13) ^ 0x5555, window | !mask(bits)] {
                    for rs in [rs, window, window | (rs & !mask(bits))] {
                        let queries: Vec<u64> = (0..=u64::from(w))
                            .map(|k| base.wrapping_add(k))
                            .chain([base.wrapping_sub(1), base.wrapping_add(8)])
                            .collect();
                        // The register is observed at every byte `j` (with one
                        // query address), memory at every query address.
                        let observations = (0..8u64)
                            .map(|j| (0u64, j, base))
                            .chain(queries.into_iter().map(|q| (1, 0, q)));
                        for (sel, j, q) in observations {
                            {
                                let mut point = vec![
                                    (BASE.to_string(), base),
                                    (M.to_string(), 0xC3),
                                    (Q.to_string(), q),
                                    (RS.to_string(), rs),
                                    (RT.to_string(), rt),
                                    (SEL.to_string(), sel),
                                    (J.to_string(), j),
                                ];
                                for k in 0..w {
                                    point.push((window_byte(k), (window >> (8 * k)) & 0xFF));
                                }
                                points.push(point);
                            }
                        }
                    }
                }
            }
        }
    }
    points
}

/// Search a structured grid (base addresses that wrap, sign-boundary window
/// and operand values, CAS successes, every query address in and around the
/// window, both observations) for a point where the two sides differ.
///
/// `Some(point)` is a definite counterexample (both sides evaluated); `None`
/// means none was found on the grid, which is NOT evidence that the theorem
/// holds: a faithful form theorem is credited only by a replayed certificate.
pub fn grid_counterexample(form: &AtomicForm, obligation: &ProofObligation) -> Option<String> {
    for point in grid_points(form) {
        let mut env = crate::smt::EvalEnv::default();
        for (name, value) in &point {
            if obligation.inputs.iter().any(|(input, _)| input == name) {
                env.insert(name.clone(), *value);
            }
        }
        let (Ok(intent), Ok(machine)) = (
            obligation.trust_ir_expr.try_eval(&env),
            obligation.aarch64_expr.try_eval(&env),
        ) else {
            continue;
        };
        if intent != machine {
            return Some(format!("{point:?}: intent {intent:?} machine {machine:?}"));
        }
    }
    None
}

#[cfg(test)]
#[path = "aarch64_atomic_forms_tests.rs"]
mod tests;
