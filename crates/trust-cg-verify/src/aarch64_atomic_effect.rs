// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Word-bound, decomposed value and memory-effect obligations for the 46
//! single-instruction AArch64 atomic opcodes (ledger `X-OPCODES-P2`,
//! `L04-P1`): `LDAR{,B,H}`, `STLR{,B,H}`, `CAS{,A,AL,L}`, `SWP{,A,AL,L}` and
//! `LD{ADD,CLR,EOR,SET,SMAX,SMIN,UMAX,UMIN}{,A,AL,L}` at every access width.
//!
//! # Bound to the word
//!
//! As in [`crate::aarch64_memory_effect`], the instruction WORD is a 32-bit
//! literal inside every part, and the machine side of each part is computed
//! from that literal's bits by SMT terms: the access width from `size`, the
//! instruction class from the fixed class bits, the operation from `o3`/`opc`
//! (or the CAS/LDAR/STLR class), and register 31 in a data position read as
//! zero. The word is the one [`atomic_effect_word`] re-derives from the
//! operands with [`crate::aarch64_atomic_forms::atomic_word`]; ENC-5
//! (`trust-cg-codegen` `decode_check`) requires the emitted word to equal it
//! ([`check_emitted_atomic_word`]). The intent side of each part is built
//! from the OPERANDS alone ([`crate::aarch64_atomic_forms::bind_atomic_instruction`]).
//!
//! # The parts
//!
//! * `fields` (ground): every field of the word equals the value the operands
//!   name — size, the class bits, the ordering bits (`A`/`R`, `L`/`o0`), the
//!   operation (`o3`/`opc`), and the register fields `Rs`, `Rt`, `Rn` (and the
//!   fixed `Rt2`/`Rs` of the ordered class).
//! * `value` (every form but `STLR`): the 64-bit value the word writes to its
//!   destination register (`Rt`, or `Rs` for CAS) — the low `size` bytes of a
//!   symbolic 8-byte memory window at `X[n]`, zero-extended (A6: a W write
//!   clears bits 63:32) — equals the operands' value.
//! * `memory` (every form): the 8-byte window the word leaves — the word's
//!   operation at its width over the old window and the data registers, the
//!   bytes above the width unchanged, nothing written for `LDAR` and for a
//!   failed CAS comparison — equals the operands' window.
//!
//! When every part holds, executing the word (Arm DDI 0487 pseudo-code of
//! `MemAtomic` / `MemAtomicCompareAndSwap`, `LDAR`, `STLR`) from ANY register
//! file and memory gives the registers and memory the operands' atomic access
//! names, under the assumptions of [`crate::aarch64_memory_effect`] (A1
//! little-endian data, A5 Normal memory, A6 register naming), with no
//! alignment fault, and with the access single-copy atomic (the
//! architecture's guarantee for an aligned access; not stated here). The
//! ordering of the access against other threads is the ordering table of
//! ledger `L03-P3` ([`crate::aarch64_memory_order`]): this decomposition only
//! pins the `A`/`R` bits in `fields`.
//!
//! # What it is, and is not, worth
//!
//! [`decide_exactly`] decides each symbolic part for every input: the word's
//! fields are folded away, a 64-bit window that keeps its upper bytes is split
//! at the access width, a selection between two values is lifted into a
//! Boolean case split, and what remains is decided by the bit-serial automaton
//! ([`crate::bitserial_decide`]), whose verdict is re-evaluated before a
//! refutation is reported. That is an in-process decision by unverified Rust:
//! TESTING-GRADE evidence, never credit. It is the in-process refutation check
//! (rule clause 2) of the Formal-only rule
//! ([`crate::bound_memory_authority`]) for an atomic row: the row is credited
//! only by a replayed certificate of its form theorem
//! ([`crate::aarch64_atomic_forms`]), and only when this check held on the
//! word whose form the certificate is about.

use crate::aarch64_atomic_forms::{
    AtomicBinding, AtomicOp, atomic_word, bind_atomic_instruction, decode_atomic_word,
};
use crate::bitserial_decide::{Exact, decide_equal};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use trust_cg_ir::{AArch64Opcode as O, MachInst};

/// The 8-byte memory window at `X[n]` before the access.
pub const WINDOW: &str = "w0";
/// `X[s]` (the operation's value, or CAS's comparison value).
pub const REG_S: &str = "s";
/// `X[t]` (STLR's data, or CAS's new value).
pub const REG_T: &str = "t";

/// The access the operands name, or `None` for a non-atomic or refused
/// shape.
pub fn atomic_access(inst: &MachInst) -> Option<AtomicBinding> {
    bind_atomic_instruction(inst).ok()
}

/// The word the parts carry: the binding's word from the verify-side
/// encoder.
pub fn atomic_effect_word(inst: &MachInst) -> Option<u32> {
    atomic_access(inst).map(|binding| atomic_word(&binding))
}

/// ENC-5's binding of the emitted word to the word the parts carry:
/// `Some(Ok(()))` when `emitted` equals [`atomic_effect_word`] and decodes
/// back to the operands' binding, `Some(Err(_))` otherwise, `None` when `inst`
/// is not an admitted atomic access (no claim).
pub fn check_emitted_atomic_word(inst: &MachInst, emitted: u32) -> Option<Result<(), String>> {
    let binding = atomic_access(inst)?;
    let expected = atomic_word(&binding);
    Some(if emitted != expected {
        Err(format!(
            "emitted word {emitted:#010x} is not the word {expected:#010x} the atomic \
             value/memory-effect obligations carry"
        ))
    } else if decode_atomic_word(emitted) != Some(binding) {
        Err(format!(
            "emitted word {emitted:#010x} does not decode to the operands' atomic form \
             {binding:?}"
        ))
    } else {
        Ok(())
    })
}

// ===========================================================================
// Parts
// ===========================================================================

/// Which fact of the access one part states.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AtomicEffectPart {
    /// Every field of the word.
    Fields,
    /// The value written to the destination register.
    Value,
    /// The 8-byte memory window after the access.
    Memory,
}

impl std::fmt::Display for AtomicEffectPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fields => write!(f, "fields"),
            Self::Value => write!(f, "value"),
            Self::Memory => write!(f, "memory"),
        }
    }
}

/// One part and its obligation (`trust_ir_expr` is the operands' side,
/// `aarch64_expr` the word's).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicEffectObligation {
    /// Which fact it states.
    pub part: AtomicEffectPart,
    /// The obligation.
    pub obligation: ProofObligation,
}

/// Every part of one admitted atomic access, for one word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicEffectDecomposition {
    /// The access the operands name.
    pub binding: AtomicBinding,
    /// The word every part carries.
    pub word: u32,
    /// The parts: fields, value (not for STLR), memory.
    pub parts: Vec<AtomicEffectObligation>,
}

/// The decomposition of `inst` over its re-derived word.
pub fn atomic_effect(inst: &MachInst) -> Option<AtomicEffectDecomposition> {
    let word = atomic_effect_word(inst)?;
    atomic_effect_for_word(inst, word)
}

/// The decomposition of `inst` over a caller-supplied word: the seam the
/// negative controls feed mutated words through.
pub fn atomic_effect_for_word(inst: &MachInst, word: u32) -> Option<AtomicEffectDecomposition> {
    let binding = atomic_access(inst)?;
    Some(decompose(inst.opcode, &binding, word))
}

/// The decomposition of a binding over a word (the gate's representative
/// instructions and the silicon differential build bindings directly).
pub fn atomic_effect_for_binding(
    opcode: O,
    binding: &AtomicBinding,
    word: u32,
) -> AtomicEffectDecomposition {
    decompose(opcode, binding, word)
}

fn decompose(opcode: O, binding: &AtomicBinding, word: u32) -> AtomicEffectDecomposition {
    let label = format!("A64 atomic effect {opcode:?} {word:#010x}");
    let mut parts = vec![part(
        &label,
        AtomicEffectPart::Fields,
        E::bool_const(true),
        fields_conjunction(binding, word),
        opcode,
    )];
    if binding.form.op.returns_old() {
        parts.push(part(
            &label,
            AtomicEffectPart::Value,
            value_intent(binding),
            value_machine(word),
            opcode,
        ));
    }
    parts.push(part(
        &label,
        AtomicEffectPart::Memory,
        memory_intent(binding),
        memory_machine(word),
        opcode,
    ));
    AtomicEffectDecomposition {
        binding: *binding,
        word,
        parts,
    }
}

fn part(
    label: &str,
    which: AtomicEffectPart,
    intent: E,
    machine: E,
    opcode: O,
) -> AtomicEffectObligation {
    let mut inputs: Vec<(String, u32)> = Vec::new();
    for expr in [&intent, &machine] {
        collect_vars(expr, &mut inputs);
    }
    inputs.sort();
    AtomicEffectObligation {
        part: which,
        obligation: ProofObligation {
            name: format!("{label}: {which}"),
            trust_ir_expr: intent,
            aarch64_expr: machine,
            inputs,
            preconditions: Vec::new(),
            fp_inputs: Vec::new(),
            category: Some(TransvalCheckKind::MemoryModel),
            machine_side_provenance: MachineSideProvenance::Reconstructed {
                from_opcode: format!("{opcode:?}"),
                arity: 1,
            },
        },
    }
}

fn collect_vars(expr: &E, out: &mut Vec<(String, u32)>) {
    if let E::Var { name, width } = expr {
        if !out.iter().any(|(seen, _)| seen == name) {
            out.push((name.clone(), *width));
        }
        return;
    }
    expr.for_each_child(&mut |child| collect_vars(child, out));
}

// ---------------------------------------------------------------------------
// Word fields, as SMT terms over the literal
// ---------------------------------------------------------------------------

fn literal(word: u32) -> E {
    E::bv_const(u64::from(word), 32)
}

fn field(word: u32, hi: u32, lo: u32) -> E {
    literal(word).extract(hi, lo)
}

fn field_is(word: u32, hi: u32, lo: u32, value: u64) -> E {
    field(word, hi, lo).eq_expr(E::bv_const(value, hi - lo + 1))
}

fn zeros(width: u32) -> E {
    E::bv_const(0, width)
}

/// `x` zero-extended by `k` bits, spelled `(concat (_ bv0 k) x)` (the
/// spelling [`crate::aarch64_memory_effect`] uses for the packaged Clean).
fn zero_extend(x: E, k: u32) -> E {
    if k == 0 { x } else { zeros(k).concat(x) }
}

fn ones(width: u32) -> E {
    E::bv_const(
        if width >= 64 {
            u64::MAX
        } else {
            (1 << width) - 1
        },
        width,
    )
}

fn size_is(word: u32, value: u64) -> E {
    field_is(word, 31, 30, value)
}

/// The ordered / compare-and-swap class: bits 29:24 = `001000`.
fn ordered_class(word: u32) -> E {
    field_is(word, 29, 24, 0b00_1000)
}

/// `CAS`: the ordered class with `o2 = 1`, `o1 = 1`.
fn is_cas(word: u32) -> E {
    ordered_class(word)
        .and_expr(field_is(word, 23, 23, 1))
        .and_expr(field_is(word, 21, 21, 1))
}

/// `LDAR`: the ordered class with `o2 = 1`, `L = 1`, `o1 = 0`.
fn is_ldar(word: u32) -> E {
    ordered_class(word)
        .and_expr(field_is(word, 23, 22, 0b11))
        .and_expr(field_is(word, 21, 21, 0))
}

/// `STLR`: the ordered class with `o2 = 1`, `L = 0`, `o1 = 0`.
fn is_stlr(word: u32) -> E {
    ordered_class(word)
        .and_expr(field_is(word, 23, 22, 0b10))
        .and_expr(field_is(word, 21, 21, 0))
}

/// `X[s]` as the word reads it: register 31 in the `Rs` position is the zero
/// register (A6).
fn read_s(word: u32) -> E {
    E::ite(field_is(word, 20, 16, 31), zeros(64), E::var(REG_S, 64))
}

/// `X[t]` as the word reads it (STLR's data, CAS's new value).
fn read_t(word: u32) -> E {
    E::ite(field_is(word, 4, 0, 31), zeros(64), E::var(REG_T, 64))
}

// ---------------------------------------------------------------------------
// fields
// ---------------------------------------------------------------------------

fn size_field(bytes: u32) -> u64 {
    match bytes {
        1 => 0b00,
        2 => 0b01,
        4 => 0b10,
        _ => 0b11,
    }
}

/// `(hi, lo, value)` of every field, from the operands.
fn intended_fields(binding: &AtomicBinding) -> Vec<(u32, u32, u64)> {
    let size = size_field(binding.form.bytes);
    let rt = u64::from(binding.rt);
    let rn = u64::from(binding.rn);
    let a = u64::from(binding.acquire);
    let r = u64::from(binding.release);
    let rs = u64::from(binding.rs.unwrap_or(31));
    match binding.form.op {
        AtomicOp::LoadAcquire | AtomicOp::StoreRelease => vec![
            (31, 30, size),
            (29, 24, 0b00_1000),
            (23, 23, 1),
            (22, 22, u64::from(binding.form.op == AtomicOp::LoadAcquire)),
            (21, 21, 0),
            (20, 16, 0b1_1111),
            (15, 15, 1),
            (14, 10, 0b1_1111),
            (9, 5, rn),
            (4, 0, rt),
        ],
        AtomicOp::Cas => vec![
            (31, 30, size),
            (29, 24, 0b00_1000),
            (23, 23, 1),
            (22, 22, a),
            (21, 21, 1),
            (20, 16, rs),
            (15, 15, r),
            (14, 10, 0b1_1111),
            (9, 5, rn),
            (4, 0, rt),
        ],
        op => {
            let (o3, opc) = op.lse_bits().expect("LSE operation");
            vec![
                (31, 30, size),
                (29, 27, 0b111),
                (26, 26, 0),
                (25, 24, 0b00),
                (23, 23, a),
                (22, 22, r),
                (21, 21, 1),
                (20, 16, rs),
                (15, 15, u64::from(o3)),
                (14, 12, u64::from(opc)),
                (11, 10, 0b00),
                (9, 5, rn),
                (4, 0, rt),
            ]
        }
    }
}

fn fields_conjunction(binding: &AtomicBinding, word: u32) -> E {
    let mut conjuncts = intended_fields(binding)
        .into_iter()
        .map(|(hi, lo, value)| field_is(word, hi, lo, value));
    let first = conjuncts.next().unwrap_or_else(|| E::bool_const(true));
    conjuncts.fold(first, E::and_expr)
}

// ---------------------------------------------------------------------------
// value
// ---------------------------------------------------------------------------

fn window() -> E {
    E::var(WINDOW, 64)
}

/// The operands' returned value: the window's low `n` bytes, zero-extended.
fn value_intent(binding: &AtomicBinding) -> E {
    let bits = 8 * binding.form.bytes;
    if bits == 64 {
        window()
    } else {
        zero_extend(window().extract(bits - 1, 0), 64 - bits)
    }
}

/// The word's returned value: `ZeroExtend(Mem[X[n], size], 64)`.
fn value_machine(word: u32) -> E {
    let low = |bits: u32| zero_extend(window().extract(bits - 1, 0), 64 - bits);
    E::ite(
        size_is(word, 0b11),
        window(),
        E::ite(
            size_is(word, 0b10),
            low(32),
            E::ite(size_is(word, 0b01), low(16), low(8)),
        ),
    )
}

// ---------------------------------------------------------------------------
// memory
// ---------------------------------------------------------------------------

/// The word's operation at `bits` over the old window's low bits (`MemAtomic`
/// / `MemAtomicCompareAndSwap`, Arm DDI 0487 J1).
fn machine_result(word: u32, bits: u32) -> E {
    let data = window().extract(bits - 1, 0);
    let value = read_s(word).extract(bits - 1, 0);
    let new_value = read_t(word).extract(bits - 1, 0);
    let opc = |value: u64| field_is(word, 14, 12, value);
    let lse = E::ite(
        field_is(word, 15, 15, 1),
        // SWP (o3 = 1, opc = 000; other o3 = 1 encodings are not admitted).
        value.clone(),
        E::ite(
            opc(0b000),
            data.clone().bvadd(value.clone()),
            E::ite(
                opc(0b001),
                data.clone().bvand(value.clone().bvxor(ones(bits))),
                E::ite(
                    opc(0b010),
                    data.clone().bvxor(value.clone()),
                    E::ite(
                        opc(0b011),
                        data.clone().bvor(value.clone()),
                        E::ite(
                            opc(0b100),
                            E::ite(
                                data.clone().bvsgt(value.clone()),
                                data.clone(),
                                value.clone(),
                            ),
                            E::ite(
                                opc(0b101),
                                E::ite(
                                    data.clone().bvsgt(value.clone()),
                                    value.clone(),
                                    data.clone(),
                                ),
                                E::ite(
                                    opc(0b110),
                                    E::ite(
                                        data.clone().bvugt(value.clone()),
                                        data.clone(),
                                        value.clone(),
                                    ),
                                    E::ite(
                                        data.clone().bvugt(value.clone()),
                                        value.clone(),
                                        data.clone(),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    E::ite(
        is_ldar(word),
        data.clone(),
        E::ite(
            is_stlr(word),
            new_value.clone(),
            E::ite(
                is_cas(word),
                E::ite(data.clone().eq_expr(value), new_value, data),
                lse,
            ),
        ),
    )
}

/// The window the word leaves: its result at its width, the window's bytes
/// above the width unchanged.
fn memory_machine(word: u32) -> E {
    let merged = |bits: u32| {
        if bits == 64 {
            machine_result(word, 64)
        } else {
            window()
                .extract(63, bits)
                .concat(machine_result(word, bits))
        }
    };
    E::ite(
        size_is(word, 0b11),
        merged(64),
        E::ite(
            size_is(word, 0b10),
            merged(32),
            E::ite(size_is(word, 0b01), merged(16), merged(8)),
        ),
    )
}

/// The operands' new value at `bits`, stated on 64-bit extended operands and
/// truncated (independently of [`machine_result`]).
fn intent_result(binding: &AtomicBinding) -> E {
    let bits = 8 * binding.form.bytes;
    let truncate = |value: E| {
        if bits < 64 {
            value.extract(bits - 1, 0)
        } else {
            value
        }
    };
    let old = truncate(window());
    let old_zx = if bits < 64 {
        old.clone().zero_ext(64 - bits)
    } else {
        old.clone()
    };
    let old_sx = if bits < 64 {
        old.clone().sign_ext(64 - bits)
    } else {
        old.clone()
    };
    let register = |field: Option<u32>, name: &str| match field {
        Some(31) => zeros(64),
        _ => E::var(name, 64),
    };
    let s = register(binding.rs, REG_S);
    let t = register(Some(binding.rt), REG_T);
    let mask = E::bv_const(
        if bits >= 64 {
            u64::MAX
        } else {
            (1 << bits) - 1
        },
        64,
    );
    let s_zx = s.clone().bvand(mask.clone());
    let s_sx = if bits < 64 {
        truncate(s.clone()).sign_ext(64 - bits)
    } else {
        s.clone()
    };
    match binding.form.op {
        AtomicOp::LoadAcquire => old,
        AtomicOp::StoreRelease => truncate(t),
        AtomicOp::Cas => E::ite(old_zx.eq_expr(s_zx), truncate(t), old),
        AtomicOp::Swp => truncate(s),
        AtomicOp::Add => truncate(old_zx.bvadd(s)),
        AtomicOp::Clr => truncate(old_zx.bvand(s.bvxor(E::bv_const(u64::MAX, 64)))),
        AtomicOp::Eor => truncate(old_zx.bvxor(s)),
        AtomicOp::Set => truncate(old_zx.bvor(s)),
        AtomicOp::Smax => E::ite(old_sx.bvsge(s_sx), old, truncate(s)),
        AtomicOp::Smin => E::ite(old_sx.bvsle(s_sx), old, truncate(s)),
        AtomicOp::Umax => E::ite(old_zx.bvuge(s_zx), old, truncate(s)),
        AtomicOp::Umin => E::ite(old_zx.bvule(s_zx), old, truncate(s)),
    }
}

/// The operands' window after the access.
fn memory_intent(binding: &AtomicBinding) -> E {
    let bits = 8 * binding.form.bytes;
    if bits == 64 {
        intent_result(binding)
    } else {
        window().extract(63, bits).concat(intent_result(binding))
    }
}

// ===========================================================================
// In-process decision
// ===========================================================================

/// How the decomposition of one word fared in process: never proof credit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicEffectVerdict {
    /// Every part holds for every input (a ground part evaluated, a symbolic
    /// part by [`decide_exactly`]).
    Holds,
    /// A part is refuted (the word does not perform the operands' access).
    Refuted {
        /// The refuted part.
        part: AtomicEffectPart,
        /// Why.
        detail: String,
    },
    /// A part could not be decided exactly.
    Undecided {
        /// The undecided part.
        part: AtomicEffectPart,
        /// Why.
        detail: String,
    },
}

/// Decide every part of `decomposition`.
pub fn judge(decomposition: &AtomicEffectDecomposition) -> AtomicEffectVerdict {
    for part in &decomposition.parts {
        let obligation = &part.obligation;
        let outcome = if obligation.inputs.is_empty() {
            let env = crate::smt::EvalEnv::default();
            match obligation.negated_equivalence().try_eval(&env) {
                Ok(result) => {
                    if result.as_bool() {
                        Some(Err("the ground part evaluates false".to_string()))
                    } else {
                        Some(Ok(()))
                    }
                }
                Err(error) => {
                    return AtomicEffectVerdict::Undecided {
                        part: part.part,
                        detail: error.to_string(),
                    };
                }
            }
        } else {
            decide_exactly(obligation)
        };
        match outcome {
            Some(Ok(())) => {}
            Some(Err(detail)) => {
                return AtomicEffectVerdict::Refuted {
                    part: part.part,
                    detail,
                };
            }
            None => {
                return AtomicEffectVerdict::Undecided {
                    part: part.part,
                    detail: "outside the exactly decided fragment".to_string(),
                };
            }
        }
    }
    AtomicEffectVerdict::Holds
}

/// Decide a symbolic part for every input, or `None` when its shape is
/// outside what this decides.
///
/// Both sides are folded (every variable-free subterm evaluated, every `ite`
/// on a constant condition replaced by its taken branch, `concat` with zero
/// bits read as `zero_extend`). Two `concat`s with the same split are decided
/// half by half. A half is decided by syntactic identity, by exact bit
/// routing ([`crate::aarch64_value_decode_proofs::exact_routing_equality`]),
/// or by the bit-serial automaton after lifting every selection between two
/// values into a Boolean case split; a bit-serial refutation carries an
/// assignment the ordinary evaluator confirmed. Still an in-process decision,
/// never a certificate.
pub fn decide_exactly(obligation: &ProofObligation) -> Option<Result<(), String>> {
    let intent = fold(&obligation.trust_ir_expr)?;
    let machine = fold(&obligation.aarch64_expr)?;
    decide_folded(&intent, &machine)
}

fn decide_folded(intent: &E, machine: &E) -> Option<Result<(), String>> {
    if intent == machine {
        return Some(Ok(()));
    }
    if let (E::Concat { hi: ih, lo: il, .. }, E::Concat { hi: mh, lo: ml, .. }) = (intent, machine)
        && il.bv_width() == ml.bv_width()
        && !is_zero(ih)
        && !is_zero(mh)
    {
        return match decide_folded(ih, mh)? {
            Ok(()) => decide_folded(il, ml),
            Err(why) => Some(Err(format!("upper bytes: {why}"))),
        };
    }
    if let Some(verdict) =
        crate::aarch64_value_decode_proofs::exact_routing_equality(intent, machine)
    {
        return Some(match verdict {
            Ok(()) => Ok(()),
            Err(mismatch) => Err(format!(
                "bit {} is {:?} in the operands' access but {:?} in the word",
                mismatch.bit, mismatch.intended, mismatch.emitted
            )),
        });
    }
    let goal = lift_equality(&normalize(intent), &normalize(machine));
    match decide_equal(&goal, &E::bool_const(true)).ok()? {
        Exact::Holds => Some(Ok(())),
        Exact::Refuted(assignment) => Some(Err(format!(
            "the word and the operands differ at {assignment:?}"
        ))),
    }
}

fn is_zero(expr: &E) -> bool {
    matches!(expr, E::BvConst { value: 0, .. })
}

/// `concat(0^k, x)` read as `zero_extend(x, k)`, recursively (the bit-serial
/// automaton reads extensions, not concatenations).
fn normalize(expr: &E) -> E {
    match expr {
        E::Concat { hi, lo, .. } if is_zero(hi) => normalize(lo).zero_ext(hi.bv_width()),
        E::Ite {
            cond,
            then_expr,
            else_expr,
        } => E::ite(normalize(cond), normalize(then_expr), normalize(else_expr)),
        E::Eq { lhs, rhs } => normalize(lhs).eq_expr(normalize(rhs)),
        E::Not { operand } => normalize(operand).not_expr(),
        E::And { lhs, rhs } => normalize(lhs).and_expr(normalize(rhs)),
        E::Or { lhs, rhs } => normalize(lhs).or_expr(normalize(rhs)),
        E::Extract {
            high, low, operand, ..
        } => normalize(operand).extract(*high, *low),
        E::ZeroExtend {
            operand,
            extra_bits,
            ..
        } => normalize(operand).zero_ext(*extra_bits),
        E::SignExtend {
            operand,
            extra_bits,
            ..
        } => normalize(operand).sign_ext(*extra_bits),
        E::BvAdd { lhs, rhs, .. } => normalize(lhs).bvadd(normalize(rhs)),
        E::BvAnd { lhs, rhs, .. } => normalize(lhs).bvand(normalize(rhs)),
        E::BvOr { lhs, rhs, .. } => normalize(lhs).bvor(normalize(rhs)),
        E::BvXor { lhs, rhs, .. } => normalize(lhs).bvxor(normalize(rhs)),
        E::BvSgt { lhs, rhs, .. } => normalize(lhs).bvsgt(normalize(rhs)),
        E::BvSge { lhs, rhs, .. } => normalize(lhs).bvsge(normalize(rhs)),
        E::BvSle { lhs, rhs, .. } => normalize(lhs).bvsle(normalize(rhs)),
        E::BvUgt { lhs, rhs, .. } => normalize(lhs).bvugt(normalize(rhs)),
        E::BvUge { lhs, rhs, .. } => normalize(lhs).bvuge(normalize(rhs)),
        E::BvUle { lhs, rhs, .. } => normalize(lhs).bvule(normalize(rhs)),
        _ => expr.clone(),
    }
}

fn is_bool(expr: &E) -> bool {
    matches!(
        expr,
        E::BoolConst(_)
            | E::Eq { .. }
            | E::Not { .. }
            | E::And { .. }
            | E::Or { .. }
            | E::BvSlt { .. }
            | E::BvSge { .. }
            | E::BvUge { .. }
            | E::BvSgt { .. }
            | E::BvSle { .. }
            | E::BvUlt { .. }
            | E::BvUgt { .. }
            | E::BvUle { .. }
    ) || matches!(expr, E::Ite { then_expr, .. } if is_bool(then_expr))
}

/// The Boolean `cond ? a : b`, spelled `(cond and a) or (not cond and b)`
/// (an `ite` of Booleans has no bit-vector sort to report).
fn choose(cond: &E, a: E, b: E) -> E {
    cond.clone()
        .and_expr(a)
        .or_expr(cond.clone().not_expr().and_expr(b))
}

/// `lhs == rhs` with every top-level selection between two bit-vector values
/// lifted into a Boolean case split over the two equalities.
fn lift_equality(lhs: &E, rhs: &E) -> E {
    if let E::Ite {
        cond,
        then_expr,
        else_expr,
    } = lhs
        && !is_bool(lhs)
    {
        return choose(
            cond,
            lift_equality(then_expr, rhs),
            lift_equality(else_expr, rhs),
        );
    }
    if let E::Ite {
        cond,
        then_expr,
        else_expr,
    } = rhs
        && !is_bool(rhs)
    {
        return choose(
            cond,
            lift_equality(lhs, then_expr),
            lift_equality(lhs, else_expr),
        );
    }
    lhs.clone().eq_expr(rhs.clone())
}

fn mentions_a_variable(expr: &E) -> bool {
    if matches!(expr, E::Var { .. }) {
        return true;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| found = found || mentions_a_variable(child));
    found
}

/// `expr` with every variable-free subterm evaluated to a constant (at most
/// 64 bits) and every `ite` on a constant condition replaced by its taken
/// branch; `None` for a node outside the parts' vocabulary.
fn fold(expr: &E) -> Option<E> {
    use crate::smt::EvalResult;
    if !mentions_a_variable(expr) {
        return match expr.try_eval(&crate::smt::EvalEnv::default()).ok()? {
            EvalResult::Bool(value) => Some(E::bool_const(value)),
            EvalResult::Bv(value) if expr.bv_width() <= 64 => {
                Some(E::bv_const(value, expr.bv_width()))
            }
            _ => None,
        };
    }
    Some(match expr {
        E::Var { .. } => expr.clone(),
        E::Ite {
            cond,
            then_expr,
            else_expr,
        } => match fold(cond)? {
            E::BoolConst(true) => fold(then_expr)?,
            E::BoolConst(false) => fold(else_expr)?,
            cond => E::ite(cond, fold(then_expr)?, fold(else_expr)?),
        },
        E::Extract {
            high, low, operand, ..
        } => fold(operand)?.extract(*high, *low),
        E::Concat { hi, lo, .. } => fold(hi)?.concat(fold(lo)?),
        E::ZeroExtend {
            operand,
            extra_bits,
            ..
        } => fold(operand)?.zero_ext(*extra_bits),
        E::SignExtend {
            operand,
            extra_bits,
            ..
        } => fold(operand)?.sign_ext(*extra_bits),
        E::BvAdd { lhs, rhs, .. } => fold(lhs)?.bvadd(fold(rhs)?),
        E::BvAnd { lhs, rhs, .. } => fold(lhs)?.bvand(fold(rhs)?),
        E::BvOr { lhs, rhs, .. } => fold(lhs)?.bvor(fold(rhs)?),
        E::BvXor { lhs, rhs, .. } => fold(lhs)?.bvxor(fold(rhs)?),
        E::Eq { lhs, rhs } => fold(lhs)?.eq_expr(fold(rhs)?),
        E::Not { operand } => fold(operand)?.not_expr(),
        E::And { lhs, rhs } => fold(lhs)?.and_expr(fold(rhs)?),
        E::Or { lhs, rhs } => fold(lhs)?.or_expr(fold(rhs)?),
        E::BvSgt { lhs, rhs, .. } => fold(lhs)?.bvsgt(fold(rhs)?),
        E::BvSge { lhs, rhs, .. } => fold(lhs)?.bvsge(fold(rhs)?),
        E::BvSle { lhs, rhs, .. } => fold(lhs)?.bvsle(fold(rhs)?),
        E::BvUgt { lhs, rhs, .. } => fold(lhs)?.bvugt(fold(rhs)?),
        E::BvUge { lhs, rhs, .. } => fold(lhs)?.bvuge(fold(rhs)?),
        E::BvUle { lhs, rhs, .. } => fold(lhs)?.bvule(fold(rhs)?),
        _ => return None,
    })
}

#[cfg(test)]
#[path = "aarch64_atomic_effect_tests.rs"]
mod tests;
