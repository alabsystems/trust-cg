// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Reference: Arm DDI 0487 (L.a), C7.2 LD1 (multiple structures) and ST1
//            (multiple structures), shared decode and operation
//            "LDST_MULT" (one register, post-index by immediate); and
//            crates/trust-cg-codegen/src/aarch64/encoding_neon.rs
//            `encode_ld1_post_imm` / `encode_st1_post_imm`.

//! Operand-bound AArch64 NEON `LD1`/`ST1` FORM theorems (one register,
//! immediate post-index): the formal credit route for the `NeonLd1Post` and
//! `NeonSt1Post` rows (ledger `L04-P1`).
//!
//! # Why this module exists
//!
//! The word-bound memory-effect decomposition
//! ([`crate::aarch64_memory_effect`], `L04-P6`) states each emitted `LD1`/`ST1`
//! per instruction and is decided exactly in process, and its model agrees
//! with silicon; neither is credit. The Formal-only bound-memory rule
//! ([`crate::bound_memory_authority`]) credits a memory row only on a
//! committed, independently replayed certificate of the row's FORM theorem,
//! and none existed for these instructions. This module supplies one theorem
//! per architectural form — `(LD1|ST1) x arrangement`, the seven arrangements
//! the encoder accepts (`8B`, `16B`, `4H`, `8H`, `2S`, `4S`, `2D`) — and a
//! binder that maps a concrete emitted instruction to exactly one form.
//!
//! # The theorem
//!
//! For ALL base values, ALL transfer register values and ALL memory
//! contents:
//!
//! * `LD1 {Vt.<T>}, [Xn|SP], #<bytes>`: every byte `j` of the 128-bit `Vt`
//!   after the instruction (the loaded bytes, and zero above a 64-bit
//!   transfer), and `Xn` after the instruction;
//! * `ST1 {Vt.<T>}, [Xn|SP], #<bytes>`: the byte at every address `q` after
//!   the instruction (the stored bytes, every other byte unchanged), and `Xn`.
//!
//! # The two sides
//!
//! * **Machine side**, from the Arm pseudocode of the encoded fields: with
//!   `datasize = Q ? 128 : 64`, `ebytes = 1 << size` and
//!   `elements = datasize / (8 * ebytes)`, element `e` is transferred
//!   between `Elem[V[t], e, esize]` and `Mem[address + e * ebytes, ebytes]`
//!   (little-endian), and the base is written back as `address + offs` where
//!   `offs` is the accumulated `elements * ebytes`. The element loop is stated
//!   in closed form over a symbolic byte position: register byte `j` belongs
//!   to element `j >> size` at byte `j & (ebytes - 1)` of it; a 64-bit load
//!   writes zeros above bit 63 (`V[t] = ZeroExtend(rval)`).
//! * **Intent side**, from the machine-IR operands `[Vt, Xn|SP, #arrangement]`
//!   alone: a load is `LDR Dt|Qt, [Xn], #bytes` — the little-endian scalar of
//!   the `bytes` bytes at the base, zero-extended to 128 bits, then byte `j` —
//!   and a store is a chain of `bytes` single-byte stores of the register's
//!   bytes in order; the base advances by the literal transfer size.
//!
//! The sides share no address, element or byte-extraction subexpression (the
//! machine side splits the position into element and byte-in-element and
//! re-multiplies, the intent side indexes bytes directly), so the theorem is
//! not X == X and every [`NeonStructureMutation`] refutes on the grid
//! ([`grid_counterexample`]).
//!
//! # Memory encoding
//!
//! As in [`crate::aarch64_pair_memory_forms`]: a store is observed at a free
//! query address `q` over a free original byte `m`, so the frame condition is
//! inside the theorem; a load reads a single-point memory
//! `M(x) = ite(x == p, c, d)`, which is complete for these equalities (each
//! observed byte is one read or the constant zero). A free selector `sel`
//! projects the observation (`sel == 0`) and the written-back base.
//!
//! # Authority and claim boundary
//!
//! A form theorem is credited only by a committed certificate of its exact
//! query in `verdict_db/neon_memory_certs/` that the vendored `drat-trim`
//! replays in process; the walk additionally requires the row's word-bound
//! memory-effect decomposition to have held exactly (rule clause 2) and the
//! judged word to decode to the bound form (clause 3,
//! [`decode_neon_structure_word`]). Instruction semantics only: no claim
//! that the memory is initialized, mapped or aligned, about ordering, or
//! about the single-copy atomicity of the element accesses. Little-endian
//! data (`SCTLR_EL1.E0E = 0`) is assumed, as for every memory form.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, SpecialReg};

/// Direction of the transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NeonStructureTransfer {
    /// `LD1`.
    Load,
    /// `ST1`.
    Store,
}

/// One architectural `LD1`/`ST1` (one register, immediate post-index) form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NeonStructureForm {
    /// Load or store.
    pub transfer: NeonStructureTransfer,
    /// `Q`: a 128-bit transfer.
    pub q: bool,
    /// `size`: log2 of the element bytes.
    pub size: u32,
}

const fn form(transfer: NeonStructureTransfer, q: bool, size: u32) -> NeonStructureForm {
    NeonStructureForm { transfer, q, size }
}

use NeonStructureTransfer::{Load as LD1, Store as ST1};

/// Every form the encoder accepts, with its unique lowercase query: the
/// arrangement selectors `0..=6` of `trust-cg-codegen` (`8B`, `16B`, `4H`,
/// `8H`, `2S`, `4S`, `2D`; the `1D` arrangement is never selected).
pub const NEON_STRUCTURE_FORMS: [(NeonStructureForm, &str); 14] = [
    (form(LD1, false, 0), "neonmem[ld1.post.8b]"),
    (form(LD1, true, 0), "neonmem[ld1.post.16b]"),
    (form(LD1, false, 1), "neonmem[ld1.post.4h]"),
    (form(LD1, true, 1), "neonmem[ld1.post.8h]"),
    (form(LD1, false, 2), "neonmem[ld1.post.2s]"),
    (form(LD1, true, 2), "neonmem[ld1.post.4s]"),
    (form(LD1, true, 3), "neonmem[ld1.post.2d]"),
    (form(ST1, false, 0), "neonmem[st1.post.8b]"),
    (form(ST1, true, 0), "neonmem[st1.post.16b]"),
    (form(ST1, false, 1), "neonmem[st1.post.4h]"),
    (form(ST1, true, 1), "neonmem[st1.post.8h]"),
    (form(ST1, false, 2), "neonmem[st1.post.2s]"),
    (form(ST1, true, 2), "neonmem[st1.post.4s]"),
    (form(ST1, true, 3), "neonmem[st1.post.2d]"),
];

impl NeonStructureForm {
    /// The unique form query, or `None` for a form outside the table.
    pub fn query(&self) -> Option<&'static str> {
        NEON_STRUCTURE_FORMS
            .iter()
            .find(|(candidate, _)| candidate == self)
            .map(|(_, query)| *query)
    }

    /// Bytes transferred (and the post-index increment).
    pub fn bytes(&self) -> u32 {
        if self.q { 16 } else { 8 }
    }

    /// Bytes per element.
    pub fn element_bytes(&self) -> u32 {
        1 << self.size
    }

    /// Elements transferred.
    pub fn elements(&self) -> u32 {
        self.bytes() / self.element_bytes()
    }

    /// The arrangement selector the machine IR carries.
    pub fn selector(&self) -> i64 {
        match (self.size, self.q) {
            (3, _) => 6,
            (size, q) => i64::from(size * 2 + u32::from(q)),
        }
    }

    /// The Arm arrangement spelling.
    pub fn arrangement(&self) -> &'static str {
        const NAMES: [&str; 7] = ["8B", "16B", "4H", "8H", "2S", "4S", "2D"];
        NAMES[self.selector() as usize]
    }

    /// The opcode of this form.
    pub fn opcode(&self) -> AArch64Opcode {
        match self.transfer {
            LD1 => AArch64Opcode::NeonLd1Post,
            ST1 => AArch64Opcode::NeonSt1Post,
        }
    }

    /// Form theorem name. Its lowercase form contains [`Self::query`].
    pub fn proof_name(&self) -> String {
        let query = self.query().expect("proof_name requires a table form");
        let tag = &query["neonmem".len()..];
        let (mnemonic, intent, effect) = match self.transfer {
            LD1 => (
                "LD1",
                if self.q { "LDR Qt" } else { "LDR Dt" },
                "Vt zero above the transfer",
            ),
            ST1 => (
                "ST1",
                if self.q { "STR Qt" } else { "STR Dt" },
                "every other byte unchanged",
            ),
        };
        format!(
            "NeonMem{tag}: {mnemonic} {{Vt.{}}}, [Xn|SP], #{} == {intent}, [Xn], #{}; {effect} \
             (element loop, operand-bound)",
            self.arrangement(),
            self.bytes(),
            self.bytes()
        )
    }
}

/// The forms an opcode can be emitted in, or `None` for another opcode.
pub fn neon_opcode_forms(opcode: AArch64Opcode) -> Option<Vec<NeonStructureForm>> {
    let transfer = match opcode {
        AArch64Opcode::NeonLd1Post => LD1,
        AArch64Opcode::NeonSt1Post => ST1,
        _ => return None,
    };
    Some(
        NEON_STRUCTURE_FORMS
            .iter()
            .map(|(form, _)| *form)
            .filter(|form| form.transfer == transfer)
            .collect(),
    )
}

/// True for the two `LD1`/`ST1` post-index opcodes.
pub fn is_neon_structure_opcode(opcode: AArch64Opcode) -> bool {
    neon_opcode_forms(opcode).is_some()
}

// ---------------------------------------------------------------------------
// Obligation construction
// ---------------------------------------------------------------------------

/// A deliberate defect injected into the MACHINE side only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NeonStructureMutation {
    /// The faithful machine semantics.
    None,
    /// Elements transferred in reverse order.
    ElementOrderReversed,
    /// The bytes of each element transferred big-endian.
    BigEndianElements,
    /// A 64-bit load leaves the register's upper half as memory instead of
    /// zero.
    NoZeroUpper,
    /// No base writeback.
    NoWriteback,
    /// The base advances by one element instead of the transfer.
    WritebackByElement,
    /// Access at the written-back base (pre-index).
    AccessAtWriteback,
    /// A store writes one byte past the transfer.
    ExtraStoredByte,
}

impl NeonStructureMutation {
    /// Every defect the refutation controls exercise.
    pub const DEFECTS: [NeonStructureMutation; 7] = [
        Self::ElementOrderReversed,
        Self::BigEndianElements,
        Self::NoZeroUpper,
        Self::NoWriteback,
        Self::WritebackByElement,
        Self::AccessAtWriteback,
        Self::ExtraStoredByte,
    ];

    /// Whether the defect changes the meaning of `form`.
    pub fn applies_to(self, form: &NeonStructureForm) -> bool {
        match self {
            Self::None => true,
            Self::BigEndianElements => form.size > 0,
            Self::NoZeroUpper => form.transfer == LD1 && !form.q,
            Self::ExtraStoredByte => form.transfer == ST1,
            _ => true,
        }
    }
}

fn c64(value: u64) -> SmtExpr {
    SmtExpr::bv_const(value, 64)
}

/// Register byte `index` of `(lo, hi)` by a variable shift (machine side).
fn machine_register_byte(lo: &SmtExpr, hi: Option<&SmtExpr>, index: SmtExpr) -> SmtExpr {
    let low = lo.clone().bvlshr(index.clone().bvshl(c64(3))).extract(7, 0);
    match hi {
        None => low,
        Some(hi) => SmtExpr::ite(
            index.clone().bvult(c64(8)),
            low,
            hi.clone()
                .bvlshr(index.bvsub(c64(8)).bvshl(c64(3)))
                .extract(7, 0),
        ),
    }
}

/// Register byte `i` (a constant) as a fixed `extract` (intent side).
fn intent_register_byte(lo: &SmtExpr, hi: Option<&SmtExpr>, i: u32) -> SmtExpr {
    let limb = if i < 8 {
        lo.clone()
    } else {
        hi.expect("a byte above 7 requires the high limb").clone()
    };
    let bit = (i % 8) * 8;
    limb.extract(bit + 7, bit)
}

/// Build the obligation for `form` with the given machine-side `mutation`;
/// `None` for a form outside the table or a mutation that does not apply.
pub fn proof_neon_structure_form_with_mutation(
    form: &NeonStructureForm,
    mutation: NeonStructureMutation,
) -> Option<ProofObligation> {
    form.query()?;
    if !mutation.applies_to(form) {
        return None;
    }
    let bytes = u64::from(form.bytes());
    let ebytes = u64::from(form.element_bytes());
    let elements = u64::from(form.elements());
    let size = u64::from(form.size);
    let base = SmtExpr::var("neon_base", 64);
    let sel = SmtExpr::var("neon_sel", 8);
    let mut inputs = vec![("neon_base".to_string(), 64), ("neon_sel".to_string(), 8)];
    let mut preconditions = Vec::new();
    let sel_is = |value: u64| sel.clone().eq_expr(SmtExpr::bv_const(value, 8));

    // Machine: offs accumulates ebytes per element, so after the loop it is
    // elements * ebytes; address = X[n]; X[n] = address + offs.
    let offs = c64(elements).bvmul(c64(ebytes));
    let address = if mutation == NeonStructureMutation::AccessAtWriteback {
        base.clone().bvadd(offs.clone())
    } else {
        base.clone()
    };
    let machine_base_after = match mutation {
        NeonStructureMutation::NoWriteback => base.clone(),
        NeonStructureMutation::WritebackByElement => base.clone().bvadd(c64(ebytes)),
        // A pre-index access writes back the address it used.
        NeonStructureMutation::AccessAtWriteback => address.clone(),
        _ => base.clone().bvadd(offs),
    };
    let intent_base_after = base.clone().bvadd(c64(bytes));
    // Position `pos` (a 64-bit byte index into the transfer) to the byte the
    // element loop places there: element `pos >> size`, byte `pos & (ebytes-1)`
    // of it, at memory offset `element * ebytes + byte`.
    let element_position = |pos: SmtExpr| {
        let element = pos.clone().bvlshr(c64(size));
        let within = pos.bvand(c64(ebytes - 1));
        let element = if mutation == NeonStructureMutation::ElementOrderReversed {
            c64(elements - 1).bvsub(element)
        } else {
            element
        };
        let within = if mutation == NeonStructureMutation::BigEndianElements {
            c64(ebytes - 1).bvsub(within)
        } else {
            within
        };
        element.bvshl(c64(size)).bvadd(within)
    };

    let (intent, machine) = match form.transfer {
        NeonStructureTransfer::Load => {
            let p = SmtExpr::var("neon_p", 64);
            let c = SmtExpr::var("neon_c", 8);
            let d = SmtExpr::var("neon_d", 8);
            let j = SmtExpr::var("neon_j", 8);
            for (name, width) in [("neon_p", 64), ("neon_c", 8), ("neon_d", 8), ("neon_j", 8)] {
                inputs.push((name.to_string(), width));
            }
            preconditions.push(j.clone().bvult(SmtExpr::bv_const(16, 8)));
            let memory =
                |address: SmtExpr| SmtExpr::ite(address.eq_expr(p.clone()), c.clone(), d.clone());
            let jz = j.clone().zero_ext(56);

            // Machine: Elem[rval, e, esize] = Mem[address + e*ebytes, ebytes];
            // V[t] = ZeroExtend(rval, 128).
            let read = memory(address.clone().bvadd(element_position(jz.clone())));
            let within_transfer = j.clone().bvult(SmtExpr::bv_const(bytes, 8));
            let machine_byte = if mutation == NeonStructureMutation::NoZeroUpper {
                read
            } else {
                SmtExpr::ite(within_transfer, read, SmtExpr::bv_const(0, 8))
            };

            // Intent: the little-endian scalar of the transfer, zero-extended,
            // then byte j.
            let assemble = |from: u64, count: u64| {
                let mut value = memory(base.clone().bvadd(c64(from)));
                for k in 1..count {
                    value = memory(base.clone().bvadd(c64(from + k))).concat(value);
                }
                value
            };
            let lo = assemble(0, 8);
            let hi = if form.q { assemble(8, 8) } else { c64(0) };
            let intent_byte = SmtExpr::ite(
                jz.clone().bvult(c64(8)),
                lo.bvlshr(jz.clone().bvshl(c64(3))).extract(7, 0),
                hi.bvlshr(jz.bvsub(c64(8)).bvshl(c64(3))).extract(7, 0),
            );
            (
                SmtExpr::ite(sel_is(0), intent_byte.zero_ext(56), intent_base_after),
                SmtExpr::ite(sel_is(0), machine_byte.zero_ext(56), machine_base_after),
            )
        }
        NeonStructureTransfer::Store => {
            let lo = SmtExpr::var("neon_v_lo", 64);
            inputs.push(("neon_v_lo".to_string(), 64));
            let hi = form.q.then(|| {
                inputs.push(("neon_v_hi".to_string(), 64));
                SmtExpr::var("neon_v_hi", 64)
            });
            let q = SmtExpr::var("neon_q", 64);
            let m = SmtExpr::var("neon_m", 8);
            inputs.push(("neon_q".to_string(), 64));
            inputs.push(("neon_m".to_string(), 8));

            // Machine: Mem[address + e*ebytes, ebytes] = Elem[V[t], e, esize]
            // for every element: the byte at q is the register byte at the
            // position q - address names, when inside the transfer.
            let rel = q.clone().bvsub(address.clone());
            let span = if mutation == NeonStructureMutation::ExtraStoredByte {
                bytes + 1
            } else {
                bytes
            };
            let machine_byte = SmtExpr::ite(
                rel.clone().bvult(c64(span)),
                machine_register_byte(&lo, hi.as_ref(), element_position(rel)),
                m.clone(),
            );

            // Intent: STR Dt|Qt as `bytes` single-byte stores, in order.
            let mut intent_byte = m;
            for i in 0..form.bytes() {
                intent_byte = SmtExpr::ite(
                    q.clone().eq_expr(base.clone().bvadd(c64(u64::from(i)))),
                    intent_register_byte(&lo, hi.as_ref(), i),
                    intent_byte,
                );
            }
            (
                SmtExpr::ite(sel_is(0), intent_byte.zero_ext(56), intent_base_after),
                SmtExpr::ite(sel_is(0), machine_byte.zero_ext(56), machine_base_after),
            )
        }
    };
    let name = if mutation == NeonStructureMutation::None {
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

/// The faithful obligation for `form`.
pub fn proof_neon_structure_form(form: &NeonStructureForm) -> Option<ProofObligation> {
    proof_neon_structure_form_with_mutation(form, NeonStructureMutation::None)
}

/// All 14 faithful form obligations, in [`NEON_STRUCTURE_FORMS`] order.
pub fn all_neon_structure_form_proofs() -> Vec<ProofObligation> {
    NEON_STRUCTURE_FORMS
        .iter()
        .map(|(form, _)| proof_neon_structure_form(form).expect("table forms are legal"))
        .collect()
}

// ---------------------------------------------------------------------------
// Grid refutation
// ---------------------------------------------------------------------------

fn grid_eval(expr: &SmtExpr, env: &crate::smt::EvalEnv) -> crate::smt::EvalResult {
    expr.try_eval(env)
        .expect("NEON structure obligation must evaluate")
}

/// Deterministic structured grid around the base and the written-back base:
/// every transfer byte, its neighbours and a wrapping base. Returns the first
/// disagreeing point. `None` is NOT evidence that a theorem holds (only a
/// replayed certificate is): it is the in-process search every machine defect
/// must not survive.
pub fn grid_counterexample(ob: &ProofObligation, form: &NeonStructureForm) -> Option<String> {
    let bytes = i64::from(form.bytes());
    for base in [0x0000_7fff_f000_1000u64, 0, u64::MAX - 5] {
        let probes: Vec<u64> = (-3..(2 * bytes + 4))
            .map(|delta| base.wrapping_add(delta as u64))
            .collect();
        for &probe in &probes {
            for sel in [0u64, 1] {
                let js: Vec<u64> = match form.transfer {
                    LD1 => (0..16).collect(),
                    ST1 => vec![0],
                };
                for j in js {
                    let mut env = crate::smt::EvalEnv::default();
                    env.insert("neon_base".into(), base);
                    env.insert("neon_sel".into(), sel);
                    env.insert("neon_p".into(), probe);
                    env.insert("neon_c".into(), 0x5a);
                    env.insert("neon_d".into(), 0xc3);
                    env.insert("neon_j".into(), j);
                    env.insert("neon_v_lo".into(), 0x0807_0605_0403_0201);
                    env.insert("neon_v_hi".into(), 0x100f_0e0d_0c0b_0a09);
                    env.insert("neon_q".into(), probe);
                    env.insert("neon_m".into(), 0xaa);
                    if !ob
                        .preconditions
                        .iter()
                        .all(|p| grid_eval(p, &env).as_bool())
                    {
                        continue;
                    }
                    let intent = grid_eval(&ob.trust_ir_expr, &env);
                    let machine = grid_eval(&ob.aarch64_expr, &env);
                    if intent != machine {
                        return Some(format!(
                            "base={base:#x} probe={probe:#x} sel={sel} j={j}: intent={intent:?} \
                             machine={machine:?}"
                        ));
                    }
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Instruction binding and word decoding
// ---------------------------------------------------------------------------

/// A concrete `LD1`/`ST1` instruction bound to exactly one form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeonStructureBinding {
    /// The form whose theorem this instruction instantiates.
    pub form: NeonStructureForm,
    /// `Rt` field (the vector register number).
    pub rt_field: u32,
    /// `Rn` field (31 is SP).
    pub base_field: u32,
}

impl NeonStructureBinding {
    /// The unique form query of the bound form.
    pub fn query(&self) -> &'static str {
        self.form
            .query()
            .expect("a binding only ever carries a table form")
    }
}

/// Bind a concrete `NeonLd1Post`/`NeonSt1Post` to its form, or explain the
/// refusal. Re-implements the admission independently of the encoder and of
/// the memory-effect lane: operands `[Vt, Xn|SP, #selector]`, `selector` in
/// `0..=6`, `Vt` an allocated `Q` register (or a `D` register for a 64-bit
/// arrangement), the base an allocated X register or SP.
pub fn bind_neon_structure_instruction(inst: &MachInst) -> Result<NeonStructureBinding, String> {
    let transfer = match inst.opcode {
        AArch64Opcode::NeonLd1Post => LD1,
        AArch64Opcode::NeonSt1Post => ST1,
        other => return Err(format!("{other:?} is not a NEON LD1/ST1 post-index opcode")),
    };
    let [vt, base, MachOperand::Imm(selector)] = inst.operands.as_slice() else {
        return Err("LD1/ST1 post-index requires exactly [Vt, Xn|SP, #arrangement]".into());
    };
    let (q, size) = match *selector {
        0 => (false, 0),
        1 => (true, 0),
        2 => (false, 1),
        3 => (true, 1),
        4 => (false, 2),
        5 => (true, 2),
        6 => (true, 3),
        other => return Err(format!("arrangement selector {other} is not in 0..=6")),
    };
    let rt_field = match vt {
        MachOperand::PReg(reg) => match reg.encoding() {
            e @ 64..=95 => u32::from(e - 64),
            e @ 96..=127 if !q => u32::from(e - 96),
            e => {
                return Err(format!(
                    "the transfer register (encoding {e}) is not a Q register, or a D register \
                     of a 64-bit arrangement"
                ));
            }
        },
        other => {
            return Err(format!(
                "the transfer {other:?} is not an allocated register"
            ));
        }
    };
    let base_field = match base {
        MachOperand::PReg(reg) if reg.encoding() <= 31 => u32::from(reg.encoding()),
        MachOperand::Special(SpecialReg::SP) => 31,
        other => return Err(format!("the base {other:?} is not an X register or SP")),
    };
    let form = NeonStructureForm { transfer, q, size };
    form.query()
        .ok_or_else(|| format!("{form:?} is not a table form"))?;
    Ok(NeonStructureBinding {
        form,
        rt_field,
        base_field,
    })
}

/// Decode an "Advanced SIMD load/store multiple structures (post-indexed)"
/// word, `0 | Q | 0011001 | L | 0 | Rm | opcode | size | Rn | Rt`, as one
/// register with an immediate post-index (`opcode = 0111`, `Rm = 11111`), to
/// the binding of its form; `None` for any other word or a form outside the
/// table (`1D`).
pub fn decode_neon_structure_word(word: u32) -> Option<NeonStructureBinding> {
    let field = |hi: u32, lo: u32| (word >> lo) & ((1 << (hi - lo + 1)) - 1);
    if field(31, 31) != 0
        || field(29, 23) != 0b001_1001
        || field(21, 21) != 0
        || field(20, 16) != 0b1_1111
        || field(15, 12) != 0b0111
    {
        return None;
    }
    let form = NeonStructureForm {
        transfer: if field(22, 22) == 1 { LD1 } else { ST1 },
        q: field(30, 30) == 1,
        size: field(11, 10),
    };
    form.query()?;
    Some(NeonStructureBinding {
        form,
        rt_field: field(4, 0),
        base_field: field(9, 5),
    })
}

/// A representative instruction of `form`: `[V3 (or D3), SP, #selector]`.
pub fn representative_neon_instruction(form: &NeonStructureForm, base_sp: bool) -> MachInst {
    use trust_cg_ir::PReg;
    let vt = if form.q {
        PReg::new(64 + 3)
    } else {
        PReg::new(96 + 3)
    };
    let base = if base_sp {
        MachOperand::Special(SpecialReg::SP)
    } else {
        MachOperand::PReg(PReg::new(9))
    };
    MachInst::new(
        form.opcode(),
        vec![
            MachOperand::PReg(vt),
            base,
            MachOperand::Imm(form.selector()),
        ],
    )
}

// ---------------------------------------------------------------------------
// Certificates
// ---------------------------------------------------------------------------

/// One form theorem and its certificate filename.
#[derive(Debug, Clone)]
pub struct CertifiableNeonQuery {
    /// Certificate filename in `verdict_db/neon_memory_certs/`.
    pub file: String,
    /// The form theorem's name.
    pub form: String,
    /// The form theorem.
    pub obligation: ProofObligation,
}

/// Every form theorem with its certificate filename, in table order.
pub fn certifiable_neon_queries() -> Vec<CertifiableNeonQuery> {
    NEON_STRUCTURE_FORMS
        .iter()
        .map(|(form, query)| {
            let tag = query
                .trim_start_matches("neonmem[")
                .trim_end_matches(']')
                .replace('.', "_");
            let obligation = proof_neon_structure_form(form).expect("table forms are legal");
            CertifiableNeonQuery {
                file: format!("neonmem_{tag}.lratcert"),
                form: obligation.name.clone(),
                obligation,
            }
        })
        .collect()
}

/// A deliberately WRONG theorem wearing a faithful form's name (elements in
/// reverse order). The certificate consumer must refuse it: its exact query
/// is not the faithful one.
pub fn representative_wrong_neon_theorem() -> ProofObligation {
    let (form, _) = NEON_STRUCTURE_FORMS[5];
    let mut wrong =
        proof_neon_structure_form_with_mutation(&form, NeonStructureMutation::ElementOrderReversed)
            .expect("ElementOrderReversed applies to every form");
    wrong.name = form.proof_name();
    wrong
}

#[cfg(test)]
#[path = "aarch64_neon_structure_forms_tests.rs"]
mod tests;
