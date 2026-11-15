// trust-cg-verify/wasm_memarg_offset_proofs.rs - emitted memarg offsets against the trust-ir layout
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — §2.4.7 / §5.4.6
//            (memory instructions and their `memarg`: an alignment exponent and
//            an unsigned LEB128 static offset added to the address operand).
//
// WHAT THIS ADDS. The value-domain offset obligations
// (`wasm_value_domain::mem_load_offset_obligation` /
// `mem_store_offset_obligation`) state what a memarg offset MEANS over a
// symbolic offset: the access at `(base, off + skew)` is the trust-ir access
// at `base + off` exactly when `skew == 0`. Built with `skew = 0` they read no
// emitted byte, so they cannot tell whether the lowering CHOSE the right
// offset. This module supplies the skew from the emitted module: it takes a
// CAPTURED closed module whose functions read and write every field of a
// struct with deliberately irregular, nonzero trust-ir offsets, DECODES the
// opcode and memarg offset of every emitted load and store, binds each to the
// trust-ir access it lowers (in order, per function), and instantiates the
// offset obligation with the intended opcode, the EMITTED opcode and
// `skew = emitted offset - trust-ir layout offset`. A shifted field offset,
// or a slipped opcode, makes that obligation refute.
//
// THE INTENT is independent of the backend: the struct's field offsets are the
// ones the trust-ir declares (the bridge copies them from rustc's layout), and
// the opcode for a field type is the value domain's carrier rule (a narrow
// integer rides in an `i32`, loaded with the extension its signedness names).
//
// WHAT THIS DOES NOT ESTABLISH. It binds the accesses of the captured shapes —
// a field READ of a by-address struct parameter (`extractfield`) and the field
// WRITES that build a struct (`make_aggregate`) — for every load and store
// byte the lowerer selects. Other sites that emit a nonzero offset (enum tags
// and niches, lanes of nested aggregates, the high half of a 128-bit value,
// sret slots, parameter and return lanes) use the same emitters but are not in
// this corpus; their offsets rest on the lane differentials
// (`wasm_g1_lane_semantics`, `wasm_g3_lane_frames`). The captured bytes are
// kept fresh by `tests/support/wasm_memarg_live_emit.rs`, which recompiles the
// corpus through the live backend and requires byte identity.

//! Emitted memarg offsets of captured field accesses, bound to the trust-ir
//! layout offsets they must equal; and the no-wrap side condition of memarg
//! offset FOLDING ([`memarg_fold_obligation`]).

use trust_ir::{Inst, Module, Ty};

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, VerificationConfig, verify_by_evaluation_with_config,
};
use crate::smt::SmtExpr;
use crate::verify::VerificationResult;
use crate::wasm_abi_proofs::{Imm, decode_insts, decode_module};
use crate::wasm_semantics as w;
use crate::wasm_value_domain as vd;

/// The corpus: a struct with irregular nonzero field offsets, one field read
/// per load opcode the lowerer selects, and one struct build whose field
/// writes cover every store opcode it selects.
pub const MEMARG_FIELDS_TIR: &str = r#"; TrustIr text format v1
module "memarg_fields"
target "wasm32-unknown-unknown" 4 little

struct @F { : u8 @1, : i8 @3, : u16 @6, : i16 @10, : i32 @12, : i64 @16, : f32 @28, : f64 @32 } size=40 align=8 id=0

functy.0 = (struct.0) -> (u8)
functy.1 = (struct.0) -> (i8)
functy.2 = (struct.0) -> (u16)
functy.3 = (struct.0) -> (i16)
functy.4 = (struct.0) -> (i32)
functy.5 = (struct.0) -> (i64)
functy.6 = (struct.0) -> (f32)
functy.7 = (struct.0) -> (f64)
functy.8 = (ptr, u8, i8, u16, i16, i32, i64, f32, f64) -> ()

fn @get0(functy.0) {
bb0(%0: struct.0):
    %1 = extractfield u8 %0, 0
    ret %1
}

fn @get1(functy.1) {
bb0(%0: struct.0):
    %1 = extractfield i8 %0, 1
    ret %1
}

fn @get2(functy.2) {
bb0(%0: struct.0):
    %1 = extractfield u16 %0, 2
    ret %1
}

fn @get3(functy.3) {
bb0(%0: struct.0):
    %1 = extractfield i16 %0, 3
    ret %1
}

fn @get4(functy.4) {
bb0(%0: struct.0):
    %1 = extractfield i32 %0, 4
    ret %1
}

fn @get5(functy.5) {
bb0(%0: struct.0):
    %1 = extractfield i64 %0, 5
    ret %1
}

fn @get6(functy.6) {
bb0(%0: struct.0):
    %1 = extractfield f32 %0, 6
    ret %1
}

fn @get7(functy.7) {
bb0(%0: struct.0):
    %1 = extractfield f64 %0, 7
    ret %1
}

fn @put(functy.8) {
bb0(%0: ptr, %1: u8, %2: i8, %3: u16, %4: i16, %5: i32, %6: i64, %7: f32, %8: f64):
    %9 = make_aggregate struct.0 (%1, %2, %3, %4, %5, %6, %7, %8)
    store struct.0 %9, ptr %0
    ret
}
"#;

/// The closed module the live backend emits for [`MEMARG_FIELDS_TIR`].
pub const MEMARG_FIELDS_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x21, 0x05, 0x60, 0x01, 0x7f, 0x01, 0x7f,
    0x60, 0x01, 0x7f, 0x01, 0x7e, 0x60, 0x01, 0x7f, 0x01, 0x7d, 0x60, 0x01, 0x7f, 0x01, 0x7c, 0x60,
    0x09, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7f, 0x7e, 0x7d, 0x7c, 0x00, 0x03, 0x0a, 0x09, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x03, 0x01, 0x00, 0x01, 0x06, 0x08, 0x01, 0x7f,
    0x01, 0x41, 0x80, 0x80, 0x04, 0x0b, 0x07, 0x3f, 0x09, 0x04, 0x67, 0x65, 0x74, 0x30, 0x00, 0x00,
    0x04, 0x67, 0x65, 0x74, 0x31, 0x00, 0x01, 0x04, 0x67, 0x65, 0x74, 0x32, 0x00, 0x02, 0x04, 0x67,
    0x65, 0x74, 0x33, 0x00, 0x03, 0x04, 0x67, 0x65, 0x74, 0x34, 0x00, 0x04, 0x04, 0x67, 0x65, 0x74,
    0x35, 0x00, 0x05, 0x04, 0x67, 0x65, 0x74, 0x36, 0x00, 0x06, 0x04, 0x67, 0x65, 0x74, 0x37, 0x00,
    0x07, 0x03, 0x70, 0x75, 0x74, 0x00, 0x08, 0x0a, 0xb4, 0x01, 0x09, 0x07, 0x00, 0x20, 0x00, 0x2d,
    0x00, 0x01, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x2c, 0x00, 0x03, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x2f,
    0x01, 0x06, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x2e, 0x01, 0x0a, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x28,
    0x02, 0x0c, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x29, 0x03, 0x10, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x2a,
    0x02, 0x1c, 0x0b, 0x07, 0x00, 0x20, 0x00, 0x2b, 0x03, 0x20, 0x0b, 0x72, 0x01, 0x03, 0x7f, 0x20,
    0x01, 0x41, 0xff, 0x01, 0x71, 0x21, 0x01, 0x20, 0x02, 0xc0, 0x21, 0x02, 0x20, 0x03, 0x41, 0xff,
    0xff, 0x03, 0x71, 0x21, 0x03, 0x20, 0x04, 0xc1, 0x21, 0x04, 0x23, 0x00, 0x22, 0x0b, 0x41, 0x28,
    0x6b, 0x22, 0x0a, 0x24, 0x00, 0x20, 0x0a, 0x22, 0x09, 0x20, 0x01, 0x3a, 0x00, 0x01, 0x20, 0x09,
    0x20, 0x02, 0x3a, 0x00, 0x03, 0x20, 0x09, 0x20, 0x03, 0x3b, 0x01, 0x06, 0x20, 0x09, 0x20, 0x04,
    0x3b, 0x01, 0x0a, 0x20, 0x09, 0x20, 0x05, 0x36, 0x02, 0x0c, 0x20, 0x09, 0x20, 0x06, 0x37, 0x03,
    0x10, 0x20, 0x09, 0x20, 0x07, 0x38, 0x02, 0x1c, 0x20, 0x09, 0x20, 0x08, 0x39, 0x03, 0x20, 0x20,
    0x00, 0x20, 0x09, 0x41, 0x28, 0xfc, 0x0a, 0x00, 0x00, 0x20, 0x0b, 0x24, 0x00, 0x0b,
];

/// One emitted load or store bound to the trust-ir access it lowers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemargAccess {
    /// The defined-function ordinal it sits in.
    pub function: usize,
    /// The opcode byte the trust-ir field type calls for.
    pub intended_byte: u8,
    /// The trust-ir layout offset of the field.
    pub intended_offset: u32,
    /// The opcode byte decoded from the module.
    pub emitted_byte: u8,
    /// The memarg offset decoded from the module.
    pub emitted_offset: u32,
}

/// The load opcode byte for a field of type `ty`: a narrow integer is loaded
/// into its `i32` carrier with the extension its signedness names.
pub fn intended_load_byte(ty: &Ty) -> Option<u8> {
    Some(match ty {
        Ty::U8 => 0x2d,
        Ty::I8 => 0x2c,
        Ty::U16 => 0x2f,
        Ty::I16 => 0x2e,
        Ty::I32 | Ty::U32 => 0x28,
        Ty::I64 | Ty::U64 => 0x29,
        Ty::F32 => 0x2a,
        Ty::F64 => 0x2b,
        _ => return None,
    })
}

/// The store opcode byte for a field of type `ty`.
pub fn intended_store_byte(ty: &Ty) -> Option<u8> {
    Some(match ty {
        Ty::U8 | Ty::I8 => 0x3a,
        Ty::U16 | Ty::I16 => 0x3b,
        Ty::I32 | Ty::U32 => 0x36,
        Ty::I64 | Ty::U64 => 0x37,
        Ty::F32 => 0x38,
        Ty::F64 => 0x39,
        _ => return None,
    })
}

/// The `(opcode byte, layout offset)` of every memory access the trust-ir
/// `func` intends, in order. `Err` on any instruction outside the corpus
/// shapes (a field read of a struct entry parameter, a struct build, a struct
/// store — a `memory.copy` — and the return), so an unmodelled access can
/// never be silently unbound.
fn intended_accesses(module: &Module, func: &trust_ir::Function) -> Result<Vec<(u8, u32)>, String> {
    let entry = func
        .blocks
        .first()
        .ok_or_else(|| format!("`{}` has no blocks", func.name))?;
    let field = |ty: &Ty, k: usize| -> Result<(Ty, u32), String> {
        let Ty::Struct(sid) = ty else {
            return Err(format!("`{}`: {ty:?} is not a struct", func.name));
        };
        let def = module
            .struct_def(*sid)
            .ok_or_else(|| format!("`{}`: struct {sid:?} is not declared", func.name))?;
        let f = def
            .fields
            .get(k)
            .ok_or_else(|| format!("`{}`: struct {sid:?} has no field {k}", func.name))?;
        let off = f
            .offset
            .ok_or_else(|| format!("`{}`: field {k} declares no offset", func.name))?;
        let off = u32::try_from(off).map_err(|_| format!("`{}`: offset {off}", func.name))?;
        Ok((f.ty.clone(), off))
    };
    let mut out = Vec::new();
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::ExtractField {
                    ty,
                    aggregate,
                    field: k,
                } => {
                    let agg_ty = entry
                        .params
                        .iter()
                        .find(|(v, _)| v == aggregate)
                        .map(|(_, t)| t)
                        .ok_or_else(|| {
                            format!(
                                "`{}`: the field read is not of an entry parameter",
                                func.name
                            )
                        })?;
                    let (fty, off) = field(agg_ty, *k as usize)?;
                    if fty != *ty {
                        return Err(format!(
                            "`{}`: field {k} is {fty:?}, read as {ty:?}",
                            func.name
                        ));
                    }
                    let byte = intended_load_byte(&fty)
                        .ok_or_else(|| format!("`{}`: no load for {fty:?}", func.name))?;
                    out.push((byte, off));
                }
                Inst::MakeAggregate {
                    ty,
                    variant: None,
                    fields,
                } => {
                    for k in 0..fields.len() {
                        let (fty, off) = field(ty, k)?;
                        let byte = intended_store_byte(&fty)
                            .ok_or_else(|| format!("`{}`: no store for {fty:?}", func.name))?;
                        out.push((byte, off));
                    }
                }
                Inst::Store {
                    ty: Ty::Struct(_), ..
                }
                | Inst::Return { .. } => {}
                other => {
                    return Err(format!(
                        "`{}`: {other:?} is outside the corpus shapes",
                        func.name
                    ));
                }
            }
        }
    }
    Ok(out)
}

/// Bind every emitted load and store of the closed module `wasm` to the
/// trust-ir access of `tir` it lowers: per function, the k-th emitted access
/// is the k-th intended one. `Err` when the text does not parse, the module
/// does not decode, imports a function, or a function emits a different
/// NUMBER of accesses than it intends.
pub fn bind_memarg_accesses(tir: &str, wasm: &[u8]) -> Result<Vec<MemargAccess>, String> {
    let module = trust_ir::parser::parse_module(tir).map_err(|e| format!("{e:?}"))?;
    let dec = decode_module(wasm).map_err(|e| format!("{e:?}"))?;
    if dec.func_import_count() != 0 {
        return Err("the corpus module imports a function".to_string());
    }
    if dec.bodies.len() != module.functions.len() {
        return Err(format!(
            "{} code bodies for {} trust-ir functions",
            dec.bodies.len(),
            module.functions.len()
        ));
    }
    let mut out = Vec::new();
    for (ordinal, (func, body)) in module.functions.iter().zip(&dec.bodies).enumerate() {
        let intended = intended_accesses(&module, func)?;
        let insts = decode_insts(&body.code).map_err(|e| format!("`{}`: {e:?}", func.name))?;
        let emitted: Vec<(u8, u32)> = insts
            .iter()
            .filter_map(|i| match i.imm {
                Imm::Memarg { offset, .. } if (0x28..=0x3e).contains(&i.op) => Some((i.op, offset)),
                _ => None,
            })
            .collect();
        if emitted.len() != intended.len() {
            return Err(format!(
                "`{}` emits {} memory access(es) for {} intended: {emitted:02x?} vs {intended:02x?}",
                func.name,
                emitted.len(),
                intended.len()
            ));
        }
        for ((ib, io), (eb, eo)) in intended.into_iter().zip(emitted) {
            out.push(MemargAccess {
                function: ordinal,
                intended_byte: ib,
                intended_offset: io,
                emitted_byte: eb,
                emitted_offset: eo,
            });
        }
    }
    Ok(out)
}

/// The offset obligation for one bound access: the intended opcode against
/// the EMITTED one, at `skew = emitted offset - layout offset`. `None` when no
/// offset obligation relates the two opcodes (a load bound to a store, or a
/// different value width), which the credit counts as a failure.
pub fn memarg_offset_obligation(access: &MemargAccess) -> Option<ProofObligation> {
    let skew = access.emitted_offset.wrapping_sub(access.intended_offset);
    if w::decode_mem_op(access.intended_byte)?.is_load() {
        vd::mem_load_offset_obligation(access.intended_byte, access.emitted_byte, skew)
    } else {
        vd::mem_store_offset_obligation(access.intended_byte, access.emitted_byte, skew)
    }
}

/// The memarg offset folding lemma at address width `w` (32 for wasm32; a
/// smaller width is the same statement, small enough to enumerate): for an
/// address `b`, a constant `c` and a memarg offset `o`, all `w`-bit, the
/// effective address of an access through `b + c` (the `w`-bit, wrapping
/// `i32.add`) at offset `o` equals the effective address through `b` at
/// offset `o + c`, PROVIDED `b + c` and `o + c` do not exceed `2^w - 1`.
/// Effective addresses are `2w`-bit sums, as the specification computes
/// them without wrapping.
///
/// The emission pass folds `b + c` into the offset only under that side
/// condition: `wasm_local_tv` accepts a folded access only when the fact of
/// `b` bounds `b + c` below `2^32` (and a memarg offset is at most
/// `2^32 - 1` by its encoding). With `drop_no_wrap` the first precondition
/// is omitted, the negative control: the statement is then false (a wrapped
/// `b + c` reaches a low address the folded access does not).
pub fn memarg_fold_obligation(w: u32, drop_no_wrap: bool) -> ProofObligation {
    let (b, c, o) = (
        SmtExpr::var("b", w),
        SmtExpr::var("c", w),
        SmtExpr::var("o", w),
    );
    let wide = |e: SmtExpr| e.zero_ext(w);
    let max = SmtExpr::bv_const(if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }, 2 * w);
    let through_sum = wide(b.clone().bvadd(c.clone())).bvadd(wide(o.clone()));
    let folded = wide(b.clone()).bvadd(wide(o.clone().bvadd(c.clone())));
    let mut preconditions = vec![wide(o).bvadd(wide(c.clone())).bvule(max.clone())];
    if !drop_no_wrap {
        preconditions.insert(0, wide(b).bvadd(wide(c)).bvule(max));
    }
    ProofObligation {
        name: format!("wasm memarg offset folding at width {w}"),
        trust_ir_expr: through_sum,
        aarch64_expr: folded,
        inputs: vec![("b".into(), w), ("c".into(), w), ("o".into(), w)],
        preconditions,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

/// The memarg offset folding lemma under a GEP's no-wrap PREMISE, at
/// address width `w`: for a base `b`, an index `i` and a memarg offset `o`,
/// all `w`-bit, and the element size `scale`, the effective address of an
/// access through `b + i * scale` (the lane's wrapping `i32.mul` and
/// `i32.add`) at offset `o` equals the effective address through `b` at
/// offset `o + i * scale`, PROVIDED the trust-ir GEP is defined (its exact
/// byte offset `i * scale` and result `b + i * scale` are at most `2^w - 1`:
/// trust-ir WS2.16, `wasm_nowrap_premise`) and the folded offset fits its
/// `u32` encoding. Arithmetic on the premise is `2w`-bit, where neither the
/// product nor the sum of two `w`-bit values wraps.
///
/// This is what `wasm_local_tv` relies on when a premise lets it absorb a
/// constant addend whatever bounds `b`. With `drop_premise` the GEP's
/// definedness is omitted, the negative control: the statement is then false
/// (a wrapped address reaches a low address the folded access does not).
pub fn memarg_gep_fold_obligation(w: u32, scale: u64, drop_premise: bool) -> ProofObligation {
    let (b, i, o) = (
        SmtExpr::var("b", w),
        SmtExpr::var("i", w),
        SmtExpr::var("o", w),
    );
    let wide = |e: SmtExpr| e.zero_ext(w);
    let max = SmtExpr::bv_const(if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }, 2 * w);
    let scale_w = SmtExpr::bv_const(scale & if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }, w);
    // The lane's addend: `i * scale` in wrapping `w`-bit arithmetic.
    let addend = i.clone().bvmul(scale_w);
    let through_sum = wide(b.clone().bvadd(addend.clone())).bvadd(wide(o.clone()));
    let folded = wide(b.clone()).bvadd(wide(o.clone().bvadd(addend.clone())));
    // The GEP's exact byte offset, at `2w` bits.
    let exact = wide(i).bvmul(SmtExpr::bv_const(scale, 2 * w));
    let mut preconditions = vec![wide(o).bvadd(wide(addend)).bvule(max.clone())];
    if !drop_premise {
        preconditions.insert(0, exact.clone().bvule(max.clone()));
        preconditions.insert(1, wide(b).bvadd(exact).bvule(max));
    }
    ProofObligation {
        name: format!("wasm memarg offset folding under a GEP premise at width {w}, scale {scale}"),
        trust_ir_expr: through_sum,
        aarch64_expr: folded,
        inputs: vec![("b".into(), w), ("i".into(), w), ("o".into(), w)],
        preconditions,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

/// A deliberately wrong lowering of the corpus, applied to the bound
/// accesses: the negative controls every credited byte must refute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemargControl {
    /// Every nonzero emitted offset moved by `+4` (a field read or written 4
    /// bytes off).
    ShiftedOffset,
    /// Every access emitted at offset 0 instead of its field's offset (the
    /// field offset dropped from the memarg).
    DroppedOffset,
}

impl MemargControl {
    /// Every control.
    pub const ALL: [MemargControl; 2] =
        [MemargControl::ShiftedOffset, MemargControl::DroppedOffset];

    /// Apply the control to one bound access.
    pub fn apply(self, mut access: MemargAccess) -> MemargAccess {
        match self {
            MemargControl::ShiftedOffset if access.emitted_offset != 0 => {
                access.emitted_offset = access.emitted_offset.wrapping_add(4);
            }
            MemargControl::ShiftedOffset => {}
            MemargControl::DroppedOffset => access.emitted_offset = 0,
        }
        access
    }
}

/// Whether `access` is credited evidence: its opcode and offset are the
/// intended ones, and its offset obligation is reconstructed and discharges
/// `Valid`.
fn access_holds(access: &MemargAccess, config: &VerificationConfig) -> Result<(), String> {
    let ob = memarg_offset_obligation(access).ok_or_else(|| {
        format!(
            "no offset obligation relates the emitted 0x{:02x} to the intended 0x{:02x}",
            access.emitted_byte, access.intended_byte
        )
    })?;
    if !ob.is_reconstructed() {
        return Err(format!("{} is not reconstructed", ob.name));
    }
    match verify_by_evaluation_with_config(&ob, config) {
        VerificationResult::Valid => {}
        other => return Err(format!("{}: {other:?}", ob.name)),
    }
    if access.emitted_byte != access.intended_byte
        || access.emitted_offset != access.intended_offset
    {
        return Err(format!(
            "emitted 0x{:02x} offset {} for intended 0x{:02x} offset {}",
            access.emitted_byte,
            access.emitted_offset,
            access.intended_byte,
            access.intended_offset
        ));
    }
    Ok(())
}

/// Why load/store byte `byte` is NOT credited with a bound emitted offset over
/// the corpus `(tir, wasm)` — empty when it is.
///
/// It credits only when the corpus binds, contains at least one access whose
/// intended opcode is `byte` at a NONZERO layout offset, every such access
/// holds ([`memarg_offset_obligation`] discharges `Valid` at the decoded skew,
/// and the decoded opcode and offset equal the intended ones), and every
/// [`MemargControl`] makes some such access fail.
pub fn memarg_offset_credit_failures(
    byte: u8,
    tir: &str,
    wasm: &[u8],
    config: &VerificationConfig,
) -> Vec<String> {
    let accesses = match bind_memarg_accesses(tir, wasm) {
        Ok(a) => a,
        Err(why) => return vec![format!("the corpus does not bind: {why}")],
    };
    let mine: Vec<MemargAccess> = accesses
        .into_iter()
        .filter(|a| a.intended_byte == byte && a.intended_offset != 0)
        .collect();
    if mine.is_empty() {
        return vec![format!(
            "0x{byte:02x}: the corpus has no access at a nonzero layout offset"
        )];
    }
    let mut failures = Vec::new();
    for a in &mine {
        if let Err(why) = access_holds(a, config) {
            failures.push(format!("0x{byte:02x} in function {}: {why}", a.function));
        }
    }
    for control in MemargControl::ALL {
        if mine
            .iter()
            .all(|a| access_holds(&control.apply(*a), config).is_ok())
        {
            failures.push(format!(
                "0x{byte:02x}: the {control:?} control does not refute"
            ));
        }
    }
    failures
}

/// The credit hook over the captured corpus: `true` exactly when
/// [`memarg_offset_credit_failures`] is empty.
pub fn memarg_offset_discharges_valid(byte: u8, config: &VerificationConfig) -> bool {
    memarg_offset_credit_failures(byte, MEMARG_FIELDS_TIR, MEMARG_FIELDS_WASM, config).is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The folding lemma holds over every 4-bit address, constant and
    /// offset (enumerated), and by sampling at 32 bits; without its no-wrap
    /// precondition it is refuted.
    #[test]
    fn memarg_folding_is_sound_exactly_under_its_no_wrap_condition() {
        let cfg = VerificationConfig::default();
        assert!(
            matches!(
                verify_by_evaluation_with_config(&memarg_fold_obligation(4, false), &cfg),
                VerificationResult::Valid
            ),
            "the 4-bit lemma"
        );
        assert!(
            matches!(
                verify_by_evaluation_with_config(&memarg_fold_obligation(32, false), &cfg),
                VerificationResult::Valid
            ),
            "the 32-bit lemma"
        );
        for w in [4, 32] {
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&memarg_fold_obligation(w, true), &cfg),
                    VerificationResult::Invalid { .. }
                ),
                "the control at width {w}"
            );
        }
        // At 32 bits the solver, where it answers: never a counterexample to
        // the lemma, never a certificate for the control.
        let ay = crate::ay_bridge::AYConfig::default().with_timeout(30_000);
        match crate::ay_bridge::verify_with_ay(&memarg_fold_obligation(32, false), &ay) {
            crate::ay_bridge::AYResult::CounterExample(cex) => {
                panic!("the solver refuted the folding lemma: {cex:?}")
            }
            other => eprintln!("32-bit folding lemma, solver: {other}"),
        }
        assert!(!matches!(
            crate::ay_bridge::verify_with_ay(&memarg_fold_obligation(32, true), &ay),
            crate::ay_bridge::AYResult::Verified
        ));
    }

    /// The premised folding lemma holds over every 4-bit base, index and
    /// offset for several element sizes (enumerated), and by sampling at 32
    /// bits; without the GEP's definedness it is refuted at each size.
    #[test]
    fn memarg_folding_under_a_gep_premise_is_sound_exactly_under_it() {
        let cfg = VerificationConfig::default();
        for scale in [1u64, 2, 3, 8] {
            assert!(
                matches!(
                    verify_by_evaluation_with_config(
                        &memarg_gep_fold_obligation(4, scale, false),
                        &cfg
                    ),
                    VerificationResult::Valid
                ),
                "the 4-bit lemma, scale {scale}"
            );
            assert!(
                matches!(
                    verify_by_evaluation_with_config(
                        &memarg_gep_fold_obligation(4, scale, true),
                        &cfg
                    ),
                    VerificationResult::Invalid { .. }
                ),
                "the 4-bit control, scale {scale}"
            );
        }
        for scale in [1u64, 4, 16] {
            assert!(
                matches!(
                    verify_by_evaluation_with_config(
                        &memarg_gep_fold_obligation(32, scale, false),
                        &cfg
                    ),
                    VerificationResult::Valid
                ),
                "the 32-bit lemma, scale {scale}"
            );
        }
        // The unpremised lemma's control and the premised one's agree: the
        // premise is exactly the no-wrap condition at scale 1.
        assert!(matches!(
            verify_by_evaluation_with_config(&memarg_gep_fold_obligation(32, 1, true), &cfg),
            VerificationResult::Invalid { .. }
        ));
    }

    /// The corpus binds, covers every load and store byte the lowerer selects
    /// at a nonzero offset, and credits each; a shifted offset refutes the
    /// bound obligation itself.
    #[test]
    fn the_corpus_binds_every_selected_access_byte() {
        let cfg = VerificationConfig::default();
        let accesses = bind_memarg_accesses(MEMARG_FIELDS_TIR, MEMARG_FIELDS_WASM).expect("binds");
        for &byte in vd::WASM_LOAD_BYTES.iter().chain(vd::WASM_STORE_BYTES) {
            if vd::value_domain_unselected(byte).is_some() {
                continue;
            }
            assert_eq!(
                memarg_offset_credit_failures(byte, MEMARG_FIELDS_TIR, MEMARG_FIELDS_WASM, &cfg),
                Vec::<String>::new(),
                "0x{byte:02x}"
            );
        }
        for a in &accesses {
            let shifted = MemargControl::ShiftedOffset.apply(*a);
            let ob = memarg_offset_obligation(&shifted).expect("builds");
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&ob, &cfg),
                    VerificationResult::Invalid { .. }
                ),
                "{a:?}: {}",
                ob.name
            );
        }
    }
}
