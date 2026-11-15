// declared_struct_layout.rs — the byte path READS the producer's offsets
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The producer stores rustc's real, reorder-aware field offsets in
//! [`trust_ir::FieldDef::offset`] (`trust-thir-lower/src/lib.rs:9392-9395`, from
//! `tcx.layout_of(..)` then `layout.fields.offset(i).bytes()`). The byte path
//! used to ignore them and RECOMPUTE the layout as declaration-ordered natural
//! C ([`trust_cg_lower::types::Type::offset_of`]), so for `#[repr(Rust)]` — the
//! repr where rustc is free to reorder fields by alignment — it addressed
//! fields at a different place than the producer specified.
//!
//! THE ORACLE IS STOCK RUSTC — `rustc 1.97.0 (2d8144b78 2026-07-07)`,
//! `size_of` / `align_of` / `offset_of!`:
//!
//! ```text
//!                                                          rustc            recomputed
//! struct TypeCheckId { expr_hash: u64, env_hash: u64,   expr@0  hash@8      hash@0  env@8
//!                      mode_hash: u64, expr: Arc<Expr> }  env@16 mode@24     mode@16 expr@24
//!                                                          size 32 align 8   size 32 align 8
//! struct AHasher { buffer: u64, pad: u64,               extra@0 buffer@16   buffer@0 pad@8
//!                  extra_keys: [u64; 2] }                 pad@24, size 32    extra@16, size 32
//! #[repr(C)] struct CMixed { a: u8, b: u64, c: u16 }    a@0 b@8 c@16        IDENTICAL
//! #[repr(packed)] struct P { a: u8, b: u64 }            a@0 b@1, size 9     packed authority
//! #[repr(packed(2))] struct P2 { a: u8, b: u64, c: u16 } a@10 b@0 c@8       REFUSED (packed)
//! #[repr(C)] struct OuterC { h: u8, inner: P }          h@0 inner@1, 10/1   REFUSED (totals)
//! ```
//!
//! Every test below reads the EMITTED opcode stream out of the public
//! [`translate_function`], not the layout helpers in isolation: the question is
//! what address the compiler computes, not what a predicate thinks it computes.
//!
//! # What is pinned here, and in which direction
//!
//! * **Fixed** — a `#[repr(Rust)]` struct whose producer layout is coherent and
//!   whose totals already match the recomputation is addressed at rustc's
//!   offsets, through all four field-addressing paths (`ExtractField`,
//!   `InsertField`, the aggregate-constant fill, and the multi-index `GEP`).
//! * **Unchanged, byte-identical** — a struct with NO declared layout, and a
//!   struct whose declared offsets are what the recomputation already produced.
//!   Those keep the `StructGep` encoding, so nothing about the 952-of-6,051
//!   corpus structs that record no layout moves.
//! * **Refused, and named (WS7.8, F-031)** — a COMPLETE declared layout the
//!   byte path cannot honour: incoherent producer data, a field whose emitted
//!   image runs off the end or into a sibling, totals that diverge from the
//!   recomputation, and a `#[repr(packed(N))]` struct that authority P lays out
//!   differently. These used to keep the recomputation SILENTLY — a different
//!   layout than rustc's, with no diagnostic. Lowering now fails with
//!   `AdapterError::DeclaredStructLayoutNotEmittable`, naming the gate. A
//!   packed struct that authority P lays out exactly as declared still
//!   compiles; nothing is overridden there.
//! * **Refused where it is held by value** — a function that reserves
//!   storage for, passes, or moves a value CONTAINING such a struct (the
//!   `Alloca` slot, the ABI classifier and SSA moves read the natural-C
//!   carrier, not rustc's size) is refused even if it never addresses a field;
//!   one that only passes a pointer to it still lowers.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::declared_layout::DeclaredLayoutGate;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FieldDef, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, StructDef, StructId,
    StructRepr, Ty, ValueId,
};

// ---------------------------------------------------------------------------
// Fixture
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// A field WITH a producer offset — rustc's own.
fn f(name: &str, ty: Ty, offset: u64) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset: Some(offset),
    }
}

/// A field with NO producer offset — the 15.7% of the corpus whose layout
/// query declined.
fn f_none(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset: None,
    }
}

fn sdef(
    id: u32,
    name: &str,
    repr: StructRepr,
    fields: Vec<FieldDef>,
    totals: Option<(u64, u64)>,
) -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(id),
        name: name.to_string(),
        fields,
        size: totals.map(|(s, _)| s),
        align: totals.map(|(_, a)| a),
        repr,
    }
}

fn st(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

const TYPE_CHECK_ID: u32 = 0;
const NO_LAYOUT: u32 = 1;
const C_MIXED: u32 = 2;
const PACKED_P: u32 = 3;
const PACKED2_REORDERED: u32 = 4;
const OUTER_C: u32 = 5;
const AHASHER: u32 = 6;
const ARR_OF_IDS: u32 = 7;
const INCOHERENT: u32 = 8;
const FIELD_OFF_THE_END: u32 = 9;
const MIXED: u32 = 10;
const OVER_ALIGNED: u32 = 11;
const PACKED_OUTER_ARR: u32 = 12;
const C07_OVERLAP: u32 = 13;

/// `types` table index of `P2` (the reordered packed struct).
const TY_P2: u32 = 2;
/// `types` table index of `Mixed` (the reorder the totals gate refuses).
const TY_MIXED: u32 = 3;

/// Every fixture, with the rustc measurement that justifies its numbers.
fn structs() -> Vec<StructDef> {
    vec![
        // rustc: expr@0 expr_hash@8 env_hash@16 mode_hash@24, size 32 align 8.
        // Recomputed: 0 / 8 / 16 / 24 in declaration order — ALL FOUR differ.
        sdef(
            TYPE_CHECK_ID,
            "TypeCheckId",
            StructRepr::Rust,
            vec![
                f("expr_hash", Ty::U64, 8),
                f("env_hash", Ty::U64, 16),
                f("mode_hash", Ty::U64, 24),
                f("expr", Ty::Ptr, 0),
            ],
            Some((32, 8)),
        ),
        // The same shape with the layout query declined — THE FALLBACK.
        sdef(
            NO_LAYOUT,
            "TypeCheckIdNoLayout",
            StructRepr::Rust,
            vec![
                f_none("expr_hash", Ty::U64),
                f_none("env_hash", Ty::U64),
                f_none("mode_hash", Ty::U64),
                f_none("expr", Ty::Ptr),
            ],
            None,
        ),
        // rustc: a@0 b@8 c@16, size 24 align 8 — IDENTICAL to the
        // recomputation, so the `StructGep` encoding is kept.
        sdef(
            C_MIXED,
            "CMixed",
            StructRepr::C,
            vec![f("a", Ty::U8, 0), f("b", Ty::U64, 8), f("c", Ty::U16, 16)],
            Some((24, 8)),
        ),
        // rustc: a@0 b@1, size 9 align 1. Packed structs keep authority P.
        sdef(
            PACKED_P,
            "P",
            StructRepr::Packed(1),
            vec![f("a", Ty::U8, 0), f("b", Ty::U64, 1)],
            Some((9, 1)),
        ),
        // rustc: a@10 b@0 c@8, size 12 align 2 — `packed(N>1)` without
        // `repr(C)` REORDERS. Authority P is declaration-ordered (a@0 b@2
        // c@10), so it cannot reproduce this: REFUSED at the packed gate.
        sdef(
            PACKED2_REORDERED,
            "P2",
            StructRepr::Packed(2),
            vec![f("a", Ty::U8, 10), f("b", Ty::U64, 0), f("c", Ty::U16, 8)],
            Some((12, 2)),
        ),
        // rustc: h@0 inner@1, size 10 align 1. The recomputation sizes this
        // 24/8 because the interior `P` is measured natural-C, so it is
        // REFUSED at the totals gate.
        sdef(
            OUTER_C,
            "OuterC",
            StructRepr::C,
            vec![f("h", Ty::U8, 0), f("inner", st(PACKED_P), 1)],
            Some((10, 1)),
        ),
        // rustc: extra_keys@0 buffer@16 pad@24, size 32 align 8.
        sdef(
            AHASHER,
            "AHasher",
            StructRepr::Rust,
            vec![
                f("buffer", Ty::U64, 16),
                f("pad", Ty::U64, 24),
                f("extra_keys", Ty::Array(trust_ir::TyId::new(0), 2), 0),
            ],
            Some((32, 8)),
        ),
        // An ARRAY of a reordered struct: the container is emittable (the
        // array's natural image, 2 * 32, fits at its declared offset) and the
        // ELEMENTS are addressed at rustc's field offsets.
        sdef(
            ARR_OF_IDS,
            "ArrOfIds",
            StructRepr::Rust,
            vec![
                f("arr", Ty::Array(trust_ir::TyId::new(1), 2), 0),
                f("tail", Ty::U8, 64),
            ],
            Some((72, 8)),
        ),
        // INCOHERENT producer data: a `u64` parked at 4 in a non-packed struct.
        // rustc never mints this; emitting it would be an undeclared unaligned
        // access, so it is declined.
        sdef(
            INCOHERENT,
            "Incoherent",
            StructRepr::Rust,
            vec![f("a", Ty::U64, 0), f("b", Ty::U64, 4)],
            Some((16, 8)),
        ),
        // CONTAINMENT failure: `b`'s 8-byte image runs to 24 in a 16-byte
        // object.
        sdef(
            FIELD_OFF_THE_END,
            "OffTheEnd",
            StructRepr::Rust,
            vec![f("a", Ty::U64, 0), f("b", Ty::U64, 16)],
            Some((16, 8)),
        ),
        // rustc: `Mixed { a: u8, b: u64, c: u16 }` is a@10 b@0 c@8, size 16
        // align 8. Recomputed: a@0 b@8 c@16, size 24 — every field moves AND
        // the object grows, so the totals gate declines it.
        sdef(
            MIXED,
            "Mixed",
            StructRepr::Rust,
            vec![f("a", Ty::U8, 10), f("b", Ty::U64, 0), f("c", Ty::U16, 8)],
            Some((16, 8)),
        ),
        // rustc: `#[repr(align(16))] struct Over { a: u8 }` is size 16 align
        // 16. Recomputed: 1/1.
        sdef(
            OVER_ALIGNED,
            "Over",
            StructRepr::Rust,
            vec![f("a", Ty::U8, 0)],
            Some((16, 16)),
        ),
        // `#[repr(packed)] { arr: [P2; 2], t: u8 }` with NO declared layout, so
        // authority P lays it out — and has to measure `[P2; 2]` to place `t`.
        // rustc: arr@0 t@24, size 25. Measuring the array needs `P2`'s layout,
        // which is refused, so nothing about this struct can be placed.
        sdef(
            PACKED_OUTER_ARR,
            "PackedOuterArr",
            StructRepr::Packed(1),
            vec![
                f_none("arr", Ty::Array(trust_ir::TyId::new(TY_P2), 2)),
                f_none("t", Ty::U8),
            ],
            None,
        ),
        // The proof program's `verify/c07_union_and_struct_overlap` repro
        // (`tests/repro.rs`, `pair_module(_, 0, 8)`): `#[repr(C)] Pair { a:
        // u32@0, b: f32@0 }`, size 8 align 4. Both fields claim bytes 0..4 —
        // no struct rustc mints (the trust-ir validator half of F-031, WS2.3,
        // refuses it upstream). The totals equal natural C's, so only the
        // overlap gate catches it, and trust-cg used to lay it out natural-C
        // (`a@0 b@4`) without a word.
        sdef(
            C07_OVERLAP,
            "Pair",
            StructRepr::C,
            vec![f("a", Ty::U32, 0), f("b", Ty::F32, 0)],
            Some((8, 4)),
        ),
    ]
}

/// The module `types` table: entry 0 is `u64` (the `AHasher` array element),
/// entry 1 is `TypeCheckId` (the `ArrOfIds` array element), entry 2 is `P2`
/// and entry 3 is `Mixed` (arrays of refused structs).
fn types_table() -> Vec<Ty> {
    vec![Ty::U64, st(TYPE_CHECK_ID), st(PACKED2_REORDERED), st(MIXED)]
}

fn module_with_body(params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> TrustIrModule {
    let mut module = TrustIrModule::new("declared_layout");
    module.structs = structs();
    module.types = types_table();
    let fty_id: FuncTyId = module
        .add_func_type(FuncTy {
            params: params.iter().map(|(_, t)| t.clone()).collect(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params,
        body,
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Lowering must FAIL with the named WS7.8 refusal for struct `id` at `gate`
/// — not "any error", and not a lowering that silently recomputed.
fn assert_refused(module: &TrustIrModule, id: u32, gate: DeclaredLayoutGate) {
    let func = module.functions.first().expect("one function");
    match trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed()) {
        Err(AdapterError::DeclaredStructLayoutNotEmittable {
            struct_id,
            gate: failed,
            ..
        }) => {
            assert_eq!(struct_id, id, "the refusal must name the struct");
            assert_eq!(failed, gate, "the refusal must name the gate");
        }
        Err(other) => panic!("expected DeclaredStructLayoutNotEmittable at `{gate}`, got {other}"),
        Ok(_) => panic!(
            "struct {id} carries a complete declared layout the byte path cannot emit; \
             lowering it must be refused at the `{gate}` gate, not recomputed"
        ),
    }
}

fn opcodes(module: &TrustIrModule) -> Vec<Opcode> {
    let func = module.functions.first().expect("one function");
    let (lir_func, _proofs) =
        trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
            .expect("adapter must lower the fixture");
    let entry = lir_func.entry_block;
    lir_func.blocks[&entry]
        .instructions
        .iter()
        .map(|i| i.opcode.clone())
        .collect()
}

/// Every `Iconst` immediate in the emitted stream, in order.
fn iconsts(opcodes: &[Opcode]) -> Vec<i64> {
    opcodes
        .iter()
        .filter_map(|o| match o {
            Opcode::Iconst { imm, .. } => Some(*imm),
            _ => None,
        })
        .collect()
}

/// Every `StructGep` field index in the emitted stream, in order.
fn struct_geps(opcodes: &[Opcode]) -> Vec<u32> {
    opcodes
        .iter()
        .filter_map(|o| match o {
            Opcode::StructGep { field_index, .. } => Some(*field_index),
            _ => None,
        })
        .collect()
}

/// Read field `index` of a value of type `ty`.
fn extract(ty: Ty, index: u32) -> Vec<InstrNode> {
    vec![
        InstrNode::new(Inst::ExtractField {
            ty,
            aggregate: v(0),
            field: index,
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ]
}

// ---------------------------------------------------------------------------
// FIXED — the repr(Rust) reorder, as EMITTED CODE
// ---------------------------------------------------------------------------

/// THE HEADLINE. `TypeCheckId`'s `Arc` is rotated to the front by rustc, so
/// every one of its four fields sits somewhere the declaration-ordered
/// recomputation does not put it.
///
/// Reading `expr_hash` must compute `base + 8`. Before the repair the adapter
/// emitted `StructGep { field_index: 0 }`, which the ISel resolves with
/// natural-C `Type::offset_of` (`isel.rs`, `x86_64_isel.rs`) to `base + 0` —
/// seven-and-a-half bytes of the `Arc` pointer, read as a hash.
#[test]
fn reading_a_reordered_field_uses_rustcs_offset_not_the_recomputation() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(TYPE_CHECK_ID), 0));
    let ops = opcodes(&module);
    assert_eq!(
        iconsts(&ops),
        vec![8],
        "rustc puts `expr_hash` at 8; the recomputation puts it at 0"
    );
    assert!(
        struct_geps(&ops).is_empty(),
        "`StructGep` can only ever express the recomputed offset, so it must not be emitted \
         for a field the producer places elsewhere: {ops:?}"
    );
}

/// The mirror: `expr`, declared LAST but placed FIRST, must be addressed at 0
/// where the recomputation says 24.
#[test]
fn the_field_rustc_rotates_to_the_front_is_addressed_at_zero() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(TYPE_CHECK_ID), 3));
    assert_eq!(
        iconsts(&opcodes(&module)),
        vec![0],
        "rustc puts `expr` at 0; the recomputation puts it at 24"
    );
}

/// All four fields, in one place, against the oracle.
#[test]
fn every_field_of_the_reordered_struct_matches_rustc() {
    // (field index, rustc offset, recomputed offset)
    for (index, rustc, recomputed) in [(0u32, 8i64, 0), (1, 16, 8), (2, 24, 16), (3, 0, 24)] {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(TYPE_CHECK_ID), index));
        assert_ne!(rustc, recomputed, "the fixture must actually diverge");
        assert_eq!(
            iconsts(&opcodes(&module)),
            vec![rustc],
            "field {index} belongs at {rustc}, not the recomputed {recomputed}"
        );
    }
}

/// `AHasher` — the shape measured end-to-end on the real `ahash` corpus module,
/// where `extra_keys: [u64; 2]` is rotated to offset 0 and the two `u64`s
/// follow it. An ARRAY field placed by rustc, not by the recomputation.
#[test]
fn an_array_field_rustc_rotates_to_the_front_is_addressed_at_zero() {
    for (index, rustc) in [(0u32, 16i64), (1, 24), (2, 0)] {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(AHASHER), index));
        assert_eq!(
            iconsts(&opcodes(&module)),
            vec![rustc],
            "AHasher field {index} belongs at {rustc}"
        );
    }
}

/// WRITING a reordered field, not only reading it. `InsertField` is the other
/// half of the miscompile: a store to `expr_hash` at the recomputed 0 lands on
/// the `Arc` pointer.
#[test]
fn writing_a_reordered_field_uses_rustcs_offset() {
    // The VALUE form (WS7.1): the base is a `TypeCheckId` value, not a pointer
    // — the store form is invalid trust-ir and refused by name.
    let module = module_with_body(
        vec![(v(0), st(TYPE_CHECK_ID)), (v(1), Ty::U64)],
        vec![
            InstrNode::new(Inst::InsertField {
                ty: st(TYPE_CHECK_ID),
                aggregate: v(0),
                field: 0,
                value: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let ops = opcodes(&module);
    // 32 = the declared extent the result's private copy receives from the
    // base; 8 = rustc's offset of `expr_hash`, where the field is written.
    assert_eq!(iconsts(&ops), vec![32, 8]);
    assert!(struct_geps(&ops).is_empty(), "{ops:?}");
    assert!(
        ops.iter()
            .any(|o| matches!(o, Opcode::Store { align: None, .. })),
        "a DECLARED offset is properly aligned for its own field type, so the store must not \
         be marked possibly-unaligned the way a packed one is: {ops:?}"
    );
}

/// The aggregate-CONSTANT path — the one with no `InsertField` chain behind it
/// to overwrite a misplaced byte, so a wrong offset here is a wrong value that
/// nothing masks.
#[test]
fn an_aggregate_constant_writes_each_field_at_rustcs_offset() {
    let module = module_with_body(
        vec![],
        vec![
            InstrNode::new(Inst::Const {
                ty: st(TYPE_CHECK_ID),
                value: Constant::Aggregate(vec![
                    Constant::Int(1),
                    Constant::Int(2),
                    Constant::Int(3),
                    Constant::Int(4),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let ops = opcodes(&module);
    // Each field emits `Iconst <offset>` for the address and `Iconst <value>`
    // for the datum, in that order.
    assert_eq!(
        iconsts(&ops),
        vec![8, 1, 16, 2, 24, 3, 0, 4],
        "the constant must be written at rustc's offsets 8/16/24/0, not the recomputed \
         0/8/16/24: {ops:?}"
    );
    assert!(struct_geps(&ops).is_empty(), "{ops:?}");
}

/// Array indexing and field projection are distinct TrustIR operations.
/// `arr[i].expr_hash` first strides the whole element, then ExtractField
/// uses the producer's declared field offset.
#[test]
fn a_field_of_an_indexed_array_element_uses_rustcs_field_offset() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: st(TYPE_CHECK_ID),
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Load {
                ty: st(TYPE_CHECK_ID),
                ptr: v(2),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U64,
                aggregate: v(3),
                field: 0,
            })
            .with_result(v(4)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let ops = opcodes(&module);
    assert!(
        iconsts(&ops).contains(&32),
        "array element stride must be 32: {ops:?}"
    );
    assert!(
        iconsts(&ops).contains(&8),
        "expr_hash must be loaded at offset 8: {ops:?}"
    );
    assert!(struct_geps(&ops).is_empty(), "{ops:?}");
}

/// An ARRAY of a reordered struct, addressed through the container. The
/// container's own offsets are what the recomputation already produces, so it
/// keeps `StructGep`; the ELEMENT's fields are the ones that moved.
#[test]
fn an_array_of_reordered_structs_keeps_the_container_encoding() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(ARR_OF_IDS), 0));
    let ops = opcodes(&module);
    assert_eq!(
        struct_geps(&ops),
        vec![0],
        "`arr@0` and `tail@64` are exactly what natural C computes, so the existing encoding \
         is kept and the emitted stream is byte-identical: {ops:?}"
    );
    assert!(iconsts(&ops).is_empty(), "{ops:?}");
}

// ---------------------------------------------------------------------------
// UNCHANGED — the named fallback, byte-identical
// ---------------------------------------------------------------------------

/// THE FALLBACK. (c) MEASURED over a 69-module corpus: 952 of 6,051 struct
/// defs (15.7%), carrying 1,811 fields, record no layout at all. Those must be
/// addressed exactly as before — `StructGep`, resolved by the recomputation.
#[test]
fn a_struct_with_no_declared_layout_is_addressed_exactly_as_before() {
    for index in 0..4u32 {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(NO_LAYOUT), index));
        let ops = opcodes(&module);
        assert_eq!(
            struct_geps(&ops),
            vec![index],
            "no producer layout means the recomputation, expressed as `StructGep`: {ops:?}"
        );
        assert!(
            iconsts(&ops).is_empty(),
            "no explicit offset arithmetic may appear: {ops:?}"
        );
    }
}

/// A `#[repr(C)]` struct: rustc lays it out in declaration order, so the
/// declared offsets and the recomputation COINCIDE. The declared layout still
/// wins — it just happens to name the same address — and the existing
/// `StructGep` encoding is kept so the emitted stream does not move.
#[test]
fn a_repr_c_struct_keeps_the_struct_gep_encoding() {
    for index in 0..3u32 {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(C_MIXED), index));
        let ops = opcodes(&module);
        assert_eq!(struct_geps(&ops), vec![index], "{ops:?}");
        assert!(iconsts(&ops).is_empty(), "{ops:?}");
    }
}

// ---------------------------------------------------------------------------
// DECLINED, AND NAMED — what this repair does NOT do
// ---------------------------------------------------------------------------

/// `#[repr(packed(N))]` keeps authority P, unconditionally.
///
/// trust-cg lays a packed struct out two ways — `packed_struct_layout` for its
/// field addresses and copy extents, natural C for its slots and ABI — and
/// `layout_refusal` declines to certify one for exactly that reason. Letting
/// the declared layout in would close the OFFSET half of that split while
/// leaving the SIZE half open, and would hand the array stride back to natural
/// C whenever the declared totals happened to match it.
#[test]
fn a_packed_struct_still_uses_the_packed_authority() {
    for (index, packed_offset) in [(0u32, 0i64), (1, 1)] {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(PACKED_P), index));
        let ops = opcodes(&module);
        assert_eq!(iconsts(&ops), vec![packed_offset], "{ops:?}");
        assert!(
            ops.iter()
                .any(|o| matches!(o, Opcode::Load { align: Some(1), .. })),
            "a packed field is still loaded as possibly-unaligned: {ops:?}"
        );
    }
}

/// REFUSED (WS7.8; was "STILL OPEN" and silently mis-addressed).
/// `#[repr(packed(2))] { a: u8, b: u64, c: u16 }` is `a@10 b@0 c@8` in rustc —
/// `packed(N)` with `N > 1` and no `repr(C)` REORDERS — and authority P is a
/// declaration-ordered walk (`a@0 b@2 c@10`) that structurally cannot express
/// that. Every field used to be read at P's address; lowering now refuses.
#[test]
fn a_reordered_packed_struct_is_refused_not_misaddressed() {
    for index in 0..3u32 {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(PACKED2_REORDERED), index));
        assert_refused(&module, PACKED2_REORDERED, DeclaredLayoutGate::Packed);
    }
}

/// REFUSED (WS7.8; was "STILL OPEN" and silently recomputed).
/// `#[repr(C)] OuterC { h: u8, inner: P }` is 10 bytes with `inner@1` in
/// rustc, because `P`'s own alignment is 1. The recomputation measures the
/// interior `P` natural-C and sizes the container 24/8 with `inner@8`, so the
/// declared totals diverge — and reading `inner` at 8 is reading rustc's
/// bytes 8.. of a 10-byte object.
#[test]
fn a_non_packed_struct_containing_a_packed_one_is_refused() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(OUTER_C), 1));
    assert_refused(&module, OUTER_C, DeclaredLayoutGate::Totals);
}

/// REFUSED. INCOHERENT producer data: a `u64` at offset 4 in a non-packed
/// struct is not a layout rustc mints; emitting it would turn a wrong-address
/// defect into an undeclared unaligned access, and recomputing it would
/// silently address `b` at 8.
#[test]
fn an_incoherently_aligned_declared_offset_is_refused() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(INCOHERENT), 1));
    assert_refused(&module, INCOHERENT, DeclaredLayoutGate::FieldAlignment);
}

/// REFUSED. A declared offset whose field's emitted image runs off the end of
/// the declared object — honouring it would be an out-of-bounds write, and
/// recomputing it would silently address `b` at 8.
#[test]
fn a_declared_offset_that_runs_off_the_end_is_refused() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(FIELD_OFF_THE_END), 1));
    assert_refused(&module, FIELD_OFF_THE_END, DeclaredLayoutGate::Containment);
}

/// ADVERSARIAL — the reorder case. `Mixed` is `a@10 b@0 c@8`, 16/8, in rustc
/// and `a@0 b@8 c@16`, 24/8, recomputed. Every field access is refused; none
/// is emitted at a recomputed address.
#[test]
fn the_mixed_reorder_is_refused_at_every_field() {
    for index in 0..3u32 {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(MIXED), index));
        assert_refused(&module, MIXED, DeclaredLayoutGate::Totals);
    }
}

/// ADVERSARIAL — `#[repr(align(16))]`. rustc says 16/16, the recomputation
/// 1/1: the field address even agrees (`a@0`), but the object the byte path
/// would copy, stride and pass is a different object. Refused.
#[test]
fn a_repr_align_16_struct_is_refused() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(OVER_ALIGNED), 0));
    assert_refused(&module, OVER_ALIGNED, DeclaredLayoutGate::Totals);
}

/// The refusal is scoped to the struct that carries the unemittable layout: a
/// function in the SAME module that addresses only an agreeing struct still
/// lowers, at rustc's offset.
#[test]
fn an_agreeing_struct_beside_a_refused_one_still_lowers() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(TYPE_CHECK_ID), 0));
    assert!(module.structs.iter().any(|s| s.id == StructId::new(MIXED)));
    assert_eq!(iconsts(&opcodes(&module)), vec![8]);
}

/// The recomputation is still reachable and still correct for the shapes it
/// owns: `Type::offset_of` is unchanged by this repair.
#[test]
fn the_recomputation_itself_is_unchanged() {
    let natural = Type::Struct(vec![Type::I64, Type::I64, Type::I64, Type::I64]);
    assert_eq!(natural.offset_of(0), Some(0));
    assert_eq!(natural.offset_of(3), Some(24));
    assert_eq!(natural.bytes(), 32);
    assert_eq!(natural.align(), 8);
}

// ---------------------------------------------------------------------------
// REFUSED THROUGH AN ARRAY — the element's refusal is not swallowed
// ---------------------------------------------------------------------------
//
// An array's extent and stride are its ELEMENT's authoritative ones. When the
// element struct's complete declared layout is refused, the array has no
// authoritative extent either; answering with the natural-C carrier instead
// is the very silent recomputation WS7.8 removes — one level down.

fn load(ty: Ty) -> Vec<InstrNode> {
    vec![
        InstrNode::new(Inst::Load {
            ty,
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Return { values: vec![] }),
    ]
}

/// A by-value copy of `[Mixed; 2]`. rustc sizes it 32 (`Mixed` is 16/8); the
/// natural-C carrier is 48. Copying 48 bytes out of (or into) rustc's 32-byte
/// object is an out-of-bounds access, so the copy must be refused with
/// `Mixed`'s own reason, never lengthed at the recomputation.
#[test]
fn a_by_value_copy_of_an_array_of_a_refused_struct_is_refused() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr)],
        load(Ty::Array(trust_ir::TyId::new(TY_MIXED), 2)),
    );
    assert_refused(&module, MIXED, DeclaredLayoutGate::Totals);
}

/// POSITIVE TWIN: the same by-value copy of an array of an EMITTABLE declared
/// struct still lowers.
#[test]
fn a_by_value_copy_of_an_array_of_an_emittable_struct_still_lowers() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr)],
        load(Ty::Array(trust_ir::TyId::new(1), 2)),
    );
    let ops = opcodes(&module);
    assert!(
        iconsts(&ops).contains(&64),
        "`[TypeCheckId; 2]` is copied at its 64-byte extent: {ops:?}"
    );
}

/// A single-index `GEP` stepping over whole `[Mixed; 2]` values (`&arrs[i]`).
/// Its stride is the array's extent — `Mixed`'s refused one times two — so it
/// must be refused rather than stride by the 48-byte recomputation.
#[test]
fn a_gep_striding_over_an_array_of_a_refused_struct_is_refused() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::Array(trust_ir::TyId::new(TY_MIXED), 2),
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    assert_refused(&module, MIXED, DeclaredLayoutGate::Totals);
}

/// A packed struct with NO declared layout of its own — authority P, the named
/// fallback — around `[P2; 2]`. To place `t`, the packed walk measures the
/// array, which means measuring `P2`, whose complete declared layout is
/// refused. Before WS7.8 the walk used `P2`'s packed size (12, stride 12,
/// `t@24` — rustc's answer); swallowing the new refusal would have silently
/// switched it to the natural-C carrier (`t@48`), a NEW wrong address for a
/// field that never touches `P2`. The refusal must surface instead.
#[test]
fn a_packed_walk_over_an_array_of_a_refused_struct_is_refused() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(PACKED_OUTER_ARR), 1));
    assert_refused(&module, PACKED2_REORDERED, DeclaredLayoutGate::Packed);
}

// ---------------------------------------------------------------------------
// REFUSED WHERE IT IS HELD BY VALUE — the consumers that never ask for a layout
// ---------------------------------------------------------------------------
//
// The stack slot, the heap request and the ABI classifier size a value from
// its natural-C carrier. For an emittable declared layout that is rustc's size
// (the totals gate). For a refused one it is not, so a function that reserves
// storage for, or holds a value of, such a struct is refused before any of
// those consumers runs — even when no field of it is ever addressed.

/// `Over` is `#[repr(align(16))] { a: u8 }`: 16/16 in rustc, 1/1 on the
/// carrier. An `Alloca` of it would reserve ONE byte for an object rustc-
/// compiled callees write sixteen of. No field is addressed here, so before
/// the by-value preflight this compiled silently.
#[test]
fn an_unaddressed_alloca_of_a_refused_struct_is_refused() {
    let module = module_with_body(
        vec![],
        vec![
            InstrNode::new(Inst::Alloca {
                ty: st(OVER_ALIGNED),
                count: None,
                align: None,
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    assert_refused(&module, OVER_ALIGNED, DeclaredLayoutGate::Totals);
}

/// A BY-VALUE parameter of a refused struct: the ABI classifier would pass
/// `Mixed` as the 24-byte recomputation where every rustc-compiled caller
/// passes 16 bytes. Refused, although the body never touches it.
#[test]
fn a_by_value_parameter_of_a_refused_struct_is_refused() {
    let module = module_with_body(
        vec![(v(0), st(MIXED))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    assert_refused(&module, MIXED, DeclaredLayoutGate::Totals);
}

/// A refused struct held INSIDE another by-value shape — here a tuple — is the
/// same hazard one level down: the tuple's carrier embeds the recomputation.
#[test]
fn a_tuple_containing_a_refused_struct_is_refused() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr)],
        load(Ty::Tuple(vec![Ty::U8, st(OVER_ALIGNED)])),
    );
    assert_refused(&module, OVER_ALIGNED, DeclaredLayoutGate::Totals);
}

/// POSITIVE TWIN — the preflight stops at every pointer. A function that only
/// passes the ADDRESS of a refused struct (as a typed `&Mixed` here) assumes
/// nothing about its layout, and still lowers.
#[test]
fn a_function_that_only_passes_a_pointer_to_a_refused_struct_still_lowers() {
    let module = module_with_body(
        vec![(v(0), Ty::Ref(Box::new(st(MIXED))))],
        vec![InstrNode::new(Inst::Return { values: vec![] })],
    );
    let func = module.functions.first().expect("one function");
    trust_cg_lower::translate_function_with_license(func, &module, &permit_unlicensed())
        .expect("a pointer to a refused struct is not a use of it");
}

/// Proof-program row `verify.c07` (trust-cg lens, F-031), ported whole: the
/// repro's own program — `alloca Pair`, store an aggregate constant, load it
/// back, read field `b` — is REFUSED at the `overlap` gate, naming `Pair`,
/// rather than compiled at the natural-C layout the c07 source read recorded
/// as the silent fallback.
#[test]
fn verify_c07_struct_overlap_is_refused_not_laid_out_as_natural_c() {
    let pair = st(C07_OVERLAP);
    let module = module_with_body(
        vec![],
        vec![
            InstrNode::new(Inst::Alloca {
                ty: pair.clone(),
                count: None,
                align: None,
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Const {
                ty: pair.clone(),
                value: Constant::Aggregate(vec![Constant::Int(7), Constant::Float(1.5)]),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Store {
                ty: pair.clone(),
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Load {
                ty: pair.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::ExtractField {
                ty: pair,
                aggregate: v(2),
                field: 1,
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    assert_refused(&module, C07_OVERLAP, DeclaredLayoutGate::Overlap);
}

// ---------------------------------------------------------------------------
// REFUSED AT A CALL EDGE — the callee's signature is an ABI use (review)
// ---------------------------------------------------------------------------
//
// A constructed aggregate is carried by ADDRESS, so a call may hand a
// `Ptr`-typed value to a by-value struct parameter; the ABI classifier then
// reads the CALLEE's declared parameter type. None of the caller's own SSA
// types names the struct, so only the callee signature reveals the use.

/// `module_with_body` plus a body-less callee `ext` (`FuncId(1)`) of the given
/// signature.
fn with_callee(mut module: TrustIrModule, params: Vec<Ty>, returns: Vec<Ty>) -> TrustIrModule {
    let fty = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module
        .try_add_function(TrustIrFunction::declaration(
            FuncId::new(1),
            "ext",
            fty,
            trust_ir::FunctionSummary::default(),
        ))
        .expect("Module::try_add_function: test fixture");
    module
}

/// `k(p: Ptr) { ext(p) }` where `ext` takes a `Mixed` BY VALUE. The caller's
/// types are all `Ptr`, but the call argument is typed from `ext`'s signature
/// — the 24-byte natural carrier `Struct([I8, I64, I16])` — and classified as
/// such, where the rustc-compiled `ext` expects rustc's 16-byte `Mixed` (two
/// registers on AArch64, not an indirect copy). Before this review the
/// preflight never looked at the callee and the call lowered silently.
#[test]
fn a_call_passing_an_address_as_a_by_value_refused_struct_is_refused() {
    let module = with_callee(
        module_with_body(
            vec![(v(0), Ty::Ptr)],
            vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![v(0)],
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        ),
        vec![st(MIXED)],
        vec![],
    );
    assert_refused(&module, MIXED, DeclaredLayoutGate::Totals);
}

/// The same edge through a function POINTER: the `CallIndirect` signature is
/// what the classifier reads.
#[test]
fn a_call_indirect_whose_signature_holds_a_refused_struct_is_refused() {
    let mut module = module_with_body(vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)], vec![]);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![st(OVER_ALIGNED)],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::CallIndirect {
            callee: v(0),
            sig,
            args: vec![v(1)],
            calling_conv: trust_ir::CallingConv::C,
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    assert_refused(&module, OVER_ALIGNED, DeclaredLayoutGate::Totals);
}

/// POSITIVE TWIN: a callee that takes the refused struct by REFERENCE is not a
/// by-value use; the call still lowers.
#[test]
fn a_call_passing_a_reference_to_a_refused_struct_still_lowers() {
    let module = with_callee(
        module_with_body(
            vec![(v(0), Ty::Ref(Box::new(st(MIXED))))],
            vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![v(0)],
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        ),
        vec![Ty::Ref(Box::new(st(MIXED)))],
        vec![],
    );
    let func = module.functions.first().expect("one function");
    trust_cg_lower::translate_function_with_license(func, &module, &permit_unlicensed())
        .expect("a reference parameter is not a by-value use");
}

/// A refused struct inside an ENUM payload is held by value too: loading the
/// enum copies the payload at the natural carrier.
#[test]
fn an_enum_whose_payload_holds_a_refused_struct_is_refused() {
    let mut module = module_with_body(
        vec![(v(0), Ty::Ptr)],
        load(Ty::Enum(trust_ir::EnumId::new(0))),
    );
    module.enums.push(trust_ir::EnumDef::new(
        trust_ir::EnumId::new(0),
        "HoldsOver",
        vec![
            trust_ir::EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            trust_ir::EnumVariant {
                name: "Some".to_string(),
                fields: vec![st(OVER_ALIGNED)],
                field_names: vec![],
            },
        ],
    ));
    assert_refused(&module, OVER_ALIGNED, DeclaredLayoutGate::Totals);
}

/// LEGITIMATE, NOT REFUSED: a complete rustc layout with zero-sized fields — a
/// field-less `PhantomData`-like struct (0/1) and a `()` — parked at the END
/// of the object (`offset == size`), which rustc does. Containment admits a
/// zero-sized image at the end, and no image is compared for overlap.
#[test]
fn a_complete_layout_with_zero_sized_fields_at_the_end_still_lowers() {
    let mut module = module_with_body(vec![(v(0), Ty::Ptr)], vec![]);
    module
        .structs
        .push(sdef(20, "Phantom", StructRepr::Rust, vec![], Some((0, 1))));
    module.structs.push(sdef(
        21,
        "WithZst",
        StructRepr::Rust,
        vec![f("a", Ty::U32, 0), f("p", st(20), 4), f("u", Ty::Unit, 4)],
        Some((4, 4)),
    ));
    module.functions[0].blocks[0].body = extract(st(21), 0);
    let ops = opcodes(&module);
    assert!(!ops.is_empty());
    module.functions[0].blocks[0].body = load(st(21));
    let func = module.functions.first().expect("one function");
    trust_cg_lower::translate_function_with_license(func, &module, &permit_unlicensed())
        .expect("a by-value copy of it lowers too");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
