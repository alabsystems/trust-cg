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
//! #[repr(packed(2))] struct P2 { a: u8, b: u64, c: u16 } a@10 b@0 c@8       STILL OPEN
//! #[repr(C)] struct OuterC { h: u8, inner: P }          h@0 inner@1, 10/1   STILL OPEN
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
//! * **Declined, and named** — a declared layout the byte path cannot honour:
//!   incoherent producer data, a field whose emitted image runs off the end or
//!   into a sibling, totals that diverge from the recomputation, and every
//!   `#[repr(packed(N))]` struct. Those keep the recomputation and stay counted
//!   by [`trust_cg_lower::layout_refusal`].

use trust_cg_lower::adapter::translate_function;
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
        // `repr(C)` REORDERS. STILL OPEN: packed keeps authority P, which is
        // declaration-ordered (a@0 b@2 c@10).
        sdef(
            PACKED2_REORDERED,
            "P2",
            StructRepr::Packed(2),
            vec![f("a", Ty::U8, 10), f("b", Ty::U64, 0), f("c", Ty::U16, 8)],
            Some((12, 2)),
        ),
        // rustc: h@0 inner@1, size 10 align 1. STILL OPEN: the recomputation
        // sizes this 24/8 because the interior `P` is measured natural-C, so
        // the totals gate declines it.
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
    ]
}

/// The module `types` table: entry 0 is `u64` (the `AHasher` array element),
/// entry 1 is `TypeCheckId` (the `ArrOfIds` array element).
fn types_table() -> Vec<Ty> {
    vec![Ty::U64, st(TYPE_CHECK_ID)]
}

fn module_with_body(params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> TrustIrModule {
    let mut module = TrustIrModule::new("declared_layout");
    module.structs = structs();
    module.types = types_table();
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: params.iter().map(|(_, t)| t.clone()).collect(),
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params,
        body,
    }];
    module.add_function(func);
    module
}

fn opcodes(module: &TrustIrModule) -> Vec<Opcode> {
    let func = module.functions.first().expect("one function");
    let (lir_func, _proofs) =
        translate_function(func, module).expect("adapter must lower the fixture");
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
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::U64)],
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
    assert_eq!(iconsts(&ops), vec![8]);
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

/// The multi-index `GEP` path: `&arr[i].expr_hash`. The array strides by the
/// element's size and the field step must then use rustc's offset.
#[test]
fn a_multi_index_gep_into_an_array_element_uses_rustcs_field_offset() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::GEP {
                pointee_ty: st(TYPE_CHECK_ID),
                base: v(0),
                indices: vec![v(1), v(2)],
                inbounds: false,
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let ops = opcodes(&module);
    assert!(
        ops.iter()
            .any(|o| matches!(o, Opcode::ArrayGep { elem_ty } if elem_ty.bytes() == 32)),
        "the element stride is `size_of::<TypeCheckId>()` = 32: {ops:?}"
    );
    assert!(
        iconsts(&ops).contains(&8),
        "the field step must be rustc's `expr_hash@8`: {ops:?}"
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

/// STILL OPEN, measured and named. `#[repr(packed(2))] { a: u8, b: u64,
/// c: u16 }` is `a@10 b@0 c@8` in rustc — `packed(N)` with `N > 1` and no
/// `repr(C)` REORDERS — and authority P is a declaration-ordered walk that
/// structurally cannot express that. Closing it means letting the declared
/// layout into the packed lane, which needs the packed size split resolved
/// first.
#[test]
fn packed_n_above_one_still_does_not_reorder() {
    for (index, authority_p, rustc) in [(0u32, 0i64, 10i64), (1, 2, 0), (2, 10, 8)] {
        let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(PACKED2_REORDERED), index));
        assert_ne!(authority_p, rustc, "the divergence is real");
        assert_eq!(
            iconsts(&opcodes(&module)),
            vec![authority_p],
            "field {index}: authority P says {authority_p}, rustc says {rustc} — STILL OPEN"
        );
    }
}

/// STILL OPEN, measured and named. `#[repr(C)] OuterC { h: u8, inner: P }` is
/// 10 bytes with `inner@1` in rustc, because `P`'s own alignment is 1. The
/// recomputation measures the interior `P` natural-C and sizes the container
/// 24/8, so the declared totals diverge and the totals gate declines the whole
/// layout — including its `inner@1`.
#[test]
fn a_non_packed_struct_containing_a_packed_one_is_still_recomputed() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(OUTER_C), 1));
    let ops = opcodes(&module);
    assert_eq!(
        struct_geps(&ops),
        vec![1],
        "rustc says `inner@1`; the recomputation says 8 and still wins here: {ops:?}"
    );
}

/// INCOHERENT producer data is declined rather than emitted. A `u64` at offset
/// 4 in a non-packed struct is not a layout rustc mints; emitting it would turn
/// a wrong-address defect into an undeclared unaligned access.
#[test]
fn an_incoherently_aligned_declared_offset_is_declined() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(INCOHERENT), 1));
    let ops = opcodes(&module);
    assert_eq!(struct_geps(&ops), vec![1], "{ops:?}");
    assert!(iconsts(&ops).is_empty(), "{ops:?}");
}

/// A declared offset whose field's emitted image runs off the end of the
/// declared object is declined — honouring it would be an out-of-bounds write,
/// not a fix.
#[test]
fn a_declared_offset_that_runs_off_the_end_is_declined() {
    let module = module_with_body(vec![(v(0), Ty::Ptr)], extract(st(FIELD_OFF_THE_END), 1));
    let ops = opcodes(&module);
    assert_eq!(struct_geps(&ops), vec![1], "{ops:?}");
    assert!(iconsts(&ops).is_empty(), "{ops:?}");
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
