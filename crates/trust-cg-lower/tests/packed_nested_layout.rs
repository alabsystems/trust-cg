// packed_nested_layout.rs — a packed struct nested inside a packed struct
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `packed_struct_layout` (`adapter.rs`) is THE packed-layout authority: it
//! backs `packed_field_offset` (`StructGep` / field extract / field insert /
//! aggregate constant on a packed struct) and `packed_struct_size` (the
//! `Inst::GEP` element stride). It used to advance its running offset by the
//! NATURAL-C `Type::bytes()` of each field and clamp the NATURAL-C
//! `Type::align()`, because `translate_type_with_enum_tables` resolves
//! `Ty::Struct(sid)` to a repr-less `Type::Struct(Vec<Type>)` and DROPS
//! `sdef.repr` (`adapter.rs:1254-1275`). Both accessors are therefore
//! unconditionally natural-C, and both are wrong when a field is ITSELF a
//! packed struct.
//!
//! THE ORACLE IS STOCK RUSTC — `rustc 1.97.0 (2d8144b78 2026-07-07)`,
//! `size_of` / `align_of` / `offset_of!`, shapes spelled `#[repr(C, packed(N))]`
//! so declaration order is what rustc lays out too:
//!
//! ```text
//! #[repr(C,packed)] P     { a: u8, b: u64 }            size  9 align 1  a@0 b@1
//! #[repr(C,packed)] N     { h: u8, inner: P }          size 10 align 1  h@0 inner@1
//! #[repr(C,packed)] Trail { h: u8, inner: P, t: u8 }   size 11 align 1  h@0 inner@1 t@10
//! ```
//!
//! Before the repair trust-cg emitted `N` = 17 and `Trail` = 18 with `t@17`.
//! Two consequences, both measured:
//!
//! * the SIZE is the `Inst::GEP` element stride, so `&[N]` indexing strode 17
//!   over memory rustc laid out at 10 — a live wrong address, not merely a
//!   wrong `size_of`;
//! * the OFFSET of every field AFTER a nested packed one was over-large.
//!
//! And the repair could not land alone. The natural-C over-report was exactly
//! what made the aggregate-field `Memmove` extents safe: `Trail`'s 16-byte copy
//! into `inner` at offset 1 covered bytes 1..17 and `t` sat at 17, flush. Once
//! `t` moves to rustc's 10, that same copy CLOBBERS it. So the two write
//! extents that copy an aggregate of packed type — the packed `InsertField` arm
//! and the aggregate `Store` arm — moved onto `packed_struct_size` in the same
//! change, via `TrustIrAdapter::aggregate_value_extent`. Those are pinned here
//! too; without them this repair would trade a wrong address for a clobbered
//! sibling.
//!
//! An ARRAY of packed structs was left over-reporting by that change, for
//! exactly the reason above: its elements were still ADDRESSED at the natural-C
//! stride by `ArrayGep` on the repr-less LIR type, and reporting a packed
//! extent while the addressing stayed natural would place a sibling INSIDE the
//! array's real extent — an overlap, strictly worse than an over-report. It has
//! since been closed by moving the extent and every `ArrayGep` stride together
//! onto one authority; the pin at the bottom of this file now reads rustc's 19,
//! and `tests/packed_array_stride.rs` owns the stride sites.
//!
//! Still deliberately NOT changed, and pinned as such below: a TUPLE of packed
//! structs (`Ty::Tuple` fields are addressed by natural-C `StructGep` and the
//! producer states no offsets for them), and a NON-packed container of a packed
//! struct (the repr-blindness of `Type::bytes`/`align`/`offset_of` themselves).

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

fn f(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset: None,
    }
}

fn sdef(id: u32, name: &str, repr: StructRepr, fields: Vec<FieldDef>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.to_string(),
        fields,
        size: None,
        align: None,
        repr,
    }
}

fn st(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// `P = #[repr(C,packed)] { a: u8, b: u64 }` (id 0),
/// `N = #[repr(C,packed)] { h: u8, inner: P }` (id 1),
/// `Trail = #[repr(C,packed)] { h: u8, inner: P, t: u8 }` (id 2).
fn packed_structs() -> Vec<StructDef> {
    vec![
        sdef(
            0,
            "P",
            StructRepr::Packed(1),
            vec![f("a", Ty::U8), f("b", Ty::U64)],
        ),
        sdef(
            1,
            "N",
            StructRepr::Packed(1),
            vec![f("h", Ty::U8), f("inner", st(0))],
        ),
        sdef(
            2,
            "Trail",
            StructRepr::Packed(1),
            vec![f("h", Ty::U8), f("inner", st(0)), f("t", Ty::U8)],
        ),
    ]
}

/// Build a module out of `packed_structs()` plus a single function whose body
/// is `body` and whose signature is `params -> ()`.
fn module_with_body(params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> TrustIrModule {
    let mut module = TrustIrModule::new("packed_nested");
    module.structs = packed_structs();
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

// ---------------------------------------------------------------------------
// The layout repair, as EMITTED CODE
// ---------------------------------------------------------------------------

/// `Inst::GEP { pointee_ty: N }` is the `&slice[i]` stride. rustc says
/// `size_of::<N>() == 10`; trust-cg emitted 17 (`1 + natural(P) = 1 + 16`).
///
/// This is the wrong-ADDRESS half of the defect: the stride is multiplied by a
/// runtime index, so element 1 of a real `&[N]` was read 7 bytes past where
/// rustc put it.
#[test]
fn gep_over_a_nested_packed_pointee_strides_by_rustcs_size() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: st(1),
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    assert_eq!(
        iconsts(&opcodes(&module)),
        vec![10],
        "`#[repr(C,packed)] N {{ h: u8, inner: P }}` is 10 bytes in rustc; the stride was 17"
    );
}

/// The offset half. `Trail { h: u8, inner: P, t: u8 }` puts `t` at rustc's
/// byte 10 — one past `inner`'s real 9-byte extent — not at byte 17, which is
/// one past `inner`'s natural-C 16.
///
/// Read through the aggregate-constant path, which addresses every field of a
/// packed struct through `packed_field_offset`.
#[test]
fn field_after_a_nested_packed_field_sits_at_rustcs_offset() {
    let module = module_with_body(
        vec![],
        vec![
            InstrNode::new(Inst::Const {
                ty: st(2),
                value: Constant::Aggregate(vec![
                    Constant::Int(1),
                    Constant::Aggregate(vec![Constant::Int(2), Constant::Int(3)]),
                    Constant::Int(4),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let imms = iconsts(&opcodes(&module));
    // h@0, then inner@1 with its own sub-fields a@0 / b@1 (values 2 and 3
    // materialised between them), then t@10 with value 4.
    assert_eq!(
        imms,
        vec![0, 1, 1, 0, 2, 1, 3, 10, 4],
        "rustc: Trail is h@0 inner@1 t@10, and inner is a@0 b@1 relative to it"
    );
}

// ---------------------------------------------------------------------------
// The write extents that had to move WITH the layout
// ---------------------------------------------------------------------------

/// `InsertField { ty: Trail, field: 1, value: <P> }` byte-copies the source
/// aggregate to `base + 1`. The copy length must be `P`'s PACKED 9, not its
/// natural-C 16: `t` now lives at byte 10, and a 16-byte copy at offset 1
/// covers bytes 1..17 — it would destroy `t` and the two bytes past it.
#[test]
fn insert_of_a_nested_packed_field_copies_only_its_packed_extent() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), st(0))],
        vec![
            InstrNode::new(Inst::Alloca {
                ty: st(2),
                count: None,
                align: None,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::InsertField {
                ty: st(2),
                aggregate: v(2),
                field: 1,
                value: v(1),
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let ops = opcodes(&module);
    assert!(
        ops.iter().any(|o| matches!(o, Opcode::Memmove)),
        "an aggregate field insert is a byte copy, got {ops:?}"
    );
    assert_eq!(
        iconsts(&ops),
        vec![1, 9],
        "field offset 1 then a 9-byte copy — `P`'s packed extent. A natural-C 16 would \
         overwrite `t`, which the layout repair moved from byte 17 to rustc's byte 10"
    );
}

/// The same obligation on the aggregate `Store` arm: `ptr` may be a packed
/// FIELD address (the packed `ExtractField` arm hands back
/// `base + packed_offset` for an aggregate field), so a natural-C length there
/// reaches past the field into the sibling.
#[test]
fn store_of_a_packed_aggregate_copies_only_its_packed_extent() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), st(0))],
        vec![
            InstrNode::new(Inst::Store {
                ty: st(0),
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    assert_eq!(
        iconsts(&opcodes(&module)),
        vec![9],
        "`#[repr(C,packed)] P {{ a: u8, b: u64 }}` is 9 bytes in rustc; the copy was 16"
    );
}

// ---------------------------------------------------------------------------
// The natural-C slot is UNCHANGED — the domination invariant
// ---------------------------------------------------------------------------

/// The packed shrink only ever LOWERS an offset, a size or an alignment, so
/// authority P stays pointwise `<=` the natural-C authority C. Every
/// extent-measuring consumer that was NOT moved — the alloca/heap element size,
/// the aggregate-constant slot, the aggregate `Load` slot, the C ABI classifier
/// — still uses C, and C still contains the packed image. This pins that the
/// slot did not move with the layout.
#[test]
fn the_stack_slot_for_a_nested_packed_struct_stays_at_the_natural_c_size() {
    let module = module_with_body(
        vec![],
        vec![
            InstrNode::new(Inst::Alloca {
                ty: st(1),
                count: None,
                align: None,
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let func = module.functions.first().expect("one function");
    let (lir_func, _proofs) = translate_function(func, &module).expect("adapter must lower");
    assert_eq!(
        (lir_func.stack_slots[0].size, lir_func.stack_slots[0].align),
        (24, 8),
        "`N`'s natural-C carrier is `Struct([I8, Struct([I8, I64])])` = 24/8; the packed \
         authority now says 10/1 and the slot deliberately does not follow it"
    );
}

// ---------------------------------------------------------------------------
// SURVIVING DIVERGENCE — pinned so it cannot be forgotten
// ---------------------------------------------------------------------------

/// FIXED — an ARRAY of packed structs inside a packed struct.
///
/// rustc: `#[repr(C,packed)] S { h: u8, arr: [P; 2] }` is size 19 with
/// `arr@1`, because `[P; 2]` is 18 bytes at a 9-byte element stride.
///
/// trust-cg used to contribute `Type::Array(Struct([I8,I64]), 2).bytes()` = 32
/// and report `S` as 33. The reason it could not be fixed with the nested-struct
/// case is the one this file states throughout: the array's ELEMENTS were still
/// addressed at the natural 16-byte stride by `Opcode::ArrayGep` on the
/// repr-less LIR type, so reporting `[P; 2]` as 18 alone would have placed a
/// sibling at byte 19, INSIDE the bytes element 1 actually wrote (16..32) — an
/// overlap, strictly worse than an over-report.
///
/// So the extent and the addressing moved in ONE change. Every `ArrayGep` site
/// now takes its stride from the same authority this extent comes from
/// (`declared_layout::emitted_field_layout`), which is what makes 18 emittable;
/// `tests/packed_array_stride.rs` pins each of those sites and their mutual
/// agreement.
#[test]
fn array_of_packed_elements_contributes_rustcs_extent() {
    let mut module = TrustIrModule::new("arr");
    let mut structs = packed_structs();
    let elem_ty_id = {
        // `[P; 2]` as a `Ty::Array` over the module type table.
        module.types.push(st(0));
        trust_ir::TyId::new(0)
    };
    structs.push(sdef(
        3,
        "S",
        StructRepr::Packed(1),
        vec![f("h", Ty::U8), f("arr", Ty::Array(elem_ty_id, 2))],
    ));
    module.structs = structs;
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: st(3),
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);

    assert_eq!(
        iconsts(&opcodes(&module)),
        vec![19],
        "rustc says `#[repr(C,packed)] S {{ h: u8, arr: [P; 2] }}` is 19 (h@0, then `[P; 2]` \
         at its real 18-byte extent); the stride was 33 while `[P; 2]` contributed its \
         natural-C 32"
    );
}

/// NOT FIXED: a NON-packed struct that CONTAINS a packed one.
///
/// rustc: `#[repr(C)] OuterC { h: u8, inner: P }` is size 10, align 1, with
/// `inner@1` — `P`'s own alignment is 1, so the container inherits align 1 and
/// gets no padding at all.
///
/// trust-cg never consults a packed authority here: `is_packed_struct_ty` is
/// false for `OuterC`, so it lowers to `Type::Struct([I8, Struct([I8, I64])])`
/// with `Type::align()` = 8, `inner@8` and size 24. The fix is not in
/// `packed_struct_layout` at all — it is in the repr-blindness of
/// `Type::bytes()` / `align()` / `offset_of()` themselves
/// (`trust-cg-ir/src/function.rs:166-217`), which every non-packed path uses.
/// Changing it would move NON-PACKED output, which this repair is required not
/// to do.
#[test]
fn non_packed_container_of_a_packed_struct_is_still_laid_out_natural_c() {
    let mut structs = packed_structs();
    structs.push(sdef(
        3,
        "OuterC",
        StructRepr::C,
        vec![f("h", Ty::U8), f("inner", st(0))],
    ));
    let mut module = TrustIrModule::new("outer");
    module.structs = structs;
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::I64],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: st(3),
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);

    assert_eq!(
        iconsts(&opcodes(&module)),
        vec![24],
        "rustc says `#[repr(C)] OuterC {{ h: u8, inner: P }}` is 10 bytes with align 1; \
         trust-cg says 24 because no packed authority is consulted for a non-packed container"
    );
    // And the field offset it emits is the natural-C 8, not rustc's 1.
    let lir = Type::Struct(vec![Type::I8, Type::Struct(vec![Type::I8, Type::I64])]);
    assert_eq!(lir.offset_of(1), Some(8));
}
