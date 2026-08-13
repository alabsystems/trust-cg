// packed_array_stride.rs — the ARRAY element stride, on every path that walks one
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `Opcode::ArrayGep` carries a repr-less LIR `Type` and is resolved downstream
//! by natural-C `Type::bytes()`, so it can express one stride and one only. For
//! an array whose ELEMENT has an authority above natural C — a
//! `#[repr(packed(N))]` struct, or a producer-declared layout — that stride is
//! the wrong address, and four separate sites emitted it.
//!
//! THE ORACLE IS STOCK RUSTC — `rustc 1.97.0 (2d8144b78 2026-07-07)`,
//! `size_of` / `align_of` / `offset_of!`, run natively on aarch64-apple-darwin:
//!
//! ```text
//! #[repr(C,packed)] P { a: u8, b: u64 }          size  9  align 1  a@0 b@1
//! [P; 2]                                         size 18  align 1  (STRIDE 9)
//! [P; 3]                                         size 27  align 1
//! [[P; 2]; 2]                                    size 36  align 1  (STRIDE 18)
//! #[repr(C,packed)] S { h: u8, arr: [P; 2] }     size 19  align 1  h@0 arr@1
//! ```
//!
//! # The write/read split this closes
//!
//! (c) MEASURED before the repair, on the SAME `[P; 2]` object:
//!
//! ```text
//! Constant::Aggregate    WRITES element 1 at byte 16   (ArrayGep, natural stride)
//! GEP { pointee_ty: P }  READS  element 1 at byte  9   (explicit_element_stride)
//! ```
//!
//! One path in four was already right. That is a live write/read split of the
//! same class as the const-path field miscompile repaired before it — a value
//! stored by the constant path and loaded back through a pointer walk read
//! seven bytes of the wrong element.
//!
//! # Why the stride and the EXTENT had to move in one change
//!
//! Three obligations, each pinned below, and each of which breaks if only its
//! partner moves:
//!
//! * **stride without copy length.** Once element `i` sits at `i * 9`, the
//!   16-byte `Memmove` the `InsertElement` arm emitted for a 9-byte element
//!   covers bytes 0..16 and CLOBBERS the first seven bytes of element 1.
//! * **extent without stride.** Reporting `[P; 2]` as 18 while `ArrayGep` still
//!   strode 16 puts the next sibling of a containing packed struct at byte 19,
//!   INSIDE the bytes element 1 actually writes (16..32) — an overlap, which is
//!   strictly worse than the over-report it replaced.
//! * **either without the containing walk.** `packed_struct_layout` advances by
//!   the field's extent, so `S`'s `arr` field and `S`'s own size only reach
//!   rustc's 19 when the array extent moves too.
//!
//! They move together because they are now ONE function:
//! `declared_layout::emitted_field_layout` — asked by the copy lengths, by the
//! containing packed walk, by the declared-layout containment gate, and (via
//! `explicit_element_stride`) by every `ArrayGep` site.
//!
//! # What deliberately did NOT move
//!
//! The natural-C stack slot. `Alloca`/`HeapAlloc` still size elements with
//! `Type::bytes()`, so every slot still DOMINATES the packed image it holds
//! (32 >= 18 for `[P; 2]`) and the shrink can only ever write further inside a
//! slot than it did before — never past it. Pinned at the bottom.

use trust_cg_lower::adapter::translate_function;
use trust_cg_lower::instructions::Opcode;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FieldDef, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, StructDef, StructId,
    StructRepr, Ty, TyId, ValueId,
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

/// `P = #[repr(C,packed)] { a: u8, b: u64 }` — rustc: size 9, align 1, a@0 b@1.
fn packed_p() -> StructDef {
    sdef(
        0,
        "P",
        StructRepr::Packed(1),
        vec![f("a", Ty::U8), f("b", Ty::U64)],
    )
}

/// `Nat = #[repr(C)] { a: u8, b: u64 }` — rustc: size 16, align 8. The CONTROL:
/// natural C is the authority, so every stride here must stay `ArrayGep`.
fn natural_n() -> StructDef {
    sdef(
        1,
        "Nat",
        StructRepr::C,
        vec![f("a", Ty::U8), f("b", Ty::U64)],
    )
}

fn p_ty() -> Ty {
    Ty::Struct(StructId::new(0))
}

fn nat_ty() -> Ty {
    Ty::Struct(StructId::new(1))
}

/// TyId(0) = `P`, TyId(1) = `[P; 2]`, TyId(2) = `Nat`.
fn p_arr2() -> Ty {
    Ty::Array(TyId::new(0), 2)
}

fn p_arr2_arr2() -> Ty {
    Ty::Array(TyId::new(1), 2)
}

fn nat_arr2() -> Ty {
    Ty::Array(TyId::new(2), 2)
}

/// A module carrying `P`, `Nat`, `[P; 2]`, `[[P; 2]; 2]` and `[Nat; 2]`, plus a
/// single function `k(params) -> ()` with `body`.
fn module_with_body(params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> TrustIrModule {
    let mut module = TrustIrModule::new("packed_array_stride");
    module.types.push(p_ty()); // TyId(0)
    module.types.push(p_arr2()); // TyId(1)
    module.types.push(nat_ty()); // TyId(2)
    module.structs = vec![packed_p(), natural_n()];
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

fn lower(module: &TrustIrModule) -> trust_cg_lower::function::Function {
    let func = module.functions.first().expect("one function");
    let (lir_func, _proofs) =
        translate_function(func, module).expect("adapter must lower the fixture");
    lir_func
}

fn opcodes(module: &TrustIrModule) -> Vec<Opcode> {
    let lir_func = lower(module);
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

/// Every `ArrayGep` element type in the emitted stream — empty means every
/// stride was materialised explicitly.
fn array_geps(opcodes: &[Opcode]) -> Vec<String> {
    opcodes
        .iter()
        .filter_map(|o| match o {
            Opcode::ArrayGep { elem_ty } => Some(format!("{elem_ty:?}")),
            _ => None,
        })
        .collect()
}

fn ret() -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![] })
}

// ---------------------------------------------------------------------------
// The four stride sites
// ---------------------------------------------------------------------------

/// SITE 1 — `Inst::ExtractElement` (a READ). `arr[i]` where `arr: [P; 2]`
/// strode 16 over memory rustc lays out at 9, so element 1 was read seven bytes
/// past where every writer put it.
#[test]
fn extract_element_of_a_packed_element_strides_by_rustcs_size() {
    let module = module_with_body(
        vec![(v(0), p_arr2()), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::ExtractElement {
                ty: p_ty(),
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
            ret(),
        ],
    );
    let ops = opcodes(&module);
    assert_eq!(
        iconsts(&ops),
        vec![9],
        "`size_of::<P>() == 9` in rustc; ExtractElement strode `Struct([I8, I64]).bytes()` = 16"
    );
    assert!(
        array_geps(&ops).is_empty(),
        "ArrayGep cannot express a 9-byte stride for a 16-byte LIR carrier, so the \
         arithmetic must be explicit; got {ops:?}"
    );
}

/// SITE 2 — `Inst::InsertElement` (a WRITE), stride AND copy length together.
///
/// This is the pair that could not be split: at a 9-byte stride, the 16-byte
/// copy the arm used to emit covers bytes 0..16 of the array and destroys the
/// first seven bytes of element 1.
#[test]
fn insert_element_strides_and_copies_the_packed_extent() {
    let module = module_with_body(
        vec![(v(0), p_arr2()), (v(1), Ty::I64), (v(2), p_ty())],
        vec![
            InstrNode::new(Inst::InsertElement {
                ty: p_arr2(),
                array: v(0),
                index: v(1),
                value: v(2),
            })
            .with_result(v(3)),
            ret(),
        ],
    );
    let ops = opcodes(&module);
    assert!(
        ops.iter().any(|o| matches!(o, Opcode::Memmove)),
        "an aggregate element insert is a byte copy, got {ops:?}"
    );
    assert_eq!(
        iconsts(&ops),
        vec![9, 9],
        "the STRIDE (9) then the COPY LENGTH (9). A 16-byte copy at a 9-byte stride \
         clobbers the next element; a 9-byte copy at a 16-byte stride leaves element 1 \
         seven bytes stale"
    );
}

/// SITE 3 — `translate_multi_index_gep`, BOTH steps.
///
/// `GEP { pointee_ty: [P; 2], indices: [i, j] }` strides the whole array then
/// one element: rustc's 18 then 9, where trust-cg emitted the natural-C 32 then
/// 16. The outer step is the case `explicit_element_stride` could not answer at
/// all before, because the pointee is a `Ty::Array` and no `StructDef` backs it.
#[test]
fn multi_index_gep_strides_both_levels_by_rustcs_sizes() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: p_arr2(),
                base: v(0),
                indices: vec![v(1), v(2)],
                inbounds: false,
            })
            .with_result(v(3)),
            ret(),
        ],
    );
    let ops = opcodes(&module);
    assert_eq!(
        iconsts(&ops),
        vec![18, 9],
        "`size_of::<[P; 2]>() == 18` and `size_of::<P>() == 9`; trust-cg strode 32 then 16"
    );
    assert!(array_geps(&ops).is_empty(), "got {ops:?}");
}

/// SITE 3, nested — `[[P; 2]; 2]` steps 36, 18, 9. The extent of an array of
/// arrays is only right if the element recursion bottoms out at the STRUCT
/// authority rather than at the outermost LIR type.
#[test]
fn multi_index_gep_over_an_array_of_arrays_recurses_to_the_element_authority() {
    let module = module_with_body(
        vec![
            (v(0), Ty::Ptr),
            (v(1), Ty::I64),
            (v(2), Ty::I64),
            (v(3), Ty::I64),
        ],
        vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: p_arr2_arr2(),
                base: v(0),
                indices: vec![v(1), v(2), v(3)],
                inbounds: false,
            })
            .with_result(v(4)),
            ret(),
        ],
    );
    assert_eq!(
        iconsts(&opcodes(&module)),
        vec![36, 18, 9],
        "rustc: `size_of::<[[P; 2]; 2]>() == 36`, `[P; 2]` 18, `P` 9"
    );
}

/// SITE 4 — `Constant::Aggregate` over an array (a WRITE). The other half of
/// the write/read split: this arm placed element 1 of `[P; 2]` at byte 16 while
/// `Inst::GEP` read it from byte 9.
///
/// At an authoritative stride the whole element address is a compile-time
/// constant, so it folds to one `Iconst` + `Iadd` — the same encoding the
/// packed/declared STRUCT branch of this arm already emits.
#[test]
fn aggregate_constant_places_array_elements_at_rustcs_offsets() {
    let module = module_with_body(
        vec![],
        vec![
            InstrNode::new(Inst::Const {
                ty: p_arr2(),
                value: Constant::Aggregate(vec![
                    Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
                    Constant::Aggregate(vec![Constant::Int(3), Constant::Int(4)]),
                ]),
            })
            .with_result(v(0)),
            ret(),
        ],
    );
    let ops = opcodes(&module);
    assert_eq!(
        iconsts(&ops),
        // elem 0 @0 { a@+0 = 1, b@+1 = 2 }, elem 1 @9 { a@+0 = 3, b@+1 = 4 }
        vec![0, 0, 1, 1, 2, 9, 0, 3, 1, 4],
        "rustc puts element 1 of `[P; 2]` at byte 9; this arm wrote it at 16 while \
         `GEP {{ pointee_ty: P }}` read it from 9"
    );
    assert!(array_geps(&ops).is_empty(), "got {ops:?}");
}

// ---------------------------------------------------------------------------
// The write/read AGREEMENT — the point of the whole change
// ---------------------------------------------------------------------------

/// The defect stated as the property it violated: every path that addresses
/// element 1 of `[P; 2]` must name the SAME byte. Before the repair the const
/// path said 16 and the pointer walk said 9.
#[test]
fn every_path_addresses_element_one_of_the_same_array_at_the_same_byte() {
    // READ, single-index GEP over the element type: `base + 1 * 9`.
    let read = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: p_ty(),
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
            ret(),
        ],
    );
    let read_stride = iconsts(&opcodes(&read));

    // READ, ExtractElement.
    let extract = module_with_body(
        vec![(v(0), p_arr2()), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::ExtractElement {
                ty: p_ty(),
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
            ret(),
        ],
    );
    let extract_stride = iconsts(&opcodes(&extract));

    // WRITE, InsertElement (first Iconst is the stride).
    let insert = module_with_body(
        vec![(v(0), p_arr2()), (v(1), Ty::I64), (v(2), p_ty())],
        vec![
            InstrNode::new(Inst::InsertElement {
                ty: p_arr2(),
                array: v(0),
                index: v(1),
                value: v(2),
            })
            .with_result(v(3)),
            ret(),
        ],
    );
    let insert_stride = vec![iconsts(&opcodes(&insert))[0]];

    assert_eq!(read_stride, vec![9], "the path that was already correct");
    assert_eq!(extract_stride, read_stride, "READ/READ agreement");
    assert_eq!(insert_stride, read_stride, "WRITE/READ agreement");
}

// ---------------------------------------------------------------------------
// The CONTROL — natural-C elements keep the exact encoding they had
// ---------------------------------------------------------------------------

/// `Nat = #[repr(C)] { a: u8, b: u64 }` is 16 bytes under BOTH authorities, so
/// nothing about `[Nat; 2]` may change: `ArrayGep` stays, no stride constant is
/// materialised, and the isel keeps its shift-addressing opportunity.
///
/// This is the guard on the repair's blast radius. It fires on any change that
/// routes a natural-C array through the explicit-arithmetic path.
#[test]
fn arrays_of_natural_c_elements_still_use_arraygep() {
    let extract = module_with_body(
        vec![(v(0), nat_arr2()), (v(1), Ty::I64)],
        vec![
            InstrNode::new(Inst::ExtractElement {
                ty: nat_ty(),
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
            ret(),
        ],
    );
    let ops = opcodes(&extract);
    assert_eq!(
        array_geps(&ops),
        vec!["Struct([I8, I64])".to_string()],
        "a natural-C element keeps the ArrayGep encoding verbatim, got {ops:?}"
    );
    assert!(iconsts(&ops).is_empty(), "no stride constant, got {ops:?}");

    let multi = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), Ty::I64), (v(2), Ty::I64)],
        vec![
            InstrNode::new(Inst::GEP {
                pointee_ty: nat_arr2(),
                base: v(0),
                indices: vec![v(1), v(2)],
                inbounds: false,
            })
            .with_result(v(3)),
            ret(),
        ],
    );
    let ops = opcodes(&multi);
    assert_eq!(
        array_geps(&ops),
        vec![
            "Array(Struct([I8, I64]), 2)".to_string(),
            "Struct([I8, I64])".to_string(),
        ],
        "both steps of a natural-C multi-index GEP keep ArrayGep, got {ops:?}"
    );
    assert!(iconsts(&ops).is_empty(), "no stride constant, got {ops:?}");
}

// ---------------------------------------------------------------------------
// The DOMINATION invariant — the slot did not move with the stride
// ---------------------------------------------------------------------------

/// `Alloca`/`HeapAlloc` still size their elements with natural-C
/// `Type::bytes()`, deliberately: those four extent sites cannot move without
/// the `abi.rs` register classifier, which sizes aggregates from `sig.params`
/// after the struct identity is gone.
///
/// That leaves an OVER-allocation, which is exactly what makes this repair
/// safe on its own. `[P; 2]` occupies bytes 0..18 of a 32-byte slot; every
/// address the shrink moved moved DOWNWARD, so no write that was in bounds
/// before is out of bounds now. Pin the slot so a future extent change has to
/// come here and state its disposition for the classifier.
#[test]
fn the_stack_slot_for_an_array_of_packed_elements_stays_natural_c() {
    let module = module_with_body(
        vec![],
        vec![
            InstrNode::new(Inst::Alloca {
                ty: p_arr2(),
                count: None,
                align: None,
            })
            .with_result(v(0)),
            ret(),
        ],
    );
    let lir = lower(&module);
    assert_eq!(
        (lir.stack_slots[0].size, lir.stack_slots[0].align),
        (32, 8),
        "`[P; 2]`'s natural-C carrier is `Array(Struct([I8, I64]), 2)` = 32/8; the packed \
         image is 18/1 and DOMINATED by it. The slot deliberately does not follow"
    );
}

/// The domination invariant as a property over the copy extents: an aggregate
/// `Load`/`Store` of `[P; 2]` now moves rustc's 18 bytes, and 18 fits inside
/// the 32-byte slot the same function reserves.
#[test]
fn aggregate_copies_of_an_array_move_rustcs_extent_inside_the_natural_slot() {
    let module = module_with_body(
        vec![(v(0), Ty::Ptr), (v(1), p_arr2())],
        vec![
            InstrNode::new(Inst::Load {
                ty: p_arr2(),
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Store {
                ty: p_arr2(),
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }),
            ret(),
        ],
    );
    let lir = lower(&module);
    let entry = lir.entry_block;
    let imms: Vec<i64> = lir.blocks[&entry]
        .instructions
        .iter()
        .filter_map(|i| match &i.opcode {
            Opcode::Iconst { imm, .. } => Some(*imm),
            _ => None,
        })
        .collect();
    assert_eq!(
        imms,
        vec![18, 18],
        "`size_of::<[P; 2]>() == 18`; both copies moved the natural-C 32"
    );
    let slot = lir.stack_slots[0].size;
    assert!(
        imms.iter().all(|&n| n as u32 <= slot),
        "every copy extent must fit the natural-C slot it lands in ({slot})"
    );
}

/// AN ARRAY WHOSE NATURAL EXTENT CANNOT FIT THE LIR CARRIER IS REFUSED.
///
/// `Type::bytes()` is a `u32`. `declared_layout` computes the authoritative
/// extent in `u64`. Below 2^32 that is a distinction without a difference, and
/// every test above lives there. At and above it the two diverge, and the
/// divergence runs the WRONG WAY: the authoritative number stays large while
/// the carrier — which sizes the `Alloca` slot, the `__rust_alloc` request and
/// the by-value ABI decision — cannot.
///
/// (c) MEASURED before this refusal, on `[Nat; 268435456]` (stock `rustc
/// 1.97.0` accepts the type; `size_of` = 4294967296):
///
/// ```text
///   emitted_value_extent -> 4294967296       (u64, exact)
///   Type::bytes()        -> 0                (u32, wrapped)
///   emitted stream       -> StackAddr slot 0 (size 0) ; Iconst 4294967296 ; Memmove
/// ```
///
/// A 4 GiB copy into a zero-byte stack slot. Every other test in this file
/// rests on `emitted <= natural`, which is also the reason `Alloca` and
/// `HeapAlloc` were left on the natural extent (defect B) rather than shrunk —
/// so this is not a corner case, it is the invariant itself inverting.
///
/// Refusal is the fail-closed answer: no `Type` can describe the object, so any
/// extent emitted for it would be a guess. The bound is exact — one element
/// short still lowers.
#[test]
fn an_array_too_large_for_the_u32_carrier_is_refused_at_type_translation() {
    use trust_cg_lower::adapter::translate_type_with_tables;

    let structs = vec![natural_n()];
    let types = vec![nat_ty()];

    // 16 x 2^28 == 2^32 exactly — the first extent that does not fit.
    let too_big = Ty::Array(TyId::new(0), 268_435_456);
    let err = translate_type_with_tables(&too_big, &structs, &types)
        .expect_err("an array whose extent cannot fit its carrier must be refused");
    let msg = format!("{err}");
    assert!(
        msg.contains("does not fit the u32 LIR carrier"),
        "expected the carrier refusal, got: {msg}"
    );

    // ONE ELEMENT SHORT STILL LOWERS, and reports its exact extent. This is
    // what makes the gate a boundary rather than a blanket ban on big arrays.
    let fits = Ty::Array(TyId::new(0), 268_435_455);
    let lir = translate_type_with_tables(&fits, &structs, &types)
        .expect("the largest representable array must still lower");
    assert_eq!(lir.bytes(), 4_294_967_280);

    // And the refusal is about the EXTENT, not the length: 2^28 elements of a
    // 1-byte type is the same count and lowers fine.
    let many_small = Ty::Array(TyId::new(1), 268_435_456);
    let small_types = vec![nat_ty(), Ty::U8];
    let lir = translate_type_with_tables(&many_small, &structs, &small_types)
        .expect("count is not the constraint; extent is");
    assert_eq!(lir.bytes(), 268_435_456);
}
