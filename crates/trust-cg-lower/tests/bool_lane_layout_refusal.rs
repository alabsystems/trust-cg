// Copyright 2026 Andrew Yates | Apache-2.0
//! A `<N x bool>` logical mask never reaches a memory layout here, and its
//! register carrier never crosses a `translate_type`-typed slot in the wrong
//! register class.
//!
//! trust-ir's normative interpreter (`docs/SPEC_RATIFICATIONS.md` §4) stores a
//! `<N x bool>` as N bytes, one `0xFF` / `0x00` byte per lane, and decodes any
//! non-zero byte as `true` — `byte_size(<N x bool>) = N` (trust-ir
//! `bool_lane_width_vs_layout.rs`, 5cad0889). This backend carries the mask in
//! the register class its PRODUCER chose (`<8 x i16>` compare -> V128 of
//! 16-bit lanes, `<8 x i8>` compare -> V64 of byte lanes, canonical constant
//! -> the physical integer vector) and `translate_type` sizes every
//! `<N x bool>` as V128. Measured 2026-09-22 on aarch64 (trust-cg 017781483,
//! `trust-cg-codegen/tests/e2e_aarch64_bool_mask_store_bytes.rs`): storing the
//! `<8 x i16> sge` mask `[T,F,T,F,T,F,T,F]` wrote 16 bytes
//! `ff ff 00 00 ff ff 00 00 ff ff 00 00 ff ff 00 00` where the referee writes 8
//! bytes `ff 00 ff 00 ff 00 ff 00`; `<4 x bool>` wrote 16 where the referee
//! writes 4; `<2 x bool>` 16 where the referee writes 2; a `Load` of
//! `01 00 01 00 01 00 01 00` re-stored the raw 16 bytes where the referee
//! re-stores `ff 00 ff 00 ..`. Only `<16 x bool>` from `<16 x i8>` agreed, by
//! coincidence of lane width.
//!
//! Ruling 2026-09-21: a shape is lowered only if the IR model defines it AND
//! the proof lane covers the lowering. The referee defines the image; no
//! `trust-cg-verify` obligation covers a lane-narrowing or canonicalising mask
//! store / load, so every LAYOUT use of a bool-lane type — `Store`, `Load`,
//! their volatile forms, the atomics, `Alloca`, `HeapAlloc`, a `GEP` pointee,
//! and any aggregate that stores one by value — is refused by name
//! (`AdapterError::BoolLaneLayoutNotAdmitted`), and a mask whose carrier is not
//! the slot's crossing a return / call / block boundary is refused by name
//! (`AdapterError::BoolMaskCarrierMismatch`). The register lane is unchanged:
//! compares, canonical constants, `vector.mask_to_bits`, and opaque
//! pass-through all still lower. Re-admitting a memory form requires the
//! proof-lane evidence, not an edit to these pins.

use trust_cg_lower::adapter::{AdapterError, translate_type, translate_type_in_module};
use trust_cg_lower::types::Type;
use trust_ir::dialect::vector as vector_dialect;
use trust_ir::inst::AllocOrigin;
use trust_ir::{
    AtomicRMWOp, Block, BlockId, ClosureTy, Constant, EnumDef, EnumId, EnumVariant, FieldDef,
    FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Interpreter, Module, Ordering, RecordDef,
    RecordId, StructDef, StructId, StructRepr, Ty, TyId, ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn vec_ty(elem: Ty, lanes: u32) -> Ty {
    Ty::Vector(Box::new(elem), lanes)
}

fn bool_ty(lanes: u32) -> Ty {
    vec_ty(Ty::Bool, lanes)
}

/// Every compare shape that PRODUCES a `<N x bool>` in this backend, as
/// `(lane element, lanes, register carrier of the mask)`.
fn producers() -> Vec<(Ty, u32, Type)> {
    vec![
        (Ty::I16, 8, Type::V128),
        (Ty::I8, 8, Type::V64),
        (Ty::I32, 4, Type::V128),
        (Ty::I64, 2, Type::V128),
        (Ty::I8, 16, Type::V128),
    ]
}

/// One function `(params) -> returns` with `body` in its entry block, plus
/// optional extra blocks.
fn module_with(
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
    extra_blocks: Vec<Block>,
) -> Module {
    let mut module = Module::new("bool_lane_layout");
    let ft = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
    let mut blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(i, ty)| (v(i as u32), ty))
            .collect(),
        body,
    }];
    blocks.extend(extra_blocks);
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn translate(module: &Module) -> Result<(), AdapterError> {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .map(|_| ())
}

/// `mask = <lanes x elem> sge (load p0), (load p1)`; the loads let the
/// `<8 x i8>` (V64) shape produce a mask, since V64 constants are refused.
fn push_loaded_compare(body: &mut Vec<InstrNode>, elem: Ty, lanes: u32, next: &mut u32) -> ValueId {
    let ty = vec_ty(elem, lanes);
    let a = v(*next);
    let b = v(*next + 1);
    let mask = v(*next + 2);
    *next += 3;
    body.push(
        InstrNode::new(Inst::Load {
            ty: ty.clone(),
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(a),
    );
    body.push(
        InstrNode::new(Inst::Load {
            ty: ty.clone(),
            ptr: v(1),
            volatile: false,
            align: None,
        })
        .with_result(b),
    );
    body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Sge,
            ty,
            lhs: a,
            rhs: b,
        })
        .with_result(mask),
    );
    mask
}

fn store(ty: Ty, ptr: ValueId, value: ValueId, volatile: bool) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty,
        ptr,
        value,
        volatile,
        align: None,
    })
}

fn ret(values: Vec<ValueId>) -> InstrNode {
    InstrNode::new(Inst::Return { values })
}

fn assert_layout_refusal(result: Result<(), AdapterError>, mask: &Ty, location: &str, what: &str) {
    match result {
        Err(AdapterError::BoolLaneLayoutNotAdmitted {
            ty,
            location: got,
            detail,
        }) => {
            assert_eq!(&ty, mask, "{what}: refused type");
            assert_eq!(got, location, "{what}: location");
            assert!(
                detail.contains("one 0xFF/0x00 byte per lane") && detail.contains("2026-09-21"),
                "{what}: the detail names the referee's image and the ruling: {detail}"
            );
        }
        other => panic!("{what}: expected BoolLaneLayoutNotAdmitted at {location}, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The register carrier is unchanged
// ---------------------------------------------------------------------------

#[test]
fn bool_lane_vectors_keep_their_v128_register_carrier() {
    for lanes in [16u32, 8, 4, 2] {
        assert_eq!(translate_type(&bool_ty(lanes)).unwrap(), Type::V128);
    }
}

// ---------------------------------------------------------------------------
// Memory boundaries: refused by name for every producer
// ---------------------------------------------------------------------------

#[test]
fn store_of_a_compare_produced_mask_is_refused_for_every_producer() {
    for (elem, lanes, _) in producers() {
        let mut body = Vec::new();
        let mut next = 3;
        let mask = push_loaded_compare(&mut body, elem.clone(), lanes, &mut next);
        body.push(store(bool_ty(lanes), v(2), mask, false));
        body.push(ret(vec![]));
        let module = module_with(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![], body, vec![]);
        assert_layout_refusal(
            translate(&module),
            &bool_ty(lanes),
            "Store",
            &format!("<{lanes} x bool> from <{lanes} x {elem:?}>"),
        );
    }
}

#[test]
fn store_of_a_canonical_mask_constant_is_refused_for_every_shape() {
    for lanes in [16u32, 8, 4, 2] {
        let body = vec![
            InstrNode::new(Inst::Const {
                ty: bool_ty(lanes),
                value: Constant::Vector(
                    (0..lanes)
                        .map(|lane| Constant::Bool(lane % 2 == 0))
                        .collect(),
                ),
            })
            .with_result(v(1)),
            store(bool_ty(lanes), v(0), v(1), false),
            ret(vec![]),
        ];
        let module = module_with(vec![Ty::Ptr], vec![], body, vec![]);
        assert_layout_refusal(
            translate(&module),
            &bool_ty(lanes),
            "Store",
            &format!("canonical <{lanes} x bool> constant"),
        );
    }
}

/// NON-VACUITY: the same store of the compare's own integer vector — the
/// physical shape, same width, same producer chain — still lowers, for the
/// V128 and the V64 carriers alike. The refusal above is the bool-lane gate.
#[test]
fn physical_integer_vector_store_control_still_lowers() {
    for (elem, lanes, _) in producers() {
        let ty = vec_ty(elem.clone(), lanes);
        let body = vec![
            InstrNode::new(Inst::Load {
                ty: ty.clone(),
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(2)),
            store(ty, v(1), v(2), false),
            ret(vec![]),
        ];
        let module = module_with(vec![Ty::Ptr, Ty::Ptr], vec![], body, vec![]);
        translate(&module).unwrap_or_else(|e| {
            panic!("NON-VACUITY: <{lanes} x {elem:?}> load/store must lower: {e}")
        });
    }
}

#[test]
fn load_and_volatile_forms_of_a_bool_mask_are_refused() {
    let mask = bool_ty(8);
    // Load, returned (the return is never reached).
    let body = vec![
        InstrNode::new(Inst::Load {
            ty: mask.clone(),
            ptr: v(0),
            volatile: false,
            align: None,
        })
        .with_result(v(1)),
        ret(vec![v(1)]),
    ];
    assert_layout_refusal(
        translate(&module_with(
            vec![Ty::Ptr],
            vec![mask.clone()],
            body,
            vec![],
        )),
        &mask,
        "Load",
        "Load",
    );
    // VolatileLoad.
    let body = vec![
        InstrNode::new(Inst::Load {
            ty: mask.clone(),
            ptr: v(0),
            volatile: true,
            align: None,
        })
        .with_result(v(1)),
        ret(vec![v(1)]),
    ];
    assert_layout_refusal(
        translate(&module_with(
            vec![Ty::Ptr],
            vec![mask.clone()],
            body,
            vec![],
        )),
        &mask,
        "VolatileLoad",
        "VolatileLoad",
    );
    // VolatileStore of a compare mask.
    let mut body = Vec::new();
    let mut next = 3;
    let value = push_loaded_compare(&mut body, Ty::I16, 8, &mut next);
    body.push(store(mask.clone(), v(2), value, true));
    body.push(ret(vec![]));
    assert_layout_refusal(
        translate(&module_with(
            vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
            vec![],
            body,
            vec![],
        )),
        &mask,
        "VolatileStore",
        "VolatileStore",
    );
}

#[test]
fn atomic_forms_of_a_bool_mask_are_refused_before_any_other_atomic_gate() {
    let mask = bool_ty(4);
    let compare =
        |body: &mut Vec<InstrNode>, next: &mut u32| push_loaded_compare(body, Ty::I32, 4, next);

    let body = vec![
        InstrNode::new(Inst::AtomicLoad {
            ty: mask.clone(),
            ptr: v(0),
            ordering: Ordering::SeqCst,
        })
        .with_result(v(1)),
        ret(vec![v(1)]),
    ];
    assert_layout_refusal(
        translate(&module_with(
            vec![Ty::Ptr],
            vec![mask.clone()],
            body,
            vec![],
        )),
        &mask,
        "AtomicLoad",
        "AtomicLoad",
    );

    let mut body = Vec::new();
    let mut next = 3;
    let value = compare(&mut body, &mut next);
    body.push(InstrNode::new(Inst::AtomicStore {
        ty: mask.clone(),
        ptr: v(2),
        value,
        ordering: Ordering::SeqCst,
    }));
    body.push(ret(vec![]));
    assert_layout_refusal(
        translate(&module_with(
            vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
            vec![],
            body,
            vec![],
        )),
        &mask,
        "AtomicStore",
        "AtomicStore",
    );

    let mut body = Vec::new();
    let mut next = 3;
    let value = compare(&mut body, &mut next);
    body.push(
        InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: mask.clone(),
            ptr: v(2),
            value,
            ordering: Ordering::SeqCst,
        })
        .with_result(v(next)),
    );
    body.push(ret(vec![]));
    assert_layout_refusal(
        translate(&module_with(
            vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
            vec![],
            body,
            vec![],
        )),
        &mask,
        "AtomicRMW",
        "AtomicRMW",
    );

    let mut body = Vec::new();
    let mut next = 3;
    let expected = compare(&mut body, &mut next);
    let desired = compare(&mut body, &mut next);
    body.push(
        InstrNode::new(Inst::CmpXchg {
            ty: mask.clone(),
            ptr: v(2),
            expected,
            desired,
            success: Ordering::SeqCst,
            failure: Ordering::SeqCst,
            weak: false,
        })
        .with_result(v(next)),
    );
    body.push(ret(vec![]));
    assert_layout_refusal(
        translate(&module_with(
            vec![Ty::Ptr, Ty::Ptr, Ty::Ptr],
            vec![],
            body,
            vec![],
        )),
        &mask,
        "CmpXchg",
        "CmpXchg",
    );
}

#[test]
fn alloca_heap_alloc_and_gep_over_a_bool_mask_are_refused() {
    let mask = bool_ty(2);
    let body = vec![
        InstrNode::new(Inst::Alloca {
            ty: mask.clone(),
            count: None,
            align: None,
        })
        .with_result(v(0)),
        ret(vec![v(0)]),
    ];
    assert_layout_refusal(
        translate(&module_with(vec![], vec![Ty::Ptr], body, vec![])),
        &mask,
        "Alloca",
        "Alloca",
    );

    let body = vec![
        InstrNode::new(Inst::HeapAlloc {
            ty: mask.clone(),
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        })
        .with_result(v(0)),
        ret(vec![v(0)]),
    ];
    assert_layout_refusal(
        translate(&module_with(vec![], vec![Ty::Ptr], body, vec![])),
        &mask,
        "HeapAlloc element type",
        "HeapAlloc",
    );

    let body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::GEP {
            pointee_ty: mask.clone(),
            base: v(0),
            indices: vec![v(1)],
            inbounds: true,
        })
        .with_result(v(2)),
        ret(vec![v(2)]),
    ];
    assert_layout_refusal(
        translate(&module_with(vec![Ty::Ptr], vec![Ty::Ptr], body, vec![])),
        &mask,
        "GEP pointee",
        "GEP",
    );
}

// ---------------------------------------------------------------------------
// Aggregates storing a mask by value: refused at type translation
// ---------------------------------------------------------------------------

fn field(name: &str, ty: Ty) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset: None,
    }
}

fn struct_def(id: u32, name: &str, fields: Vec<FieldDef>) -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(id),
        name: name.to_string(),
        fields,
        size: None,
        align: None,
        repr: StructRepr::default(),
    }
}

fn assert_aggregate_refusal(module: &Module, ty: &Ty, mask: &Ty, what: &str) {
    match translate_type_in_module(module, ty) {
        Err(AdapterError::BoolLaneLayoutNotAdmitted {
            ty: got,
            location,
            detail,
        }) => {
            assert_eq!(&got, mask, "{what}: the vector reached");
            assert_eq!(
                location, "an aggregate type's by-value field layout",
                "{what}"
            );
            assert!(
                detail.contains(&format!("stored by value inside {ty:?}")),
                "{what}: the detail names the aggregate: {detail}"
            );
        }
        other => panic!("{what}: expected BoolLaneLayoutNotAdmitted, got {other:?}"),
    }
}

#[test]
fn aggregates_that_store_a_bool_mask_by_value_are_refused_by_name() {
    let mut module = Module::new("aggregates");
    // struct Outer { pad: u8, mask: <8 x bool> }; struct Nest { inner: Outer }
    module.structs.push(struct_def(
        0,
        "Outer",
        vec![field("pad", Ty::U8), field("mask", bool_ty(8))],
    ));
    module.structs.push(struct_def(
        1,
        "Nest",
        vec![field("inner", Ty::Struct(StructId::new(0)))],
    ));
    // types[0] = <4 x bool>; types[1] = Outer; [<4 x bool>; 3]; [Outer; 2]
    module.types.push(bool_ty(4));
    module.types.push(Ty::Struct(StructId::new(0)));
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "MaybeMask",
        vec![
            EnumVariant {
                name: "none".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "some".to_string(),
                fields: vec![bool_ty(16)],
                field_names: vec![],
            },
        ],
    ));
    module.records.push(RecordDef {
        id: RecordId::new(0),
        name: "Rec".to_string(),
        fields: vec![field("mask", bool_ty(2))],
    });
    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.closure_types.push(ClosureTy {
        func: ft,
        captures: vec![Ty::I64, bool_ty(8)],
    });

    assert_aggregate_refusal(
        &module,
        &Ty::Struct(StructId::new(0)),
        &bool_ty(8),
        "struct field",
    );
    assert_aggregate_refusal(
        &module,
        &Ty::Struct(StructId::new(1)),
        &bool_ty(8),
        "nested struct",
    );
    assert_aggregate_refusal(
        &module,
        &Ty::Array(TyId::new(0), 3),
        &bool_ty(4),
        "array element",
    );
    assert_aggregate_refusal(
        &module,
        &Ty::Array(TyId::new(1), 2),
        &bool_ty(8),
        "array of structs",
    );
    assert_aggregate_refusal(
        &module,
        &Ty::Tuple(vec![Ty::I32, bool_ty(4)]),
        &bool_ty(4),
        "tuple element",
    );
    assert_aggregate_refusal(
        &module,
        &Ty::Enum(EnumId::new(0)),
        &bool_ty(16),
        "enum payload",
    );
    assert_aggregate_refusal(
        &module,
        &Ty::Record(RecordId::new(0)),
        &bool_ty(2),
        "record field",
    );
    assert_aggregate_refusal(
        &module,
        &Ty::Closure(trust_ir::ClosureTyId::new(0)),
        &bool_ty(8),
        "closure capture",
    );

    // Controls: a pointer edge is one word and is NOT followed, and the same
    // aggregates with an integer vector in the mask's place still translate.
    assert_eq!(
        translate_type_in_module(
            &module,
            &Ty::Tuple(vec![Ty::PtrConst(Box::new(bool_ty(8)))])
        )
        .unwrap(),
        Type::Struct(vec![Type::I64]),
        "a pointer to a mask is one word"
    );
    assert_eq!(
        translate_type_in_module(&module, &Ty::Tuple(vec![Ty::I32, vec_ty(Ty::I32, 4)])).unwrap(),
        Type::Struct(vec![Type::I32, Type::V128]),
        "NON-VACUITY: the physical vector in the same position translates"
    );
}

// ---------------------------------------------------------------------------
// Carrier mismatch at value boundaries
// ---------------------------------------------------------------------------

fn assert_carrier_mismatch(
    result: Result<(), AdapterError>,
    mask: &Ty,
    location_prefix: &str,
    what: &str,
) {
    match result {
        Err(AdapterError::BoolMaskCarrierMismatch {
            ty,
            location,
            carrier,
            slot,
        }) => {
            assert_eq!(&ty, mask, "{what}: type");
            assert!(
                location.starts_with(location_prefix),
                "{what}: location `{location}` should start with `{location_prefix}`"
            );
            assert_eq!(carrier, Type::V64, "{what}: the <8 x i8> compare's carrier");
            assert_eq!(slot, Type::V128, "{what}: the slot's carrier");
        }
        other => panic!("{what}: expected BoolMaskCarrierMismatch, got {other:?}"),
    }
}

/// `(params: [Ptr, Ptr] ++ extra) -> returns`, the mask produced by a
/// `<8 x elem>` compare of the two loaded pointers, then `tail(mask)`.
fn mask_boundary_module(
    elem: Ty,
    extra_params: Vec<Ty>,
    returns: Vec<Ty>,
    tail: impl FnOnce(ValueId, u32) -> (Vec<InstrNode>, Vec<Block>),
) -> Module {
    let mut body = Vec::new();
    let mut next = 2 + extra_params.len() as u32;
    let mask = push_loaded_compare(&mut body, elem, 8, &mut next);
    let (tail_body, extra_blocks) = tail(mask, next);
    body.extend(tail_body);
    let mut params = vec![Ty::Ptr, Ty::Ptr];
    params.extend(extra_params);
    module_with(params, returns, body, extra_blocks)
}

#[test]
fn v64_mask_returned_through_a_v128_slot_is_refused_and_the_v128_mask_is_not() {
    let mask = bool_ty(8);
    let build = |elem| {
        mask_boundary_module(elem, vec![], vec![mask.clone()], |m, _| {
            (vec![ret(vec![m])], vec![])
        })
    };
    assert_carrier_mismatch(translate(&build(Ty::I8)), &mask, "Return value 0", "Return");
    translate(&build(Ty::I16)).expect("NON-VACUITY: the <8 x i16> compare's V128 mask returns");
}

#[test]
fn v64_mask_passed_as_a_block_argument_is_refused_and_the_v128_mask_is_not() {
    let mask = bool_ty(8);
    let build = |elem| {
        mask_boundary_module(elem, vec![], vec![mask.clone()], |m, next| {
            (
                vec![InstrNode::new(Inst::Br {
                    target: BlockId::new(1),
                    args: vec![m],
                })],
                vec![Block {
                    id: BlockId::new(1),
                    params: vec![(v(next), mask.clone())],
                    body: vec![ret(vec![v(next)])],
                }],
            )
        })
    };
    assert_carrier_mismatch(
        translate(&build(Ty::I8)),
        &mask,
        "block argument 0 to BlockId(1)",
        "block argument",
    );
    translate(&build(Ty::I16)).expect("NON-VACUITY: the V128 mask passes as a block argument");
}

#[test]
fn v64_mask_passed_as_a_call_argument_is_refused_and_the_v128_mask_is_not() {
    let mask = bool_ty(8);
    let build = |elem: Ty| {
        let mut module = Module::new("call_boundary");
        let callee_ft = module
            .add_func_type(FuncTy {
                params: vec![mask.clone()],
                returns: vec![mask.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        // Opaque pass-through: the callee returns its mask parameter.
        let mut callee = Function::new(FuncId::new(1), "callee", callee_ft, BlockId::new(0));
        callee.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), mask.clone())],
            body: vec![ret(vec![v(0)])],
        }];
        let caller_ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr],
                returns: vec![mask.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut caller = Function::new(FuncId::new(0), "caller", caller_ft, BlockId::new(0));
        let mut body = Vec::new();
        let mut next = 2;
        let m = push_loaded_compare(&mut body, elem, 8, &mut next);
        body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![m],
            })
            .with_result(v(next)),
        );
        body.push(ret(vec![v(next)]));
        caller.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)],
            body,
        }];
        module
            .try_add_function(caller)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");
        module
    };
    let translate_all = |module: &Module| -> Result<(), AdapterError> {
        for function in &module.functions {
            trust_cg_lower::translate_function_with_license(
                function,
                module,
                &permit_unlicensed(),
            )?;
        }
        Ok(())
    };
    assert_carrier_mismatch(
        translate_all(&build(Ty::I8)),
        &mask,
        "Call argument 0 of FuncId(1)",
        "call argument",
    );
    translate_all(&build(Ty::I16))
        .expect("NON-VACUITY: the V128 mask passes through a call and its callee returns it");
}

// ---------------------------------------------------------------------------
// The register lane stays admitted
// ---------------------------------------------------------------------------

#[test]
fn bool_masks_remain_register_values_for_compares_constants_and_mask_to_bits() {
    // <8 x i16> compare -> vector.mask_to_bits -> i32.
    let mut body = Vec::new();
    let mut next = 2;
    let mask = push_loaded_compare(&mut body, Ty::I16, 8, &mut next);
    body.push(
        InstrNode::new(Inst::DialectOp(Box::new(vector_dialect::mask_to_bits(
            bool_ty(8),
            mask,
            Ty::I32,
        ))))
        .with_result(v(next)),
    );
    body.push(ret(vec![v(next)]));
    translate(&module_with(
        vec![Ty::Ptr, Ty::Ptr],
        vec![Ty::I32],
        body,
        vec![],
    ))
    .expect("compare -> mask_to_bits stays a register lowering");

    // Canonical <4 x bool> constant returned as a value.
    let body = vec![
        InstrNode::new(Inst::Const {
            ty: bool_ty(4),
            value: Constant::Vector(vec![
                Constant::Bool(true),
                Constant::Bool(false),
                Constant::Bool(true),
                Constant::Bool(true),
            ]),
        })
        .with_result(v(0)),
        ret(vec![v(0)]),
    ];
    translate(&module_with(vec![], vec![bool_ty(4)], body, vec![]))
        .expect("a canonical mask constant stays a register value");

    // A <16 x bool> parameter passed straight back out: an opaque V128.
    let module = module_with(
        vec![bool_ty(16)],
        vec![bool_ty(16)],
        vec![ret(vec![v(0)])],
        vec![],
    );
    translate(&module).expect("a mask parameter is an opaque register pass-through");
}

// ---------------------------------------------------------------------------
// The referee, quoted: one byte per lane, all-ones per true lane
// ---------------------------------------------------------------------------

/// The referee's image for a `<lanes x bool>` mask with `true` at the even
/// lanes, stored into a 0xAA-filled 16-byte buffer read back as two LE u64.
#[test]
fn referee_stores_one_all_ones_byte_per_lane_whatever_the_compare_width() {
    for (elem, lanes, _) in producers() {
        let mut module = Module::new("referee");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U64, Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "referee", ft, BlockId::new(0));
        let ty = vec_ty(elem.clone(), lanes);
        let alternating: Vec<Constant> = (0..lanes)
            .map(|lane| {
                let lane = i128::from(lane);
                Constant::Int(if lane % 2 == 0 { lane } else { -lane })
            })
            .collect();
        let sentinel = Constant::Int(0xAAAA_AAAA_AAAA_AAAA);
        let mut body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::U64,
                count: Some(v(0)),
                align: Some(16),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U64,
                base: v(1),
                indices: vec![v(2)],
                inbounds: true,
            })
            .with_result(v(3)),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: sentinel.clone(),
            })
            .with_result(v(4)),
            store(Ty::U64, v(1), v(4), false),
            store(Ty::U64, v(3), v(4), false),
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Vector(alternating),
            })
            .with_result(v(5)),
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Vector(vec![Constant::Int(0); lanes as usize]),
            })
            .with_result(v(6)),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sge,
                ty,
                lhs: v(5),
                rhs: v(6),
            })
            .with_result(v(7)),
            store(bool_ty(lanes), v(1), v(7), false),
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: v(1),
                volatile: false,
                align: None,
            })
            .with_result(v(8)),
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: v(3),
                volatile: false,
                align: None,
            })
            .with_result(v(9)),
        ];
        body.push(ret(vec![v(8), v(9)]));
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body,
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .expect("the referee executes the mask store");
        let words: Vec<u64> = outcome
            .returns
            .iter()
            .map(|w| u64::try_from(w.as_int().expect("u64").as_unsigned()).unwrap())
            .collect();
        let mut bytes = [0xAAu8; 16];
        for (lane, byte) in bytes.iter_mut().enumerate().take(lanes as usize) {
            *byte = if lane % 2 == 0 { 0xFF } else { 0x00 };
        }
        let expected = [
            u64::from_le_bytes(bytes[..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..].try_into().unwrap()),
        ];
        assert_eq!(
            words, expected,
            "<{lanes} x bool> from <{lanes} x {elem:?}>: the referee writes {lanes} bytes, 0xFF per true lane"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
