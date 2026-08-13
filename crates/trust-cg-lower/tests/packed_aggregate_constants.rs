// packed_aggregate_constants.rs — packed-struct aggregate-constant lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The aggregate-constant path (`translate_aggregate_const` ->
//! `fill_aggregate_at_ptr`) used to address every struct field through
//! `Opcode::StructGep`, which the isel resolves with natural-C
//! `Type::offset_of` (`isel.rs:9306`, `x86_64_isel.rs:13208`). For a
//! `#[repr(packed)]` struct that is the WRONG ADDRESS: `packed_struct_layout`
//! — the authority behind `packed_field_offset` (GEP / field insert / field
//! extract) and `packed_struct_size` (array stride) — puts field 1 of
//! `#[repr(packed)] { a: u8, b: u64 }` at byte 1, while `Type::offset_of` puts
//! it at byte 8.
//!
//! That was a live wrong-value miscompile, not a latent one. `trust-thir-lower`
//! decodes a CTFE valtree straight into `Constant::Aggregate` under a packed
//! `Ty::Struct` (`crate_module.rs:3160-3172`) with no `InsertField` chain to
//! overwrite the seed, so
//!
//! ```text
//! #[repr(packed)] pub struct P { pub a: u8, pub b: u64 }
//! pub const K: P = P { a: 7, b: 0x1122334455667788 };
//! pub fn read_k() -> u64 { K.b }
//! ```
//!
//! stored the u64 at slot+8 (const path) and loaded it from slot+1 (the packed
//! `ExtractField` path), reading seven never-written stack bytes.
//!
//! These tests pin the repair AND its blast radius:
//!
//! * a packed aggregate constant addresses its fields at
//!   `packed_struct_layout`'s offsets, with `align: Some(1)` stores;
//! * a NON-packed aggregate constant emits a byte-identical instruction
//!   stream to the one it emitted before the repair — the new branch is gated
//!   on `is_packed_struct_ty`, so nothing else can reach it;
//! * the stack slot deliberately stays at the LIR type's natural-C size (see
//!   `slot_for_a_packed_aggregate_const_stays_at_the_lir_type_size`).

use trust_cg_lower::adapter::translate_function;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FieldDef, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, StructDef, StructId,
    StructRepr, Ty, ValueId,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset,
    }
}

/// `{ a: u8, b: u64 }` under `repr`. Under `Packed(1)` the producer's own
/// layout is `offsets [0, 1] size 9 align 1`; under `Rust`/`C` it is
/// `offsets [0, 8] size 16 align 8`.
fn u8_u64_struct(name: &str, repr: StructRepr, offsets: [Option<u64>; 2]) -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: name.to_string(),
        fields: vec![
            field("a", Ty::U8, offsets[0]),
            field("b", Ty::U64, offsets[1]),
        ],
        size: None,
        align: None,
        repr,
    }
}

/// A one-block function whose body is `%0 = const <ty> {7, 0x1122334455667788};
/// ret %0`.
fn const_then_return(sdef: StructDef) -> TrustIrModule {
    let struct_ty = Ty::Struct(sdef.id);
    let mut module = TrustIrModule::new("k");
    module.structs = vec![sdef];
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![struct_ty.clone()],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: struct_ty,
                value: Constant::Aggregate(vec![
                    Constant::Int(7),
                    Constant::Int(0x1122_3344_5566_7788),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![v(0)] }),
        ],
    }];
    module.add_function(func);
    module
}

fn lower(module: &TrustIrModule) -> Vec<Opcode> {
    let func = module
        .functions
        .first()
        .expect("the fixture module holds exactly one function");
    let (lir_func, _proofs) =
        translate_function(func, module).expect("adapter must accept the aggregate constant");
    let entry = lir_func.entry_block;
    lir_func.blocks[&entry]
        .instructions
        .iter()
        .map(|i| i.opcode.clone())
        .collect()
}

// ---------------------------------------------------------------------------
// The repair
// ---------------------------------------------------------------------------

/// A `#[repr(packed)]` aggregate constant must address `b` at byte 1 — the
/// offset `packed_struct_layout` gives, and the one the packed `ExtractField`
/// path (`adapter.rs:11656-11683`) reads back from — not the natural-C byte 8
/// a `StructGep` on `Struct([I8, I64])` resolves to.
#[test]
fn packed_aggregate_const_addresses_fields_at_packed_offsets() {
    let opcodes = lower(&const_then_return(u8_u64_struct(
        "P",
        StructRepr::Packed(1),
        [Some(0), Some(1)],
    )));

    assert!(
        !opcodes
            .iter()
            .any(|op| matches!(op, Opcode::StructGep { .. })),
        "a packed struct field must NOT be addressed through StructGep — the isel resolves \
         it with natural-C `Type::offset_of`. Got {opcodes:?}"
    );

    // An OFFSET constant is an `Iconst` consumed by the following `Iadd`;
    // filtering on `Iconst { ty: I64 }` alone would also collect the u64 field
    // VALUE, which is not an address.
    let offsets: Vec<i64> = opcodes
        .windows(2)
        .filter_map(|w| match (&w[0], &w[1]) {
            (Opcode::Iconst { ty: Type::I64, imm }, Opcode::Iadd) => Some(*imm),
            _ => None,
        })
        .collect();
    assert_eq!(
        offsets,
        vec![0, 1],
        "field offsets must be authority P's [0, 1], got {opcodes:?}"
    );

    let stores: Vec<(Type, Option<u32>)> = opcodes
        .iter()
        .filter_map(|op| match op {
            Opcode::Store { ty, align } => Some((ty.clone(), *align)),
            _ => None,
        })
        .collect();
    assert_eq!(
        stores,
        vec![(Type::I8, Some(1)), (Type::I64, Some(1))],
        "a packed field may be UNALIGNED, so its store must declare align 1 exactly as the \
         packed InsertField path (`adapter.rs:6963`) does. Got {opcodes:?}"
    );

    let iadds = opcodes
        .iter()
        .filter(|op| matches!(op, Opcode::Iadd))
        .count();
    assert_eq!(iadds, 2, "one base+offset Iadd per field, got {opcodes:?}");
}

/// A packed struct NESTED inside a packed struct. `fill_aggregate_at_ptr`
/// recurses into a nested aggregate field using the parent's field pointer as
/// the sub-aggregate's base and no fresh slot, so the offsets must COMPOSE:
/// for `#[repr(packed)] N { h: u8, inner: P }` with `P { a: u8, b: u64 }`,
/// `N.inner` is at byte 1 and `N.inner.b` at byte 1 + 1 = 2 — which is
/// rustc's own layout. Before the repair the const path put `N.inner` at the
/// natural byte 8 and `N.inner.b` at 8 + 8 = 16, a 14-byte error.
///
/// The writes must also all land inside the natural-C slot, which they do:
/// the deepest byte written is `2 + 8 = 10` and the slot is 24 bytes.
#[test]
fn nested_packed_aggregate_const_composes_packed_offsets() {
    let inner = StructDef {
        id: StructId::new(0),
        name: "P".to_string(),
        fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
        size: Some(9),
        align: Some(1),
        repr: StructRepr::Packed(1),
    };
    let outer = StructDef {
        id: StructId::new(1),
        name: "N".to_string(),
        fields: vec![
            field("h", Ty::U8, Some(0)),
            field("inner", Ty::Struct(StructId::new(0)), Some(1)),
        ],
        size: Some(10),
        align: Some(1),
        repr: StructRepr::Packed(1),
    };
    let outer_ty = Ty::Struct(StructId::new(1));

    let mut module = TrustIrModule::new("n");
    module.structs = vec![inner, outer];
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![outer_ty.clone()],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "n", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: outer_ty,
                value: Constant::Aggregate(vec![
                    Constant::Int(3),
                    Constant::Aggregate(vec![
                        Constant::Int(7),
                        Constant::Int(0x1122_3344_5566_7788),
                    ]),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![v(0)] }),
        ],
    }];
    module.add_function(func);

    let opcodes = lower(&module);
    assert!(
        !opcodes
            .iter()
            .any(|op| matches!(op, Opcode::StructGep { .. })),
        "neither the outer nor the inner packed struct may use StructGep, got {opcodes:?}"
    );
    // The inner base is `N + 1`; the inner fields then add 0 and 1 to THAT.
    let offsets: Vec<i64> = opcodes
        .windows(2)
        .filter_map(|w| match (&w[0], &w[1]) {
            (Opcode::Iconst { ty: Type::I64, imm }, Opcode::Iadd) => Some(*imm),
            _ => None,
        })
        .collect();
    assert_eq!(
        offsets,
        vec![0, 1, 0, 1],
        "N.h at +0, N.inner at +1, then P.a at +0 and P.b at +1 relative to the inner base \
         (absolute byte 2). Got {opcodes:?}"
    );
    assert_eq!(
        opcodes
            .iter()
            .filter(|op| matches!(op, Opcode::Store { align: Some(1), .. }))
            .count(),
        3,
        "all three scalar stores are into packed structs and must declare align 1, \
         got {opcodes:?}"
    );
}

/// The full emitted stream for the packed case, pinned exactly. Any future
/// change to the packed aggregate-constant shape has to come through here.
#[test]
fn packed_aggregate_const_full_stream() {
    let opcodes = lower(&const_then_return(u8_u64_struct(
        "P",
        StructRepr::Packed(1),
        [Some(0), Some(1)],
    )));
    let expected = vec![
        Opcode::StackAddr { slot: 0 },
        Opcode::Iconst {
            ty: Type::I64,
            imm: 0,
        },
        Opcode::Iadd,
        Opcode::Iconst {
            ty: Type::I8,
            imm: 7,
        },
        Opcode::Store {
            ty: Type::I8,
            align: Some(1),
        },
        Opcode::Iconst {
            ty: Type::I64,
            imm: 1,
        },
        Opcode::Iadd,
        Opcode::Iconst {
            ty: Type::I64,
            imm: 0x1122_3344_5566_7788,
        },
        Opcode::Store {
            ty: Type::I64,
            align: Some(1),
        },
        Opcode::Return,
    ];
    assert_eq!(opcodes, expected);
}

// ---------------------------------------------------------------------------
// THE MISCOMPILE ITSELF — write address must equal read address
// ---------------------------------------------------------------------------

/// THE ACCEPTANCE TEST. This is the `read_k()` shape end to end:
///
/// ```text
/// %0 = const struct.0 { 7, 0x1122334455667788 }   (packed P { a: u8, b: u64 })
/// %1 = extractfield u64 %0, 1
/// ret %1
/// ```
///
/// The const path WRITES field 1 and the `ExtractField` path READS it. Before
/// the repair the write went to `StructGep(Struct([I8, I64]), 1)` = byte 8 and
/// the read to `base + 1`, so `read_k()` returned seven never-written stack
/// bytes under the field's low byte. Both addresses must be the same byte
/// offset from the slot base, and it must be authority P's offset 1.
///
/// This is stronger than either address in isolation: it fails if the write
/// moves, if the read moves, or if the two ever disagree again.
#[test]
fn packed_const_write_address_equals_packed_read_address() {
    let sdef = u8_u64_struct("P", StructRepr::Packed(1), [Some(0), Some(1)]);
    let struct_ty = Ty::Struct(sdef.id);
    let mut module = TrustIrModule::new("read_k");
    module.structs = vec![sdef];
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::U64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "read_k", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: struct_ty.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Int(7),
                    Constant::Int(0x1122_3344_5566_7788),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::ExtractField {
                ty: struct_ty,
                aggregate: v(0),
                field: 1,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    }];
    module.add_function(func);

    let (lir_func, _proofs) =
        translate_function(module.functions.first().expect("one function"), &module)
            .expect("adapter must accept const-aggregate + packed field extract");
    let bb = &lir_func.blocks[&lir_func.entry_block];

    // The slot base is the single `StackAddr` result; every field address is
    // `base + Iconst`. Walk the stream resolving each `Iadd` on the base into
    // the byte offset its `Iconst` operand carries.
    let base = bb
        .instructions
        .iter()
        .find(|i| matches!(i.opcode, Opcode::StackAddr { .. }))
        .and_then(|i| i.results.first().copied())
        .expect("the aggregate constant allocates one slot");

    let mut offset_of_value = std::collections::HashMap::new();
    let mut const_of_value = std::collections::HashMap::new();
    let mut store_i64_offsets = Vec::new();
    let mut load_i64_offsets = Vec::new();
    for inst in &bb.instructions {
        match &inst.opcode {
            Opcode::Iconst { imm, .. } => {
                if let Some(r) = inst.results.first() {
                    const_of_value.insert(*r, *imm);
                }
            }
            Opcode::Iadd => {
                if let (Some(&a), Some(&b), Some(r)) =
                    (inst.args.first(), inst.args.get(1), inst.results.first())
                    && a == base
                    && let Some(off) = const_of_value.get(&b)
                {
                    offset_of_value.insert(*r, *off);
                }
            }
            Opcode::StructGep { .. } => {
                panic!("no packed field address may go through StructGep: {bb:?}");
            }
            Opcode::Store { ty: Type::I64, .. } => {
                let ptr = inst.args.get(1).expect("Store takes value, ptr");
                store_i64_offsets.push(offset_of_value.get(ptr).copied());
            }
            Opcode::Load { ty: Type::I64, .. } => {
                let ptr = inst.args.first().expect("Load takes ptr");
                load_i64_offsets.push(offset_of_value.get(ptr).copied());
            }
            _ => {}
        }
    }

    assert_eq!(
        store_i64_offsets,
        vec![Some(1)],
        "the const path must WRITE `b` at authority P's byte 1"
    );
    assert_eq!(
        load_i64_offsets,
        vec![Some(1)],
        "the ExtractField path must READ `b` at authority P's byte 1"
    );
    assert_eq!(
        store_i64_offsets, load_i64_offsets,
        "the byte a packed field is written to and the byte it is read from must be the SAME \
         byte — the divergence between them is the miscompile"
    );
}

// ---------------------------------------------------------------------------
// NON-PACKED INVARIANCE — the blast-radius pin
// ---------------------------------------------------------------------------

/// BYTE-IDENTICAL CONTROL. The repair adds a branch gated on
/// `is_packed_struct_ty`, which is `false` for every `Ty::Tuple`, `Ty::Record`,
/// `Ty::Array` and for a `Ty::Struct` whose `repr` is not `Packed`. This pins
/// the exact pre-repair stream for the SAME field types under `repr(Rust)`:
/// `StructGep` on `Struct([I8, I64])`, natural-C offsets, `align: None`
/// stores. (c) MEASURED against HEAD before the repair — this assertion
/// passed unchanged on both sides of it.
#[test]
fn non_packed_aggregate_const_stream_is_unchanged() {
    for repr in [StructRepr::Rust, StructRepr::C, StructRepr::Transparent] {
        let opcodes = lower(&const_then_return(u8_u64_struct(
            "NotPacked",
            repr,
            [Some(0), Some(8)],
        )));
        let expected = vec![
            Opcode::StackAddr { slot: 0 },
            Opcode::StructGep {
                struct_ty: Type::Struct(vec![Type::I8, Type::I64]),
                field_index: 0,
            },
            Opcode::Iconst {
                ty: Type::I8,
                imm: 7,
            },
            Opcode::Store {
                ty: Type::I8,
                align: None,
            },
            Opcode::StructGep {
                struct_ty: Type::Struct(vec![Type::I8, Type::I64]),
                field_index: 1,
            },
            Opcode::Iconst {
                ty: Type::I64,
                imm: 0x1122_3344_5566_7788,
            },
            Opcode::Store {
                ty: Type::I64,
                align: None,
            },
            Opcode::Return,
        ];
        assert_eq!(
            opcodes, expected,
            "{repr:?}: a non-packed aggregate constant must emit exactly what it emitted \
             before the packed repair"
        );
    }
}

/// A tuple constant with the same field types also never enters the packed
/// branch: `is_packed_struct_ty` is `false` for `Ty::Tuple`.
#[test]
fn tuple_aggregate_const_stream_is_unchanged() {
    let tuple_ty = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let mut module = TrustIrModule::new("t");
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![tuple_ty.clone()],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "t", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: tuple_ty,
                value: Constant::Aggregate(vec![Constant::Int(7), Constant::Int(9)]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![v(0)] }),
        ],
    }];
    module.add_function(func);

    let opcodes = lower(&module);
    assert_eq!(
        opcodes
            .iter()
            .filter(|op| matches!(op, Opcode::StructGep { .. }))
            .count(),
        2,
        "a tuple constant still uses StructGep, got {opcodes:?}"
    );
    assert!(
        opcodes
            .iter()
            .all(|op| !matches!(op, Opcode::Store { align: Some(_), .. })),
        "a tuple field store must keep its natural alignment, got {opcodes:?}"
    );
}

// ---------------------------------------------------------------------------
// The slot is deliberately NOT shrunk
// ---------------------------------------------------------------------------

/// The stack slot stays at the LIR type's natural-C size (16 / 8 for
/// `Struct([I8, I64])`) even though authority P says the packed struct is 9/1.
///
/// This is a DELIBERATE over-allocation, not an oversight, and it is the
/// bounded half of the repair:
///
/// * the LIR `Type` carries no repr (`types.rs`, `Type::Struct(Vec<Type>)`),
///   so the consumers of the resulting pointer that still measure an EXTENT
///   do so with `Type::bytes()` — the aggregate-field `Memmove` on the
///   NON-packed `InsertField` arm, the aggregate `Load` slot and copy length,
///   the alloca/heap element stride, and the C ABI classifier. Shrinking this
///   slot to 9 while those still copy 16 bytes would trade a wrong-value bug
///   for an out-of-bounds read AND write. (The packed `InsertField` arm and
///   the aggregate `Store` arm no longer do: the nested-packed repair moved
///   both onto `packed_struct_size` via `aggregate_value_extent`, because
///   shrinking a packed struct's own layout moves the NEXT sibling down and a
///   natural-C-lengthed copy would then clobber it. See
///   `tests/packed_nested_layout.rs`.);
/// * the over-allocation is provably safe in the other direction: the packed
///   clamp `min(true_align, N)` only ever LOWERS an alignment, the packed
///   extent only ever lowers a size, and both `N` and every alignment are
///   powers of two, so authority P's offsets, size and align are pointwise <=
///   authority C's. The natural-C slot therefore always contains the packed
///   extent. See
///   `layout_refusal::tests::test_packed_authority_is_dominated_by_natural_c`
///   and `adapter::tests::nested_packed_layout_is_dominated_by_the_natural_c_layout`.
#[test]
fn slot_for_a_packed_aggregate_const_stays_at_the_lir_type_size() {
    let module = const_then_return(u8_u64_struct(
        "P",
        StructRepr::Packed(1),
        [Some(0), Some(1)],
    ));
    let func = module.functions.first().expect("one function");
    let (lir_func, _proofs) = translate_function(func, &module).expect("adapter must accept");
    assert_eq!(lir_func.stack_slots.len(), 1);
    assert_eq!(
        (lir_func.stack_slots[0].size, lir_func.stack_slots[0].align),
        (16, 8),
        "the slot is sized from the LIR type, which every extent-measuring consumer also uses"
    );
}

// ---------------------------------------------------------------------------
// WHAT THIS REPAIR DOES **NOT** FIX — pinned so it cannot be forgotten
// ---------------------------------------------------------------------------

/// SURVIVING DIVERGENCE (`Inst::Alloca` vs `Inst::GEP` stride).
///
/// This repair moved the aggregate-constant path's FIELD OFFSETS onto
/// `packed_struct_layout`. It did NOT unify the packed struct's total SIZE:
/// `translate_alloc` (`adapter.rs:8961-8966`) still sizes an alloca element
/// with natural-C `lir_ty.bytes()`/`lir_ty.align()`, while `Inst::GEP` over
/// the very same pointer strides by `packed_struct_size`
/// (`adapter.rs:6325-6326`). For `#[repr(packed)] { a: u8, b: u64 }` that is
/// 16 versus 9.
///
/// So a packed struct still has TWO size authorities, and
/// `layout_refusal::classify_struct_layout` correctly still refuses to score
/// one. This test states the surviving gap as a measurement rather than
/// letting the repair be mistaken for a full collapse; when the alloca stride
/// is moved onto the packed authority, this assertion is what has to change.
#[test]
fn alloca_stride_for_a_packed_struct_still_disagrees_with_gep_stride() {
    let sdef = u8_u64_struct("P", StructRepr::Packed(1), [Some(0), Some(1)]);
    let struct_ty = Ty::Struct(sdef.id);
    let mut module = TrustIrModule::new("alloc2");
    module.structs = vec![sdef];
    let fty_id: FuncTyId = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "alloc2", fty_id, b(0));
    func.blocks = vec![TrustIrBlock {
        id: b(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Alloca {
                ty: struct_ty,
                count: Some(v(0)),
                align: None,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module.add_function(func);

    let (lir_func, _proofs) =
        translate_function(module.functions.first().expect("one function"), &module)
            .expect("adapter must accept the alloca");
    assert_eq!(
        (lir_func.stack_slots[0].size, lir_func.stack_slots[0].align),
        (32, 8),
        "`Inst::Alloca` still strides a packed element by its NATURAL 16 bytes; the packed \
         authority says 9, and `Inst::GEP` over the same pointer uses 9. Two size authorities \
         survive this repair"
    );
}
