// array_splat_lowering.rs - trust-ir v50 `Inst::ArraySplat` / `Constant::Splat`
// lowering in the trust-cg-lower adapter.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// A uniform array `[v; n]` must lower in CONSTANT size in `n`: one `Memset`
// when the element's whole image is one repeated byte, otherwise one write of
// lane 0 and a doubling copy (`ceil(log2 n)` `Memcpy`s, at most 64 for any
// u64 `n`). Nothing may store per lane.
//
// Every test here compares a small and a HUGE lane count by the LIR the
// adapter emits — instruction census, stack-slot size and the byte offsets and
// counts the copies carry. None runs the code or allocates per lane: a
// regression to per-lane unrolling fails on the census long before it could
// exhaust memory.

use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::instructions::{Opcode, Value};
use trust_ir::{
    Block, BlockId, Constant, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    StructDef, StructId, StructRepr, Ty, TyId, ValueId,
};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

#[path = "common/below_admission.rs"]
mod below_admission;
use below_admission::body_refusal_below_admission;

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

/// `f(params) -> ret` whose single block is `body` then `return result`.
fn module(
    types: Vec<Ty>,
    params: Vec<(ValueId, Ty)>,
    ret: Ty,
    body: Vec<InstrNode>,
    result: ValueId,
) -> Module {
    let mut module = Module::new("array_splat_lowering");
    module.types = types;
    let ty = module
        .add_func_type(FuncTy {
            params: params.iter().map(|(_, ty)| ty.clone()).collect(),
            returns: vec![ret],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "f", ty, BlockId::new(0));
    let mut body = body;
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params,
        body,
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn lower(module: &Module) -> Result<LirFunction, String> {
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .map(|(func, _proofs)| func)
    .map_err(|err| err.to_string())
}

/// What the lowering emitted, by the opcodes a lane write can take.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct Census {
    memset: usize,
    memcpy: usize,
    memmove: usize,
    stores: usize,
    total: usize,
    largest_slot: u32,
}

fn census(func: &LirFunction) -> Census {
    let mut census = Census {
        largest_slot: func
            .stack_slots
            .iter()
            .map(|slot| slot.size)
            .max()
            .unwrap_or(0),
        ..Census::default()
    };
    for block in func.blocks.values() {
        for inst in &block.instructions {
            census.total += 1;
            match inst.opcode {
                Opcode::Memset => census.memset += 1,
                Opcode::Memcpy => census.memcpy += 1,
                Opcode::Memmove => census.memmove += 1,
                Opcode::Store { .. } => census.stores += 1,
                _ => {}
            }
        }
    }
    census
}

/// The immediate an `Iconst` defining `value` carries.
fn iconst(func: &LirFunction, value: Value) -> i64 {
    func.blocks
        .values()
        .flat_map(|block| &block.instructions)
        .find_map(|inst| match inst.opcode {
            Opcode::Iconst { imm, .. } if inst.results.contains(&value) => Some(imm),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{value:?} is not an Iconst"))
}

/// `(destination offset from the slot base, byte count)` of every `Memcpy`, in
/// emission order: `Memcpy(base + off, base, count)`.
fn copies(func: &LirFunction) -> Vec<(i64, i64)> {
    let insts: Vec<_> = func
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .collect();
    insts
        .iter()
        .filter(|inst| matches!(inst.opcode, Opcode::Memcpy))
        .map(|copy| {
            let dst = copy.args[0];
            let add = insts
                .iter()
                .find(|inst| matches!(inst.opcode, Opcode::Iadd) && inst.results.contains(&dst))
                .expect("a doubling copy's destination is base + offset");
            assert_eq!(add.args[0], copy.args[1], "the copy reads the slot base");
            (iconst(func, add.args[1]), iconst(func, copy.args[2]))
        })
        .collect()
}

/// `(fill byte, byte count)` of the one `Memset`.
fn memset(func: &LirFunction) -> (i64, i64) {
    let set = func
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .find(|inst| matches!(inst.opcode, Opcode::Memset))
        .expect("one Memset");
    (iconst(func, set.args[1]), iconst(func, set.args[2]))
}

fn ceil_log2(n: u64) -> usize {
    (64 - (n - 1).leading_zeros()) as usize
}

/// The copies a doubling fill of `n` lanes at `stride` bytes must make.
fn doubling(n: u64, stride: u64) -> Vec<(i64, i64)> {
    let mut done = 1u64;
    let mut out = Vec::new();
    while done < n {
        let chunk = done.min(n - done);
        out.push(((done * stride) as i64, (chunk * stride) as i64));
        done += chunk;
    }
    out
}

/// `f(x: u32, i: u64) -> u32 { [x; n][i] }`.
fn register_splat_u32(n: u64) -> Module {
    module(
        vec![Ty::U32],
        vec![(v(0), Ty::U32), (v(1), Ty::U64)],
        Ty::U32,
        vec![
            InstrNode::new(Inst::ArraySplat {
                ty: Ty::Array(TyId::new(0), n),
                value: v(0),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::U32,
                array: v(2),
                index: v(1),
            })
            .with_result(v(3)),
        ],
        v(3),
    )
}

/// `f(i: u64) -> elem { const [elem; n] = splat[ value; n ] ; [..][i] }`.
fn constant_splat(elem: Ty, value: Constant, n: u64) -> Module {
    module(
        vec![elem.clone()],
        vec![(v(0), Ty::U64)],
        elem.clone(),
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Array(TyId::new(0), n),
                value: Constant::Splat {
                    elem: Box::new(value),
                    len: n,
                },
            })
            .with_result(v(1)),
            InstrNode::new(Inst::ExtractElement {
                ty: elem,
                array: v(1),
                index: v(0),
            })
            .with_result(v(2)),
        ],
        v(2),
    )
}

/// A register element that is no constant: one store into lane 0, then the
/// doubling copy. The census grows by one copy (four instructions) per
/// doubling of `n`, and the stack slot is exactly `4 n` bytes.
#[test]
fn register_splat_is_one_store_and_a_doubling_copy() {
    let small = lower(&register_splat_u32(1024)).expect("[u32; 1024]");
    let huge_n = (1u64 << 30) - 1; // 4 * n still fits one stack slot
    let huge = lower(&register_splat_u32(huge_n)).expect("[u32; 2^30 - 1]");
    for (func, n) in [(&small, 1024u64), (&huge, huge_n)] {
        let census = census(func);
        assert_eq!(census.stores, 1, "n = {n}: {census:?}");
        assert_eq!(census.memset, 0, "n = {n}: {census:?}");
        assert_eq!(census.memmove, 0, "n = {n}: {census:?}");
        assert_eq!(census.memcpy, ceil_log2(n), "n = {n}: {census:?}");
        assert_eq!(u64::from(census.largest_slot), 4 * n, "n = {n}: {census:?}");
        assert_eq!(copies(func), doubling(n, 4), "n = {n}");
    }
    let (small, huge) = (census(&small), census(&huge));
    assert_eq!(
        huge.total - small.total,
        4 * (ceil_log2(huge_n) - ceil_log2(1024)),
        "{small:?} vs {huge:?}: the only growth is the doubling steps"
    );
    for n in [1, 2, 3] {
        let census = census(&lower(&register_splat_u32(n)).expect("small n"));
        assert_eq!(census.memcpy, ceil_log2(n.max(1)), "n = {n}: {census:?}");
        assert_eq!(census.stores, 1, "n = {n}: {census:?}");
    }
}

/// Offsets and counts are u64 byte arithmetic: the doubling of
/// `[u8; 2^32 - 1]` copies to offset 2^31 and moves `2^32 - 1 - 2^31` bytes in
/// its last step — a u32 or i32 offset would wrap there.
#[test]
fn doubling_offsets_do_not_wrap_at_32_bits() {
    let n = u64::from(u32::MAX);
    let func = lower(&module(
        vec![Ty::U8],
        vec![(v(0), Ty::U8), (v(1), Ty::U64)],
        Ty::U8,
        vec![
            InstrNode::new(Inst::ArraySplat {
                ty: Ty::Array(TyId::new(0), n),
                value: v(0),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::U8,
                array: v(2),
                index: v(1),
            })
            .with_result(v(3)),
        ],
        v(3),
    ))
    .expect("[u8; 2^32 - 1]");
    let copies = copies(&func);
    assert_eq!(copies, doubling(n, 1));
    assert_eq!(copies.last(), Some(&(1i64 << 31, (1i64 << 31) - 1)));
    assert_eq!(census(&func).largest_slot, u32::MAX);
}

/// An array whose byte extent passes what the u32 LIR carrier (and so one
/// stack slot) can describe is refused by name — its u64 extent is never
/// truncated to a smaller slot (the carrier type's own size saturates at
/// `u32::MAX`, so sizing from it would under-allocate a slot the fill then
/// overruns).
#[test]
fn an_extent_past_a_stack_slot_is_refused_not_truncated() {
    let refused_by_name = |error: &str| {
        error.contains("does not fit the u32 LIR carrier") || error.contains("beyond a stack slot")
    };
    let error = lower(&register_splat_u32(1 << 30)).expect_err("4 GiB of u32 lanes");
    assert!(refused_by_name(&error), "{error}");
    let error =
        lower(&constant_splat(Ty::U64, Constant::Int(0), 1 << 29)).expect_err("4 GiB of u64 lanes");
    assert!(refused_by_name(&error), "{error}");
}

/// A constant element whose whole image is one repeated byte fills the array
/// with ONE memset of `n * stride` bytes, whatever `n` is.
#[test]
fn byte_uniform_constant_splat_is_one_memset() {
    let cases: Vec<(Ty, Constant, u64, i64)> = vec![
        (Ty::U64, Constant::Int(0), 8, 0),
        (Ty::I32, Constant::Int(-1), 4, 0xFF),
        (Ty::U16, Constant::Int(0x0101), 2, 1),
        (Ty::U8, Constant::Int(0xAB), 1, 0xAB),
        (Ty::Bool, Constant::Bool(true), 1, 1),
        (Ty::F64, Constant::Float(0.0), 8, 0),
        (Ty::I128, Constant::Int(0), 16, 0),
    ];
    for (elem, value, stride, byte) in cases {
        for n in [2u64, 3, 1 << 20, ((1u64 << 32) - 1) / stride] {
            let func = lower(&constant_splat(elem.clone(), value.clone(), n))
                .unwrap_or_else(|err| panic!("{elem:?} x {n}: {err}"));
            let census = census(&func);
            assert_eq!(census.memset, 1, "{elem:?} x {n}: {census:?}");
            assert_eq!(census.stores, 0, "{elem:?} x {n}: {census:?}");
            assert_eq!(census.memcpy, 0, "{elem:?} x {n}: {census:?}");
            assert_eq!(memset(&func), (byte, (n * stride) as i64), "{elem:?} x {n}");
        }
    }
    // Two lane counts, one census.
    let small = census(&lower(&constant_splat(Ty::U64, Constant::Int(0), 2)).unwrap());
    let huge = census(&lower(&constant_splat(Ty::U64, Constant::Int(0), 1 << 28)).unwrap());
    assert_eq!(
        Census {
            largest_slot: 0,
            ..small
        },
        Census {
            largest_slot: 0,
            ..huge
        }
    );
}

/// A constant element with a mixed-byte image is written once, then copied by
/// doubling.
#[test]
fn non_uniform_constant_splat_writes_lane_zero_once() {
    for n in [2u64, 3, 1000, (1 << 30) - 1] {
        let func = lower(&constant_splat(Ty::U32, Constant::Int(1), n)).expect("[1u32; n]");
        let census = census(&func);
        assert_eq!(census.stores, 1, "n = {n}: {census:?}");
        assert_eq!(census.memset, 0, "n = {n}: {census:?}");
        assert_eq!(copies(&func), doubling(n, 4), "n = {n}");
    }
    // A float other than +0.0 has no one-byte image.
    let census = census(&lower(&constant_splat(Ty::F32, Constant::Float(1.5), 1 << 20)).unwrap());
    assert_eq!((census.memset, census.stores, census.memcpy), (0, 1, 20));
}

/// A register splat of a CONSTANT byte-uniform value is the memset too.
#[test]
fn register_splat_of_a_byte_uniform_constant_is_one_memset() {
    for n in [2u64, 1 << 31] {
        let func = lower(&module(
            vec![Ty::U8],
            vec![(v(0), Ty::U64)],
            Ty::U8,
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::U8,
                    value: Constant::Int(7),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::ArraySplat {
                    ty: Ty::Array(TyId::new(0), n),
                    value: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::ExtractElement {
                    ty: Ty::U8,
                    array: v(2),
                    index: v(0),
                })
                .with_result(v(3)),
            ],
            v(3),
        ))
        .expect("[7u8; n]");
        let census = census(&func);
        assert_eq!(
            (census.memset, census.stores, census.memcpy),
            (1, 0, 0),
            "{census:?}"
        );
        assert_eq!(memset(&func), (7, n as i64));
    }
}

fn pair_struct() -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::U8,
                offset: None,
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    }
}

/// A pointer-represented element: lane 0 is a copy of the operand's own
/// 16-byte extent (never its address), then the doubling copy at stride 16.
#[test]
fn aggregate_element_splat_copies_lane_zero_then_doubles() {
    let pair = Ty::Struct(StructId::new(0));
    for n in [2u64, 5, (1 << 28) - 1] {
        let mut module = module(
            vec![pair.clone()],
            vec![(v(0), pair.clone()), (v(1), Ty::U64)],
            Ty::U64,
            vec![
                InstrNode::new(Inst::ArraySplat {
                    ty: Ty::Array(TyId::new(0), n),
                    value: v(0),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::ExtractElement {
                    ty: pair.clone(),
                    array: v(2),
                    index: v(1),
                })
                .with_result(v(3)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::U64,
                    aggregate: v(3),
                    field: 1,
                })
                .with_result(v(4)),
            ],
            v(4),
        );
        module.add_struct(pair_struct());
        let func = lower(&module).unwrap_or_else(|err| panic!("[Pair; {n}]: {err}"));
        let census = census(&func);
        assert!(census.memmove >= 1, "n = {n}: {census:?}");
        assert_eq!(census.memset, 0, "n = {n}: {census:?}");
        assert_eq!(copies(&func), doubling(n, 16), "n = {n}");
    }
}

/// A splat nested in an aggregate constant fills in place: the tuple's `u8`
/// and lane 0 are the only stores; a zero splat field is one memset.
#[test]
fn splat_nested_in_an_aggregate_constant_fills_in_place() {
    for (value, n, uniform) in [
        (Constant::Int(1), 9u64, false),
        (Constant::Int(1), (1 << 29) - 1, false),
        (Constant::Int(0), (1 << 29) - 1, true),
    ] {
        let tuple = Ty::Tuple(vec![Ty::U8, Ty::Array(TyId::new(0), n)]);
        let func = lower(&module(
            vec![Ty::U32],
            vec![],
            Ty::U8,
            vec![
                InstrNode::new(Inst::Const {
                    ty: tuple.clone(),
                    value: Constant::Aggregate(vec![
                        Constant::Int(9),
                        Constant::Splat {
                            elem: Box::new(value.clone()),
                            len: n,
                        },
                    ]),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::ExtractField {
                    ty: Ty::U8,
                    aggregate: v(0),
                    field: 0,
                })
                .with_result(v(1)),
            ],
            v(1),
        ))
        .unwrap_or_else(|err| panic!("{value:?} x {n}: {err}"));
        let census = census(&func);
        if uniform {
            assert_eq!(
                (census.memset, census.stores, census.memcpy),
                (1, 1, 0),
                "{census:?}"
            );
        } else {
            assert_eq!(census.memset, 0, "{census:?}");
            assert_eq!(census.stores, 2, "{census:?}");
            assert_eq!(census.memcpy, ceil_log2(n), "{census:?}");
        }
    }
}

/// A splat of splats: `[[0x1234u16; 3]; n]` writes one inner lane, doubles it
/// to the inner array, then doubles the inner array — `ceil(log2 3) +
/// ceil(log2 n)` copies; `[[0u8; 4]; n]` is one memset of `4 n` bytes.
#[test]
fn nested_splats_stay_logarithmic() {
    let nested = |elem: Ty, value: Constant, inner: u64, n: u64| {
        module(
            vec![elem, Ty::Array(TyId::new(0), inner)],
            vec![],
            Ty::Bool,
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Array(TyId::new(1), n),
                    value: Constant::Splat {
                        elem: Box::new(Constant::Splat {
                            elem: Box::new(value),
                            len: inner,
                        }),
                        len: n,
                    },
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                })
                .with_result(v(1)),
            ],
            v(1),
        )
    };
    for n in [2u64, (1 << 28) - 1] {
        let words = census(&lower(&nested(Ty::U16, Constant::Int(0x1234), 3, n)).unwrap());
        assert_eq!(words.stores, 1, "{words:?}");
        assert_eq!(words.memcpy, ceil_log2(3) + ceil_log2(n), "{words:?}");
        let func = lower(&nested(Ty::U8, Constant::Int(0), 4, n)).unwrap();
        let zeros = census(&func);
        assert_eq!(
            (zeros.memset, zeros.stores, zeros.memcpy),
            (1, 0, 0),
            "{zeros:?}"
        );
        assert_eq!(memset(&func), (0, (4 * n) as i64));
    }
}

/// Shapes trust-ir's validator refuses are refused by name here too.
#[test]
fn splat_shape_mismatches_are_refused_by_name() {
    let not_an_array = module(
        vec![Ty::U32],
        vec![(v(0), Ty::U32)],
        Ty::U32,
        vec![
            InstrNode::new(Inst::ArraySplat {
                ty: Ty::U32,
                value: v(0),
            })
            .with_result(v(1)),
        ],
        v(1),
    );
    let error = lower(&not_an_array).expect_err("ArraySplat at u32");
    assert!(
        error.contains("Inst::ArraySplat") && error.contains("not an array"),
        "{error}"
    );

    let mistyped = module(
        vec![Ty::U32],
        vec![(v(0), Ty::U64), (v(1), Ty::U64)],
        Ty::U32,
        vec![
            InstrNode::new(Inst::ArraySplat {
                ty: Ty::Array(TyId::new(0), 4),
                value: v(0),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::U32,
                array: v(2),
                index: v(1),
            })
            .with_result(v(3)),
        ],
        v(3),
    );
    let error = lower(&mistyped).expect_err("a u64 operand for u32 lanes");
    assert!(
        error.contains("Inst::ArraySplat") && error.contains("operand has type"),
        "{error}"
    );

    let mut wrong_len = constant_splat(Ty::U32, Constant::Int(1), 4);
    let Inst::Const { value, .. } = &mut wrong_len.functions[0].blocks[0].body[0].inst else {
        unreachable!()
    };
    *value = Constant::Splat {
        elem: Box::new(Constant::Int(1)),
        len: 5,
    };
    // The constant splat's shape is TrustIR's to check: its typed admission
    // refuses a wrong lane count, a splat at a scalar type and an out-of-range
    // element before the adapter's own splat checks are reached on any
    // codegen entry. Each adapter check is pinned below that admission.
    let error = trust_cg_lower::translate_function_with_license(
        &wrong_len.functions[0],
        &wrong_len,
        &permit_unlicensed(),
    )
    .expect_err("a 5-lane splat at [u32; 4]");
    assert_typed_const_refusal(&error, "function 'f' bb0", "[ty.0 x 4]", "splat[5]");
    assert_eq!(
        body_refusal_below_admission(&wrong_len),
        "not lowerable: unsupported trust_ir instruction: Constant::Splat has 5 lane(s), but \
         declared type Array(TyId(0), 4) has 4"
    );

    let scalar = module(
        vec![],
        vec![],
        Ty::U32,
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Splat {
                    elem: Box::new(Constant::Int(1)),
                    len: 2,
                },
            })
            .with_result(v(0)),
        ],
        v(0),
    );
    let error = trust_cg_lower::translate_function_with_license(
        &scalar.functions[0],
        &scalar,
        &permit_unlicensed(),
    )
    .expect_err("a splat at u32");
    assert_typed_const_refusal(&error, "function 'f' bb0", "u32", "splat[2]");
    let at_non_array = "not lowerable: unsupported trust_ir instruction: Constant::Splat (len 2) \
                        at non-array type U32: a splat mirrors Ty::Array only";
    assert_eq!(body_refusal_below_admission(&scalar), at_non_array);

    // The same shape one level down, at a tuple's `u32` field: the in-place
    // fill (`fill_splat_at_ptr`) checks the field type itself.
    let nested_scalar = module(
        vec![],
        vec![],
        Ty::U32,
        vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Tuple(vec![Ty::U32, Ty::U32]),
                value: Constant::Aggregate(vec![
                    Constant::Splat {
                        elem: Box::new(Constant::Int(1)),
                        len: 2,
                    },
                    Constant::Int(0),
                ]),
            })
            .with_result(v(0)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U32,
                aggregate: v(0),
                field: 1,
            })
            .with_result(v(1)),
        ],
        v(1),
    );
    let error = trust_cg_lower::translate_function_with_license(
        &nested_scalar.functions[0],
        &nested_scalar,
        &permit_unlicensed(),
    )
    .expect_err("a splat at a u32 field");
    assert_typed_const_refusal(&error, "function 'f' bb0[0]", "u32", "splat[2]");
    assert_eq!(body_refusal_below_admission(&nested_scalar), at_non_array);

    // An out-of-range element is refused even though its low byte would make
    // a tidy memset.
    let out_of_range = constant_splat(Ty::U8, Constant::Int(0x100), 8);
    let error = trust_cg_lower::translate_function_with_license(
        &out_of_range.functions[0],
        &out_of_range,
        &permit_unlicensed(),
    )
    .expect_err("256 does not fit u8");
    assert_typed_const_refusal(&error, "function 'f' bb0[0]", "u8", "int");
    assert_eq!(
        body_refusal_below_admission(&out_of_range),
        "not lowerable: unsupported trust_ir instruction: Constant::Int(256) does not fit in U8 \
         (range [0, 255])"
    );
}

/// §3.1 (validated by trust-ir): the non-canonical spellings of a uniform
/// array are refused on the shared pin-move floor with trust-ir's own error —
/// a list of equal elements (nested included), uniform raw bytes, a splat of
/// fewer than two, a `MakeAggregate` of one repeated lane and a zero-lane
/// `ArraySplat` — while the canonical spellings pass.
#[test]
fn non_canonical_uniform_arrays_are_refused_on_the_floor() {
    use trust_cg_lower::adapter::reject_unconsumed_v41_target_neutral_surface as floor;
    let refused = |module: &Module| {
        let error = floor(module)
            .expect_err("a non-canonical uniform array")
            .to_string();
        assert!(error.contains("non-canonical uniform array"), "{error}");
    };
    let with_const = |types: Vec<Ty>, ty: Ty, value: Constant| {
        module(
            types,
            vec![],
            Ty::Bool,
            vec![
                InstrNode::new(Inst::Const { ty, value }).with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                })
                .with_result(v(1)),
            ],
            v(1),
        )
    };
    let i32s = |n: u64| Ty::Array(TyId::new(0), n);
    refused(&with_const(
        vec![Ty::I32],
        i32s(3),
        Constant::Array(vec![Constant::Int(7); 3]),
    ));
    refused(&with_const(
        vec![Ty::I32],
        i32s(2),
        Constant::Aggregate(vec![Constant::Int(0); 2]),
    ));
    // Nested: the inner rows are equal lists, the outer list differs.
    refused(&with_const(
        vec![Ty::I32, i32s(2)],
        Ty::Array(TyId::new(1), 2),
        Constant::Array(vec![
            Constant::Array(vec![Constant::Int(1), Constant::Int(1)]),
            Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
        ]),
    ));
    refused(&with_const(
        vec![Ty::U8],
        Ty::Array(TyId::new(0), 4),
        Constant::Bytes {
            data: vec![0; 4],
            utf8: false,
        },
    ));
    refused(&with_const(
        vec![Ty::I32],
        i32s(1),
        Constant::Splat {
            elem: Box::new(Constant::Int(7)),
            len: 1,
        },
    ));
    let lanes = |ty: Ty, fields: Vec<ValueId>| {
        module(
            vec![Ty::I32],
            vec![(v(0), Ty::I32), (v(1), Ty::I32)],
            Ty::Bool,
            vec![
                InstrNode::new(Inst::MakeAggregate {
                    ty,
                    variant: None,
                    fields,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                })
                .with_result(v(3)),
            ],
            v(3),
        )
    };
    refused(&lanes(i32s(2), vec![v(0), v(0)]));
    refused(&lanes(i32s(1), vec![v(0)]));
    refused(&module(
        vec![Ty::I32],
        vec![(v(0), Ty::I32)],
        Ty::Bool,
        vec![
            InstrNode::new(Inst::ArraySplat {
                ty: i32s(0),
                value: v(0),
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(2)),
        ],
        v(2),
    ));
    // A global initializer is held to the same rule.
    let mut global = with_const(vec![Ty::I32], Ty::Bool, Constant::Bool(true));
    global.globals.push(trust_ir::Global {
        name: "G".to_string(),
        ty: i32s(2),
        mutable: false,
        initializer: Some(Constant::Array(vec![Constant::Int(5); 2])),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    refused(&global);

    // The canonical spellings pass: a splat, a mixed list, a one-element
    // list, UTF-8 bytes, distinct lanes and a register splat.
    for (types, ty, value) in [
        (
            vec![Ty::I32],
            i32s(3),
            Constant::Splat {
                elem: Box::new(Constant::Int(7)),
                len: 3,
            },
        ),
        (
            vec![Ty::I32],
            i32s(2),
            Constant::Array(vec![Constant::Int(1), Constant::Int(2)]),
        ),
        (
            vec![Ty::I32],
            i32s(1),
            Constant::Array(vec![Constant::Int(7)]),
        ),
        (
            vec![Ty::U8],
            Ty::Array(TyId::new(0), 2),
            Constant::Bytes {
                data: b"aa".to_vec(),
                utf8: true,
            },
        ),
    ] {
        floor(&with_const(types, ty.clone(), value.clone()))
            .unwrap_or_else(|err| panic!("{ty:?} {value:?}: {err}"));
    }
    floor(&lanes(i32s(2), vec![v(0), v(1)])).expect("distinct lanes");
    floor(&register_splat_u32(3)).expect("a register splat");
}

/// §3.1 descends where trust-ir's validator does: a uniform list is refused
/// wherever it sits at an array type, including as the element of a
/// sequence, a set or a vector (the validator's `ChildTypes::Repeated`),
/// while equal elements of the collection itself are its canonical spelling.
/// Each row is checked against trust-ir's own validator too, so the floor
/// and the format agree on it.
#[test]
fn uniform_arrays_inside_collections_are_refused_as_the_validator_refuses_them() {
    use trust_cg_lower::adapter::reject_unconsumed_v41_target_neutral_surface as floor;
    use trust_ir::SetRepr;
    let with_const = |types: Vec<Ty>, ty: Ty, value: Constant| {
        module(
            types,
            vec![],
            Ty::Bool,
            vec![
                InstrNode::new(Inst::Const { ty, value }).with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                })
                .with_result(v(1)),
            ],
            v(1),
        )
    };
    let format_refuses = |module: &Module| {
        trust_ir_build::validate_module(module).iter().any(|error| {
            matches!(
                error,
                trust_ir_build::ValidationError::NonCanonicalUniformArray { .. }
            )
        })
    };
    // ty 0 = i32, ty 1 = [i32; 2].
    let types = || vec![Ty::I32, Ty::Array(TyId::new(0), 2)];
    let pair = |a, b| Constant::Array(vec![Constant::Int(a), Constant::Int(b)]);
    let must_refuse = [
        (
            "sequence element",
            Ty::Sequence(TyId::new(1)),
            Constant::Sequence(vec![pair(1, 2), pair(3, 3)]),
        ),
        (
            "set element",
            Ty::Set(TyId::new(1), SetRepr::Boxed),
            Constant::Set(vec![pair(4, 4)]),
        ),
        (
            "vector lane",
            Ty::Vector(Box::new(Ty::Array(TyId::new(0), 2)), 2),
            Constant::Vector(vec![pair(1, 2), pair(5, 5)]),
        ),
        (
            "sequence of sequences",
            Ty::Sequence(TyId::new(2)),
            Constant::Sequence(vec![Constant::Sequence(vec![pair(6, 6)])]),
        ),
    ];
    for (row, ty, value) in must_refuse {
        let mut types = types();
        types.push(Ty::Sequence(TyId::new(1))); // ty 2 = seq<[i32; 2]>
        let module = with_const(types, ty, value);
        let error = floor(&module)
            .expect_err(&format!("{row}: a uniform array inside a collection"))
            .to_string();
        assert!(
            error.contains("non-canonical uniform array"),
            "{row}: {error}"
        );
        assert!(format_refuses(&module), "{row}: trust-ir refuses it too");
    }
    // The collection's own equal elements are canonical: the rule is about
    // arrays, and a splat element inside a collection is the array's one
    // spelling.
    let must_pass = [
        (
            "equal sequence elements",
            Ty::Sequence(TyId::new(0)),
            Constant::Sequence(vec![Constant::Int(9); 3]),
        ),
        (
            "equal vector lanes",
            Ty::Vector(Box::new(Ty::I32), 4),
            Constant::Vector(vec![Constant::Int(9); 4]),
        ),
        (
            "splat element",
            Ty::Sequence(TyId::new(1)),
            Constant::Sequence(vec![
                Constant::Splat {
                    elem: Box::new(Constant::Int(3)),
                    len: 2,
                },
                pair(1, 2),
            ]),
        ),
    ];
    for (row, ty, value) in must_pass {
        let module = with_const(types(), ty, value);
        floor(&module).unwrap_or_else(|error| panic!("{row}: {error}"));
        assert!(!format_refuses(&module), "{row}: trust-ir admits it too");
    }
}

// ---------------------------------------------------------------------------
// The EH type table spelled `splat[ @typeinfo; n ]` (trust-ir v50)
// ---------------------------------------------------------------------------

/// Module: `thrower()` is an external declaration; each catcher is
/// `invoke thrower() to bb1 unwind bb2`, bb1 `ret 0`, bb2 a landing pad that
/// catches `catch_type_index` and returns its selector. The reserved EH type
/// table global is `table` at `[ptr; table_len]`.
fn eh_module(table: Constant, table_len: u64, catchers: u32, catch_type_index: u32) -> Module {
    use trust_cg_lower::function::EH_TYPE_TABLE_GLOBAL;
    let mut module = Module::new("eh_type_table_splat");
    module.types = vec![Ty::Ptr];
    let thrower_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut thrower = Function::new(FuncId::new(0), "thrower", thrower_ty, BlockId::new(0));
    thrower.linkage = trust_ir::Linkage::External;
    module
        .try_add_function(thrower)
        .expect("Module::try_add_function: test fixture");
    let catcher_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    for id in 1..=catchers {
        let mut catcher = Function::new(
            FuncId::new(id),
            format!("catcher{id}"),
            catcher_ty,
            BlockId::new(0),
        );
        catcher.blocks = vec![
            Block {
                id: BlockId::new(0),
                params: vec![],
                body: vec![InstrNode::new(Inst::Invoke {
                    callee: FuncId::new(0),
                    args: vec![],
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                })],
            },
            Block {
                id: BlockId::new(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(0),
                    })
                    .with_result(v(0)),
                    InstrNode::new(Inst::Return { values: vec![v(0)] }),
                ],
            },
            Block {
                id: BlockId::new(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::LandingPad {
                        is_cleanup: false,
                        catch_type_indices: vec![catch_type_index],
                    })
                    .with_results(vec![v(1), v(2)]),
                    InstrNode::new(Inst::Return { values: vec![v(2)] }),
                ],
            },
        ];
        module
            .try_add_function(catcher)
            .expect("Module::try_add_function: test fixture");
    }
    module.globals.push(trust_ir::Global {
        name: EH_TYPE_TABLE_GLOBAL.to_string(),
        ty: Ty::Array(TyId::new(0), table_len),
        mutable: false,
        initializer: Some(table),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    module
}

fn typeinfo(symbol: &str) -> Constant {
    Constant::SymbolAddr {
        symbol: symbol.to_string(),
        addend: 0,
    }
}

fn splat_table(n: u64) -> Constant {
    Constant::Splat {
        elem: Box::new(typeinfo("_ZTIi")),
        len: n,
    }
}

/// A splat EH type table binds every catch type index `1..=n` to its one
/// typeinfo and stays one symbol and a length on the lowered function: a
/// small and a huge `n` lower to the same LIR, differing only in the length
/// the table records. (The table was expanded to `n` symbols; `2^61 - 1`
/// entries could not even be reserved.)
#[test]
fn splat_eh_type_table_binds_in_constant_size() {
    use trust_cg_lower::function::{EhTypeTable, EhTypeTableEntries};
    let lower_catcher = |n: u64, index: u32| {
        let module = eh_module(splat_table(n), n, 1, index);
        trust_cg_lower::translate_function_with_license(
            &module.functions[1],
            &module,
            &permit_unlicensed(),
        )
        .map(|(func, _)| func)
        .map_err(|error| error.to_string())
    };
    // `2^61 - 1` precedes `2^40`: an expanding table fails on its
    // reservation at once instead of filling terabytes.
    for n in [2u64, 3, (1 << 61) - 1, 1 << 40] {
        for index in [1, 2] {
            let small = lower_catcher(2, index).expect("2-entry splat table");
            let func = lower_catcher(n, index).unwrap_or_else(|error| panic!("n = {n}: {error}"));
            assert_eq!(
                func.eh_type_table.entries(),
                EhTypeTableEntries::Splat {
                    symbol: "_ZTIi",
                    len: n
                },
                "n = {n}"
            );
            assert_eq!(
                func.eh_type_table.symbol_for_catch_index(index),
                Some("_ZTIi")
            );
            assert_eq!(census(&func), census(&small), "n = {n}");
            assert_eq!(
                func.eh_info.landing_pads, small.eh_info.landing_pads,
                "n = {n}"
            );
        }
    }
    // An index past the table is refused by name, whatever the spelling.
    let error = lower_catcher(2, 3).expect_err("index 3 of a 2-entry table");
    assert!(
        error.contains("not bound") && error.contains("[TCG-EH-TTYPE]"),
        "{error}"
    );
    // A two-entry list of distinct typeinfos stays the list.
    let list = eh_module(
        Constant::Array(vec![typeinfo("_ZTIi"), typeinfo("_ZTId")]),
        2,
        1,
        2,
    );
    let func = trust_cg_lower::translate_function_with_license(
        &list.functions[1],
        &list,
        &permit_unlicensed(),
    )
    .unwrap()
    .0;
    assert_eq!(
        func.eh_type_table,
        EhTypeTable::from_symbols(vec!["_ZTIi".to_string(), "_ZTId".to_string()])
    );
}

/// The module EH type table is read ONCE per module translation and shared:
/// every function that catches a typed exception carries a clone of the one
/// table (shared storage, not a per-function copy or re-read).
#[test]
fn eh_type_table_is_read_once_per_module_translation() {
    let cases = [
        (
            "list",
            Constant::Array(vec![typeinfo("_ZTIi"), typeinfo("_ZTId")]),
            2,
        ),
        ("splat", splat_table(1 << 40), 1 << 40),
    ];
    for (spelling, table, n) in cases {
        let module = eh_module(table, n, 3, 1);
        let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::default(),
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap_or_else(|error| panic!("{spelling}: {error}"));
        assert_eq!(lowered.len(), 3, "{spelling}: the three catchers");
        let first = &lowered[0].0.eh_type_table;
        assert_eq!(first.len(), n, "{spelling}");
        for (func, _) in &lowered[1..] {
            assert!(
                func.eh_type_table.shares_storage_with(first),
                "{spelling}: `{}` carries its own copy of the module table",
                func.name
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
