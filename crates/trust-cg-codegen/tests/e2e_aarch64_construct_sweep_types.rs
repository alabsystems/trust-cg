// Copyright 2026 Andrew Yates | Apache-2.0
//! Construct sweep, TYPES (ledger L05-P2, Darwin row D05): trust-ir types the
//! construct inventory recorded as model-only, executed natively on
//! aarch64-apple-darwin at O0-O3 and checked against the pinned trust-ir
//! reference interpreter and, where the type has one, its C meaning:
//!
//! * `Ty::Isize` / `Ty::Usize` pointer-width arithmetic (`intptr_t` /
//!   `uintptr_t`), `Ty::Char` (a `ZExt` origin, a `Char` switch selector and
//!   constant, a `Bitcast` to `u32`);
//! * the typed pointer carriers `Ty::Ref`, `Ty::RefMut`, `Ty::PtrConst`
//!   reached through `CastOp::PtrToPtr` and loaded/stored through;
//! * `Ty::Never` (a divergent callee) and `Inst::Unreachable`, whose native
//!   run must die by a trap where the interpreter refuses;
//! * `Ty::Record` values over the `records` table (`Constant::Record`, a
//!   by-value record argument, `ExtractField` by declaration index);
//! * `Ty::FatPtr` slices built by `Inst::PtrFromParts`, passed by value and
//!   taken apart by `Inst::PtrData` / `Inst::PtrMetadata`;
//! * a `Ty::Refine` carrier across a call and the C boundary.
//!
//! Execution evidence on this host only (Mach-O objects linked by the host
//! `cc`); not a proof of any lowering.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/construct_sweep.rs"]
mod sweep;

use sweep::{Arg, Body, Call, Trap, define, sweep, sweep_module};
use trust_ir::interpret::InterpretErrorCode;
use trust_ir::{
    BinOp, CastOp, Constant, FatPtrKind, FieldDef, ICmpOp, Inst, Module, Pred, RecordDef, RecordId,
    SwitchCase, Ty, ValueId,
};

fn binop(body: &mut Body, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
    body.emit(Inst::BinOp { op, ty, lhs, rhs })
}

fn int_const(body: &mut Body, ty: Ty, value: i128) -> ValueId {
    body.emit(Inst::Const {
        ty,
        value: Constant::Int(value),
    })
}

fn ret(body: &mut Body, values: Vec<ValueId>) {
    body.effect(Inst::Return { values });
}

/// `Isize`, `Usize` and `Char` functions.
fn scalar_types_module() -> Module {
    let mut module = sweep_module("construct_sweep_scalar_types");

    // ((a - b) * 3) >> 1, arithmetic, at the pointer width.
    let mut body = Body::new();
    let a = body.param(Ty::Isize);
    let b = body.param(Ty::Isize);
    let diff = binop(&mut body, BinOp::Sub, Ty::Isize, a, b);
    let three = int_const(&mut body, Ty::Isize, 3);
    let scaled = binop(&mut body, BinOp::Mul, Ty::Isize, diff, three);
    let one = int_const(&mut body, Ty::Isize, 1);
    let halved = binop(&mut body, BinOp::AShr, Ty::Isize, scaled, one);
    ret(&mut body, vec![halved]);
    define(
        &mut module,
        "sweep_isize_affine",
        vec![Ty::Isize, Ty::Isize],
        vec![Ty::Isize],
        body,
    );

    // a / b + a % b, unsigned, at the pointer width.
    let mut body = Body::new();
    let a = body.param(Ty::Usize);
    let b = body.param(Ty::Usize);
    let quotient = binop(&mut body, BinOp::UDiv, Ty::Usize, a, b);
    let remainder = binop(&mut body, BinOp::URem, Ty::Usize, a, b);
    let sum = binop(&mut body, BinOp::Add, Ty::Usize, quotient, remainder);
    ret(&mut body, vec![sum]);
    define(
        &mut module,
        "sweep_usize_divmod",
        vec![Ty::Usize, Ty::Usize],
        vec![Ty::Usize],
        body,
    );

    // A `Char` from a byte, dispatched by a `Char` switch.
    let mut body = Body::new();
    let byte = body.param(Ty::U8);
    let ch = body.emit(Inst::Cast {
        op: CastOp::ZExt,
        src_ty: Ty::U8,
        dst_ty: Ty::Char,
        operand: byte,
    });
    let (upper_a, _) = body.block(&[]);
    let (lower_z, _) = body.block(&[]);
    let (other, other_params) = body.block(&[Ty::Char]);
    body.effect(Inst::Switch {
        value: ch,
        default: other,
        default_args: vec![ch],
        cases: vec![
            SwitchCase {
                value: Constant::Int(0x41),
                target: upper_a,
                args: vec![],
            },
            SwitchCase {
                value: Constant::Int(0x7A),
                target: lower_z,
                args: vec![],
            },
        ],
        exhaustive_enum_unreachable: false,
    });
    body.switch_to(upper_a);
    let one = int_const(&mut body, Ty::U32, 1);
    ret(&mut body, vec![one]);
    body.switch_to(lower_z);
    let two = int_const(&mut body, Ty::U32, 2);
    ret(&mut body, vec![two]);
    body.switch_to(other);
    let scalar = body.emit(Inst::Cast {
        op: CastOp::Bitcast,
        src_ty: Ty::Char,
        dst_ty: Ty::U32,
        operand: other_params[0],
    });
    let emoji = int_const(&mut body, Ty::U32, 0x1F600);
    let shifted = binop(&mut body, BinOp::Add, Ty::U32, scalar, emoji);
    ret(&mut body, vec![shifted]);
    define(
        &mut module,
        "sweep_char_class",
        vec![Ty::U8],
        vec![Ty::U32],
        body,
    );

    // The largest Unicode scalar, returned as a `Char`.
    let mut body = Body::new();
    let max = int_const(&mut body, Ty::Char, 0x10FFFF);
    ret(&mut body, vec![max]);
    define(&mut module, "sweep_char_max", vec![], vec![Ty::Char], body);
    module
}

#[test]
fn native_isize_usize_and_char_match_the_interpreter_and_c_o0_through_o3() {
    let module = scalar_types_module();
    let i = |value: i64| Arg(Ty::Isize, u128::from(value as u64));
    let u = |value: u64| Arg(Ty::Usize, u128::from(value));
    let byte = |value: u8| Arg(Ty::U8, u128::from(value));
    let mut calls = vec![
        Call::new(
            "isize_neg",
            "sweep_isize_affine",
            vec![i(5), i(90)],
            Ty::Isize,
        )
        .c("(intptr_t)(((a0 - a1) * 3) >> 1)"),
        Call::new(
            "isize_wide",
            "sweep_isize_affine",
            vec![i(1 << 40), i(-(1 << 41))],
            Ty::Isize,
        )
        .c("(intptr_t)(((a0 - a1) * 3) >> 1)"),
        Call::new(
            "usize_high",
            "sweep_usize_divmod",
            vec![u(u64::MAX - 6), u(1000)],
            Ty::Usize,
        )
        .c("a0 / a1 + a0 % a1"),
        Call::new(
            "usize_small",
            "sweep_usize_divmod",
            vec![u(17), u(5)],
            Ty::Usize,
        )
        .c("a0 / a1 + a0 % a1"),
        Call::new("char_max", "sweep_char_max", vec![], Ty::Char).c("0x10FFFF"),
    ];
    for value in [0x41u8, 0x7A, 0x00, 0x42, 0xFF] {
        calls.push(
            Call::new(
                format!("char_class_{value:02x}"),
                "sweep_char_class",
                vec![byte(value)],
                Ty::U32,
            )
            .c("a0 == 'A' ? 1u : a0 == 'z' ? 2u : (uint32_t)a0 + 0x1F600u"),
        );
    }
    let compared = sweep("scalar-types", &module, &calls, &[], "", "");
    assert_eq!(compared, calls.len());
}

/// Typed pointer carriers reached through `PtrToPtr`.
fn reference_carriers_module() -> Module {
    let mut module = sweep_module("construct_sweep_reference_carriers");

    // *q = *p + *r; return 2 * *q, through a shared reference, a unique
    // reference and a typed const pointer.
    let mut body = Body::new();
    let shared = body.param(Ty::Ref(Box::new(Ty::I64)));
    let unique = body.param(Ty::RefMut(Box::new(Ty::I64)));
    let raw = body.param(Ty::PtrConst(Box::new(Ty::I64)));
    let a = body.emit(Inst::Load {
        ty: Ty::I64,
        ptr: shared,
        volatile: false,
        align: None,
    });
    let c = body.emit(Inst::Load {
        ty: Ty::I64,
        ptr: raw,
        volatile: false,
        align: None,
    });
    let sum = binop(&mut body, BinOp::Add, Ty::I64, a, c);
    body.effect(Inst::Store {
        ty: Ty::I64,
        ptr: unique,
        value: sum,
        volatile: false,
        align: None,
    });
    let stored = body.emit(Inst::Load {
        ty: Ty::I64,
        ptr: unique,
        volatile: false,
        align: None,
    });
    let doubled = binop(&mut body, BinOp::Add, Ty::I64, stored, stored);
    ret(&mut body, vec![doubled]);
    let combine = define(
        &mut module,
        "sweep_ref_combine",
        vec![
            Ty::Ref(Box::new(Ty::I64)),
            Ty::RefMut(Box::new(Ty::I64)),
            Ty::PtrConst(Box::new(Ty::I64)),
        ],
        vec![Ty::I64],
        body,
    );

    // Stack cells retyped by `PtrToPtr`, then the combine and a reload.
    let mut body = Body::new();
    let a = body.param(Ty::I64);
    let c = body.param(Ty::I64);
    let cell = |body: &mut Body, value: ValueId, retyped: Ty| {
        let slot = body.emit(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        });
        body.effect(Inst::Store {
            ty: Ty::I64,
            ptr: slot,
            value,
            volatile: false,
            align: None,
        });
        let typed = body.emit(Inst::Cast {
            op: CastOp::PtrToPtr,
            src_ty: Ty::Ptr,
            dst_ty: retyped,
            operand: slot,
        });
        (slot, typed)
    };
    let zero = int_const(&mut body, Ty::I64, 0);
    let (_, shared) = cell(&mut body, a, Ty::Ref(Box::new(Ty::I64)));
    let (unique_slot, unique) = cell(&mut body, zero, Ty::RefMut(Box::new(Ty::I64)));
    let (_, raw) = cell(&mut body, c, Ty::PtrConst(Box::new(Ty::I64)));
    let doubled = body.emit_n(
        Inst::Call {
            callee: combine,
            args: vec![shared, unique, raw],
        },
        1,
    )[0];
    let written = body.emit(Inst::Load {
        ty: Ty::I64,
        ptr: unique_slot,
        volatile: false,
        align: None,
    });
    let total = binop(&mut body, BinOp::Add, Ty::I64, doubled, written);
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_ref_run",
        vec![Ty::I64, Ty::I64],
        vec![Ty::I64],
        body,
    );
    module
}

#[test]
fn native_reference_carriers_load_and_store_through_ptr_to_ptr_o0_through_o3() {
    let module = reference_carriers_module();
    let i = |value: i64| Arg(Ty::I64, u128::from(value as u64));
    let calls = vec![
        Call::new(
            "ref_run_small",
            "sweep_ref_run",
            vec![i(11), i(-4)],
            Ty::I64,
        )
        .c("(a0 + a1) * 3"),
        Call::new(
            "ref_run_wide",
            "sweep_ref_run",
            vec![i(1 << 50), i(-(1 << 33) + 7)],
            Ty::I64,
        )
        .c("(a0 + a1) * 3"),
    ];
    // The C driver also passes its own cells to the reference-typed callee.
    let extra = r#"    {
        int64_t a = 21, b = 0, c = -100;
        int64_t r = sweep_ref_combine(&a, &b, &c);
        report("ref_combine_direct", (u128)(uint64_t)r, 1, (u128)(uint64_t)((a + c) * 2));
        report("ref_combine_store", (u128)(uint64_t)b, 1, (u128)(uint64_t)(a + c));
    }
"#;
    let prelude = "extern int64_t sweep_ref_combine(void *, void *, void *);\n";
    let compared = sweep("reference-carriers", &module, &calls, &[], prelude, extra);
    assert_eq!(compared, calls.len());
}

/// A divergent function (`-> !`) the C driver calls, and an `Unreachable`
/// arm behind a zero-divisor branch.
fn never_module() -> Module {
    let mut module = sweep_module("construct_sweep_never");
    let mut body = Body::new();
    body.effect(Inst::Unreachable);
    define(&mut module, "sweep_diverge", vec![], vec![Ty::Never], body);

    let mut body = Body::new();
    let a = body.param(Ty::U64);
    let b = body.param(Ty::U64);
    let zero = int_const(&mut body, Ty::U64, 0);
    let is_zero = body.emit(Inst::ICmp {
        op: ICmpOp::Eq,
        ty: Ty::U64,
        lhs: b,
        rhs: zero,
    });
    let (bad, _) = body.block(&[]);
    let (good, _) = body.block(&[]);
    body.effect(Inst::CondBr {
        cond: is_zero,
        then_target: bad,
        then_args: vec![],
        else_target: good,
        else_args: vec![],
    });
    body.switch_to(bad);
    body.effect(Inst::Unreachable);
    body.switch_to(good);
    let quotient = binop(&mut body, BinOp::UDiv, Ty::U64, a, b);
    ret(&mut body, vec![quotient]);
    define(
        &mut module,
        "sweep_checked_div",
        vec![Ty::U64, Ty::U64],
        vec![Ty::U64],
        body,
    );
    module
}

#[test]
fn native_never_callee_and_unreachable_trap_where_the_interpreter_refuses_o0_through_o3() {
    let module = never_module();
    let u = |value: u64| Arg(Ty::U64, u128::from(value));
    let calls = vec![
        Call::new(
            "checked_div",
            "sweep_checked_div",
            vec![u(100), u(7)],
            Ty::U64,
        )
        .c("a0 / a1"),
        Call::new(
            "checked_div_wide",
            "sweep_checked_div",
            vec![u(u64::MAX), u(3)],
            Ty::U64,
        )
        .c("a0 / a1"),
    ];
    let traps = vec![
        Trap {
            mode: "divide_by_zero",
            func: "sweep_checked_div",
            args: vec![u(5), u(0)],
            refusal: InterpretErrorCode::UndefinedBehavior,
        },
        Trap {
            mode: "diverge",
            func: "sweep_diverge",
            args: vec![],
            refusal: InterpretErrorCode::UndefinedBehavior,
        },
    ];
    let compared = sweep("never", &module, &calls, &traps, "", "");
    assert_eq!(compared, calls.len());
}

/// `Point { x: i64, y: i32 }` in the `records` table.
fn record_module() -> Module {
    let mut module = sweep_module("construct_sweep_records");
    let point = module.add_record(RecordDef {
        id: RecordId::new(0),
        name: "Point".to_string(),
        fields: vec![
            FieldDef {
                name: "x".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "y".to_string(),
                ty: Ty::I32,
                offset: None,
            },
        ],
    });
    let record = Ty::Record(point);

    // A by-value record parameter, projected by declaration index.
    let mut body = Body::new();
    let value = body.param(record.clone());
    let x = body.emit(Inst::ExtractField {
        ty: Ty::I64,
        aggregate: value,
        field: 0,
    });
    let y = body.emit(Inst::ExtractField {
        ty: Ty::I32,
        aggregate: value,
        field: 1,
    });
    let wide_y = body.emit(Inst::Cast {
        op: CastOp::SExt,
        src_ty: Ty::I32,
        dst_ty: Ty::I64,
        operand: y,
    });
    let scaled = binop(&mut body, BinOp::Mul, Ty::I64, x, wide_y);
    ret(&mut body, vec![scaled]);
    let product = define(
        &mut module,
        "sweep_record_product",
        vec![record.clone()],
        vec![Ty::I64],
        body,
    );

    // A record constant, handed by value to the projection above.
    let mut body = Body::new();
    let a = body.param(Ty::I64);
    let point_value = body.emit(Inst::Const {
        ty: record.clone(),
        value: Constant::Record(vec![
            ("x".to_string(), Constant::Int(40)),
            ("y".to_string(), Constant::Int(-3)),
        ]),
    });
    let from_callee = body.emit_n(
        Inst::Call {
            callee: product,
            args: vec![point_value],
        },
        1,
    )[0];
    let x = body.emit(Inst::ExtractField {
        ty: Ty::I64,
        aggregate: point_value,
        field: 0,
    });
    let partial = binop(&mut body, BinOp::Add, Ty::I64, from_callee, x);
    let total = binop(&mut body, BinOp::Add, Ty::I64, partial, a);
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_record_mix",
        vec![Ty::I64],
        vec![Ty::I64],
        body,
    );
    module
}

#[test]
fn native_records_over_the_records_table_match_the_interpreter_o0_through_o3() {
    let module = record_module();
    let i = |value: i64| Arg(Ty::I64, u128::from(value as u64));
    let calls = vec![
        Call::new("record_mix", "sweep_record_mix", vec![i(1000)], Ty::I64).c("40 * -3 + 40 + a0"),
        Call::new("record_mix_neg", "sweep_record_mix", vec![i(-77)], Ty::I64)
            .c("40 * -3 + 40 + a0"),
    ];
    let compared = sweep("records", &module, &calls, &[], "", "");
    assert_eq!(compared, calls.len());
}

/// `&[u64]` slices: fat pointers built, passed and taken apart.
fn fat_pointer_module() -> Module {
    let mut module = sweep_module("construct_sweep_fat_pointers");
    let elem = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let slice = Ty::FatPtr(FatPtrKind::Slice(elem));

    // len * 1000 + last element (0 for an empty slice).
    let mut body = Body::new();
    let fat = body.param(slice.clone());
    let data = body.emit(Inst::PtrData {
        ptr_ty: slice.clone(),
        ptr: fat,
    });
    let len = body.emit(Inst::PtrMetadata {
        ptr_ty: slice.clone(),
        metadata_ty: Ty::U64,
        ptr: fat,
    });
    let zero = int_const(&mut body, Ty::U64, 0);
    let empty = body.emit(Inst::ICmp {
        op: ICmpOp::Eq,
        ty: Ty::U64,
        lhs: len,
        rhs: zero,
    });
    let (none, _) = body.block(&[]);
    let (some, _) = body.block(&[]);
    body.effect(Inst::CondBr {
        cond: empty,
        then_target: none,
        then_args: vec![],
        else_target: some,
        else_args: vec![],
    });
    body.switch_to(none);
    let nothing = int_const(&mut body, Ty::U64, 0);
    ret(&mut body, vec![nothing]);
    body.switch_to(some);
    let one = int_const(&mut body, Ty::U64, 1);
    let last_index = binop(&mut body, BinOp::Sub, Ty::U64, len, one);
    let last_ptr = body.emit(Inst::GEP {
        pointee_ty: Ty::U64,
        base: data,
        indices: vec![last_index],
        inbounds: true,
    });
    let last = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: last_ptr,
        volatile: false,
        align: None,
    });
    let thousand = int_const(&mut body, Ty::U64, 1000);
    let scaled = binop(&mut body, BinOp::Mul, Ty::U64, len, thousand);
    let summary = binop(&mut body, BinOp::Add, Ty::U64, scaled, last);
    ret(&mut body, vec![summary]);
    let last_of = define(
        &mut module,
        "sweep_slice_last",
        vec![slice.clone()],
        vec![Ty::U64],
        body,
    );

    // A slice from its parts, handed on by value.
    let mut body = Body::new();
    let data = body.param(Ty::Ptr);
    let len = body.param(Ty::U64);
    let fat = body.emit(Inst::PtrFromParts {
        ptr_ty: slice.clone(),
        metadata_ty: Ty::U64,
        data,
        metadata: len,
    });
    let summary = body.emit_n(
        Inst::Call {
            callee: last_of,
            args: vec![fat],
        },
        1,
    )[0];
    ret(&mut body, vec![summary]);
    let of_parts = define(
        &mut module,
        "sweep_slice_of",
        vec![Ty::Ptr, Ty::U64],
        vec![Ty::U64],
        body,
    );

    // Three stack elements, viewed as a slice of `len` of them.
    let mut body = Body::new();
    let values = [
        body.param(Ty::U64),
        body.param(Ty::U64),
        body.param(Ty::U64),
    ];
    let len = body.param(Ty::U64);
    let array_ty = Ty::Array(elem, 3);
    let base = body.emit(Inst::Alloca {
        ty: array_ty,
        count: None,
        align: None,
    });
    for (index, value) in values.into_iter().enumerate() {
        let at = int_const(&mut body, Ty::U64, index as i128);
        let slot = body.emit(Inst::GEP {
            pointee_ty: Ty::U64,
            base,
            indices: vec![at],
            inbounds: true,
        });
        body.effect(Inst::Store {
            ty: Ty::U64,
            ptr: slot,
            value,
            volatile: false,
            align: None,
        });
    }
    let summary = body.emit_n(
        Inst::Call {
            callee: of_parts,
            args: vec![base, len],
        },
        1,
    )[0];
    ret(&mut body, vec![summary]);
    define(
        &mut module,
        "sweep_slice_run",
        vec![Ty::U64, Ty::U64, Ty::U64, Ty::U64],
        vec![Ty::U64],
        body,
    );
    module
}

#[test]
fn native_fat_pointers_round_trip_their_parts_o0_through_o3() {
    let module = fat_pointer_module();
    let u = |value: u64| Arg(Ty::U64, u128::from(value));
    let model = "a3 == 0 ? 0 : a3 * 1000 + (a3 == 1 ? a0 : a3 == 2 ? a1 : a2)";
    let calls = vec![
        Call::new(
            "slice_three",
            "sweep_slice_run",
            vec![u(7), u(8), u(9), u(3)],
            Ty::U64,
        )
        .c(model),
        Call::new(
            "slice_two",
            "sweep_slice_run",
            vec![u(7), u(u64::MAX / 4), u(9), u(2)],
            Ty::U64,
        )
        .c(model),
        Call::new(
            "slice_empty",
            "sweep_slice_run",
            vec![u(7), u(8), u(9), u(0)],
            Ty::U64,
        )
        .c(model),
    ];
    // The C driver hands its own array and length across the boundary.
    let extra = r#"    {
        uint64_t data[5] = {3, 1, 4, 1, 5};
        report("slice_c_array", (u128)sweep_slice_of(data, 5), 1, (u128)(5 * 1000 + 5));
        report("slice_c_prefix", (u128)sweep_slice_of(data, 3), 1, (u128)(3 * 1000 + 4));
    }
"#;
    let prelude = "extern uint64_t sweep_slice_of(void *, uint64_t);\n";
    let compared = sweep("fat-pointers", &module, &calls, &[], prelude, extra);
    assert_eq!(compared, calls.len());
}

/// `Refine<i64, NonZero>` across a call and the C boundary.
fn refinement_module() -> Module {
    let mut module = sweep_module("construct_sweep_refinement");
    let base = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let nonzero = module
        .intern_pred(Pred::NonZero)
        .expect("Module::intern_pred: test fixture")
        .unwrap_or_else(|| panic!("NonZero interns"));
    let refined = Ty::Refine(base, nonzero);

    let mut body = Body::new();
    let value = body.param(refined.clone());
    ret(&mut body, vec![value]);
    let identity = define(
        &mut module,
        "sweep_refine_id",
        vec![refined.clone()],
        vec![refined.clone()],
        body,
    );

    let mut body = Body::new();
    let value = body.param(refined.clone());
    let passed = body.emit_n(
        Inst::Call {
            callee: identity,
            args: vec![value],
        },
        1,
    )[0];
    ret(&mut body, vec![passed]);
    define(
        &mut module,
        "sweep_refine_twice",
        vec![refined.clone()],
        vec![refined],
        body,
    );
    module
}

#[test]
fn native_refinement_carrier_crosses_calls_unchanged_o0_through_o3() {
    let module = refinement_module();
    let refined = module.functions[0].blocks[0].params[0].1.clone();
    let arg = |value: i64| Arg(refined.clone(), u128::from(value as u64));
    let calls = vec![
        Call::new(
            "refine_twice",
            "sweep_refine_twice",
            vec![arg(7)],
            refined.clone(),
        )
        .c("a0"),
        Call::new(
            "refine_negative",
            "sweep_refine_twice",
            vec![arg(-9)],
            refined.clone(),
        )
        .c("a0"),
        Call::new(
            "refine_id",
            "sweep_refine_id",
            vec![arg(i64::MIN)],
            refined.clone(),
        )
        .c("a0"),
    ];
    let compared = sweep("refinement", &module, &calls, &[], "", "");
    assert_eq!(compared, calls.len());
}
