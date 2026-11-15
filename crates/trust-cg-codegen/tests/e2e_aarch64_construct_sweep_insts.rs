// Copyright 2026 Andrew Yates | Apache-2.0
//! Construct sweep, INSTRUCTIONS (ledger L05-P2, Darwin row D05): trust-ir
//! instructions and constants the construct inventory recorded as model-only
//! or refused, executed natively on aarch64-apple-darwin at O0-O3 and checked
//! against the pinned trust-ir reference interpreter and their C meaning:
//!
//! * `Inst::Fence` at every non-relaxed ordering (and a `dmb` read back from
//!   the object), `Inst::NullPtr`, `Inst::Copy`, `Constant::Bool`;
//! * `Inst::Assume`, which passes on in-domain inputs and traps natively where
//!   the interpreter refuses (`AssumeViolated`). The original combined source
//!   Assert fixture remains, but v52 now refuses it instead of conflating a
//!   Rust panic with a trap; that historical native credit is not retained;
//! * `Inst::DialectOp` over the in-tree `vector` dialect (`pack_lanes`,
//!   `insert_lane`, `extract_lane`), rewritten to core IR by the compiler's
//!   dialect phase before lowering (`shuffle` and `reduce` are not executed
//!   here: this backend refuses them by name);
//! * `Inst::MakeAggregate` (trust-ir WS3.5) building struct (natural,
//!   declared-reordered, packed, typed-reference lane), record, tuple, array
//!   and nested values, read back by `ExtractField` / `ExtractElement`,
//!   passed by value to a callee, returned by value to C and stored to
//!   C-visible memory; enum constructors are covered separately by
//!   `result_aggregate_native`, with unknown niche validity still refused;
//! * trust-ir v50 `Inst::ArraySplat` and `Constant::Splat` (the uniform
//!   array `[v; n]`) in bodies and as global initializers, each lane read
//!   back by a runtime index.
//!
//! Execution evidence on this host only (Mach-O objects linked by the host
//! `cc`); not a proof of any lowering.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/construct_sweep.rs"]
mod sweep;

use sweep::{
    Arg, Body, Call, LEVELS, TRIPLE, Trap, compile, define, object_has_word, permit_unlicensed,
    sweep, sweep_module,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    ArtifactKind, CompileGeneration, CompilePlan, CompileRequest, CompileService,
    CompileServiceConfig, CompileStatus, InstallIntent,
};
use trust_ir::dialect::vector;
use trust_ir::interpret::InterpretErrorCode;
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, CastOp, Constant, EnumDef, EnumId, EnumVariant, FieldDef, Global, ICmpOp, Inst, Linkage,
    Module, Ordering, RecordDef, RecordId, StructDef, StructId, StructRepr, Ty, ValueId,
    Visibility,
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

fn widen(body: &mut Body, op: CastOp, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
    body.emit(Inst::Cast {
        op,
        src_ty,
        dst_ty,
        operand,
    })
}

const DMB_ISH: u32 = 0xd503_3bbf;

/// Fences, null pointers, SSA copies and boolean constants.
fn pseudo_module() -> Module {
    let mut module = sweep_module("construct_sweep_pseudo");

    // A stack round trip fenced at every non-relaxed ordering.
    let mut body = Body::new();
    let value = body.param(Ty::U64);
    let slot = body.emit(Inst::Alloca {
        ty: Ty::U64,
        count: None,
        align: None,
    });
    body.effect(Inst::Store {
        ty: Ty::U64,
        ptr: slot,
        value,
        volatile: false,
        align: None,
    });
    for ordering in [
        Ordering::Release,
        Ordering::Acquire,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ] {
        body.effect(Inst::Fence { ordering });
    }
    let reloaded = body.emit(Inst::Load {
        ty: Ty::U64,
        ptr: slot,
        volatile: false,
        align: None,
    });
    let one = int_const(&mut body, Ty::U64, 1);
    let next = binop(&mut body, BinOp::Add, Ty::U64, reloaded, one);
    ret(&mut body, vec![next]);
    define(
        &mut module,
        "sweep_fence",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );

    // The null pointer, returned and compared.
    let mut body = Body::new();
    let null = body.emit(Inst::NullPtr);
    ret(&mut body, vec![null]);
    define(&mut module, "sweep_null_ptr", vec![], vec![Ty::Ptr], body);

    // Compared by address (the interpreter compares integers, not pointers).
    let mut body = Body::new();
    let pointer = body.param(Ty::Ptr);
    let null = body.emit(Inst::NullPtr);
    let address = widen(&mut body, CastOp::PtrToInt, Ty::Ptr, Ty::U64, pointer);
    let null_address = widen(&mut body, CastOp::PtrToInt, Ty::Ptr, Ty::U64, null);
    let is_null = body.emit(Inst::ICmp {
        op: ICmpOp::Eq,
        ty: Ty::U64,
        lhs: address,
        rhs: null_address,
    });
    ret(&mut body, vec![is_null]);
    define(
        &mut module,
        "sweep_is_null",
        vec![Ty::Ptr],
        vec![Ty::Bool],
        body,
    );

    let mut body = Body::new();
    let null = body.emit(Inst::NullPtr);
    let address = widen(&mut body, CastOp::PtrToInt, Ty::Ptr, Ty::U64, null);
    ret(&mut body, vec![address]);
    define(
        &mut module,
        "sweep_null_address",
        vec![],
        vec![Ty::U64],
        body,
    );

    // SSA copies: x + 2 * copy(copy(x)).
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let first = body.emit(Inst::Copy {
        ty: Ty::U64,
        operand: x,
    });
    let second = body.emit(Inst::Copy {
        ty: Ty::U64,
        operand: first,
    });
    let doubled = binop(&mut body, BinOp::Add, Ty::U64, first, second);
    let total = binop(&mut body, BinOp::Add, Ty::U64, doubled, x);
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_copy",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );

    // Boolean constants steering selects, and returned as `bool`.
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let truth = body.emit(Inst::Const {
        ty: Ty::Bool,
        value: Constant::Bool(true),
    });
    let falsity = body.emit(Inst::Const {
        ty: Ty::Bool,
        value: Constant::Bool(false),
    });
    let zero = int_const(&mut body, Ty::U64, 0);
    let seven = int_const(&mut body, Ty::U64, 7);
    let kept = body.emit(Inst::Select {
        ty: Ty::U64,
        cond: truth,
        then_val: x,
        else_val: zero,
    });
    let fallback = body.emit(Inst::Select {
        ty: Ty::U64,
        cond: falsity,
        then_val: zero,
        else_val: seven,
    });
    let total = binop(&mut body, BinOp::Add, Ty::U64, kept, fallback);
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_bool_select",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );

    for (name, flag) in [("sweep_true", true), ("sweep_false", false)] {
        let mut body = Body::new();
        let value = body.emit(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(flag),
        });
        ret(&mut body, vec![value]);
        define(&mut module, name, vec![], vec![Ty::Bool], body);
    }
    module
}

#[test]
fn native_fence_null_copy_and_bool_constants_match_the_interpreter_o0_through_o3() {
    let module = pseudo_module();
    let u = |value: u64| Arg(Ty::U64, u128::from(value));
    let pointer = |address: u64| Arg(Ty::Ptr, u128::from(address));
    let calls = vec![
        Call::new("fence", "sweep_fence", vec![u(41)], Ty::U64).c("a0 + 1"),
        Call::new("fence_wrap", "sweep_fence", vec![u(u64::MAX)], Ty::U64).c("a0 + 1"),
        Call::new("null_ptr", "sweep_null_ptr", vec![], Ty::Ptr).c("NULL"),
        Call::new("is_null_null", "sweep_is_null", vec![pointer(0)], Ty::Bool).c("a0 == NULL"),
        Call::new(
            "is_null_other",
            "sweep_is_null",
            vec![pointer(0x1000)],
            Ty::Bool,
        )
        .c("a0 == NULL"),
        Call::new("null_address", "sweep_null_address", vec![], Ty::U64)
            .c("(uint64_t)(uintptr_t)NULL"),
        Call::new("copy", "sweep_copy", vec![u(0x1234_5678_9abc)], Ty::U64).c("3 * a0"),
        Call::new("bool_select", "sweep_bool_select", vec![u(35)], Ty::U64).c("a0 + 7"),
        Call::new("true", "sweep_true", vec![], Ty::Bool).c("true"),
        Call::new("false", "sweep_false", vec![], Ty::Bool).c("false"),
    ];
    let compared = sweep("pseudo", &module, &calls, &[], "", "");
    assert_eq!(compared, calls.len());
    // The fences reach the object: a `dmb ish` barrier at every level.
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile(&module, opt_level).unwrap_or_else(|error| panic!("{error}"));
        assert!(
            object_has_word(&object, DMB_ISH),
            "{opt_level:?}: no `dmb ish` in the object"
        );
    }
}

/// `1_000_000 / x` under `assume(x != 0)` and `assert(x < 1000)`.
fn checks_module() -> Module {
    let mut module = sweep_module("construct_sweep_checks");
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let zero = int_const(&mut body, Ty::U64, 0);
    let nonzero = body.emit(Inst::ICmp {
        op: ICmpOp::Ne,
        ty: Ty::U64,
        lhs: x,
        rhs: zero,
    });
    body.effect(Inst::Assume { cond: nonzero });
    let bound = int_const(&mut body, Ty::U64, 1000);
    let in_range = body.emit(Inst::ICmp {
        op: ICmpOp::Ult,
        ty: Ty::U64,
        lhs: x,
        rhs: bound,
    });
    body.effect(Inst::Assert {
        cond: in_range,
        kind: trust_ir::AssertKind::Unspecified,
        site: None,
    });
    let million = int_const(&mut body, Ty::U64, 1_000_000);
    let quotient = binop(&mut body, BinOp::UDiv, Ty::U64, million, x);
    ret(&mut body, vec![quotient]);
    define(
        &mut module,
        "sweep_guarded_div",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );
    module
}

#[test]
fn source_assert_checks_refuse_instead_of_receiving_native_trap_credit() {
    let module = checks_module();
    for opt_level in LEVELS {
        let err = compile(&module, opt_level).unwrap_err();
        assert!(err.contains("fn sweep_guarded_div: bb0#5"), "{err}");
        assert!(err.contains("unspecified panic kind"), "{err}");
    }
}

/// Independent source fixture: `1_000_000 / x` under `assume(x != 0)`.
/// It is not the historical Assert fixture with its source semantics changed.
fn assume_only_module() -> Module {
    let mut module = sweep_module("construct_sweep_assume_only");
    let mut body = Body::new();
    let x = body.param(Ty::U64);
    let zero = int_const(&mut body, Ty::U64, 0);
    let nonzero = body.emit(Inst::ICmp {
        op: ICmpOp::Ne,
        ty: Ty::U64,
        lhs: x,
        rhs: zero,
    });
    body.effect(Inst::Assume { cond: nonzero });
    let million = int_const(&mut body, Ty::U64, 1_000_000);
    let quotient = binop(&mut body, BinOp::UDiv, Ty::U64, million, x);
    ret(&mut body, vec![quotient]);
    define(
        &mut module,
        "sweep_guarded_div",
        vec![Ty::U64],
        vec![Ty::U64],
        body,
    );
    module
}

#[test]
fn native_assume_only_passes_in_domain_and_traps_outside_it_o0_through_o3() {
    let module = assume_only_module();
    let u = |value: u64| Arg(Ty::U64, u128::from(value));
    let calls = vec![
        Call::new("guarded_7", "sweep_guarded_div", vec![u(7)], Ty::U64).c("1000000 / a0"),
        Call::new("guarded_999", "sweep_guarded_div", vec![u(999)], Ty::U64).c("1000000 / a0"),
        Call::new("guarded_1", "sweep_guarded_div", vec![u(1)], Ty::U64).c("1000000 / a0"),
    ];
    let traps = vec![Trap {
        mode: "assume_zero",
        func: "sweep_guarded_div",
        args: vec![u(0)],
        refusal: InterpretErrorCode::AssumeViolated,
    }];
    let compared = sweep("checks", &module, &calls, &traps, "", "");
    assert_eq!(compared, calls.len());
}

/// In-tree `vector` dialect ops over `<4 x i32>`: the ones this backend
/// lowers (`pack_lanes`, `insert_lane`, `extract_lane`).
fn dialect_module() -> Module {
    let mut module = sweep_module("construct_sweep_dialect");
    let v4 = Ty::v4_i32();
    let mut body = Body::new();
    let lanes = [
        body.param(Ty::I32),
        body.param(Ty::I32),
        body.param(Ty::I32),
        body.param(Ty::I32),
    ];
    let replacement = body.param(Ty::I32);
    let packed = body.emit(Inst::DialectOp(Box::new(vector::pack_lanes(
        v4.clone(),
        lanes,
    ))));
    let replaced = body.emit(Inst::DialectOp(Box::new(vector::insert_lane(
        v4.clone(),
        packed,
        1,
        replacement,
    ))));
    let read: Vec<ValueId> = [0u32, 1, 3]
        .into_iter()
        .map(|lane| {
            body.emit(Inst::DialectOp(Box::new(vector::extract_lane(
                v4.clone(),
                replaced,
                lane,
            ))))
        })
        .collect();
    let thousand = int_const(&mut body, Ty::I32, 1000);
    let scaled = binop(&mut body, BinOp::Mul, Ty::I32, read[1], thousand);
    let partial = binop(&mut body, BinOp::Add, Ty::I32, scaled, read[2]);
    let total = binop(&mut body, BinOp::Add, Ty::I32, partial, read[0]);
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_vector_dialect",
        vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32, Ty::I32],
        vec![Ty::I32],
        body,
    );
    module
}

#[test]
fn native_vector_dialect_ops_match_the_interpreter_o0_through_o3() {
    let module = dialect_module();
    let i = |value: i32| Arg(Ty::I32, u128::from(value as u32));
    let model = "(int32_t)((uint32_t)a4 * 1000u + (uint32_t)a3 + (uint32_t)a0)";
    let calls = vec![
        Call::new(
            "dialect_small",
            "sweep_vector_dialect",
            vec![i(1), i(2), i(3), i(4), i(5)],
            Ty::I32,
        )
        .c(model),
        Call::new(
            "dialect_wrap",
            "sweep_vector_dialect",
            vec![i(i32::MAX), i(-7), i(123_456), i(i32::MIN), i(-3_000_000)],
            Ty::I32,
        )
        .c(model),
    ];
    let compared = sweep("dialect", &module, &calls, &[], "", "");
    assert_eq!(compared, calls.len());
}

fn field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
    FieldDef {
        name: name.to_string(),
        ty,
        offset,
    }
}

const MIXED: u32 = 0;
const DECLARED: u32 = 1;
const PACKED: u32 = 2;
const HOLDER: u32 = 3;
const NEST: u32 = 4;
const SMALL: u32 = 5;

/// Struct, tuple, array and nested values built by `MakeAggregate`.
fn make_aggregate_module() -> Module {
    let mut module = sweep_module("construct_sweep_make_aggregate");
    let i32_id = module
        .add_type(Ty::I32)
        .expect("Module::add_type: test fixture");
    let array4 = Ty::Array(i32_id, 4);
    let array3 = Ty::Array(i32_id, 3);
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(MIXED),
        name: "Mixed".to_string(),
        fields: vec![
            field("a", Ty::U8, None),
            field("b", Ty::U64, None),
            field("c", Ty::U16, None),
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    // rustc-style reordering: the declared offsets put `b` first.
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(DECLARED),
        name: "Declared".to_string(),
        fields: vec![field("a", Ty::U32, Some(8)), field("b", Ty::U64, Some(0))],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
    });
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(PACKED),
        name: "Packed".to_string(),
        fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U32, Some(1))],
        size: Some(5),
        align: Some(1),
        repr: StructRepr::Packed(1),
    });
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(HOLDER),
        name: "Holder".to_string(),
        fields: vec![
            field("r", Ty::Ref(Box::new(Ty::I64)), None),
            field("n", Ty::U64, None),
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(NEST),
        name: "Nest".to_string(),
        fields: vec![
            field("inner", Ty::Struct(StructId::new(DECLARED)), None),
            field("arr", array3.clone(), None),
            field("t", Ty::U16, None),
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let mixed = Ty::Struct(StructId::new(MIXED));
    let declared = Ty::Struct(StructId::new(DECLARED));
    let packed = Ty::Struct(StructId::new(PACKED));
    let holder = Ty::Struct(StructId::new(HOLDER));
    let nest = Ty::Struct(StructId::new(NEST));
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(SMALL),
        name: "Small".to_string(),
        fields: vec![field("a", Ty::U32, None), field("b", Ty::U64, None)],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let small = Ty::Struct(StructId::new(SMALL));
    let point = module.add_record(RecordDef {
        id: RecordId::new(0),
        name: "Point".to_string(),
        fields: vec![field("x", Ty::I64, None), field("y", Ty::I32, None)],
    });
    let record = Ty::Record(point);

    // Build, then store to C-visible memory.
    for (name, ty, lanes) in [
        (
            "sweep_make_mixed",
            mixed.clone(),
            vec![Ty::U8, Ty::U64, Ty::U16],
        ),
        (
            "sweep_make_declared",
            declared.clone(),
            vec![Ty::U32, Ty::U64],
        ),
        ("sweep_make_packed", packed.clone(), vec![Ty::U8, Ty::U32]),
        (
            "sweep_make_array_store",
            array4.clone(),
            vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32],
        ),
    ] {
        let mut body = Body::new();
        let out = body.param(Ty::Ptr);
        let fields: Vec<ValueId> = lanes.iter().map(|lane| body.param(lane.clone())).collect();
        let value = body.emit(Inst::MakeAggregate {
            ty: ty.clone(),
            variant: None,
            fields,
        });
        body.effect(Inst::Store {
            ty,
            ptr: out,
            value,
            volatile: false,
            align: None,
        });
        ret(&mut body, vec![]);
        let mut params = vec![Ty::Ptr];
        params.extend(lanes);
        define(&mut module, name, params, vec![], body);
    }

    // Build, then read every lane back: a checksum per struct shape.
    for (name, ty, lanes) in [
        (
            "sweep_mixed_sum",
            mixed.clone(),
            vec![Ty::U8, Ty::U64, Ty::U16],
        ),
        (
            "sweep_declared_sum",
            declared.clone(),
            vec![Ty::U32, Ty::U64],
        ),
        ("sweep_packed_sum", packed.clone(), vec![Ty::U8, Ty::U32]),
    ] {
        let mut body = Body::new();
        let fields: Vec<ValueId> = lanes.iter().map(|lane| body.param(lane.clone())).collect();
        let value = body.emit(Inst::MakeAggregate {
            ty,
            variant: None,
            fields,
        });
        let mut total = int_const(&mut body, Ty::U64, 0);
        for (index, lane) in lanes.iter().enumerate() {
            let read = body.emit(Inst::ExtractField {
                ty: lane.clone(),
                aggregate: value,
                field: index as u32,
            });
            let wide = if *lane == Ty::U64 {
                read
            } else {
                widen(&mut body, CastOp::ZExt, lane.clone(), Ty::U64, read)
            };
            let shift = int_const(&mut body, Ty::U64, 8 * index as i128);
            let placed = binop(&mut body, BinOp::Shl, Ty::U64, wide, shift);
            total = binop(&mut body, BinOp::Xor, Ty::U64, total, placed);
        }
        ret(&mut body, vec![total]);
        define(&mut module, name, lanes, vec![Ty::U64], body);
    }

    // By value: into a callee, and back to C in registers.
    let mut body = Body::new();
    let value = body.param(mixed.clone());
    let lanes = [Ty::U8, Ty::U64, Ty::U16];
    let mut total = int_const(&mut body, Ty::U64, 0);
    for (index, lane) in lanes.iter().enumerate() {
        let read = body.emit(Inst::ExtractField {
            ty: lane.clone(),
            aggregate: value,
            field: index as u32,
        });
        let wide = if *lane == Ty::U64 {
            read
        } else {
            widen(&mut body, CastOp::ZExt, lane.clone(), Ty::U64, read)
        };
        let shift = int_const(&mut body, Ty::U64, 8 * index as i128);
        let placed = binop(&mut body, BinOp::Shl, Ty::U64, wide, shift);
        total = binop(&mut body, BinOp::Xor, Ty::U64, total, placed);
    }
    ret(&mut body, vec![total]);
    let fold = define(
        &mut module,
        "sweep_mixed_fold",
        vec![mixed.clone()],
        vec![Ty::U64],
        body,
    );
    let mut body = Body::new();
    let fields: Vec<ValueId> = lanes.iter().map(|lane| body.param(lane.clone())).collect();
    let value = body.emit(Inst::MakeAggregate {
        ty: mixed.clone(),
        variant: None,
        fields,
    });
    let folded = body.emit_n(
        Inst::Call {
            callee: fold,
            args: vec![value],
        },
        1,
    )[0];
    ret(&mut body, vec![folded]);
    define(
        &mut module,
        "sweep_mixed_byval",
        lanes.to_vec(),
        vec![Ty::U64],
        body,
    );

    let mut body = Body::new();
    let a = body.param(Ty::U32);
    let b = body.param(Ty::U64);
    let value = body.emit(Inst::MakeAggregate {
        ty: small.clone(),
        variant: None,
        fields: vec![a, b],
    });
    ret(&mut body, vec![value]);
    define(
        &mut module,
        "sweep_make_small_ret",
        vec![Ty::U32, Ty::U64],
        vec![small],
        body,
    );

    // A record value from its lanes.
    let mut body = Body::new();
    let x = body.param(Ty::I64);
    let y = body.param(Ty::I32);
    let value = body.emit(Inst::MakeAggregate {
        ty: record,
        variant: None,
        fields: vec![x, y],
    });
    let x2 = body.emit(Inst::ExtractField {
        ty: Ty::I64,
        aggregate: value,
        field: 0,
    });
    let y2 = body.emit(Inst::ExtractField {
        ty: Ty::I32,
        aggregate: value,
        field: 1,
    });
    let y_wide = widen(&mut body, CastOp::SExt, Ty::I32, Ty::I64, y2);
    let product = binop(&mut body, BinOp::Mul, Ty::I64, x2, y_wide);
    ret(&mut body, vec![product]);
    define(
        &mut module,
        "sweep_make_record",
        vec![Ty::I64, Ty::I32],
        vec![Ty::I64],
        body,
    );

    // A tuple of mixed register classes.
    let tuple = Ty::Tuple(vec![Ty::U32, Ty::F64, Ty::I16]);
    let mut body = Body::new();
    let x = body.param(Ty::U32);
    let y = body.param(Ty::F64);
    let z = body.param(Ty::I16);
    let value = body.emit(Inst::MakeAggregate {
        ty: tuple.clone(),
        variant: None,
        fields: vec![x, y, z],
    });
    let x2 = body.emit(Inst::ExtractField {
        ty: Ty::U32,
        aggregate: value,
        field: 0,
    });
    let y2 = body.emit(Inst::ExtractField {
        ty: Ty::F64,
        aggregate: value,
        field: 1,
    });
    let z2 = body.emit(Inst::ExtractField {
        ty: Ty::I16,
        aggregate: value,
        field: 2,
    });
    let xf = widen(&mut body, CastOp::UIToFP, Ty::U32, Ty::F64, x2);
    let zf = widen(&mut body, CastOp::SIToFP, Ty::I16, Ty::F64, z2);
    let y_twice = binop(&mut body, BinOp::FAdd, Ty::F64, y2, y2);
    let partial = binop(&mut body, BinOp::FAdd, Ty::F64, xf, y_twice);
    let total = binop(&mut body, BinOp::FAdd, Ty::F64, partial, zf);
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_make_tuple",
        vec![Ty::U32, Ty::F64, Ty::I16],
        vec![Ty::F64],
        body,
    );

    // An array, indexed at run time.
    let mut body = Body::new();
    let elems: Vec<ValueId> = (0..4).map(|_| body.param(Ty::I32)).collect();
    let index = body.param(Ty::U64);
    let value = body.emit(Inst::MakeAggregate {
        ty: array4.clone(),
        variant: None,
        fields: elems,
    });
    let picked = body.emit(Inst::ExtractElement {
        ty: Ty::I32,
        array: value,
        index,
    });
    ret(&mut body, vec![picked]);
    define(
        &mut module,
        "sweep_make_array",
        vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32, Ty::U64],
        vec![Ty::I32],
        body,
    );

    // A typed-reference lane: the aggregate no `Const` can seed.
    let mut body = Body::new();
    let reference = body.param(Ty::Ref(Box::new(Ty::I64)));
    let n = body.param(Ty::U64);
    let value = body.emit(Inst::MakeAggregate {
        ty: holder.clone(),
        variant: None,
        fields: vec![reference, n],
    });
    let reference2 = body.emit(Inst::ExtractField {
        ty: Ty::Ref(Box::new(Ty::I64)),
        aggregate: value,
        field: 0,
    });
    let pointee = body.emit(Inst::Load {
        ty: Ty::I64,
        ptr: reference2,
        volatile: false,
        align: None,
    });
    let n2 = body.emit(Inst::ExtractField {
        ty: Ty::U64,
        aggregate: value,
        field: 1,
    });
    let n_signed = widen(&mut body, CastOp::Bitcast, Ty::U64, Ty::I64, n2);
    let total = binop(&mut body, BinOp::Add, Ty::I64, pointee, n_signed);
    ret(&mut body, vec![total]);
    let through_holder = define(
        &mut module,
        "sweep_make_holder",
        vec![Ty::Ref(Box::new(Ty::I64)), Ty::U64],
        vec![Ty::I64],
        body,
    );

    let mut body = Body::new();
    let x = body.param(Ty::I64);
    let n = body.param(Ty::U64);
    let slot = body.emit(Inst::Alloca {
        ty: Ty::I64,
        count: None,
        align: None,
    });
    body.effect(Inst::Store {
        ty: Ty::I64,
        ptr: slot,
        value: x,
        volatile: false,
        align: None,
    });
    let reference = widen(
        &mut body,
        CastOp::PtrToPtr,
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::I64)),
        slot,
    );
    let total = body.emit_n(
        Inst::Call {
            callee: through_holder,
            args: vec![reference, n],
        },
        1,
    )[0];
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_holder_run",
        vec![Ty::I64, Ty::U64],
        vec![Ty::I64],
        body,
    );

    // Aggregate lanes land by value: rewriting the inner value after the
    // outer one is built must not reach the outer one.
    let mut body = Body::new();
    let a = body.param(Ty::U32);
    let b = body.param(Ty::U64);
    let elems: Vec<ValueId> = (0..3).map(|_| body.param(Ty::I32)).collect();
    let t = body.param(Ty::U16);
    let inner = body.emit(Inst::MakeAggregate {
        ty: declared.clone(),
        variant: None,
        fields: vec![a, b],
    });
    let arr = body.emit(Inst::MakeAggregate {
        ty: array3.clone(),
        variant: None,
        fields: elems,
    });
    let outer = body.emit(Inst::MakeAggregate {
        ty: nest,
        variant: None,
        fields: vec![inner, arr, t],
    });
    let zero32 = int_const(&mut body, Ty::U32, 0);
    let clobbered = body.emit(Inst::InsertField {
        ty: declared.clone(),
        aggregate: inner,
        field: 0,
        value: zero32,
    });
    let clobbered_a = body.emit(Inst::ExtractField {
        ty: Ty::U32,
        aggregate: clobbered,
        field: 0,
    });
    let inner2 = body.emit(Inst::ExtractField {
        ty: declared,
        aggregate: outer,
        field: 0,
    });
    let a2 = body.emit(Inst::ExtractField {
        ty: Ty::U32,
        aggregate: inner2,
        field: 0,
    });
    let b2 = body.emit(Inst::ExtractField {
        ty: Ty::U64,
        aggregate: inner2,
        field: 1,
    });
    let arr2 = body.emit(Inst::ExtractField {
        ty: array3,
        aggregate: outer,
        field: 1,
    });
    let two = int_const(&mut body, Ty::U64, 2);
    let e2 = body.emit(Inst::ExtractElement {
        ty: Ty::I32,
        array: arr2,
        index: two,
    });
    let t2 = body.emit(Inst::ExtractField {
        ty: Ty::U16,
        aggregate: outer,
        field: 2,
    });
    // b ^ (a << 8) ^ (sext(e2) << 24) ^ (t << 40) + clobbered_a
    let a_wide = widen(&mut body, CastOp::ZExt, Ty::U32, Ty::U64, a2);
    let e_wide = widen(&mut body, CastOp::SExt, Ty::I32, Ty::I64, e2);
    let e_bits = widen(&mut body, CastOp::Bitcast, Ty::I64, Ty::U64, e_wide);
    let t_wide = widen(&mut body, CastOp::ZExt, Ty::U16, Ty::U64, t2);
    let c_wide = widen(&mut body, CastOp::ZExt, Ty::U32, Ty::U64, clobbered_a);
    let mut total = b2;
    for (lane, shift) in [(a_wide, 8), (e_bits, 24), (t_wide, 40)] {
        let amount = int_const(&mut body, Ty::U64, shift);
        let placed = binop(&mut body, BinOp::Shl, Ty::U64, lane, amount);
        total = binop(&mut body, BinOp::Xor, Ty::U64, total, placed);
    }
    let total = binop(&mut body, BinOp::Add, Ty::U64, total, c_wide);
    ret(&mut body, vec![total]);
    define(
        &mut module,
        "sweep_make_nested",
        vec![Ty::U32, Ty::U64, Ty::I32, Ty::I32, Ty::I32, Ty::U16],
        vec![Ty::U64],
        body,
    );
    module
}

const AGGREGATE_PRELUDE: &str = r#"
struct Mixed { uint8_t a; uint64_t b; uint16_t c; };
struct Declared { uint64_t b; uint32_t a; };
struct __attribute__((packed)) Packed { uint8_t a; uint32_t b; };
_Static_assert(sizeof(struct Mixed) == 24, "Mixed");
_Static_assert(sizeof(struct Declared) == 16, "Declared");
_Static_assert(sizeof(struct Packed) == 5, "Packed");
extern void sweep_make_mixed(struct Mixed *, uint8_t, uint64_t, uint16_t);
extern void sweep_make_declared(struct Declared *, uint32_t, uint64_t);
extern void sweep_make_packed(struct Packed *, uint8_t, uint32_t);
extern void sweep_make_array_store(int32_t *, int32_t, int32_t, int32_t, int32_t);
extern int64_t sweep_make_holder(const int64_t *, uint64_t);
struct Small { uint32_t a; uint64_t b; };
extern struct Small sweep_make_small_ret(uint32_t, uint64_t);
"#;

/// The C side reads every stored image field by field (padding untouched).
const AGGREGATE_EXTRA: &str = r#"    {
        struct Mixed m; memset(&m, 0xAB, sizeof m);
        sweep_make_mixed(&m, 0xC3, 0x0123456789ABCDEFULL, 0xBEEF);
        report("mixed_a", (u128)m.a, 1, (u128)0xC3);
        report("mixed_b", (u128)m.b, 1, (u128)0x0123456789ABCDEFULL);
        report("mixed_c", (u128)m.c, 1, (u128)0xBEEF);
        struct Declared d; memset(&d, 0xAB, sizeof d);
        sweep_make_declared(&d, 0xDEADBEEFu, 0x1122334455667788ULL);
        report("declared_a", (u128)d.a, 1, (u128)0xDEADBEEFu);
        report("declared_b", (u128)d.b, 1, (u128)0x1122334455667788ULL);
        unsigned char raw[6]; memset(raw, 0xAB, sizeof raw);
        sweep_make_packed((struct Packed *)(raw + 1), 0x5A, 0xCAFEF00Du);
        struct Packed p; memcpy(&p, raw + 1, sizeof p);
        report("packed_a", (u128)p.a, 1, (u128)0x5A);
        report("packed_b", (u128)p.b, 1, (u128)0xCAFEF00Du);
        report("packed_guard", (u128)raw[0], 1, (u128)0xAB);
        int32_t arr[5] = {0, 0, 0, 0, 0x7777};
        sweep_make_array_store(arr, -1, 2, -3, 0x7FFFFFFF);
        report("stored_array_0", (u128)(uint32_t)arr[0], 1, (u128)(uint32_t)-1);
        report("stored_array_3", (u128)(uint32_t)arr[3], 1, (u128)(uint32_t)0x7FFFFFFF);
        report("stored_array_guard", (u128)(uint32_t)arr[4], 1, (u128)0x7777);
        int64_t cell = -40;
        report("holder_direct", (u128)(uint64_t)sweep_make_holder(&cell, 45), 1, (u128)5);
        struct Small small = sweep_make_small_ret(0x89ABCDEFu, 0xFEDCBA9876543210ULL);
        report("small_ret_a", (u128)small.a, 1, (u128)0x89ABCDEFu);
        report("small_ret_b", (u128)small.b, 1, (u128)0xFEDCBA9876543210ULL);
    }
"#;

#[test]
fn native_make_aggregate_builds_structs_tuples_arrays_and_nests_o0_through_o3() {
    let module = make_aggregate_module();
    let u8a = |value: u8| Arg(Ty::U8, u128::from(value));
    let u16a = |value: u16| Arg(Ty::U16, u128::from(value));
    let u32a = |value: u32| Arg(Ty::U32, u128::from(value));
    let u64a = |value: u64| Arg(Ty::U64, u128::from(value));
    let i16a = |value: i16| Arg(Ty::I16, u128::from(value as u16));
    let i32a = |value: i32| Arg(Ty::I32, u128::from(value as u32));
    let i64a = |value: i64| Arg(Ty::I64, u128::from(value as u64));
    let f64a = |value: f64| Arg(Ty::F64, u128::from(value.to_bits()));
    let calls = vec![
        Call::new(
            "mixed_sum",
            "sweep_mixed_sum",
            vec![u8a(0x9C), u64a(0xF0E1_D2C3_B4A5_9687), u16a(0x1357)],
            Ty::U64,
        )
        .c("(uint64_t)a0 ^ (a1 << 8) ^ ((uint64_t)a2 << 16)"),
        Call::new(
            "declared_sum",
            "sweep_declared_sum",
            vec![u32a(0x8765_4321), u64a(0x0FED_CBA9_8765_4321)],
            Ty::U64,
        )
        .c("(uint64_t)a0 ^ (a1 << 8)"),
        Call::new(
            "packed_sum",
            "sweep_packed_sum",
            vec![u8a(0xEE), u32a(0x0BAD_F00D)],
            Ty::U64,
        )
        .c("(uint64_t)a0 ^ ((uint64_t)a1 << 8)"),
        Call::new(
            "tuple",
            "sweep_make_tuple",
            vec![u32a(4_000_000_000), f64a(-1.25), i16a(-300)],
            Ty::F64,
        )
        .c("(double)a0 + (a1 + a1) + (double)a2"),
        Call::new(
            "array_2",
            "sweep_make_array",
            vec![i32a(10), i32a(-20), i32a(30), i32a(-40), u64a(2)],
            Ty::I32,
        )
        .c("a4 == 0 ? a0 : a4 == 1 ? a1 : a4 == 2 ? a2 : a3"),
        Call::new(
            "array_3",
            "sweep_make_array",
            vec![i32a(10), i32a(-20), i32a(30), i32a(-40), u64a(3)],
            Ty::I32,
        )
        .c("a4 == 0 ? a0 : a4 == 1 ? a1 : a4 == 2 ? a2 : a3"),
        Call::new(
            "holder",
            "sweep_holder_run",
            vec![i64a(-1_000_000_007), u64a(7)],
            Ty::I64,
        )
        .c("a0 + (int64_t)a1"),
        Call::new(
            "mixed_byval",
            "sweep_mixed_byval",
            vec![u8a(0x42), u64a(0x0011_2233_4455_6677), u16a(0x8899)],
            Ty::U64,
        )
        .c("(uint64_t)a0 ^ (a1 << 8) ^ ((uint64_t)a2 << 16)"),
        Call::new(
            "record",
            "sweep_make_record",
            vec![i64a(-123_456_789), Arg(Ty::I32, u128::from((-3i32) as u32))],
            Ty::I64,
        )
        .c("a0 * (int64_t)a1"),
        Call::new(
            "nested",
            "sweep_make_nested",
            vec![
                u32a(0xA1B2_C3D4),
                u64a(0x0102_0304_0506_0708),
                i32a(5),
                i32a(6),
                i32a(-7),
                u16a(0xFACE),
            ],
            Ty::U64,
        )
        .c("(a1 ^ ((uint64_t)a0 << 8) ^ ((uint64_t)(int64_t)a4 << 24) ^ ((uint64_t)a5 << 40)) + 0"),
    ];
    let compared = sweep(
        "make-aggregate",
        &module,
        &calls,
        &[],
        AGGREGATE_PRELUDE,
        AGGREGATE_EXTRA,
    );
    assert_eq!(compared, calls.len());
}

/// An enum variant is refused by name at every level.
#[test]
fn make_aggregate_over_an_enum_stays_refused_by_name() {
    let mut module = sweep_module("construct_sweep_make_enum");
    module.add_enum(EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "Choice".to_string(),
        variants: vec![
            EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: None,
    });
    let choice = Ty::Enum(EnumId::new(0));
    let mut body = Body::new();
    let payload = body.param(Ty::U32);
    let value = body.emit(Inst::MakeAggregate {
        ty: choice.clone(),
        variant: Some(1),
        fields: vec![payload],
    });
    ret(&mut body, vec![value]);
    define(
        &mut module,
        "sweep_make_enum",
        vec![Ty::U32],
        vec![choice],
        body,
    );
    for opt_level in LEVELS {
        let error = compile(&module, opt_level).expect_err("an enum MakeAggregate");
        assert!(
            error.contains("Inst::MakeAggregate") && error.contains("over an enum"),
            "{opt_level:?}: {error}"
        );
    }
}

/// The compile service binds every artifact to the module's canonical tMBC
/// image. Before trust-ir's v51 INST wire batch (`e2154f00`) `MakeAggregate`
/// had no wire tag, and `CompileService` refused such a module by name
/// (`compile.identity_input`); at v51 it has one, so the service binds the
/// image and compiles a `MakeAggregate` module exactly like the same function
/// spelled without it, for an object and an executable-memory artifact alike.
#[test]
fn the_compile_service_compiles_make_aggregate_modules_at_v51() {
    let module_for = |with_make_aggregate: bool| {
        let mut module = sweep_module("construct_sweep_make_service");
        let mut body = Body::new();
        let a = body.param(Ty::U32);
        let b = body.param(Ty::U64);
        let total = if with_make_aggregate {
            let pair = body.emit(Inst::MakeAggregate {
                ty: Ty::Tuple(vec![Ty::U32, Ty::U64]),
                variant: None,
                fields: vec![a, b],
            });
            body.emit(Inst::ExtractField {
                ty: Ty::U64,
                aggregate: pair,
                field: 1,
            })
        } else {
            b
        };
        ret(&mut body, vec![total]);
        define(
            &mut module,
            "sweep_make_service",
            vec![Ty::U32, Ty::U64],
            vec![Ty::U64],
            body,
        );
        module
    };
    let spec = TargetSpec::parse(TRIPLE).expect("the Darwin AArch64 target");
    for kind in [ArtifactKind::Object, ArtifactKind::ExecutableMemory] {
        let service = CompileService::new(CompileServiceConfig {
            codegen_license: permit_unlicensed(),
            ..CompileServiceConfig::default()
        });
        let request = |id: &str| {
            let mut request = CompileRequest::new(id, CompileGeneration::new(1));
            request.artifact_kind = kind;
            request.install_intent = InstallIntent::CompileOnly;
            request
        };
        let control = service.compile_plan(
            CompilePlan::new(request("make-service-control"), spec),
            &module_for(false),
        );
        assert_eq!(
            control.status,
            CompileStatus::Compiled,
            "{kind:?} control: {:?}",
            control.diagnostics
        );
        let aggregate = service.compile_plan(
            CompilePlan::new(request("make-service-aggregate"), spec),
            &module_for(true),
        );
        assert_eq!(
            aggregate.status,
            CompileStatus::Compiled,
            "{kind:?}: {:?}",
            aggregate.diagnostics
        );
        assert!(
            !aggregate
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "compile.identity_input"),
            "{kind:?}: {:?}",
            aggregate.diagnostics
        );
    }
}

/// trust-ir v50 uniform arrays: `Inst::ArraySplat` of a register (lane 0 and
/// a doubling copy), of a byte-uniform constant (one memset) and of a tuple
/// built by `MakeAggregate`; `Constant::Splat` in a body (byte-uniform,
/// mixed-byte, a float, a splat of splats, a splat field of a tuple constant,
/// an insert into a zero splat) and as global initializers (a mixed-byte
/// table and a zero table). Every function reads lanes back by a runtime
/// index, including the first and last lane and lanes on each side of a
/// doubling boundary.
fn array_splat_module() -> Module {
    let mut module = sweep_module("construct_sweep_array_splat");
    let u32_id = module
        .add_type(Ty::U32)
        .expect("Module::add_type: test fixture");
    let u8_id = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let u64_id = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let u16_id = module
        .add_type(Ty::U16)
        .expect("Module::add_type: test fixture");
    let f64_id = module
        .add_type(Ty::F64)
        .expect("Module::add_type: test fixture");
    let row_id = module
        .add_type(Ty::Array(u16_id, 3))
        .expect("Module::add_type: test fixture");
    let pair = Ty::Tuple(vec![Ty::U8, Ty::U64]);
    let pair_id = module
        .add_type(pair.clone())
        .expect("Module::add_type: test fixture");
    let splat = |elem: Constant, len: u64| Constant::Splat {
        elem: Box::new(elem),
        len,
    };
    let extract = |body: &mut Body, ty: Ty, array: ValueId, index: ValueId| {
        body.emit(Inst::ExtractElement { ty, array, index })
    };

    // [x; 1000][i], x a register: one store, then a doubling copy.
    let mut body = Body::new();
    let x = body.param(Ty::U32);
    let i = body.param(Ty::U64);
    let array = body.emit(Inst::ArraySplat {
        ty: Ty::Array(u32_id, 1000),
        value: x,
    });
    let lane = extract(&mut body, Ty::U32, array, i);
    ret(&mut body, vec![lane]);
    define(
        &mut module,
        "sweep_splat_u32",
        vec![Ty::U32, Ty::U64],
        vec![Ty::U32],
        body,
    );

    // splat[0xA5; 4096][i]: one memset.
    let mut body = Body::new();
    let i = body.param(Ty::U64);
    let array = body.emit(Inst::Const {
        ty: Ty::Array(u8_id, 4096),
        value: splat(Constant::Int(0xA5), 4096),
    });
    let lane = extract(&mut body, Ty::U8, array, i);
    ret(&mut body, vec![lane]);
    define(
        &mut module,
        "sweep_splat_bytes",
        vec![Ty::U64],
        vec![Ty::U8],
        body,
    );

    // [7u8; 3000][i], the element a constant register: one memset.
    let mut body = Body::new();
    let i = body.param(Ty::U64);
    let seven = int_const(&mut body, Ty::U8, 7);
    let array = body.emit(Inst::ArraySplat {
        ty: Ty::Array(u8_id, 3000),
        value: seven,
    });
    let lane = extract(&mut body, Ty::U8, array, i);
    ret(&mut body, vec![lane]);
    define(
        &mut module,
        "sweep_splat_register_byte",
        vec![Ty::U64],
        vec![Ty::U8],
        body,
    );

    // (splat[0u64; 1000] with [i] = v)[j].
    let mut body = Body::new();
    let i = body.param(Ty::U64);
    let v = body.param(Ty::U64);
    let j = body.param(Ty::U64);
    let zeros = body.emit(Inst::Const {
        ty: Ty::Array(u64_id, 1000),
        value: splat(Constant::Int(0), 1000),
    });
    let written = body.emit(Inst::InsertElement {
        ty: Ty::Array(u64_id, 1000),
        array: zeros,
        index: i,
        value: v,
    });
    let lane = extract(&mut body, Ty::U64, written, j);
    ret(&mut body, vec![lane]);
    define(
        &mut module,
        "sweep_splat_insert",
        vec![Ty::U64, Ty::U64, Ty::U64],
        vec![Ty::U64],
        body,
    );

    // splat[-2.5; 100][i]: a float has no one-byte image.
    let mut body = Body::new();
    let i = body.param(Ty::U64);
    let array = body.emit(Inst::Const {
        ty: Ty::Array(f64_id, 100),
        value: splat(Constant::Float(-2.5), 100),
    });
    let lane = extract(&mut body, Ty::F64, array, i);
    ret(&mut body, vec![lane]);
    define(
        &mut module,
        "sweep_splat_float",
        vec![Ty::U64],
        vec![Ty::F64],
        body,
    );

    // splat[splat[0x1234u16; 3]; 65537][i][j].
    let mut body = Body::new();
    let i = body.param(Ty::U64);
    let j = body.param(Ty::U64);
    let rows = body.emit(Inst::Const {
        ty: Ty::Array(row_id, 65537),
        value: splat(splat(Constant::Int(0x1234), 3), 65537),
    });
    let row = extract(&mut body, Ty::Array(u16_id, 3), rows, i);
    let lane = extract(&mut body, Ty::U16, row, j);
    ret(&mut body, vec![lane]);
    define(
        &mut module,
        "sweep_splat_nested",
        vec![Ty::U64, Ty::U64],
        vec![Ty::U16],
        body,
    );

    // [(a, b); 33][i].1, the element a tuple register.
    let mut body = Body::new();
    let a = body.param(Ty::U8);
    let b = body.param(Ty::U64);
    let i = body.param(Ty::U64);
    let element = body.emit(Inst::MakeAggregate {
        ty: pair.clone(),
        variant: None,
        fields: vec![a, b],
    });
    let array = body.emit(Inst::ArraySplat {
        ty: Ty::Array(pair_id, 33),
        value: element,
    });
    let picked = extract(&mut body, pair.clone(), array, i);
    let second = body.emit(Inst::ExtractField {
        ty: Ty::U64,
        aggregate: picked,
        field: 1,
    });
    ret(&mut body, vec![second]);
    define(
        &mut module,
        "sweep_splat_pair",
        vec![Ty::U8, Ty::U64, Ty::U64],
        vec![Ty::U64],
        body,
    );

    // (9u8, splat[0xC0FFEE; 77]).1[i]: a splat field of a tuple constant.
    let mut body = Body::new();
    let i = body.param(Ty::U64);
    let tuple = body.emit(Inst::Const {
        ty: Ty::Tuple(vec![Ty::U8, Ty::Array(u32_id, 77)]),
        value: Constant::Aggregate(vec![Constant::Int(9), splat(Constant::Int(0xC0_FFEE), 77)]),
    });
    let field = body.emit(Inst::ExtractField {
        ty: Ty::Array(u32_id, 77),
        aggregate: tuple,
        field: 1,
    });
    let lane = extract(&mut body, Ty::U32, field, i);
    ret(&mut body, vec![lane]);
    define(
        &mut module,
        "sweep_splat_tuple_field",
        vec![Ty::U64],
        vec![Ty::U32],
        body,
    );

    // Global tables: a mixed-byte splat and a zero splat, read through their
    // addresses.
    for (name, ty, elem, len, initializer) in [
        (
            "SPLAT_WORDS",
            Ty::U32,
            u32_id,
            1024,
            splat(Constant::Int(0x0102_0304), 1024),
        ),
        (
            "SPLAT_ZEROS",
            Ty::U64,
            u64_id,
            4096,
            splat(Constant::Int(0), 4096),
        ),
    ] {
        module.globals.push(Global {
            name: name.to_string(),
            ty: Ty::Array(elem, len),
            mutable: false,
            initializer: Some(initializer),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        });
        let global = GlobalId::new(module.globals.len() as u32 - 1);
        let mut body = Body::new();
        let i = body.param(Ty::U64);
        let base = body.emit(Inst::GlobalAddr { global });
        let slot = body.emit(Inst::GEP {
            pointee_ty: ty.clone(),
            base,
            indices: vec![i],
            inbounds: true,
        });
        let lane = body.emit(Inst::Load {
            ty: ty.clone(),
            ptr: slot,
            volatile: false,
            align: None,
        });
        ret(&mut body, vec![lane]);
        let func = if name == "SPLAT_WORDS" {
            "sweep_splat_global_words"
        } else {
            "sweep_splat_global_zeros"
        };
        define(&mut module, func, vec![Ty::U64], vec![ty], body);
    }
    module
}

#[test]
fn native_array_splat_and_splat_constants_fill_every_lane_o0_through_o3() {
    let module = array_splat_module();
    let u8a = |value: u8| Arg(Ty::U8, u128::from(value));
    let u32a = |value: u32| Arg(Ty::U32, u128::from(value));
    let u64a = |value: u64| Arg(Ty::U64, u128::from(value));
    let mut calls = Vec::new();
    for i in [0u64, 1, 511, 512, 999] {
        calls.push(
            Call::new(
                format!("u32_{i}"),
                "sweep_splat_u32",
                vec![u32a(0xDEAD_BEEF), u64a(i)],
                Ty::U32,
            )
            .c("a0"),
        );
    }
    for i in [0u64, 2047, 2048, 4095] {
        calls.push(
            Call::new(
                format!("bytes_{i}"),
                "sweep_splat_bytes",
                vec![u64a(i)],
                Ty::U8,
            )
            .c("(uint8_t)0xA5"),
        );
    }
    for i in [0u64, 1499, 1500, 2999] {
        calls.push(
            Call::new(
                format!("register_byte_{i}"),
                "sweep_splat_register_byte",
                vec![u64a(i)],
                Ty::U8,
            )
            .c("(uint8_t)7"),
        );
    }
    for (i, j) in [(0u64, 0u64), (0, 999), (512, 512), (999, 998)] {
        calls.push(
            Call::new(
                format!("insert_{i}_{j}"),
                "sweep_splat_insert",
                vec![u64a(i), u64a(0x0123_4567_89AB_CDEF), u64a(j)],
                Ty::U64,
            )
            .c("a2 == a0 ? a1 : 0"),
        );
    }
    for i in [0u64, 63, 64, 99] {
        calls.push(
            Call::new(
                format!("float_{i}"),
                "sweep_splat_float",
                vec![u64a(i)],
                Ty::F64,
            )
            .c("-2.5"),
        );
    }
    for (i, j) in [(0u64, 0u64), (32768, 1), (65536, 2)] {
        calls.push(
            Call::new(
                format!("nested_{i}_{j}"),
                "sweep_splat_nested",
                vec![u64a(i), u64a(j)],
                Ty::U16,
            )
            .c("(uint16_t)0x1234"),
        );
    }
    for i in [0u64, 16, 32] {
        calls.push(
            Call::new(
                format!("pair_{i}"),
                "sweep_splat_pair",
                vec![u8a(0x5A), u64a(0xFEDC_BA98_7654_3210), u64a(i)],
                Ty::U64,
            )
            .c("a1"),
        );
    }
    for i in [0u64, 38, 76] {
        calls.push(
            Call::new(
                format!("tuple_field_{i}"),
                "sweep_splat_tuple_field",
                vec![u64a(i)],
                Ty::U32,
            )
            .c("(uint32_t)0xC0FFEE"),
        );
    }
    for i in [0u64, 512, 1023] {
        calls.push(
            Call::new(
                format!("global_words_{i}"),
                "sweep_splat_global_words",
                vec![u64a(i)],
                Ty::U32,
            )
            .c("(uint32_t)0x01020304"),
        );
        calls.push(
            Call::new(
                format!("global_zeros_{i}"),
                "sweep_splat_global_zeros",
                vec![u64a(i)],
                Ty::U64,
            )
            .c("(uint64_t)0"),
        );
    }
    let compared = sweep("array-splat", &module, &calls, &[], "", "");
    assert_eq!(compared, calls.len());
}
