// Symbolic execution: holds fsym's layout port to trust-ir's reference interpreter, by execution
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `fsym_layout` ports the reference interpreter's byte layout (its layout
//! functions are private); every size, stride, alignment and initialized
//! byte fsym reasons with comes from it. This test MEASURES the interpreter's
//! numbers by executing probes and compares every one with the port, over a
//! catalog of types (scalars, pointers, fat pointers, `<N x bool>` and other
//! vectors, arrays, tuples with and without a declared layout, structs
//! synthesized, declared, packed and transparent, canonical and
//! descriptor-laid enums, a zero-sized type aligned to 2^63, and types with
//! no layout) at 64 bits (target-free and x86_64) and at 32 (wasm32):
//!
//! * SIZE: `gep T, p, 1` minus `p` (the interpreter's GEP stride is its
//!   `byte_size`); a type the interpreter cannot lay out faults the GEP with
//!   a type error, and the port must refuse it too.
//! * ALIGNMENT: the stride of `{ u8, T }` minus `T`'s size (the interpreter
//!   places `T` at its `byte_align`, and every interpreter size is a multiple
//!   of its alignment).
//! * WRITTEN BYTES: fill a buffer, store a `T` value, read each byte back and
//!   inspect it: a byte the store left uninitialized is poison (UB when
//!   inspected). fsym may claim a byte written only if the interpreter wrote
//!   it — and, with no enum nested below the top, exactly those.
//! * READ BYTES: a load of `T` from a buffer with exactly one byte left
//!   uninitialized must not be UB wherever fsym's read mask says the byte is
//!   not needed — with the buffer filled by each of several bytes, so an
//!   enum's tag names each of its variants in turn (a load needs the fields
//!   of the variant its tag names).

use trust_cg_verify::fsym_layout::FsymLayout;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, EnumDef, EnumId, EnumLayoutDescriptor,
    EnumTagEncoding, EnumTagRepr, EnumVariant, FatPtrKind, FieldDef, FuncId, FuncTy, FuncTyId,
    Function, Inst, InstrNode, InterpretErrorCode, InterpretOptions, Interpreter, Module,
    StructDef, StructId, StructRepr, TupleLayoutDescriptor, Ty, TyId, ValueId,
};

fn x86_64() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    }
}

fn wasm32() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "wasm32-unknown-unknown".to_string(),
        pointer_size: 4,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    }
}

fn field(ty: Ty, offset: Option<u64>) -> FieldDef {
    FieldDef {
        name: "f".to_string(),
        ty,
        offset,
    }
}

fn struct_def(
    id: u32,
    fields: Vec<FieldDef>,
    size: Option<u64>,
    align: Option<u64>,
    repr: StructRepr,
) -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(id),
        name: format!("S{id}"),
        fields,
        size,
        align,
        repr,
    }
}

fn variant(fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: "V".to_string(),
        fields,
        field_names: Vec::new(),
    }
}

/// The catalog's named types (the struct / enum / type tables they need).
const PAD: u32 = 0;
const DECLARED: u32 = 1;
const PACKED: u32 = 2;
const TRANSPARENT: u32 = 3;
const NESTED: u32 = 4;
const BIG: u32 = 5;
const HUGE: u32 = 6;
const HALF_DECLARED: u32 = 7;
const OVERLAPPING: u32 = 8;
const WITH_ENUM: u32 = 9;
/// Probe structs `{ u8, T }` start here, one per catalog type.
const PROBES: u32 = 100;

fn base_module(name: &str, target: Option<trust_ir::TargetInfo>) -> Module {
    let mut module = Module::new(name);
    module.target_info = target;
    // ty.0 i32, ty.1 bool, ty.2 Pad, ty.3 (u8, u16, u8) (declared below)
    module.types = vec![
        Ty::I32,
        Ty::Bool,
        Ty::Struct(StructId::new(PAD)),
        Ty::Tuple(vec![Ty::U8, Ty::U16, Ty::U8]),
    ];
    if module.target_info.is_some() {
        module.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: TyId::new(3),
            size: 4,
            align: 2,
            field_offsets: vec![2, 0, 3],
        });
    }
    let rust = StructRepr::Rust;
    module.structs = vec![
        struct_def(
            PAD,
            vec![field(Ty::U8, None), field(Ty::U64, None)],
            None,
            None,
            rust,
        ),
        struct_def(
            DECLARED,
            vec![field(Ty::U8, Some(8))],
            Some(16),
            Some(1),
            rust,
        ),
        struct_def(
            PACKED,
            vec![field(Ty::U8, Some(0)), field(Ty::U32, Some(1))],
            Some(5),
            Some(1),
            StructRepr::Packed(1),
        ),
        struct_def(
            TRANSPARENT,
            vec![field(Ty::U32, Some(0))],
            Some(4),
            Some(4),
            StructRepr::Transparent,
        ),
        struct_def(
            NESTED,
            vec![
                field(Ty::Struct(StructId::new(PAD)), None),
                field(Ty::U8, None),
            ],
            None,
            None,
            rust,
        ),
        struct_def(
            BIG,
            vec![field(Ty::U8, Some(0))],
            Some(1 << 62),
            Some(1),
            rust,
        ),
        struct_def(HUGE, vec![], Some(0), Some(1 << 63), rust),
        // Incoherent declarations: a size with no alignment; overlapping
        // fields. Neither has a layout.
        struct_def(
            HALF_DECLARED,
            vec![field(Ty::U8, Some(0))],
            Some(8),
            None,
            rust,
        ),
        struct_def(
            OVERLAPPING,
            vec![field(Ty::U32, Some(0)), field(Ty::U16, Some(2))],
            Some(4),
            Some(4),
            rust,
        ),
        struct_def(
            WITH_ENUM,
            vec![field(Ty::U8, None), field(Ty::Enum(EnumId::new(0)), None)],
            None,
            None,
            rust,
        ),
    ];
    // enum.0 canonical `E { A, B(i32), C(i64, u8) }`; enum.1 a direct-tag
    // descriptor; enum.2 a niche descriptor (`Option<&T>`-like); enum.3 a
    // descriptor whose tag overlaps a field (no layout).
    module.enums = vec![
        EnumDef::new(
            EnumId::new(0),
            "E",
            vec![
                variant(vec![]),
                variant(vec![Ty::I32]),
                variant(vec![Ty::I64, Ty::U8]),
            ],
        ),
        {
            let mut def = EnumDef::new(
                EnumId::new(1),
                "Direct",
                vec![variant(vec![]), variant(vec![Ty::U64])],
            );
            def.layout = Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Direct { tag_offset: 0 },
                size: 16,
                align: 8,
                variant_field_offsets: vec![vec![], vec![8]],
            });
            def
        },
        {
            let mut def = EnumDef::new(
                EnumId::new(2),
                "Niche",
                vec![variant(vec![]), variant(vec![Ty::U64])],
            );
            def.layout = Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Niche {
                    untagged_variant: 1,
                    niche_variants_start: 0,
                    niche_variants_end: 0,
                    niche_start: 0,
                    niche_offset: 0,
                    niche_ty: EnumTagRepr::U64,
                },
                size: 8,
                align: 8,
                variant_field_offsets: vec![vec![], vec![0]],
            });
            def
        },
        {
            let mut def = EnumDef::new(
                EnumId::new(3),
                "Clash",
                vec![variant(vec![]), variant(vec![Ty::U64])],
            );
            def.layout = Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Direct { tag_offset: 0 },
                size: 8,
                align: 8,
                variant_field_offsets: vec![vec![], vec![0]],
            });
            def
        },
    ];
    for active in 0..2 {
        let mut variants = vec![variant(vec![Ty::Never]); 2];
        variants[active] = variant(vec![Ty::U32]);
        let mut offsets = vec![vec![]; 2];
        offsets[active] = vec![0];
        let mut def = EnumDef::new(EnumId::new(4 + active as u32), "SingleInhabited", variants);
        def.discriminants = vec![Some(7), Some(23)];
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::SingleInhabited {
                variant: active as u32,
            },
            size: 4,
            align: 4,
            variant_field_offsets: offsets,
        });
        module.enums.push(def);
    }
    module
}

/// The catalog of types each target is measured on.
fn catalog() -> Vec<Ty> {
    let s = |id| Ty::Struct(StructId::new(id));
    let e = |id| Ty::Enum(EnumId::new(id));
    vec![
        Ty::Bool,
        Ty::I8,
        Ty::U16,
        Ty::I32,
        Ty::U64,
        Ty::I128,
        Ty::F32,
        Ty::F64,
        Ty::Char,
        Ty::Usize,
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Vector(Box::new(Ty::Bool), 4),
        Ty::Vector(Box::new(Ty::Bool), 3),
        Ty::Vector(Box::new(Ty::I32), 4),
        Ty::Vector(Box::new(Ty::U8), 3),
        Ty::Vector(Box::new(Ty::I64), 2),
        Ty::Vector(Box::new(Ty::I32), 0),
        Ty::Array(TyId::new(0), 3),
        Ty::Array(TyId::new(1), 5),
        Ty::Array(TyId::new(2), 2),
        Ty::Array(TyId::new(9), 2),
        Ty::Tuple(vec![Ty::I32, Ty::I64]),
        Ty::Tuple(vec![Ty::U8, Ty::U16, Ty::U8]),
        Ty::Tuple(vec![]),
        Ty::Tuple(vec![Ty::Bool, Ty::Vector(Box::new(Ty::Bool), 4)]),
        s(PAD),
        s(DECLARED),
        s(PACKED),
        s(TRANSPARENT),
        s(NESTED),
        s(BIG),
        s(HUGE),
        s(HALF_DECLARED),
        s(OVERLAPPING),
        s(WITH_ENUM),
        s(77),
        e(0),
        e(1),
        e(2),
        e(3),
        e(4),
        e(5),
        Ty::Func(FuncTyId::new(0)),
        Ty::Storage(trust_ir::StorageLayout::new(80, 8)),
        Ty::Storage(trust_ir::StorageLayout::new(0, 32)),
    ]
}

/// `name() -> int`: returns `ptrtoint(gep T, p, 1) - ptrtoint(p)` for `p`
/// a 64-byte buffer — the interpreter's stride of `T`.
fn stride_probe(name: &str, ty: Ty, int: Ty) -> (FuncTy, Function) {
    let v = ValueId::new;
    let node = |result: u32, inst: Inst| InstrNode::new(inst).with_result(v(result));
    let body = vec![
        node(
            0,
            Inst::Const {
                ty: int.clone(),
                value: Constant::Int(64),
            },
        ),
        node(
            1,
            Inst::Alloca {
                ty: Ty::U8,
                count: Some(v(0)),
                align: Some(64),
            },
        ),
        node(
            2,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            },
        ),
        node(
            3,
            Inst::GEP {
                pointee_ty: ty,
                base: v(1),
                indices: vec![v(2)],
                inbounds: false,
            },
        ),
        node(
            4,
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: int.clone(),
                operand: v(3),
            },
        ),
        node(
            5,
            Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: int.clone(),
                operand: v(1),
            },
        ),
        node(
            6,
            Inst::BinOp {
                op: BinOp::Sub,
                ty: int.clone(),
                lhs: v(4),
                rhs: v(5),
            },
        ),
        InstrNode::new(Inst::Return { values: vec![v(6)] }),
    ];
    let mut function = Function::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    (
        FuncTy {
            params: vec![],
            returns: vec![int],
            abi: None,
            is_vararg: false,
        },
        function,
    )
}

/// Install `function` (typed `ty`) into `module`; its id.
fn install(module: &mut Module, ty: FuncTy, mut function: Function) -> FuncId {
    let ty_id = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(ty);
    let id = FuncId::new(module.functions.len() as u32);
    function.id = id;
    function.ty = ty_id;
    module.functions.push(function);
    id
}

enum Measured {
    Value(u64),
    /// The interpreter has no layout for the type (a type error).
    NoLayout(String),
    /// Anything else (the probe itself faulted): no measurement.
    Other(String),
}

fn run(module: &Module, function: FuncId) -> Measured {
    let interpreter = Interpreter::with_module(module).with_options(InterpretOptions {
        fuel: 10_000,
        max_call_depth: 4,
        panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
    });
    match interpreter.execute_func(function, vec![]) {
        Ok(outcome) => Measured::Value(
            outcome
                .returns
                .first()
                .and_then(|value| value.as_int())
                .map(|int| int.as_unsigned() as u64)
                .expect("the probe returns an integer"),
        ),
        Err(error)
            if matches!(
                error.code,
                InterpretErrorCode::TypeError
                    | InterpretErrorCode::UnsupportedVectorShape
                    | InterpretErrorCode::UnsupportedMemory
            ) =>
        {
            Measured::NoLayout(error.to_string())
        }
        Err(error) => Measured::Other(error.to_string()),
    }
}

#[test]
fn sizes_and_alignments_are_the_interpreters() {
    let mut failures = Vec::new();
    let mut measured = 0usize;
    for (target_name, target) in [
        ("target-free", None),
        ("x86_64", Some(x86_64())),
        ("wasm32", Some(wasm32())),
    ] {
        let int = if target.is_some() { Ty::Usize } else { Ty::U64 };
        let catalog = catalog();
        let mut module = base_module(target_name, target.clone());
        // One `{ u8, T }` probe struct per catalog type.
        for (index, ty) in catalog.iter().enumerate() {
            module.structs.push(struct_def(
                PROBES + index as u32,
                vec![field(Ty::U8, None), field(ty.clone(), None)],
                None,
                None,
                StructRepr::Rust,
            ));
        }
        let mut probes = Vec::new();
        for (index, ty) in catalog.iter().enumerate() {
            let (fty, f) = stride_probe(&format!("size{index}"), ty.clone(), int.clone());
            let size = install(&mut module, fty, f);
            let (fty, f) = stride_probe(
                &format!("align{index}"),
                Ty::Struct(StructId::new(PROBES + index as u32)),
                int.clone(),
            );
            let align = install(&mut module, fty, f);
            probes.push((ty.clone(), size, align));
        }
        let layout = FsymLayout::new(&module);
        for (ty, size_probe, align_probe) in probes {
            let ported_size = layout.size(&ty);
            let ported_align = layout.align(&ty);
            match (run(&module, size_probe), &ported_size) {
                (Measured::Value(size), Ok(ported)) if size == *ported => measured += 1,
                (Measured::NoLayout(_), Err(_)) => measured += 1,
                // A stride the probe cannot take on this target (past a
                // 32-bit address space): the size is not measurable here.
                (Measured::Other(_), Ok(ported)) if *ported > (1 << 31) => {}
                (interpreter, ported) => failures.push(format!(
                    "{target_name} {ty:?}: interpreter size {}, fsym {ported:?}",
                    describe(&interpreter)
                )),
            }
            let size = ported_size.as_ref().ok().copied();
            match (run(&module, align_probe), &ported_align, size) {
                (Measured::Value(stride), Ok(ported), Some(size)) if stride - size == *ported => {
                    measured += 1
                }
                (Measured::NoLayout(_), Err(_), _) => measured += 1,
                (Measured::Other(_), Ok(ported), Some(size))
                    if (*ported).saturating_add(size) > (1 << 31) => {}
                (interpreter, ported, size) => failures.push(format!(
                    "{target_name} {ty:?}: interpreter {{u8, T}} stride {} (T size {size:?}), fsym alignment {ported:?}",
                    describe(&interpreter)
                )),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} layout disagreement(s) with the reference interpreter:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert!(measured >= 200, "only {measured} measurements agreed");
}

fn describe(measured: &Measured) -> String {
    match measured {
        Measured::Value(value) => value.to_string(),
        Measured::NoLayout(error) => format!("none ({error})"),
        Measured::Other(error) => format!("unmeasured ({error})"),
    }
}

/// `f() -> u8`: fill a `size`-byte buffer, `store T value`, then read byte
/// `byte` and inspect it (`or`). `value` builds the stored value.
fn written_probe(
    module: &mut Module,
    ty: &Ty,
    size: u64,
    byte: u64,
    value: &dyn Fn(&mut Vec<InstrNode>, u32) -> u32,
) -> FuncId {
    let v = ValueId::new;
    let node = |result: u32, inst: Inst| InstrNode::new(inst).with_result(v(result));
    let mut body = vec![
        node(
            0,
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(i128::from(size)),
            },
        ),
        node(
            1,
            Inst::Alloca {
                ty: Ty::U8,
                count: Some(v(0)),
                align: Some(16),
            },
        ),
        node(
            2,
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(0xAB),
            },
        ),
        InstrNode::new(Inst::MemSet {
            dst: v(1),
            byte: v(2),
            bytes: v(0),
        }),
    ];
    let stored = value(&mut body, 10);
    body.push(InstrNode::new(Inst::Store {
        ty: ty.clone(),
        ptr: v(1),
        value: v(stored),
        volatile: false,
        align: None,
    }));
    body.push(node(
        3,
        Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(i128::from(byte)),
        },
    ));
    body.push(node(
        4,
        Inst::GEP {
            pointee_ty: Ty::U8,
            base: v(1),
            indices: vec![v(3)],
            inbounds: false,
        },
    ));
    body.push(node(
        5,
        Inst::Load {
            ty: Ty::U8,
            ptr: v(4),
            volatile: false,
            align: None,
        },
    ));
    body.push(node(
        6,
        Inst::BinOp {
            op: BinOp::Or,
            ty: Ty::U8,
            lhs: v(5),
            rhs: v(5),
        },
    ));
    body.push(InstrNode::new(Inst::Return { values: vec![v(6)] }));
    let mut function = Function::new(FuncId::new(0), "w", FuncTyId::new(0), BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    install(
        module,
        FuncTy {
            params: vec![],
            returns: vec![Ty::U8],
            abi: None,
            is_vararg: false,
        },
        function,
    )
}

/// A constant `value` of type `ty`, as the node building it.
fn constant(ty: Ty, value: Constant) -> impl Fn(&mut Vec<InstrNode>, u32) -> u32 {
    move |body, at| {
        body.push(
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: value.clone(),
            })
            .with_result(ValueId::new(at)),
        );
        at
    }
}

/// `MakeAggregate` of `ty` (`variant`) from integer constants `fields`.
fn aggregate(
    ty: Ty,
    variant: Option<u32>,
    fields: Vec<(Ty, i128)>,
) -> impl Fn(&mut Vec<InstrNode>, u32) -> u32 {
    move |body, at| {
        let mut values = Vec::new();
        for (index, (ty, value)) in fields.iter().enumerate() {
            let id = at + 1 + index as u32;
            body.push(
                InstrNode::new(Inst::Const {
                    ty: ty.clone(),
                    value: Constant::Int(*value),
                })
                .with_result(ValueId::new(id)),
            );
            values.push(ValueId::new(id));
        }
        body.push(
            InstrNode::new(Inst::MakeAggregate {
                ty: ty.clone(),
                variant,
                fields: values,
            })
            .with_result(ValueId::new(at)),
        );
        at
    }
}

#[test]
fn a_typed_store_writes_the_bytes_fsym_says_and_no_others() {
    let s = |id| Ty::Struct(StructId::new(id));
    let e0 = Ty::Enum(EnumId::new(0));
    type Build = Box<dyn Fn(&mut Vec<InstrNode>, u32) -> u32>;
    // (type, known variant, builder, nests an enum below the top)
    let cases: Vec<(Ty, Option<u32>, Build, bool)> = vec![
        (
            Ty::Enum(EnumId::new(4)),
            None,
            Box::new(aggregate(
                Ty::Enum(EnumId::new(4)),
                Some(0),
                vec![(Ty::U32, 0x12345678)],
            )),
            false,
        ),
        (
            Ty::Enum(EnumId::new(5)),
            None,
            Box::new(aggregate(
                Ty::Enum(EnumId::new(5)),
                Some(1),
                vec![(Ty::U32, 0x12345678)],
            )),
            false,
        ),
        (
            s(PAD),
            None,
            Box::new(aggregate(s(PAD), None, vec![(Ty::U8, 1), (Ty::U64, 2)])),
            false,
        ),
        (
            s(DECLARED),
            None,
            Box::new(aggregate(s(DECLARED), None, vec![(Ty::U8, 1)])),
            false,
        ),
        (
            s(PACKED),
            None,
            Box::new(aggregate(s(PACKED), None, vec![(Ty::U8, 1), (Ty::U32, 2)])),
            false,
        ),
        (
            Ty::Tuple(vec![Ty::I32, Ty::I64]),
            None,
            Box::new(aggregate(
                Ty::Tuple(vec![Ty::I32, Ty::I64]),
                None,
                vec![(Ty::I32, 1), (Ty::I64, 2)],
            )),
            false,
        ),
        (
            Ty::Vector(Box::new(Ty::Bool), 4),
            None,
            Box::new(constant(
                Ty::Vector(Box::new(Ty::Bool), 4),
                Constant::Vector(vec![Constant::Bool(true); 4]),
            )),
            false,
        ),
        (
            Ty::U32,
            None,
            Box::new(constant(Ty::U32, Constant::Int(5))),
            false,
        ),
        (
            e0.clone(),
            Some(0),
            Box::new(aggregate(e0.clone(), Some(0), vec![])),
            false,
        ),
        (
            e0.clone(),
            Some(1),
            Box::new(aggregate(e0.clone(), Some(1), vec![(Ty::I32, 3)])),
            false,
        ),
        (
            e0.clone(),
            Some(2),
            Box::new(aggregate(
                e0.clone(),
                Some(2),
                vec![(Ty::I64, 3), (Ty::U8, 4)],
            )),
            false,
        ),
        // The variant not tracked: fsym claims only the tag lane written —
        // whichever variant is stored, the shorter (`B`) included, whose
        // store leaves the bytes only `C` covers uninitialized.
        (
            e0.clone(),
            None,
            Box::new(aggregate(
                e0.clone(),
                Some(2),
                vec![(Ty::I64, 3), (Ty::U8, 4)],
            )),
            true,
        ),
        (
            e0.clone(),
            None,
            Box::new(aggregate(e0.clone(), Some(1), vec![(Ty::I32, 3)])),
            true,
        ),
    ];
    let mut failures = Vec::new();
    let mut probes = 0usize;
    for (ty, variant, build, nests_enum) in &cases {
        let mut module = base_module("written", Some(x86_64()));
        let layout = FsymLayout::new(&module);
        let size = layout.size(ty).expect("the case lays out");
        let coverage = layout
            .written_coverage(ty, *variant)
            .expect("the case has a coverage");
        assert_eq!(coverage.size(), size, "{ty:?}");
        let claimed: Vec<bool> = (0..size).map(|byte| coverage.contains(byte)).collect();
        let mut written = Vec::new();
        for byte in 0..size {
            let probe = written_probe(&mut module, ty, size.max(1), byte, build.as_ref());
            written.push(match run(&module, probe) {
                Measured::Value(_) => true,
                Measured::Other(message) if message.contains("uninitialized") => false,
                other => panic!("{ty:?} byte {byte}: probe failed: {}", describe(&other)),
            });
            probes += 1;
        }
        let unsound = claimed
            .iter()
            .zip(&written)
            .enumerate()
            .filter(|(_, (claimed, written))| **claimed && !**written)
            .map(|(byte, _)| byte)
            .collect::<Vec<_>>();
        if !unsound.is_empty() || (!nests_enum && claimed != written) {
            failures.push(format!(
                "{ty:?} (variant {variant:?}): fsym says written {claimed:?}, the interpreter wrote {written:?}"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(probes >= 80, "only {probes} probes");
}

/// `f() -> i64`: fill a `size`-byte buffer with `fill` except byte `hole`
/// (`None`: every byte), then load a `T` from it.
fn read_probe(module: &mut Module, ty: &Ty, size: u64, hole: Option<u64>, fill: u8) -> FuncId {
    // With no hole, the "hole" is one past the end and the second fill
    // writes nothing.
    let (hole, after) = match hole {
        Some(hole) => (hole, size - hole - 1),
        None => (size, 0),
    };
    let v = ValueId::new;
    let node = |result: u32, inst: Inst| InstrNode::new(inst).with_result(v(result));
    let int = |result: u32, value: u64| {
        node(
            result,
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(i128::from(value)),
            },
        )
    };
    let body = vec![
        int(0, size),
        node(
            1,
            Inst::Alloca {
                ty: Ty::U8,
                count: Some(v(0)),
                align: Some(16),
            },
        ),
        node(
            2,
            Inst::Const {
                ty: Ty::U8,
                value: Constant::Int(i128::from(fill)),
            },
        ),
        int(3, hole),
        InstrNode::new(Inst::MemSet {
            dst: v(1),
            byte: v(2),
            bytes: v(3),
        }),
        int(4, hole + 1),
        node(
            5,
            Inst::GEP {
                pointee_ty: Ty::U8,
                base: v(1),
                indices: vec![v(4)],
                inbounds: false,
            },
        ),
        int(6, after),
        InstrNode::new(Inst::MemSet {
            dst: v(5),
            byte: v(2),
            bytes: v(6),
        }),
        node(
            7,
            Inst::Load {
                ty: ty.clone(),
                ptr: v(1),
                volatile: false,
                align: None,
            },
        ),
        node(
            8,
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            },
        ),
        InstrNode::new(Inst::Return { values: vec![v(8)] }),
    ];
    let mut function = Function::new(FuncId::new(0), "r", FuncTyId::new(0), BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body,
    }];
    install(
        module,
        FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        },
        function,
    )
}

#[test]
fn a_typed_load_needs_no_byte_fsym_says_it_does_not() {
    let s = |id| Ty::Struct(StructId::new(id));
    let tys = [
        s(PAD),
        s(DECLARED),
        s(PACKED),
        s(NESTED),
        s(WITH_ENUM),
        Ty::Tuple(vec![Ty::I32, Ty::I64]),
        Ty::Array(TyId::new(2), 2),
        Ty::Enum(EnumId::new(0)),
        Ty::Enum(EnumId::new(1)),
        Ty::Vector(Box::new(Ty::Bool), 4),
        Ty::U64,
    ];
    let mut failures = Vec::new();
    let mut probes = 0usize;
    for ty in &tys {
        let mut module = base_module("read", Some(x86_64()));
        let layout = FsymLayout::new(&module);
        let size = layout.size(ty).expect("the case lays out");
        let needed = layout.read_coverage(ty).expect("the case has a coverage");
        assert_eq!(needed.size(), size, "{ty:?}");
        // The fill byte is the tag an enum's bytes carry (0 = `A`, 1 = `B`,
        // 2 = `C` for `E`): a load needs the fields of the variant the tag
        // names, so each variant's fields are probed. A fill whose fully
        // filled image does not load (no such variant, an invalid value) is
        // skipped.
        for fill in [0u8, 1, 2] {
            let control = read_probe(&mut module, ty, size, None, fill);
            if !matches!(run(&module, control), Measured::Value(_)) {
                continue;
            }
            for hole in 0..size {
                if needed.contains(hole) {
                    continue;
                }
                let probe = read_probe(&mut module, ty, size, Some(hole), fill);
                probes += 1;
                match run(&module, probe) {
                    Measured::Value(_) => {}
                    other => failures.push(format!(
                        "{ty:?} filled with {fill}: fsym says byte {hole} is not needed, but loading with it uninitialized: {}",
                        describe(&other)
                    )),
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(probes >= 80, "only {probes} probes");
}

/// An array's covered bytes are ONE periodic run of its element's: the
/// coverage of `[Pad; n]` is built from one `Pad` whatever `n` is, and byte
/// `k * stride + b` is covered exactly when byte `b` of a `Pad` is (the two
/// probe tests above measure the element and `[Pad; 2]` against the
/// interpreter). At `n = 2^59` the image is 2^63 bytes: a flag per byte could
/// not even be reserved.
#[test]
fn array_coverage_is_one_periodic_run_whatever_the_length() {
    let module = base_module("coverage", Some(x86_64()));
    let layout = FsymLayout::new(&module);
    let pad = Ty::Struct(StructId::new(PAD));
    let element_written = layout.written_coverage(&pad, None).expect("Pad");
    let element_read = layout.read_coverage(&pad).expect("Pad");
    let stride = layout.size(&pad).expect("Pad");
    assert!(
        (0..stride).any(|byte| !element_written.contains(byte)),
        "Pad has padding, so the periodic pattern is not trivially full"
    );
    for n in [2u64, 3, 1 << 40, 1 << 59] {
        let array = Ty::Array(TyId::new(2), n);
        let written = layout.written_coverage(&array, None).expect("[Pad; n]");
        let read = layout.read_coverage(&array).expect("[Pad; n]");
        assert_eq!(written.size(), n * stride, "n = {n}");
        assert_eq!(read.size(), n * stride, "n = {n}");
        for element in [0, 1, n / 2, n - 1] {
            for byte in 0..stride {
                let at = element * stride + byte;
                assert_eq!(
                    written.contains(at),
                    element_written.contains(byte),
                    "n = {n}: written byte {at}"
                );
                assert_eq!(
                    read.contains(at),
                    element_read.contains(byte),
                    "n = {n}: read byte {at}"
                );
            }
        }
        assert!(!written.contains(n * stride), "n = {n}: past the image");
    }
    // An empty array covers nothing.
    let empty = layout
        .written_coverage(&Ty::Array(TyId::new(2), 0), None)
        .expect("[Pad; 0]");
    assert_eq!(empty.size(), 0);
    assert!(!empty.contains(0));
}

#[test]
fn storage_dimensions_never_grant_initialized_coverage_or_a_bounded_verdict() {
    for target in [None, Some(x86_64()), Some(wasm32())] {
        let mut module = base_module("storage_scope", target);
        let storage = Ty::Storage(trust_ir::StorageLayout::new(80, 8));
        module.structs.push(struct_def(
            20,
            vec![
                field(Ty::U64, Some(0)),
                field(storage.clone(), Some(8)),
                field(Ty::U64, Some(88)),
            ],
            Some(96),
            Some(8),
            StructRepr::Rust,
        ));
        let layout = FsymLayout::new(&module);
        assert_eq!(layout.size(&storage).unwrap(), 80);
        assert_eq!(layout.align(&storage).unwrap(), 8);
        let parent = Ty::Struct(StructId::new(20));
        assert_eq!(layout.size(&parent).unwrap(), 96);
        for ty in [storage.clone(), parent] {
            assert!(layout.read_coverage(&ty).unwrap_err().contains("Storage"));
            assert!(
                layout
                    .written_coverage(&ty, None)
                    .unwrap_err()
                    .contains("Storage")
            );
        }
        let (fty, f) = stride_probe("storage_stride", storage, Ty::U64);
        let id = install(&mut module, fty, f);
        let report = trust_cg_verify::fsym_trust_ir::scan_function_in_module(
            &module,
            &module.functions[id.as_usize()],
        );
        assert_eq!(report.scanned_functions, 0);
        assert!(
            report
                .skipped_functions
                .iter()
                .any(|skip| skip.detail.contains("Storage geometry"))
        );
    }
    let mut invalid = Module::new("invalid_storage_geometry");
    let ty = Ty::Storage(trust_ir::StorageLayout::new(80, 0));
    assert!(FsymLayout::new(&invalid).size(&ty).is_err());
    assert!(FsymLayout::new(&invalid).align(&ty).is_err());
    let (fty, function) = stride_probe("invalid_storage", ty, Ty::U64);
    let id = install(&mut invalid, fty, function);
    let error = Interpreter::with_module(&invalid)
        .execute_func(id, vec![])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::TypeError);
}

#[path = "../../trust-cg-lower/tests/common/single_inhabited.rs"]
mod single_fixture;

#[test]
fn single_inhabited_coverage_uses_selected_payload_and_refuses_impossible_writes() {
    for active in 0..2 {
        let module = single_fixture::module(active, true);
        let ty = Ty::Enum(EnumId::new(0));
        let layout = FsymLayout::new(&module);
        assert_eq!(layout.size(&ty).unwrap(), 8);
        assert_eq!(layout.align(&ty).unwrap(), 8);
        for coverage in [
            layout.read_coverage(&ty).unwrap(),
            layout.written_coverage(&ty, None).unwrap(),
            layout.written_coverage(&ty, Some(active)).unwrap(),
        ] {
            for byte in 0..8 {
                assert!(coverage.contains(byte));
            }
            assert!(!coverage.contains(8));
        }
        assert!(
            layout
                .written_coverage(&ty, Some(1 - active))
                .unwrap_err()
                .contains("inactive variant")
        );
    }
}

#[test]
fn inactive_storage_retains_geometry_but_never_initialized_coverage() {
    let mut module = single_fixture::module(1, true);
    module.enums[0].variants[0]
        .fields
        .push(Ty::Storage(trust_ir::StorageLayout::new(8, 8)));
    let ty = Ty::Enum(EnumId::new(0));
    let layout = FsymLayout::new(&module);
    assert_eq!(layout.size(&ty).unwrap(), 8);
    assert!(layout.read_coverage(&ty).unwrap_err().contains("Storage"));
    assert!(
        layout
            .written_coverage(&ty, None)
            .unwrap_err()
            .contains("Storage")
    );
}

fn stored_closure_layout_case(zero: bool) -> (Module, Ty, Constant) {
    let mut module = Module::new("fsym_stored_closure_bytes");
    module.target_info = Some(x86_64());
    let captures = if zero { vec![] } else { vec![Ty::U8, Ty::U64] };
    let apparent = FuncTyId::new(0);
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    let closure = trust_ir::ClosureTyId::new(0);
    module.closure_types.push(trust_ir::ClosureTy {
        func: apparent,
        captures: captures.clone(),
    });
    module
        .closure_layouts
        .push(trust_ir::ClosureLayoutDescriptor {
            origin: None,
            closure,
            size: if zero { 0 } else { 16 },
            align: if zero { 1 } else { 8 },
            capture_offsets: if zero { vec![] } else { vec![8, 0] },
        });
    let mut target = Function::new(
        FuncId::new(0),
        "stored_target",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    target.blocks = vec![Block {
        id: BlockId::new(0),
        params: captures
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty))
            .collect(),
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    let target = install(
        &mut module,
        FuncTy {
            params: captures,
            returns: vec![],
            abi: None,
            is_vararg: false,
        },
        target,
    );
    let ty = Ty::Closure(closure);
    let value = Constant::Closure {
        func: target,
        captures: if zero {
            vec![]
        } else {
            vec![Constant::Int(7), Constant::Int(0x0102030405060708)]
        },
    };
    let mut constructor = Function::new(
        FuncId::new(0),
        "stored_constructor",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    constructor.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: value.clone(),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    install(
        &mut module,
        FuncTy {
            params: vec![],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        },
        constructor,
    );
    (module, ty, value)
}

#[test]
fn stored_closure_geometry_and_covered_bytes_match_actual_interpreter() {
    for zero in [false, true] {
        let (mut module, ty, value) = stored_closure_layout_case(zero);
        let layout = FsymLayout::new(&module);
        let size = layout.size(&ty).unwrap();
        let align = layout.align(&ty).unwrap();
        assert_eq!((size, align), if zero { (0, 1) } else { (16, 8) });
        let written = layout.written_coverage(&ty, None).unwrap();
        let read = layout.read_coverage(&ty).unwrap();
        assert_eq!(written.size(), size);
        assert_eq!(read.size(), size);
        assert!(!written.contains(size));
        assert!(!read.contains(size));
        let (signature, function) = stride_probe("stored_size", ty.clone(), Ty::U64);
        let probe = install(&mut module, signature, function);
        assert!(matches!(run(&module, probe), Measured::Value(observed) if observed == size));
        module.structs.push(struct_def(
            0,
            vec![field(Ty::U8, None), field(ty.clone(), None)],
            None,
            None,
            StructRepr::Rust,
        ));
        let (signature, function) =
            stride_probe("stored_alignment", Ty::Struct(StructId::new(0)), Ty::U64);
        let probe = install(&mut module, signature, function);
        assert!(
            matches!(run(&module, probe), Measured::Value(observed) if observed - size == align)
        );
        let control = read_probe(&mut module, &ty, size.max(1), None, 1);
        assert!(matches!(run(&module, control), Measured::Value(_)));
        let builder = constant(ty.clone(), value);
        for byte in 0..size {
            let probe = written_probe(&mut module, &ty, size, byte, &builder);
            match run(&module, probe) {
                Measured::Value(_) => {
                    assert!(written.contains(byte), "unclaimed written byte {byte}")
                }
                Measured::Other(error) if error.contains("uninitialized") => assert!(
                    !written.contains(byte),
                    "padding byte {byte} was claimed initialized"
                ),
                observed => panic!("closure write byte {byte}: {}", describe(&observed)),
            }
            let probe = read_probe(&mut module, &ty, size, Some(byte), 1);
            match run(&module, probe) {
                Measured::Value(_) => {
                    assert!(!read.contains(byte), "required byte {byte} was not read")
                }
                Measured::Other(error) if error.contains("uninitialized") => {
                    assert!(read.contains(byte), "unmodeled required byte {byte}")
                }
                observed => panic!("closure read byte {byte}: {}", describe(&observed)),
            }
        }
    }
}

#[test]
fn stored_closure_layout_refuses_missing_conflicting_and_malformed_bindings() {
    let (module, ty, _) = stored_closure_layout_case(false);
    let healthy = FsymLayout::new(&module);
    assert_eq!(healthy.size(&ty).unwrap(), 16);
    assert_eq!(healthy.align(&ty).unwrap(), 8);
    assert!(healthy.written_coverage(&ty, None).is_ok());
    assert!(healthy.read_coverage(&ty).is_ok());
    let mut control = module.clone();
    let (signature, function) = stride_probe("healthy_stored_layout", ty.clone(), Ty::U64);
    let probe = install(&mut control, signature, function);
    assert!(matches!(run(&control, probe), Measured::Value(16)));
    for mutation in 0..5 {
        let mut changed = module.clone();
        match mutation {
            0 => {
                changed.functions.pop();
            }
            1 => {
                let mut target = changed.functions[0].clone();
                target.id = FuncId::new(2);
                target.name = "other_stored_target".into();
                changed.functions.push(target);
                let mut constructor = changed.functions[1].clone();
                constructor.id = FuncId::new(3);
                constructor.name = "conflicting_stored_constructor".into();
                let Inst::Const {
                    value: Constant::Closure { func, .. },
                    ..
                } = &mut constructor.blocks[0].body[0].inst
                else {
                    panic!("fixture constructor")
                };
                *func = FuncId::new(2);
                changed.functions.push(constructor);
            }
            2 => changed.closure_layouts[0].capture_offsets[1] = 9,
            3 => changed.func_types[1].params.clear(),
            _ => {
                changed.closure_types[0].captures = vec![ty.clone()];
                changed.closure_layouts[0].capture_offsets = vec![0];
                changed.func_types[1].params = vec![ty.clone()];
            }
        }
        let layout = FsymLayout::new(&changed);
        assert!(layout.size(&ty).is_err(), "binding mutation {mutation}");
        assert!(layout.align(&ty).is_err(), "binding mutation {mutation}");
        assert!(
            layout.written_coverage(&ty, None).is_err(),
            "binding mutation {mutation}"
        );
        assert!(
            layout.read_coverage(&ty).is_err(),
            "binding mutation {mutation}"
        );
        let (signature, function) = stride_probe("bad_stored_layout", ty.clone(), Ty::U64);
        let probe = install(&mut changed, signature, function);
        assert!(
            matches!(run(&changed, probe), Measured::NoLayout(_)),
            "interpreter must also refuse mutation {mutation}"
        );
    }
}
