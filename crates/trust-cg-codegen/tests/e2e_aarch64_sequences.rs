// trust-cg-codegen/tests/e2e_aarch64_sequences.rs
//
// Ledger L05-P8: trust-ir sequences and boxed sets on aarch64-apple-darwin.
//
// trust-ir states the FORM of a `Ty::Sequence` ("a packed buffer
// (length-prefixed)") but no layout, and its codegen gate names an element op
// over a sequence `UnlowerableForCodegen`. trust-cg's image and ABI are
// defined once in `trust_cg_lower::sequence_layout`: a collection value is the
// pointer to an immutable `u64 len` + packed-elements image, a
// collection-returning function takes a trailing caller-provided result
// buffer (sized from the length the callee publishes) and returns it in x0,
// and the `SeqMap` family lowers as a counted loop into a fresh image.
//
// Every positive case executes natively at O0-O3 against TWO independent
// oracles: trust-ir's reference interpreter, which evaluates the same module
// (its results are embedded into the C driver), and a C model in the driver.
// The driver passes images built by C and reads the images the backend writes
// through the documented layout, so the native checks exercise the ABI end to
// end. Loop-carried images keep the previous iteration's image live while the
// next is produced, a `SeqMap` gives every element a fresh cell (checked
// against a C model of trust-ir's per-element cells), and every run-time
// length witness is driven to its trap in a forked child. The negative cases
// pin the named refusals for every shape that stays outside the image:
// element ops (the format's own refusal), memory and arithmetic positions,
// bitsets, set elements that store one image, unadmitted element types,
// unpublished result lengths, replaceable callees and indirect or unwinding
// results.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::constant::Constant;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{
    Block, BlockId, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode, Module, SetRepr,
    StructDef, StructId, StructRepr, Ty, ValueId,
};

#[path = "common/aarch64_native.rs"]
mod aarch64_native;

#[path = "common/admission_expect.rs"]
mod admission_expect;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// ---------------------------------------------------------------------------
// trust-ir construction helpers
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn op(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}

fn eff(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn ret(values: &[u32]) -> InstrNode {
    eff(Inst::Return {
        values: values.iter().map(|n| v(*n)).collect(),
    })
}

fn block(id: u32, params: &[(u32, Ty)], body: Vec<InstrNode>) -> Block {
    let mut block = Block::new(b(id));
    for (param, ty) in params {
        block = block.with_param(v(*param), ty.clone());
    }
    block.body = body;
    block
}

/// Define `name(params) -> returns` with `blocks` (entry = block 0).
fn define(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    blocks: Vec<Block>,
) -> FuncId {
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, b(0));
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

/// Declare an external `name(params) -> returns`.
fn declare(module: &mut Module, name: &str, params: Vec<Ty>, returns: Vec<Ty>) -> FuncId {
    define(module, name, params, returns, Vec::new())
}

fn seq_of(module: &mut Module, elem: Ty) -> Ty {
    Ty::Sequence(
        module
            .add_type(elem)
            .expect("Module::add_type: test fixture"),
    )
}

fn int(value: i128) -> Constant {
    Constant::Int(value)
}

// ---------------------------------------------------------------------------
// Elements, the interpreter oracle and the C side
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq)]
enum Elem {
    Int(i128),
    F32(f32),
    F64(f64),
    Bool(bool),
}

impl Elem {
    fn constant(self) -> Constant {
        match self {
            Elem::Int(value) => Constant::Int(value),
            Elem::F32(value) => Constant::Float(f64::from(value)),
            Elem::F64(value) => Constant::Float(value),
            Elem::Bool(value) => Constant::Bool(value),
        }
    }

    fn interpret_value(self, ty: &Ty) -> InterpretValue {
        match self {
            Elem::Int(value) => InterpretValue::int(ty.clone(), value).expect("integer element"),
            Elem::F32(value) => InterpretValue {
                ty: Ty::F32,
                kind: InterpretValueKind::FloatBits(u64::from(value.to_bits())),
            },
            Elem::F64(value) => InterpretValue {
                ty: Ty::F64,
                kind: InterpretValueKind::FloatBits(value.to_bits()),
            },
            Elem::Bool(value) => InterpretValue::bool(value),
        }
    }

    fn from_interpret(value: &InterpretValue) -> Elem {
        match (&value.ty, &value.kind) {
            (Ty::F32, InterpretValueKind::FloatBits(bits)) => {
                Elem::F32(f32::from_bits(u32::try_from(*bits).expect("f32 bits")))
            }
            (Ty::F64, InterpretValueKind::FloatBits(bits)) => Elem::F64(f64::from_bits(*bits)),
            (Ty::Bool, _) => Elem::Bool(value.as_bool().expect("bool element")),
            (ty, _) => {
                let int = value.as_int().expect("integer element");
                let signed = matches!(ty, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64);
                Elem::Int(if signed {
                    int.as_signed()
                } else {
                    int.as_unsigned() as i128
                })
            }
        }
    }

    /// A C literal of this element's image slot: the value for integers and
    /// `Bool`, the IEEE bit pattern for floats (`c_type` spells float slots
    /// as unsigned integers so every array is a compile-time constant).
    fn c_literal(self) -> String {
        match self {
            Elem::Int(value) if value == i128::from(i64::MIN) => {
                "(-9223372036854775807LL - 1)".to_string()
            }
            Elem::Int(value) if value < 0 => format!("({value}LL)"),
            Elem::Int(value) => format!("{value}ULL"),
            Elem::F32(value) => format!("0x{:08x}u", value.to_bits()),
            Elem::F64(value) => format!("0x{:016x}ULL", value.to_bits()),
            Elem::Bool(value) => u8::from(value).to_string(),
        }
    }
}

/// The C type of one image slot of `ty` elements (floats as their bits).
fn c_type(ty: &Ty) -> &'static str {
    match ty {
        Ty::Bool | Ty::U8 => "uint8_t",
        Ty::I8 => "int8_t",
        Ty::I16 => "int16_t",
        Ty::U16 => "uint16_t",
        Ty::I32 => "int32_t",
        Ty::U32 | Ty::F32 => "uint32_t",
        Ty::I64 => "int64_t",
        Ty::U64 | Ty::F64 => "uint64_t",
        other => panic!("no C element type for {other:?}"),
    }
}

fn collection_value(ty: &Ty, elem_ty: &Ty, elems: &[Elem]) -> InterpretValue {
    let values = elems
        .iter()
        .map(|elem| elem.interpret_value(elem_ty))
        .collect();
    InterpretValue {
        ty: ty.clone(),
        kind: match ty {
            Ty::Set(_, _) => InterpretValueKind::Set(values),
            _ => InterpretValueKind::Sequence(values),
        },
    }
}

/// Run `name(args)` in trust-ir's reference interpreter; its one result must
/// be a sequence or set, returned element by element.
fn interpret_collection(module: &Module, name: &str, args: Vec<InterpretValue>) -> Vec<Elem> {
    let function = module
        .function_by_name(name)
        .unwrap_or_else(|| panic!("fixture defines @{name}"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, args)
        .unwrap_or_else(|error| panic!("interpreter oracle for @{name}: {error:?}"));
    let [result] = outcome.returns.as_slice() else {
        panic!("@{name}: expected one result, got {:?}", outcome.returns)
    };
    match &result.kind {
        InterpretValueKind::Sequence(values) | InterpretValueKind::Set(values) => {
            values.iter().map(Elem::from_interpret).collect()
        }
        other => panic!("@{name}: expected a collection result, got {other:?}"),
    }
}

/// The C array initializer for `elems` (a zero-length array is spelled as
/// one unused element so the declaration stays valid C).
fn c_array(elems: &[Elem]) -> String {
    if elems.is_empty() {
        return "{0}".to_string();
    }
    let items: Vec<String> = elems.iter().map(|elem| elem.c_literal()).collect();
    format!("{{{}}}", items.join(", "))
}

/// The C prelude every driver shares: image construction, bit-exact float
/// literals and an image comparison that names the first difference.
const PRELUDE: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static float bits_f32(uint32_t bits) { float f; memcpy(&f, &bits, 4); return f; }
static double bits_f64(uint64_t bits) { double d; memcpy(&d, &bits, 8); return d; }

/* trust_cg_lower::sequence_layout: u64 count at offset 0, elements packed from
   offset 8 (every admitted element is at most 8-byte aligned). */
static void *image_new(uint64_t len, size_t stride, const void *elems) {
    unsigned char *image = malloc(8 + (len ? len : 1) * stride);
    memcpy(image, &len, 8);
    if (len) memcpy(image + 8, elems, len * stride);
    return image;
}

/* A result buffer of `cap` elements, poisoned so an unwritten byte shows. */
static void *buffer_new(uint64_t cap, size_t stride) {
    unsigned char *buffer = malloc(8 + (cap ? cap : 1) * stride);
    memset(buffer, 0xA5, 8 + (cap ? cap : 1) * stride);
    return buffer;
}

static uint64_t image_len(const void *image) { uint64_t len; memcpy(&len, image, 8); return len; }

static int image_equals(const char *what, const void *image, uint64_t len, size_t stride,
                        const void *want) {
    if (image_len(image) != len) {
        printf("%s: length %llu, expected %llu\n", what,
               (unsigned long long)image_len(image), (unsigned long long)len);
        return 0;
    }
    for (uint64_t i = 0; i < len * stride; i++) {
        unsigned char got = ((const unsigned char *)image)[8 + i];
        unsigned char exp = ((const unsigned char *)want)[i];
        if (got != exp) {
            printf("%s: byte %llu of the elements is 0x%02x, expected 0x%02x\n", what,
                   (unsigned long long)i, got, exp);
            return 0;
        }
    }
    return 1;
}
"#;

fn run_native_at_every_level(tag: &str, module: &Module, driver: &str) {
    for opt in OPTS {
        let object = aarch64_native::compile(module, opt);
        let Some(code) = aarch64_native::link_run(&format!("{tag}_{opt:?}"), &object, driver)
        else {
            return;
        };
        assert_eq!(code, 0, "{tag}: native driver failed at {opt:?}");
    }
}

/// `module` is refused at every level: by trust-ir's own first admission
/// finding when trust-ir refuses it (WS7.3: ingestion admission runs before
/// any backend arm), else by the backend's refusal naming every `needle`.
/// trust-ir judges the module as [`aarch64_native::try_compile`] compiles it:
/// pinned, under its license policy.
fn expect_refusal(tag: &str, module: &Module, needles: &[&str]) {
    let pinned = aarch64_native::pinned(module);
    let license = aarch64_native::permit_unlicensed();
    for opt in OPTS {
        let error = aarch64_native::try_compile(module, opt)
            .err()
            .unwrap_or_else(|| panic!("{tag}: must be refused at {opt:?}"));
        if let Some(named) = admission_expect::names_first_finding(&pinned, &error, &license) {
            assert!(
                named,
                "{tag} at {opt:?}: refusal must name trust-ir's admission finding {:?}, got: \
                 {error}",
                admission_expect::first_finding(&pinned, &license)
            );
            continue;
        }
        for needle in needles {
            assert!(
                error.contains(needle),
                "{tag} at {opt:?}: refusal must name `{needle}`, got: {error}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Constants of every admitted element type, returned through the ABI
// ---------------------------------------------------------------------------

struct ConstCase {
    name: &'static str,
    elem: Ty,
    elems: Vec<Elem>,
}

fn const_cases() -> Vec<ConstCase> {
    vec![
        ConstCase {
            name: "k_i8",
            elem: Ty::I8,
            elems: [-128, -1, 0, 1, 127].map(Elem::Int).to_vec(),
        },
        ConstCase {
            name: "k_u8",
            elem: Ty::U8,
            elems: [0, 7, 255].map(Elem::Int).to_vec(),
        },
        ConstCase {
            name: "k_i16",
            elem: Ty::I16,
            elems: [-32768, 12345, 32767].map(Elem::Int).to_vec(),
        },
        ConstCase {
            name: "k_u16",
            elem: Ty::U16,
            elems: [65535, 1, 0, 40000].map(Elem::Int).to_vec(),
        },
        ConstCase {
            name: "k_i32",
            elem: Ty::I32,
            elems: [i32::MIN as i128, -7, 3, i32::MAX as i128]
                .map(Elem::Int)
                .to_vec(),
        },
        ConstCase {
            name: "k_u32",
            elem: Ty::U32,
            elems: [u32::MAX as i128, 0x8000_0000].map(Elem::Int).to_vec(),
        },
        ConstCase {
            name: "k_i64",
            elem: Ty::I64,
            elems: [i64::MIN as i128, -1, i64::MAX as i128]
                .map(Elem::Int)
                .to_vec(),
        },
        ConstCase {
            name: "k_u64",
            elem: Ty::U64,
            elems: [u64::MAX as i128, 1 << 63, 42].map(Elem::Int).to_vec(),
        },
        ConstCase {
            name: "k_f32",
            elem: Ty::F32,
            elems: [1.5f32, -0.0, f32::MAX, f32::MIN_POSITIVE]
                .map(Elem::F32)
                .to_vec(),
        },
        ConstCase {
            name: "k_f64",
            elem: Ty::F64,
            elems: [std::f64::consts::PI, -2.25, f64::MIN_POSITIVE / 4.0]
                .map(Elem::F64)
                .to_vec(),
        },
        ConstCase {
            name: "k_bool",
            elem: Ty::Bool,
            elems: [true, false, false, true, true].map(Elem::Bool).to_vec(),
        },
        ConstCase {
            name: "k_empty_i64",
            elem: Ty::I64,
            elems: Vec::new(),
        },
        ConstCase {
            name: "k_long_u16",
            elem: Ty::U16,
            elems: (0..37).map(|i| Elem::Int(i * 1771 % 65536)).collect(),
        },
    ]
}

fn build_constants(cases: &[ConstCase]) -> Module {
    let mut module = Module::new("sequence_constants");
    for case in cases {
        let seq = seq_of(&mut module, case.elem.clone());
        define(
            &mut module,
            case.name,
            vec![],
            vec![seq.clone()],
            vec![block(
                0,
                &[],
                vec![
                    op(
                        Inst::Const {
                            ty: seq,
                            value: Constant::Sequence(
                                case.elems.iter().map(|e| e.constant()).collect(),
                            ),
                        },
                        0,
                    ),
                    ret(&[0]),
                ],
            )],
        );
    }
    module
}

#[test]
fn sequence_constants_of_every_element_type_return_through_the_abi_o0_through_o3() {
    let cases = const_cases();
    let module = build_constants(&cases);
    let mut driver = PRELUDE.to_string();
    let mut body = String::new();
    for (index, case) in cases.iter().enumerate() {
        let interp = interpret_collection(&module, case.name, vec![]);
        assert_eq!(
            interp, case.elems,
            "interpreter oracle for @{}: the constant's elements, in order",
            case.name
        );
        let c = c_type(&case.elem);
        driver.push_str(&format!(
            "extern void *{name}(void *out);\n\
             static const {c} {name}_model[] = {model};\n\
             static const {c} {name}_interp[] = {interp};\n",
            name = case.name,
            model = c_array(&case.elems),
            interp = c_array(&interp),
        ));
        body.push_str(&format!(
            "    {{\n\
                 void *out = buffer_new({len}, sizeof({c}));\n\
                 void *got = {name}(out);\n\
                 if (got != out) {{ printf(\"{name}: result is not the caller's buffer\\n\"); return {code}; }}\n\
                 if (!image_equals(\"{name} vs C model\", got, {len}, sizeof({c}), {name}_model)) return {code};\n\
                 if (!image_equals(\"{name} vs interpreter\", got, {len}, sizeof({c}), {name}_interp)) return {code};\n\
                 free(out);\n\
             }}\n",
            name = case.name,
            len = case.elems.len(),
            code = index + 1,
        ));
    }
    driver.push_str("int main(void) {\n");
    driver.push_str(&body);
    driver.push_str("    return 0;\n}\n");
    run_native_at_every_level("seq_constants", &module, &driver);
}

// ---------------------------------------------------------------------------
// The SeqMap family, at every integer width, over Bool and through `fwd`
// ---------------------------------------------------------------------------

struct MapCase {
    name: &'static str,
    elem: Ty,
    kind: MapKind,
    inputs: Vec<Elem>,
}

#[derive(Clone, Copy)]
enum MapKind {
    AddK(u64),
    Not,
    /// `fwd(x) = x * mul + add` (integers wrap; floats round per IEEE).
    Fwd {
        mul: i128,
        add: i128,
    },
    FwdF64 {
        mul: f64,
        add: f64,
    },
    FwdNot,
}

fn map_cases() -> Vec<MapCase> {
    let i = |values: &[i128]| values.iter().copied().map(Elem::Int).collect::<Vec<_>>();
    vec![
        MapCase {
            name: "add_k_i8",
            elem: Ty::I8,
            kind: MapKind::AddK(200),
            inputs: i(&[-128, -57, 0, 55, 127]),
        },
        MapCase {
            name: "add_k_u8",
            elem: Ty::U8,
            kind: MapKind::AddK(300),
            inputs: i(&[0, 211, 212, 255]),
        },
        MapCase {
            name: "add_k_i16",
            elem: Ty::I16,
            kind: MapKind::AddK(1),
            inputs: i(&[32767, -32768, -1]),
        },
        MapCase {
            name: "add_k_u16",
            elem: Ty::U16,
            kind: MapKind::AddK(65535),
            inputs: i(&[0, 1, 65535]),
        },
        MapCase {
            name: "add_k_i32",
            elem: Ty::I32,
            kind: MapKind::AddK(5),
            inputs: i(&[i32::MAX as i128, -5, 0, i32::MIN as i128, 123_456]),
        },
        MapCase {
            name: "add_k_u32",
            elem: Ty::U32,
            kind: MapKind::AddK(0x1_0000_0003),
            inputs: i(&[u32::MAX as i128, 0, 7]),
        },
        MapCase {
            name: "add_k_i64",
            elem: Ty::I64,
            kind: MapKind::AddK(u64::MAX),
            inputs: i(&[i64::MIN as i128, 0, 1, i64::MAX as i128]),
        },
        MapCase {
            name: "add_k_u64",
            elem: Ty::U64,
            kind: MapKind::AddK(1 << 63),
            inputs: i(&[0, u64::MAX as i128, 12]),
        },
        MapCase {
            name: "add_k_empty",
            elem: Ty::I32,
            kind: MapKind::AddK(9),
            inputs: Vec::new(),
        },
        MapCase {
            name: "not_bool",
            elem: Ty::Bool,
            kind: MapKind::Not,
            inputs: [true, false, true, true, false, false, true]
                .map(Elem::Bool)
                .to_vec(),
        },
        MapCase {
            name: "map_i32",
            elem: Ty::I32,
            kind: MapKind::Fwd { mul: 3, add: 1 },
            inputs: i(&[0, -1, 5, 715_827_882, i32::MIN as i128]),
        },
        MapCase {
            name: "map_u8",
            elem: Ty::U8,
            kind: MapKind::Fwd { mul: 7, add: 200 },
            inputs: i(&[0, 1, 100, 255]),
        },
        MapCase {
            name: "map_f64",
            elem: Ty::F64,
            kind: MapKind::FwdF64 {
                mul: 2.5,
                add: -1.0,
            },
            inputs: [0.0, 1.0, -3.25, 1e300].map(Elem::F64).to_vec(),
        },
        MapCase {
            name: "map_bool",
            elem: Ty::Bool,
            kind: MapKind::FwdNot,
            inputs: [false, true, true].map(Elem::Bool).to_vec(),
        },
    ]
}

/// The element function `name(p: &mut elem) { *p = op(*p) }`.
fn define_element_function(module: &mut Module, name: &str, elem: &Ty, kind: MapKind) -> FuncId {
    let ptr = Ty::RefMut(Box::new(elem.clone()));
    let load = op(
        Inst::Load {
            ty: elem.clone(),
            ptr: v(0),
            volatile: false,
            align: None,
        },
        1,
    );
    let mut body = vec![load];
    let result = match kind {
        MapKind::Fwd { mul, add } => {
            body.push(op(
                Inst::Const {
                    ty: elem.clone(),
                    value: int(mul),
                },
                2,
            ));
            body.push(op(
                Inst::BinOp {
                    op: trust_ir::BinOp::Mul,
                    ty: elem.clone(),
                    lhs: v(1),
                    rhs: v(2),
                },
                3,
            ));
            body.push(op(
                Inst::Const {
                    ty: elem.clone(),
                    value: int(add),
                },
                4,
            ));
            body.push(op(
                Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: elem.clone(),
                    lhs: v(3),
                    rhs: v(4),
                },
                5,
            ));
            5
        }
        MapKind::FwdF64 { mul, add } => {
            body.push(op(
                Inst::Const {
                    ty: Ty::F64,
                    value: Constant::Float(mul),
                },
                2,
            ));
            body.push(op(
                Inst::BinOp {
                    op: trust_ir::BinOp::FMul,
                    ty: Ty::F64,
                    lhs: v(1),
                    rhs: v(2),
                },
                3,
            ));
            body.push(op(
                Inst::Const {
                    ty: Ty::F64,
                    value: Constant::Float(add),
                },
                4,
            ));
            body.push(op(
                Inst::BinOp {
                    op: trust_ir::BinOp::FAdd,
                    ty: Ty::F64,
                    lhs: v(3),
                    rhs: v(4),
                },
                5,
            ));
            5
        }
        MapKind::FwdNot => {
            body.push(op(
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                },
                2,
            ));
            body.push(op(
                Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(true),
                },
                3,
            ));
            body.push(op(
                Inst::Select {
                    ty: Ty::Bool,
                    cond: v(1),
                    then_val: v(2),
                    else_val: v(3),
                },
                4,
            ));
            4
        }
        MapKind::AddK(_) | MapKind::Not => unreachable!("not an element-function case"),
    };
    body.push(eff(Inst::Store {
        ty: elem.clone(),
        ptr: v(0),
        value: v(result),
        volatile: false,
        align: None,
    }));
    body.push(ret(&[]));
    define(
        module,
        name,
        vec![ptr.clone()],
        vec![],
        vec![block(0, &[(0, ptr)], body)],
    )
}

fn build_maps(cases: &[MapCase]) -> Module {
    let mut module = Module::new("sequence_maps");
    for case in cases {
        let seq = seq_of(&mut module, case.elem.clone());
        let inst = match case.kind {
            MapKind::AddK(k) => Inst::SeqMapAddK {
                ty: seq.clone(),
                seq: v(0),
                k,
            },
            MapKind::Not => Inst::SeqMapNot {
                ty: seq.clone(),
                seq: v(0),
            },
            kind => {
                let fwd = define_element_function(
                    &mut module,
                    &format!("{}_elem", case.name),
                    &case.elem,
                    kind,
                );
                Inst::SeqMap {
                    ty: seq.clone(),
                    seq: v(0),
                    fwd,
                }
            }
        };
        define(
            &mut module,
            case.name,
            vec![seq.clone()],
            vec![seq.clone()],
            vec![block(0, &[(0, seq)], vec![op(inst, 1), ret(&[1])])],
        );
    }
    module
}

/// The C model of one case: a C function body over the slot `x`.
fn c_model(case: &MapCase) -> String {
    let c = c_type(&case.elem);
    let expression = match case.kind {
        MapKind::AddK(k) => {
            // Unsigned arithmetic at the element width is the wrapping add.
            let width = match &case.elem {
                Ty::I8 | Ty::U8 => "uint8_t",
                Ty::I16 | Ty::U16 => "uint16_t",
                Ty::I32 | Ty::U32 => "uint32_t",
                _ => "uint64_t",
            };
            format!("({c})({width})(({width})x + ({width}){k}ULL)")
        }
        MapKind::Not | MapKind::FwdNot => "(uint8_t)!x".to_string(),
        MapKind::Fwd { mul, add } => {
            let width = match &case.elem {
                Ty::I8 | Ty::U8 => "uint8_t",
                Ty::I16 | Ty::U16 => "uint16_t",
                Ty::I32 | Ty::U32 => "uint32_t",
                _ => "uint64_t",
            };
            format!("({c})({width})(({width})x * ({width})({mul}LL) + ({width})({add}LL))")
        }
        MapKind::FwdF64 { mul, add } => {
            return format!(
                "double d = bits_f64(x) * bits_f64(0x{:016x}ULL) + bits_f64(0x{:016x}ULL); \
                 uint64_t r; memcpy(&r, &d, 8); return r;",
                mul.to_bits(),
                add.to_bits()
            );
        }
    };
    format!("return {expression};")
}

#[test]
fn seq_map_family_matches_the_interpreter_and_a_c_model_o0_through_o3() {
    let cases = map_cases();
    let module = build_maps(&cases);
    let mut driver = PRELUDE.to_string();
    let mut body = String::new();
    for (index, case) in cases.iter().enumerate() {
        let seq = match module
            .function_by_name(case.name)
            .map(|f| module.func_types[f.ty.as_usize()].params[0].clone())
        {
            Some(ty) => ty,
            None => panic!("fixture defines @{}", case.name),
        };
        let interp = interpret_collection(
            &module,
            case.name,
            vec![collection_value(&seq, &case.elem, &case.inputs)],
        );
        assert_eq!(
            interp.len(),
            case.inputs.len(),
            "@{}: a map keeps the length",
            case.name
        );
        let c = c_type(&case.elem);
        let n = case.inputs.len();
        driver.push_str(&format!(
            "extern void *{name}(const void *s, void *out);\n\
             static const {c} {name}_in[] = {inputs};\n\
             static const {c} {name}_interp[] = {interp};\n\
             static {c} {name}_model_of({c} x) {{ {model} }}\n",
            name = case.name,
            inputs = c_array(&case.inputs),
            interp = c_array(&interp),
            model = c_model(case),
        ));
        body.push_str(&format!(
            "    {{\n\
                 void *s = image_new({n}, sizeof({c}), {name}_in);\n\
                 void *out = buffer_new({n}, sizeof({c}));\n\
                 {c} model[{n_or_1}];\n\
                 for (int i = 0; i < {n}; i++) model[i] = {name}_model_of({name}_in[i]);\n\
                 void *got = {name}(s, out);\n\
                 if (got != out) {{ printf(\"{name}: result is not the caller's buffer\\n\"); return {code}; }}\n\
                 if (!image_equals(\"{name} vs C model\", got, {n}, sizeof({c}), model)) return {code};\n\
                 if (!image_equals(\"{name} vs interpreter\", got, {n}, sizeof({c}), {name}_interp)) return {code};\n\
                 if (!image_equals(\"{name} input untouched\", s, {n}, sizeof({c}), {name}_in)) return {code};\n\
                 free(s); free(out);\n\
             }}\n",
            name = case.name,
            n_or_1 = n.max(1),
            code = index + 1,
        ));
    }
    driver.push_str("int main(void) {\n");
    driver.push_str(&body);
    driver.push_str("    return 0;\n}\n");
    run_native_at_every_level("seq_maps", &module, &driver);
}

// ---------------------------------------------------------------------------
// Parameters, results, calls, selects, loops and C callees
// ---------------------------------------------------------------------------

/// * `inc(s: seq<i32>) -> seq<i32> = seq_map_add_k(s, 1)`
/// * `twice(s) = inc(inc(s))` (call results sized by the callee's
///   published parameter length, fixed and runtime buffers)
/// * `pick(c: bool, s) = select(c, seq_map_add_k(s, 10), s)`
/// * `iterate(s, n: u32)`: `n` times `s = inc(s)` around a loop, so every
///   call's result buffer is a runtime allocation in a cyclic block
/// * `wide(x0..x7: i64, s: seq<i32>)`: `s` travels in the ninth argument slot
///   and the result buffer on the stack
/// * `three() -> seq<i32> = inc([1, 2, 3])` (a static published length)
/// * `sum_mapped(s) = c_sum(seq_map_add_k(s, 2))`: a sequence argument to a C
///   callee (C model only: the interpreter executes no external call)
/// * `consts_in_loop(n)`: a constant image re-materialized every iteration
///   and passed to `inc`
fn build_flows() -> Module {
    let mut module = Module::new("sequence_flows");
    let seq = seq_of(&mut module, Ty::I32);
    let inc = define(
        &mut module,
        "inc",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(0),
                        k: 1,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    define(
        &mut module,
        "twice",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::Call {
                        callee: inc,
                        args: vec![v(0)],
                    },
                    1,
                ),
                op(
                    Inst::Call {
                        callee: inc,
                        args: vec![v(1)],
                    },
                    2,
                ),
                ret(&[2]),
            ],
        )],
    );
    define(
        &mut module,
        "pick",
        vec![Ty::Bool, seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, Ty::Bool), (1, seq.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(1),
                        k: 10,
                    },
                    2,
                ),
                op(
                    Inst::Select {
                        ty: seq.clone(),
                        cond: v(0),
                        then_val: v(2),
                        else_val: v(1),
                    },
                    3,
                ),
                ret(&[3]),
            ],
        )],
    );
    // iterate(s, n): i = 0; while i != n { s = inc(s); i += 1 } return s
    define(
        &mut module,
        "iterate",
        vec![seq.clone(), Ty::U32],
        vec![seq.clone()],
        vec![
            block(
                0,
                &[(0, seq.clone()), (1, Ty::U32)],
                vec![
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(0),
                        },
                        2,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(0), v(2)],
                    }),
                ],
            ),
            block(
                1,
                &[(3, seq.clone()), (4, Ty::U32)],
                vec![
                    op(
                        Inst::ICmp {
                            op: trust_ir::ICmpOp::Eq,
                            ty: Ty::U32,
                            lhs: v(4),
                            rhs: v(1),
                        },
                        5,
                    ),
                    eff(Inst::CondBr {
                        cond: v(5),
                        then_target: b(3),
                        then_args: vec![v(3)],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            ),
            block(
                2,
                &[],
                vec![
                    op(
                        Inst::Call {
                            callee: inc,
                            args: vec![v(3)],
                        },
                        6,
                    ),
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(1),
                        },
                        7,
                    ),
                    op(
                        Inst::BinOp {
                            op: trust_ir::BinOp::Add,
                            ty: Ty::U32,
                            lhs: v(4),
                            rhs: v(7),
                        },
                        8,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(6), v(8)],
                    }),
                ],
            ),
            block(3, &[(9, seq.clone())], vec![ret(&[9])]),
        ],
    );
    let mut wide_params: Vec<Ty> = vec![Ty::I64; 8];
    wide_params.push(seq.clone());
    let mut wide_block_params: Vec<(u32, Ty)> = (0..8).map(|i| (i, Ty::I64)).collect();
    wide_block_params.push((8, seq.clone()));
    define(
        &mut module,
        "wide",
        wide_params,
        vec![seq.clone()],
        vec![block(
            0,
            &wide_block_params,
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(8),
                        k: 100,
                    },
                    9,
                ),
                ret(&[9]),
            ],
        )],
    );
    define(
        &mut module,
        "three",
        vec![],
        vec![seq.clone()],
        vec![block(
            0,
            &[],
            vec![
                op(
                    Inst::Const {
                        ty: seq.clone(),
                        value: Constant::Sequence(vec![int(1), int(2), int(3)]),
                    },
                    0,
                ),
                op(
                    Inst::Call {
                        callee: inc,
                        args: vec![v(0)],
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    // mapped_const() = seq_map_add_k([1, 2, 3], 5): a static length in a
    // straight-line block, so the map writes a fixed frame slot.
    define(
        &mut module,
        "mapped_const",
        vec![],
        vec![seq.clone()],
        vec![block(
            0,
            &[],
            vec![
                op(
                    Inst::Const {
                        ty: seq.clone(),
                        value: Constant::Sequence(vec![int(1), int(2), int(3)]),
                    },
                    0,
                ),
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(0),
                        k: 5,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    // twice_inline(s) = add_k(add_k(s, 1), 2): two loop expansions in one
    // trust-ir block, the second in the first one's continuation.
    define(
        &mut module,
        "twice_inline",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(0),
                        k: 1,
                    },
                    1,
                ),
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(1),
                        k: 2,
                    },
                    2,
                ),
                ret(&[2]),
            ],
        )],
    );
    // iterate_inline(s, n): n times s = seq_map_add_k(s, 3) inside the loop
    // body itself, so the expansion's loop nests in the source loop and each
    // iteration's result is a fresh runtime allocation.
    define(
        &mut module,
        "iterate_inline",
        vec![seq.clone(), Ty::U32],
        vec![seq.clone()],
        vec![
            block(
                0,
                &[(0, seq.clone()), (1, Ty::U32)],
                vec![
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(0),
                        },
                        2,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(0), v(2)],
                    }),
                ],
            ),
            block(
                1,
                &[(3, seq.clone()), (4, Ty::U32)],
                vec![
                    op(
                        Inst::ICmp {
                            op: trust_ir::ICmpOp::Eq,
                            ty: Ty::U32,
                            lhs: v(4),
                            rhs: v(1),
                        },
                        5,
                    ),
                    eff(Inst::CondBr {
                        cond: v(5),
                        then_target: b(3),
                        then_args: vec![v(3)],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            ),
            block(
                2,
                &[],
                vec![
                    op(
                        Inst::SeqMapAddK {
                            ty: seq.clone(),
                            seq: v(3),
                            k: 3,
                        },
                        6,
                    ),
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(1),
                        },
                        7,
                    ),
                    op(
                        Inst::BinOp {
                            op: trust_ir::BinOp::Add,
                            ty: Ty::U32,
                            lhs: v(4),
                            rhs: v(7),
                        },
                        8,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(6), v(8)],
                    }),
                ],
            ),
            block(3, &[(9, seq.clone())], vec![ret(&[9])]),
        ],
    );
    // countdown(s, n) = if n == 0 { s } else { countdown(inc(s), n - 1) }:
    // the published length of a recursive function (its own Param(0) through
    // the recursive call), and call results passed on as arguments.
    let countdown = FuncId::new(module.functions.len() as u32);
    define(
        &mut module,
        "countdown",
        vec![seq.clone(), Ty::U32],
        vec![seq.clone()],
        vec![
            block(
                0,
                &[(0, seq.clone()), (1, Ty::U32)],
                vec![
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(0),
                        },
                        2,
                    ),
                    op(
                        Inst::ICmp {
                            op: trust_ir::ICmpOp::Eq,
                            ty: Ty::U32,
                            lhs: v(1),
                            rhs: v(2),
                        },
                        3,
                    ),
                    eff(Inst::CondBr {
                        cond: v(3),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            ),
            block(1, &[], vec![ret(&[0])]),
            block(
                2,
                &[],
                vec![
                    op(
                        Inst::Call {
                            callee: inc,
                            args: vec![v(0)],
                        },
                        4,
                    ),
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(1),
                        },
                        5,
                    ),
                    op(
                        Inst::BinOp {
                            op: trust_ir::BinOp::Sub,
                            ty: Ty::U32,
                            lhs: v(1),
                            rhs: v(5),
                        },
                        6,
                    ),
                    op(
                        Inst::Call {
                            callee: countdown,
                            args: vec![v(4), v(6)],
                        },
                        7,
                    ),
                    ret(&[7]),
                ],
            ),
        ],
    );
    let c_sum = declare(&mut module, "c_sum", vec![seq.clone()], vec![Ty::I64]);
    define(
        &mut module,
        "sum_mapped",
        vec![seq.clone()],
        vec![Ty::I64],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(0),
                        k: 2,
                    },
                    1,
                ),
                op(
                    Inst::Call {
                        callee: c_sum,
                        args: vec![v(1)],
                    },
                    2,
                ),
                ret(&[2]),
            ],
        )],
    );
    // consts_in_loop(n): acc = 0; repeat n times acc += c_sum(inc([10, 20])); return acc
    define(
        &mut module,
        "consts_in_loop",
        vec![Ty::U32],
        vec![Ty::I64],
        vec![
            block(
                0,
                &[(0, Ty::U32)],
                vec![
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(0),
                        },
                        1,
                    ),
                    op(
                        Inst::Const {
                            ty: Ty::I64,
                            value: int(0),
                        },
                        2,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(1), v(2)],
                    }),
                ],
            ),
            block(
                1,
                &[(3, Ty::U32), (4, Ty::I64)],
                vec![
                    op(
                        Inst::ICmp {
                            op: trust_ir::ICmpOp::Eq,
                            ty: Ty::U32,
                            lhs: v(3),
                            rhs: v(0),
                        },
                        5,
                    ),
                    eff(Inst::CondBr {
                        cond: v(5),
                        then_target: b(3),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            ),
            block(
                2,
                &[],
                vec![
                    op(
                        Inst::Const {
                            ty: seq.clone(),
                            value: Constant::Sequence(vec![int(10), int(20)]),
                        },
                        6,
                    ),
                    op(
                        Inst::Call {
                            callee: inc,
                            args: vec![v(6)],
                        },
                        7,
                    ),
                    op(
                        Inst::Call {
                            callee: c_sum,
                            args: vec![v(7)],
                        },
                        8,
                    ),
                    op(
                        Inst::BinOp {
                            op: trust_ir::BinOp::Add,
                            ty: Ty::I64,
                            lhs: v(4),
                            rhs: v(8),
                        },
                        9,
                    ),
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(1),
                        },
                        10,
                    ),
                    op(
                        Inst::BinOp {
                            op: trust_ir::BinOp::Add,
                            ty: Ty::U32,
                            lhs: v(3),
                            rhs: v(10),
                        },
                        11,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(11), v(9)],
                    }),
                ],
            ),
            block(3, &[], vec![ret(&[4])]),
        ],
    );
    module
}

const FLOWS_DRIVER: &str = r#"
extern void *twice(const void *s, void *out);
extern void *pick(uint8_t c, const void *s, void *out);
extern void *iterate(const void *s, uint32_t n, void *out);
extern void *wide(int64_t a0, int64_t a1, int64_t a2, int64_t a3, int64_t a4, int64_t a5,
                  int64_t a6, int64_t a7, const void *s, void *out);
extern void *three(void *out);
extern int64_t sum_mapped(const void *s);
extern int64_t consts_in_loop(uint32_t n);
extern void *mapped_const(void *out);
extern void *twice_inline(const void *s, void *out);
extern void *iterate_inline(const void *s, uint32_t n, void *out);
extern void *countdown(const void *s, uint32_t n, void *out);

/* The C callee the backend passes a sequence image to. */
int64_t c_sum(const void *s) {
    int64_t sum = 0;
    uint64_t len = image_len(s);
    for (uint64_t i = 0; i < len; i++) {
        int32_t x; memcpy(&x, (const unsigned char *)s + 8 + 4 * i, 4);
        sum += x;
    }
    return sum;
}

static const int32_t in5[] = {-3, 0, 2147483646, 17, -2147483648};
static const int32_t twice_interp[] = INTERP_TWICE;
static const int32_t pick_true_interp[] = INTERP_PICK_TRUE;
static const int32_t pick_false_interp[] = INTERP_PICK_FALSE;
static const int32_t iterate_interp[] = INTERP_ITERATE;
static const int32_t wide_interp[] = INTERP_WIDE;
static const int32_t three_interp[] = INTERP_THREE;
static const int32_t mapped_const_interp[] = INTERP_MAPPED_CONST;
static const int32_t twice_inline_interp[] = INTERP_INLINE_TWICE;
static const int32_t iterate_inline_interp[] = INTERP_INLINE_ITERATE;
static const int32_t countdown_interp[] = INTERP_COUNTDOWN;

static void add_model(int32_t *out, const int32_t *in, int n, uint32_t k) {
    for (int i = 0; i < n; i++) out[i] = (int32_t)((uint32_t)in[i] + k);
}

int main(void) {
    int32_t model[5];
    void *s = image_new(5, 4, in5);

    void *out = buffer_new(5, 4);
    add_model(model, in5, 5, 2);
    if (twice(s, out) != out || !image_equals("twice vs C model", out, 5, 4, model)
        || !image_equals("twice vs interpreter", out, 5, 4, twice_interp)) return 1;
    free(out);

    out = buffer_new(5, 4);
    add_model(model, in5, 5, 10);
    if (pick(1, s, out) != out || !image_equals("pick(true) vs C model", out, 5, 4, model)
        || !image_equals("pick(true) vs interpreter", out, 5, 4, pick_true_interp)) return 2;
    free(out);
    out = buffer_new(5, 4);
    if (pick(0, s, out) != out || !image_equals("pick(false) vs C model", out, 5, 4, in5)
        || !image_equals("pick(false) vs interpreter", out, 5, 4, pick_false_interp)) return 3;
    free(out);

    for (uint32_t n = 0; n < 40; n += 13) {
        out = buffer_new(5, 4);
        add_model(model, in5, 5, n);
        if (iterate(s, n, out) != out || !image_equals("iterate vs C model", out, 5, 4, model))
            return 4;
        if (n == 13 && !image_equals("iterate(13) vs interpreter", out, 5, 4, iterate_interp))
            return 5;
        free(out);
    }

    out = buffer_new(5, 4);
    add_model(model, in5, 5, 100);
    if (wide(1, 2, 3, 4, 5, 6, 7, 8, s, out) != out
        || !image_equals("wide vs C model", out, 5, 4, model)
        || !image_equals("wide vs interpreter", out, 5, 4, wide_interp)) return 6;
    free(out);

    out = buffer_new(3, 4);
    const int32_t three_model[] = {2, 3, 4};
    if (three(out) != out || !image_equals("three vs C model", out, 3, 4, three_model)
        || !image_equals("three vs interpreter", out, 3, 4, three_interp)) return 7;
    free(out);

    int64_t want = 0;
    for (int i = 0; i < 5; i++) want += (int32_t)((uint32_t)in5[i] + 2);
    if (sum_mapped(s) != want) {
        printf("sum_mapped %lld, C model %lld\n", (long long)sum_mapped(s), (long long)want);
        return 8;
    }
    if (!image_equals("input untouched", s, 5, 4, in5)) return 9;

    if (consts_in_loop(0) != 0 || consts_in_loop(1) != 32 || consts_in_loop(1000) != 32000) {
        printf("consts_in_loop %lld %lld %lld\n", (long long)consts_in_loop(0),
               (long long)consts_in_loop(1), (long long)consts_in_loop(1000));
        return 10;
    }

    out = buffer_new(3, 4);
    const int32_t mapped_const_model[] = {6, 7, 8};
    if (mapped_const(out) != out
        || !image_equals("mapped_const vs C model", out, 3, 4, mapped_const_model)
        || !image_equals("mapped_const vs interpreter", out, 3, 4, mapped_const_interp)) return 11;
    free(out);

    out = buffer_new(5, 4);
    add_model(model, in5, 5, 3);
    if (twice_inline(s, out) != out || !image_equals("twice_inline vs C model", out, 5, 4, model)
        || !image_equals("twice_inline vs interpreter", out, 5, 4, twice_inline_interp)) return 12;
    free(out);

    for (uint32_t n = 0; n < 700; n += 233) {
        out = buffer_new(5, 4);
        add_model(model, in5, 5, 3 * n);
        if (iterate_inline(s, n, out) != out
            || !image_equals("iterate_inline vs C model", out, 5, 4, model)) return 13;
        if (n == 233
            && !image_equals("iterate_inline(233) vs interpreter", out, 5, 4, iterate_inline_interp))
            return 14;
        free(out);
    }
    for (uint32_t n = 0; n < 60; n += 17) {
        out = buffer_new(5, 4);
        add_model(model, in5, 5, n);
        if (countdown(s, n, out) != out || !image_equals("countdown vs C model", out, 5, 4, model))
            return 16;
        if (n == 17 && !image_equals("countdown(17) vs interpreter", out, 5, 4, countdown_interp))
            return 17;
        free(out);
    }
    if (!image_equals("input untouched at exit", s, 5, 4, in5)) return 15;
    free(s);
    return 0;
}
"#;

#[test]
fn sequences_flow_through_parameters_results_calls_selects_and_loops_o0_through_o3() {
    let module = build_flows();
    let seq =
        module.func_types[module.function_by_name("inc").unwrap().ty.as_usize()].params[0].clone();
    let in5: Vec<Elem> = [-3, 0, 2_147_483_646, 17, i32::MIN as i128]
        .map(Elem::Int)
        .to_vec();
    let s = || collection_value(&seq, &Ty::I32, &in5);
    let array = |elems: Vec<Elem>| c_array(&elems);
    let twice = interpret_collection(&module, "twice", vec![s()]);
    let pick_true = interpret_collection(&module, "pick", vec![InterpretValue::bool(true), s()]);
    let pick_false = interpret_collection(&module, "pick", vec![InterpretValue::bool(false), s()]);
    let iterate = interpret_collection(
        &module,
        "iterate",
        vec![s(), InterpretValue::int(Ty::U32, 13).unwrap()],
    );
    let mut wide_args: Vec<InterpretValue> = (1..=8)
        .map(|x| InterpretValue::int(Ty::I64, x).unwrap())
        .collect();
    wide_args.push(s());
    let wide = interpret_collection(&module, "wide", wide_args);
    let three = interpret_collection(&module, "three", vec![]);
    assert_eq!(three, [2, 3, 4].map(Elem::Int).to_vec());
    let mapped_const = interpret_collection(&module, "mapped_const", vec![]);
    let twice_inline = interpret_collection(&module, "twice_inline", vec![s()]);
    let iterate_inline = interpret_collection(
        &module,
        "iterate_inline",
        vec![s(), InterpretValue::int(Ty::U32, 233).unwrap()],
    );
    let countdown = interpret_collection(
        &module,
        "countdown",
        vec![s(), InterpretValue::int(Ty::U32, 17).unwrap()],
    );
    let driver = format!("{PRELUDE}{FLOWS_DRIVER}")
        .replace("INTERP_TWICE", &array(twice))
        .replace("INTERP_PICK_TRUE", &array(pick_true))
        .replace("INTERP_PICK_FALSE", &array(pick_false))
        .replace("INTERP_ITERATE", &array(iterate))
        .replace("INTERP_WIDE", &array(wide))
        .replace("INTERP_THREE", &array(three))
        .replace("INTERP_MAPPED_CONST", &array(mapped_const))
        .replace("INTERP_INLINE_TWICE", &array(twice_inline))
        .replace("INTERP_INLINE_ITERATE", &array(iterate_inline))
        .replace("INTERP_COUNTDOWN", &array(countdown));
    run_native_at_every_level("seq_flows", &module, &driver);
}

/// The element calls a `SeqMap` loop emits live in the loop's own blocks. With
/// module-local element functions they carry exact-module bindings, and the
/// strict adapter replays every one against its recorded (block, instruction)
/// coordinates and source edge after an exhaustive carrier census.
#[test]
fn seq_map_element_calls_replay_as_exact_module_bindings_in_the_strict_adapter() {
    use trust_cg_codegen::strict_adapter::translate_core_module_for_target_with_validation_and_license;
    use trust_cg_codegen::target::TargetSpec;
    let cases = map_cases();
    let mut module = build_maps(&cases);
    let mut element_functions = 0;
    for function in &mut module.functions {
        if function.name.ends_with("_elem") {
            function.linkage = trust_ir::Linkage::Internal;
            element_functions += 1;
        }
    }
    assert_eq!(element_functions, 4, "four SeqMap element functions");
    let result = translate_core_module_for_target_with_validation_and_license(
        &module,
        TargetSpec::parse("aarch64-apple-darwin").expect("target"),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("strict adapter: {error}"));
    assert_eq!(
        result.exact_module_call_count(),
        element_functions,
        "one exact element call per SeqMap loop body"
    );
}

// ---------------------------------------------------------------------------
// Boxed sets: constants, parameters, results, selects
// ---------------------------------------------------------------------------

fn build_sets() -> Module {
    let mut module = Module::new("boxed_sets");
    let elem = module
        .add_type(Ty::U16)
        .expect("Module::add_type: test fixture");
    let set = Ty::Set(elem, SetRepr::Boxed);
    define(
        &mut module,
        "set_const",
        vec![],
        vec![set.clone()],
        vec![block(
            0,
            &[],
            vec![
                op(
                    Inst::Const {
                        ty: set.clone(),
                        value: Constant::Set(vec![int(9), int(1), int(65535), int(300)]),
                    },
                    0,
                ),
                ret(&[0]),
            ],
        )],
    );
    define(
        &mut module,
        "set_pass",
        vec![Ty::Bool, set.clone()],
        vec![set.clone()],
        vec![block(
            0,
            &[(0, Ty::Bool), (1, set.clone())],
            vec![
                op(
                    Inst::Copy {
                        ty: set.clone(),
                        operand: v(1),
                    },
                    2,
                ),
                op(
                    Inst::Select {
                        ty: set.clone(),
                        cond: v(0),
                        then_val: v(2),
                        else_val: v(1),
                    },
                    3,
                ),
                ret(&[3]),
            ],
        )],
    );
    module
}

const SETS_DRIVER: &str = r#"
extern void *set_const(void *out);
extern void *set_pass(uint8_t c, const void *s, void *out);
static const uint16_t const_model[] = {9, 1, 65535, 300};
static const uint16_t const_interp[] = INTERP_CONST;
static const uint16_t in3[] = {4, 65534, 8};
static const uint16_t pass_interp[] = INTERP_PASS;
int main(void) {
    void *out = buffer_new(4, 2);
    if (set_const(out) != out || !image_equals("set_const vs C model", out, 4, 2, const_model)
        || !image_equals("set_const vs interpreter", out, 4, 2, const_interp)) return 1;
    free(out);
    void *s = image_new(3, 2, in3);
    for (int c = 0; c < 2; c++) {
        out = buffer_new(3, 2);
        if (set_pass((uint8_t)c, s, out) != out
            || !image_equals("set_pass vs C model", out, 3, 2, in3)
            || !image_equals("set_pass vs interpreter", out, 3, 2, pass_interp)) return 2 + c;
        free(out);
    }
    free(s);
    return 0;
}
"#;

#[test]
fn boxed_sets_move_as_constants_parameters_and_results_o0_through_o3() {
    let module = build_sets();
    let set = module.func_types[module.function_by_name("set_const").unwrap().ty.as_usize()]
        .returns[0]
        .clone();
    let constant = interpret_collection(&module, "set_const", vec![]);
    let input: Vec<Elem> = [4, 65534, 8].map(Elem::Int).to_vec();
    let pass = interpret_collection(
        &module,
        "set_pass",
        vec![
            InterpretValue::bool(true),
            collection_value(&set, &Ty::U16, &input),
        ],
    );
    assert_eq!(
        pass, input,
        "interpreter oracle: a set value moves unchanged"
    );
    let driver = format!("{PRELUDE}{SETS_DRIVER}")
        .replace("INTERP_CONST", &c_array(&constant))
        .replace("INTERP_PASS", &c_array(&pass));
    run_native_at_every_level("boxed_sets", &module, &driver);
}

// ---------------------------------------------------------------------------
// Named refusals
// ---------------------------------------------------------------------------

/// `f(s: seq<i64>) -> i64 = extract_element(s, 0)`: the must-refuse corpus
/// row `sequence_element_op`'s shape.
fn element_op_over_parameter() -> Module {
    let mut module = Module::new("seq_extract_param");
    let seq = seq_of(&mut module, Ty::I64);
    define(
        &mut module,
        "first",
        vec![seq.clone()],
        vec![Ty::I64],
        vec![block(
            0,
            &[(0, seq)],
            vec![
                op(
                    Inst::Const {
                        ty: Ty::U64,
                        value: int(0),
                    },
                    1,
                ),
                op(
                    Inst::ExtractElement {
                        ty: Ty::I64,
                        array: v(0),
                        index: v(1),
                    },
                    2,
                ),
                ret(&[2]),
            ],
        )],
    );
    module
}

/// The same element ops over a constant this backend materialized: the
/// format's refusal does not depend on the operand's provenance.
fn element_ops_over_constant(insert: bool) -> Module {
    let mut module = Module::new("seq_element_const");
    let seq = seq_of(&mut module, Ty::I64);
    let constant = op(
        Inst::Const {
            ty: seq.clone(),
            value: Constant::Sequence(vec![int(5), int(8)]),
        },
        0,
    );
    let index = op(
        Inst::Const {
            ty: Ty::U64,
            value: int(1),
        },
        1,
    );
    let body = if insert {
        vec![
            constant,
            index,
            op(
                Inst::Const {
                    ty: Ty::I64,
                    value: int(13),
                },
                2,
            ),
            op(
                Inst::InsertElement {
                    ty: seq.clone(),
                    array: v(0),
                    index: v(1),
                    value: v(2),
                },
                3,
            ),
            ret(&[2]),
        ]
    } else {
        vec![
            constant,
            index,
            op(
                Inst::ExtractElement {
                    ty: Ty::I64,
                    array: v(0),
                    index: v(1),
                },
                2,
            ),
            ret(&[2]),
        ]
    };
    define(
        &mut module,
        "element",
        vec![],
        vec![Ty::I64],
        vec![block(0, &[], body)],
    );
    module
}

/// One function `f(p: ptr, s: seq<i32>) -> ptr` whose body is `inst`.
fn memory_shape(name: &str, inst: impl FnOnce(&Ty) -> Vec<InstrNode>) -> Module {
    let mut module = Module::new(name);
    let seq = seq_of(&mut module, Ty::I32);
    let body = inst(&seq);
    define(
        &mut module,
        name,
        vec![Ty::Ptr, seq.clone()],
        vec![Ty::Ptr],
        vec![block(0, &[(0, Ty::Ptr), (1, seq)], body)],
    );
    module
}

#[test]
fn sequence_element_ops_are_refused_as_the_format_states_whatever_the_provenance() {
    let needles = ["[TCG-SEQ]", "UnlowerableForCodegen", "no machine layout"];
    expect_refusal(
        "extract over a parameter",
        &element_op_over_parameter(),
        &needles,
    );
    expect_refusal(
        "extract over a constant",
        &element_ops_over_constant(false),
        &needles,
    );
    expect_refusal(
        "insert over a constant",
        &element_ops_over_constant(true),
        &needles,
    );
}

#[test]
fn sequences_outside_value_slots_are_refused_by_name() {
    let no_layout = ["[TCG-SEQ]", "no byte layout"];
    expect_refusal(
        "GEP over a sequence pointee",
        &memory_shape("seq_gep", |seq| {
            vec![
                op(
                    Inst::Const {
                        ty: Ty::I64,
                        value: int(1),
                    },
                    2,
                ),
                op(
                    Inst::GEP {
                        pointee_ty: seq.clone(),
                        base: v(0),
                        indices: vec![v(2)],
                        inbounds: false,
                    },
                    3,
                ),
                ret(&[3]),
            ]
        }),
        &["Inst::GEP spells", "no byte layout"],
    );
    expect_refusal(
        "load of a sequence",
        &memory_shape("seq_load", |seq| {
            vec![
                op(
                    Inst::Load {
                        ty: seq.clone(),
                        ptr: v(0),
                        volatile: false,
                        align: None,
                    },
                    2,
                ),
                ret(&[0]),
            ]
        }),
        &no_layout,
    );
    expect_refusal(
        "store of a sequence",
        &memory_shape("seq_store", |seq| {
            vec![
                eff(Inst::Store {
                    ty: seq.clone(),
                    ptr: v(0),
                    value: v(1),
                    volatile: false,
                    align: None,
                }),
                ret(&[0]),
            ]
        }),
        &no_layout,
    );
    expect_refusal(
        "alloca of a sequence",
        &memory_shape("seq_alloca", |seq| {
            vec![
                op(
                    Inst::Alloca {
                        ty: seq.clone(),
                        count: None,
                        align: None,
                    },
                    2,
                ),
                ret(&[2]),
            ]
        }),
        &no_layout,
    );
    expect_refusal(
        "a sequence as an i64 store operand",
        &memory_shape("seq_as_scalar", |_| {
            vec![
                eff(Inst::Store {
                    ty: Ty::I64,
                    ptr: v(0),
                    value: v(1),
                    volatile: false,
                    align: None,
                }),
                ret(&[0]),
            ]
        }),
        &["[TCG-SEQ]", "as an operand"],
    );
    expect_refusal(
        "pointer cast of a sequence",
        &memory_shape("seq_cast", |seq| {
            vec![
                op(
                    Inst::Cast {
                        op: trust_ir::CastOp::PtrToPtr,
                        src_ty: seq.clone(),
                        dst_ty: Ty::Ptr,
                        operand: v(1),
                    },
                    2,
                ),
                ret(&[2]),
            ]
        }),
        &no_layout,
    );
}

/// `f() -> seq<elem>` returning `value` (declared `ty`).
fn returning(
    name: &str,
    elem: Option<Ty>,
    ty: impl FnOnce(Option<trust_ir::TyId>) -> Ty,
    value: Constant,
) -> Module {
    let mut module = Module::new(name);
    let id = elem.map(|elem| {
        module
            .add_type(elem)
            .expect("Module::add_type: test fixture")
    });
    let ty = ty(id);
    define(
        &mut module,
        name,
        vec![],
        vec![ty.clone()],
        vec![block(
            0,
            &[],
            vec![op(Inst::Const { ty, value }, 0), ret(&[0])],
        )],
    );
    module
}

#[test]
fn unadmitted_elements_bitsets_nesting_and_repeated_set_members_are_refused_by_name() {
    expect_refusal(
        "i128 elements",
        &returning(
            "seq_i128",
            Some(Ty::I128),
            |id| Ty::Sequence(id.unwrap()),
            Constant::Sequence(vec![int(1)]),
        ),
        &["[TCG-SEQ]", "I128", "is not admitted"],
    );
    expect_refusal(
        "pointer elements",
        &returning(
            "seq_ptr",
            Some(Ty::Ptr),
            |id| Ty::Sequence(id.unwrap()),
            Constant::Sequence(vec![]),
        ),
        &["[TCG-SEQ]", "is not admitted"],
    );
    expect_refusal(
        "bitset",
        &returning(
            "set_bitset",
            Some(Ty::U8),
            |id| Ty::Set(id.unwrap(), SetRepr::Bitset),
            Constant::Set(vec![int(1)]),
        ),
        &["[TCG-SEQ]", "SetRepr::Bitset", "universe"],
    );
    expect_refusal(
        "repeated set element",
        &returning(
            "set_repeat",
            Some(Ty::I32),
            |id| Ty::Set(id.unwrap(), SetRepr::Boxed),
            Constant::Set(vec![int(3), int(4), int(3)]),
        ),
        &["[TCG-SEQ]", "repeats an element", "multiset"],
    );
    // Distinct literals that store one image repeat too: two f64 literals
    // that round to one f32 are one `F32` slot. The integer form of that alias
    // (`Int(-1)` and `Int(255)` as one `I8` byte 0xff) is no longer
    // constructible: `255` is no `i8` value, and TrustIR's typed admission,
    // which every compiler entry consumes first, refuses it by name.
    expect_refusal(
        "aliasing i8 set literals",
        &returning(
            "set_alias_i8",
            Some(Ty::I8),
            |id| Ty::Set(id.unwrap(), SetRepr::Boxed),
            Constant::Set(vec![int(-1), int(7), int(255)]),
        ),
        &[
            "TrustIrAdmissionRefused",
            "function 'set_alias_i8' bb0[2]: const type mismatch: expected i8, got int",
        ],
    );
    expect_refusal(
        "aliasing f32 set literals",
        &returning(
            "set_alias_f32",
            Some(Ty::F32),
            |id| Ty::Set(id.unwrap(), SetRepr::Boxed),
            Constant::Set(vec![
                Constant::Float(1.0),
                Constant::Float(1.0 + f64::EPSILON),
            ]),
        ),
        &["[TCG-SEQ]", "repeats an element", "0x3f800000"],
    );
    expect_refusal(
        "set constant under a sequence type",
        &returning(
            "seq_set_mismatch",
            Some(Ty::I32),
            |id| Ty::Sequence(id.unwrap()),
            Constant::Set(vec![int(3)]),
        ),
        // Typed admission refuses it before the adapter's own
        // `does not match its declared type` arm.
        &[
            "TrustIrAdmissionRefused",
            "function 'seq_set_mismatch' bb0: const type mismatch: expected seq<ty.0>, got set[1]",
        ],
    );
    // A struct field of sequence type has no in-memory layout.
    let mut module = Module::new("seq_in_struct");
    let seq = seq_of(&mut module, Ty::I32);
    module.structs.push(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Holder".to_string(),
        fields: vec![FieldDef {
            name: "s".to_string(),
            ty: seq,
            offset: None,
        }],
        repr: StructRepr::C,
        size: None,
        align: None,
    });
    let holder = Ty::Struct(StructId::new(0));
    define(
        &mut module,
        "holder",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
        vec![block(
            0,
            &[(0, Ty::Ptr)],
            vec![
                op(
                    Inst::Alloca {
                        ty: holder,
                        count: None,
                        align: None,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    expect_refusal(
        "sequence nested in a struct",
        &module,
        &["[TCG-SEQ]", "nested inside another type"],
    );
}

#[test]
fn seq_map_shapes_outside_trust_ir_semantics_are_refused_by_name() {
    let unary = |name: &str, elem: Ty, inst: fn(Ty) -> Inst| {
        let mut module = Module::new(name);
        let seq = seq_of(&mut module, elem);
        define(
            &mut module,
            name,
            vec![seq.clone()],
            vec![seq.clone()],
            vec![block(
                0,
                &[(0, seq.clone())],
                vec![op(inst(seq), 1), ret(&[1])],
            )],
        );
        module
    };
    expect_refusal(
        "SeqMapAddK over f64",
        &unary("add_k_f64", Ty::F64, |seq| Inst::SeqMapAddK {
            ty: seq,
            seq: v(0),
            k: 1,
        }),
        &["[TCG-SEQ]", "Inst::SeqMapAddK", "integer elements"],
    );
    expect_refusal(
        "SeqMapNot over i32",
        &unary("not_i32", Ty::I32, |seq| Inst::SeqMapNot {
            ty: seq,
            seq: v(0),
        }),
        &["[TCG-SEQ]", "Inst::SeqMapNot", "Bool elements"],
    );
    // SeqMap over a set: trust-ir defines the family only over sequences.
    let mut module = Module::new("map_set");
    let elem = module
        .add_type(Ty::I32)
        .expect("Module::add_type: test fixture");
    let set = Ty::Set(elem, SetRepr::Boxed);
    define(
        &mut module,
        "map_set",
        vec![set.clone()],
        vec![set.clone()],
        vec![block(
            0,
            &[(0, set.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: set,
                        seq: v(0),
                        k: 1,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    expect_refusal(
        "SeqMapAddK over a set",
        &module,
        &["[TCG-SEQ]", "only over Ty::Sequence"],
    );
    // An element function by value instead of `fn(&mut elem)`.
    let mut module = Module::new("map_bad_fwd");
    let seq = seq_of(&mut module, Ty::I32);
    let by_value = define(
        &mut module,
        "by_value",
        vec![Ty::I32],
        vec![Ty::I32],
        vec![block(0, &[(0, Ty::I32)], vec![ret(&[0])])],
    );
    define(
        &mut module,
        "map_bad_fwd",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMap {
                        ty: seq,
                        seq: v(0),
                        fwd: by_value,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    expect_refusal(
        "SeqMap with a by-value element function",
        &module,
        &["[TCG-SEQ]", "SeqMapFwdSignatureMismatch"],
    );
}

#[test]
fn results_without_a_published_length_or_a_direct_callee_are_refused_by_name() {
    // Two paths return different lengths.
    let mut module = Module::new("seq_conflict");
    let seq = seq_of(&mut module, Ty::I32);
    define(
        &mut module,
        "conflict",
        vec![Ty::Bool, seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, Ty::Bool), (1, seq.clone())],
            vec![
                op(
                    Inst::Const {
                        ty: seq.clone(),
                        value: Constant::Sequence(vec![int(1)]),
                    },
                    2,
                ),
                op(
                    Inst::Select {
                        ty: seq,
                        cond: v(0),
                        then_val: v(1),
                        else_val: v(2),
                    },
                    3,
                ),
                ret(&[3]),
            ],
        )],
    );
    expect_refusal(
        "conflicting result lengths",
        &module,
        &["[TCG-SEQ]", "no caller can size its result buffer"],
    );

    // A declaration returning a sequence, called directly.
    let mut module = Module::new("seq_extern_result");
    let seq = seq_of(&mut module, Ty::I32);
    let external = declare(&mut module, "external_seq", vec![], vec![seq.clone()]);
    define(
        &mut module,
        "caller",
        vec![],
        vec![Ty::I64],
        vec![block(
            0,
            &[],
            vec![
                op(
                    Inst::Call {
                        callee: external,
                        args: vec![],
                    },
                    0,
                ),
                op(
                    Inst::Const {
                        ty: Ty::I64,
                        value: int(0),
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    expect_refusal(
        "a declaration's sequence result",
        &module,
        &["[TCG-SEQ]", "publishes no result length"],
    );

    // An indirect call returning a sequence.
    let mut module = Module::new("seq_indirect_result");
    let seq = seq_of(&mut module, Ty::I32);
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![seq.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    define(
        &mut module,
        "indirect",
        vec![Ty::Ptr],
        vec![Ty::I64],
        vec![block(
            0,
            &[(0, Ty::Ptr)],
            vec![
                op(
                    Inst::CallIndirect {
                        callee: v(0),
                        sig,
                        args: vec![],
                        calling_conv: trust_ir::CallingConv::C,
                    },
                    1,
                ),
                op(
                    Inst::Const {
                        ty: Ty::I64,
                        value: int(0),
                    },
                    2,
                ),
                ret(&[2]),
            ],
        )],
    );
    expect_refusal(
        "an indirect sequence result",
        &module,
        &["[TCG-SEQ]", "CallIndirect", "indirect edge"],
    );

    // The ABI is stated for the C convention only: a definition and a call
    // edge of another convention carrying a collection are refused.
    let mut module = Module::new("seq_rust_convention");
    let seq = seq_of(&mut module, Ty::I32);
    let callee = define(
        &mut module,
        "rust_conv",
        vec![seq.clone()],
        vec![Ty::I64],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::Const {
                        ty: Ty::I64,
                        value: int(0),
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    module.functions[callee.index() as usize].calling_conv = trust_ir::CallingConv::Rust;
    expect_refusal(
        "a Rust-convention sequence parameter",
        &module,
        &["[TCG-SEQ]", "C convention only"],
    );
    let mut module = Module::new("seq_rust_convention_edge");
    let seq = seq_of(&mut module, Ty::I32);
    let external = declare(&mut module, "rust_sink", vec![seq.clone()], vec![Ty::I64]);
    module.functions[external.index() as usize].calling_conv = trust_ir::CallingConv::Rust;
    define(
        &mut module,
        "caller",
        vec![seq.clone()],
        vec![Ty::I64],
        vec![block(
            0,
            &[(0, seq)],
            vec![
                op(
                    Inst::Call {
                        callee: external,
                        args: vec![v(0)],
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    expect_refusal(
        "a Rust-convention call edge carrying a sequence",
        &module,
        &["[TCG-SEQ]", "C convention only"],
    );

    // A sequence beside another result.
    let mut module = Module::new("seq_pair_result");
    let seq = seq_of(&mut module, Ty::I32);
    define(
        &mut module,
        "pair",
        vec![seq.clone()],
        vec![seq.clone(), Ty::I64],
        vec![block(
            0,
            &[(0, seq)],
            vec![
                op(
                    Inst::Const {
                        ty: Ty::I64,
                        value: int(0),
                    },
                    1,
                ),
                ret(&[0, 1]),
            ],
        )],
    );
    expect_refusal(
        "a sequence beside another result",
        &module,
        &["[TCG-SEQ]", "only result"],
    );
}

// ---------------------------------------------------------------------------
// Loop-carried images: a per-iteration image never reuses a live one
// ---------------------------------------------------------------------------

/// `name(n: u32) -> seq<i32>`:
///
/// ```text
///   prev = [0, 0, 0]; i = n
///   loop { cur = step(prev); if i == 0 { return prev }; prev = cur; i -= 1 }
/// ```
///
/// Each iteration produces `cur` while `prev`, the previous iteration's
/// image, is still live and is what the function finally returns. Its length
/// is statically 3, so only the cycle rule keeps `cur` out of a fixed frame
/// slot: an image that reused one slot per iteration would overwrite `prev`
/// with `cur` and return `n + 1` instead of `n`.
fn define_loop_carried(
    module: &mut Module,
    name: &str,
    seq: &Ty,
    step: impl Fn(ValueId) -> Inst,
) -> FuncId {
    define(
        module,
        name,
        vec![Ty::U32],
        vec![seq.clone()],
        vec![
            block(
                0,
                &[(0, Ty::U32)],
                vec![
                    op(
                        Inst::Const {
                            ty: seq.clone(),
                            value: Constant::Sequence(vec![int(0), int(0), int(0)]),
                        },
                        1,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(1), v(0)],
                    }),
                ],
            ),
            block(
                1,
                &[(2, seq.clone()), (3, Ty::U32)],
                vec![
                    op(step(v(2)), 4),
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(0),
                        },
                        5,
                    ),
                    op(
                        Inst::ICmp {
                            op: trust_ir::ICmpOp::Eq,
                            ty: Ty::U32,
                            lhs: v(3),
                            rhs: v(5),
                        },
                        6,
                    ),
                    eff(Inst::CondBr {
                        cond: v(6),
                        then_target: b(3),
                        then_args: vec![v(2)],
                        else_target: b(2),
                        else_args: vec![],
                    }),
                ],
            ),
            block(
                2,
                &[],
                vec![
                    op(
                        Inst::Const {
                            ty: Ty::U32,
                            value: int(1),
                        },
                        7,
                    ),
                    op(
                        Inst::BinOp {
                            op: trust_ir::BinOp::Sub,
                            ty: Ty::U32,
                            lhs: v(3),
                            rhs: v(7),
                        },
                        8,
                    ),
                    eff(Inst::Br {
                        target: b(1),
                        args: vec![v(4), v(8)],
                    }),
                ],
            ),
            block(3, &[(9, seq.clone())], vec![ret(&[9])]),
        ],
    )
}

fn build_loop_carried() -> Module {
    let mut module = Module::new("sequence_loop_carried");
    let seq = seq_of(&mut module, Ty::I32);
    let inc = define(
        &mut module,
        "inc",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(0),
                        k: 1,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    let bump = define_element_function(
        &mut module,
        "bump",
        &Ty::I32,
        MapKind::Fwd { mul: 1, add: 1 },
    );
    let map_seq = seq.clone();
    define_loop_carried(&mut module, "loop_map", &seq, move |prev| {
        Inst::SeqMapAddK {
            ty: map_seq.clone(),
            seq: prev,
            k: 1,
        }
    });
    define_loop_carried(&mut module, "loop_call", &seq, move |prev| Inst::Call {
        callee: inc,
        args: vec![prev],
    });
    let fwd_seq = seq.clone();
    define_loop_carried(&mut module, "loop_fwd", &seq, move |prev| Inst::SeqMap {
        ty: fwd_seq.clone(),
        seq: prev,
        fwd: bump,
    });
    module
}

const LOOP_COUNTS: [u32; 5] = [0, 1, 2, 5, 40];

const LOOP_CARRIED_DRIVER: &str = r#"
extern void *loop_map(uint32_t n, void *out);
extern void *loop_call(uint32_t n, void *out);
extern void *loop_fwd(uint32_t n, void *out);
static const uint32_t counts[] = LOOP_COUNTS;
static const int32_t map_interp[] = INTERP_LOOP_MAP;
static const int32_t call_interp[] = INTERP_LOOP_CALL;
static const int32_t fwd_interp[] = INTERP_LOOP_FWD;

static int check(const char *what, void *(*f)(uint32_t, void *), const int32_t *interp) {
    for (int k = 0; k < (int)(sizeof counts / sizeof counts[0]); k++) {
        uint32_t n = counts[k];
        /* C model: `prev` after n iterations of +1 is [n, n, n]. */
        const int32_t model[3] = {(int32_t)n, (int32_t)n, (int32_t)n};
        char label[80];
        void *out = buffer_new(3, 4);
        snprintf(label, sizeof label, "%s(%u) vs C model", what, n);
        if (f(n, out) != out || !image_equals(label, out, 3, 4, model)) return 0;
        snprintf(label, sizeof label, "%s(%u) vs interpreter", what, n);
        if (!image_equals(label, out, 3, 4, interp + 3 * k)) return 0;
        free(out);
    }
    return 1;
}

int main(void) {
    if (!check("loop_map", loop_map, map_interp)) return 1;
    if (!check("loop_call", loop_call, call_interp)) return 2;
    if (!check("loop_fwd", loop_fwd, fwd_interp)) return 3;
    return 0;
}
"#;

#[test]
fn loop_carried_images_keep_the_previous_iteration_alive_o0_through_o3() {
    let module = build_loop_carried();
    let interp = |name: &str| {
        let mut flat = Vec::new();
        for n in LOOP_COUNTS {
            let result = interpret_collection(
                &module,
                name,
                vec![InterpretValue::int(Ty::U32, i128::from(n)).unwrap()],
            );
            assert_eq!(
                result,
                vec![Elem::Int(i128::from(n)); 3],
                "interpreter oracle: {name}({n}) returns the previous iteration's image"
            );
            flat.extend(result);
        }
        c_array(&flat)
    };
    let map = interp("loop_map");
    let call = interp("loop_call");
    let fwd = interp("loop_fwd");
    let counts: Vec<String> = LOOP_COUNTS.iter().map(u32::to_string).collect();
    let driver = format!("{PRELUDE}{LOOP_CARRIED_DRIVER}")
        .replace("LOOP_COUNTS", &format!("{{{}}}", counts.join(", ")))
        .replace("INTERP_LOOP_MAP", &map)
        .replace("INTERP_LOOP_CALL", &call)
        .replace("INTERP_LOOP_FWD", &fwd);
    run_native_at_every_level("seq_loop_carried", &module, &driver);
}

// ---------------------------------------------------------------------------
// SeqMap element cells: one fresh cell per element, alive for the frame
// ---------------------------------------------------------------------------

/// `chain(s) = seq_map(s, stash)` and `chain_then_peek(s)`, which maps, then
/// allocates another image, then asks C for the value in the LAST element's
/// cell. `stash` is C: it adds the previous element's cell to this one and
/// keeps the pointer.
fn build_cells() -> Module {
    let mut module = Module::new("sequence_element_cells");
    let seq = seq_of(&mut module, Ty::I32);
    let stash = declare(
        &mut module,
        "stash",
        vec![Ty::RefMut(Box::new(Ty::I32))],
        vec![],
    );
    let peek = declare(&mut module, "peek", vec![], vec![Ty::I64]);
    define(
        &mut module,
        "chain",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMap {
                        ty: seq.clone(),
                        seq: v(0),
                        fwd: stash,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    define(
        &mut module,
        "chain_then_peek",
        vec![seq.clone()],
        vec![Ty::I64],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMap {
                        ty: seq.clone(),
                        seq: v(0),
                        fwd: stash,
                    },
                    1,
                ),
                op(
                    Inst::Const {
                        ty: seq.clone(),
                        value: Constant::Sequence(vec![int(-7), int(-7), int(-7), int(-7)]),
                    },
                    2,
                ),
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(2),
                        k: 3,
                    },
                    3,
                ),
                op(
                    Inst::Call {
                        callee: peek,
                        args: vec![],
                    },
                    4,
                ),
                ret(&[4]),
            ],
        )],
    );
    module
}

const CELLS_DRIVER: &str = r#"
extern void *chain(const void *s, void *out);
extern int64_t chain_then_peek(const void *s);

static int32_t *prev_cell;
static int32_t *cells[64];
static int ncells;

/* The element function: each cell adds the previous element's cell, which
   trust-ir keeps allocated (and holding that element's final value) for the
   rest of the frame. */
void stash(int32_t *p) {
    if (prev_cell) *p += *prev_cell;
    prev_cell = p;
    if (ncells < 64) cells[ncells++] = p;
}

int64_t peek(void) { return prev_cell ? *prev_cell : -1; }

static const int32_t in5[] = {1, 2, 3, 4, -20};
/* Fresh-cell model: the running prefix sums. */
static const int32_t model[] = {1, 3, 6, 10, -10};

int main(void) {
    void *s = image_new(5, 4, in5);
    for (int round = 0; round < 3; round++) {
        prev_cell = 0;
        ncells = 0;
        void *out = buffer_new(5, 4);
        if (chain(s, out) != out || !image_equals("chain vs fresh-cell model", out, 5, 4, model))
            return 1;
        if (ncells != 5) {
            printf("chain called its element function %d times\n", ncells);
            return 2;
        }
        for (int i = 0; i < ncells; i++)
            for (int j = i + 1; j < ncells; j++)
                if (cells[i] == cells[j]) {
                    printf("elements %d and %d share the cell %p\n", i, j, (void *)cells[i]);
                    return 3;
                }
        free(out);
    }
    prev_cell = 0;
    ncells = 0;
    int64_t last = chain_then_peek(s);
    if (last != -10) {
        printf("chain_then_peek read %lld from the last cell, model -10\n", (long long)last);
        return 4;
    }
    if (!image_equals("input untouched", s, 5, 4, in5)) return 5;
    free(s);
    return 0;
}
"#;

/// trust-ir's interpreter gives every `SeqMap` element a FRESH cell that stays
/// allocated for the rest of the frame (`eval_alloca` per element). The
/// interpreter cannot call the C element function, so the oracle here is the
/// C model of those semantics: an element function that keeps its `&mut elem`
/// and reads it back on the next element sees the previous element's final
/// value, the cells are pairwise distinct, and the last cell still holds its
/// value after the map and a later allocation.
#[test]
fn seq_map_gives_every_element_a_fresh_cell_that_outlives_the_map_o0_through_o3() {
    run_native_at_every_level(
        "seq_cells",
        &build_cells(),
        &format!("{PRELUDE}{CELLS_DRIVER}"),
    );
}

// ---------------------------------------------------------------------------
// Run-time length witnesses: each one traps
// ---------------------------------------------------------------------------

/// Functions whose length witnesses a C callee (`shrink`, which drops the
/// last element of an image it was passed, when enabled) can break, and an
/// `inc` a C caller can hand a header no real image has.
fn build_witnesses() -> Module {
    let mut module = Module::new("sequence_length_witnesses");
    let seq = seq_of(&mut module, Ty::I32);
    let shrink = declare(&mut module, "shrink", vec![seq.clone()], vec![]);
    let c_sum = declare(&mut module, "c_sum", vec![seq.clone()], vec![Ty::I64]);
    let inc = define(
        &mut module,
        "inc",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(0),
                        k: 1,
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    // The callee's return witness: `t` has the length `s` had, but `s` is
    // shorter by the return.
    define(
        &mut module,
        "map_then_shrink",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::SeqMapAddK {
                        ty: seq.clone(),
                        seq: v(0),
                        k: 1,
                    },
                    1,
                ),
                eff(Inst::Call {
                    callee: shrink,
                    args: vec![v(0)],
                }),
                ret(&[1]),
            ],
        )],
    );
    // The caller's post-call witness: `shrink_then_return` returns a shorter
    // image than the caller sized for, and its own return check agrees with
    // the shrunk parameter.
    let shrink_then_return = define(
        &mut module,
        "shrink_then_return",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                eff(Inst::Call {
                    callee: shrink,
                    args: vec![v(0)],
                }),
                ret(&[0]),
            ],
        )],
    );
    define(
        &mut module,
        "forward_shrunk",
        vec![seq.clone()],
        vec![seq.clone()],
        vec![block(
            0,
            &[(0, seq.clone())],
            vec![
                op(
                    Inst::Call {
                        callee: shrink_then_return,
                        args: vec![v(0)],
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    // The fixed-slot witnesses: a constant's static length sizes a fixed
    // slot (for a map result, then for a call result sized by that constant
    // argument), but its header was shrunk first.
    let shrunk_const = |module: &mut Module, name: &str, step: Inst| {
        define(
            module,
            name,
            vec![],
            vec![Ty::I64],
            vec![block(
                0,
                &[],
                vec![
                    op(
                        Inst::Const {
                            ty: seq.clone(),
                            value: Constant::Sequence(vec![int(1), int(2), int(3)]),
                        },
                        0,
                    ),
                    eff(Inst::Call {
                        callee: shrink,
                        args: vec![v(0)],
                    }),
                    op(step, 1),
                    op(
                        Inst::Call {
                            callee: c_sum,
                            args: vec![v(1)],
                        },
                        2,
                    ),
                    ret(&[2]),
                ],
            )],
        );
    };
    shrunk_const(
        &mut module,
        "shrunk_const_map",
        Inst::SeqMapAddK {
            ty: seq.clone(),
            seq: v(0),
            k: 1,
        },
    );
    shrunk_const(
        &mut module,
        "shrunk_const_call",
        Inst::Call {
            callee: inc,
            args: vec![v(0)],
        },
    );
    module
}

const WITNESSES_DRIVER: &str = r#"
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

extern void *inc(const void *s, void *out);
extern void *map_then_shrink(const void *s, void *out);
extern void *forward_shrunk(const void *s, void *out);
extern int64_t shrunk_const_map(void);
extern int64_t shrunk_const_call(void);

static int shrink_enabled;

void shrink(void *s) {
    if (!shrink_enabled) return;
    uint64_t len = image_len(s);
    if (len) {
        len -= 1;
        memcpy(s, &len, 8);
    }
}

int64_t c_sum(const void *s) {
    int64_t sum = 0;
    uint64_t len = image_len(s);
    for (uint64_t i = 0; i < len; i++) {
        int32_t x; memcpy(&x, (const unsigned char *)s + 8 + 4 * i, 4);
        sum += x;
    }
    return sum;
}

static const int32_t in3[] = {1, 2, 3};
static const int32_t plus_one[] = {2, 3, 4};

static int case_bomb(void) {
    /* A header of 2^62 elements: (len + 2) * 4 wraps to 8 bytes. */
    unsigned char bomb[8 + 16] = {0};
    uint64_t len = (uint64_t)1 << 62;
    memcpy(bomb, &len, 8);
    inc(bomb, buffer_new(4, 4));
    return 0;
}
static int case_map_then_shrink(void) {
    map_then_shrink(image_new(3, 4, in3), buffer_new(3, 4));
    return 0;
}
static int case_forward_shrunk(void) {
    forward_shrunk(image_new(3, 4, in3), buffer_new(3, 4));
    return 0;
}
static int case_shrunk_const_map(void) { return (int)shrunk_const_map(); }
static int case_shrunk_const_call(void) { return (int)shrunk_const_call(); }

/* Run `body` in a child with `shrink` enabled: it must die of SIGTRAP (the
   backend's `brk`), not return, and not die of another signal. */
static int expect_trap(const char *what, int (*body)(void)) {
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) { printf("%s: fork failed\n", what); return 0; }
    if (pid == 0) {
        shrink_enabled = 1;
        int value = body();
        printf("%s: returned %d instead of trapping\n", what, value);
        fflush(stdout);
        _exit(0);
    }
    int status = 0;
    if (waitpid(pid, &status, 0) != pid) { printf("%s: waitpid failed\n", what); return 0; }
    if (WIFSIGNALED(status) && WTERMSIG(status) == SIGTRAP) return 1;
    if (WIFSIGNALED(status))
        printf("%s: child died of signal %d, expected SIGTRAP\n", what, WTERMSIG(status));
    else
        printf("%s: child exited %d, expected SIGTRAP\n", what, WEXITSTATUS(status));
    return 0;
}

int main(void) {
    /* Controls: with `shrink` disabled every function returns the model. */
    void *s = image_new(3, 4, in3);
    void *out = buffer_new(3, 4);
    if (map_then_shrink(s, out) != out
        || !image_equals("map_then_shrink control", out, 3, 4, plus_one)) return 1;
    free(out);
    out = buffer_new(3, 4);
    if (forward_shrunk(s, out) != out
        || !image_equals("forward_shrunk control", out, 3, 4, in3)) return 2;
    free(out);
    if (shrunk_const_map() != 9 || shrunk_const_call() != 9) {
        printf("controls %lld %lld, model 9 9\n", (long long)shrunk_const_map(),
               (long long)shrunk_const_call());
        return 3;
    }
    free(s);

    if (!expect_trap("header below 2^56", case_bomb)) return 10;
    if (!expect_trap("callee return length", case_map_then_shrink)) return 11;
    if (!expect_trap("caller post-call length", case_forward_shrunk)) return 12;
    if (!expect_trap("fixed map slot count", case_shrunk_const_map)) return 13;
    if (!expect_trap("fixed call-result slot count", case_shrunk_const_call)) return 14;
    return 0;
}
"#;

/// Every run-time length witness the ABI states fires, each in a forked child
/// that must die of SIGTRAP: the `< 2^56` header bound (a C caller's header
/// that would wrap the byte count), the callee's check that it returns its
/// published length, the caller's check of the returned header after the
/// call, and the check that a fixed slot's source has the static count the
/// slot was sized for (for a map result and for a call result). A C callee
/// that shrinks an image it was passed (which the ABI forbids) breaks each
/// witness; with it disabled the same functions return the C model.
#[test]
fn every_run_time_length_witness_traps_o0_through_o3() {
    run_native_at_every_level(
        "seq_witnesses",
        &build_witnesses(),
        &format!("{PRELUDE}{WITNESSES_DRIVER}"),
    );
}

// ---------------------------------------------------------------------------
// Replaceable callees publish no length
// ---------------------------------------------------------------------------

/// `make() -> seq<i32> = [1, 2, 3]` with `linkage`/`visibility`, and
/// `user() -> i64 { make(); 0 }`.
fn replaceable_callee(linkage: trust_ir::Linkage, visibility: trust_ir::Visibility) -> Module {
    let mut module = Module::new("seq_replaceable_callee");
    let seq = seq_of(&mut module, Ty::I32);
    let make = define(
        &mut module,
        "make",
        vec![],
        vec![seq.clone()],
        vec![block(
            0,
            &[],
            vec![
                op(
                    Inst::Const {
                        ty: seq.clone(),
                        value: Constant::Sequence(vec![int(1), int(2), int(3)]),
                    },
                    0,
                ),
                ret(&[0]),
            ],
        )],
    );
    module.functions[make.index() as usize].linkage = linkage;
    module.functions[make.index() as usize].visibility = visibility;
    define(
        &mut module,
        "user",
        vec![],
        vec![Ty::I64],
        vec![block(
            0,
            &[],
            vec![
                op(
                    Inst::Call {
                        callee: make,
                        args: vec![],
                    },
                    0,
                ),
                op(
                    Inst::Const {
                        ty: Ty::I64,
                        value: int(0),
                    },
                    1,
                ),
                ret(&[1]),
            ],
        )],
    );
    module
}

/// [`replaceable_callee`] plus `relay() -> seq<i32> { make() }`, a caller
/// whose own result shows the image `make` wrote into the buffer it sized.
fn replaceable_callee_with_relay(
    linkage: trust_ir::Linkage,
    visibility: trust_ir::Visibility,
) -> Module {
    let mut module = replaceable_callee(linkage, visibility);
    let make = module
        .function_by_name("make")
        .expect("fixture defines @make")
        .id;
    let seq = module.func_types[module.function_by_name("make").unwrap().ty.as_usize()].returns[0]
        .clone();
    define(
        &mut module,
        "relay",
        vec![],
        vec![seq],
        vec![block(
            0,
            &[],
            vec![
                op(
                    Inst::Call {
                        callee: make,
                        args: vec![],
                    },
                    0,
                ),
                ret(&[0]),
            ],
        )],
    );
    module
}

/// Compile `module` for the explicit AArch64 `triple` under
/// `relocation_model`, whatever the host, so each object format's
/// replacement rule is checked on every host.
fn try_compile_for(
    module: &Module,
    triple: &str,
    relocation_model: trust_cg_codegen::RelocationModel,
    opt_level: OptLevel,
) -> Result<(), String> {
    let mut module = module.clone();
    module.target_info = Some(trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    trust_cg_codegen::Compiler::new_for_target_spec(
        trust_cg_codegen::CompilerConfig {
            opt_level,
            relocation_model,
            ..trust_cg_codegen::CompilerConfig::default()
        },
        trust_cg_codegen::target::TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .map(|_| ())
    .map_err(|error| format!("{error:?}"))
}

/// The driver for a callee whose length is kept: `make` and `relay` write the
/// image `[1, 2, 3]` (checked against a C model and trust-ir's interpreter)
/// into the caller's buffer, and `user` returns 0. `C_MAKE` is replaced by
/// nothing, or by a strong C definition of `make` that the static link keeps
/// in place of the object's weak one.
const REPLACEABLE_DRIVER: &str = r#"
extern void *make(void *out);
extern void *relay(void *out);
extern int64_t user(void);
static const int32_t model[] = {1, 2, 3};
static const int32_t interp[] = INTERP_RELAY;
C_MAKE
int main(void) {
    void *out = buffer_new(3, sizeof(int32_t));
    if (make(out) != out) { printf("make: result is not the caller's buffer\n"); return 1; }
    if (!image_equals("make vs C model", out, 3, sizeof(int32_t), model)) return 2;
    free(out);
    out = buffer_new(3, sizeof(int32_t));
    if (relay(out) != out) { printf("relay: result is not the caller's buffer\n"); return 3; }
    if (!image_equals("relay vs C model", out, 3, sizeof(int32_t), model)) return 4;
    if (!image_equals("relay vs interpreter", out, 3, sizeof(int32_t), interp)) return 5;
    free(out);
    if (user() != 0) { printf("user: nonzero result\n"); return 6; }
    return 0;
}
"#;

/// An ODR-equivalent C definition of `make`: the same image, strong, so the
/// static link keeps it instead of the object's weak definition.
const C_ODR_MAKE: &str = r#"
void *make(void *out) {
    static const int32_t elems[] = {1, 2, 3};
    uint64_t len = 3;
    memcpy(out, &len, 8);
    memcpy((unsigned char *)out + 8, elems, sizeof elems);
    return out;
}
"#;

/// A caller sizes its result buffer from the callee's body, so a body another
/// object may replace grants no length, and a call to it is refused by name
/// (naming the callee, its linkage and its visibility):
///
/// * at static link, on every object format: `Weak`/`LinkOnce`, which a
///   strong definition elsewhere overrides;
/// * at Darwin load time: every default-visibility weak or link-once
///   definition, ODR or not, which dyld may coalesce with another image's;
/// * at ELF load time, under the shared-object relocation model (`pic`):
///   every default-visibility definition, which another shared object may
///   preempt.
///
/// `WeakOdr`/`LinkOnceOdr` promise equivalent definitions (trust-ir's
/// `Linkage::is_interposable` is false for them, as LLVM's is), so the static
/// link of an ELF executable (`static`, `pie`) may replace their body only
/// with an equivalent one: there, and for a hidden ODR definition under
/// `pic`, they keep their length, as do a strong definition on Darwin and a
/// hidden one under `pic`.
///
/// The targets are explicit, so every host checks both object formats. On an
/// AArch64 Linux GNU host the kept ELF ODR lengths also execute at O0-O3
/// against a C model and the interpreter, with the object's own `make` and
/// with an equivalent strong C `make` that the link prefers.
#[test]
fn calls_to_replaceable_sequence_returning_bodies_are_refused_by_name() {
    use trust_cg_codegen::RelocationModel;
    use trust_ir::{Linkage, Visibility};
    const DARWIN: &str = "aarch64-apple-darwin";
    const LINUX: &str = "aarch64-unknown-linux-gnu";
    let link_replaceable = |linkage: Linkage| matches!(linkage, Linkage::Weak | Linkage::LinkOnce);
    let weak_family = |linkage: Linkage| {
        matches!(
            linkage,
            Linkage::Weak | Linkage::LinkOnce | Linkage::WeakOdr | Linkage::LinkOnceOdr
        )
    };
    // What each (triple, model) does with the callee: keep its length,
    // refuse the call as replaceable, or refuse the definition's visibility
    // before any call is lowered (Mach-O spells hidden on an `External`
    // definition alone).
    #[derive(Debug, PartialEq)]
    enum Expect {
        Keeps,
        Replaceable,
        HiddenUnspelled,
    }
    let mut cases = 0;
    for linkage in [
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
        Linkage::External,
    ] {
        for visibility in [Visibility::Default, Visibility::Hidden] {
            let module = replaceable_callee(linkage, visibility);
            let default = visibility == Visibility::Default;
            let judge = |replaceable: bool| {
                if replaceable {
                    Expect::Replaceable
                } else {
                    Expect::Keeps
                }
            };
            let darwin = if !default && linkage != Linkage::External {
                Expect::HiddenUnspelled
            } else {
                judge(link_replaceable(linkage) || (default && weak_family(linkage)))
            };
            for (triple, model, expect) in [
                (DARWIN, RelocationModel::Static, darwin),
                (
                    LINUX,
                    RelocationModel::Static,
                    judge(link_replaceable(linkage)),
                ),
                (
                    LINUX,
                    RelocationModel::Pie,
                    judge(link_replaceable(linkage)),
                ),
                (
                    LINUX,
                    RelocationModel::Pic,
                    judge(link_replaceable(linkage) || default),
                ),
            ] {
                for opt in OPTS {
                    let tag =
                        format!("{linkage:?} {visibility:?} callee, {triple} {model:?} {opt:?}");
                    let result = try_compile_for(&module, triple, model, opt);
                    let needles = match expect {
                        Expect::Keeps => {
                            result
                                .unwrap_or_else(|error| panic!("{tag}: keeps its length: {error}"));
                            cases += 1;
                            continue;
                        }
                        Expect::Replaceable => vec![
                            "[TCG-SEQ]".to_string(),
                            "a call to `make`".to_string(),
                            format!("replaceable ({linkage:?} linkage, {visibility:?} visibility"),
                        ],
                        Expect::HiddenUnspelled => vec![
                            "function: \"make\", facet: \"visibility\", value: \"hidden\""
                                .to_string(),
                        ],
                    };
                    let error = result
                        .err()
                        .unwrap_or_else(|| panic!("{tag}: must be refused ({expect:?})"));
                    for needle in needles {
                        assert!(
                            error.contains(&needle),
                            "{tag}: refusal must name `{needle}`, got: {error}"
                        );
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 5 * 2 * 4 * OPTS.len());

    if cfg!(all(
        target_arch = "aarch64",
        target_os = "linux",
        target_env = "gnu"
    )) {
        for linkage in [Linkage::WeakOdr, Linkage::LinkOnceOdr] {
            let module = replaceable_callee_with_relay(linkage, Visibility::Default);
            let interp = interpret_collection(&module, "relay", vec![]);
            assert_eq!(interp, [1, 2, 3].map(Elem::Int).to_vec());
            let driver =
                format!("{PRELUDE}{REPLACEABLE_DRIVER}").replace("INTERP_RELAY", &c_array(&interp));
            run_native_at_every_level(
                &format!("seq_odr_{linkage:?}"),
                &module,
                &driver.replace("C_MAKE", ""),
            );
            run_native_at_every_level(
                &format!("seq_odr_{linkage:?}_c_make"),
                &module,
                &driver.replace("C_MAKE", C_ODR_MAKE),
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so no
/// sequence refusal asserted here is the license's refusal in disguise.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
