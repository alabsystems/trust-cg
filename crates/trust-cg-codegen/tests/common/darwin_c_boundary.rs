// Copyright 2026 Andrew Yates | Apache-2.0
//! Signature-driven DarwinPCS C-boundary oracle for native `aarch64-apple-darwin`
//! link-and-run twins of the Linux L01 suites.
//!
//! A corpus is a list of C signatures over scalars and `repr(C)` aggregates.
//! For every signature the helper emits:
//!
//! * `c_take_N`, an Apple clang function with that C signature (or a variadic
//!   one that reads its anonymous tail with `va_arg` through Apple's `char *`
//!   `va_list`) returning an order-sensitive 64-bit digest of every argument
//!   bit;
//! * `cg_take_N`, the same digest as a TrustCG definition, which the clang
//!   driver calls (C caller -> CG callee; non-variadic signatures only, since
//!   TrustCG refuses variadic definitions);
//! * `cg_send_N(const unsigned char *slots)`, a TrustCG caller that loads each
//!   argument from its own 32-byte slot and calls `c_take_N` (CG caller -> C
//!   callee), applying C's default argument promotions to anonymous arguments
//!   explicitly, as a C producer does. A `bool` or integer narrower than 64
//!   bits arrives as a 64-bit carrier with garbage above its width and is
//!   truncated in the caller. The AArch64 `Trunc` lowering (UXTB/UXTH, a
//!   W-register move, `AND #1` for `bool`) already clears every bit above the
//!   width, so the value reaches the call zero-extended: the corpus's
//!   `i8`/`i16` values, all negative, make the clang callee's reliance on
//!   Apple's caller-side SIGN extension to 32 bits observable, while caller
//!   zero extension of `bool`/`u8`/`u16` already holds before the boundary and
//!   is not independently exercised.
//!
//! The expected digest is computed here, in Rust, from the same values the
//! driver passes, so the clang-to-clang call is checked too and none of the
//! three results depends on another. The driver prints the number of checks it
//! executed and the caller requires the exact count. Placement is never
//! computed here: Apple clang decides it on both sides of the boundary.
//! This is execution evidence on one host, not an ABI proof.

#![allow(dead_code)]

// Exposed so a twin that loads this helper reuses them instead of loading the
// same files a second time (clippy::duplicate_mod).
#[path = "rosetta.rs"]
pub mod process;

#[path = "fresh_dir.rs"]
pub mod fresh_dir;

use std::fmt::Write as _;
use std::fs;
use std::process::Command;
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_ir::{
    BinOp, CastOp, Endianness, FieldDef, FuncId, Module, StructDef, StructId, StructPassingPolicy,
    StructRepr, TargetInfo, Ty, ValueId,
};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, validate_module};

/// The only triple this oracle compiles for.
pub const TRIPLE: &str = "aarch64-apple-darwin";
/// Every optimization level the twins execute.
pub const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

const DIGEST_SEED: u64 = 0x6a09_e667_f3bc_c909;
const DIGEST_PRIME: u64 = 0x0000_0100_0000_01b3;
/// Bytes per argument slot handed to a `cg_send_N` caller.
const SLOT: u64 = 32;

/// Trust IR target description for DarwinPCS with native C struct passing.
pub fn target_info() -> TargetInfo {
    TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// A C scalar argument type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scalar {
    Bool,
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    I128,
    F32,
    F64,
}

impl Scalar {
    pub fn ty(self) -> Ty {
        match self {
            Scalar::Bool => Ty::Bool,
            Scalar::U8 => Ty::U8,
            Scalar::I8 => Ty::I8,
            Scalar::U16 => Ty::U16,
            Scalar::I16 => Ty::I16,
            Scalar::U32 => Ty::U32,
            Scalar::I32 => Ty::I32,
            Scalar::U64 => Ty::U64,
            Scalar::I64 => Ty::I64,
            Scalar::I128 => Ty::I128,
            Scalar::F32 => Ty::F32,
            Scalar::F64 => Ty::F64,
        }
    }

    pub fn c(self) -> &'static str {
        match self {
            Scalar::Bool => "bool",
            Scalar::U8 => "uint8_t",
            Scalar::I8 => "int8_t",
            Scalar::U16 => "uint16_t",
            Scalar::I16 => "int16_t",
            Scalar::U32 => "uint32_t",
            Scalar::I32 => "int32_t",
            Scalar::U64 => "uint64_t",
            Scalar::I64 => "int64_t",
            Scalar::I128 => "__int128",
            Scalar::F32 => "float",
            Scalar::F64 => "double",
        }
    }

    /// C size and alignment on arm64 Darwin (`__int128` is 16-aligned).
    pub fn size_align(self) -> (u64, u64) {
        match self {
            Scalar::Bool | Scalar::U8 | Scalar::I8 => (1, 1),
            Scalar::U16 | Scalar::I16 => (2, 2),
            Scalar::U32 | Scalar::I32 | Scalar::F32 => (4, 4),
            Scalar::U64 | Scalar::I64 | Scalar::F64 => (8, 8),
            Scalar::I128 => (16, 16),
        }
    }

    /// Bit width of a scalar narrower than 64 bits whose register image a
    /// caller must extend (DarwinPCS: to 32 bits, by the caller). `Bool` is the
    /// one-bit carrier trust-ir truncates to.
    pub fn narrow_bits(self) -> Option<u32> {
        match self {
            Scalar::Bool => Some(1),
            Scalar::U8 | Scalar::I8 => Some(8),
            Scalar::U16 | Scalar::I16 => Some(16),
            Scalar::U32 | Scalar::I32 => Some(32),
            _ => None,
        }
    }

    /// C's default argument promotion for an anonymous argument: the promoted
    /// scalar, the Trust IR cast a producer emits, and the C type `va_arg`
    /// reads.
    fn promotion(self) -> Option<(Scalar, CastOp, &'static str)> {
        match self {
            Scalar::Bool | Scalar::U8 | Scalar::U16 => Some((Scalar::I32, CastOp::ZExt, "int")),
            Scalar::I8 | Scalar::I16 => Some((Scalar::I32, CastOp::SExt, "int")),
            Scalar::F32 => Some((Scalar::F64, CastOp::FPExt, "double")),
            _ => None,
        }
    }
}

/// A C argument: a scalar or an aggregate registered with the corpus.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arg {
    S(Scalar),
    A(usize),
}

struct Aggregate {
    name: String,
    fields: Vec<Scalar>,
    offsets: Vec<u64>,
    size: u64,
    align: u64,
    id: StructId,
}

/// One literal value: its C spelling, the digest components it contributes
/// and (for scalars) its Trust IR type.
struct Value {
    c: String,
    components: Vec<u64>,
}

/// A compiled-and-linked fixture: the module, its C driver and the exact
/// number of checks the driver must report.
pub struct Fixture {
    pub name: String,
    pub module: Module,
    pub driver: String,
    pub checks: usize,
    pub cases: usize,
}

/// A corpus under construction.
pub struct Corpus {
    name: String,
    builder: ModuleBuilder,
    aggregates: Vec<Aggregate>,
    c_types: String,
    c_functions: String,
    c_checks: String,
    counter: u64,
    cases: usize,
    checks: usize,
}

fn align_up(value: u64, align: u64) -> u64 {
    value.div_ceil(align) * align
}

fn mix(acc: u64, component: u64) -> u64 {
    (acc ^ component).wrapping_mul(DIGEST_PRIME)
}

impl Corpus {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.into(),
            builder: ModuleBuilder::new_with_target_info(name, target_info()),
            aggregates: Vec::new(),
            c_types: String::new(),
            c_functions: String::new(),
            c_checks: String::new(),
            counter: 0,
            cases: 0,
            checks: 0,
        }
    }

    /// Register `typedef struct { fields } name;` with its C layout (natural
    /// alignment, no packing), cross-checked by `_Static_assert`s in the
    /// driver against the declared Trust IR layout.
    pub fn aggregate(&mut self, name: &str, fields: &[Scalar]) -> Arg {
        assert!(!fields.is_empty(), "{name}: empty aggregates are not C");
        let mut offsets = Vec::with_capacity(fields.len());
        let mut end = 0;
        let mut align = 1;
        for field in fields {
            let (size, field_align) = field.size_align();
            let offset = align_up(end, field_align);
            offsets.push(offset);
            end = offset + size;
            align = align.max(field_align);
        }
        let size = align_up(end, align);
        let id = StructId::new(self.aggregates.len() as u32);
        let struct_id = self.builder.add_struct(StructDef {
            origin: None,
            id,
            name: name.into(),
            fields: fields
                .iter()
                .zip(&offsets)
                .enumerate()
                .map(|(index, (field, offset))| FieldDef {
                    name: format!("f{index}"),
                    ty: field.ty(),
                    offset: Some(*offset),
                })
                .collect(),
            size: Some(size),
            align: Some(align),
            repr: StructRepr::C,
        });
        assert_eq!(struct_id, id);
        let members = fields
            .iter()
            .enumerate()
            .map(|(index, field)| format!("{} f{index};", field.c()))
            .collect::<Vec<_>>()
            .join(" ");
        writeln!(self.c_types, "typedef struct {{ {members} }} {name};").unwrap();
        writeln!(
            self.c_types,
            "_Static_assert(sizeof({name})=={size} && _Alignof({name})=={align}, \"{name} layout\");"
        )
        .unwrap();
        for (index, offset) in offsets.iter().enumerate() {
            writeln!(
                self.c_types,
                "_Static_assert(offsetof({name},f{index})=={offset}, \"{name}.f{index}\");"
            )
            .unwrap();
        }
        self.aggregates.push(Aggregate {
            name: name.into(),
            fields: fields.to_vec(),
            offsets,
            size,
            align,
            id,
        });
        Arg::A(self.aggregates.len() - 1)
    }

    pub fn ty(&self, arg: Arg) -> Ty {
        match arg {
            Arg::S(scalar) => scalar.ty(),
            Arg::A(index) => Ty::Struct(self.aggregates[index].id),
        }
    }

    fn c_type(&self, arg: Arg) -> String {
        match arg {
            Arg::S(scalar) => scalar.c().into(),
            Arg::A(index) => self.aggregates[index].name.clone(),
        }
    }

    fn size_align(&self, arg: Arg) -> (u64, u64) {
        match arg {
            Arg::S(scalar) => scalar.size_align(),
            Arg::A(index) => (self.aggregates[index].size, self.aggregates[index].align),
        }
    }

    /// A deterministic scalar value exercising sign bits and full widths.
    fn scalar_value(&mut self, scalar: Scalar) -> Value {
        let k = self.counter;
        self.counter += 1;
        match scalar {
            Scalar::Bool => {
                let value = (k * 7 + 3) % 5 < 3;
                Value {
                    c: if value { "true" } else { "false" }.into(),
                    components: vec![u64::from(value)],
                }
            }
            Scalar::U8 => {
                let value = 0x80 | ((k * 37 + 11) & 0x7f);
                Value {
                    c: format!("(uint8_t)0x{value:x}"),
                    components: vec![value],
                }
            }
            Scalar::I8 => {
                let value = -(((k * 13 + 5) % 127) as i64) - 1;
                Value {
                    c: format!("(int8_t)({value})"),
                    components: vec![value as u64],
                }
            }
            Scalar::U16 => {
                let value = 0x8000 | ((k * 4099 + 7) & 0x7fff);
                Value {
                    c: format!("(uint16_t)0x{value:x}"),
                    components: vec![value],
                }
            }
            Scalar::I16 => {
                let value = -(((k * 997 + 3) % 32767) as i64) - 1;
                Value {
                    c: format!("(int16_t)({value})"),
                    components: vec![value as u64],
                }
            }
            Scalar::U32 => {
                let value =
                    0x8000_0000 | (k.wrapping_mul(2_654_435_761).wrapping_add(17) & 0x7fff_ffff);
                Value {
                    c: format!("(uint32_t)0x{value:x}u"),
                    components: vec![value],
                }
            }
            Scalar::I32 => {
                let value =
                    -((k.wrapping_mul(7919 * 104_729).wrapping_add(1) % 2_000_000_000) as i64) - 1;
                Value {
                    c: format!("(int32_t)({value})"),
                    components: vec![value as u64],
                }
            }
            Scalar::U64 => {
                let value = 0x9e37_79b9_7f4a_7c15_u64.wrapping_mul(k + 1) | (1 << 63);
                Value {
                    c: format!("UINT64_C(0x{value:x})"),
                    components: vec![value],
                }
            }
            Scalar::I64 => {
                let value = -((0x1234_5678_9abc_def1_u64.wrapping_mul(k + 3) >> 2) as i64);
                Value {
                    c: format!("INT64_C({value})"),
                    components: vec![value as u64],
                }
            }
            Scalar::I128 => {
                let high =
                    -(((k + 1).wrapping_mul(0x0123_4567_89ab_cdef) % 0x7fff_ffff_ffff) as i64) - 1;
                let low = 0xfedc_ba98_7654_3210_u64 ^ k.wrapping_mul(0x0101_0101);
                Value {
                    c: format!(
                        "(((__int128)INT64_C({high}) << 64) | (__int128)UINT64_C(0x{low:x}))"
                    ),
                    components: vec![low, high as u64],
                }
            }
            Scalar::F32 => {
                let sign = if k.is_multiple_of(2) { -1.0 } else { 1.0 };
                let value = sign * ((k % 97) as f32 * 1.625 + 0.3);
                Value {
                    c: format!("{value:?}f"),
                    components: vec![u64::from(value.to_bits())],
                }
            }
            Scalar::F64 => {
                let sign = if k % 2 == 1 { -1.0 } else { 1.0 };
                let value = sign * (k as f64 * std::f64::consts::PI + 0.0001);
                Value {
                    c: format!("{value:?}"),
                    components: vec![value.to_bits()],
                }
            }
        }
    }

    fn value(&mut self, arg: Arg) -> Value {
        match arg {
            Arg::S(scalar) => self.scalar_value(scalar),
            Arg::A(index) => {
                let fields = self.aggregates[index].fields.clone();
                let name = self.aggregates[index].name.clone();
                let values: Vec<_> = fields.iter().map(|f| self.scalar_value(*f)).collect();
                Value {
                    c: format!(
                        "(({name}){{{}}})",
                        values
                            .iter()
                            .map(|v| v.c.clone())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    components: values.into_iter().flat_map(|v| v.components).collect(),
                }
            }
        }
    }

    /// C expression list folding the digest components of `name` (a variable
    /// of `arg`'s C type) into `acc`.
    fn c_digest(&self, arg: Arg, name: &str, out: &mut String) {
        let scalar = |scalar: Scalar, name: &str, out: &mut String| {
            match scalar {
            Scalar::Bool
            | Scalar::U8
            | Scalar::U16
            | Scalar::U32
            | Scalar::U64 => writeln!(out, "acc = mix(acc, (uint64_t){name});").unwrap(),
            Scalar::I8 | Scalar::I16 | Scalar::I32 | Scalar::I64 => {
                writeln!(out, "acc = mix(acc, (uint64_t)(int64_t){name});").unwrap()
            }
            Scalar::I128 => writeln!(
                out,
                "acc = mix(acc, (uint64_t){name}); acc = mix(acc, (uint64_t)((unsigned __int128){name} >> 64));"
            )
            .unwrap(),
            Scalar::F32 => {
                writeln!(out, "acc = mix(acc, (uint64_t)f32_bits({name}));").unwrap()
            }
            Scalar::F64 => writeln!(out, "acc = mix(acc, f64_bits({name}));").unwrap(),
        }
        };
        match arg {
            Arg::S(s) => scalar(s, name, out),
            Arg::A(index) => {
                for (field_index, field) in self.aggregates[index].fields.iter().enumerate() {
                    scalar(*field, &format!("{name}.f{field_index}"), out);
                }
            }
        }
    }

    /// A non-variadic signature, checked in both directions.
    pub fn case(&mut self, label: &str, params: &[Arg]) {
        self.add(label, params, None);
    }

    /// A variadic C callee `c_take_N(params[..fixed], ...)` called by a
    /// TrustCG caller (CG caller -> C callee only: TrustCG refuses variadic
    /// definitions, see `[TCG-VARIADIC-DEFINITION]`).
    pub fn variadic_case(&mut self, label: &str, params: &[Arg], fixed: usize) {
        assert!(
            fixed >= 1 && fixed <= params.len(),
            "{label}: C needs a named argument"
        );
        self.add(label, params, Some(fixed));
    }

    fn add(&mut self, label: &str, params: &[Arg], fixed: Option<usize>) {
        let n = self.cases;
        self.cases += 1;
        let values: Vec<Value> = params.iter().map(|arg| self.value(*arg)).collect();
        let expected = values
            .iter()
            .flat_map(|v| v.components.iter())
            .fold(DIGEST_SEED, |acc, c| mix(acc, *c));

        // --- C callee (the oracle's callee) --------------------------------
        let named = fixed.unwrap_or(params.len());
        let declaration = params[..named]
            .iter()
            .enumerate()
            .map(|(i, arg)| format!("{} a{i}", self.c_type(*arg)))
            .collect::<Vec<_>>()
            .join(", ");
        let ellipsis = if fixed.is_some() { ", ..." } else { "" };
        writeln!(
            self.c_functions,
            "/* {n}: {label} */\n__attribute__((noinline)) uint64_t c_take_{n}({declaration}{ellipsis}) {{"
        )
        .unwrap();
        if fixed.is_some() {
            writeln!(
                self.c_functions,
                "va_list ap; va_start(ap, a{});",
                named - 1
            )
            .unwrap();
            for (i, arg) in params.iter().enumerate().skip(named) {
                let c_type = self.c_type(*arg);
                let read = match arg {
                    Arg::S(scalar) => match scalar.promotion() {
                        Some((_, _, promoted)) => format!("({c_type})va_arg(ap, {promoted})"),
                        None => format!("va_arg(ap, {c_type})"),
                    },
                    Arg::A(_) => format!("va_arg(ap, {c_type})"),
                };
                writeln!(self.c_functions, "{c_type} a{i} = {read};").unwrap();
            }
            writeln!(self.c_functions, "va_end(ap);").unwrap();
        }
        writeln!(
            self.c_functions,
            "uint64_t acc = UINT64_C(0x{DIGEST_SEED:x});"
        )
        .unwrap();
        let mut body = String::new();
        for (i, arg) in params.iter().enumerate() {
            self.c_digest(*arg, &format!("a{i}"), &mut body);
        }
        self.c_functions.push_str(&body);
        writeln!(self.c_functions, "return acc;\n}}").unwrap();

        // --- Trust IR: the external C callee and the two CG functions ------
        let named_tys: Vec<Ty> = params[..named].iter().map(|arg| self.ty(*arg)).collect();
        let callee_sig = if fixed.is_some() {
            self.builder
                .add_vararg_func_type(named_tys.clone(), vec![Ty::U64])
        } else {
            self.builder.add_func_type(named_tys.clone(), vec![Ty::U64])
        };
        let callee: FuncId = self
            .builder
            .declare_function(format!("c_take_{n}"), callee_sig);

        if fixed.is_none() {
            let tys: Vec<Ty> = params.iter().map(|arg| self.ty(*arg)).collect();
            let sig = self.builder.add_func_type(tys.clone(), vec![Ty::U64]);
            let aggregates_view = self.view();
            let mut f = self.builder.function(format!("cg_take_{n}"), sig);
            let entry = f.create_block();
            let args: Vec<ValueId> = tys
                .into_iter()
                .map(|ty| f.add_block_param(entry, ty))
                .collect();
            f.switch_to_block(entry);
            let mut acc = f.iconst(Ty::U64, i128::from(DIGEST_SEED));
            for (arg, value) in params.iter().zip(args) {
                acc = aggregates_view.cg_digest(&mut f, *arg, value, acc);
            }
            f.ret(vec![acc]);
            f.build();
        }

        let send_sig = self.builder.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let view = self.view();
        let mut f = self.builder.function(format!("cg_send_{n}"), send_sig);
        let entry = f.create_block();
        let slots = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let mut call_args = Vec::with_capacity(params.len());
        for (i, arg) in params.iter().enumerate() {
            let pointer = f.gep_byte_offset(slots, SLOT * i as u64);
            let (_, align) = view.size_align(*arg);
            // A narrow scalar arrives as a 64-bit carrier with garbage above
            // its width and is truncated here. `Trunc` leaves the value
            // zero-extended, so a negative `i8`/`i16` needs the caller's sign
            // extension to 32 bits that the Apple clang callee relies on; the
            // unsigned and `bool` cases are already clean before the boundary.
            let loaded = match arg {
                Arg::S(scalar) if scalar.narrow_bits().is_some() => {
                    let carrier = f.load_aligned(Ty::U64, pointer, 8);
                    f.cast(CastOp::Trunc, Ty::U64, scalar.ty(), carrier)
                }
                _ => f.load_aligned(view.ty(*arg), pointer, align),
            };
            let passed = match (arg, fixed) {
                (Arg::S(scalar), Some(fixed)) if i >= fixed => match scalar.promotion() {
                    Some((promoted, op, _)) => f.cast(op, scalar.ty(), promoted.ty(), loaded),
                    None => loaded,
                },
                _ => loaded,
            };
            call_args.push(passed);
        }
        let result = f.call(callee, call_args);
        f.ret(vec![result]);
        f.build();

        // --- driver checks --------------------------------------------------
        let literals: Vec<String> = values.iter().map(|v| v.c.clone()).collect();
        let c_label = label.replace('"', "'");
        writeln!(self.c_checks, "{{ /* {n}: {c_label} */").unwrap();
        writeln!(
            self.c_checks,
            "  const uint64_t expected = UINT64_C(0x{expected:x});"
        )
        .unwrap();
        writeln!(
            self.c_checks,
            "  check(\"C->C {c_label}\", {n}, c_take_{n}({}), expected);",
            literals.join(", ")
        )
        .unwrap();
        self.checks += 1;
        if fixed.is_none() {
            writeln!(
                self.c_checks,
                "  check(\"C->CG {c_label}\", {n}, cg_take_{n}({}), expected);",
                literals.join(", ")
            )
            .unwrap();
            self.checks += 1;
        }
        writeln!(self.c_checks, "  memset(slots, 0xa5, sizeof slots);").unwrap();
        for (i, ((arg, literal), value)) in params.iter().zip(&literals).zip(&values).enumerate() {
            let offset = SLOT * i as u64;
            match arg {
                Arg::S(scalar) if scalar.narrow_bits().is_some() => {
                    let bits = scalar.narrow_bits().unwrap_or(64);
                    let mask = (1_u64 << bits) - 1;
                    let garbage = 0xdead_beef_5a5a_c3c3_u64.rotate_left(i as u32 * 7 + n as u32);
                    let carrier = (garbage & !mask) | (value.components[0] & mask);
                    writeln!(
                        self.c_checks,
                        "  {{ uint64_t v = UINT64_C(0x{carrier:x}); memcpy(slots + {offset}, &v, 8); }}"
                    )
                    .unwrap();
                }
                _ => writeln!(
                    self.c_checks,
                    "  {{ {} v = {literal}; memcpy(slots + {offset}, &v, sizeof v); }}",
                    self.c_type(*arg)
                )
                .unwrap(),
            }
        }
        writeln!(
            self.c_checks,
            "  check(\"CG->C {c_label}\", {n}, cg_send_{n}(slots), expected);\n}}"
        )
        .unwrap();
        self.checks += 1;
        let send_decl = if fixed.is_none() {
            let all = params
                .iter()
                .map(|arg| self.c_type(*arg))
                .collect::<Vec<_>>()
                .join(", ");
            format!("extern uint64_t cg_take_{n}({all});\n")
        } else {
            String::new()
        };
        writeln!(
            self.c_functions,
            "{send_decl}extern uint64_t cg_send_{n}(const unsigned char *);"
        )
        .unwrap();
        let max_slots = params.len() as u64 * SLOT;
        assert!(
            max_slots <= 64 * SLOT,
            "{label}: too many arguments for the slot buffer"
        );
    }

    /// A layout-only view used while the builder is mutably borrowed.
    fn view(&self) -> View {
        View {
            aggregates: self
                .aggregates
                .iter()
                .map(|a| (a.id, a.fields.clone(), a.size, a.align))
                .collect(),
        }
    }

    pub fn finish(self) -> Fixture {
        let module = self
            .builder
            .build()
            .expect("ModuleBuilder::build: test fixture");
        let errors = validate_module(&module);
        assert!(
            errors.is_empty(),
            "{}: invalid Trust IR: {errors:?}",
            self.name
        );
        let mut driver = String::from(
            "#include <stdint.h>\n#include <stdbool.h>\n#include <stddef.h>\n#include <stdio.h>\n\
             #include <string.h>\n#include <stdarg.h>\n",
        );
        driver.push_str(&self.c_types);
        writeln!(
            driver,
            "static inline uint64_t mix(uint64_t acc, uint64_t c) {{ return (acc ^ c) * UINT64_C(0x{DIGEST_PRIME:x}); }}\n\
             static inline uint32_t f32_bits(float x) {{ uint32_t b; memcpy(&b, &x, 4); return b; }}\n\
             static inline uint64_t f64_bits(double x) {{ uint64_t b; memcpy(&b, &x, 8); return b; }}\n\
             static unsigned passed, failed;\n\
             static void check(const char *what, unsigned n, uint64_t actual, uint64_t expected) {{\n\
               if (actual == expected) {{ passed++; return; }}\n\
               failed++; printf(\"FAIL %s (case %u): actual=%016llx expected=%016llx\\n\", what, n,\n\
                 (unsigned long long)actual, (unsigned long long)expected);\n}}"
        )
        .unwrap();
        driver.push_str(&self.c_functions);
        writeln!(
            driver,
            "int main(void) {{\n  static unsigned char slots[{}] __attribute__((aligned(16)));\n{}  printf(\"PASS %u of %u checks over {} signatures\\n\", passed, passed + failed);\n  return failed != 0;\n}}",
            64 * SLOT,
            self.c_checks,
            self.cases
        )
        .unwrap();
        Fixture {
            name: self.name,
            module,
            driver,
            checks: self.checks,
            cases: self.cases,
        }
    }
}

struct View {
    aggregates: Vec<(StructId, Vec<Scalar>, u64, u64)>,
}

impl View {
    fn ty(&self, arg: Arg) -> Ty {
        match arg {
            Arg::S(scalar) => scalar.ty(),
            Arg::A(index) => Ty::Struct(self.aggregates[index].0),
        }
    }

    fn size_align(&self, arg: Arg) -> (u64, u64) {
        match arg {
            Arg::S(scalar) => scalar.size_align(),
            Arg::A(index) => (self.aggregates[index].2, self.aggregates[index].3),
        }
    }

    fn cg_digest(
        &self,
        f: &mut FunctionBuilder<'_>,
        arg: Arg,
        value: ValueId,
        acc: ValueId,
    ) -> ValueId {
        let mut acc = acc;
        let mut components = Vec::new();
        match arg {
            Arg::S(scalar) => components.push((scalar, value)),
            Arg::A(index) => {
                // trust-ir's `ExtractField { ty }` is the RESULT (lane) type.
                for (field_index, field) in self.aggregates[index].1.iter().enumerate() {
                    let member = f.extract_field(field.ty(), value, field_index as u32);
                    components.push((*field, member));
                }
            }
        }
        for (scalar, value) in components {
            for component in scalar_components(f, scalar, value) {
                let mixed = f.binop(BinOp::Xor, Ty::U64, acc, component);
                let prime = f.iconst(Ty::U64, i128::from(DIGEST_PRIME));
                acc = f.binop(BinOp::Mul, Ty::U64, mixed, prime);
            }
        }
        acc
    }
}

/// The U64 digest components of one scalar, in the order `c_digest` folds them.
fn scalar_components(f: &mut FunctionBuilder<'_>, scalar: Scalar, value: ValueId) -> Vec<ValueId> {
    match scalar {
        Scalar::Bool | Scalar::U8 | Scalar::U16 | Scalar::U32 => {
            vec![f.cast(CastOp::ZExt, scalar.ty(), Ty::U64, value)]
        }
        Scalar::U64 => vec![value],
        Scalar::I8 | Scalar::I16 | Scalar::I32 => {
            let widened = f.cast(CastOp::SExt, scalar.ty(), Ty::I64, value);
            vec![f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, widened)]
        }
        Scalar::I64 => vec![f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, value)],
        Scalar::I128 => {
            let low = f.cast(CastOp::Trunc, Ty::I128, Ty::I64, value);
            let low = f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, low);
            let shift = f.iconst(Ty::I128, 64);
            let high = f.binop(BinOp::LShr, Ty::I128, value, shift);
            let high = f.cast(CastOp::Trunc, Ty::I128, Ty::I64, high);
            let high = f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, high);
            vec![low, high]
        }
        Scalar::F32 => {
            let bits = f.cast(CastOp::Bitcast, Ty::F32, Ty::U32, value);
            vec![f.cast(CastOp::ZExt, Ty::U32, Ty::U64, bits)]
        }
        Scalar::F64 => vec![f.cast(CastOp::Bitcast, Ty::F64, Ty::U64, value)],
    }
}

/// Compile `module` for DarwinPCS at `level` into a Mach-O object, or the
/// compiler's refusal.
///
/// The fixtures are hand-built and carry no codegen license (`body_gate:
/// None`), which trust-cg REFUSES by default (roadmap WS7.5, decision gate
/// DG-73). This compile states `Permit` explicitly, so no fixture passes, or
/// is refused, because the license silently refused it.
pub fn compile(module: &Module, level: OptLevel) -> Result<Vec<u8>, String> {
    let output = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).expect("Darwin triple parses"),
    )
    .with_codegen_license(
        trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
    .compile(module)
    .map_err(|error| format!("{error} ({error:?})"))?;
    assert_eq!(
        &output.object_code[..4],
        &[0xcf, 0xfa, 0xed, 0xfe],
        "DarwinPCS output must be a Mach-O object"
    );
    Ok(output.object_code)
}

/// Compile the fixture at O0-O3, link each object with its driver through the
/// host Apple clang (`cc -O2`, so the C side is optimized and trusts the ABI's
/// extension and placement guarantees), run it, and require the exact check
/// count. Returns the number of checks executed across the four levels.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
pub fn run_native(fixture: &Fixture) -> usize {
    let dir = fresh_dir::create(&format!("trust-cg-darwin-{}-", fixture.name));
    let driver = dir.join("driver.c");
    fs::write(&driver, &fixture.driver).unwrap();
    fs::write(
        dir.join("module.ir-debug"),
        format!("{:#?}", fixture.module),
    )
    .unwrap();
    let mut executed = 0;
    for level in LEVELS {
        let object = compile(&fixture.module, level).unwrap_or_else(|error| {
            panic!(
                "{} {level:?}: {error}; retained {}",
                fixture.name,
                dir.display()
            )
        });
        let object_path = dir.join(format!("{level:?}.o"));
        let binary = dir.join(format!("{level:?}"));
        fs::write(&object_path, object).unwrap();
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .args(["-O2", "-fno-inline"])
                .arg(&driver)
                .arg(&object_path)
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .expect("the host Apple clang is required");
        assert!(
            !link.timed_out && link.output.status.success(),
            "{} {level:?} link: {}; retained {}",
            fixture.name,
            String::from_utf8_lossy(&link.output.stderr),
            dir.display()
        );
        let run = process::run_executable_with_timeout(&binary, process::codegen_run_timeout())
            .expect("run the linked driver");
        let stdout = String::from_utf8_lossy(&run.output.stdout);
        assert!(
            !run.timed_out && run.output.status.success(),
            "{} {level:?}: status={} stdout={stdout} stderr={}; retained {}",
            fixture.name,
            run.output.status,
            String::from_utf8_lossy(&run.output.stderr),
            dir.display()
        );
        let expected = format!(
            "PASS {0} of {0} checks over {1} signatures",
            fixture.checks, fixture.cases
        );
        assert_eq!(
            stdout.trim(),
            expected,
            "{} {level:?}: incomplete native execution; retained {}",
            fixture.name,
            dir.display()
        );
        executed += fixture.checks;
    }
    fs::remove_dir_all(&dir).unwrap();
    executed
}
