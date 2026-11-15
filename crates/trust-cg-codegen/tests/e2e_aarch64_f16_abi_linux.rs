// Copyright 2026 Andrew Yates | Apache-2.0
//! L01-P7: scalar `f16` and `f16` homogeneous floating-point aggregate (HFA)
//! argument and return boundaries on aarch64-unknown-linux-gnu, executed
//! natively in both directions against a C oracle that uses `_Float16`.
//!
//! Corpus (`shapes`): every CG callee `cg_<shape>` records each argument
//! (every HFA member separately) into its own eight-byte slot of a
//! sentinel-filled record and returns one designated argument; every CG
//! caller `cg_call_<shape>` loads the same arguments from an input record,
//! calls the C callee `c_<shape>`, which records them, and records what it
//! returns. Neither side performs `f16` arithmetic, so NaN payloads (quiet
//! and signalling, either sign), signed zeros, subnormals and infinities must
//! cross every boundary bit for bit. The shapes cover twelve `f16` arguments
//! (four on the stack); `f16` interleaved with `f32`, `f64` and 8/16/32/64-bit
//! integers until both register banks are exhausted; HFAs of one to four
//! `f16` members exactly filling the remaining H registers, one register
//! short, and after all eight are taken, each followed by an `f16`, an `f16`
//! HFA and an `int` (no backfill of a skipped H register); and HFA returns
//! arriving in registers, from the stack and permuted.
//!
//! Placement (`aapcs64_placement`) is an independent model of the Arm IHI
//! 0055 parameter-passing rules for exactly these types, written without the
//! lowering's classifier: `f16`/`f32`/`f64` take the next SIMD&FP register,
//! an HFA takes consecutive registers only if all are free and otherwise goes
//! to the stack with the NSRN set to 8, and a stack argument starts at a
//! multiple of 8 and occupies a multiple of 8 bytes (a half-precision or
//! narrow integer argument a full 8-byte slot, an HFA its size rounded up).
//! The object rows decode the Linux ELF objects with the `trust-cg-lift`
//! decoder (not the compiler's emitter) and require, per function and opt
//! level, that each register argument's first read (callee) or last write
//! before the call (caller) is a 16-bit H transfer or a full-register copy
//! for `f16` (S/D-sized for `f32`/`f64`), that each stack-passed `f16` is
//! stored and loaded by a 16-bit H-register transfer at exactly the modelled
//! offset, that no access strays outside the modelled argument slots, and
//! that returned `f16` values leave through H0.. and are read from there.
//!
//! FEAT_FP16 availability: base AArch64 transports `f16` (H-register loads
//! and stores, the full-vector `ORR` copy and `FCVT` to and from `f32`/`f64`),
//! so the ABI corpus compiles for the generic Linux baseline profile, whose
//! objects are checked to contain no FEAT_FP16 instruction. `f16` data
//! processing over the same boundary is refused by name without the explicit
//! `fp16` profile and executes with it; the explicit-profile native lane
//! requires host FP16, read here from `AT_HWCAP` (`fphp`, `asimdhp`), and a
//! host without it is a failure, never a skip.
//!
//! Negative controls: mutating one stack-argument load (callee) or store
//! (caller) in a real object is rejected by the placement check and, linked,
//! by the C oracle; a C prototype that spells one `f16` argument `float` is
//! detected for every shape; the baseline profile refuses `f16` arithmetic.
//!
//! Evidence boundary: native execution against GCC's `_Float16` ABI and
//! decoded object placement at O0-O3 for the baseline and explicit-fp16
//! lanes on one Linux host. It is not a proof and does not cover variadic
//! `f16`, `f16` vectors or DarwinPCS. The native rows are Linux GNU only:
//! DarwinPCS packs HFA members on the stack at their natural size (LLVM
//! places the `f16` after a stack HFA3 at offset 6), which the Darwin
//! classifier does not do yet, so this corpus is not a Darwin oracle.

#[path = "common/field_typed.rs"]
mod field_typed;

use std::collections::BTreeMap;
use std::fmt::Write as _;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lift::disasm::aarch64::{Instruction, LoadStorePairAddressMode, decode};
use trust_ir::{
    BinOp, Block, BlockId, Constant, Endianness, FieldDef, FuncId, FuncTy, Function, Inst,
    InstrNode, Linkage, Module, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo,
    Ty, ValueId,
};

const LINUX: &str = "aarch64-unknown-linux-gnu";
const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
/// The two lanes: the generic Linux AOT contract (no FEAT_FP16) and an
/// explicit, recorded `fp16` profile.
const LANES: [(&str, Option<AArch64IsaProfile>); 2] = [
    ("baseline", None),
    ("explicit-fp16", Some(AArch64IsaProfile::FP16)),
];

// ---------------------------------------------------------------------------
// Corpus
// ---------------------------------------------------------------------------

/// One argument kind. `Hfa(n)` is `struct { _Float16 m0..m{n-1}; }`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum P {
    H,
    S,
    D,
    B,
    W16,
    W32,
    X64,
    Hfa(u8),
}

impl P {
    /// Bytes the argument occupies in its record slot (at most eight).
    fn bytes(self) -> u32 {
        match self {
            P::B => 1,
            P::H | P::W16 => 2,
            P::S | P::W32 => 4,
            P::D | P::X64 => 8,
            P::Hfa(n) => 2 * u32::from(n),
        }
    }

    fn c_type(self) -> String {
        match self {
            P::H => "_Float16".into(),
            P::S => "float".into(),
            P::D => "double".into(),
            P::B => "int8_t".into(),
            P::W16 => "int16_t".into(),
            P::W32 => "int32_t".into(),
            P::X64 => "int64_t".into(),
            P::Hfa(n) => format!("HFA{n}"),
        }
    }

    /// C value-generator kind; HFA members use the `f16` generator.
    fn kind(self) -> &'static str {
        match self {
            P::H | P::Hfa(_) => "K_H",
            P::S => "K_S",
            P::D => "K_D",
            P::B => "K_B",
            P::W16 => "K_W16",
            P::W32 => "K_W32",
            P::X64 => "K_X64",
        }
    }

    fn members(self) -> u32 {
        match self {
            P::Hfa(n) => u32::from(n),
            _ => 1,
        }
    }

    /// Register view a SIMD&FP argument of this kind is transferred through.
    fn fp_view(self) -> Option<V> {
        match self {
            P::H | P::Hfa(_) => Some(V::H),
            P::S => Some(V::S),
            P::D => Some(V::D),
            _ => None,
        }
    }
}

/// What a shape returns: argument `k` unchanged (an `f16` or an HFA), or the
/// HFA argument `k` with its members reversed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ret {
    Param(usize),
    Reverse(usize),
}

#[derive(Clone, Debug)]
struct Shape {
    name: String,
    params: Vec<P>,
    ret: Ret,
}

impl Shape {
    fn ret_kind(&self) -> P {
        match self.ret {
            Ret::Param(k) | Ret::Reverse(k) => self.params[k],
        }
    }

    /// Index of the argument the mismatched-prototype control misdeclares.
    fn last_f16(&self) -> usize {
        self.params.iter().rposition(|p| *p == P::H).unwrap()
    }
}

fn shape(name: impl Into<String>, params: Vec<P>, ret: Ret) -> Shape {
    let shape = Shape {
        name: name.into(),
        params,
        ret,
    };
    match shape.ret {
        Ret::Param(k) => assert!(matches!(shape.params[k], P::H | P::Hfa(_))),
        Ret::Reverse(k) => assert!(matches!(shape.params[k], P::Hfa(_))),
    }
    assert!(shape.params.contains(&P::H));
    shape
}

fn shapes() -> Vec<Shape> {
    use P::*;
    let mut out = vec![
        // Twelve f16: H0-H7, then four 8-byte stack slots.
        shape("h12", vec![H; 12], Ret::Param(11)),
        // FP and GPR banks exhausted in interleaved order; the stack then
        // holds f16, i16, f16, f64, f32, f16, i64 at 0, 8, ..., 48.
        shape(
            "mixed",
            vec![
                W32, H, D, X64, H, S, W16, H, D, B, H, S, X64, H, W32, X64, W16, H, D, S, H, X64,
            ],
            Ret::Param(20),
        ),
    ];
    for n in 1..=4u8 {
        let mut prefixes = vec![0, 8 - n, 9 - n, 8];
        prefixes.dedup();
        for prefix in prefixes {
            let mut params = vec![H; usize::from(prefix)];
            params.extend([Hfa(n), H, Hfa(2), H, W32]);
            out.push(shape(
                format!("hfa{n}_p{prefix}"),
                params,
                Ret::Param(usize::from(prefix) + 3),
            ));
        }
    }
    for n in 1..=4u8 {
        // Arrives in H1.., returned in H0.. .
        out.push(shape(format!("ret{n}_reg"), vec![H, Hfa(n)], Ret::Param(1)));
        // Arrives on the stack after eight f16, returned in H0.. .
        let mut params = vec![H; 8];
        params.push(Hfa(n));
        out.push(shape(format!("ret{n}_stack"), params, Ret::Param(8)));
        // Arrives in H0.., returned with its members permuted.
        out.push(shape(format!("rev{n}"), vec![Hfa(n), H], Ret::Reverse(0)));
    }
    out
}

// ---------------------------------------------------------------------------
// Independent AAPCS64 placement model (Arm IHI 0055 stage C), no classifier
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Loc {
    /// General-purpose register number.
    Gpr(u8),
    /// First SIMD&FP register and the number of consecutive registers.
    Fpr(u8, u8),
    /// Byte offset from the stack pointer at the call.
    Stack(u32),
}

/// Placement of `params` after the leading record pointer (X0).
fn aapcs64_placement(params: &[P]) -> Vec<Loc> {
    placement(params, Rules::AAPCS64)
}

/// The AAPCS64 rules, and two deliberately wrong variants that serve only as
/// negative controls of the placement check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rules {
    /// Stack arguments packed at natural size and alignment (DarwinPCS
    /// style) instead of 8-byte slots.
    packed: bool,
    /// The NSRN is set to 8 once an HFA goes to the stack (no backfill).
    clamp: bool,
}

impl Rules {
    const AAPCS64: Self = Self {
        packed: false,
        clamp: true,
    };
    const PACKED: Self = Self {
        packed: true,
        clamp: true,
    };
    const BACKFILL: Self = Self {
        packed: false,
        clamp: false,
    };
}

fn placement(params: &[P], rules: Rules) -> Vec<Loc> {
    let (mut ngrn, mut nsrn, mut nsaa) = (1u8, 0u8, 0u32);
    let stack = |p: P, nsaa: &mut u32| {
        let (align, bytes) = if rules.packed {
            let align = if let P::Hfa(_) = p { 2 } else { p.bytes() };
            (align, p.bytes())
        } else {
            // Every argument here has natural alignment <= 8: the NSAA is
            // rounded up to 8 and the argument occupies whole 8-byte units.
            (8, p.bytes().div_ceil(8) * 8)
        };
        *nsaa = nsaa.div_ceil(align) * align;
        let at = *nsaa;
        *nsaa += bytes;
        Loc::Stack(at)
    };
    params
        .iter()
        .map(|p| match p {
            P::B | P::W16 | P::W32 | P::X64 => {
                if ngrn < 8 {
                    ngrn += 1;
                    Loc::Gpr(ngrn - 1)
                } else {
                    stack(*p, &mut nsaa)
                }
            }
            P::H | P::S | P::D => {
                if nsrn < 8 {
                    nsrn += 1;
                    Loc::Fpr(nsrn - 1, 1)
                } else {
                    stack(*p, &mut nsaa)
                }
            }
            P::Hfa(n) => {
                if nsrn + n <= 8 {
                    nsrn += n;
                    Loc::Fpr(nsrn - n, *n)
                } else {
                    // No later SIMD&FP argument may use a skipped register.
                    if rules.clamp {
                        nsrn = 8;
                    }
                    stack(*p, &mut nsaa)
                }
            }
        })
        .collect()
}

/// Stack-argument units of one shape: `(offset, bytes, kind, member)` for
/// every scalar and every HFA member, plus the slot extents.
struct StackArea {
    /// `f16` transported as a 16-bit unit: scalar `f16` and HFA members.
    halves: Vec<u32>,
    /// Scalar `f16` offsets (a subset of `halves`).
    scalar_halves: Vec<u32>,
    /// Other scalars: offset, width and SIMD&FP view (None for integers).
    others: Vec<(u32, u32, Option<V>)>,
    /// Slot extents `[start, end)`.
    slots: Vec<(u32, u32)>,
    /// Total bytes of the stack-argument area.
    size: u32,
}

fn stack_area(params: &[P], locs: &[Loc]) -> StackArea {
    let mut area = StackArea {
        halves: Vec::new(),
        scalar_halves: Vec::new(),
        others: Vec::new(),
        slots: Vec::new(),
        size: 0,
    };
    for (p, loc) in params.iter().zip(locs) {
        let Loc::Stack(at) = *loc else { continue };
        let end = at + p.bytes().div_ceil(8) * 8;
        area.slots.push((at, end));
        area.size = area.size.max(end);
        match p {
            P::H => {
                area.halves.push(at);
                area.scalar_halves.push(at);
            }
            P::Hfa(n) => area.halves.extend((0..u32::from(*n)).map(|m| at + 2 * m)),
            other => area.others.push((at, other.bytes(), other.fp_view())),
        }
    }
    area
}

// ---------------------------------------------------------------------------
// trust-ir corpus
// ---------------------------------------------------------------------------

fn linux_target_info() -> TargetInfo {
    TargetInfo {
        triple: LINUX.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn hfa_ty(n: u8) -> Ty {
    Ty::Struct(StructId::new(u32::from(n) - 1))
}

fn ir_ty(p: P) -> Ty {
    match p {
        P::H => Ty::F16,
        P::S => Ty::F32,
        P::D => Ty::F64,
        P::B => Ty::I8,
        P::W16 => Ty::I16,
        P::W32 => Ty::I32,
        P::X64 => Ty::I64,
        P::Hfa(n) => hfa_ty(n),
    }
}

/// Straight-line function body builder with fresh value ids.
struct Body {
    next: u32,
    nodes: Vec<InstrNode>,
}

impl Body {
    fn new(params: u32) -> Self {
        Self {
            next: params,
            nodes: Vec::new(),
        }
    }

    fn push(&mut self, inst: Inst) -> ValueId {
        let id = ValueId::new(self.next);
        self.next += 1;
        self.nodes.push(InstrNode::new(inst).with_result(id));
        id
    }

    fn effect(&mut self, inst: Inst) {
        self.nodes.push(InstrNode::new(inst));
    }

    /// `base + offset` bytes, as a byte-scaled GEP.
    fn at(&mut self, base: ValueId, offset: u32) -> ValueId {
        let index = self.push(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(i128::from(offset)),
        });
        self.push(Inst::GEP {
            pointee_ty: Ty::I8,
            base,
            indices: vec![index],
            inbounds: true,
        })
    }

    fn store(&mut self, ty: Ty, value: ValueId, base: ValueId, offset: u32, align: u32) {
        let ptr = self.at(base, offset);
        self.effect(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: Some(u64::from(align)),
        });
    }

    fn load(&mut self, ty: Ty, base: ValueId, offset: u32, align: u32) -> ValueId {
        let ptr = self.at(base, offset);
        self.push(Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: Some(u64::from(align)),
        })
    }

    /// Record argument `value` of kind `p` into slot `slot` of `record`.
    fn record(&mut self, p: P, value: ValueId, record: ValueId, slot: u32) {
        match p {
            P::Hfa(n) => {
                for member in 0..u32::from(n) {
                    let field = self.push(Inst::ExtractField {
                        ty: hfa_ty(n),
                        aggregate: value,
                        field: member,
                    });
                    self.store(Ty::F16, field, record, 8 * slot + 2 * member, 2);
                }
            }
            scalar => self.store(ir_ty(scalar), value, record, 8 * slot, scalar.bytes()),
        }
    }
}

fn define(module: &mut Module, name: &str, params: Vec<Ty>, ret: Option<Ty>, body: Body) {
    let ty = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: ret.into_iter().collect(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty))
            .collect(),
        body: body.nodes,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn declare(module: &mut Module, name: &str, params: Vec<Ty>, ret: Option<Ty>) -> FuncId {
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns: ret.into_iter().collect(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, BlockId::new(0));
    function.linkage = Linkage::External;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

fn hfa_structs(module: &mut Module) {
    for n in 1..=4u8 {
        module.structs.push(StructDef {
            origin: None,
            id: StructId::new(u32::from(n) - 1),
            name: format!("HFA{n}"),
            size: Some(2 * u64::from(n)),
            align: Some(2),
            repr: StructRepr::C,
            fields: (0..u64::from(n))
                .map(|member| FieldDef {
                    name: format!("m{member}"),
                    ty: Ty::F16,
                    offset: Some(2 * member),
                })
                .collect(),
        });
    }
}

/// `cg_<shape>(rec, args...)` records every argument and returns the
/// designated one; `cg_call_<shape>(in, rec)` loads the arguments from `in`,
/// calls the C callee `c_<shape>(rec, args...)` and records its result in
/// the slot after the arguments.
fn build_module(shapes: &[Shape], target: TargetInfo) -> Module {
    let mut module = Module::new("f16_abi_linux");
    module.target_info = Some(target);
    hfa_structs(&mut module);
    for shape in shapes {
        let count = shape.params.len() as u32;
        let mut params = vec![Ty::Ptr];
        params.extend(shape.params.iter().map(|p| ir_ty(*p)));
        let ret_ty = ir_ty(shape.ret_kind());

        // C calls CG.
        let mut body = Body::new(count + 1);
        for (index, p) in shape.params.iter().enumerate() {
            body.record(
                *p,
                ValueId::new(index as u32 + 1),
                ValueId::new(0),
                index as u32,
            );
        }
        let result = match shape.ret {
            Ret::Param(k) => ValueId::new(k as u32 + 1),
            Ret::Reverse(k) => {
                let P::Hfa(n) = shape.params[k] else {
                    unreachable!()
                };
                // Every member is extracted before the first insert: the
                // adapter lowers InsertField by updating the source
                // aggregate's storage in place, so a read of the argument
                // after an insert would observe it (LIMITATIONS.md).
                let source = ValueId::new(k as u32 + 1);
                let members: Vec<_> = (0..u32::from(n))
                    .map(|member| {
                        body.push(Inst::ExtractField {
                            ty: hfa_ty(n),
                            aggregate: source,
                            field: u32::from(n) - 1 - member,
                        })
                    })
                    .collect();
                let mut aggregate = source;
                for (member, value) in (0..u32::from(n)).zip(members) {
                    aggregate = body.push(Inst::InsertField {
                        ty: hfa_ty(n),
                        aggregate,
                        field: member,
                        value,
                    });
                }
                aggregate
            }
        };
        body.effect(Inst::Return {
            values: vec![result],
        });
        define(
            &mut module,
            &format!("cg_{}", shape.name),
            params.clone(),
            Some(ret_ty.clone()),
            body,
        );

        // CG calls C.
        let callee = declare(
            &mut module,
            &format!("c_{}", shape.name),
            params,
            Some(ret_ty),
        );
        let (input, record) = (ValueId::new(0), ValueId::new(1));
        let mut body = Body::new(2);
        let mut args = vec![record];
        for (index, p) in shape.params.iter().enumerate() {
            let align = match p {
                P::Hfa(_) => 2,
                scalar => scalar.bytes(),
            };
            args.push(body.load(ir_ty(*p), input, 8 * index as u32, align));
        }
        let result = body.push(Inst::Call { callee, args });
        body.record(shape.ret_kind(), result, record, count);
        body.effect(Inst::Return { values: vec![] });
        define(
            &mut module,
            &format!("cg_call_{}", shape.name),
            vec![Ty::Ptr, Ty::Ptr],
            None,
            body,
        );
    }
    module
}

/// `cg_fadd(h0..h9) -> h1 + h9`: FEAT_FP16 data processing over a register
/// and a stack-passed `f16`, the positive control of the profile gate.
fn build_fp16_arith_module(target: TargetInfo) -> Module {
    let mut module = Module::new("f16_abi_fp16_arith");
    module.target_info = Some(target);
    let mut body = Body::new(10);
    let sum = body.push(Inst::BinOp {
        op: BinOp::FAdd,
        ty: Ty::F16,
        lhs: ValueId::new(1),
        rhs: ValueId::new(9),
    });
    body.effect(Inst::Return { values: vec![sum] });
    define(
        &mut module,
        "cg_fadd",
        vec![Ty::F16; 10],
        Some(Ty::F16),
        body,
    );
    module
}

// ---------------------------------------------------------------------------
// C oracle
// ---------------------------------------------------------------------------

/// Round 0 gives every position a distinct ordinary value (so any swap is
/// visible); round r >= 1 rotates the special patterns so every position
/// carries every one of them.
const C_PRELUDE: &str = r#"#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef struct { _Float16 m0; } HFA1;
typedef struct { _Float16 m0, m1; } HFA2;
typedef struct { _Float16 m0, m1, m2; } HFA3;
typedef struct { _Float16 m0, m1, m2, m3; } HFA4;
_Static_assert(sizeof(_Float16) == 2 && _Alignof(_Float16) == 2, "binary16 layout");
_Static_assert(sizeof(HFA3) == 6 && _Alignof(HFA3) == 2, "HFA layout");
_Static_assert(sizeof(HFA4) == 8, "HFA layout");
enum { K_H, K_S, K_D, K_B, K_W16, K_W32, K_X64 };
/* binary16: +-0, +-min subnormal, +-max subnormal, min normal, +-1, +-max,
   +-inf, default qNaN, quiet NaNs with payloads (either sign), signalling
   NaNs with payloads (either sign), ordinary values. */
static const uint16_t PH[] = {
  0x0000, 0x8000, 0x0001, 0x8001, 0x03ff, 0x83ff, 0x0400, 0x3c00, 0xbc00,
  0x7bff, 0xfbff, 0x7c00, 0xfc00, 0x7e00, 0x7e01, 0x7fff, 0xfe5a, 0x7c01,
  0x7d55, 0xfd01, 0x3555, 0x5140, 0xc948 };
static const uint32_t PS[] = { 0x00000000u, 0x80000000u, 0x00000001u, 0x807fffffu,
  0x7f800000u, 0xff800000u, 0x7fc00001u, 0x7f800001u, 0xffa5a5a5u, 0x3f800000u, 0xc0490fdbu };
static const uint64_t PD[] = { 0x0000000000000000ull, 0x8000000000000000ull, 0x0000000000000001ull,
  0x7ff0000000000000ull, 0xfff0000000000000ull, 0x7ff8000000000001ull, 0x7ff0000000000001ull,
  0xfff5a5a5a5a5a5a5ull, 0x3ff0000000000000ull, 0xc00921fb54442d18ull };
static const uint64_t PI[] = { 0x8000000000000001ull, 0x7fffffffffffffffull, 0xffffffffffffffffull,
  0x0000000000000001ull, 0xfedcba9876543210ull, 0x00000000ffff8001ull, 0x5a5a5a5a5a5a5a5aull };
#define N(a) ((int)(sizeof(a) / sizeof((a)[0])))
static uint64_t gen(int kind, int round, int pos) {
  if (round == 0) {
    switch (kind) {
      case K_H: return 0x3c00u + 1u + (unsigned)pos;
      case K_S: return 0x3f800000u + 1u + (unsigned)pos;
      case K_D: return 0x3ff0000000000000ull + 1u + (unsigned)pos;
      default: return 0x4000000000000041ull + 0x0101010101010101ull * (unsigned)pos;
    }
  }
  switch (kind) {
    case K_H: return PH[(pos + round - 1) % N(PH)];
    case K_S: return PS[(pos + round - 1) % N(PS)];
    case K_D: return PD[(pos + round - 1) % N(PD)];
    default: return PI[(pos + round - 1) % N(PI)];
  }
}
#define ROUNDS (1 + N(PH))
static long calls, checks;
static void dump(const unsigned char *p, int n) { for (int i = 0; i < n; i++) printf("%02x", p[i]); }
static int compare(const char *shape, const char *dir, int round, const unsigned char *want,
                   const unsigned char *got, int slots) {
  for (int s = 0; s < slots; s++) {
    checks++;
    if (memcmp(want + 8 * s, got + 8 * s, 8)) {
      printf("MISMATCH %s %s round=%d slot=%d want=", shape, dir, round, s);
      dump(want + 8 * s, 8); printf(" got="); dump(got + 8 * s, 8); printf("\n");
      return 1;
    }
  }
  return 0;
}
"#;

/// The C driver: C callees, the prototypes of the CG functions and `main`
/// (`argv[1]`, when given, selects one shape). Compiled with
/// `-DMISMATCH_<shape>`, the prototype C calls `cg_<shape>` through spells
/// that shape's last `f16` argument `float` (negative control).
fn c_driver(shapes: &[Shape]) -> String {
    let mut c = String::from(C_PRELUDE);
    for shape in shapes {
        let name = &shape.name;
        let count = shape.params.len();
        let ret = shape.ret_kind().c_type();
        let decls = shape
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| format!(", {} p{i}", p.c_type()))
            .collect::<String>();
        let result = match shape.ret {
            Ret::Param(k) => format!("p{k}"),
            Ret::Reverse(k) => {
                let n = shape.params[k].members();
                let fields = (0..n)
                    .map(|m| format!("p{k}.m{}", n - 1 - m))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({ret}){{ {fields} }}")
            }
        };
        let records = (0..count)
            .map(|i| format!("  memcpy(rec + {}, &p{i}, sizeof p{i});\n", 8 * i))
            .collect::<String>();
        writeln!(
            c,
            "__attribute__((noinline)) {ret} c_{name}(unsigned char *rec{decls}) {{\n{records}  return {result};\n}}"
        )
        .unwrap();
        let prototype = |mismatch: bool| {
            shape
                .params
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    if mismatch && i == shape.last_f16() {
                        ", float".to_string()
                    } else {
                        format!(", {}", p.c_type())
                    }
                })
                .collect::<String>()
        };
        writeln!(
            c,
            "#ifdef MISMATCH_{name}\nextern {ret} cg_{name}(unsigned char *{});\n#else\nextern {ret} cg_{name}(unsigned char *{});\n#endif\nextern void cg_call_{name}(const unsigned char *, unsigned char *);",
            prototype(true),
            prototype(false),
        )
        .unwrap();

        // Runner: values, expected record, both directions.
        let mut run = format!(
            "static int run_{name}(int round) {{\n  unsigned char in[{bytes}], want[{bytes}], got[{bytes}];\n  memset(in, 0, sizeof in); memset(want, 0xa5, sizeof want);\n  uint64_t bits; int pos = 0;\n",
            bytes = 8 * (count + 1)
        );
        for (i, p) in shape.params.iter().enumerate() {
            let ty = p.c_type();
            writeln!(run, "  {ty} p{i};").unwrap();
            for m in 0..p.members() {
                let width = if matches!(p, P::Hfa(_)) { 2 } else { p.bytes() };
                let at = 8 * i as u32 + 2 * m;
                writeln!(
                    run,
                    "  bits = gen({kind}, round, pos++); memcpy(in + {at}, &bits, {width}); memcpy(want + {at}, &bits, {width});",
                    kind = p.kind()
                )
                .unwrap();
            }
            writeln!(run, "  memcpy(&p{i}, in + {}, sizeof p{i});", 8 * i).unwrap();
        }
        let rs = 8 * count;
        match shape.ret {
            Ret::Param(k) => {
                let bytes = shape.params[k].bytes();
                writeln!(run, "  memcpy(want + {rs}, in + {}, {bytes});", 8 * k).unwrap();
            }
            Ret::Reverse(k) => {
                let n = shape.params[k].members() as usize;
                for m in 0..n {
                    writeln!(
                        run,
                        "  memcpy(want + {}, in + {}, 2);",
                        rs + 2 * m,
                        8 * k + 2 * (n - 1 - m)
                    )
                    .unwrap();
                }
            }
        }
        let args = (0..count).map(|i| format!(", p{i}")).collect::<String>();
        let rbytes = shape.ret_kind().bytes();
        write!(
            run,
            "  memset(got, 0xa5, sizeof got);\n  {{ {ret} r = cg_{name}(got{args}); memcpy(got + {rs}, &r, {rbytes}); }}\n  calls++;\n  if (compare(\"{name}\", \"c-calls-cg\", round, want, got, {slots})) return 1;\n  memset(got, 0xa5, sizeof got);\n  cg_call_{name}(in, got);\n  calls++;\n  if (compare(\"{name}\", \"cg-calls-c\", round, want, got, {slots})) return 1;\n  return 0;\n}}\n",
            slots = count + 1
        )
        .unwrap();
        c.push_str(&run);
    }
    c.push_str(
        "int main(int argc, char **argv) {\n  const char *only = argc > 1 ? argv[1] : 0;\n  int ran = 0;\n  for (int round = 0; round < ROUNDS; round++) {\n",
    );
    for shape in shapes {
        writeln!(
            c,
            "    if (!only || !strcmp(only, \"{0}\")) {{ ran++; if (run_{0}(round)) return 1; }}",
            shape.name
        )
        .unwrap();
    }
    c.push_str(
        "  }\n  if (!ran) { printf(\"no shape selected\\n\"); return 2; }\n  printf(\"f16-abi shapes=%d calls=%ld slot_checks=%ld\\n\", ran / ROUNDS, calls, checks);\n  return 0;\n}\n",
    );
    c
}

// ---------------------------------------------------------------------------
// Compilation
// ---------------------------------------------------------------------------

/// `profile = None` is the target's own AOT contract (the generic baseline
/// for Linux); `Some` is an explicit, recorded ISA profile.
fn compile(
    module: &Module,
    triple: &str,
    opt: OptLevel,
    profile: Option<AArch64IsaProfile>,
) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            aarch64_isa_profile: profile,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&field_typed::normalized(module))
    .map(|output| output.object_code)
    .map_err(|error| error.to_string())
}

/// The corpus compiled for Linux at every opt level and lane.
fn linux_objects(shapes: &[Shape]) -> Vec<(String, Vec<u8>)> {
    let module = build_module(shapes, linux_target_info());
    let mut objects = Vec::new();
    for (lane, profile) in LANES {
        for opt in OPTS {
            let object = compile(&module, LINUX, opt, profile)
                .unwrap_or_else(|error| panic!("{lane} {opt:?}: {error}"));
            objects.push((format!("{lane}-{opt:?}"), object));
        }
    }
    objects
}

// ---------------------------------------------------------------------------
// ELF64 reader (independent of the compiler's writer)
// ---------------------------------------------------------------------------

fn u16_at(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8], at: usize) -> usize {
    usize::try_from(u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())).unwrap()
}

struct ElfSection {
    kind: u32,
    offset: usize,
    size: usize,
    link: usize,
    info: usize,
}

/// One `STT_FUNC` symbol: file offset of its first word, its words and its
/// `R_AARCH64_CALL26` targets by byte offset within the function.
struct ElfFunction {
    file_offset: usize,
    words: Vec<u32>,
    calls: BTreeMap<usize, String>,
}

fn c_string(bytes: &[u8], at: usize) -> String {
    let end = bytes[at..].iter().position(|b| *b == 0).unwrap();
    String::from_utf8(bytes[at..at + end].to_vec()).unwrap()
}

fn elf_functions(object: &[u8]) -> BTreeMap<String, ElfFunction> {
    assert_eq!(&object[..4], b"\x7fELF", "ELF magic");
    assert_eq!(&object[4..6], b"\x02\x01", "ELFCLASS64/ELFDATA2LSB");
    assert_eq!(u16_at(object, 16), 1, "ET_REL");
    assert_eq!(u16_at(object, 18), 183, "EM_AARCH64");
    let table = u64_at(object, 40);
    let entry = usize::from(u16_at(object, 58));
    let sections: Vec<ElfSection> = (0..usize::from(u16_at(object, 60)))
        .map(|index| {
            let at = table + index * entry;
            ElfSection {
                kind: u32_at(object, at + 4),
                offset: u64_at(object, at + 24),
                size: u64_at(object, at + 32),
                link: u32_at(object, at + 40) as usize,
                info: u32_at(object, at + 44) as usize,
            }
        })
        .collect();
    let symtab = sections
        .iter()
        .find(|section| section.kind == 2)
        .expect("SHT_SYMTAB");
    let strtab = &sections[symtab.link];
    let symbols: Vec<(String, u8, usize, usize, usize)> = (0..symtab.size / 24)
        .map(|index| {
            let at = symtab.offset + index * 24;
            (
                c_string(object, strtab.offset + u32_at(object, at) as usize),
                object[at + 4],
                usize::from(u16_at(object, at + 6)),
                u64_at(object, at + 8),
                u64_at(object, at + 16),
            )
        })
        .collect();
    let mut functions = BTreeMap::new();
    for (name, info, shndx, value, size) in &symbols {
        if info & 0xf != 2 || *shndx == 0 {
            continue;
        }
        let section = &sections[*shndx];
        let file_offset = section.offset + value;
        let words = object[file_offset..file_offset + size]
            .as_chunks::<4>()
            .0
            .iter()
            .map(|word| u32::from_le_bytes(*word))
            .collect();
        let mut calls = BTreeMap::new();
        for rela in sections
            .iter()
            .filter(|rela| rela.kind == 4 && rela.info == *shndx)
        {
            for index in 0..rela.size / 24 {
                let at = rela.offset + index * 24;
                let offset = u64_at(object, at);
                let info = u64::from_le_bytes(object[at + 8..at + 16].try_into().unwrap());
                // R_AARCH64_CALL26 = 283.
                if info & 0xffff_ffff == 283 && (*value..value + size).contains(&offset) {
                    calls.insert(offset - value, symbols[(info >> 32) as usize].0.clone());
                }
            }
        }
        functions.insert(
            name.clone(),
            ElfFunction {
                file_offset,
                words,
                calls,
            },
        );
    }
    functions
}

// ---------------------------------------------------------------------------
// Straight-line decoded trace: SP/frame tracking and V-register events
// ---------------------------------------------------------------------------

/// How a V register is read or written by one instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V {
    B,
    H,
    S,
    D,
    Q,
    /// Full-register `ORR Vd.16B, Vn.16B, Vn.16B` (the `MOV` alias).
    Copy,
    Other,
    /// Clobbered by a call.
    Clobber,
}

fn fp_view_of_bytes(bytes: u32) -> V {
    match bytes {
        1 => V::B,
        2 => V::H,
        4 => V::S,
        8 => V::D,
        _ => V::Q,
    }
}

fn fp_view_of_ftype(ftype: u8) -> V {
    match ftype {
        0 => V::S,
        1 => V::D,
        3 => V::H,
        _ => V::Other,
    }
}

/// A memory access through SP or an SP-derived register, as a byte offset
/// from the stack pointer at function entry.
#[derive(Clone, Copy, Debug)]
struct Mem {
    index: usize,
    at: i64,
    bytes: u32,
    load: bool,
    /// The SIMD&FP view for a V-register transfer, None for a GPR transfer.
    fp: Option<V>,
}

#[derive(Default)]
struct Trace {
    mem: Vec<Mem>,
    /// `(index, register, read, view)` in program order.
    events: Vec<(usize, u8, bool, V)>,
    /// `(index, symbol, SP offset at the call)`.
    calls: Vec<(usize, String, i64)>,
    ret: Option<usize>,
}

impl Trace {
    fn first_access(&self, reg: u8) -> Option<(usize, bool, V)> {
        self.events
            .iter()
            .find(|event| event.1 == reg)
            .map(|event| (event.0, event.2, event.3))
    }

    fn first_access_after(&self, reg: u8, after: usize) -> Option<(usize, bool, V)> {
        self.events
            .iter()
            .find(|event| event.1 == reg && event.0 > after)
            .map(|event| (event.0, event.2, event.3))
    }

    /// The last write to `reg` strictly before `before` (a later write at
    /// the same index as a read, as in `ORR Vd, Vd`, still counts).
    fn last_write_before(&self, reg: u8, before: usize) -> Option<(usize, V)> {
        self.events
            .iter()
            .rfind(|event| event.1 == reg && !event.2 && event.0 < before)
            .map(|event| (event.0, event.3))
    }
}

fn sign_extend(value: u32, bits: u32) -> i64 {
    let shift = 64 - bits;
    (i64::from(value) << shift) >> shift
}

/// Walk one straight-line function. Any control flow, unclassified
/// instruction or untracked write of SP fails closed.
fn trace(function: &ElfFunction) -> Result<Trace, String> {
    let mut out = Trace::default();
    let mut sp = 0i64;
    // X registers holding SP-derived addresses (entry-SP relative).
    let mut frame: BTreeMap<u8, i64> = BTreeMap::new();
    for (index, &word) in function.words.iter().enumerate() {
        if out.ret.is_some() {
            return Err(format!("word {index} follows RET"));
        }
        let inst = decode(word).map_err(|error| format!("word {index} {word:#010x}: {error}"))?;
        let base = |frame: &BTreeMap<u8, i64>, rn: u8, sp: i64| {
            if rn == 31 {
                Some(sp)
            } else {
                frame.get(&rn).copied()
            }
        };
        let mut read = |reg: u8, view: V| out.events.push((index, reg, true, view));
        match inst {
            Instruction::AddSubImm(a) => {
                let imm = i64::from(a.imm12) << if a.shift12 { 12 } else { 0 };
                if a.set_flags {
                    // CMP/CMN or ADDS/SUBS: rd 31 is XZR.
                    frame.remove(&a.rd);
                    continue;
                }
                let value = base(&frame, a.rn, sp)
                    .filter(|_| a.sf == 1)
                    .map(|value| if a.op == 0 { value + imm } else { value - imm });
                if a.rd == 31 {
                    sp = value.ok_or(format!("word {index}: SP set from an untracked value"))?;
                } else if let Some(value) = value {
                    frame.insert(a.rd, value);
                } else {
                    frame.remove(&a.rd);
                }
            }
            Instruction::LogicalShiftedReg(l) => {
                // MOV Xd, Xm is ORR Xd, XZR, Xm; anything else defines rd.
                let copy = l.sf == 1
                    && l.opc == 1
                    && !l.n
                    && l.shift == 0
                    && l.imm6 == 0
                    && l.rn == 31
                    && l.rm != 31;
                match copy.then(|| frame.get(&l.rm).copied()).flatten() {
                    Some(value) => {
                        frame.insert(l.rd, value);
                    }
                    None => {
                        frame.remove(&l.rd);
                    }
                }
            }
            Instruction::LogicalImm(l) => {
                if l.rd == 31 {
                    return Err(format!("word {index}: logical immediate writes SP"));
                }
                frame.remove(&l.rd);
            }
            Instruction::AddSubShiftedReg(a) => {
                frame.remove(&a.rd);
            }
            Instruction::AddSubCarry(a) => {
                frame.remove(&a.rd);
            }
            Instruction::MoveWide(m) => {
                frame.remove(&m.rd);
            }
            Instruction::BitfieldMove(b) => {
                frame.remove(&b.rd);
            }
            Instruction::PcRelAddress(p) => {
                frame.remove(&p.rd);
            }
            Instruction::DataProcessing2Source(d) => {
                frame.remove(&d.rd);
            }
            Instruction::DataProcessing3Source(d) => {
                frame.remove(&d.rd);
            }
            Instruction::ConditionalSelect(c) => {
                frame.remove(&c.rd);
            }
            Instruction::LoadStoreUnsignedImm(m) => {
                let (bytes, load) = single_transfer(m.size, m.vector, m.opc)
                    .ok_or(format!("word {index}: prefetch"))?;
                let at = base(&frame, m.rn, sp).map(|b| b + i64::from(m.imm12) * i64::from(bytes));
                transfer(&mut out, &mut frame, index, at, bytes, load, m.vector, m.rt);
            }
            Instruction::LoadStoreUnscaled(m) => {
                let (bytes, load) = single_transfer(m.size, m.vector, m.opc)
                    .ok_or(format!("word {index}: prefetch"))?;
                let at = base(&frame, m.rn, sp).map(|b| b + i64::from(m.imm9));
                transfer(&mut out, &mut frame, index, at, bytes, load, m.vector, m.rt);
            }
            Instruction::LoadStoreIndexed(m) => {
                use trust_cg_lift::disasm::aarch64::LoadStoreIndexMode;
                let (bytes, load) = single_transfer(m.size, m.vector, m.opc)
                    .ok_or(format!("word {index}: prefetch"))?;
                let old = base(&frame, m.rn, sp);
                let new = old.map(|b| b + i64::from(m.imm9));
                let at = match m.mode {
                    LoadStoreIndexMode::PreIndex => new,
                    LoadStoreIndexMode::PostIndex => old,
                };
                transfer(&mut out, &mut frame, index, at, bytes, load, m.vector, m.rt);
                writeback(&mut frame, &mut sp, m.rn, new, index)?;
            }
            Instruction::LoadStorePair(m) => {
                let bytes: u32 = if m.vector {
                    4 << m.opc
                } else if m.opc == 2 {
                    8
                } else {
                    4
                };
                let offset = sign_extend(u32::from(m.imm7), 7) * i64::from(bytes);
                let old = base(&frame, m.rn, sp);
                let new = old.map(|b| b + offset);
                let at = match m.mode {
                    LoadStorePairAddressMode::SignedOffset | LoadStorePairAddressMode::PreIndex => {
                        new
                    }
                    LoadStorePairAddressMode::PostIndex => old,
                };
                transfer(
                    &mut out, &mut frame, index, at, bytes, m.load, m.vector, m.rt,
                );
                transfer(
                    &mut out,
                    &mut frame,
                    index,
                    at.map(|a| a + i64::from(bytes)),
                    bytes,
                    m.load,
                    m.vector,
                    m.rt2,
                );
                if m.mode != LoadStorePairAddressMode::SignedOffset {
                    writeback(&mut frame, &mut sp, m.rn, new, index)?;
                }
            }
            Instruction::NeonVecLogic(l) => {
                if !l.u && l.size == 0b10 && l.rn == l.rm && l.q {
                    read(l.rn, V::Copy);
                    out.events.push((index, l.rd, false, V::Copy));
                } else {
                    read(l.rn, V::Other);
                    read(l.rm, V::Other);
                    out.events.push((index, l.rd, false, V::Other));
                }
            }
            Instruction::FpArith(f) => {
                let view = fp_view_of_ftype(f.ftype);
                read(f.rn, view);
                read(f.rm, view);
                out.events.push((index, f.rd, false, view));
            }
            Instruction::FpUnary(f) => {
                let view = fp_view_of_ftype(f.ftype);
                read(f.rn, view);
                out.events.push((index, f.rd, false, view));
            }
            Instruction::FpPrecisionConvert(f) => {
                read(f.rn, fp_view_of_ftype(f.src_ftype));
                out.events
                    .push((index, f.rd, false, fp_view_of_ftype(f.dst_ftype)));
            }
            Instruction::Nop => {}
            Instruction::UncondBranch(b) if b.link => {
                let symbol = function
                    .calls
                    .get(&(4 * index))
                    .cloned()
                    .ok_or(format!("word {index}: BL without an R_AARCH64_CALL26"))?;
                out.calls.push((index, symbol, sp));
                // AAPCS64: X0-X18 and X30 are not preserved; V8-V15 are
                // callee-saved (low 64 bits), the rest are clobbered.
                frame.retain(|reg, _| (19..=29).contains(reg));
                for reg in (0..8).chain(16..32) {
                    out.events.push((index, reg, false, V::Clobber));
                }
            }
            Instruction::BranchReg(b) if b.opc == 2 && b.rn == 30 => out.ret = Some(index),
            other => return Err(format!("word {index}: unclassified {other:?}")),
        }
    }
    if out.ret.is_none() {
        return Err("no RET".into());
    }
    Ok(out)
}

/// `(bytes, load)` of a single-register transfer; None for PRFM.
fn single_transfer(size: u8, vector: bool, opc: u8) -> Option<(u32, bool)> {
    if vector {
        let bytes = if size == 0 && opc & 2 != 0 {
            16
        } else {
            1 << size
        };
        Some((bytes, opc & 1 == 1))
    } else if size == 3 && opc == 2 {
        None
    } else {
        Some((1 << size, opc != 0))
    }
}

#[allow(clippy::too_many_arguments)]
fn transfer(
    out: &mut Trace,
    frame: &mut BTreeMap<u8, i64>,
    index: usize,
    at: Option<i64>,
    bytes: u32,
    load: bool,
    vector: bool,
    rt: u8,
) {
    let fp = vector.then(|| fp_view_of_bytes(bytes));
    if let Some(at) = at {
        out.mem.push(Mem {
            index,
            at,
            bytes,
            load,
            fp,
        });
    }
    match (vector, load) {
        (true, true) => out.events.push((index, rt, false, fp.unwrap())),
        (true, false) => out.events.push((index, rt, true, fp.unwrap())),
        (false, true) => {
            frame.remove(&rt);
        }
        (false, false) => {}
    }
}

fn writeback(
    frame: &mut BTreeMap<u8, i64>,
    sp: &mut i64,
    rn: u8,
    new: Option<i64>,
    index: usize,
) -> Result<(), String> {
    if rn == 31 {
        *sp = new.ok_or(format!("word {index}: SP writeback from an untracked base"))?;
    } else if let Some(new) = new {
        frame.insert(rn, new);
    } else {
        frame.remove(&rn);
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Placement checks
// ---------------------------------------------------------------------------

fn view_ok(expected: V, actual: V) -> bool {
    actual == expected || actual == V::Copy
}

/// Registers the returned value leaves in: V0.. .
fn return_registers(shape: &Shape) -> u8 {
    shape.ret_kind().members() as u8
}

/// Entry register of member `member` of the returned value, if it arrives
/// in a register (the callee may then legitimately leave it untouched).
fn returned_member_entry_register(shape: &Shape, locs: &[Loc], member: u8) -> Option<u8> {
    match shape.ret {
        Ret::Param(k) => match locs[k] {
            Loc::Fpr(r, _) => Some(r + member),
            _ => None,
        },
        Ret::Reverse(k) => match locs[k] {
            Loc::Fpr(r, n) => Some(r + n - 1 - member),
            _ => None,
        },
    }
}

/// Callee `cg_<shape>`: register arguments consumed through their modelled
/// registers and views, stack arguments read by the right transfers at the
/// modelled offsets from the entry SP, results left in H0.. .
fn check_callee(shape: &Shape, function: &ElfFunction, locs: &[Loc]) -> Result<(), String> {
    let trace = trace(function)?;
    let mut expected: BTreeMap<u8, V> = BTreeMap::new();
    for (p, loc) in shape.params.iter().zip(locs) {
        if let Loc::Fpr(r, n) = *loc {
            for k in r..r + n {
                expected.insert(k, p.fp_view().unwrap());
            }
        }
    }
    for reg in 0..8u8 {
        let first = trace.first_access(reg);
        match (expected.get(&reg), first) {
            (Some(view), Some((_, true, actual))) if view_ok(*view, actual) => {}
            (Some(view), other) => {
                return Err(format!(
                    "argument register v{reg} ({view:?}) is first accessed as {other:?}"
                ));
            }
            (None, Some((index, true, _))) => {
                return Err(format!(
                    "v{reg} carries no argument but word {index} reads it before any write"
                ));
            }
            (None, _) => {}
        }
    }
    let area = stack_area(&shape.params, locs);
    let incoming: Vec<&Mem> = trace.mem.iter().filter(|m| m.at >= 0).collect();
    for m in &incoming {
        if !m.load {
            return Err(format!(
                "word {} stores into the incoming argument area at +{}",
                m.index, m.at
            ));
        }
        let (start, end) = (m.at as u32, m.at as u32 + m.bytes);
        if !area.slots.iter().any(|(s, e)| *s <= start && end <= *e) {
            return Err(format!(
                "word {} reads +{start}..+{end}, outside every stack-argument slot",
                m.index
            ));
        }
        if m.fp == Some(V::H) && !area.halves.contains(&start) {
            return Err(format!(
                "word {} is an H load at +{start}, which holds no f16",
                m.index
            ));
        }
    }
    let loaded = |at: u32, bytes: u32, fp: Option<V>| {
        incoming
            .iter()
            .any(|m| m.at == i64::from(at) && m.bytes == bytes && m.fp == fp)
    };
    for at in &area.halves {
        if !loaded(*at, 2, Some(V::H)) {
            return Err(format!(
                "the f16 stack argument at +{at} is not read by an H load"
            ));
        }
    }
    for (at, bytes, fp) in &area.others {
        if !loaded(*at, *bytes, *fp) {
            return Err(format!(
                "the {bytes}-byte stack argument at +{at} is not read by a {fp:?} load"
            ));
        }
    }
    let ret = trace.ret.unwrap();
    for member in 0..return_registers(shape) {
        match trace.last_write_before(member, ret + 1) {
            Some((_, view)) if view_ok(V::H, view) => {}
            None if returned_member_entry_register(shape, locs, member) == Some(member) => {}
            other => {
                return Err(format!(
                    "return register v{member} holds {other:?} at RET, not an f16"
                ));
            }
        }
    }
    Ok(())
}

/// Caller `cg_call_<shape>`: the call to `c_<shape>` is found by its
/// relocation; each register argument's last write before it is an H (or
/// S/D) transfer or a full copy made after any earlier call, each outgoing
/// stack argument is written at its modelled offset from the SP at the call
/// (an `f16` by an H store), and the returned H0.. are read after it.
fn check_caller(shape: &Shape, function: &ElfFunction, locs: &[Loc]) -> Result<(), String> {
    let trace = trace(function)?;
    let callee = format!("c_{}", shape.name);
    let sites: Vec<_> = trace.calls.iter().filter(|call| call.1 == callee).collect();
    let [(call, _, sp_call)] = sites.as_slice() else {
        return Err(format!(
            "expected one call to {callee}, found {}",
            sites.len()
        ));
    };
    let (call, sp_call) = (*call, *sp_call);
    for (p, loc) in shape.params.iter().zip(locs) {
        if let Loc::Fpr(r, n) = *loc {
            let view = p.fp_view().unwrap();
            for reg in r..r + n {
                // An earlier call's clobber is itself a write, so a value
                // set up before it fails here.
                match trace.last_write_before(reg, call) {
                    Some((_, actual)) if view_ok(view, actual) => {}
                    other => {
                        return Err(format!(
                            "argument register v{reg} ({view:?}) was last written as {other:?} before the call"
                        ));
                    }
                }
            }
        }
    }
    let area = stack_area(&shape.params, locs);
    let outgoing: Vec<(u32, &Mem)> = trace
        .mem
        .iter()
        .filter(|m| m.index < call && m.at >= sp_call && m.at < sp_call + i64::from(area.size))
        .map(|m| ((m.at - sp_call) as u32, m))
        .collect();
    for (at, m) in &outgoing {
        if m.load {
            return Err(format!(
                "word {} reads the outgoing argument area at +{at}",
                m.index
            ));
        }
        let end = at + m.bytes;
        if !area.slots.iter().any(|(s, e)| s <= at && end <= *e) {
            return Err(format!(
                "word {} writes +{at}..+{end}, outside every stack-argument slot",
                m.index
            ));
        }
        if m.fp == Some(V::H) && !area.halves.contains(at) {
            return Err(format!(
                "word {} is an H store at +{at}, which holds no f16",
                m.index
            ));
        }
    }
    let covered = |at: u32, bytes: u32| {
        (at..at + bytes).all(|byte| {
            outgoing
                .iter()
                .any(|(start, m)| *start <= byte && byte < start + m.bytes)
        })
    };
    for at in &area.scalar_halves {
        if !outgoing
            .iter()
            .any(|(start, m)| start == at && m.bytes == 2 && m.fp == Some(V::H))
        {
            return Err(format!(
                "the f16 stack argument at +{at} is not written by an H store"
            ));
        }
    }
    for at in &area.halves {
        if !covered(*at, 2) {
            return Err(format!("the HFA member at +{at} is not written"));
        }
    }
    for (at, bytes, fp) in &area.others {
        let written = outgoing
            .iter()
            .any(|(start, m)| start == at && m.bytes >= *bytes && m.fp == *fp);
        if !written {
            return Err(format!(
                "the {bytes}-byte stack argument at +{at} is not written by a {fp:?} store"
            ));
        }
    }
    for member in 0..return_registers(shape) {
        match trace.first_access_after(member, call) {
            Some((_, true, view)) if view_ok(V::H, view) => {}
            other => {
                return Err(format!(
                    "returned v{member} is first accessed after the call as {other:?}"
                ));
            }
        }
    }
    Ok(())
}

fn check_object(shapes: &[Shape], object: &[u8]) -> Result<(), String> {
    let functions = elf_functions(object);
    for shape in shapes {
        let locs = aapcs64_placement(&shape.params);
        let callee = format!("cg_{}", shape.name);
        let caller = format!("cg_call_{}", shape.name);
        check_callee(shape, &functions[&callee], &locs)
            .map_err(|error| format!("{callee}: {error}"))?;
        check_caller(shape, &functions[&caller], &locs)
            .map_err(|error| format!("{caller}: {error}"))?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// FEAT_FP16 instruction classifier (Arm ARM encoding tables, not the decoder)
// ---------------------------------------------------------------------------

/// Whether `w` is a scalar or Advanced SIMD half-precision data-processing
/// encoding that requires FEAT_FP16. Covered: scalar FP data-processing (1-
/// and 2-source, compare, conditional compare/select, immediate) and FP <->
/// integer/fixed-point conversions with `ftype = 0b11`, except FCVT from half
/// to single/double, which is base FP; FP 3-source with `ftype = 0b11`;
/// Advanced SIMD (vector and scalar) three-same FP16 and two-register-misc
/// FP16. Not covered: by-element and across-lanes FP16 forms.
fn requires_fp16(w: u32) -> bool {
    let half = (w >> 22) & 3 == 3;
    let scalar_fp = w & 0x7f20_0000 == 0x1e20_0000;
    let fixed_point = w & 0x7f20_0000 == 0x1e00_0000;
    let fcvt_from_half = w & 0xffff_7c00 == 0x1ee2_4000;
    let three_source = w & 0x7f00_0000 == 0x1f00_0000;
    let simd_three_same = w & 0x9f60_c400 == 0x0e40_0400;
    let simd_two_misc = w & 0x9f7e_0c00 == 0x0e78_0800;
    let scalar_three_same = w & 0xdf60_c400 == 0x5e40_0400;
    let scalar_two_misc = w & 0xdf7e_0c00 == 0x5e78_0800;
    ((scalar_fp || fixed_point || three_source) && half && !fcvt_from_half)
        || simd_three_same
        || simd_two_misc
        || scalar_three_same
        || scalar_two_misc
}

fn text_words(object: &[u8]) -> Vec<u32> {
    elf_functions(object)
        .into_values()
        .flat_map(|function| function.words)
        .collect()
}

// ---------------------------------------------------------------------------
// Host-neutral rows (object level; they run on every host)
// ---------------------------------------------------------------------------

/// The model reproduces placements written out by hand from the rules, and
/// the lowering's own AAPCS64 classifier agrees with it on every shape.
#[test]
fn aapcs64_model_pins_and_agrees_with_the_lowering_classifier() {
    use Loc::*;
    let by_name = |name: &str| shapes().into_iter().find(|s| s.name == name).unwrap();
    let pins: [(&str, Vec<Loc>); 5] = [
        (
            "h12",
            (0..8)
                .map(|r| Fpr(r, 1))
                .chain([Stack(0), Stack(8), Stack(16), Stack(24)])
                .collect(),
        ),
        (
            "mixed",
            vec![
                Gpr(1),
                Fpr(0, 1),
                Fpr(1, 1),
                Gpr(2),
                Fpr(2, 1),
                Fpr(3, 1),
                Gpr(3),
                Fpr(4, 1),
                Fpr(5, 1),
                Gpr(4),
                Fpr(6, 1),
                Fpr(7, 1),
                Gpr(5),
                Stack(0),
                Gpr(6),
                Gpr(7),
                Stack(8),
                Stack(16),
                Stack(24),
                Stack(32),
                Stack(40),
                Stack(48),
            ],
        ),
        (
            // HFA3 exactly fills H5-H7; everything after it is on the stack.
            "hfa3_p5",
            (0..5)
                .map(|r| Fpr(r, 1))
                .chain([Fpr(5, 3), Stack(0), Stack(8), Stack(16), Gpr(1)])
                .collect(),
        ),
        (
            // HFA3 is one register short: stack, NSRN = 8, so the following
            // f16 does not backfill H6/H7.
            "hfa3_p6",
            (0..6)
                .map(|r| Fpr(r, 1))
                .chain([Stack(0), Stack(8), Stack(16), Stack(24), Gpr(1)])
                .collect(),
        ),
        (
            "hfa4_p0",
            vec![Fpr(0, 4), Fpr(4, 1), Fpr(5, 2), Fpr(7, 1), Gpr(1)],
        ),
    ];
    for (name, expected) in pins {
        assert_eq!(aapcs64_placement(&by_name(name).params), expected, "{name}");
    }

    use trust_cg_lower::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation, PReg};
    use trust_cg_lower::types::Type;
    for shape in shapes() {
        let mut types = vec![Type::I64];
        types.extend(shape.params.iter().map(|p| match p {
            P::H => Type::F16,
            P::S => Type::F32,
            P::D => Type::F64,
            P::B => Type::I8,
            P::W16 => Type::I16,
            P::W32 => Type::I32,
            P::X64 => Type::I64,
            P::Hfa(n) => Type::Struct(vec![Type::F16; usize::from(*n)]),
        }));
        let classified = AppleAArch64ABI::classify_params_with(AArch64AbiVariant::Aapcs64, &types);
        let model = aapcs64_placement(&shape.params);
        for (index, ((p, loc), actual)) in shape
            .params
            .iter()
            .zip(&model)
            .zip(&classified[1..])
            .enumerate()
        {
            let views = |view: V| match view {
                V::H => AppleAArch64ABI::h_arg_regs(),
                V::S => AppleAArch64ABI::s_arg_regs(),
                _ => AppleAArch64ABI::d_arg_regs(),
            };
            let agrees = match (*loc, actual) {
                (Gpr(r), ArgLocation::Reg(reg)) => *reg == PReg::new(u16::from(r)),
                (Fpr(r, 1), ArgLocation::Reg(reg)) if !matches!(p, P::Hfa(_)) => {
                    *reg == views(p.fp_view().unwrap())[usize::from(r)]
                }
                (Fpr(r, n), ArgLocation::RegSequence(regs)) => {
                    regs.as_slice()
                        == &AppleAArch64ABI::h_arg_regs()[usize::from(r)..usize::from(r + n)]
                }
                (Stack(at), ArgLocation::Stack { offset, .. }) => i64::from(at) == *offset,
                _ => false,
            };
            assert!(
                agrees,
                "{} argument {index} ({p:?}): model {loc:?}, classifier {actual:?}",
                shape.name
            );
        }
    }
}

/// Every Linux object, both lanes and O0-O3, places every corpus argument
/// and result where the model says, through H/S/D transfers. The same
/// objects are rejected, in both directions, under a DarwinPCS-style packed
/// stack model and under a model without the NSRN clamp, for every shape
/// where those differ from AAPCS64.
#[test]
fn linux_objects_place_f16_in_h_registers_and_aapcs64_stack_slots_o0_through_o3() {
    let shapes = shapes();
    let differing = |rules| {
        shapes
            .iter()
            .filter(|shape| placement(&shape.params, rules) != aapcs64_placement(&shape.params))
            .count()
    };
    // Corpus pins: packing changes an offset in the 13 shapes with two or
    // more stack arguments (h12, mixed and 11 HFA shapes); backfill changes
    // the 3 HFA shapes left one H register short with a later f16 argument
    // (hfa2_p7, hfa3_p6, hfa4_p5).
    assert_eq!(
        (differing(Rules::PACKED), differing(Rules::BACKFILL)),
        (13, 3)
    );
    let mut checked = 0;
    let mut refuted = 0;
    for (label, object) in linux_objects(&shapes) {
        check_object(&shapes, &object).unwrap_or_else(|error| panic!("{label}: {error}"));
        checked += 2 * shapes.len();
        let functions = elf_functions(&object);
        for (model, rules) in [("packed", Rules::PACKED), ("backfill", Rules::BACKFILL)] {
            for shape in &shapes {
                let wrong = placement(&shape.params, rules);
                if wrong == aapcs64_placement(&shape.params) {
                    continue;
                }
                let callee = check_callee(shape, &functions[&format!("cg_{}", shape.name)], &wrong);
                let caller = check_caller(
                    shape,
                    &functions[&format!("cg_call_{}", shape.name)],
                    &wrong,
                );
                assert!(
                    callee.is_err() && caller.is_err(),
                    "{label} {model} {}: the wrong model passed (callee {callee:?}, caller {caller:?})",
                    shape.name
                );
                refuted += 2;
            }
        }
    }
    println!(
        "placement: {checked} functions ({} shapes x 2 directions x 4 opt levels x 2 lanes) match AAPCS64; {refuted} wrong-model checks rejected",
        shapes.len()
    );
}

/// The generated C oracle defines and declares every shape in both
/// directions, and its mismatched-prototype switch changes exactly the
/// shape's last `f16` argument to `float`.
#[test]
fn c_oracle_wires_every_shape_and_exactly_one_mismatched_argument() {
    let shapes = shapes();
    let c = c_driver(&shapes);
    let arguments = |prototype: &str| -> Vec<String> {
        let open = prototype.find('(').unwrap();
        let close = prototype.rfind(')').unwrap();
        prototype[open + 1..close]
            .split(", ")
            .map(str::to_owned)
            .collect()
    };
    for shape in &shapes {
        let name = &shape.name;
        assert!(
            c.contains(&format!(" c_{name}(unsigned char *rec, ")),
            "{name}"
        );
        assert!(
            c.contains(&format!("extern void cg_call_{name}(")),
            "{name}"
        );
        assert!(
            c.contains(&format!("static int run_{name}(int round)")),
            "{name}"
        );
        let guarded = c
            .split_once(&format!("#ifdef MISMATCH_{name}\n"))
            .unwrap()
            .1;
        let (mismatched, rest) = guarded.split_once("\n#else\n").unwrap();
        let correct = rest.split_once("\n#endif").unwrap().0;
        let (mismatched, correct) = (arguments(mismatched), arguments(correct));
        assert_eq!(correct.len(), shape.params.len() + 1, "{name}");
        let changed: Vec<usize> = (0..correct.len())
            .filter(|index| mismatched[*index] != correct[*index])
            .collect();
        assert_eq!(changed, [shape.last_f16() + 1], "{name}");
        assert_eq!(
            (
                correct[shape.last_f16() + 1].as_str(),
                mismatched[shape.last_f16() + 1].as_str()
            ),
            ("_Float16", "float"),
            "{name}"
        );
    }
}

/// The classifier flags the FEAT_FP16 forms and passes base-FP `f16`
/// transport; the baseline objects carry no FEAT_FP16 instruction; the
/// explicit-profile arithmetic object does.
#[test]
fn baseline_linux_objects_contain_no_feat_fp16_instruction() {
    for word in [
        0x1ee0_2800, // FADD H0, H0, H0
        0x1ee0_4000, // FMOV H0, H0
        0x1ee6_0000, // FMOV W0, H0
        0x9ee7_0000, // FMOV H0, X0
        0x1ef8_0000, // FCVTZS W0, H0
        0x1ee2_0000, // SCVTF H0, W0
        0x1ec2_fc00, // SCVTF H0, W0, #1 (fixed point)
        0x1fc0_0000, // FMADD H0, H0, H0, H0
        0x1ee0_2000, // FCMP H0, H0
        0x1ee0_0c00, // FCSEL H0, H0, H0, EQ
        0x1ee0_1000, // FMOV H0, #2.0
        0x4e40_1400, // FADD V0.8H, V0.8H, V0.8H
        0x4ef8_f800, // FABS V0.8H, V0.8H
        0x5e40_1c00, // FMULX H0, H0, H0
        0x5ef8_d800, // FCMEQ H0, H0, #0
    ] {
        assert!(
            requires_fp16(word),
            "{word:#010x} must be classified FEAT_FP16"
        );
    }
    for word in [
        0x1ee2_4000, // FCVT S0, H0
        0x1ee2_c000, // FCVT D0, H0
        0x1e23_c000, // FCVT H0, S0
        0x1e63_c000, // FCVT H0, D0
        0x7d40_0000, // LDR H0, [X0]
        0x7d00_0000, // STR H0, [X0]
        0x7c40_0000, // LDUR H0, [X0]
        0x4ea0_1c00, // MOV V0.16B, V0.16B
        0x1e20_2800, // FADD S0, S0, S0
        0x1e60_2800, // FADD D0, D0, D0
        0x4e20_d400, // FADD V0.4S, V0.4S, V0.4S
        0x1e20_4000, // FMOV S0, S0
        0xd65f_03c0, // RET
    ] {
        assert!(!requires_fp16(word), "{word:#010x} is base AArch64");
    }
    let shapes = shapes();
    let mut words = 0;
    for (label, object) in linux_objects(&shapes) {
        for word in text_words(&object) {
            words += 1;
            assert!(
                !requires_fp16(word),
                "{label}: FEAT_FP16 word {word:#010x} in the f16 transport corpus"
            );
        }
    }
    let arith = build_fp16_arith_module(linux_target_info());
    for opt in OPTS {
        let object = compile(&arith, LINUX, opt, Some(AArch64IsaProfile::FP16)).unwrap();
        assert!(
            text_words(&object).into_iter().any(requires_fp16),
            "{opt:?}: the explicit-profile FADD H object must carry a FEAT_FP16 word"
        );
    }
    println!("fp16 classifier: {words} corpus words, none FEAT_FP16");
}

/// FEAT_FP16 data processing over the same ABI boundary is refused by name
/// for the generic Linux profile at every opt level (while the transport
/// corpus is admitted) and admitted only by the explicit profile.
#[test]
fn f16_arithmetic_over_the_abi_refuses_by_name_without_the_fp16_profile() {
    let arith = build_fp16_arith_module(linux_target_info());
    for opt in OPTS {
        let error = compile(&arith, LINUX, opt, None).unwrap_err();
        assert!(
            error.contains("FEAT_FP16 is not admitted for FADD H"),
            "{opt:?}: {error}"
        );
        let error = compile(&arith, LINUX, opt, Some(AArch64IsaProfile::BASELINE)).unwrap_err();
        assert!(
            error.contains("FEAT_FP16 is not admitted for FADD H"),
            "{opt:?} explicit baseline: {error}"
        );
        compile(&arith, LINUX, opt, Some(AArch64IsaProfile::FP16))
            .unwrap_or_else(|error| panic!("{opt:?} explicit fp16: {error}"));
    }
}

/// A single-word mutation of one stack-argument load (callee) or store
/// (caller) in a real object fails the placement check with the moved
/// offset named.
#[test]
fn mutated_stack_argument_transfers_fail_the_placement_check() {
    let shapes = shapes();
    let h12 = shapes.iter().find(|s| s.name == "h12").unwrap();
    for (label, object) in linux_objects(&shapes) {
        for (function, error) in [("cg_h12", "+8"), ("cg_call_h12", "+8")] {
            let mutated = mutate_h12(&object, function);
            let functions = elf_functions(&mutated);
            let locs = aapcs64_placement(&h12.params);
            let result = if function == "cg_h12" {
                check_callee(h12, &functions[function], &locs)
            } else {
                check_caller(h12, &functions[function], &locs)
            };
            let message = result.expect_err(&format!("{label} {function}: mutation passed"));
            assert!(
                message.contains(error),
                "{label} {function}: unexpected rejection {message}"
            );
        }
    }
}

/// Retarget the H transfer of `h12`'s argument 9 (stack +8) to argument
/// 8's slot (+0) in `cg_h12` (a load) or argument 10's slot (+16) in
/// `cg_call_h12` (a store). Panics unless exactly one word matches.
fn mutate_h12(object: &[u8], function: &str) -> Vec<u8> {
    let functions = elf_functions(object);
    let target = &functions[function];
    let trace = trace(target).unwrap();
    let (reference, delta) = if function == "cg_h12" {
        (0i64, -8i64)
    } else {
        let call = trace.calls.iter().find(|c| c.1 == "c_h12").unwrap();
        (call.2, 8)
    };
    let hits: Vec<&Mem> = trace
        .mem
        .iter()
        .filter(|m| m.at == reference + 8 && m.fp == Some(V::H) && m.load == (function == "cg_h12"))
        .collect();
    assert_eq!(hits.len(), 1, "{function}: argument 9 transfers {hits:?}");
    let index = hits[0].index;
    let word = target.words[index];
    let mutated_word = match decode(word).unwrap() {
        Instruction::LoadStoreUnsignedImm(m) => {
            let imm = i64::from(m.imm12) + delta / 2;
            (word & !(0xfff << 10)) | ((imm as u32 & 0xfff) << 10)
        }
        Instruction::LoadStoreUnscaled(m) => {
            let imm = i64::from(m.imm9) + delta;
            (word & !(0x1ff << 12)) | ((imm as u32 & 0x1ff) << 12)
        }
        other => panic!("{function}: argument 9 moved by {other:?}"),
    };
    let mut mutated = object.to_vec();
    let at = target.file_offset + 4 * index;
    mutated[at..at + 4].copy_from_slice(&mutated_word.to_le_bytes());
    mutated
}

// ---------------------------------------------------------------------------
// Native rows: Linux GNU AArch64 only (the floor host executes them)
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::*;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Duration;

    const AT_HWCAP: std::ffi::c_ulong = 16;
    const HWCAP_FPHP: std::ffi::c_ulong = 1 << 9;
    const HWCAP_ASIMDHP: std::ffi::c_ulong = 1 << 10;

    unsafe extern "C" {
        fn getauxval(kind: std::ffi::c_ulong) -> std::ffi::c_ulong;
    }

    /// C driver for `cg_fadd`: every ordered pair of the binary16 patterns, as
    /// arguments 1 and 9 (the tenth argument is on the stack). The result must
    /// equal the host's FADD H bit for bit (inline assembly, same operand order,
    /// default FPCR) and, NaN-aware, the float-promoted C sum.
    const FADD_DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>
#include <string.h>
static const uint16_t PH[] = {
  0x0000, 0x8000, 0x0001, 0x8001, 0x03ff, 0x83ff, 0x0400, 0x3c00, 0xbc00,
  0x7bff, 0xfbff, 0x7c00, 0xfc00, 0x7e00, 0x7e01, 0x7fff, 0xfe5a, 0x7c01,
  0x7d55, 0xfd01, 0x3555, 0x5140, 0xc948 };
#define N ((int)(sizeof(PH) / sizeof(PH[0])))
extern _Float16 cg_fadd(_Float16, _Float16, _Float16, _Float16, _Float16,
                        _Float16, _Float16, _Float16, _Float16, _Float16);
static _Float16 h(uint16_t bits) { _Float16 v; memcpy(&v, &bits, 2); return v; }
static uint16_t b(_Float16 v) { uint16_t bits; memcpy(&bits, &v, 2); return bits; }
static int nan16(uint16_t x) { return (x & 0x7c00) == 0x7c00 && (x & 0x03ff); }
int main(void) {
  long checks = 0;
  for (int i = 0; i < N; i++) for (int j = 0; j < N; j++) {
    _Float16 x = h(PH[i]), y = h(PH[j]), fill = h(0x4242), hw;
    __asm__ volatile("fadd %h0, %h1, %h2" : "=w"(hw) : "w"(x), "w"(y));
    _Float16 promoted = (_Float16)((float)x + (float)y);
    uint16_t got = b(cg_fadd(fill, x, fill, fill, fill, fill, fill, fill, fill, y));
    checks++;
    if (got != b(hw) || (got != b(promoted) && !(nan16(got) && nan16(b(promoted))))) {
      printf("MISMATCH fadd %04x+%04x got=%04x hw=%04x promoted=%04x\n", PH[i], PH[j], got, b(hw), b(promoted));
      return 1;
    }
  }
  printf("fp16-fadd checks=%ld\n", checks);
  return 0;
}
"#;

    /// Scratch directory, or `TCG_F16_ABI_RETAIN` when a qualifying run
    /// retains its objects and drivers.
    fn workdir(tag: &str) -> (PathBuf, bool) {
        if let Ok(dir) = std::env::var("TCG_F16_ABI_RETAIN") {
            let dir = Path::new(&dir).join(tag);
            std::fs::create_dir_all(&dir).unwrap();
            return (dir, true);
        }
        (
            crate::fresh_dir::create(&format!("trust_cg_f16_abi_{tag}_")).keep(),
            false,
        )
    }

    fn link(dir: &Path, stem: &str, driver: &Path, object: &[u8], flags: &[&str]) -> PathBuf {
        let object_path = dir.join(format!("{stem}.o"));
        std::fs::write(&object_path, object).unwrap();
        let binary = dir.join(stem);
        let linked = Command::new("cc")
            .args(["-O2", "-fno-inline", "-Wall", "-Werror"])
            .args(flags)
            .arg(driver)
            .arg(&object_path)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("the host C compiler `cc` is required");
        assert!(
            linked.status.success(),
            "{stem}: link failed in {}:\n{}",
            dir.display(),
            String::from_utf8_lossy(&linked.stderr)
        );
        binary
    }

    fn run(binary: &Path, args: &[&str]) -> (i32, String) {
        let run = process::command_output_with_timeout(
            Command::new(binary).args(args),
            process::exec_timeout(Duration::from_secs(30)),
        )
        .unwrap();
        assert!(!run.timed_out, "{} timed out", binary.display());
        (
            run.output.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&run.output.stdout).into_owned(),
        )
    }

    fn host_has_fp16_hwcaps() -> bool {
        // SAFETY: getauxval has no preconditions; AT_HWCAP is always defined.
        let hwcap = unsafe { getauxval(AT_HWCAP) };
        hwcap & HWCAP_FPHP != 0 && hwcap & HWCAP_ASIMDHP != 0
    }

    /// The whole corpus, both directions, both lanes, O0-O3: every slot of
    /// every call agrees with GCC's `_Float16` ABI bit for bit.
    #[test]
    fn native_f16_and_hfa_boundaries_both_directions_o0_through_o3() {
        let shapes = shapes();
        let (dir, retain) = workdir("corpus");
        let driver = dir.join("driver.c");
        std::fs::write(&driver, c_driver(&shapes)).unwrap();
        let (mut calls, mut checks) = (0u64, 0u64);
        for (label, object) in linux_objects(&shapes) {
            let binary = link(&dir, &label, &driver, &object, &[]);
            let (code, stdout) = run(&binary, &[]);
            assert_eq!(code, 0, "{label}: {stdout} (retained {})", dir.display());
            let counts: Vec<u64> = stdout
                .trim()
                .rsplit(' ')
                .take(2)
                .map(|field| field.split('=').nth(1).unwrap().parse().unwrap())
                .collect();
            assert!(
                stdout.starts_with(&format!("f16-abi shapes={} ", shapes.len())),
                "{label}: {stdout}"
            );
            checks += counts[0];
            calls += counts[1];
            println!("{label}: {}", stdout.trim());
        }
        println!(
            "native f16 ABI ({}): {calls} calls, {checks} slot checks over {} shapes x 2 lanes x O0-O3",
            LINUX,
            shapes.len()
        );
        if !retain {
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    /// The oracle detects placement defects: the mutated objects fail at
    /// run time in the mutated direction, and a C prototype that spells one
    /// `f16` argument `float` is detected for every shape.
    #[test]
    fn native_mutated_objects_and_mismatched_prototypes_are_detected() {
        let shapes = shapes();
        let (dir, retain) = workdir("controls");
        let driver = dir.join("driver.c");
        std::fs::write(&driver, c_driver(&shapes)).unwrap();
        let module = build_module(&shapes, linux_target_info());
        let object = compile(&module, LINUX, OptLevel::O2, None).unwrap();
        for (function, direction) in [("cg_h12", "c-calls-cg"), ("cg_call_h12", "cg-calls-c")] {
            let binary = link(
                &dir,
                &format!("mutated_{function}"),
                &driver,
                &mutate_h12(&object, function),
                &[],
            );
            let (code, stdout) = run(&binary, &["h12"]);
            assert!(
                code == 1 && stdout.starts_with(&format!("MISMATCH h12 {direction} round=0")),
                "{function} mutation was not detected: exit {code}, {stdout}"
            );
        }
        let flags: Vec<String> = shapes
            .iter()
            .map(|shape| format!("-DMISMATCH_{}", shape.name))
            .collect();
        let flags: Vec<&str> = flags.iter().map(String::as_str).collect();
        let binary = link(&dir, "mismatched_prototypes", &driver, &object, &flags);
        for shape in &shapes {
            let (code, stdout) = run(&binary, &[&shape.name]);
            assert!(
                code == 1
                    && stdout.starts_with(&format!("MISMATCH {} c-calls-cg round=0", shape.name)),
                "{}: a float prototype for argument {} was not detected: exit {code}, {stdout}",
                shape.name,
                shape.last_f16()
            );
        }
        println!(
            "controls: 2 mutated objects and {} mismatched prototypes detected",
            shapes.len()
        );
        if !retain {
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    /// Host FEAT_FP16 from AT_HWCAP agrees with the runtime detection the
    /// compiler uses; the floor host must have it (the explicit lane is a
    /// failure, never a skip, without it). With it, `f16` arithmetic over a
    /// register and a stack argument executes under the explicit profile at
    /// O0-O3, equal to the hardware FADD H bit for bit.
    #[test]
    fn native_fp16_arithmetic_over_the_abi_runs_under_the_explicit_profile() {
        let hwcaps = host_has_fp16_hwcaps();
        assert_eq!(
            hwcaps,
            AArch64IsaProfile::FP16.is_supported_by_host(),
            "AT_HWCAP fphp/asimdhp and the runtime FEAT_FP16 detection disagree"
        );
        assert!(
            hwcaps,
            "this host lacks FEAT_FP16 (AT_HWCAP fphp/asimdhp): the explicit-fp16 lane cannot execute"
        );
        let (dir, retain) = workdir("fp16_fadd");
        let driver = dir.join("fadd.c");
        std::fs::write(&driver, FADD_DRIVER).unwrap();
        let arith = build_fp16_arith_module(linux_target_info());
        for opt in OPTS {
            let object = compile(&arith, LINUX, opt, Some(AArch64IsaProfile::FP16)).unwrap();
            let binary = link(
                &dir,
                &format!("fadd_{opt:?}"),
                &driver,
                &object,
                &["-march=armv8.2-a+fp16"],
            );
            let (code, stdout) = run(&binary, &[]);
            assert!(
                code == 0 && stdout.trim() == "fp16-fadd checks=529",
                "{opt:?}: exit {code}, {stdout}"
            );
        }
        println!("fp16 FADD H over the ABI: 529 pairs x O0-O3 bit-exact vs hardware");
        if !retain {
            std::fs::remove_dir_all(dir).unwrap();
        }
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
