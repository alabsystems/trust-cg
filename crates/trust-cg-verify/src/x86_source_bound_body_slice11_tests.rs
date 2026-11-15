// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 11 of the x86-64 source-bound body theorem: `I128` register pairs
//! and float bit patterns in SSE registers. An `I128` parameter, argument or
//! result travels in two INTEGER registers (low half first; a result in
//! RAX:RDX), and the selector computes its operations on 64-bit halves with
//! `add`/`adc`, `sub`/`sbb`, `mul`/`imul`, compare-and-`setcc` chains,
//! `cmov`s and shifts by CL. An `F32`/`F64` travels in the low bits of an SSE
//! register and is only moved, stored, loaded or reinterpreted (`movss`,
//! `movsd`, `movd`, `movq`); every floating-point operation stays outside.
//!
//! Fixtures are real: LIR from the trust-ir adapter and the machine stream
//! from the real x86-64 instruction selector (`super::select`). Negative
//! controls mutate that stream and must end as a typed mismatch, a refuted
//! theorem or an unsupported (uncredited) body, never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice11::` library gate). The
//! replay on AY and Clean and the verifier-credit tests are in
//! `slice11_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::*;
use trust_ir::{ICmpOp, UnOp};

// ---------------------------------------------------------------------------
// The sampler (test-only semantics check; never credit)
// ---------------------------------------------------------------------------

/// Slice 11's pooled words: two words per sample, related so that halves of
/// different values coincide (equal, equal but for the sign bit, adjacent,
/// complementary, or two edge words), while the earlier samplers draw every
/// input independently. An `I128` compare decides on its low halves only
/// when the high halves are equal, and a carry crosses into the high half
/// only at a low half's edge: needles an independent draw rarely reaches.
fn pool(seed: u64) -> [u64; 2] {
    const EDGES: [u64; 12] = [
        0,
        1,
        u64::MAX,
        u64::MAX - 1,
        1 << 63,
        (1 << 63) - 1,
        0xffff_ffff,
        0x8000_0000,
        0x5555_5555_5555_5555,
        0xaaaa_aaaa_aaaa_aaaa,
        0x3333_3333_3333_3333,
        0xcccc_cccc_cccc_cccc,
    ];
    let mut state = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(0x51);
    state ^= state >> 29;
    let first = if seed.is_multiple_of(3) {
        EDGES[(seed / 3 % 12) as usize]
    } else {
        state
    };
    let second = match (seed / 2) % 5 {
        0 => first ^ (1 << 63),
        1 => first.wrapping_add(1),
        2 => !first,
        3 => EDGES[(seed / 10 % 12) as usize],
        _ => first,
    };
    [first, second]
}

/// Whether the theorem holds at pooled sample `seed`: each free input is one
/// of the two pooled words, chosen by a bit of the seed.
pub(crate) fn holds_at_pool(obligation: &ProofObligation, seed: u64) -> bool {
    use crate::smt::{EvalEnv, EvalResult};
    let words = pool(seed);
    let mut env = EvalEnv::default();
    for (k, (name, width)) in free_inputs_of(obligation).into_iter().enumerate() {
        let pick = (seed.rotate_right((k as u32 * 5) % 64) >> 7) & 1;
        env.insert(name, crate::smt::mask(words[pick as usize], width));
    }
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not an equation")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        let EvalResult::Bv(value) = rhs.eval(&env) else {
            panic!("definition of {name} is not a bitvector")
        };
        env.insert(name.clone(), value);
    }
    if obligation.trust_ir_expr == E::bool_const(true) {
        matches!(obligation.aarch64_expr.eval(&env), EvalResult::Bool(true))
    } else {
        obligation.trust_ir_expr.eval(&env) == obligation.aarch64_expr.eval(&env)
    }
}

pub(crate) const POOL_SAMPLES: u64 = 4096;

/// Whether the theorem holds at every sample of slice 10's sampler (and
/// through it the earlier slices') and at every pooled sample.
pub(crate) fn theorem_holds(obligation: &ProofObligation) -> bool {
    super::slice10::theorem_holds(obligation)
        && (0..POOL_SAMPLES).all(|seed| holds_at_pool(obligation, seed))
}

/// Whether some sample refutes the theorem (the earlier samplers or a pooled
/// sample).
pub(crate) fn theorem_refuted(obligation: &ProofObligation) -> bool {
    super::slice10::theorem_refuted(obligation)
        || (0..POOL_SAMPLES).any(|seed| !holds_at_pool(obligation, seed))
}

/// Slice-11 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WideShape {
    // ---- (a) `I128` register pairs: `fn(a: u128, b: u128) -> u128`
    /// `u128::wrapping_add`: `add; adc`.
    AddU128,
    /// `u128::wrapping_sub`: `sub; sbb`.
    SubU128,
    /// `i128::wrapping_neg`: `0 - a`, `sub; sbb` from a zero pair.
    NegI128,
    /// `a ^ b`: two independent `xor`s.
    XorU128,
    /// `!a`: two `not`s.
    NotU128,
    /// `u128::wrapping_mul`: `mul` of the low halves, two `imul` cross
    /// products and two `add`s.
    MulU128,
    /// `a >> 64` (the amount an `I32` constant). Selected through the CL
    /// funnel with constant counts until OD-215; since, the folded move of
    /// the high half and a zero (`i128_const_shift` holds every amount).
    ShrU128By64,
    /// `a << 3`: `shl`/`shr` imm of the halves and an `or` (OD-215).
    ShlU128By3,
    /// `(a as i128) >> 100`: an arithmetic shift past the low half, `sar`
    /// imm of the high half by 36 and its sign fill `sar 63` (OD-215).
    SarI128By100,
    /// `a < b` (unsigned): `cmp`/`setcc` of the halves combined.
    LtU128,
    /// `a < b` (signed).
    LtI128,
    /// `a == b`.
    EqU128,
    /// `if c { a } else { b }` as a trust-ir `select`: two `cmov`s.
    SelectU128,
    /// `x as u128` from a `u64`.
    ZextU64,
    /// `x as i128` from an `i64`: the high half is the sign.
    SextI64,
    /// `a as u64`: the low half.
    TruncU128,
    /// `fn() -> u128 { (1 << 100) | 5 }`: an `Iconst128`.
    WideConst,
    /// `fn(a: i128) -> i128 { a & -2 }`: an `Iconst { ty: I128 }`, its high
    /// half the immediate's sign extension.
    NarrowConst,
    // ---- (b) calls
    /// `fn(a: u128) -> u128 { g(a) }`: an `I128` argument and result.
    CallU128,
    /// `fn(x: u64, a: u128) -> u64 { h(x, a) }`: the pair in RSI:RDX.
    CallAfterWord,
    // ---- (c) memory
    /// `fn(p: *mut u128, a: u128) { *p = a }`: two 8-byte stores.
    StoreU128,
    /// `fn(p: *const u128) -> u128 { *p }`: two 8-byte loads.
    LoadU128,
    /// `fn(a: u128, b: u128) -> u128 { let s = a; s + b }` through a private
    /// slot.
    SlotU128,
    // ---- (d) aggregates with an `I128` field
    /// `fn(a: [u128; 1]) -> u128 { a[0] }`.
    ParamArrayU128,
    /// `fn(a: u128) -> [u128; 1] { [a] }`.
    ResultArrayU128,
    // ---- (e) float bit patterns
    /// `f32::to_bits`: `movss; movd`.
    ToBitsF32,
    /// `f64::to_bits`: `movsd; movq`.
    ToBitsF64,
    /// `f32::from_bits`.
    FromBitsF32,
    /// `f64::from_bits`.
    FromBitsF64,
    /// `fn(x: f64) -> f64 { x }`.
    IdF64,
    /// `fn(x: f32) -> u8 { classify(x) }`: a float argument in XMM0.
    CallArgF32,
    /// `fn(x: u64) -> f64 { from_bits(x) }`: a float call result in XMM0.
    CallResultF64,
    /// `fn(p: *mut f32, x: f32) { *p = x }`: a `movss` store.
    StoreF32,
    /// `fn(p: *const f64) -> f64 { *p }`: a `movsd` load.
    LoadF64,
    /// `fn(a: u64, x: f64) -> (u64, f64) { (a, x) }`: RAX and XMM0.
    MixedPair,
    /// `fn(a: u64, x: f32, b: u64, y: f64) -> u64 { k(y, b, x, a) }`: the
    /// integer and SSE registers numbered apart.
    Interleaved,
}

/// Every slice-11 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_eleven_fixture_is_qualified`]
/// checks that none is left out).
pub(crate) const SLICE_ELEVEN: [WideShape; 36] = [
    WideShape::AddU128,
    WideShape::SubU128,
    WideShape::NegI128,
    WideShape::XorU128,
    WideShape::NotU128,
    WideShape::MulU128,
    WideShape::ShrU128By64,
    WideShape::ShlU128By3,
    WideShape::SarI128By100,
    WideShape::LtU128,
    WideShape::LtI128,
    WideShape::EqU128,
    WideShape::SelectU128,
    WideShape::ZextU64,
    WideShape::SextI64,
    WideShape::TruncU128,
    WideShape::WideConst,
    WideShape::NarrowConst,
    WideShape::CallU128,
    WideShape::CallAfterWord,
    WideShape::StoreU128,
    WideShape::LoadU128,
    WideShape::SlotU128,
    WideShape::ParamArrayU128,
    WideShape::ResultArrayU128,
    WideShape::ToBitsF32,
    WideShape::ToBitsF64,
    WideShape::FromBitsF32,
    WideShape::FromBitsF64,
    WideShape::IdF64,
    WideShape::CallArgF32,
    WideShape::CallResultF64,
    WideShape::StoreF32,
    WideShape::LoadF64,
    WideShape::MixedPair,
    WideShape::Interleaved,
];

impl WideShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s11_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }

    /// Whether the shape is a float one (section (e)).
    fn float(self) -> bool {
        use WideShape::*;
        matches!(
            self,
            ToBitsF32
                | ToBitsF64
                | FromBitsF32
                | FromBitsF64
                | IdF64
                | CallArgF32
                | CallResultF64
                | StoreF32
                | LoadF64
                | MixedPair
                | Interleaved
        )
    }
}

/// The LIR the trust-ir adapter produces for a slice-11 shape.
pub(crate) fn slice11_lir(shape: WideShape) -> Function {
    use WideShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice11");
    let u128x1 = {
        let element = builder.add_type(Ty::U128);
        Ty::Array(element, 1)
    };
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let g = declare("g", vec![Ty::U128], vec![Ty::U128]);
    let h = declare("h", vec![Ty::U64, Ty::U128], vec![Ty::U64]);
    let classify = declare("classify", vec![Ty::F32], vec![Ty::U8]);
    let from_bits = declare("from_bits", vec![Ty::U64], vec![Ty::F64]);
    let k = declare("k", vec![Ty::F64, Ty::U64, Ty::F32, Ty::U64], vec![Ty::U64]);
    let binary = |ty: Ty| (vec![ty.clone(), ty.clone()], vec![ty]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        AddU128 | SubU128 | XorU128 | MulU128 | SlotU128 => binary(Ty::U128),
        NegI128 | NarrowConst => (vec![Ty::I128], vec![Ty::I128]),
        NotU128 | ShrU128By64 | ShlU128By3 | CallU128 => (vec![Ty::U128], vec![Ty::U128]),
        SarI128By100 => (vec![Ty::I128], vec![Ty::I128]),
        LtU128 | EqU128 => (vec![Ty::U128, Ty::U128], vec![Ty::Bool]),
        LtI128 => (vec![Ty::I128, Ty::I128], vec![Ty::Bool]),
        SelectU128 => (vec![Ty::Bool, Ty::U128, Ty::U128], vec![Ty::U128]),
        ZextU64 => (vec![Ty::U64], vec![Ty::U128]),
        SextI64 => (vec![Ty::I64], vec![Ty::I128]),
        TruncU128 => (vec![Ty::U128], vec![Ty::U64]),
        WideConst => (vec![], vec![Ty::U128]),
        CallAfterWord => (vec![Ty::U64, Ty::U128], vec![Ty::U64]),
        StoreU128 => (vec![Ty::Ptr, Ty::U128], vec![]),
        LoadU128 => (vec![Ty::Ptr], vec![Ty::U128]),
        ParamArrayU128 => (vec![u128x1.clone()], vec![Ty::U128]),
        ResultArrayU128 => (vec![Ty::U128], vec![u128x1.clone()]),
        ToBitsF32 => (vec![Ty::F32], vec![Ty::U32]),
        ToBitsF64 => (vec![Ty::F64], vec![Ty::U64]),
        FromBitsF32 => (vec![Ty::U32], vec![Ty::F32]),
        FromBitsF64 => (vec![Ty::U64], vec![Ty::F64]),
        IdF64 => (vec![Ty::F64], vec![Ty::F64]),
        CallArgF32 => (vec![Ty::F32], vec![Ty::U8]),
        CallResultF64 => (vec![Ty::U64], vec![Ty::F64]),
        StoreF32 => (vec![Ty::Ptr, Ty::F32], vec![]),
        LoadF64 => (vec![Ty::Ptr], vec![Ty::F64]),
        MixedPair => (vec![Ty::U64, Ty::F64], vec![Ty::U64, Ty::F64]),
        Interleaved => (vec![Ty::U64, Ty::F32, Ty::U64, Ty::F64], vec![Ty::U64]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        AddU128 => {
            let sum = f.add(Ty::U128, args[0], args[1]);
            f.ret(vec![sum]);
        }
        SubU128 => {
            let difference = f.binop(BinOp::Sub, Ty::U128, args[0], args[1]);
            f.ret(vec![difference]);
        }
        NegI128 => {
            let negated = f.unop(UnOp::Neg, Ty::I128, args[0]);
            f.ret(vec![negated]);
        }
        XorU128 => {
            let mixed = f.binop(BinOp::Xor, Ty::U128, args[0], args[1]);
            f.ret(vec![mixed]);
        }
        NotU128 => {
            let not = f.unop(UnOp::Not, Ty::U128, args[0]);
            f.ret(vec![not]);
        }
        MulU128 => {
            let product = f.binop(BinOp::Mul, Ty::U128, args[0], args[1]);
            f.ret(vec![product]);
        }
        ShrU128By64 | ShlU128By3 | SarI128By100 => {
            let (op, ty, amount) = match shape {
                ShrU128By64 => (BinOp::LShr, Ty::U128, 64),
                ShlU128By3 => (BinOp::Shl, Ty::U128, 3),
                _ => (BinOp::AShr, Ty::I128, 100),
            };
            let amount = f.iconst(Ty::U32, amount);
            let shifted = f.binop(op, ty, args[0], amount);
            f.ret(vec![shifted]);
        }
        LtU128 | LtI128 | EqU128 => {
            let (op, ty) = match shape {
                LtU128 => (ICmpOp::Ult, Ty::U128),
                LtI128 => (ICmpOp::Slt, Ty::I128),
                _ => (ICmpOp::Eq, Ty::U128),
            };
            let holds = f.icmp(op, ty, args[0], args[1]);
            f.ret(vec![holds]);
        }
        SelectU128 => {
            let chosen = f.select(Ty::U128, args[0], args[1], args[2]);
            f.ret(vec![chosen]);
        }
        ZextU64 => {
            let wide = f.zext(Ty::U64, Ty::U128, args[0]);
            f.ret(vec![wide]);
        }
        SextI64 => {
            let wide = f.sext(Ty::I64, Ty::I128, args[0]);
            f.ret(vec![wide]);
        }
        TruncU128 => {
            let low = f.trunc(Ty::U128, Ty::U64, args[0]);
            f.ret(vec![low]);
        }
        WideConst => {
            let value = f.uconst(Ty::U128, (1u128 << 100) | 5);
            f.ret(vec![value]);
        }
        NarrowConst => {
            let mask = f.iconst(Ty::I128, -2);
            let masked = f.binop(BinOp::And, Ty::I128, args[0], mask);
            f.ret(vec![masked]);
        }
        CallU128 => {
            let result = f.call(g, vec![args[0]]);
            f.ret(vec![result]);
        }
        CallAfterWord => {
            let result = f.call(h, vec![args[0], args[1]]);
            f.ret(vec![result]);
        }
        StoreU128 | StoreF32 => {
            let ty = if shape == StoreU128 {
                Ty::U128
            } else {
                Ty::F32
            };
            f.store(ty, args[0], args[1]);
            f.ret(vec![]);
        }
        LoadU128 | LoadF64 => {
            let ty = if shape == LoadU128 { Ty::U128 } else { Ty::F64 };
            let value = f.load(ty, args[0]);
            f.ret(vec![value]);
        }
        SlotU128 => {
            let slot = f.alloca(Ty::U128);
            f.store(Ty::U128, slot, args[0]);
            let back = f.load(Ty::U128, slot);
            let sum = f.add(Ty::U128, back, args[1]);
            f.ret(vec![sum]);
        }
        ParamArrayU128 => {
            let field = f.extract_field(Ty::U128, args[0], 0);
            f.ret(vec![field]);
        }
        ResultArrayU128 => {
            // Its one field written as the rustc bridge writes an aggregate's
            // field since WS7.1 (`emit_aggregate_field_store`): the address
            // `Const 0`, `PtrToInt`, `Add`, `IntToPtr`, then a typed `Store`.
            // The store form of `insert_field` is invalid trust-ir and refused
            // by name.
            let storage = f.alloca(u128x1.clone());
            let offset = f.iconst(Ty::I64, 0);
            let base = f.cast(trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::I64, storage);
            let address = f.binop(BinOp::Add, Ty::I64, base, offset);
            let address = f.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, address);
            f.store(Ty::U128, address, args[0]);
            f.ret(vec![storage]);
        }
        ToBitsF32 | ToBitsF64 | FromBitsF32 | FromBitsF64 => {
            let (from, to) = match shape {
                ToBitsF32 => (Ty::F32, Ty::U32),
                ToBitsF64 => (Ty::F64, Ty::U64),
                FromBitsF32 => (Ty::U32, Ty::F32),
                _ => (Ty::U64, Ty::F64),
            };
            let bits = f.cast(CastOp::Bitcast, from, to, args[0]);
            f.ret(vec![bits]);
        }
        IdF64 => {
            f.ret(vec![args[0]]);
        }
        CallArgF32 => {
            let class = f.call(classify, vec![args[0]]);
            f.ret(vec![class]);
        }
        CallResultF64 => {
            let value = f.call(from_bits, vec![args[0]]);
            f.ret(vec![value]);
        }
        MixedPair => {
            f.ret(vec![args[0], args[1]]);
        }
        Interleaved => {
            let result = f.call(k, vec![args[3], args[2], args[1], args[0]]);
            f.ret(vec![result]);
        }
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn slice11_pair(shape: WideShape) -> (Function, X86ISelFunction) {
    let source = slice11_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_slice_eleven_shapes() -> Vec<WideShape> {
    use WideShape::*;
    let all = SLICE_ELEVEN.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            AddU128 | SubU128 | NegI128 | XorU128 | NotU128 | MulU128 | ShrU128By64
            | ShlU128By3 | SarI128By100 | LtU128 | LtI128 | EqU128 | SelectU128 | ZextU64
            | SextI64 | TruncU128 | WideConst | NarrowConst | CallU128 | CallAfterWord
            | StoreU128 | LoadU128 | SlotU128 | ParamArrayU128 | ResultArrayU128 | ToBitsF32
            | ToBitsF64 | FromBitsF32 | FromBitsF64 | IdF64 | CallArgF32 | CallResultF64
            | StoreF32 | LoadF64 | MixedPair | Interleaved => {}
        }
    }
    all
}

#[track_caller]
fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    source_bound_x86_body(source, machine, SYSV)
        .unwrap_or_else(|refusal| {
            panic!(
                "{what}: {refusal}\n{}{}",
                describe_lir(source),
                describe(machine)
            )
        })
        .obligation()
        .clone()
}

/// A wrong lowering whose theorem the owner builds without its exact affine
/// refusal must be refuted on samples (the replay refutes it on the
/// qualification host).
#[track_caller]
fn refuted(source: &Function, machine: &X86ISelFunction, what: &str) {
    let theorem = theorem_without_affine_refusal(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}\n{}", describe(machine)));
    assert!(
        theorem_refuted(&theorem),
        "{what}: the theorem must refute the wrong lowering\n{}",
        describe(machine)
    );
}

/// The walk ordinal of the first row satisfying `predicate`.
#[track_caller]
fn row_where(machine: &X86ISelFunction, predicate: impl Fn(&X86ISelInst) -> bool) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| predicate(inst(machine, *ordinal)))
        .unwrap_or_else(|| panic!("no such row\n{}", describe(machine)))
}

fn xmm_preg(n: u16) -> O {
    preg(XMM_ROOTS.start + n)
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

#[test]
fn owner_builds_for_every_slice_eleven_shape_and_covers_every_value_row() {
    for shape in SLICE_ELEVEN {
        let (source, machine) = slice11_pair(shape);
        let body = source_bound_x86_body(&source, &machine, SYSV).unwrap_or_else(|refusal| {
            panic!(
                "{shape:?}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        let expected: Vec<usize> = rows(&machine)
            .into_iter()
            .filter(|(_, block, index)| {
                let opcode = machine.blocks[block].insts[*index].opcode;
                !opcode.is_pseudo()
                    && !matches!(
                        opcode,
                        X86Opcode::Jmp
                            | X86Opcode::Ret
                            | X86Opcode::Call
                            | X86Opcode::CallR
                            | X86Opcode::Ud2
                    )
            })
            .map(|(ordinal, _, _)| ordinal)
            .collect();
        assert_eq!(
            body.bound_rows(),
            expected,
            "{shape:?}\n{}",
            describe(&machine)
        );
        let entries = free_inputs_of(body.obligation());
        assert_eq!(
            owner_check(&source, &machine, body.obligation(), &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(body.obligation().is_genuinely_proven(), "{shape:?}");
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
        // Every name the theorem defines or declares is at most 64 bits
        // wide ([`name_source_value`]).
        assert!(
            body.obligation()
                .inputs
                .iter()
                .all(|(_, width)| *width <= 64),
            "{shape:?}: {:?}",
            body.obligation().inputs
        );
    }
}

#[test]
fn slice_eleven_theorems_hold_on_samples() {
    for shape in SLICE_ELEVEN {
        let (source, machine) = slice11_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_ELEVEN`]: every fixture whose real selection the owner admits with
/// a theorem that holds must be in it.
#[test]
fn every_admitted_slice_eleven_fixture_is_qualified() {
    for shape in all_slice_eleven_shapes() {
        let (source, machine) = slice11_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV)
            .is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(SLICE_ELEVEN.contains(&shape), holds, "{shape:?}");
    }
}

/// Each fixture holds the rows the shape exists for: `adc`/`sbb` for the
/// `I128` add and subtract, the folded immediate rows for the constant
/// `I128` shifts (OD-215: no shift by CL, no `cmov`; slice 20's variable
/// shifts keep the one-operand shifts by CL), and SSE moves for every float
/// shape.
#[test]
fn slice_eleven_fixtures_have_the_expected_pre_ra_rows() {
    use WideShape::*;
    for shape in all_slice_eleven_shapes() {
        let (source, machine) = slice11_pair(shape);
        let text = format!("{shape:?}\n{}{}", describe_lir(&source), describe(&machine));
        let has = |opcode: X86Opcode| !find(&machine, opcode).is_empty();
        match shape {
            AddU128 => assert!(has(X86Opcode::AdcRR), "{text}"),
            SubU128 | NegI128 => assert!(has(X86Opcode::SbbRR), "{text}"),
            ShrU128By64 | ShlU128By3 | SarI128By100 => {
                for opcode in [
                    X86Opcode::ShlRR,
                    X86Opcode::ShrRR,
                    X86Opcode::SarRR,
                    X86Opcode::Cmovcc,
                ] {
                    assert!(!has(opcode), "{opcode:?}: {text}");
                }
                match shape {
                    ShrU128By64 => {
                        assert!(!has(X86Opcode::ShrRI) && !has(X86Opcode::ShlRI), "{text}")
                    }
                    ShlU128By3 => assert!(
                        has(X86Opcode::ShlRI) && has(X86Opcode::ShrRI) && has(X86Opcode::OrRR),
                        "{text}"
                    ),
                    _ => assert_eq!(find(&machine, X86Opcode::SarRI).len(), 2, "{text}"),
                }
            }
            MulU128 => assert!(has(X86Opcode::Mul), "{text}"),
            _ if shape.float() => assert!(
                has(X86Opcode::MovssRR)
                    || has(X86Opcode::MovsdRR)
                    || has(X86Opcode::MovssMR)
                    || has(X86Opcode::MovsdRM)
                    || has(X86Opcode::MovdToXmm)
                    || has(X86Opcode::MovqToXmm),
                "{text}"
            ),
            _ => {}
        }
    }
}

/// The observables: an `I128` result is two 64-bit items (RAX, then RDX),
/// an `I128` argument two, and a float lane its own width.
#[test]
fn the_observables_carry_both_halves_and_the_float_bits() {
    let widths = |shape: WideShape| {
        let (source, machine) = slice11_pair(shape);
        observable_items(&owned_plain_theorem(
            &source,
            &machine,
            &format!("{shape:?}"),
        ))
        .iter()
        .map(|(source, _)| source.bv_width())
        .collect::<Vec<_>>()
    };
    assert_eq!(widths(WideShape::AddU128), [64, 64]);
    // `g(a)`: the result's halves, then the argument's.
    assert_eq!(widths(WideShape::CallU128), [64, 64, 64, 64]);
    // `h(x, a)`: the result, then `x` and both halves of `a`.
    assert_eq!(widths(WideShape::CallAfterWord), [64, 64, 64, 64]);
    assert_eq!(widths(WideShape::ToBitsF32), [32]);
    assert_eq!(widths(WideShape::FromBitsF32), [32]);
    assert_eq!(widths(WideShape::MixedPair), [64, 64]);
    // `classify(x)`: the `u8` result, then the 32-bit float argument.
    assert_eq!(widths(WideShape::CallArgF32), [8, 32]);
}

// ---------------------------------------------------------------------------
// The System V classes: the verify-owned assignment against the selector's
// ---------------------------------------------------------------------------

/// `fn(x: T) -> T { g(x) }` and `fn(w: u64, x: T, y: f64) -> T { g2(y, x, w) }`
/// for every scalar class the slice admits: the selector's own argument and
/// result registers (the call row's metadata, which the walk compares with
/// [`argument_roots`] and [`result_roots`]) are the verify-owned ones, and
/// the owner builds a theorem that holds. A mixed `{f64, i64}` aggregate (an
/// SSE eightbyte beside an INTEGER one) and a float aggregate are classified
/// SSE by the selector and refused by name by the owner.
#[test]
fn the_verify_owned_classes_agree_with_the_selector() {
    // (A `bool` forwarded from a `bool` parameter stays outside: slice 3.)
    let scalar_types = [
        Ty::U128,
        Ty::I128,
        Ty::F32,
        Ty::F64,
        Ty::U64,
        Ty::U32,
        Ty::U8,
    ];
    let mut checked = 0;
    for ty in &scalar_types {
        for wrapped in [false, true] {
            let mut builder = ModuleBuilder::new("x86_source_bound_body_slice11_classes");
            let (params, call_params): (Vec<Ty>, Vec<Ty>) = if wrapped {
                (
                    vec![Ty::U64, ty.clone(), Ty::F64],
                    vec![Ty::F64, ty.clone(), Ty::U64],
                )
            } else {
                (vec![ty.clone()], vec![ty.clone()])
            };
            let callee = {
                let callee_ty = builder.add_func_type(call_params, vec![ty.clone()]);
                builder.declare_function("g", callee_ty)
            };
            let signature = builder.add_func_type(params.clone(), vec![ty.clone()]);
            let name = format!("s11_class_{}", checked);
            let mut f = builder.function(&name, signature);
            let entry = f.create_block();
            let args: Vec<_> = params
                .iter()
                .map(|param| f.add_block_param(entry, param.clone()))
                .collect();
            f.switch_to_block(entry);
            let call_args = if wrapped {
                vec![args[2], args[1], args[0]]
            } else {
                vec![args[0]]
            };
            let result = f.call(callee, call_args);
            f.ret(vec![result]);
            f.build();
            let module = builder.build().expect("ModuleBuilder::build: test fixture");
            let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &module,
                trust_cg_lower::GuardCarrierArch::X86_64,
                trust_cg_lower::TlsDialect::default(),
                &crate::license_test_support::permit_unlicensed(),
            )
            .expect("translates")
            .into_iter()
            .map(|(function, _)| function)
            .find(|function| function.name == name)
            .expect("translated");
            let machine = select(&source, X86CallAbi::SystemV);
            let body = admitted_body(&source).unwrap_or_else(|refusal| {
                panic!(
                    "{ty:?} wrapped={wrapped}: {refusal}\n{}",
                    describe_lir(&source)
                )
            });
            let program = &body.paths[0];
            // The selector's call row declares exactly the verify-owned
            // registers (compared again, per compile, by the walk).
            let call = row_where(&machine, |i| i.opcode == X86Opcode::Call);
            let row = inst(&machine, call);
            let declared: Vec<u16> = row
                .call_arg_regs
                .iter()
                .map(|arg| arg.reg.encoding())
                .collect();
            assert_eq!(
                declared,
                program.calls[0].arg_roots,
                "{ty:?} wrapped={wrapped}\n{}",
                describe(&machine)
            );
            let results: Vec<u16> = row
                .call_result_regs
                .as_ref()
                .expect("result registers")
                .iter()
                .map(|result| result.reg.encoding())
                .collect();
            let lanes: Vec<u16> = program.calls[0]
                .results
                .iter()
                .map(|lane| lane.root)
                .collect();
            assert_eq!(results, lanes, "{ty:?} wrapped={wrapped}");
            // The parameters arrive where the verify-owned table puts them:
            // the selector's entry copies read exactly those registers.
            let entry_reads: Vec<u16> = rows(&machine)
                .into_iter()
                .take_while(|(ordinal, _, _)| inst(&machine, *ordinal).opcode != X86Opcode::Call)
                .filter_map(
                    |(ordinal, _, _)| match inst(&machine, ordinal).operands.as_slice() {
                        [O::VReg(_), O::PReg(preg)] => Some(match preg.encoding() {
                            // A 32-, 16- or 8-bit alias names its 64-bit root.
                            alias @ 16..=63 => alias % 16,
                            root => root,
                        }),
                        _ => None,
                    },
                )
                .collect();
            let param_roots: Vec<u16> = program
                .params
                .iter()
                .flat_map(|param| param.roots.iter().copied())
                .collect();
            assert_eq!(entry_reads, param_roots, "{ty:?} wrapped={wrapped}");
            let obligation = owner(&source, &machine, &format!("{ty:?} wrapped={wrapped}"));
            assert!(theorem_holds(&obligation), "{ty:?} wrapped={wrapped}");
            checked += 1;
        }
    }
    assert_eq!(checked, 14);
    // Aggregates with a float field: the selector classifies them SSE (or
    // SSE beside INTEGER), and the owner refuses them by name.
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice11_sse_aggregates");
    let mixed = Ty::Struct(
        builder.add_struct(StructDef {
            origin: None,
            id: StructId::new(0),
            name: "Mixed".into(),
            fields: [Ty::F64, Ty::I64]
                .into_iter()
                .enumerate()
                .map(|(i, ty)| FieldDef {
                    name: format!("f{i}"),
                    ty,
                    offset: None,
                })
                .collect(),
            size: None,
            align: None,
            repr: StructRepr::C,
        }),
    );
    let floats = {
        let element = builder.add_type(Ty::F32);
        Ty::Array(element, 2)
    };
    let mut names = Vec::new();
    for (index, ty) in [mixed, floats].into_iter().enumerate() {
        let callee = {
            let callee_ty = builder.add_func_type(vec![ty.clone()], vec![Ty::U64]);
            builder.declare_function(format!("take_{index}"), callee_ty)
        };
        let signature = builder.add_func_type(vec![ty.clone()], vec![Ty::U64]);
        let name = format!("s11_sse_aggregate_{index}");
        let mut f = builder.function(&name, signature);
        let entry = f.create_block();
        let x = f.add_block_param(entry, ty.clone());
        f.switch_to_block(entry);
        let result = f.call(callee, vec![x]);
        f.ret(vec![result]);
        f.build();
        names.push(name);
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let mut refused = 0;
    for (function, _) in trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("translates")
    {
        if !names.contains(&function.name) {
            continue;
        }
        // The selector passes the aggregate's SSE eightbyte in XMM0.
        let machine = select(&function, X86CallAbi::SystemV);
        let call = row_where(&machine, |i| i.opcode == X86Opcode::Call);
        assert!(
            inst(&machine, call)
                .call_arg_regs
                .iter()
                .any(|arg| XMM_ROOTS.contains(&arg.reg.encoding())),
            "{}: the selector passes an SSE eightbyte\n{}",
            function.name,
            describe(&machine)
        );
        let refusal = match admitted_body(&function) {
            Ok(_) => panic!("{}: an SSE aggregate is admitted", function.name),
            Err(refusal) => refusal.to_string(),
        };
        assert!(refusal.contains("an SSE eightbyte"), "{refusal}");
        refused += 1;
    }
    assert_eq!(refused, 2);
}

// ---------------------------------------------------------------------------
// The semantics, against the hardware and trust-ir definitions (no solver)
// ---------------------------------------------------------------------------

/// Concrete 64-bit halves of the sampler's kind: edges, repeating patterns
/// and random words.
fn halves() -> Vec<u64> {
    let mut values = vec![
        0,
        1,
        2,
        u64::MAX,
        u64::MAX - 1,
        1 << 63,
        (1 << 63) - 1,
        0x5555_5555_5555_5555,
        0xaaaa_aaaa_aaaa_aaaa,
    ];
    let mut state = 0x2545_f491_4f6c_dd1du64;
    for _ in 0..12 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        values.push(state);
    }
    values
}

/// The `I128` fixtures compute trust-ir's 128-bit result, through the real
/// selector's halves: each theorem holds, and its source side is Rust's
/// `u128`/`i128` arithmetic at every pair of edge halves (the machine side
/// equal to it is the theorem).
#[test]
fn the_i128_fixtures_state_rusts_128_bit_arithmetic() {
    use crate::smt::EvalEnv;
    type WideArithmeticCase = (WideShape, fn(u128, u128) -> u128);
    let values = halves();
    let cases: [WideArithmeticCase; 8] = [
        (WideShape::AddU128, |a, b| a.wrapping_add(b)),
        (WideShape::SubU128, |a, b| a.wrapping_sub(b)),
        (WideShape::XorU128, |a, b| a ^ b),
        (WideShape::MulU128, |a, b| a.wrapping_mul(b)),
        (WideShape::ShrU128By64, |a, _| a >> 64),
        (WideShape::ShlU128By3, |a, _| a << 3),
        (WideShape::SarI128By100, |a, _| ((a as i128) >> 100) as u128),
        // `x as i128` of the low half (RSI is not a parameter here).
        (WideShape::SextI64, |a, _| a as u64 as i64 as i128 as u128),
    ];
    for (shape, expected) in cases {
        let (source, machine) = slice11_pair(shape);
        // Each half's item as built (slice 18's spelling): slice 19's
        // spelling drops the low half's, an identity once `addlo` applies.
        let obligation = with_normal_groups(normal::Groups::NONE, || {
            owner(&source, &machine, &format!("{shape:?}"))
        });
        let unary = matches!(
            shape,
            WideShape::ShrU128By64
                | WideShape::ShlU128By3
                | WideShape::SarI128By100
                | WideShape::SextI64
        );
        for (k, &a_lo) in values.iter().enumerate() {
            let (a_hi, b_lo, b_hi) = (
                values[(k * 7 + 3) % values.len()],
                values[(k * 5 + 1) % values.len()],
                values[(k * 3 + 2) % values.len()],
            );
            let mut fixed = vec![("e_rdi", a_lo), ("e_rsi", a_hi)];
            if !unary {
                fixed.extend([("e_rdx", b_lo), ("e_rcx", b_hi)]);
            }
            let mut env = EvalEnv::default();
            for (name, value) in &fixed {
                env.insert((*name).into(), *value);
            }
            let a = (u128::from(a_hi) << 64) | u128::from(a_lo);
            let b = (u128::from(b_hi) << 64) | u128::from(b_lo);
            let want = expected(a, b);
            let items = observable_items(&obligation);
            let premises = evaluate_premises(&obligation, &fixed);
            let got_lo = eval_word(&items[0].0, &premises);
            let got_hi = eval_word(&items[1].0, &premises);
            assert_eq!(
                (u128::from(got_hi) << 64) | u128::from(got_lo),
                want,
                "{shape:?} a={a:#x} b={b:#x}"
            );
            assert!(
                super::sides_agree_with(&obligation, k as u64, &fixed),
                "{shape:?} a={a:#x} b={b:#x}"
            );
            let _ = env;
        }
    }
}

/// The one spelling of a shift by a constant ([`ShiftOp::by_constant`], an
/// arithmetic one a sign extension of the kept bits) is Rust's shift at
/// every width the lane has, 8 to 128 bits, and every amount below it.
#[test]
fn shifts_by_a_constant_are_rusts() {
    use crate::smt::{EvalEnv, EvalResult};
    let values: Vec<u128> = halves()
        .into_iter()
        .flat_map(|low| [u128::from(low), (u128::from(low) << 64) | u128::from(!low)])
        .collect();
    for bits in [8u32, 16, 32, 64, 128] {
        let mask = if bits == 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        for x in &values {
            let x = x & mask;
            for amount in 0..bits {
                let mut env = EvalEnv::default();
                let value = if bits == 128 {
                    env.insert("hi".into(), (x >> 64) as u64);
                    env.insert("lo".into(), x as u64);
                    E::var("hi", 64).concat(E::var("lo", 64))
                } else {
                    env.insert("x".into(), x as u64);
                    E::var("x", bits)
                };
                for op in [ShiftOp::Shl, ShiftOp::Lshr, ShiftOp::Ashr] {
                    let signed = if bits == 128 {
                        x as i128
                    } else {
                        ((x << (128 - bits)) as i128) >> (128 - bits)
                    };
                    let expected = match op {
                        ShiftOp::Shl => (x << amount) & mask,
                        ShiftOp::Lshr => x >> amount,
                        ShiftOp::Ashr => (signed >> amount) as u128 & mask,
                    };
                    let found = match op.by_constant(value.clone(), amount).eval(&env) {
                        EvalResult::Bv(value) => u128::from(value),
                        EvalResult::Bv128(value) => value,
                        other => panic!("{other:?}"),
                    };
                    assert_eq!(found, expected, "{op:?} {bits} {x:#x} {amount}");
                }
            }
        }
    }
}

/// Every premise evaluated in order with the named free inputs fixed and
/// every other free input 0.
pub(crate) fn evaluate_premises(
    obligation: &ProofObligation,
    fixed: &[(&str, u64)],
) -> crate::smt::EvalEnv {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    for (name, width) in free_inputs_of(obligation) {
        let value = fixed
            .iter()
            .find(|(fixed, _)| *fixed == name)
            .map_or(0, |(_, value)| *value);
        env.insert(name, crate::smt::mask(value, width));
    }
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not an equation")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        let EvalResult::Bv(value) = rhs.eval(&env) else {
            panic!("definition of {name} is not a word")
        };
        env.insert(name.clone(), value);
    }
    env
}

pub(crate) fn eval_word(expr: &E, env: &crate::smt::EvalEnv) -> u64 {
    match expr.eval(env) {
        crate::smt::EvalResult::Bv(value) => value,
        other => panic!("{expr} is not a <= 64-bit bitvector: {other:?}"),
    }
}

/// `adc` and `sbb` (Intel SDM): `a + b + CF` and `a - (b + CF)` at the
/// operand width, CF the carry or borrow of the `add`/`sub` before them.
#[test]
fn adc_and_sbb_carry_between_the_halves() {
    let values = halves();
    for (shape, op) in [
        (
            WideShape::AddU128,
            u128::wrapping_add as fn(u128, u128) -> u128,
        ),
        (WideShape::SubU128, u128::wrapping_sub),
    ] {
        let (source, machine) = slice11_pair(shape);
        // Each half's item as built (slice 18's spelling): slice 19's
        // spelling drops the low half's, an identity once `addlo` applies.
        let obligation = with_normal_groups(normal::Groups::NONE, || {
            owner(&source, &machine, &format!("{shape:?}"))
        });
        for &a_lo in &values {
            for &b_lo in &values {
                // The high halves 0: the high result is the carry or borrow
                // alone (all ones for a borrow).
                let fixed = [("e_rdi", a_lo), ("e_rsi", 0), ("e_rdx", b_lo), ("e_rcx", 0)];
                let env = evaluate_premises(&obligation, &fixed);
                let items = observable_items(&obligation);
                let want = op(u128::from(a_lo), u128::from(b_lo));
                assert_eq!(eval_word(&items[0].1, &env), want as u64, "{shape:?}");
                assert_eq!(
                    eval_word(&items[1].1, &env),
                    (want >> 64) as u64,
                    "{shape:?} {a_lo:#x} {b_lo:#x}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Wrong lowerings (controls): never credited
// ---------------------------------------------------------------------------

/// Each wrong lowering of a slice-11 row the owner binds, with the fixture it
/// mutates. Every one changes what a caller or callee can observe for some
/// input (the robustness probe's independent interpreter agrees), so its
/// theorem must be refuted; `slice11_qualification` replays each to an AY
/// counterexample.
pub(crate) fn slice_eleven_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // The carry dropped: `add` where the selector adds the high halves with
    // `adc`.
    let (source, mut machine) = slice11_pair(WideShape::AddU128);
    let adc = row_where(&machine, |i| i.opcode == X86Opcode::AdcRR);
    inst_mut(&mut machine, adc).opcode = X86Opcode::AddRR;
    inst_mut(&mut machine, adc).flags = X86Opcode::AddRR.default_flags();
    cases.push(("AddU128/adc-as-add", source, machine));
    // The borrow dropped.
    let (source, mut machine) = slice11_pair(WideShape::SubU128);
    let sbb = row_where(&machine, |i| i.opcode == X86Opcode::SbbRR);
    inst_mut(&mut machine, sbb).opcode = X86Opcode::SubRR;
    inst_mut(&mut machine, sbb).flags = X86Opcode::SubRR.default_flags();
    cases.push(("SubU128/sbb-as-sub", source, machine));
    // A borrow added: `sbb` where the high halves add.
    let (source, mut machine) = slice11_pair(WideShape::AddU128);
    let adc = row_where(&machine, |i| i.opcode == X86Opcode::AdcRR);
    inst_mut(&mut machine, adc).opcode = X86Opcode::SbbRR;
    cases.push(("AddU128/adc-as-sbb", source, machine));
    // The subtraction's operands swapped in the high half only.
    let (source, mut machine) = slice11_pair(WideShape::SubU128);
    let sbb = row_where(&machine, |i| i.opcode == X86Opcode::SbbRR);
    inst_mut(&mut machine, sbb).operands.swap(1, 2);
    cases.push(("SubU128/high-swapped", source, machine));
    // The halves of the result swapped: the high half in RAX.
    let (source, mut machine) = slice11_pair(WideShape::XorU128);
    let to_rax = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR && i.operands.first() == Some(&preg(RAX))
    });
    let to_rdx = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR && i.operands.first() == Some(&preg(RDX))
    });
    let (low, high) = (
        inst(&machine, to_rax).operands[1].clone(),
        inst(&machine, to_rdx).operands[1].clone(),
    );
    inst_mut(&mut machine, to_rax).operands[1] = high;
    inst_mut(&mut machine, to_rdx).operands[1] = low;
    cases.push(("XorU128/halves-swapped", source, machine));
    // The parameter's halves read from swapped registers.
    let (source, mut machine) = slice11_pair(WideShape::NotU128);
    let from_rdi = row_where(&machine, |i| i.operands.get(1) == Some(&preg(RDI)));
    let from_rsi = row_where(&machine, |i| i.operands.get(1) == Some(&preg(RSI)));
    inst_mut(&mut machine, from_rdi).operands[1] = preg(RSI);
    inst_mut(&mut machine, from_rsi).operands[1] = preg(RDI);
    cases.push(("NotU128/parameter-halves-swapped", source, machine));
    // A negation's high half without the borrow.
    let (source, mut machine) = slice11_pair(WideShape::NegI128);
    let sbb = row_where(&machine, |i| i.opcode == X86Opcode::SbbRR);
    inst_mut(&mut machine, sbb).opcode = X86Opcode::SubRR;
    inst_mut(&mut machine, sbb).flags = X86Opcode::SubRR.default_flags();
    cases.push(("NegI128/no-borrow", source, machine));
    // An unsigned compare of the high halves where the source is signed.
    let (source, mut machine) = slice11_pair(WideShape::LtI128);
    let setl = row_where(&machine, |i| {
        i.opcode == X86Opcode::Setcc
            && i.operands.get(1) == Some(&O::CondCode(trust_cg_ir::X86CondCode::L))
    });
    inst_mut(&mut machine, setl).operands[1] = O::CondCode(trust_cg_ir::X86CondCode::B);
    cases.push(("LtI128/unsigned-high", source, machine));
    // A signed compare of the low halves (always unsigned).
    let (source, mut machine) = slice11_pair(WideShape::LtI128);
    let setb = row_where(&machine, |i| {
        i.opcode == X86Opcode::Setcc
            && i.operands.get(1) == Some(&O::CondCode(trust_cg_ir::X86CondCode::B))
    });
    inst_mut(&mut machine, setb).operands[1] = O::CondCode(trust_cg_ir::X86CondCode::L);
    cases.push(("LtI128/signed-low", source, machine));
    // Equality of the low halves alone.
    let (source, mut machine) = slice11_pair(WideShape::EqU128);
    let and = row_where(&machine, |i| i.opcode == X86Opcode::AndRR);
    let low = inst(&machine, and).operands[2].clone();
    inst_mut(&mut machine, and).operands[1] = low;
    cases.push(("EqU128/low-half-only", source, machine));
    // A sign extension whose high half is zero.
    let (source, mut machine) = slice11_pair(WideShape::SextI64);
    let sar = row_where(&machine, |i| i.opcode == X86Opcode::SarRI);
    inst_mut(&mut machine, sar).opcode = X86Opcode::ShrRI;
    cases.push(("SextI64/high-zero-extended", source, machine));
    // A wide constant's high half wrong.
    let (source, mut machine) = slice11_pair(WideShape::WideConst);
    let high = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRI && i.operands[1] == O::Imm(1 << 36)
    });
    inst_mut(&mut machine, high).operands[1] = O::Imm(1 << 35);
    cases.push(("WideConst/high-half", source, machine));
    // An `Iconst { ty: I128, imm: -2 }` whose high half is zero-extended.
    let (source, mut machine) = slice11_pair(WideShape::NarrowConst);
    let high = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRI && i.operands[1] == O::Imm(-1)
    });
    inst_mut(&mut machine, high).operands[1] = O::Imm(0);
    cases.push(("NarrowConst/high-zero", source, machine));
    // The constant shift's low half moved from the low half of the operand
    // (the fold's `mov lo', hi` reading the wrong half; until OD-215 this
    // case was the CL funnel's spill count off by one).
    let (source, mut machine) = slice11_pair(WideShape::ShrU128By64);
    let from_rdi = row_where(&machine, |i| i.operands.get(1) == Some(&preg(RDI)));
    let from_rsi = row_where(&machine, |i| i.operands.get(1) == Some(&preg(RSI)));
    let (low, high) = (
        inst(&machine, from_rdi).operands[0].clone(),
        inst(&machine, from_rsi).operands[0].clone(),
    );
    let mov = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR && i.operands.get(1) == Some(&high)
    });
    inst_mut(&mut machine, mov).operands[1] = low;
    cases.push(("ShrU128By64/low-half-moved", source, machine));
    // The arithmetic shift's sign fill logical (the last `sar`: the high
    // half's fill by 63 for an amount of 64 or more).
    let (source, mut machine) = slice11_pair(WideShape::SarI128By100);
    let sar = *find(&machine, X86Opcode::SarRI).last().expect("a sar");
    inst_mut(&mut machine, sar).opcode = X86Opcode::ShrRI;
    cases.push(("SarI128By100/logical", source, machine));
    // A select's halves crossed.
    let (source, mut machine) = slice11_pair(WideShape::SelectU128);
    let cmov = row_where(&machine, |i| i.opcode == X86Opcode::Cmovcc);
    let other = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| inst(&machine, *ordinal).opcode == X86Opcode::Cmovcc)
        .nth(1)
        .expect("two cmovs");
    let (first, second) = (
        inst(&machine, cmov).operands[1].clone(),
        inst(&machine, other).operands[1].clone(),
    );
    inst_mut(&mut machine, cmov).operands[1] = second;
    inst_mut(&mut machine, other).operands[1] = first;
    cases.push(("SelectU128/halves-crossed", source, machine));
    // A call's `I128` result halves swapped.
    let (source, mut machine) = slice11_pair(WideShape::CallU128);
    let call = row_where(&machine, |i| i.opcode == X86Opcode::Call);
    let from_rax = row_where(&machine, |i| i.operands.get(1) == Some(&preg(RAX)));
    let from_rdx = row_where(&machine, |i| i.operands.get(1) == Some(&preg(RDX)));
    assert!(from_rax > call && from_rdx > call);
    inst_mut(&mut machine, from_rax).operands[1] = preg(RDX);
    inst_mut(&mut machine, from_rdx).operands[1] = preg(RAX);
    cases.push(("CallU128/result-halves-swapped", source, machine));
    // The pair argument shifted by one register (its halves in RDX:RCX).
    let (source, mut machine) = slice11_pair(WideShape::CallAfterWord);
    let to_rsi = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR && i.operands.first() == Some(&preg(RSI))
    });
    let to_rdx = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR && i.operands.first() == Some(&preg(RDX))
    });
    let (low, high) = (
        inst(&machine, to_rsi).operands[1].clone(),
        inst(&machine, to_rdx).operands[1].clone(),
    );
    inst_mut(&mut machine, to_rsi).operands[1] = high;
    inst_mut(&mut machine, to_rdx).operands[1] = low;
    cases.push(("CallAfterWord/argument-halves-swapped", source, machine));
    // The high half stored at the low address.
    let (source, mut machine) = slice11_pair(WideShape::StoreU128);
    let stores: Vec<usize> = find(&machine, X86Opcode::MovMR);
    let (low_value, high_value) = (
        inst(&machine, stores[0]).operands[1].clone(),
        inst(&machine, stores[1]).operands[1].clone(),
    );
    inst_mut(&mut machine, stores[0]).operands[1] = high_value;
    inst_mut(&mut machine, stores[1]).operands[1] = low_value;
    cases.push(("StoreU128/halves-swapped", source, machine));
    // The high half loaded from the low address.
    let (source, mut machine) = slice11_pair(WideShape::LoadU128);
    let loads: Vec<usize> = find(&machine, X86Opcode::MovRM);
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, loads[1]).operands[1] {
        *disp = 4;
    }
    cases.push(("LoadU128/high-half-offset", source, machine));
    // A private slot's high half read from its low half.
    let (source, mut machine) = slice11_pair(WideShape::SlotU128);
    let loads: Vec<usize> = find(&machine, X86Opcode::MovRM);
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, *loads.last().unwrap()).operands[1]
    {
        *disp -= 8;
    }
    cases.push(("SlotU128/high-half-from-low", source, machine));
    // `to_bits` of an `f64` through a 32-bit `movd`.
    let (source, mut machine) = slice11_pair(WideShape::ToBitsF64);
    let movq = row_where(&machine, |i| i.opcode == X86Opcode::MovqFromXmm);
    let row = inst_mut(&mut machine, movq);
    row.opcode = X86Opcode::MovdFromXmm;
    if let O::VReg(vreg) = &mut row.operands[0] {
        *vreg = trust_cg_ir::regs::VReg::new(vreg.id, RegClass::Gpr32);
    }
    // Every later use of that register names it at 32 bits.
    let id = match &inst(&machine, movq).operands[0] {
        O::VReg(vreg) => vreg.id,
        other => panic!("{other:?}"),
    };
    for (ordinal, _, _) in rows(&machine) {
        for operand in &mut inst_mut(&mut machine, ordinal).operands {
            if let O::VReg(vreg) = operand
                && vreg.id == id
            {
                *vreg = trust_cg_ir::regs::VReg::new(id, RegClass::Gpr32);
            }
        }
    }
    let ret_move = row_where(&machine, |i| {
        matches!(i.opcode, X86Opcode::MovRR | X86Opcode::MovRR32)
            && i.operands.first() == Some(&preg(RAX))
    });
    let row = inst_mut(&mut machine, ret_move);
    row.opcode = X86Opcode::MovRR32;
    row.operands[0] = preg(GPR32_ALIAS_BASE + RAX);
    cases.push(("ToBitsF64/movd", source, machine));
    // A `movss` copy of the `f64` parameter: the copy defines its low 32 bits
    // only (register allocation treats its destination as a pure definition).
    let (source, mut machine) = slice11_pair(WideShape::ToBitsF64);
    let movsd = row_where(&machine, |i| i.opcode == X86Opcode::MovsdRR);
    inst_mut(&mut machine, movsd).opcode = X86Opcode::MovssRR;
    cases.push(("ToBitsF64/movss-copy", source, machine));
    // A `movss` over that copy, rewriting its low 32 bits with the same bits:
    // register allocation treats the `movss` destination as a pure
    // definition, so the bits above 32 are no longer the copy's.
    let (source, mut machine) = slice11_pair(WideShape::ToBitsF64);
    let movsd = row_where(&machine, |i| i.opcode == X86Opcode::MovsdRR);
    let mut movss = inst(&machine, movsd).clone();
    movss.opcode = X86Opcode::MovssRR;
    movss.flags = X86Opcode::MovssRR.default_flags();
    insert_at(&mut machine, movsd + 1, movss);
    cases.push(("ToBitsF64/movss-over-its-copy", source, machine));
    // A float argument passed in XMM1 where the callee reads XMM0.
    let (source, mut machine) = slice11_pair(WideShape::Interleaved);
    let to_xmm0 = row_where(&machine, |i| {
        matches!(i.opcode, X86Opcode::MovssRR | X86Opcode::MovsdRR)
            && i.operands.first() == Some(&xmm_preg(0))
    });
    let to_xmm1 = row_where(&machine, |i| {
        matches!(i.opcode, X86Opcode::MovssRR | X86Opcode::MovsdRR)
            && i.operands.first() == Some(&xmm_preg(1))
    });
    let (first, second) = (
        inst(&machine, to_xmm0).operands[1].clone(),
        inst(&machine, to_xmm1).operands[1].clone(),
    );
    let (first_op, second_op) = (
        inst(&machine, to_xmm0).opcode,
        inst(&machine, to_xmm1).opcode,
    );
    inst_mut(&mut machine, to_xmm0).operands[1] = second;
    inst_mut(&mut machine, to_xmm0).opcode = second_op;
    inst_mut(&mut machine, to_xmm1).operands[1] = first;
    inst_mut(&mut machine, to_xmm1).opcode = first_op;
    cases.push(("Interleaved/sse-arguments-swapped", source, machine));
    // The mixed pair's float lane returned from the integer argument.
    let (source, mut machine) = slice11_pair(WideShape::MixedPair);
    let to_xmm0 = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovsdRR && i.operands.first() == Some(&xmm_preg(0))
    });
    let integer = {
        let from_rdi = row_where(&machine, |i| i.operands.get(1) == Some(&preg(RDI)));
        inst(&machine, from_rdi).operands[0].clone()
    };
    let row = inst_mut(&mut machine, to_xmm0);
    row.opcode = X86Opcode::MovqToXmm;
    row.operands[1] = integer;
    cases.push(("MixedPair/float-lane-from-integer", source, machine));
    cases
}

#[test]
fn every_slice_eleven_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_eleven_refutations() {
        refuted(&source, &machine, label);
    }
}

/// `adc`/`sbb` read CF: after a call (CF undefined) a named undefined read;
/// after a row whose flags the walk does not model, no claim.
#[test]
fn the_carry_an_adc_reads_is_a_modelled_rows() {
    let (source, mut machine) = slice11_pair(WideShape::AddU128);
    let adc = row_where(&machine, |i| i.opcode == X86Opcode::AdcRR);
    let destination = inst(&machine, adc - 1).operands[0].clone();
    insert_at(
        &mut machine,
        adc,
        X86ISelInst::new(
            X86Opcode::AndRI,
            vec![destination.clone(), destination, O::Imm(-1)],
        ),
    );
    expect_unsupported(&source, &machine, "AddU128/and-before-adc");
    // No `add` before the `adc`: RFLAGS is undefined at entry.
    let (source, mut machine) = slice11_pair(WideShape::AddU128);
    let add = row_where(&machine, |i| i.opcode == X86Opcode::AddRR);
    inst_mut(&mut machine, add).opcode = X86Opcode::OrRR;
    // `or` writes flags the walk does not model: no claim.
    expect_unsupported(&source, &machine, "AddU128/or-before-adc");
    let (source, mut machine) = slice11_pair(WideShape::AddU128);
    let add = row_where(&machine, |i| i.opcode == X86Opcode::AddRR);
    let row = inst(&machine, add).clone();
    remove_at(&mut machine, add);
    let adc = row_where(&machine, |i| i.opcode == X86Opcode::AdcRR);
    insert_at(&mut machine, adc + 1, row);
    expect_mismatch(
        &source,
        &machine,
        "AddU128/adc-before-add",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rflags"),
    );
}

/// A call may change every SSE register: a float read after a call that does
/// not define it is a named undefined read; a float call result's register
/// is the callee's XMM0, and the call row must declare it.
#[test]
fn sse_registers_follow_the_caller_saved_and_result_rules() {
    let (source, mut machine) = slice11_pair(WideShape::CallResultF64);
    let call = row_where(&machine, |i| i.opcode == X86Opcode::Call);
    let result = inst_mut(&mut machine, call)
        .call_result_regs
        .as_mut()
        .expect("result registers");
    result[0] = X86CallResultReg::new(X86PReg::new(RAX), 64);
    expect_mismatch(&source, &machine, "CallResultF64/result-in-rax", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });
    let (source, mut machine) = slice11_pair(WideShape::CallArgF32);
    let call = row_where(&machine, |i| i.opcode == X86Opcode::Call);
    inst_mut(&mut machine, call).call_arg_regs[0] =
        X86CallArgReg::new(X86PReg::new(XMM_ROOTS.start + 1), 32);
    expect_mismatch(&source, &machine, "CallArgF32/argument-in-xmm1", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });
    // The result read from XMM1, which the call left undefined.
    let (source, mut machine) = slice11_pair(WideShape::CallResultF64);
    let from_xmm0 = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovsdRR && i.operands.get(1) == Some(&xmm_preg(0))
    });
    inst_mut(&mut machine, from_xmm0).operands[1] = xmm_preg(1);
    expect_mismatch(
        &source,
        &machine,
        "CallResultF64/read-xmm1",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "xmm1"),
    );
}

/// What slice 11 refuses stays refused by name: every floating-point
/// operation, a shift of an `I128` by a non-constant amount, a branch on an
/// `I128`, an `I128` beside another result, and an `I128` argument that
/// would go on the stack.
#[test]
fn slice_eleven_sources_outside_the_lane_are_refused_by_name() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice11_refused");
    let mut expect = Vec::new();
    let mut define =
        |builder: &mut ModuleBuilder,
         name: &str,
         params: Vec<Ty>,
         results: Vec<Ty>,
         body: &dyn Fn(&mut trust_ir_build::FunctionBuilder<'_>, &[trust_ir::ValueId]),
         reason: &'static str| {
            let signature = builder.add_func_type(params.clone(), results);
            let mut f = builder.function(name, signature);
            let entry = f.create_block();
            let args: Vec<_> = params
                .iter()
                .map(|ty| f.add_block_param(entry, ty.clone()))
                .collect();
            f.switch_to_block(entry);
            body(&mut f, &args);
            f.build();
            expect.push((name.to_owned(), reason));
        };
    // (Slice 21 admits `Fmul` as a rounding event, OD-198; a widening of a
    // float stays outside.)
    define(
        &mut builder,
        "s11_fpext",
        vec![Ty::F32],
        vec![Ty::F64],
        &|f, args| {
            let wide = f.cast(CastOp::FPExt, Ty::F32, Ty::F64, args[0]);
            f.ret(vec![wide]);
        },
        "is a floating-point operation",
    );
    // (Slice 15 admits `Fneg` and `Fabs`, sign-bit operations; a square root
    // stays outside.)
    define(
        &mut builder,
        "s11_fsqrt",
        vec![Ty::F32],
        vec![Ty::F32],
        &|f, args| {
            let root = f.unop(UnOp::FSqrt, Ty::F32, args[0]);
            f.ret(vec![root]);
        },
        "is a floating-point operation",
    );
    define(
        &mut builder,
        "s11_shl_variable",
        vec![Ty::U128, Ty::U32],
        vec![Ty::U128],
        &|f, args| {
            let shifted = f.binop(BinOp::Shl, Ty::U128, args[0], args[1]);
            f.ret(vec![shifted]);
        },
        "shifts an i128 by a non-constant amount",
    );
    define(
        &mut builder,
        "s11_switch",
        vec![Ty::U128],
        vec![Ty::U64],
        &|f, args| {
            let (zero, other) = (f.create_block(), f.create_block());
            f.switch(
                args[0],
                vec![trust_ir::SwitchCase {
                    value: trust_ir::Constant::Int(0),
                    target: zero,
                    args: vec![],
                }],
                other,
                vec![],
            );
            f.switch_to_block(zero);
            let one = f.iconst(Ty::U64, 1);
            f.ret(vec![one]);
            f.switch_to_block(other);
            let two = f.iconst(Ty::U64, 2);
            f.ret(vec![two]);
        },
        "",
    );
    // (Slice 15 admits an `I128` on the stack, `[u64; 5]` then `u128`; a
    // float past XMM7 stays outside.)
    define(
        &mut builder,
        "s11_on_the_stack",
        vec![Ty::F64; 9],
        vec![Ty::F64],
        &|f, args| f.ret(vec![args[0]]),
        "more than six argument registers",
    );
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let lir: HashMap<String, Function> =
        trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &crate::license_test_support::permit_unlicensed(),
        )
        .expect("translates")
        .into_iter()
        .map(|(function, _)| (function.name.clone(), function))
        .collect();
    // The adapter splits a `u128` switch into a test of the high half and a
    // switch on the low one, so no LIR branch tests an `I128`; one that does
    // (the switch retyped onto the parameter) is refused by name.
    let mut switch = lir["s11_switch"].clone();
    for block in switch.blocks.values_mut() {
        for inst in &mut block.instructions {
            if matches!(inst.opcode, L::Switch { .. }) {
                inst.args = vec![Value(0)];
            }
        }
    }
    let refusal = match admitted_body(&switch) {
        Ok(_) => panic!("a switch on an i128 is admitted"),
        Err(refusal) => refusal.to_string(),
    };
    assert!(refusal.contains("an i128 or float branch"), "{refusal}");
    for (name, reason) in expect {
        if reason.is_empty() {
            continue;
        }
        let source = &lir[&name];
        let refusal = match admitted_body(source) {
            Ok(_) => panic!("{name} is admitted\n{}", describe_lir(source)),
            Err(refusal) => refusal.to_string(),
        };
        assert!(refusal.contains(reason), "{name}: {refusal}");
    }
    // An `I128` beside another result (the adapter itself refuses one under
    // the C convention, so the add fixture's signature is retyped).
    let (mut source, _) = slice11_pair(WideShape::AddU128);
    source.signature.returns = vec![Type::I128, Type::I64];
    let refusal = match admitted_body(&source) {
        Ok(_) => panic!("an i128 beside another result is admitted"),
        Err(refusal) => refusal.to_string(),
    };
    assert!(
        refusal.contains("an i128 result beside another result"),
        "{refusal}"
    );
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-11
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds.
#[test]
fn optimized_slice_eleven_fixtures_are_judged_without_false_mismatches() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut built = 0;
    for opt_level in [
        trust_cg_opt::OptLevel::O1,
        trust_cg_opt::OptLevel::O2,
        trust_cg_opt::OptLevel::O3,
    ] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        for shape in all_slice_eleven_shapes() {
            let (source, mut machine) = slice11_pair(shape);
            pipeline.run_x86_optimization_passes(&mut machine);
            match source_bound_x86_body(&source, &machine, SYSV) {
                Ok(owner) => {
                    built += 1;
                    assert!(
                        theorem_holds(owner.obligation()),
                        "{shape:?} at {opt_level:?}\n{}",
                        describe(&machine)
                    );
                    eprintln!("{opt_level:?} {shape:?}: theorem holds on samples");
                }
                Err(X86BodyRefusal::Unsupported(refusal)) => {
                    eprintln!("{opt_level:?} {shape:?}: no claim ({refusal})");
                }
                Err(other) => panic!(
                    "{shape:?} at {opt_level:?}: {other}\n{}",
                    describe(&machine)
                ),
            }
        }
    }
    assert!(built > 0, "no optimized fixture built a theorem");
}

const SLICE_ELEVEN_SNAPSHOT_SHA256: &str =
    "a297b6e9c98581e327dc8c29d34e607f56c2e53e71ef042853e6a85ea875a773";

#[test]
fn slice_eleven_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice11_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_ELEVEN {
        let (source, machine) = slice11_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice11_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_ELEVEN_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_ELEVEN_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-11 snapshots drifted");
}

/// A shift by CL whose count the walk knows (slice 11's constant-count
/// spelling) masks the count as the hardware does: `shl r64, cl` with CL =
/// 67 shifts by 3, so it computes slice 1's `x << 3`, and CL = 66 does not.
#[test]
fn a_known_count_in_cl_is_masked_like_the_hardware() {
    for (count, holds) in [(67, true), (3, true), (66, false), (131, true)] {
        let (source, mut machine) = pair(Shape::ShlImm);
        let shl = find(&machine, X86Opcode::ShlRI)[0];
        let row = inst(&machine, shl).clone();
        // `shl d, s, imm`, or the tied `shl d, imm` (`s` is `d`).
        let destination = row.operands[0].clone();
        let operand = if row.operands.len() == 3 {
            row.operands[1].clone()
        } else {
            destination.clone()
        };
        *inst_mut(&mut machine, shl) =
            X86ISelInst::new(X86Opcode::ShlRR, vec![destination.clone()]);
        insert_at(
            &mut machine,
            shl,
            X86ISelInst::new(X86Opcode::MovRR, vec![destination, operand]),
        );
        insert_at(
            &mut machine,
            shl,
            X86ISelInst::new(X86Opcode::MovRI, vec![preg(RCX), O::Imm(count)]),
        );
        let obligation = owner(&source, &machine, &format!("ShlImm by CL = {count}"));
        assert_eq!(
            theorem_holds(&obligation),
            holds,
            "CL = {count}\n{}",
            describe(&machine)
        );
        if !holds {
            assert!(theorem_refuted(&obligation), "CL = {count}");
        }
    }
}

/// A call may change every SSE register: reading XMM0 after a call that
/// defines no float result is a named undefined read.
#[test]
fn a_call_leaves_every_sse_register_undefined() {
    let (source, mut machine) = slice11_pair(WideShape::CallArgF32);
    let call = row_where(&machine, |i| i.opcode == X86Opcode::Call);
    let fresh = rows(&machine)
        .into_iter()
        .flat_map(|(ordinal, _, _)| inst(&machine, ordinal).operands.clone())
        .filter_map(|operand| match operand {
            O::VReg(vreg) => Some(vreg.id),
            _ => None,
        })
        .max()
        .expect("a virtual register")
        + 1;
    insert_at(
        &mut machine,
        call + 1,
        X86ISelInst::new(
            X86Opcode::MovssRR,
            vec![
                O::VReg(trust_cg_ir::regs::VReg::new(fresh, RegClass::Fpr32)),
                xmm_preg(0),
            ],
        ),
    );
    expect_mismatch(
        &source,
        &machine,
        "CallArgF32/xmm0-after-call",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "xmm0"),
    );
}
