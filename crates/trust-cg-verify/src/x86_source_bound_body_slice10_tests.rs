// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 10 of the x86-64 source-bound body theorem: instruction coverage.
//! LIR checked arithmetic (`[value, overflow]` of `CheckedUadd` ..
//! `CheckedSmul`), `Bnot`, `Ineg`, `CtPop`, shifts by a variable amount and
//! `CallIndirect`, with the machine rows the selector lowers them to: the
//! register-register `add`, `sub` and `imul` with the flags a `setb`/`seto`
//! reads, the one-operand `mul` with its implicit RAX/RDX, `not`, `neg`,
//! `popcnt` (and the tied `and d, imm` that masks a narrow operand), the
//! shifts by CL and `call r64`.
//!
//! Fixtures are real: LIR from the trust-ir adapter (`overflow`, `unop`,
//! `ctpop`, `call_indirect`) and the machine stream from the real x86-64
//! instruction selector (`super::select`). Negative controls mutate that
//! stream and must end as a typed mismatch, a refuted theorem or an
//! unsupported (uncredited) body, never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice10::` library gate). The
//! replay on AY and Clean and the verifier-credit tests are in
//! `slice10_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::*;
use trust_ir::{ICmpOp, OverflowOp, UnOp};

// ---------------------------------------------------------------------------
// The sampler (test-only semantics check; never credit)
// ---------------------------------------------------------------------------

/// The edge words of slice 10's sampler: overflow and sign boundaries at
/// every width a carrier or a shift count has (0, 1, all ones, the signed
/// minimum and maximum, and those at 8, 16 and 32 bits), repeating bit
/// patterns (`0x5555…`, `0xAAAA…`, `0x3333…`, `0xCCCC…`: a sum or a
/// complement of two of them lands on all ones or zero), and words whose
/// bytes above a boundary are all ones (structured partial saturation, the
/// complement of slice 8's partial zeroing: a carry or overflow out of a
/// narrower or wider width differs exactly there).
fn edge_word(k: u64) -> u64 {
    const EDGES: [u64; 20] = [
        0,
        1,
        2,
        u64::MAX,
        u64::MAX - 1,
        1 << 63,
        (1 << 63) - 1,
        (1 << 63) + 1,
        0xffff_ffff,
        0x8000_0000,
        0x7fff_ffff,
        0xffff,
        0x8000,
        0xff,
        0x80,
        63,
        0x5555_5555_5555_5555,
        0xaaaa_aaaa_aaaa_aaaa,
        0x3333_3333_3333_3333,
        0xcccc_cccc_cccc_cccc,
    ];
    let boundary = (k / 3) % 8;
    match k % 3 {
        0 => EDGES[(k / 3 % 20) as usize],
        1 => u64::MAX << (8 * boundary),
        _ => !(u64::MAX << (8 * boundary)) | (1 << (8 * boundary)).min(1 << 63),
    }
}

/// Whether the theorem holds at the edge sample `seed`: every free input an
/// edge word ([`edge_word`]), the choice rotating per input at even seeds and
/// one word for every input at odd seeds (equal operands: `x + x`, `x ^ x`).
pub(crate) fn holds_at_edge(obligation: &ProofObligation, seed: u64) -> bool {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    for (k, (name, width)) in free_inputs_of(obligation).into_iter().enumerate() {
        let word = if seed % 2 == 1 {
            edge_word(seed / 2)
        } else {
            edge_word(seed.wrapping_mul(7).wrapping_add(k as u64 * 13))
        };
        env.insert(name, crate::smt::mask(word, width));
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

pub(crate) const EDGE_SAMPLES: u64 = 2048;

/// Whether the theorem holds at every sample of slice 8's sampler (random,
/// small and partially zeroed words; through it slices 6 and 7's) and at
/// every edge sample.
pub(crate) fn theorem_holds(obligation: &ProofObligation) -> bool {
    super::slice8::theorem_holds(obligation)
        && (0..EDGE_SAMPLES).all(|seed| holds_at_edge(obligation, seed))
}

/// Whether some sample refutes the theorem (slice 8's samplers or an edge
/// sample).
pub(crate) fn theorem_refuted(obligation: &ProofObligation) -> bool {
    super::slice8::theorem_refuted(obligation)
        || (0..EDGE_SAMPLES).any(|seed| !holds_at_edge(obligation, seed))
}

/// Slice-10 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InsnShape {
    // ---- (a) checked arithmetic: `fn(a, b) -> (T, bool)`, the
    // `overflowing_*` methods (a RAX:DL pair result)
    /// `u64::overflowing_add`: `add; setb`.
    AddU64,
    /// `u64::overflowing_sub`: `sub; setb`.
    SubU64,
    /// `u64::overflowing_mul`: `mov rax, a; mul b; setb`.
    MulU64,
    /// `i64::overflowing_add`: `add; seto`.
    AddI64,
    /// `i64::overflowing_sub`: `sub; seto`.
    SubI64,
    /// `i64::overflowing_mul`: `imul; seto`.
    MulI64,
    /// `i32::overflowing_add`: below 64 bits the adapter lowers the overflow
    /// to ordinary arithmetic, its signed flag through `Bnot` (`!(a ^ b) &
    /// (a ^ sum) < 0`).
    AddI32,
    /// `fn(a: u64, b: u64) -> u64 { a + b }` with overflow checks: the
    /// overflow `bool` branched on, a panic call on the overflowing path.
    AddPanics,
    /// `fn(a: u64, b: u64) -> u64 { a * b }` with overflow checks.
    MulPanics,
    // ---- (b) `Bnot`
    /// `fn(x: u64) -> u64 { !x }`.
    NotU64,
    /// `fn(x: u32) -> u32 { !x }`.
    NotU32,
    /// `fn(x: u8) -> u8 { !x }`: a 32-bit `not` of the byte's carrier.
    NotU8,
    /// `fn(x: i32) -> i32 { x.wrapping_neg() }` (`Ineg`, `neg`).
    NegI32,
    // ---- (c) `CtPop`
    /// `u64::count_ones`.
    CountU64,
    /// `u32::count_ones`.
    CountU32,
    /// `u16::count_ones`: the operand masked first (`and d, 0xffff`).
    CountU16,
    /// `u8::count_ones`: the operand masked first (`and d, 0xff`).
    CountU8,
    // ---- (d) variable shifts
    /// `fn(x: u32, n: u32) -> u32 { x << n }` with overflow checks: the
    /// shift only on the path where `n < 32`.
    ShlChecked,
    /// `fn(x: u64, n: u64) -> u64 { x.unchecked_shr(n) }`: no range check
    /// (an out-of-range `n` is undefined behavior in trust-ir).
    ShrU64,
    /// `fn(x: i32, n: i32) -> i32 { x.unchecked_shr(n) }`: `sar r32, cl`.
    SarI32,
    /// `fn(x: u8, n: u8) -> u8 { x.unchecked_shl(n) }`: the count masked to
    /// 3 bits, then a 32-bit `shl` of the byte's carrier.
    ShlU8,
    /// `fn(x: i16, n: i16) -> i16 { x.unchecked_shr(n) }`: the operand
    /// sign-extended, the count masked to 4 bits.
    SarI16,
    // ---- (e) `CallIndirect`
    /// `fn(f: fn(u64) -> u64, x: u64) -> u64 { f(x) }`.
    Indirect,
    /// `fn(f: fn(u32), x: u32) { f(x) }`: no result, the function pointer
    /// and the argument observed.
    IndirectVoid,
    /// `fn(f: fn(u64) -> u64, x: u64) -> u64 { g(f(x)) }`: an indirect call,
    /// then a direct one.
    IndirectThenDirect,
}

/// Every slice-10 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_ten_fixture_is_qualified`] checks
/// that none is left out).
pub(crate) const SLICE_TEN: [InsnShape; 25] = [
    InsnShape::AddU64,
    InsnShape::SubU64,
    InsnShape::MulU64,
    InsnShape::AddI64,
    InsnShape::SubI64,
    InsnShape::MulI64,
    InsnShape::AddI32,
    InsnShape::AddPanics,
    InsnShape::MulPanics,
    InsnShape::NotU64,
    InsnShape::NotU32,
    InsnShape::NotU8,
    InsnShape::NegI32,
    InsnShape::CountU64,
    InsnShape::CountU32,
    InsnShape::CountU16,
    InsnShape::CountU8,
    InsnShape::ShlChecked,
    InsnShape::ShrU64,
    InsnShape::SarI32,
    InsnShape::ShlU8,
    InsnShape::SarI16,
    InsnShape::Indirect,
    InsnShape::IndirectVoid,
    InsnShape::IndirectThenDirect,
];

impl InsnShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s10_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }

    /// The LIR opcode the shape exists for.
    fn admits(self, opcode: &L) -> bool {
        use InsnShape::*;
        match self {
            AddU64 | AddPanics => matches!(opcode, L::CheckedUadd),
            SubU64 => matches!(opcode, L::CheckedUsub),
            MulU64 | MulPanics => matches!(opcode, L::CheckedUmul),
            AddI64 => matches!(opcode, L::CheckedSadd),
            SubI64 => matches!(opcode, L::CheckedSsub),
            MulI64 => matches!(opcode, L::CheckedSmul),
            AddI32 | NotU64 | NotU32 | NotU8 => matches!(opcode, L::Bnot),
            NegI32 => matches!(opcode, L::Ineg),
            CountU64 | CountU32 | CountU16 | CountU8 => matches!(opcode, L::CtPop),
            ShlChecked | ShlU8 => matches!(opcode, L::Ishl),
            ShrU64 => matches!(opcode, L::Ushr),
            SarI32 | SarI16 => matches!(opcode, L::Sshr),
            Indirect | IndirectVoid | IndirectThenDirect => matches!(opcode, L::CallIndirect),
        }
    }

    /// The machine row the shape's opcode lowers to.
    fn row(self) -> X86Opcode {
        use InsnShape::*;
        match self {
            AddU64 | AddI64 | AddPanics => X86Opcode::AddRR,
            SubU64 | SubI64 => X86Opcode::SubRR,
            MulU64 | MulPanics => X86Opcode::Mul,
            MulI64 => X86Opcode::ImulRR,
            AddI32 | NotU64 | NotU32 | NotU8 => X86Opcode::Not,
            NegI32 => X86Opcode::Neg,
            CountU64 | CountU32 | CountU16 | CountU8 => X86Opcode::Popcnt,
            ShlChecked | ShlU8 => X86Opcode::ShlRR,
            ShrU64 => X86Opcode::ShrRR,
            SarI32 | SarI16 => X86Opcode::SarRR,
            Indirect | IndirectVoid | IndirectThenDirect => X86Opcode::CallR,
        }
    }
}

/// The LIR the trust-ir adapter produces for a slice-10 shape.
pub(crate) fn slice10_lir(shape: InsnShape) -> Function {
    use InsnShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice10");
    let unary_u64 = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let unary_u32_void = builder.add_func_type(vec![Ty::U32], vec![]);
    let g = builder.declare_function("g", unary_u64);
    let panic = {
        let ty = builder.add_func_type(vec![], vec![]);
        builder.declare_function("panic_const_overflow", ty)
    };
    let overflowing = |ty: Ty| (vec![ty.clone(), ty.clone()], vec![ty, Ty::Bool]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        AddU64 | SubU64 | MulU64 => overflowing(Ty::U64),
        AddI64 | SubI64 | MulI64 => overflowing(Ty::I64),
        AddI32 => overflowing(Ty::I32),
        AddPanics | MulPanics => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        NotU64 | CountU64 => (vec![Ty::U64], vec![Ty::U64]),
        NotU32 | CountU32 => (vec![Ty::U32], vec![Ty::U32]),
        CountU16 => (vec![Ty::U16], vec![Ty::U16]),
        NotU8 | CountU8 => (vec![Ty::U8], vec![Ty::U8]),
        NegI32 => (vec![Ty::I32], vec![Ty::I32]),
        ShlChecked => (vec![Ty::U32, Ty::U32], vec![Ty::U32]),
        ShrU64 => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        SarI32 => (vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        ShlU8 => (vec![Ty::U8, Ty::U8], vec![Ty::U8]),
        SarI16 => (vec![Ty::I16, Ty::I16], vec![Ty::I16]),
        Indirect | IndirectThenDirect => (vec![Ty::Ptr, Ty::U64], vec![Ty::U64]),
        IndirectVoid => (vec![Ty::Ptr, Ty::U32], vec![]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let op = |shape: InsnShape| match shape {
        AddU64 | AddI64 | AddI32 | AddPanics => OverflowOp::AddOverflow,
        SubU64 | SubI64 => OverflowOp::SubOverflow,
        _ => OverflowOp::MulOverflow,
    };
    match shape {
        AddU64 | SubU64 | MulU64 | AddI64 | SubI64 | MulI64 | AddI32 => {
            let (value, overflow) = f.overflow(op(shape), params[0].clone(), args[0], args[1]);
            f.ret(vec![value, overflow]);
        }
        AddPanics | MulPanics => {
            let (value, overflow) = f.overflow(op(shape), Ty::U64, args[0], args[1]);
            let (fail, ok) = (f.create_block(), f.create_block());
            f.condbr(overflow, fail, vec![], ok, vec![]);
            f.switch_to_block(fail);
            f.call_void(panic, vec![]);
            f.unreachable();
            f.switch_to_block(ok);
            f.ret(vec![value]);
        }
        NotU64 | NotU32 | NotU8 => {
            let not = f.unop(UnOp::Not, params[0].clone(), args[0]);
            f.ret(vec![not]);
        }
        NegI32 => {
            let negated = f.unop(UnOp::Neg, Ty::I32, args[0]);
            f.ret(vec![negated]);
        }
        CountU64 | CountU32 | CountU16 | CountU8 => {
            let count = f.ctpop(params[0].clone(), args[0]);
            f.ret(vec![count]);
        }
        ShlChecked => {
            let (fail, ok) = (f.create_block(), f.create_block());
            let width = f.iconst(Ty::U32, 32);
            let in_range = f.icmp(ICmpOp::Ult, Ty::U32, args[1], width);
            f.condbr(in_range, ok, vec![], fail, vec![]);
            f.switch_to_block(fail);
            f.call_void(panic, vec![]);
            f.unreachable();
            f.switch_to_block(ok);
            let shifted = f.binop(BinOp::Shl, Ty::U32, args[0], args[1]);
            f.ret(vec![shifted]);
        }
        ShrU64 | SarI32 | ShlU8 | SarI16 => {
            let op = match shape {
                ShrU64 => BinOp::LShr,
                ShlU8 => BinOp::Shl,
                _ => BinOp::AShr,
            };
            let shifted = f.binop(op, params[0].clone(), args[0], args[1]);
            f.ret(vec![shifted]);
        }
        Indirect => {
            let y = f.call_indirect(args[0], unary_u64, vec![args[1]]);
            f.ret(vec![y]);
        }
        IndirectVoid => {
            f.call_indirect_void(args[0], unary_u32_void, vec![args[1]]);
            f.ret(vec![]);
        }
        IndirectThenDirect => {
            let y = f.call_indirect(args[0], unary_u64, vec![args[1]]);
            let z = f.call(g, vec![y]);
            f.ret(vec![z]);
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

pub(crate) fn slice10_pair(shape: InsnShape) -> (Function, X86ISelFunction) {
    let source = slice10_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_slice_ten_shapes() -> Vec<InsnShape> {
    use InsnShape::*;
    let all = SLICE_TEN.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            AddU64 | SubU64 | MulU64 | AddI64 | SubI64 | MulI64 | AddI32 | AddPanics
            | MulPanics | NotU64 | NotU32 | NotU8 | NegI32 | CountU64 | CountU32 | CountU16
            | CountU8 | ShlChecked | ShrU64 | SarI32 | ShlU8 | SarI16 | Indirect | IndirectVoid
            | IndirectThenDirect => {}
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

fn cond_code(inst: &X86ISelInst) -> Option<trust_cg_ir::X86CondCode> {
    inst.operands.iter().find_map(|operand| match operand {
        O::CondCode(cc) => Some(*cc),
        _ => None,
    })
}

// ---------------------------------------------------------------------------
// The semantics, against the hardware and trust-ir definitions (no solver)
// ---------------------------------------------------------------------------

/// Concrete values of the sampler's kind: edges, small and dense words.
fn edge_values(bits: u32) -> Vec<u64> {
    let mask = crate::smt::mask(u64::MAX, bits);
    let top = 1u64 << (bits - 1);
    let mut values = vec![0, 1, 2, 3, mask, mask - 1, top, top - 1, top + 1, mask >> 1];
    let mut state = 0x2545_f491_4f6c_dd1du64;
    for _ in 0..40 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        values.push(state & mask);
        values.push((state >> 7) & 0xffff);
    }
    values
}

fn eval_bool(expr: &E, env: &crate::smt::EvalEnv) -> bool {
    match expr.eval(env) {
        crate::smt::EvalResult::Bool(value) => value,
        other => panic!("{expr} is not Boolean: {other:?}"),
    }
}

fn eval_bv(expr: &E, env: &crate::smt::EvalEnv) -> u64 {
    match expr.eval(env) {
        crate::smt::EvalResult::Bv(value) => value,
        other => panic!("{expr} is not a <= 64-bit bitvector: {other:?}"),
    }
}

/// [`CheckedOp::overflows`] is trust-ir's overflow at both widths and every
/// signedness: Rust's `overflowing_add`/`_sub`/`_mul` of the same operands,
/// which are what trust-ir's `unsigned_overflow`/`signed_overflow` state.
#[test]
fn the_overflow_predicate_is_trust_irs() {
    use crate::smt::EvalEnv;
    for bits in [32u32, 64] {
        let values = edge_values(bits);
        for &a in &values {
            for &b in &values {
                let mut env = EvalEnv::default();
                env.insert("a".into(), a);
                env.insert("b".into(), b);
                let (x, y) = (E::var("a", bits), E::var("b", bits));
                for op in [
                    CheckedOp::Uadd,
                    CheckedOp::Usub,
                    CheckedOp::Umul,
                    CheckedOp::Sadd,
                    CheckedOp::Ssub,
                    CheckedOp::Smul,
                ] {
                    let expected = match (bits, op) {
                        (32, CheckedOp::Uadd) => (a as u32).overflowing_add(b as u32).1,
                        (32, CheckedOp::Usub) => (a as u32).overflowing_sub(b as u32).1,
                        (32, CheckedOp::Umul) => (a as u32).overflowing_mul(b as u32).1,
                        (32, CheckedOp::Sadd) => (a as i32).overflowing_add(b as i32).1,
                        (32, CheckedOp::Ssub) => (a as i32).overflowing_sub(b as i32).1,
                        (32, CheckedOp::Smul) => (a as i32).overflowing_mul(b as i32).1,
                        (_, CheckedOp::Uadd) => a.overflowing_add(b).1,
                        (_, CheckedOp::Usub) => a.overflowing_sub(b).1,
                        (_, CheckedOp::Umul) => a.overflowing_mul(b).1,
                        (_, CheckedOp::Sadd) => (a as i64).overflowing_add(b as i64).1,
                        (_, CheckedOp::Ssub) => (a as i64).overflowing_sub(b as i64).1,
                        (_, CheckedOp::Smul) => (a as i64).overflowing_mul(b as i64).1,
                    };
                    let overflow = op.overflows(x.clone(), y.clone(), bits);
                    assert_eq!(
                        eval_bool(&overflow, &env),
                        expected,
                        "{op:?} at {bits} bits of {a:#x}, {b:#x}"
                    );
                }
            }
        }
    }
}

/// The flags the walk models are the hardware's (Intel SDM; checked against
/// Rust's own carry and overflow arithmetic): `add` and `sub` set CF to the
/// unsigned and OF to the signed overflow and ZF/SF/PF from the result,
/// `imul` sets CF = OF to the signed overflow of the product, `mul` to its
/// unsigned overflow, and both leave SF, ZF and PF undefined. `popcnt` is
/// `count_ones`.
#[test]
fn the_flag_models_are_the_hardwares() {
    use crate::smt::EvalEnv;
    use trust_cg_ir::X86CondCode as C;
    for bits in [32u32, 64] {
        let values = edge_values(bits);
        let mask = crate::smt::mask(u64::MAX, bits);
        let signed = |v: u64| ((v << (64 - bits)) as i64) >> (64 - bits);
        for &a in &values {
            for &b in &values {
                let mut env = EvalEnv::default();
                env.insert("a".into(), a);
                env.insert("b".into(), b);
                let (x, y) = (E::var("a", bits), E::var("b", bits));
                let holds = |flags: &AluFlags, cc| {
                    flags
                        .condition(cc)
                        .map(|condition| eval_bool(&condition, &env))
                };
                let (sum, difference, product) = (
                    a.wrapping_add(b) & mask,
                    a.wrapping_sub(b) & mask,
                    a.wrapping_mul(b) & mask,
                );
                let add = AluFlags::add(x.clone(), y.clone(), bits);
                assert_eq!(
                    holds(&add, C::B),
                    Some(u128::from(a) + u128::from(b) > u128::from(mask)),
                    "add CF {a:#x} {b:#x}"
                );
                assert_eq!(
                    holds(&add, C::O),
                    Some(
                        signed(a)
                            .checked_add(signed(b))
                            .is_none_or(|s| signed(s as u64 & mask) != s)
                    ),
                    "add OF {a:#x} {b:#x}"
                );
                assert_eq!(holds(&add, C::E), Some(sum == 0));
                assert_eq!(holds(&add, C::S), Some(sum >> (bits - 1) == 1));
                assert_eq!(holds(&add, C::P), Some((sum & 0xff).count_ones() % 2 == 0));
                let sub = AluFlags::sub(x.clone(), y.clone(), bits);
                assert_eq!(holds(&sub, C::B), Some(a < b), "sub CF {a:#x} {b:#x}");
                assert_eq!(
                    holds(&sub, C::O),
                    Some(
                        signed(a)
                            .checked_sub(signed(b))
                            .is_none_or(|s| signed(s as u64 & mask) != s)
                    ),
                    "sub OF {a:#x} {b:#x}"
                );
                assert_eq!(holds(&sub, C::E), Some(difference == 0));
                let imul = AluFlags::imul(x.clone(), y.clone(), bits);
                let wide = i128::from(signed(a)) * i128::from(signed(b));
                let imul_overflow = i128::from(signed(product)) != wide;
                assert_eq!(holds(&imul, C::O), Some(imul_overflow), "imul OF");
                assert_eq!(holds(&imul, C::B), Some(imul_overflow), "imul CF");
                for undefined in [
                    C::E,
                    C::NE,
                    C::S,
                    C::NS,
                    C::P,
                    C::NP,
                    C::L,
                    C::GE,
                    C::LE,
                    C::G,
                    C::BE,
                    C::A,
                ] {
                    assert_eq!(holds(&imul, undefined), None, "imul {undefined:?}");
                }
                let high = ((u128::from(a) * u128::from(b)) >> bits) as u64;
                let mul = AluFlags::carry_and_overflow(
                    crate::x86_64_semantics::encode_mul_high(x.clone(), y.clone())
                        .eq_expr(E::bv_const(0, bits))
                        .not_expr(),
                );
                assert_eq!(holds(&mul, C::B), Some(high != 0), "mul CF");
                assert_eq!(holds(&mul, C::NO), Some(high == 0), "mul OF");
                assert_eq!(
                    eval_bv(&x.clone().bvmul(y.clone()), &env),
                    product,
                    "mul low half"
                );
                assert_eq!(
                    eval_bv(&count_ones(x.clone()), &env),
                    u64::from(a.count_ones()),
                    "popcnt {a:#x}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

/// Each fixture's LIR holds the shape's opcode and its machine the row the
/// selector lowers it to (with, for checked arithmetic, the flag reader the
/// shape's signedness needs).
#[test]
fn slice_ten_fixtures_have_the_expected_lir_and_pre_ra_shapes() {
    use trust_cg_ir::X86CondCode as C;
    for shape in all_slice_ten_shapes() {
        let (source, machine) = slice10_pair(shape);
        let text = format!("{shape:?}\n{}{}", describe_lir(&source), describe(&machine));
        assert!(
            source
                .blocks
                .values()
                .flat_map(|block| &block.instructions)
                .any(|inst| shape.admits(&inst.opcode)),
            "{text}"
        );
        assert!(!find(&machine, shape.row()).is_empty(), "{text}");
        let setcc: Vec<_> = find(&machine, X86Opcode::Setcc)
            .into_iter()
            .map(|row| cond_code(inst(&machine, row)))
            .collect();
        use InsnShape::*;
        match shape {
            AddU64 | SubU64 | MulU64 | AddPanics | MulPanics => {
                assert!(setcc.contains(&Some(C::B)), "{text}")
            }
            AddI64 | SubI64 | MulI64 => assert!(setcc.contains(&Some(C::O)), "{text}"),
            CountU16 | CountU8 => assert!(
                rows(&machine).iter().any(|(ordinal, _, _)| {
                    let row = inst(&machine, *ordinal);
                    row.opcode == X86Opcode::AndRI && row.operands.len() == 2
                }),
                "{text}"
            ),
            _ => {}
        }
    }
}

#[test]
fn owner_builds_for_every_slice_ten_shape_and_covers_every_value_row() {
    for shape in SLICE_TEN {
        let (source, machine) = slice10_pair(shape);
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
    }
}

#[test]
fn slice_ten_theorems_hold_on_samples() {
    for shape in SLICE_TEN {
        let (source, machine) = slice10_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_TEN`]: every fixture whose real selection the owner admits with a
/// theorem that holds must be in it.
#[test]
fn every_admitted_slice_ten_fixture_is_qualified() {
    for shape in all_slice_ten_shapes() {
        let (source, machine) = slice10_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV)
            .is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(SLICE_TEN.contains(&shape), holds, "{shape:?}");
    }
}

/// An indirect call observes its function pointer, all 64 bits, before its
/// arguments; the flag of checked arithmetic is the second result lane.
#[test]
fn the_observables_carry_the_callee_pointer_and_the_overflow_bool() {
    let widths = |shape: InsnShape| {
        let (source, machine) = slice10_pair(shape);
        observable_items(&owned_plain_theorem(
            &source,
            &machine,
            &format!("{shape:?}"),
        ))
        .iter()
        .map(|(source, _)| source.bv_width())
        .collect::<Vec<_>>()
    };
    // `f(x)`: the result, then the callee pointer and the argument.
    assert_eq!(widths(InsnShape::Indirect), [64, 64, 64]);
    // `f(x)` with a `u32` and no result: the pointer and the argument.
    assert_eq!(widths(InsnShape::IndirectVoid), [64, 32]);
    // `(u64, bool)`: RAX, then EDX as the backend's clean 32-bit bool.
    assert_eq!(widths(InsnShape::AddU64), [64, 32]);
    let (source, machine) = slice10_pair(InsnShape::Indirect);
    let items = observable_items(&owned_plain_theorem(&source, &machine, "Indirect"));
    assert_eq!(items[1].0, E::var("p0", 64), "{items:?}");
}

// ---------------------------------------------------------------------------
// Wrong lowerings (controls): never credited
// ---------------------------------------------------------------------------

/// Each wrong lowering of a slice-10 row the owner binds, with the fixture it
/// mutates. Every one changes what a caller or callee can observe for some
/// input (the robustness probe's independent interpreter agrees), so its
/// theorem must be refuted; `slice10_qualification` replays each to an AY
/// counterexample.
pub(crate) fn slice_ten_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use trust_cg_ir::X86CondCode as C;
    let mut cases = Vec::new();
    let set_cc = |machine: &mut X86ISelFunction, cc: C| {
        let row = row_where(machine, |i| i.opcode == X86Opcode::Setcc);
        inst_mut(machine, row).operands[1] = O::CondCode(cc);
    };
    // The signed overflow read for an unsigned add.
    let (source, mut machine) = slice10_pair(InsnShape::AddU64);
    set_cc(&mut machine, C::O);
    cases.push(("AddU64/seto", source, machine));
    // The unsigned carry read for a signed add.
    let (source, mut machine) = slice10_pair(InsnShape::AddI64);
    set_cc(&mut machine, C::B);
    cases.push(("AddI64/setb", source, machine));
    // The overflow inverted.
    let (source, mut machine) = slice10_pair(InsnShape::SubU64);
    set_cc(&mut machine, C::AE);
    cases.push(("SubU64/setae", source, machine));
    // A subtraction's operands swapped (value and borrow).
    let (source, mut machine) = slice10_pair(InsnShape::SubU64);
    let sub = row_where(&machine, |i| i.opcode == X86Opcode::SubRR);
    inst_mut(&mut machine, sub).operands.swap(1, 2);
    cases.push(("SubU64/swapped", source, machine));
    // An add where the source subtracts (signed).
    let (source, mut machine) = slice10_pair(InsnShape::SubI64);
    let sub = row_where(&machine, |i| i.opcode == X86Opcode::SubRR);
    inst_mut(&mut machine, sub).opcode = X86Opcode::AddRR;
    cases.push(("SubI64/add", source, machine));
    // The product's high half (RDX) taken for its value.
    let (source, mut machine) = slice10_pair(InsnShape::MulU64);
    let mul = row_where(&machine, |i| i.opcode == X86Opcode::Mul);
    inst_mut(&mut machine, mul + 1).operands[1] = preg(RDX);
    cases.push(("MulU64/high-half", source, machine));
    // A signed multiply's overflow read as "no overflow".
    let (source, mut machine) = slice10_pair(InsnShape::MulI64);
    set_cc(&mut machine, C::NO);
    cases.push(("MulI64/setno", source, machine));
    // The complement of the signed-add fallback dropped.
    let (source, mut machine) = slice10_pair(InsnShape::AddI32);
    let not = row_where(&machine, |i| i.opcode == X86Opcode::Not);
    inst_mut(&mut machine, not).opcode = X86Opcode::MovRR;
    cases.push(("AddI32/not-dropped", source, machine));
    // The fallback's overflow word `!(a ^ b) & (a ^ (a + b))` compared with
    // -1 instead of 0: it differs only where that word is all ones, which is
    // at `a = b = 0x5555_5555` alone (a needle only the sampler's repeating
    // patterns with equal operands reach; found by the robustness probe).
    let (source, mut machine) = slice10_pair(InsnShape::AddI32);
    let zero = row_where(&machine, |i| i.opcode == X86Opcode::MovRI);
    assert_eq!(inst(&machine, zero).operands[1], O::Imm(0));
    inst_mut(&mut machine, zero).operands[1] = O::Imm(-1);
    cases.push(("AddI32/overflow-word-needle", source, machine));
    // The overflow branch on a wrong flag: the panic taken on a carry the
    // signed reading would ignore.
    let (source, mut machine) = slice10_pair(InsnShape::AddPanics);
    set_cc(&mut machine, C::O);
    cases.push(("AddPanics/seto", source, machine));
    // `not` dropped: the operand returned.
    let (source, mut machine) = slice10_pair(InsnShape::NotU64);
    let not = row_where(&machine, |i| i.opcode == X86Opcode::Not);
    inst_mut(&mut machine, not).opcode = X86Opcode::MovRR;
    cases.push(("NotU64/dropped", source, machine));
    // A negation lowered as a complement (off by one).
    let (source, mut machine) = slice10_pair(InsnShape::NegI32);
    let neg = row_where(&machine, |i| i.opcode == X86Opcode::Neg);
    inst_mut(&mut machine, neg).opcode = X86Opcode::Not;
    cases.push(("NegI32/not", source, machine));
    // A narrow count without its mask: the bits of the carrier above the
    // byte are the caller's.
    let (source, mut machine) = slice10_pair(InsnShape::CountU8);
    let mask = row_where(&machine, |i| {
        i.opcode == X86Opcode::AndRI && i.operands.len() == 2
    });
    remove_at(&mut machine, mask);
    cases.push(("CountU8/unmasked", source, machine));
    // A 16-bit count masked to a byte.
    let (source, mut machine) = slice10_pair(InsnShape::CountU16);
    let mask = row_where(&machine, |i| {
        i.opcode == X86Opcode::AndRI && i.operands.len() == 2
    });
    inst_mut(&mut machine, mask).operands[1] = O::Imm(0xff);
    cases.push(("CountU16/byte-mask", source, machine));
    // A logical shift right lowered as an arithmetic one.
    let (source, mut machine) = slice10_pair(InsnShape::ShrU64);
    let shift = row_where(&machine, |i| i.opcode == X86Opcode::ShrRR);
    inst_mut(&mut machine, shift).opcode = X86Opcode::SarRR;
    cases.push(("ShrU64/sar", source, machine));
    // A narrow count masked to 2 bits: an in-range amount of 4 to 7 is
    // shifted by its low two bits.
    let (source, mut machine) = slice10_pair(InsnShape::ShlU8);
    let mask = row_where(&machine, |i| {
        i.opcode == X86Opcode::AndRI && i.operands.last() == Some(&O::Imm(7))
    });
    inst_mut(&mut machine, mask).operands[2] = O::Imm(3);
    cases.push(("ShlU8/count-masked-to-two-bits", source, machine));
    // A narrow arithmetic shift of a zero-extended operand.
    let (source, mut machine) = slice10_pair(InsnShape::SarI16);
    let extend = row_where(&machine, |i| i.opcode == X86Opcode::MovsxW);
    inst_mut(&mut machine, extend).opcode = X86Opcode::MovzxW;
    cases.push(("SarI16/zero-extended", source, machine));
    // The count register loaded from the shifted value.
    let (source, mut machine) = slice10_pair(InsnShape::ShlChecked);
    let count = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR32 && i.operands.first() == Some(&preg(GPR32_ALIAS_BASE + RCX))
    });
    let shift = row_where(&machine, |i| i.opcode == X86Opcode::ShlRR);
    let shifted = inst(&machine, shift).operands[1].clone();
    inst_mut(&mut machine, count).operands[1] = shifted;
    cases.push(("ShlChecked/count-from-value", source, machine));
    // A call through the argument instead of the function pointer.
    let (source, mut machine) = slice10_pair(InsnShape::Indirect);
    let call = row_where(&machine, |i| i.opcode == X86Opcode::CallR);
    let argument = {
        let copy = row_where(&machine, |i| {
            i.opcode == X86Opcode::MovRR && i.operands.get(1) == Some(&preg(RSI))
        });
        inst(&machine, copy).operands[0].clone()
    };
    inst_mut(&mut machine, call).operands[0] = argument;
    cases.push(("Indirect/wrong-target", source, machine));
    cases
}

#[test]
fn every_slice_ten_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_ten_refutations() {
        refuted(&source, &machine, label);
    }
}

/// A flag reader of a flag its writer leaves undefined (Intel SDM: SF, ZF, AF
/// and PF after `imul` or `mul`) is a named undefined read, like a flag
/// reader after a call.
#[test]
fn reading_a_flag_imul_or_mul_leaves_undefined_is_a_named_mismatch() {
    use trust_cg_ir::X86CondCode as C;
    for (shape, cc) in [
        (InsnShape::MulU64, C::E),
        (InsnShape::MulI64, C::S),
        (InsnShape::MulI64, C::L),
        (InsnShape::MulU64, C::P),
    ] {
        let (source, mut machine) = slice10_pair(shape);
        let setcc = row_where(&machine, |i| i.opcode == X86Opcode::Setcc);
        inst_mut(&mut machine, setcc).operands[1] = O::CondCode(cc);
        expect_mismatch(
            &source,
            &machine,
            &format!("{shape:?}/{cc:?}"),
            |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand.starts_with("rflags")),
        );
    }
}

/// `mul` reads EAX/RAX: without the move into it, the read is undefined.
#[test]
fn mul_reads_its_accumulator() {
    let (source, mut machine) = slice10_pair(InsnShape::MulU64);
    let mul = row_where(&machine, |i| i.opcode == X86Opcode::Mul);
    remove_at(&mut machine, mul - 1);
    expect_mismatch(
        &source,
        &machine,
        "MulU64/no-accumulator",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rax"),
    );
}

/// A shift by CL reads RCX: without the move into it, the read is undefined.
#[test]
fn a_shift_by_cl_reads_its_count_register() {
    let (source, mut machine) = slice10_pair(InsnShape::ShrU64);
    let count = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR && i.operands.first() == Some(&preg(RCX))
    });
    remove_at(&mut machine, count);
    expect_mismatch(
        &source,
        &machine,
        "ShrU64/no-count",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rcx"),
    );
}

/// The stated refinement of an out-of-range variable shift: the amount
/// modulo the width. At an in-range amount it is trust-ir's shift, and the
/// theorem of an unchecked shift holds for the selector's masked lowering
/// at every amount, including the ones trust-ir leaves undefined.
#[test]
fn a_variable_shift_is_trust_irs_in_range_and_masked_beyond() {
    use crate::smt::EvalEnv;
    for (op, bits) in [
        (ShiftOp::Shl, 64u32),
        (ShiftOp::Lshr, 32),
        (ShiftOp::Ashr, 16),
        (ShiftOp::Shl, 8),
    ] {
        let mask = crate::smt::mask(u64::MAX, bits);
        for x in edge_values(bits) {
            for n in 0..(2 * u64::from(bits)) {
                let mut env = EvalEnv::default();
                env.insert("x".into(), x);
                env.insert("n".into(), n & mask);
                let shifted = shift_modulo_width(op, E::var("x", bits), E::var("n", bits));
                let k = (n % u64::from(bits)) as u32;
                let expected = match op {
                    ShiftOp::Shl => (x << k) & mask,
                    ShiftOp::Lshr => (x & mask) >> k,
                    ShiftOp::Ashr => {
                        ((((x << (64 - bits)) as i64) >> (64 - bits)) >> k) as u64 & mask
                    }
                };
                assert_eq!(
                    eval_bv(&shifted, &env),
                    expected,
                    "{op:?} {bits} {x:#x} {n}"
                );
            }
        }
    }
    for shape in [InsnShape::ShrU64, InsnShape::SarI32, InsnShape::ShlU8] {
        let (source, machine) = slice10_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(theorem_holds(&obligation), "{shape:?}");
    }
}

/// An indirect source call pairs only with `call r64` and a direct one only
/// with `call symbol`: anything else is a named call-target mismatch.
#[test]
fn an_indirect_call_pairs_only_with_a_register_call() {
    let (source, mut machine) = slice10_pair(InsnShape::Indirect);
    let call = row_where(&machine, |i| i.opcode == X86Opcode::CallR);
    let row = inst_mut(&mut machine, call);
    row.opcode = X86Opcode::Call;
    row.operands = vec![O::Symbol("g".into())];
    expect_mismatch(&source, &machine, "Indirect/as-direct", |m| {
        matches!(m, X86BodyMismatch::CallTarget { .. })
    });
    let (source, mut machine) = slice10_pair(InsnShape::IndirectThenDirect);
    let direct = row_where(&machine, |i| i.opcode == X86Opcode::Call);
    let callee = {
        let call = row_where(&machine, |i| i.opcode == X86Opcode::CallR);
        inst(&machine, call).operands[0].clone()
    };
    let row = inst_mut(&mut machine, direct);
    row.opcode = X86Opcode::CallR;
    row.operands = vec![callee];
    row.flags = X86Opcode::CallR.default_flags();
    expect_mismatch(
        &source,
        &machine,
        "IndirectThenDirect/direct-as-indirect",
        |m| matches!(m, X86BodyMismatch::CallTarget { .. }),
    );
}

/// The flags of an `add`, `sub` or `imul` reach only the readers of their
/// own block, an `add` of a private stack address writes none the walk
/// models, and every other ALU row (`and`, `not`, `popcnt`, ...) still
/// leaves them unmodelled: a reader after one makes no claim.
#[test]
fn only_the_arithmetic_rows_define_flags_a_reader_may_use() {
    let (source, mut machine) = slice10_pair(InsnShape::AddU64);
    let setcc = row_where(&machine, |i| i.opcode == X86Opcode::Setcc);
    let destination = {
        let add = row_where(&machine, |i| i.opcode == X86Opcode::AddRR);
        inst(&machine, add).operands[0].clone()
    };
    insert_at(
        &mut machine,
        setcc,
        X86ISelInst::new(
            X86Opcode::AndRI,
            vec![destination.clone(), destination, O::Imm(-1)],
        ),
    );
    expect_unsupported(&source, &machine, "AddU64/and-before-setb");
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-10
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds.
#[test]
fn optimized_slice_ten_fixtures_are_judged_without_false_mismatches() {
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
        for shape in all_slice_ten_shapes() {
            let (source, mut machine) = slice10_pair(shape);
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

const SLICE_TEN_SNAPSHOT_SHA256: &str =
    "5a237a721dca170bcb2fd2672bf5367575fc37a0395499f9f3dd50f4b72201ae";

#[test]
fn slice_ten_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice10_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_TEN {
        let (source, machine) = slice10_pair(shape);
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
            .join("tests/fixtures/x86_source_bound_body/slice10_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TEN_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_TEN_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-10 snapshots drifted");
}

/// What slice 10 refuses stays refused by name: checked arithmetic on a
/// carrier the adapter never maps to it.
#[test]
fn slice_ten_sources_outside_the_lane_are_refused_by_name() {
    let (source, _) = slice10_pair(InsnShape::AddU64);
    let narrow = {
        let mut source = source.clone();
        source.signature.params = vec![Type::I16, Type::I16];
        source.signature.returns = vec![Type::I16, Type::B1];
        if let Some(entry) = source.blocks.get_mut(&source.entry_block) {
            for (_, ty) in &mut entry.params {
                *ty = Type::I16;
            }
        }
        source
    };
    let refusal = match admitted_body(&narrow) {
        Ok(_) => panic!("a 16-bit checked add is admitted"),
        Err(refusal) => refusal.to_string(),
    };
    assert!(
        refusal.contains("checked arithmetic on a carrier other than I64"),
        "{refusal}"
    );
}
