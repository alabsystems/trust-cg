// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 6 of the x86-64 source-bound body theorem: acyclic control flow.
//! Conditional branches (`Brif` on a scalar), `Switch` compare chains, joins
//! with block parameters, several `Return`s and paths that end in a trap
//! (bare, or after a diverging call).
//!
//! Fixtures are real: LIR from the trust-ir adapter, the machine stream from
//! the real x86-64 instruction selector (`super::select`). Negative controls
//! mutate that stream and must end as a typed mismatch, a refuted theorem or
//! an unsupported (uncredited) body, never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice6::` library gate). The
//! replay on AY and Clean, the encoding evidence and the verifier-credit
//! tests are in `slice6_qualification`.

use super::slice5::describe;
use super::*;
use trust_ir::{Constant, ICmpOp, SwitchCase};

/// Slice-6 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FlowShape {
    // ---- (a) conditional branches and joins
    /// `if a < b { a } else { b }` (u64): a diamond whose join takes a block
    /// parameter.
    MinU64,
    /// `if a > b { a } else { b }` (i32): a signed order of narrow operands.
    MaxI32,
    /// `if x < 0 { 0 - x } else { x }` (i64).
    AbsI64,
    /// `if x == 0 { return 7 } x + 1`: two `Return`s.
    EarlyReturn,
    /// `if c { a } else { b }`, `c: bool` a parameter.
    BoolParam,
    /// `if c { d } else { false }` (`bool`s in and out: the clean-bool walk).
    BoolInOut,
    /// `if x != 0 { x } else { 1 }` (u8 in and out).
    U8Test,
    /// `if a < b { if a < c { 1 } else { 2 } } else { 3 }`: three paths.
    NestedIf,
    /// Two diamonds in sequence, the second on the first's join: four paths.
    TwoDiamonds,
    /// `if x > 0 { (1, x) } else { (0, 0) }`: a pair joined lane by lane.
    PairJoin,
    /// `condbr c, join(a), join(b)`: one join on both edges, through the
    /// adapter's edge copy blocks.
    EdgeCopies,
    // ---- (b) traps and calls
    /// `if x > 10 { unreachable } x`: a bare trap.
    TrapArm,
    /// `if i >= n { panic(i, n) } i`: a diverging call, then a trap.
    PanicArm,
    /// `if c { g1(x) } else { x }`: a call on one path only.
    CallArm,
    /// `let y = g1(x); if y == 0 { 1 } else { y }`: a branch on a call
    /// result.
    CallThenBranch,
    /// `if c { *p = x }` (void): an incoming store on one path.
    StoreArm,
    /// `if *p != 0 { *p } else { 5 }`: a branch on a load, a second load on
    /// one path.
    LoadBranch,
    // ---- (c) switches (compare chains)
    /// `match x { 1 => 10, 2 => 20, 7 => 70, _ => 0 }` (u64).
    Switch3,
    /// `match x { 0 => 1, 200 => 2, _ => 3 }` (u8: a high-bit case).
    SwitchU8,
    /// `match x { -1 => 1, 5 => 2, _ => 3 }` (i32: a negative case).
    SwitchI32Neg,
    /// `match x { 0x1_0000_0000 => 1, _ => 2 }` (u64: a case that is no
    /// `imm32`).
    SwitchWide,
    /// `match c { false => 1, _ => 2 }` (`switchInt` on a `bool`).
    SwitchBool,
    // ---- (d) branch-free selects and partially written slots
    /// `select(c, a, b)` (u64): one path, a 64-bit `cmovne`.
    SelectU64,
    /// `select(a < b, a, b)` (i32): a compared select, a 32-bit `cmovne`.
    SelectI32,
    /// `let (t, v); if c { t = 1; v = x } else { t = 0 }; (t, v)`: the
    /// payload slot is written on one path only, and read on both (the
    /// `Option::None` payload shape): the other path reads its initial
    /// bytes.
    PartialInit,
}

/// Every slice-6 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_six_fixture_is_qualified`] checks
/// that none is left out).
pub(crate) const SLICE_SIX: [FlowShape; 25] = [
    FlowShape::MinU64,
    FlowShape::MaxI32,
    FlowShape::AbsI64,
    FlowShape::EarlyReturn,
    FlowShape::BoolParam,
    FlowShape::BoolInOut,
    FlowShape::U8Test,
    FlowShape::NestedIf,
    FlowShape::TwoDiamonds,
    FlowShape::PairJoin,
    FlowShape::EdgeCopies,
    FlowShape::TrapArm,
    FlowShape::PanicArm,
    FlowShape::CallArm,
    FlowShape::CallThenBranch,
    FlowShape::StoreArm,
    FlowShape::LoadBranch,
    FlowShape::Switch3,
    FlowShape::SwitchU8,
    FlowShape::SwitchI32Neg,
    FlowShape::SwitchWide,
    FlowShape::SwitchBool,
    FlowShape::SelectU64,
    FlowShape::SelectI32,
    FlowShape::PartialInit,
];

impl FlowShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s6_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// The LIR the trust-ir adapter produces for a slice-6 shape.
pub(crate) fn slice6_lir(shape: FlowShape) -> Function {
    use FlowShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice6");
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let g1 = declare("g1", vec![Ty::U64], vec![Ty::U64]);
    let panic = declare("panic_at", vec![Ty::U64, Ty::U64], vec![]);
    let ptr = Ty::PtrMut(Box::new(Ty::U64));
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        MinU64 | TwoDiamonds => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        MaxI32 => (vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        AbsI64 => (vec![Ty::I64], vec![Ty::I64]),
        EarlyReturn | TrapArm | CallThenBranch | Switch3 | SwitchWide => {
            (vec![Ty::U64], vec![Ty::U64])
        }
        BoolParam | EdgeCopies => (vec![Ty::Bool, Ty::U64, Ty::U64], vec![Ty::U64]),
        BoolInOut => (vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]),
        U8Test => (vec![Ty::U8], vec![Ty::U8]),
        NestedIf => (vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        PairJoin => (vec![Ty::I64], vec![Ty::U64, Ty::I64]),
        PanicArm => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        CallArm => (vec![Ty::Bool, Ty::U64], vec![Ty::U64]),
        StoreArm => (vec![ptr.clone(), Ty::U64, Ty::Bool], vec![]),
        LoadBranch => (vec![ptr.clone()], vec![Ty::U64]),
        SwitchU8 => (vec![Ty::U8], vec![Ty::U32]),
        SwitchI32Neg => (vec![Ty::I32], vec![Ty::I32]),
        SwitchBool => (vec![Ty::Bool], vec![Ty::U64]),
        SelectU64 => (vec![Ty::Bool, Ty::U64, Ty::U64], vec![Ty::U64]),
        SelectI32 => (vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        PartialInit => (vec![Ty::U64, Ty::Bool], vec![Ty::U64, Ty::U64]),
    };
    let signature = builder.add_func_type(params.clone(), results.clone());
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    // A block that returns the constant `value` of `ty`.
    let ret_const = |f: &mut trust_ir_build::FunctionBuilder<'_>, block, ty: Ty, value: i128| {
        f.switch_to_block(block);
        let constant = f.iconst(ty, value);
        f.ret(vec![constant]);
    };
    match shape {
        MinU64 | MaxI32 => {
            let (op, ty) = if shape == MinU64 {
                (ICmpOp::Ult, Ty::U64)
            } else {
                (ICmpOp::Sgt, Ty::I32)
            };
            let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let result = f.add_block_param(join, ty.clone());
            let test = f.icmp(op, ty, args[0], args[1]);
            f.condbr(test, then, vec![], other, vec![]);
            f.switch_to_block(then);
            f.br(join, vec![args[0]]);
            f.switch_to_block(other);
            f.br(join, vec![args[1]]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
        AbsI64 => {
            let (negative, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let result = f.add_block_param(join, Ty::I64);
            let zero = f.iconst(Ty::I64, 0);
            let test = f.icmp(ICmpOp::Slt, Ty::I64, args[0], zero);
            f.condbr(test, negative, vec![], other, vec![]);
            f.switch_to_block(negative);
            let zero = f.iconst(Ty::I64, 0);
            let negated = f.sub(Ty::I64, zero, args[0]);
            f.br(join, vec![negated]);
            f.switch_to_block(other);
            f.br(join, vec![args[0]]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
        EarlyReturn => {
            let (early, rest) = (f.create_block(), f.create_block());
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Eq, Ty::U64, args[0], zero);
            f.condbr(test, early, vec![], rest, vec![]);
            ret_const(&mut f, early, Ty::U64, 7);
            f.switch_to_block(rest);
            let one = f.iconst(Ty::U64, 1);
            let sum = f.add(Ty::U64, args[0], one);
            f.ret(vec![sum]);
        }
        BoolParam => {
            let (then, other) = (f.create_block(), f.create_block());
            f.condbr(args[0], then, vec![], other, vec![]);
            f.switch_to_block(then);
            f.ret(vec![args[1]]);
            f.switch_to_block(other);
            f.ret(vec![args[2]]);
        }
        BoolInOut => {
            let (then, other) = (f.create_block(), f.create_block());
            f.condbr(args[0], then, vec![], other, vec![]);
            f.switch_to_block(then);
            f.ret(vec![args[1]]);
            f.switch_to_block(other);
            let no = f.bool_const(false);
            f.ret(vec![no]);
        }
        U8Test => {
            let (then, other) = (f.create_block(), f.create_block());
            let zero = f.iconst(Ty::U8, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U8, args[0], zero);
            f.condbr(test, then, vec![], other, vec![]);
            f.switch_to_block(then);
            f.ret(vec![args[0]]);
            ret_const(&mut f, other, Ty::U8, 1);
        }
        NestedIf => {
            let (inner, one, two, three) = (
                f.create_block(),
                f.create_block(),
                f.create_block(),
                f.create_block(),
            );
            let test = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(test, inner, vec![], three, vec![]);
            f.switch_to_block(inner);
            let test = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[2]);
            f.condbr(test, one, vec![], two, vec![]);
            ret_const(&mut f, one, Ty::U64, 1);
            ret_const(&mut f, two, Ty::U64, 2);
            ret_const(&mut f, three, Ty::U64, 3);
        }
        TwoDiamonds => {
            let (then1, else1, join1) = (f.create_block(), f.create_block(), f.create_block());
            let (then2, else2, join2) = (f.create_block(), f.create_block(), f.create_block());
            let low = f.add_block_param(join1, Ty::U64);
            let result = f.add_block_param(join2, Ty::U64);
            let test = f.icmp(ICmpOp::Ult, Ty::U64, args[0], args[1]);
            f.condbr(test, then1, vec![], else1, vec![]);
            f.switch_to_block(then1);
            f.br(join1, vec![args[0]]);
            f.switch_to_block(else1);
            f.br(join1, vec![args[1]]);
            f.switch_to_block(join1);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Eq, Ty::U64, low, zero);
            f.condbr(test, then2, vec![], else2, vec![]);
            f.switch_to_block(then2);
            f.br(join2, vec![args[0]]);
            f.switch_to_block(else2);
            f.br(join2, vec![low]);
            f.switch_to_block(join2);
            f.ret(vec![result]);
        }
        PairJoin => {
            let (some, none, join) = (f.create_block(), f.create_block(), f.create_block());
            let tag = f.add_block_param(join, Ty::U64);
            let payload = f.add_block_param(join, Ty::I64);
            let zero = f.iconst(Ty::I64, 0);
            let test = f.icmp(ICmpOp::Sgt, Ty::I64, args[0], zero);
            f.condbr(test, some, vec![], none, vec![]);
            f.switch_to_block(some);
            let one = f.iconst(Ty::U64, 1);
            f.br(join, vec![one, args[0]]);
            f.switch_to_block(none);
            let zero_tag = f.iconst(Ty::U64, 0);
            let zero_payload = f.iconst(Ty::I64, 0);
            f.br(join, vec![zero_tag, zero_payload]);
            f.switch_to_block(join);
            f.ret(vec![tag, payload]);
        }
        EdgeCopies => {
            let join = f.create_block();
            let result = f.add_block_param(join, Ty::U64);
            f.condbr(args[0], join, vec![args[1]], join, vec![args[2]]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
        TrapArm => {
            let (trap, ok) = (f.create_block(), f.create_block());
            let ten = f.iconst(Ty::U64, 10);
            let test = f.icmp(ICmpOp::Ugt, Ty::U64, args[0], ten);
            f.condbr(test, trap, vec![], ok, vec![]);
            f.switch_to_block(trap);
            f.unreachable();
            f.switch_to_block(ok);
            f.ret(vec![args[0]]);
        }
        PanicArm => {
            let (fail, ok) = (f.create_block(), f.create_block());
            let test = f.icmp(ICmpOp::Uge, Ty::U64, args[0], args[1]);
            f.condbr(test, fail, vec![], ok, vec![]);
            f.switch_to_block(fail);
            f.call_void(panic, vec![args[0], args[1]]);
            f.unreachable();
            f.switch_to_block(ok);
            f.ret(vec![args[0]]);
        }
        CallArm => {
            let (call, skip, join) = (f.create_block(), f.create_block(), f.create_block());
            let result = f.add_block_param(join, Ty::U64);
            f.condbr(args[0], call, vec![], skip, vec![]);
            f.switch_to_block(call);
            let y = f.call(g1, vec![args[1]]);
            f.br(join, vec![y]);
            f.switch_to_block(skip);
            f.br(join, vec![args[1]]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
        CallThenBranch => {
            let (zero_arm, other) = (f.create_block(), f.create_block());
            let y = f.call(g1, vec![args[0]]);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Eq, Ty::U64, y, zero);
            f.condbr(test, zero_arm, vec![], other, vec![]);
            ret_const(&mut f, zero_arm, Ty::U64, 1);
            f.switch_to_block(other);
            f.ret(vec![y]);
        }
        StoreArm => {
            let (store, done) = (f.create_block(), f.create_block());
            f.condbr(args[2], store, vec![], done, vec![]);
            f.switch_to_block(store);
            f.store(Ty::U64, args[0], args[1]);
            f.br(done, vec![]);
            f.switch_to_block(done);
            f.ret(vec![]);
        }
        LoadBranch => {
            let (reload, other) = (f.create_block(), f.create_block());
            let value = f.load(Ty::U64, args[0]);
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, value, zero);
            f.condbr(test, reload, vec![], other, vec![]);
            f.switch_to_block(reload);
            let again = f.load(Ty::U64, args[0]);
            f.ret(vec![again]);
            ret_const(&mut f, other, Ty::U64, 5);
        }
        Switch3 | SwitchU8 | SwitchI32Neg | SwitchWide | SwitchBool => {
            let (cases, result_ty): (Vec<(i128, i128)>, Ty) = match shape {
                Switch3 => (vec![(1, 10), (2, 20), (7, 70)], Ty::U64),
                SwitchU8 => (vec![(0, 1), (200, 2)], Ty::U32),
                SwitchI32Neg => (vec![(-1, 1), (5, 2)], Ty::I32),
                SwitchWide => (vec![(0x1_0000_0000, 1)], Ty::U64),
                _ => (vec![(0, 1)], Ty::U64),
            };
            let targets: Vec<_> = cases.iter().map(|_| f.create_block()).collect();
            let default = f.create_block();
            f.switch(
                args[0],
                cases
                    .iter()
                    .zip(&targets)
                    .map(|((value, _), target)| SwitchCase {
                        value: Constant::Int(*value),
                        target: *target,
                        args: vec![],
                    })
                    .collect(),
                default,
                vec![],
            );
            for ((_, result), target) in cases.iter().zip(&targets) {
                ret_const(&mut f, *target, result_ty.clone(), *result);
            }
            let fallback = if shape == Switch3 { 0 } else { 3 };
            let fallback = if matches!(shape, SwitchWide | SwitchBool) {
                2
            } else {
                fallback
            };
            ret_const(&mut f, default, result_ty, fallback);
        }
        SelectU64 => {
            let chosen = f.select(Ty::U64, args[0], args[1], args[2]);
            f.ret(vec![chosen]);
        }
        SelectI32 => {
            let less = f.icmp(ICmpOp::Slt, Ty::I32, args[0], args[1]);
            let chosen = f.select(Ty::I32, less, args[0], args[1]);
            f.ret(vec![chosen]);
        }
        PartialInit => {
            let (some, none, join) = (f.create_block(), f.create_block(), f.create_block());
            let tag = f.alloca(Ty::U64);
            let payload = f.alloca(Ty::U64);
            f.condbr(args[1], some, vec![], none, vec![]);
            f.switch_to_block(some);
            let one = f.iconst(Ty::U64, 1);
            f.store(Ty::U64, tag, one);
            f.store(Ty::U64, payload, args[0]);
            f.br(join, vec![]);
            f.switch_to_block(none);
            let zero = f.iconst(Ty::U64, 0);
            f.store(Ty::U64, tag, zero);
            f.br(join, vec![]);
            f.switch_to_block(join);
            let tag = f.load(Ty::U64, tag);
            let payload = f.load(Ty::U64, payload);
            f.ret(vec![tag, payload]);
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

pub(crate) fn slice6_pair(shape: FlowShape) -> (Function, X86ISelFunction) {
    let source = slice6_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// The LIR of `source`, one line per instruction, for failure messages.
pub(crate) fn describe_lir(source: &Function) -> String {
    let mut text = String::new();
    for block in source.layout_order() {
        let body = &source.blocks[&block];
        text.push_str(&format!("  {block:?} params={:?}\n", body.params));
        for inst in &body.instructions {
            text.push_str(&format!(
                "    {:?} {:?} -> {:?}\n",
                inst.opcode, inst.args, inst.results
            ));
        }
    }
    text
}

/// The path claims of a several-path theorem, `(C, X)` per source path.
pub(crate) fn path_claims(obligation: &ProofObligation) -> Vec<(E, E)> {
    assert_eq!(obligation.trust_ir_expr, E::bool_const(true));
    let mut claims = Vec::new();
    let mut conjunction = &obligation.aarch64_expr;
    loop {
        let (claim, rest) = match conjunction {
            E::And { lhs, rhs } => (lhs.as_ref(), Some(rhs.as_ref())),
            last => (last, None),
        };
        let E::Or { lhs, rhs } = claim else {
            panic!("path claim {claim} is not (or (not C) X)")
        };
        let E::Not { operand } = lhs.as_ref() else {
            panic!("path claim {claim} is not (or (not C) X)")
        };
        claims.push((operand.as_ref().clone(), rhs.as_ref().clone()));
        match rest {
            Some(rest) => conjunction = rest,
            None => return claims,
        }
    }
}

/// Evaluate a several-path theorem at one sampled assignment of its free
/// inputs (the premises are definitional): whether the machine side is
/// `true`, and which source paths' conditions hold. Test-only semantics
/// check; it is never credit.
fn evaluate_paths(obligation: &ProofObligation, seed: u64) -> (bool, Vec<bool>) {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    let mut state = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let constants = theorem_constants(obligation);
    for (i, (name, width)) in free_inputs_of(obligation).into_iter().enumerate() {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        // Past the random seeds, every input takes the theorem's constants
        // and their neighbours (a switch case, a compared constant), which
        // random words almost never meet.
        let value = match seed.checked_sub(RANDOM_SEEDS) {
            Some(k) => {
                let k = k as usize + i;
                let constant = constants[(k / 3) % constants.len()];
                match k % 3 {
                    0 => constant,
                    1 => constant.wrapping_add(1),
                    _ => constant.wrapping_sub(1),
                }
            }
            None => {
                // Dense words, sparse bytes and small values, drawn from the
                // generator's high bits (its low bits have short periods).
                let high = state >> 29;
                match seed % 4 {
                    0 => high & 0xff,
                    1 => high % 12,
                    2 => high & 0x1_ffff_ffff,
                    _ => state ^ (state >> 31),
                }
            }
        };
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
            panic!("definition of {name} is not a bitvector")
        };
        env.insert(name.clone(), value);
    }
    let holds = |expr: &E| matches!(expr.eval(&env), EvalResult::Bool(true));
    let conditions = path_claims(obligation)
        .iter()
        .map(|(condition, _)| holds(condition))
        .collect();
    (holds(&obligation.aarch64_expr), conditions)
}

/// Random samples before the constant-driven ones.
const RANDOM_SEEDS: u64 = 256;

/// Every bitvector constant the obligation mentions (its value, whatever
/// its width), in first-seen order, and 0.
fn theorem_constants(obligation: &ProofObligation) -> Vec<u64> {
    fn walk(expr: &E, constants: &mut Vec<u64>) {
        if let E::BvConst { value, .. } = expr
            && !constants.contains(value)
        {
            constants.push(*value);
        }
        expr.for_each_child(&mut |child| walk(child, constants));
    }
    let mut constants = vec![0];
    for expr in [&obligation.trust_ir_expr, &obligation.aarch64_expr]
        .into_iter()
        .chain(&obligation.preconditions)
    {
        walk(expr, &mut constants);
    }
    constants
}

/// The samples a several-path theorem is evaluated at.
fn sample_seeds(obligation: &ProofObligation) -> std::ops::Range<u64> {
    0..RANDOM_SEEDS + 3 * theorem_constants(obligation).len() as u64 * 4
}

/// Whether a several-path theorem holds at every sample, and every source
/// path's condition holds at some sample (each path is exercised).
pub(crate) fn paths_hold_on_samples(obligation: &ProofObligation) -> bool {
    let mut exercised = vec![false; path_claims(obligation).len()];
    for seed in sample_seeds(obligation) {
        let (holds, conditions) = evaluate_paths(obligation, seed);
        if !holds {
            return false;
        }
        assert_eq!(
            conditions.iter().filter(|c| **c).count(),
            1,
            "exactly one source path is taken at seed {seed}"
        );
        for (seen, now) in exercised.iter_mut().zip(conditions) {
            *seen |= now;
        }
    }
    exercised.into_iter().all(|seen| seen)
}

/// Whether some sample refutes a several-path theorem.
pub(crate) fn paths_refuted_on_samples(obligation: &ProofObligation) -> bool {
    sample_seeds(obligation).any(|seed| !evaluate_paths(obligation, seed).0)
}

/// Whether the theorem of `shape`'s owner holds (sampled): the one-path
/// check of slices 1 to 5, or the several-path check.
fn theorem_holds(obligation: &ProofObligation) -> bool {
    if path_form(obligation) {
        paths_hold_on_samples(obligation)
    } else {
        holds_on_samples(obligation)
    }
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_slice_six_shapes() -> Vec<FlowShape> {
    use FlowShape::*;
    let all = SLICE_SIX.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            MinU64 | MaxI32 | AbsI64 | EarlyReturn | BoolParam | BoolInOut | U8Test | NestedIf
            | TwoDiamonds | PairJoin | EdgeCopies | TrapArm | PanicArm | CallArm
            | CallThenBranch | StoreArm | LoadBranch | Switch3 | SwitchU8 | SwitchI32Neg
            | SwitchWide | SwitchBool | SelectU64 | SelectI32 | PartialInit => {}
        }
    }
    all
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

#[test]
fn owner_builds_for_every_slice_six_shape_and_covers_every_value_row() {
    for shape in SLICE_SIX {
        let (source, machine) = slice6_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap_or_else(|refusal| {
            panic!(
                "{shape:?}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        // Every row but a jump, a return, a call and a trap is covered: the
        // conditional jumps too, whose direction the theorem states.
        let expected: Vec<usize> = rows(&machine)
            .into_iter()
            .filter(|(_, block, index)| {
                let opcode = machine.blocks[block].insts[*index].opcode;
                !opcode.is_pseudo()
                    && !matches!(
                        opcode,
                        X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Call | X86Opcode::Ud2
                    )
            })
            .map(|(ordinal, _, _)| ordinal)
            .collect();
        assert_eq!(
            owner.bound_rows(),
            expected,
            "{shape:?}\n{}",
            describe(&machine)
        );
        let entries = free_inputs_of(owner.obligation());
        assert_eq!(
            owner_check(&source, &machine, owner.obligation(), &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(owner.obligation().is_genuinely_proven(), "{shape:?}");
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
        // One claim per source path (a select is one path).
        let paths = source_paths(&source).unwrap().len();
        if matches!(shape, FlowShape::SelectU64 | FlowShape::SelectI32) {
            assert_eq!(paths, 1, "{shape:?}");
        } else {
            assert!(paths > 1, "{shape:?}");
            assert_eq!(path_claims(owner.obligation()).len(), paths, "{shape:?}");
        }
    }
}

#[test]
fn slice_six_theorems_hold_on_samples() {
    for shape in SLICE_SIX {
        let (source, machine) = slice6_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert!(
            theorem_holds(owner.obligation()),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_SIX`]: every fixture whose real selection the owner admits with a
/// theorem that holds must be in it, so none is silently left out of
/// qualification.
#[test]
fn every_admitted_slice_six_fixture_is_qualified() {
    for shape in all_slice_six_shapes() {
        let (source, machine) = slice6_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV)
            .is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(
            SLICE_SIX.contains(&shape),
            holds,
            "{shape:?}: SLICE_SIX must hold exactly the admitted fixtures whose theorem holds"
        );
    }
}

// ---------------------------------------------------------------------------
// Negative controls (no solver)
// ---------------------------------------------------------------------------

/// The walk ordinal of the `n`-th row with `opcode`.
fn nth(machine: &X86ISelFunction, opcode: X86Opcode, n: usize) -> usize {
    find(machine, opcode)
        .get(n)
        .copied()
        .unwrap_or_else(|| panic!("no {opcode:?} #{n}\n{}", describe(machine)))
}

/// The block holding walk ordinal `ordinal`.
fn block_of(machine: &X86ISelFunction, ordinal: usize) -> Block {
    rows(machine)[ordinal].1
}

fn condition(machine: &X86ISelFunction, ordinal: usize) -> trust_cg_ir::X86CondCode {
    let O::CondCode(cc) = inst(machine, ordinal).operands[0] else {
        panic!("row {ordinal} is no Jcc")
    };
    cc
}

fn condition_of_setcc(machine: &X86ISelFunction, ordinal: usize) -> trust_cg_ir::X86CondCode {
    let O::CondCode(cc) = inst(machine, ordinal).operands[1] else {
        panic!("row {ordinal} is no Setcc")
    };
    cc
}

fn set_condition(machine: &mut X86ISelFunction, ordinal: usize, cc: trust_cg_ir::X86CondCode) {
    let row = inst_mut(machine, ordinal);
    let index = usize::from(row.opcode == X86Opcode::Setcc);
    row.operands[index] = O::CondCode(cc);
}

/// The operand the entry block copies argument register `root` into (its
/// value register).
fn entry_copy(machine: &X86ISelFunction, root: u16) -> O {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| inst(machine, ordinal))
        .find(|row| {
            row.opcode == X86Opcode::MovRR
                && row.operands.get(1).and_then(gpr).map(|reg| reg.root)
                    == Some(Root::Physical(root))
        })
        .map(|row| row.operands[0].clone())
        .unwrap_or_else(|| panic!("no entry copy of root {root}\n{}", describe(machine)))
}

/// The `arm`-th arm's copy into the join parameter (the `MovRR`/`MovRR32`
/// that is the only row of its block besides the `Jmp`).
fn join_copy(machine: &X86ISelFunction, arm: usize) -> usize {
    let mut copies = rows(machine).into_iter().filter(|(ordinal, block, _)| {
        let body = &machine.blocks[block].insts;
        body.len() == 2
            && matches!(
                inst(machine, *ordinal).opcode,
                X86Opcode::MovRR | X86Opcode::MovRR32
            )
            && body[1].opcode == X86Opcode::Jmp
    });
    copies
        .nth(arm)
        .map(|(ordinal, _, _)| ordinal)
        .unwrap_or_else(|| panic!("no join copy of arm {arm}\n{}", describe(machine)))
}

/// `MinU64` in the fused form the O1+ peephole leaves: `cmp a, b; jb then`
/// (the `setcc`, its two extensions, the mask and the zero test removed).
pub(crate) fn fused_min() -> (Function, X86ISelFunction) {
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let setcc = nth(&machine, X86Opcode::Setcc, 0);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    for ordinal in (setcc..jcc).rev() {
        remove_at(&mut machine, ordinal);
    }
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    set_condition(&mut machine, jcc, trust_cg_ir::X86CondCode::B);
    (source, machine)
}

/// `fn(n: u64) -> u64 { let mut i = 0; while i < n { i += 1 } i }`: a loop.
pub(crate) fn counting_loop() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice6");
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s6_counting_loop", signature);
    let entry = f.create_block();
    let header = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    let n = f.add_block_param(entry, Ty::U64);
    let i = f.add_block_param(header, Ty::U64);
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    f.br(header, vec![zero]);
    f.switch_to_block(header);
    let lt = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(lt, body, vec![], exit, vec![]);
    f.switch_to_block(body);
    let one = f.iconst(Ty::U64, 1);
    let next = f.add(Ty::U64, i, one);
    f.br(header, vec![next]);
    f.switch_to_block(exit);
    f.ret(vec![i]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .remove(0)
    .0
}

/// Replace row `ordinal` by `opcode operands`, keeping its TV-1 provenance
/// (a wrong lowering of the same LIR instruction).
fn replace_row(machine: &mut X86ISelFunction, ordinal: usize, opcode: X86Opcode, operands: Vec<O>) {
    let provenance = inst(machine, ordinal).lowering_provenance;
    let row = inst_mut(machine, ordinal);
    *row = X86ISelInst::new(opcode, operands);
    row.lowering_provenance = provenance;
}

/// An extra `jcc cc, target` before row `before`, with its edge recorded
/// first among the block's successors.
fn insert_jump(
    machine: &mut X86ISelFunction,
    before: usize,
    cc: trust_cg_ir::X86CondCode,
    target: Block,
) {
    insert_at(
        machine,
        before,
        X86ISelInst::new(X86Opcode::Jcc, vec![O::CondCode(cc), O::Block(target)]),
    );
    let block = block_of(machine, before);
    let successors = &mut machine.blocks.get_mut(&block).unwrap().successors;
    successors.retain(|successor| *successor != target);
    successors.insert(0, target);
}

/// Wrong lowerings of slice-6 shapes the owner binds: the sampled oracle
/// refutes each one here, and the replayed theorem must be refuted by AY with
/// a counterexample (`slice6_qualification`). Together with
/// [`wrong_control_is_named_or_refused`] they cover the slice's negative
/// controls: an inverted condition, swapped successors, a wrong condition
/// code (signed/unsigned, strict/non-strict), a trap on the wrong condition,
/// a join taking the wrong arm's value, an early return with the wrong
/// value, and the select, switch and partially-written-slot forms. (A
/// machine path the source does not have breaks the block correspondence:
/// no claim, in [`wrong_control_is_named_or_refused`].)
pub(crate) fn slice_six_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use trust_cg_ir::X86CondCode as C;
    let mut cases = Vec::new();
    // An inverted branch condition.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    assert_eq!(condition(&machine, jcc), C::NE);
    set_condition(&mut machine, jcc, C::E);
    cases.push(("inverted branch condition", source, machine));
    // Swapped successors, the recorded edges swapped with them (so the
    // control skeleton agrees and only the theorem can judge).
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let jmp = jcc + 1;
    let (taken, other) = (
        inst(&machine, jcc).operands[1].clone(),
        inst(&machine, jmp).operands[0].clone(),
    );
    inst_mut(&mut machine, jcc).operands[1] = other;
    inst_mut(&mut machine, jmp).operands[0] = taken;
    let entry = block_of(&machine, jcc);
    machine.blocks.get_mut(&entry).unwrap().successors.reverse();
    cases.push(("swapped successors", source, machine));
    // A wrong condition code at the compare that feeds the branch, and at a
    // fused compare-and-branch (the O1+ peephole's `cmp; jb`).
    for (cc, label) in [
        (C::L, "signed for unsigned"),
        (C::BE, "non-strict for strict"),
    ] {
        let (source, mut machine) = slice6_pair(FlowShape::MinU64);
        let setcc = nth(&machine, X86Opcode::Setcc, 0);
        assert_eq!(condition_of_setcc(&machine, setcc), C::B);
        set_condition(&mut machine, setcc, cc);
        cases.push((label, source, machine));
    }
    for (cc, label) in [
        (C::L, "fused signed for unsigned"),
        (C::BE, "fused non-strict for strict"),
        (C::AE, "fused inverted"),
    ] {
        let (source, mut machine) = fused_min();
        let jcc = nth(&machine, X86Opcode::Jcc, 0);
        set_condition(&mut machine, jcc, cc);
        cases.push((label, source, machine));
    }
    for (cc, label) in [(C::B, "unsigned for signed"), (C::GE, "non-strict signed")] {
        let (source, mut machine) = slice6_pair(FlowShape::MaxI32);
        let setcc = nth(&machine, X86Opcode::Setcc, 0);
        assert_eq!(condition_of_setcc(&machine, setcc), C::G);
        set_condition(&mut machine, setcc, cc);
        cases.push((label, source, machine));
    }
    // A trap on the wrong condition (after a panic call, and bare).
    for (shape, label) in [
        (FlowShape::PanicArm, "panic on the wrong condition"),
        (FlowShape::TrapArm, "trap on the wrong condition"),
    ] {
        let (source, mut machine) = slice6_pair(shape);
        let jcc = nth(&machine, X86Opcode::Jcc, 0);
        set_condition(&mut machine, jcc, C::E);
        cases.push((label, source, machine));
    }
    // A join taking the wrong arm's value.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let b = entry_copy(&machine, RSI);
    let arm_copy = join_copy(&machine, 0);
    inst_mut(&mut machine, arm_copy).operands[1] = b;
    cases.push(("join takes the other arm's value", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::MaxI32);
    let then_value = inst(&machine, join_copy(&machine, 0)).operands[1].clone();
    let arm_copy = join_copy(&machine, 1);
    inst_mut(&mut machine, arm_copy).operands[1] = then_value;
    cases.push(("narrow join takes the other arm's value", source, machine));
    // An early return with the wrong value.
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let seven = find(&machine, X86Opcode::MovRI)
        .into_iter()
        .find(|row| inst(&machine, *row).operands[1] == O::Imm(7))
        .expect("the early return's constant");
    inst_mut(&mut machine, seven).operands[1] = O::Imm(8);
    cases.push(("early return with the wrong value", source, machine));
    // A switch case against the wrong constant, and a case test inverted.
    let (source, mut machine) = slice6_pair(FlowShape::Switch3);
    let cmp = find(&machine, X86Opcode::CmpRI)
        .into_iter()
        .find(|row| inst(&machine, *row).operands[1] == O::Imm(2))
        .expect("the case-2 compare");
    inst_mut(&mut machine, cmp).operands[1] = O::Imm(3);
    cases.push(("switch case against the wrong constant", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::SwitchU8);
    let jcc = nth(&machine, X86Opcode::Jcc, 1);
    set_condition(&mut machine, jcc, C::NE);
    cases.push(("switch case test inverted", source, machine));
    // A narrow switch selector compared without its zero extension.
    let (source, mut machine) = slice6_pair(FlowShape::SwitchU8);
    let movzx = nth(&machine, X86Opcode::Movzx, 0);
    inst_mut(&mut machine, movzx).opcode = X86Opcode::MovsxB;
    cases.push(("narrow selector sign-extended", source, machine));
    // A select's condition inverted, and its arms swapped.
    let (source, mut machine) = slice6_pair(FlowShape::SelectU64);
    let cmov = nth(&machine, X86Opcode::Cmovcc, 0);
    inst_mut(&mut machine, cmov).operands[2] = O::CondCode(C::E);
    cases.push(("select condition inverted", source, machine));
    let (source, mut machine) = slice6_pair(FlowShape::SelectI32);
    let cmov = nth(&machine, X86Opcode::Cmovcc32, 0);
    let setcc = nth(&machine, X86Opcode::Setcc, 0);
    set_condition(&mut machine, setcc, C::B);
    let _ = cmov;
    cases.push(("compared select, unsigned for signed", source, machine));
    // A partially written slot read at the wrong offset: the path that
    // wrote the payload reads the tag slot instead.
    let (source, mut machine) = slice6_pair(FlowShape::PartialInit);
    let payload_load = nth(&machine, X86Opcode::MovRM, 1);
    let tag_base = inst(&machine, nth(&machine, X86Opcode::MovRM, 0)).operands[1].clone();
    inst_mut(&mut machine, payload_load).operands[1] = tag_base;
    cases.push(("payload read from the tag slot", source, machine));
    cases
}

#[test]
fn every_slice_six_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_six_refutations() {
        let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        let refuted = if path_form(&theorem) {
            paths_refuted_on_samples(&theorem)
        } else {
            refuted_on_samples(&theorem)
        };
        assert!(
            refuted,
            "{label}: the theorem must refute the wrong lowering\n{}",
            describe(&machine)
        );
    }
}

/// Whether `obligation` is a several-path theorem.
fn path_form(obligation: &ProofObligation) -> bool {
    obligation.trust_ir_expr == E::bool_const(true)
        && matches!(
            &obligation.aarch64_expr,
            E::And { lhs, .. } if matches!(lhs.as_ref(), E::Or { .. })
        )
}

/// Control defects the walk names before any theorem exists, and machine
/// shapes outside the pairing it makes no claim about: a flag writer
/// between a compare and its jump (or `cmov`), flags an ALU row wrote,
/// flags from another block, flags a call left undefined (also when a
/// compare set them before the call), a missing trap, a wrong arm value (the
/// theorem refutes it: several paths get no exact affine refusal), a jump to
/// a block no LIR block lowers, a dead laid-out block, an extra machine
/// branch, both edges of a branch to one arm (either arm), a return before
/// the source path ends, a switch with two edges to one block, an
/// if-converted (`cmov`) diamond, and a loop. Every machine CFG without the
/// block correspondence makes no claim; none is a named mismatch.
#[test]
fn wrong_control_is_named_or_refused() {
    use trust_cg_ir::X86CondCode as C;
    // A flag-writing row between the compare and its jump: its flags are
    // not modelled, so no claim.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    insert_at(
        &mut machine,
        jcc,
        X86ISelInst::new(X86Opcode::MovRI, vec![vreg(90), O::Imm(0)]),
    );
    insert_at(
        &mut machine,
        jcc + 1,
        X86ISelInst::new(X86Opcode::AddRI, vec![vreg(90), vreg(90), O::Imm(1)]),
    );
    expect_unsupported(&source, &machine, "flag clobber between cmp and jcc");
    // ... and before a cmov.
    let (source, mut machine) = slice6_pair(FlowShape::SelectU64);
    let cmov = nth(&machine, X86Opcode::Cmovcc, 0);
    insert_at(
        &mut machine,
        cmov,
        X86ISelInst::new(X86Opcode::AndRI, vec![vreg(4), vreg(4), O::Imm(1)]),
    );
    expect_unsupported(&source, &machine, "flag clobber between cmp and cmov");
    // Flags an ALU row wrote: the second diamond's zero test removed, so its
    // jump reads the flags of the mask's `and`.
    let (source, mut machine) = slice6_pair(FlowShape::TwoDiamonds);
    let second = nth(&machine, X86Opcode::Jcc, 1);
    let cmp = (0..second)
        .rev()
        .find(|row| inst(&machine, *row).opcode == X86Opcode::CmpRI)
        .unwrap();
    remove_at(&mut machine, cmp);
    expect_unsupported(&source, &machine, "flags an ALU row wrote before a jump");
    // Flags from another block: every row of the second diamond's block
    // before its jump removed, so the jump would read the first block's
    // compare (no row between them writes the flags).
    let (source, mut machine) = slice6_pair(FlowShape::TwoDiamonds);
    let second = nth(&machine, X86Opcode::Jcc, 1);
    let block = block_of(&machine, second);
    let first = (0..second)
        .find(|row| block_of(&machine, *row) == block)
        .unwrap();
    for row in (first..second).rev() {
        remove_at(&mut machine, row);
    }
    expect_unsupported(&source, &machine, "flags from another block");
    // Flags a call left undefined: the compare after the call, the `bool` it
    // sets and the branch's zero test removed, so the jump reads the flags
    // the callee left.
    let (source, mut machine) = slice6_pair(FlowShape::CallThenBranch);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let first = nth(&machine, X86Opcode::CmpRR, 0);
    for row in (first..jcc).rev() {
        remove_at(&mut machine, row);
    }
    expect_mismatch(
        &source,
        &machine,
        "jump on flags a call left undefined",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rflags"),
    );
    // ... and flags a compare set BEFORE the call: the call still leaves them
    // undefined (a compare of the argument, then the call, then the jump).
    let (source, mut machine) = slice6_pair(FlowShape::CallThenBranch);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let first = nth(&machine, X86Opcode::CmpRR, 0);
    for row in (first..jcc).rev() {
        remove_at(&mut machine, row);
    }
    let call = nth(&machine, X86Opcode::Call, 0);
    let argument = inst(&machine, 0).operands[0].clone();
    insert_at(
        &mut machine,
        call,
        X86ISelInst::new(X86Opcode::CmpRI, vec![argument, O::Imm(0)]),
    );
    expect_mismatch(
        &source,
        &machine,
        "jump on flags set before a call",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rflags"),
    );
    // A cmov whose destination holds nothing (the move of the else value
    // removed): the value it keeps when the condition fails is undefined.
    let (source, mut machine) = slice6_pair(FlowShape::SelectU64);
    let cmov = nth(&machine, X86Opcode::Cmovcc, 0);
    let kept = inst(&machine, cmov).operands[0].clone();
    let init = (0..cmov)
        .rev()
        .find(|row| {
            let row = inst(&machine, *row);
            row.opcode == X86Opcode::MovRR && row.operands[0] == kept
        })
        .unwrap();
    remove_at(&mut machine, init);
    expect_mismatch(&source, &machine, "cmov into an undefined register", |m| {
        matches!(m, X86BodyMismatch::UndefinedRead { .. })
    });
    // A missing trap: the trap arm returns, or runs off its block.
    let (source, mut machine) = slice6_pair(FlowShape::TrapArm);
    let ud2 = nth(&machine, X86Opcode::Ud2, 0);
    replace_row(&mut machine, ud2, X86Opcode::Ret, vec![]);
    expect_mismatch(
        &source,
        &machine,
        "returns where the source traps",
        |m| matches!(m, X86BodyMismatch::Control { detail, .. } if detail.contains("diverges")),
    );
    let (source, mut machine) = slice6_pair(FlowShape::PanicArm);
    let ud2 = nth(&machine, X86Opcode::Ud2, 0);
    remove_at(&mut machine, ud2);
    expect_mismatch(&source, &machine, "a trap removed", |m| {
        matches!(m, X86BodyMismatch::Control { .. })
    });
    // ... and a trap where the source returns.
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let ret = nth(&machine, X86Opcode::Ret, 0);
    replace_row(&mut machine, ret, X86Opcode::Ud2, vec![]);
    expect_mismatch(
        &source,
        &machine,
        "traps where the source returns",
        |m| matches!(m, X86BodyMismatch::Control { detail, .. } if detail.contains("returns")),
    );
    // A wrong arm value: with several paths the owner builds the theorem
    // (no exact affine refusal, which ignores the path condition), and the
    // theorem refutes it.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let b = entry_copy(&machine, RSI);
    let arm_copy = join_copy(&machine, 0);
    inst_mut(&mut machine, arm_copy).operands[1] = b;
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("wrong arm value: {refusal}"));
    assert!(
        paths_refuted_on_samples(owner.obligation()),
        "wrong arm value"
    );
    // A machine path to a block no LIR block lowers: no claim.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let extra = Block(source.blocks.keys().map(|block| block.0).max().unwrap() + 1);
    machine.ensure_block(extra);
    machine
        .blocks
        .get_mut(&extra)
        .unwrap()
        .insts
        .push(X86ISelInst::new(X86Opcode::Ret, vec![]));
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    insert_jump(&mut machine, jcc, C::O, extra);
    expect_unsupported(&source, &machine, "a jump to a machine-only block");
    // A laid-out block no machine transfer reaches either (dead code): it
    // lowers no LIR block, so no claim.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let extra = Block(source.blocks.keys().map(|block| block.0).max().unwrap() + 1);
    machine.ensure_block(extra);
    machine
        .blocks
        .get_mut(&extra)
        .unwrap()
        .insts
        .push(X86ISelInst::new(X86Opcode::Ret, vec![]));
    expect_unsupported(&source, &machine, "a dead laid-out block");
    // A machine path the source does not have: an extra branch out of the
    // `then` arm into the `else` arm. Its successors are not the LIR's.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let arm_copy = join_copy(&machine, 0);
    let else_block = block_of(&machine, join_copy(&machine, 1));
    let value = inst(&machine, arm_copy).operands[1].clone();
    insert_at(
        &mut machine,
        arm_copy,
        X86ISelInst::new(X86Opcode::CmpRI, vec![value, O::Imm(5)]),
    );
    insert_jump(&mut machine, arm_copy + 1, C::E, else_block);
    expect_unsupported(&source, &machine, "an extra machine branch");
    // A laid-out LIR block no source path reaches: named.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let then_block = match &inst(&machine, jcc).operands[1] {
        O::Block(block) => *block,
        other => panic!("{other:?}"),
    };
    // Both edges to the `else` block: `then` is laid out but unreachable.
    let else_block = match &inst(&machine, jcc + 1).operands[0] {
        O::Block(block) => *block,
        other => panic!("{other:?}"),
    };
    inst_mut(&mut machine, jcc).operands[1] = O::Block(else_block);
    let entry = block_of(&machine, jcc);
    machine.blocks.get_mut(&entry).unwrap().successors = vec![else_block];
    // The entry's successors are not the LIR's: no claim.
    expect_unsupported(&source, &machine, "both edges to one arm");
    // Recorded successors that are not the block's transfers (an edge
    // missing): named, whatever their order.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let entry = block_of(&machine, jcc);
    machine.blocks.get_mut(&entry).unwrap().successors = vec![then_block];
    expect_mismatch(&source, &machine, "a recorded edge missing", |m| {
        matches!(m, X86BodyMismatch::Control { detail, .. }
            if detail.starts_with("records successors"))
    });
    // ... and both edges to the arm the jump already takes: the jump's
    // direction decides nothing, so no claim.
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    inst_mut(&mut machine, jcc + 1).operands[0] = O::Block(then_block);
    let entry = block_of(&machine, jcc);
    machine.blocks.get_mut(&entry).unwrap().successors = vec![then_block];
    expect_unsupported(
        &source,
        &machine,
        "a jump whose fallthrough reaches its target",
    );
    // A return in the middle of a source path: the `else` arm returns where
    // the source continues to the join (the block laid out next).
    let (source, mut machine) = slice6_pair(FlowShape::MinU64);
    let else_copy = join_copy(&machine, 1);
    let else_arm = block_of(&machine, else_copy);
    replace_row(&mut machine, else_copy + 1, X86Opcode::Ret, vec![]);
    machine
        .blocks
        .get_mut(&else_arm)
        .unwrap()
        .successors
        .clear();
    expect_unsupported(&source, &machine, "a return before the path ends");
    // A switch with two edges to one block is slice 14's (one edge whose
    // test is the disjunction of its cases'; see `slice14::`); a `Brif`
    // with both edges to one block stays outside.
    let (mut source, _) = slice6_pair(FlowShape::MinU64);
    for block in source.blocks.values_mut() {
        if let Some(last) = block.instructions.last_mut()
            && let L::Brif {
                then_dest,
                else_dest,
                ..
            } = &mut last.opcode
        {
            *else_dest = *then_dest;
        }
    }
    match admitted_body(&source) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceShape(detail))) => {
            assert!(detail.contains("on both edges"), "{detail}")
        }
        other => panic!("a branch with two edges to one block: {:?}", other.err()),
    }
    // An if-converted diamond (the O1+ `cmov` form of `MinU64`: one block)
    // makes no claim: its arms have no machine blocks.
    let (source, machine) = slice6_pair(FlowShape::MinU64);
    let (_, selected) = slice6_pair(FlowShape::SelectU64);
    let mut converted = selected.clone();
    converted.name = machine.name.clone();
    converted.sig = machine.sig.clone();
    expect_unsupported_or_mismatch(&source, &converted, "if-converted diamond");
    // A back edge into a block that does not dominate its source (an
    // irreducible cycle) stays outside the lane; slice 12 admits a natural
    // loop.
    let looped = super::slice12::irreducible_loop();
    match admitted_body(&looped) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceShape(detail))) => {
            assert!(detail.contains("an irreducible loop"), "{detail}")
        }
        other => panic!("an irreducible loop: {:?}", other.err()),
    }
    assert!(!source_admits_x86_body_owner(&looped, SYSV));
    assert!(source_admits_x86_body_owner(&counting_loop(), SYSV));
}

/// A pair outside the pairing: no theorem, and no credit.
#[track_caller]
fn expect_unsupported_or_mismatch(source: &Function, machine: &X86ISelFunction, what: &str) {
    assert!(
        source_bound_x86_body(source, machine, SYSV).is_err(),
        "{what}: built a body theorem"
    );
}

// ---------------------------------------------------------------------------
// Alternative machine forms and the golden snapshots (no solver)
// ---------------------------------------------------------------------------

/// Alternative correct machine bodies for admitted slice-6 sources, qualified
/// exactly like the selector's own output: the fused compare-and-branch the
/// O1+ peephole leaves, a branch laid out with its `else` edge as the jump
/// and its `then` block as the fallthrough (`jcc` inverted, the `jmp`
/// removed), and a zero test spelled `test r, r`.
pub(crate) fn slice_six_variants() -> Vec<(String, Function, X86ISelFunction)> {
    use trust_cg_ir::X86CondCode as C;
    let mut variants = Vec::new();
    let (source, machine) = fused_min();
    variants.push(("MinU64/fused".into(), source, machine));
    // `jcc e, else` with the `then` block laid out next: the branch-layout
    // form (the fallthrough reaches the `then` arm).
    let (source, mut machine) = slice6_pair(FlowShape::BoolParam);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let (then_block, else_block) = match (
        &inst(&machine, jcc).operands[1],
        &inst(&machine, jcc + 1).operands[0],
    ) {
        (O::Block(then_block), O::Block(else_block)) => (*then_block, *else_block),
        other => panic!("{other:?}"),
    };
    inst_mut(&mut machine, jcc).operands = vec![O::CondCode(C::E), O::Block(else_block)];
    remove_at(&mut machine, jcc + 1);
    let entry = block_of(&machine, jcc);
    // The recorded successors keep the selector's order (`then`, `else`), as
    // the branch-layout pass leaves them: they are a set of edges.
    assert_eq!(
        machine.blocks[&entry].successors,
        vec![then_block, else_block]
    );
    machine.block_order.retain(|block| *block != then_block);
    let position = machine
        .block_order
        .iter()
        .position(|block| *block == entry)
        .unwrap();
    machine.block_order.insert(position + 1, then_block);
    variants.push(("BoolParam/fallthrough".into(), source, machine));
    // The zero test as `test r, r`.
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let cmp = jcc - 1;
    let register = inst(&machine, cmp).operands[0].clone();
    assert_eq!(inst(&machine, cmp).operands[1], O::Imm(0));
    *inst_mut(&mut machine, cmp) =
        X86ISelInst::new(X86Opcode::TestRR, vec![register.clone(), register]);
    variants.push(("EarlyReturn/test".into(), source, machine));
    variants
}

// ---------------------------------------------------------------------------
// Renumbered and reshaped machine CFGs, path-conditioned values, and the
// emitted width of `test r, imm32`
// ---------------------------------------------------------------------------

/// `fn dom(i: u64, n: u64) -> u64 { if i < n { if i < n { i } else { unsafe {
/// core::hint::unreachable_unchecked() } } } else { 0 } }` as the rustc bridge
/// hands it to the backend at `-Copt-level=2 -Zmir-opt-level=0` (the review's
/// repro, read back from `-Ztrust-ir-cg-args=dump-trust-ir`): MIR block ids,
/// the inner `else` a call-then-trap (`abort`), laid out `0, 1, 4, 5, 2, 3`.
/// The inner compare repeats the outer one, so at O1+ the optimizer removes
/// the trap arm, block 5, and renumbers the survivors by layout to `0..5`:
/// LIR blocks 4, 2 and 3 become machine blocks 2, 3 and 4, each id now
/// another LIR block's.
pub(crate) fn dominated_trap() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice6");
    let nothing = builder.add_func_type(vec![], vec![]);
    let abort = builder.declare_function("abort", nothing);
    let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s6_dominated_trap", signature);
    let entry = f.create_block();
    let (outer, inner, trap, other, join) = (
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
        f.create_block(),
    );
    let i = f.add_block_param(entry, Ty::U64);
    let n = f.add_block_param(entry, Ty::U64);
    let result = f.add_block_param(join, Ty::U64);
    f.switch_to_block(entry);
    let less = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(less, outer, vec![], other, vec![]);
    f.switch_to_block(outer);
    let again = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(again, inner, vec![], trap, vec![]);
    f.switch_to_block(inner);
    f.br(join, vec![i]);
    f.switch_to_block(trap);
    f.call_void(abort, vec![]);
    f.unreachable();
    f.switch_to_block(other);
    let zero = f.iconst(Ty::U64, 0);
    f.br(join, vec![zero]);
    f.switch_to_block(join);
    f.ret(vec![result]);
    f.build();
    let mut source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s6_dominated_trap")
    .unwrap();
    // The adapter numbers the blocks in its own order; give them the
    // bridge's MIR ids (entry 0, outer 1, other 2, join 3, inner 4, trap 5).
    let laid_out = source.layout_order();
    assert_eq!(laid_out.len(), 6);
    let bridge: HashMap<Block, Block> = laid_out
        .iter()
        .zip([0, 1, 4, 5, 2, 3].map(Block))
        .map(|(adapter, bridge)| (*adapter, bridge))
        .collect();
    rename_lir_blocks(&mut source, &bridge);
    assert_eq!(
        source.layout_order(),
        [0, 1, 4, 5, 2, 3].map(Block).to_vec()
    );
    source
}

/// Rename every LIR block id with `rename` (blocks, layout, entry, origins
/// and every terminator's targets).
fn rename_lir_blocks(source: &mut Function, rename: &HashMap<Block, Block>) {
    let blocks = std::mem::take(&mut source.blocks);
    for (id, mut body) in blocks {
        for inst in &mut body.instructions {
            match &mut inst.opcode {
                L::Jump { dest } => *dest = rename[dest],
                L::Brif {
                    then_dest,
                    else_dest,
                    ..
                } => {
                    *then_dest = rename[then_dest];
                    *else_dest = rename[else_dest];
                }
                _ => {}
            }
        }
        source.blocks.insert(rename[&id], body);
    }
    for block in &mut source.block_order {
        *block = rename[block];
    }
    source.entry_block = rename[&source.entry_block];
    source.trust_ir_origins = std::mem::take(&mut source.trust_ir_origins)
        .into_iter()
        .map(|(block, origins)| (rename[&block], origins))
        .collect();
}

/// Rename every machine block id with `rename` (the map, `block_order`,
/// successors and every `Block` operand), keeping the rows and their order.
fn rename_blocks(machine: &mut X86ISelFunction, rename: &HashMap<Block, Block>) {
    let blocks = std::mem::take(&mut machine.blocks);
    for (id, mut body) in blocks {
        for successor in &mut body.successors {
            *successor = rename[successor];
        }
        for inst in &mut body.insts {
            for operand in &mut inst.operands {
                if let O::Block(block) = operand {
                    *block = rename[block];
                }
            }
        }
        machine.blocks.insert(rename[&id], body);
    }
    for block in &mut machine.block_order {
        *block = rename[block];
    }
}

/// The machine blocks are paired with the LIR blocks by their rows' TV-1
/// provenance, never by id: every fixture, its blocks renamed the way
/// `renumber_blocks_contiguous` renames them (to their layout position) and
/// the other way round (ids reversed, so each surviving id names another LIR
/// block), builds exactly the theorem of its selector-numbered form.
#[test]
fn renamed_machine_blocks_are_paired_by_provenance() {
    let mut renamed_fixtures = 0;
    for shape in all_slice_six_shapes() {
        let (source, machine) = slice6_pair(shape);
        let expected = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        let expected_query = generate_smt2_query_raw(expected.obligation(), &replay_config());
        let count = machine.block_order.len() as u32;
        let orders: [Box<dyn Fn(usize) -> u32>; 2] = [
            Box::new(|position| position as u32),
            Box::new(move |position| count - 1 - position as u32),
        ];
        for order in orders {
            let rename: HashMap<Block, Block> = machine
                .block_order
                .iter()
                .enumerate()
                .map(|(position, block)| (*block, Block(order(position))))
                .collect();
            if rename.iter().all(|(old, new)| old == new) {
                continue;
            }
            renamed_fixtures += 1;
            let mut renamed = machine.clone();
            rename_blocks(&mut renamed, &rename);
            let owner = source_bound_x86_body(&source, &renamed, SYSV).unwrap_or_else(|refusal| {
                panic!(
                    "{shape:?} renamed {rename:?}: {refusal}\n{}",
                    describe(&renamed)
                )
            });
            assert_eq!(
                generate_smt2_query_raw(owner.obligation(), &replay_config()),
                expected_query,
                "{shape:?} renamed {rename:?}"
            );
            assert_eq!(owner.bound_rows(), expected.bound_rows(), "{shape:?}");
        }
    }
    assert!(renamed_fixtures > 20, "{renamed_fixtures} renamed fixtures");
}

/// The review's repro: [`dominated_trap`] through the real x86 optimizer. At
/// O1+ its trap arm is removed and the survivors renumbered; the owner makes
/// no claim (the LIR trap block has no machine block) and never names the
/// correct, renumbered body a mismatch. At O0 it binds and holds.
#[test]
fn a_renumbered_optimized_body_is_never_a_mismatch() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let source = dominated_trap();
    let selected = select(&source, X86CallAbi::SystemV);
    let owner = source_bound_x86_body(&source, &selected, SYSV)
        .unwrap_or_else(|refusal| panic!("O0: {refusal}\n{}", describe(&selected)));
    // Its trap path (`i < n` and not `i < n`) is infeasible: no sample
    // exercises it, and none refutes the theorem.
    assert!(!paths_refuted_on_samples(owner.obligation()), "O0");
    let mut renumbered = 0;
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
        let mut machine = selected.clone();
        pipeline.run_x86_optimization_passes(&mut machine);
        // Renumbered: fewer blocks than the LIR, with ids `0..n`.
        let ids: Vec<u32> = machine.block_order.iter().map(|block| block.0).collect();
        if machine.block_order.len() < source.blocks.len()
            && ids == (0..ids.len() as u32).collect::<Vec<_>>()
        {
            renumbered += 1;
        }
        match source_bound_x86_body(&source, &machine, SYSV) {
            Ok(owner) => assert!(
                !paths_refuted_on_samples(owner.obligation()),
                "{opt_level:?}\n{}",
                describe(&machine)
            ),
            Err(X86BodyRefusal::Unsupported(refusal)) => {
                eprintln!("{opt_level:?} dominated trap: no claim ({refusal})");
            }
            Err(other) => panic!("{opt_level:?}: {other}\n{}", describe(&machine)),
        }
    }
    assert!(renumbered > 0, "the optimizer did not renumber the repro");
}

/// `fn(x: u64, p: *mut u64) -> u64 { if x == 0 { g1(x); *p = x; x + 7 }
/// else { x } }`.
pub(crate) fn zero_arm_uses_x() -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice6");
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let g1 = builder.declare_function("g1", unary);
    let ptr = Ty::PtrMut(Box::new(Ty::U64));
    let signature = builder.add_func_type(vec![Ty::U64, ptr], vec![Ty::U64]);
    let mut f = builder.function("s6_zero_arm_uses_x", signature);
    let entry = f.create_block();
    let (zero_arm, other) = (f.create_block(), f.create_block());
    let x = f.add_block_param(entry, Ty::U64);
    let p = f.add_block_param(entry, Ty::PtrMut(Box::new(Ty::U64)));
    f.switch_to_block(entry);
    let zero = f.iconst(Ty::U64, 0);
    let test = f.icmp(ICmpOp::Eq, Ty::U64, x, zero);
    f.condbr(test, zero_arm, vec![], other, vec![]);
    f.switch_to_block(zero_arm);
    let _ = f.call(g1, vec![x]);
    f.store(Ty::U64, p, x);
    let seven = f.iconst(Ty::U64, 7);
    let sum = f.add(Ty::U64, x, seven);
    f.ret(vec![sum]);
    f.switch_to_block(other);
    f.ret(vec![x]);
    f.build();
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s6_zero_arm_uses_x")
    .unwrap()
}

/// [`zero_arm_uses_x`]'s real selection with the `x == 0` arm using
/// constants: the call's argument (`arg`), the stored value (`stored`) and
/// the return value (`returned`) each replaced, when given, by a fresh
/// register holding that constant.
fn zero_arm_with_constants(
    arg: Option<i64>,
    stored: Option<i64>,
    returned: Option<i64>,
) -> (Function, X86ISelFunction) {
    let source = zero_arm_uses_x();
    let mut machine = select(&source, X86CallAbi::SystemV);
    let call = nth(&machine, X86Opcode::Call, 0);
    let arm = block_of(&machine, call);
    let in_arm = |machine: &X86ISelFunction, pick: &dyn Fn(&X86ISelInst) -> bool| {
        rows(machine)
            .into_iter()
            .map(|(ordinal, _, _)| ordinal)
            .find(|ordinal| block_of(machine, *ordinal) == arm && pick(inst(machine, *ordinal)))
            .unwrap_or_else(|| panic!("no such row in the zero arm\n{}", describe(machine)))
    };
    let mut fresh = 500;
    let mut use_constant = |machine: &mut X86ISelFunction, row: usize, operand: usize, value| {
        fresh += 1;
        inst_mut(machine, row).operands[operand] = vreg(fresh);
        insert_at(
            machine,
            row,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(fresh), O::Imm(value)]),
        );
    };
    let rdi = |operand: &O| gpr(operand).map(|reg| reg.root) == Some(Root::Physical(7));
    let rax = |operand: &O| gpr(operand).map(|reg| reg.root) == Some(Root::Physical(0));
    if let Some(value) = arg {
        let row = in_arm(&machine, &|inst| {
            inst.opcode == X86Opcode::MovRR && rdi(&inst.operands[0])
        });
        use_constant(&mut machine, row, 1, value);
    }
    if let Some(value) = stored {
        let row = in_arm(&machine, &|inst| inst.opcode == X86Opcode::MovMR);
        use_constant(&mut machine, row, 1, value);
    }
    if let Some(value) = returned {
        let row = in_arm(&machine, &|inst| {
            inst.opcode == X86Opcode::MovRR && rax(&inst.operands[0])
        });
        use_constant(&mut machine, row, 1, value);
    }
    (source, machine)
}

/// On a path of several, a value is observed only where the path condition
/// holds: a correct machine that uses the constant `x` has on the `x == 0`
/// path (as the call argument, the stored value or the returned `x + 7`) is
/// never a named mismatch; the theorem, which states the condition, holds.
/// The same rows with a wrong constant are refuted by the theorem.
#[test]
fn path_conditioned_values_are_judged_by_the_theorem() {
    let (source, machine) = zero_arm_with_constants(None, None, None);
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("selection: {refusal}\n{}", describe(&machine)));
    assert!(theorem_holds(owner.obligation()), "selection");
    for (label, arg, stored, returned) in [
        ("call argument", Some(0), None, None),
        ("stored value", None, Some(0), None),
        ("returned value", None, None, Some(7)),
        ("all three", Some(0), Some(0), Some(7)),
    ] {
        let (source, machine) = zero_arm_with_constants(arg, stored, returned);
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(theorem_holds(owner.obligation()), "{label}");
    }
    for (label, arg, stored, returned) in [
        ("wrong call argument", Some(1), None, None),
        ("wrong stored value", None, Some(1), None),
        ("wrong returned value", None, None, Some(8)),
    ] {
        let (source, machine) = zero_arm_with_constants(arg, stored, returned);
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(paths_refuted_on_samples(owner.obligation()), "{label}");
    }
}

/// `bt r, imm8` is admitted as a CF-ONLY flag writer, and only a condition
/// that reads CF may consume it.
///
/// `trust_cg_ir` groups `BtRI` with the compares — a flag-only side effect
/// that produces no value — and the peephole emits `[reg, imm]` with operand 0
/// a pure use, so the row's SHAPE is a compare's. What differs is which flags
/// it defines: Intel SDM Vol 2A, BT sets `CF := bit(r, k)` and leaves OF, SF,
/// ZF, AF and PF ARCHITECTURALLY UNDEFINED. The partial model
/// ([`AluFlags::carry_only`]) is what makes that fail closed.
///
/// WHAT THIS TEST DOES NOT EXHIBIT: a body in which `bt` + `jb` genuinely
/// implements its source, and which therefore HOLDS. The slice-6 fixtures
/// branch on a zero test, so every `bt` body reachable by rewriting one is a
/// mismatched rewrite by construction. So the cases below are: the row is
/// admitted, the theorem it builds is FALSE for a rewrite that changed the
/// predicate (the non-vacuity control), a ZF reader refuses rather than
/// reading a flag `bt` never defined, and an out-of-range bit index is refused
/// at the row shape instead of being modelled.
#[test]
fn a_bit_test_defines_only_the_carry_flag() {
    use trust_cg_ir::X86CondCode;

    // A CF reader: `bt reg, 3` then `jb`. The source compare's own `Jcc` is
    // retargeted to a CF condition, because the flags `bt` leaves are not the
    // ones the fixture's branch was reading.
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let cmp = jcc - 1;
    assert_eq!(inst(&machine, cmp).opcode, X86Opcode::CmpRI);
    let register = inst(&machine, cmp).operands[0].clone();
    *inst_mut(&mut machine, cmp) =
        X86ISelInst::new(X86Opcode::BtRI, vec![register.clone(), O::Imm(3)]);
    let targets = inst(&machine, jcc).operands[1..].to_vec();
    let mut jb = vec![O::CondCode(X86CondCode::B)];
    jb.extend(targets.clone());
    *inst_mut(&mut machine, jcc) = X86ISelInst::new(X86Opcode::Jcc, jb);
    // Two claims, and NEITHER is that this body is correct. This machine
    // branches on bit 3 of the register while the source still branches on
    // the register being zero, so it is a DELIBERATELY mismatched rewrite.
    //  (1) the `bt` row is ADMITTED: the body is built rather than refused for
    //      the row, which is the capability this change adds;
    //  (2) the theorem it builds is FALSE, which is the non-vacuity control —
    //      a model that said nothing about `bt` would let this rewrite hold.
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("the bt row must not refuse: {refusal}"));
    assert!(
        !theorem_holds(owner.obligation()),
        "a machine branching on bit 3 where the source branches on zero must NOT hold: \
         the CF model would be saying nothing"
    );

    // A ZF reader after a `bt`: `bt` never defines ZF, so the jump reads a
    // flag its writer leaves undefined. This is the fail-closed half.
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let cmp = jcc - 1;
    let register = inst(&machine, cmp).operands[0].clone();
    *inst_mut(&mut machine, cmp) = X86ISelInst::new(X86Opcode::BtRI, vec![register, O::Imm(3)]);
    let reads_zf = matches!(
        inst(&machine, jcc).operands.first(),
        Some(O::CondCode(X86CondCode::E | X86CondCode::NE))
    );
    assert!(reads_zf, "the fixture's branch must read ZF for this case");
    expect_mismatch(
        &source,
        &machine,
        "a jump on ZF after a bit test",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand.contains("rflags")),
    );

    // An out-of-range bit index is refused at the row shape: the model's own
    // precondition is `k < width`, and a body that carries one makes no claim
    // rather than being modelled at a wrong width.
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let cmp = jcc - 1;
    let register = inst(&machine, cmp).operands[0].clone();
    *inst_mut(&mut machine, cmp) = X86ISelInst::new(X86Opcode::BtRI, vec![register, O::Imm(64)]);
    expect_unsupported(&source, &machine, "a bit test whose index is out of range");
}

/// The encoder emits `test r/m64, imm32` (REX.W) whatever the operand's
/// register class, so a `TestRI` is modelled only on a 64-bit register: the
/// 64-bit form of a zero test holds, and a 32-bit one makes no claim (its
/// 32-bit model would not be the emitted instruction).
#[test]
fn a_test_with_an_immediate_is_admitted_only_at_the_emitted_width() {
    let (source, mut machine) = slice6_pair(FlowShape::EarlyReturn);
    let jcc = nth(&machine, X86Opcode::Jcc, 0);
    let cmp = jcc - 1;
    assert_eq!(inst(&machine, cmp).opcode, X86Opcode::CmpRI);
    assert_eq!(inst(&machine, cmp).operands[1], O::Imm(0));
    let register = inst(&machine, cmp).operands[0].clone();
    *inst_mut(&mut machine, cmp) = X86ISelInst::new(X86Opcode::TestRI, vec![register, O::Imm(-1)]);
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("64-bit test: {refusal}"));
    assert!(theorem_holds(owner.obligation()), "64-bit test");
    let (source, mut machine) = slice6_pair(FlowShape::MaxI32);
    let cmp = nth(&machine, X86Opcode::CmpRR, 0);
    let lhs = inst(&machine, cmp).operands[0].clone();
    assert!(matches!(&lhs, O::VReg(vreg) if vreg.class == RegClass::Gpr32));
    *inst_mut(&mut machine, cmp) = X86ISelInst::new(X86Opcode::TestRI, vec![lhs, O::Imm(-1)]);
    expect_unsupported(&source, &machine, "a 32-bit test with an immediate");
}

/// The real x86 optimizer's output at O1, O2 and O3 (branch layout, block
/// merging, `cmov` if-conversion, peepholes) for every slice-6 fixture: the
/// owner never names a mismatch for a correct lowering, and every theorem it
/// builds holds. (An optimized body it cannot pair makes no claim.)
#[test]
fn optimized_slice_six_fixtures_are_judged_without_false_mismatches() {
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
        for shape in all_slice_six_shapes() {
            let (source, mut machine) = slice6_pair(shape);
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
    // The optimizer leaves some shapes pairable (the fused `cmp; jcc` and the
    // inverted fallthrough forms): the test judges real theorems.
    assert!(built > 0, "no optimized fixture built a theorem");
}

#[test]
fn slice_six_variants_hold_on_samples() {
    for (label, source, machine) in slice_six_variants() {
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(theorem_holds(owner.obligation()), "{label}");
    }
}

const SLICE_SIX_SNAPSHOT_SHA256: &str =
    "d96b1d589ede3069ed9eb4a9bd48ac8147a0c78b2f869cd9c611a60d03940b88";

#[test]
fn slice_six_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice6_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_SIX {
        let (source, machine) = slice6_pair(shape);
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
            .join("tests/fixtures/x86_source_bound_body/slice6_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_SIX_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_SIX_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-6 snapshots drifted");
}

/// The theorem states every source path, and each path's claim reads only
/// what that path computes: a claim of the `k`-th path names no definition
/// that only another path makes. (A definition two paths share, their common
/// prefix, is stated once.)
#[test]
fn each_path_claim_is_stated_once_and_shares_its_prefix() {
    let (source, machine) = slice6_pair(FlowShape::TwoDiamonds);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let claims = path_claims(owner.obligation());
    assert_eq!(claims.len(), 4);
    // The entry block's compare is one definition, read by every path.
    let names = |expr: &E| expr.free_vars().into_iter().collect::<HashSet<_>>();
    let shared: HashSet<String> = claims
        .iter()
        .map(|(condition, _)| names(condition))
        .reduce(|a, b| a.intersection(&b).cloned().collect())
        .unwrap();
    assert!(
        !shared.is_empty(),
        "the paths share their first branch's value"
    );
    // Two paths through different arms of the first diamond define the join
    // value differently.
    assert_ne!(names(&claims[0].1), names(&claims[2].1));
}
