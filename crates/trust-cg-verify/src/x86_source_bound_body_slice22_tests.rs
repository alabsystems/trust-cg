// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 22 of the x86-64 source-bound body theorem: the `i128` division
//! class. An `I128` division is the call of its runtime routine and the
//! `I128` divide-by-zero guard is slice 14's guard at 128 bits (OD-202); a
//! 128-bit product is spelled by its 64-bit limbs (OD-203). The 128-bit
//! checked multiply, a division by its operand when slice 22 landed, is the
//! division-free limb check since OD-224 (two `I64` `CheckedUmul`s, no call);
//! its shapes stay here, and the goldens rendered before OD-224 are rendered
//! again in the division form for their custody
//! (`trust_cg_lower::with_x86_i128_mulo_division_form`).
//!
//! Fixtures are real: LIR from the trust-ir adapter (translated with an
//! explicit `Permit`), the machine stream from the real x86-64 instruction
//! selector (`super::select`). Every test here runs without a solver (the
//! `x86_source_bound_body::tests::slice22::` library gate); the replay on AY
//! and Clean is in `slice22_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::slice16::{cut_at, every_block, parts_hold, some_part_refuted};
use super::*;
use normal::Groups;
use trust_ir::{ICmpOp, OverflowOp, ProofAnnotation};

/// Slice-22 fixture shapes: each a source one of the slice's rules admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape22 {
    /// `fn(a: u128, b: u128) -> u128 { if b == 0 { trap } a / b }`: rustc's
    /// zero check, then `__udivti3`.
    U128Div,
    /// `fn(a: u128, b: u128) -> u128 { if b == 0 { trap } a % b }`.
    U128Rem,
    /// `fn(a: i128, b: i128) -> i128 { if b == 0 { trap } if a == MIN { if b
    /// == -1 { trap } } a / b }`: both of rustc's checks, then `__divti3`.
    I128Div,
    /// `fn(a: i128, b: i128) -> i128 { if b == 0 { trap } a % b }`.
    I128Rem,
    /// `<u64 as FullOps>::full_div_rem`'s shape: `fn(a: u128, b: u128) ->
    /// u128 { if b == 0 { trap } (a / b) ^ (a % b) }`, two calls.
    U128DivRem,
    /// `fn(n: u128) -> u128 { n / 10^16 }` (`div_rem_1e16`'s divisor: its
    /// halves moved as constants).
    U128DivConst,
    /// `fn(a: u64, b: u64) -> bool { (a as u128).checked_mul(b as u128)
    /// .is_none() }`: the adapter's 128-bit overflow check, the
    /// division-free limb check since OD-224 (`build_u128_mul_overflow_divfree`;
    /// a division of the product by `a == 0 ? 1 : a` before).
    U128CheckedMulSmall,
    /// `fn(a: u128) -> u128 { a / (2^64 + 3) }` annotated `DivNonZero`: the
    /// guard of a nonzero constant with a high half (no stop).
    I128GuardConst,
    /// `fn(a: u128, b: u128) -> u128 { a / b }` annotated `DivNonZero`: the
    /// guard of a variable, `or d, lo, hi; TrapDivZeroExact d`.
    I128GuardVar,
    /// `fn(a: i128, b: i128) -> i128 { a / b }`, no check: `MIN / -1` and a
    /// zero divisor reach the call. The call model claims nothing about the
    /// routine's result, so the theorem holds; only the contract's link to
    /// the LIR's meaning is scoped to trust-ir's defined domain.
    I128SdivMinNegOne,
    // ---- OD-203: the 128-bit product by its limbs (each with 22a's call)
    /// `fn(a: u128, b: u128) -> bool { a.checked_mul(b).is_none() }`: the
    /// product of two full operands and its overflow check.
    U128CheckedMul,
    /// `fn(a: i128, b: i128, out: *mut i128) -> bool { let (p, o) =
    /// a.overflowing_mul(b); *out = p; o }`: the signed check (the limb check
    /// on the magnitudes since OD-224; `__divti3` with `MIN / -1` avoided
    /// before), the product stored, as `i128::overflowing_mul` returns its
    /// pair through memory.
    I128OverflowingMul,
    /// `fn(n: u128, q: u128) -> u128 { n - q * 10^16 }` (`div_rem_1e16`'s
    /// remainder: a product by a constant below `2^64`, then a 128-bit
    /// difference, so the theorem keeps a claim once the product's spells
    /// alike).
    U128MulConst,
    /// `fn(a: u128, b: u128, out: *mut u128) -> bool { let (p, o) =
    /// a.overflowing_mul(b); tick(); *out = p; o }`: the product and its
    /// check live across a block boundary (`from_ascii_radix`'s shape),
    /// stated in parts at every block too.
    U128MulAcrossCut,
    /// `fn(a: u128, b: u64) -> bool { a.checked_mul(b as u128).is_none() }`:
    /// one operand a zero extension (still a full product: `limb` rewrites
    /// it), as `from_ascii_radix` multiplies by its radix.
    U128MulZextOperand,
    /// `<u64 as CarryingMulAdd>::carrying_mul_add`'s value: `fn(a: u64, b:
    /// u64, c: u64, d: u64) -> u128 { (a as u128) * (b as u128) + (c as u128)
    /// + (d as u128) }`, a widening product: OD-203 leaves its theorem as it
    /// was (the guard of the scoped `acmul`).
    U64CarryingMulAdd,
    /// `fn(a: u128, b: u128) -> u128 { let mut x = 7u64; sink(&mut x); a / b
    /// }` with the division in a block of its own: the local escaped to
    /// `sink`, and the division's call reads it (slice 7), so its bytes are
    /// live at the cut before the division (slice 17's liveness), stated in
    /// parts at every block.
    EscapedSlotAcrossDivision,
}

/// Every slice-22 fixture shape.
pub(crate) const SLICE_TWENTY_TWO: [Shape22; 17] = [
    Shape22::U128Div,
    Shape22::U128Rem,
    Shape22::I128Div,
    Shape22::I128Rem,
    Shape22::U128DivRem,
    Shape22::U128DivConst,
    Shape22::U128CheckedMulSmall,
    Shape22::I128GuardConst,
    Shape22::I128GuardVar,
    Shape22::I128SdivMinNegOne,
    Shape22::U128CheckedMul,
    Shape22::I128OverflowingMul,
    Shape22::U128MulConst,
    Shape22::U128MulAcrossCut,
    Shape22::U128MulZextOperand,
    Shape22::U64CarryingMulAdd,
    Shape22::EscapedSlotAcrossDivision,
];

/// The shapes stated in parts by a test policy that cuts at every block
/// (slice 16's [`cut_at`]): values live across a cut point.
pub(crate) fn cut_everywhere(shape: Shape22) -> bool {
    matches!(
        shape,
        Shape22::U128MulAcrossCut | Shape22::EscapedSlotAcrossDivision
    )
}

impl Shape22 {
    pub(crate) fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s22_");
        let mut previous_lower = false;
        for c in name.chars() {
            if c.is_ascii_uppercase() && previous_lower {
                snake.push('_');
            }
            previous_lower = c.is_ascii_lowercase() || c.is_ascii_digit();
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }

    /// The symbol of each call the selector emits for the shape, in order.
    /// The checked multiplies call nothing since OD-224.
    pub(crate) fn calls(self) -> &'static [&'static str] {
        use Shape22::*;
        match self {
            U128Div | U128DivConst | I128GuardConst | I128GuardVar => &["__udivti3"],
            U128Rem => &["__umodti3"],
            I128Div | I128SdivMinNegOne => &["__divti3"],
            I128Rem => &["__modti3"],
            U128DivRem => &["__udivti3", "__umodti3"],
            U128MulAcrossCut => &["tick"],
            EscapedSlotAcrossDivision => &["sink", "__udivti3"],
            U128CheckedMulSmall | U128CheckedMul | I128OverflowingMul | U128MulZextOperand
            | U128MulConst | U64CarryingMulAdd => &[],
        }
    }

    /// The symbol of each call the selector emitted for the shape before
    /// OD-224 (the checked multiplies in the division form,
    /// `trust_cg_lower::with_x86_i128_mulo_division_form`).
    pub(crate) fn calls_in_the_division_form(self) -> &'static [&'static str] {
        use Shape22::*;
        match self {
            U128CheckedMulSmall | U128CheckedMul | U128MulZextOperand => &["__udivti3"],
            I128OverflowingMul => &["__divti3"],
            U128MulAcrossCut => &["__udivti3", "tick"],
            other => other.calls(),
        }
    }

    /// Whether the shape holds a 128-bit checked multiply (whose expansion
    /// OD-224 changed on x86-64).
    pub(crate) fn checks_a_multiply(self) -> bool {
        use Shape22::*;
        matches!(
            self,
            U128CheckedMulSmall
                | U128CheckedMul
                | I128OverflowingMul
                | U128MulAcrossCut
                | U128MulZextOperand
        )
    }

    /// The number of `I128` divisions of the shape (each a routine's call).
    pub(crate) fn divisions(self) -> usize {
        self.calls()
            .iter()
            .filter(|symbol| symbol.ends_with("ti3"))
            .count()
    }
}

type Builder<'a> = trust_ir_build::FunctionBuilder<'a>;
type V = trust_ir::value::ValueId;

/// `if test == 0 { trap }` from the current block, which continues in a new
/// block.
fn trap_if_zero(f: &mut Builder<'_>, ty: Ty, test: V) {
    let (trap, go) = (f.create_block(), f.create_block());
    let zero = f.iconst(ty.clone(), 0);
    let is_zero = f.icmp(ICmpOp::Eq, ty, test, zero);
    f.condbr(is_zero, trap, vec![], go, vec![]);
    f.switch_to_block(trap);
    f.unreachable();
    f.switch_to_block(go);
}

/// `10^16`, `div_rem_1e16`'s divisor.
const TEN_TO_THE_16: i128 = 10_000_000_000_000_000;

/// The trust-ir module of a slice-22 fixture: the fixture function, and the
/// declarations of `sink` and `tick`.
fn slice22_module(shape: Shape22) -> trust_ir::Module {
    use Shape22::*;
    let name = shape.name();
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice22");
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        U128Div | U128Rem | U128DivRem | I128GuardVar => (vec![Ty::U128, Ty::U128], vec![Ty::U128]),
        I128Div | I128Rem | I128SdivMinNegOne => (vec![Ty::I128, Ty::I128], vec![Ty::I128]),
        U128DivConst | I128GuardConst => (vec![Ty::U128], vec![Ty::U128]),
        U128CheckedMulSmall => (vec![Ty::U64, Ty::U64], vec![Ty::Bool]),
        U128CheckedMul => (vec![Ty::U128, Ty::U128], vec![Ty::Bool]),
        U128MulAcrossCut => (
            vec![Ty::U128, Ty::U128, Ty::PtrMut(Box::new(Ty::U128))],
            vec![Ty::Bool],
        ),
        I128OverflowingMul => (
            vec![Ty::I128, Ty::I128, Ty::PtrMut(Box::new(Ty::I128))],
            vec![Ty::Bool],
        ),
        U128MulConst => (vec![Ty::U128, Ty::U128], vec![Ty::U128]),
        U128MulZextOperand => (vec![Ty::U128, Ty::U64], vec![Ty::Bool]),
        U64CarryingMulAdd => (vec![Ty::U64; 4], vec![Ty::U128]),
        EscapedSlotAcrossDivision => (vec![Ty::U128, Ty::U128], vec![Ty::U128]),
    };
    let sink = {
        let ty = builder.add_func_type(vec![Ty::PtrMut(Box::new(Ty::U64))], vec![]);
        builder.declare_function("sink", ty)
    };
    let tick = {
        let ty = builder.add_func_type(vec![], vec![]);
        builder.declare_function("tick", ty)
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        U128Div | U128Rem | I128Rem => {
            let (ty, op) = match shape {
                U128Div => (Ty::U128, BinOp::UDiv),
                U128Rem => (Ty::U128, BinOp::URem),
                _ => (Ty::I128, BinOp::SRem),
            };
            trap_if_zero(&mut f, ty.clone(), args[1]);
            let q = f.binop(op, ty, args[0], args[1]);
            f.ret(vec![q]);
        }
        I128Div => {
            trap_if_zero(&mut f, Ty::I128, args[1]);
            let (check, trap, go) = (f.create_block(), f.create_block(), f.create_block());
            let min = f.iconst(Ty::I128, i128::MIN);
            let is_min = f.icmp(ICmpOp::Eq, Ty::I128, args[0], min);
            f.condbr(is_min, check, vec![], go, vec![]);
            f.switch_to_block(check);
            let minus_one = f.iconst(Ty::I128, -1);
            let is_minus_one = f.icmp(ICmpOp::Eq, Ty::I128, args[1], minus_one);
            f.condbr(is_minus_one, trap, vec![], go, vec![]);
            f.switch_to_block(trap);
            f.unreachable();
            f.switch_to_block(go);
            let q = f.binop(BinOp::SDiv, Ty::I128, args[0], args[1]);
            f.ret(vec![q]);
        }
        U128DivRem => {
            trap_if_zero(&mut f, Ty::U128, args[1]);
            let q = f.binop(BinOp::UDiv, Ty::U128, args[0], args[1]);
            let r = f.binop(BinOp::URem, Ty::U128, args[0], args[1]);
            let both = f.binop(BinOp::Xor, Ty::U128, q, r);
            f.ret(vec![both]);
        }
        U128DivConst => {
            let divisor = f.iconst(Ty::U128, TEN_TO_THE_16);
            let q = f.binop(BinOp::UDiv, Ty::U128, args[0], divisor);
            f.ret(vec![q]);
        }
        U128CheckedMulSmall => {
            let a = f.zext(Ty::U64, Ty::U128, args[0]);
            let b = f.zext(Ty::U64, Ty::U128, args[1]);
            let (_, overflow) = f.overflow(OverflowOp::MulOverflow, Ty::U128, a, b);
            f.ret(vec![overflow]);
        }
        I128GuardConst => {
            let divisor = f.iconst(Ty::U128, (1i128 << 64) + 3);
            let q = f.binop_proven(
                BinOp::UDiv,
                Ty::U128,
                args[0],
                divisor,
                vec![ProofAnnotation::DivNonZero],
            );
            f.ret(vec![q]);
        }
        I128GuardVar => {
            let q = f.binop_proven(
                BinOp::UDiv,
                Ty::U128,
                args[0],
                args[1],
                vec![ProofAnnotation::DivNonZero],
            );
            f.ret(vec![q]);
        }
        I128SdivMinNegOne => {
            let q = f.binop(BinOp::SDiv, Ty::I128, args[0], args[1]);
            f.ret(vec![q]);
        }
        U128CheckedMul => {
            let (_, overflow) = f.overflow(OverflowOp::MulOverflow, Ty::U128, args[0], args[1]);
            f.ret(vec![overflow]);
        }
        I128OverflowingMul => {
            let (product, overflow) =
                f.overflow(OverflowOp::MulOverflow, Ty::I128, args[0], args[1]);
            f.store(Ty::I128, args[2], product);
            f.ret(vec![overflow]);
        }
        U128MulConst => {
            let ten = f.iconst(Ty::U128, TEN_TO_THE_16);
            let p = f.mul(Ty::U128, args[1], ten);
            let r = f.sub(Ty::U128, args[0], p);
            f.ret(vec![r]);
        }
        U128MulAcrossCut => {
            let (product, overflow) =
                f.overflow(OverflowOp::MulOverflow, Ty::U128, args[0], args[1]);
            let after = f.create_block();
            f.br(after, vec![]);
            f.switch_to_block(after);
            f.call_void(tick, vec![]);
            f.store(Ty::U128, args[2], product);
            f.ret(vec![overflow]);
        }
        U128MulZextOperand => {
            let b = f.zext(Ty::U64, Ty::U128, args[1]);
            let (_, overflow) = f.overflow(OverflowOp::MulOverflow, Ty::U128, args[0], b);
            f.ret(vec![overflow]);
        }
        U64CarryingMulAdd => {
            let wide: Vec<V> = args
                .iter()
                .map(|arg| f.zext(Ty::U64, Ty::U128, *arg))
                .collect();
            let p = f.mul(Ty::U128, wide[0], wide[1]);
            let s = f.add(Ty::U128, p, wide[2]);
            let t = f.add(Ty::U128, s, wide[3]);
            f.ret(vec![t]);
        }
        EscapedSlotAcrossDivision => {
            let x = f.alloca(Ty::U64);
            let seven = f.iconst(Ty::U64, 7);
            f.store(Ty::U64, x, seven);
            f.call_void(sink, vec![x]);
            let divide = f.create_block();
            f.br(divide, vec![]);
            f.switch_to_block(divide);
            let q = f.binop(BinOp::UDiv, Ty::U128, args[0], args[1]);
            f.ret(vec![q]);
        }
    }
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The LIR the trust-ir adapter translates `module`'s function `name` to.
fn translated(module: &trust_ir::Module, name: &str) -> Function {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"))
}

fn slice22_function(shape: Shape22) -> Function {
    translated(&slice22_module(shape), &shape.name())
}

pub(crate) fn slice22_lir(shape: Shape22) -> Function {
    slice22_function(shape)
}

pub(crate) fn slice22_pair(shape: Shape22) -> (Function, X86ISelFunction) {
    let source = slice22_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// The owner of a slice-22 pair: in parts at every block for the
/// [`cut_everywhere`] shapes, else the production owner.
pub(crate) fn slice22_owner<'a>(
    shape: Shape22,
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    if cut_everywhere(shape) {
        let owner =
            source_bound_x86_body_in_parts(source, machine, SYSV, &cut_at(every_block(source)))?;
        check_trusted_routines(&owner, Some(&fixture_module(source)))?;
        Ok(owner)
    } else {
        fixture_owner(source, machine)
    }
}

/// The definitions of a slice-22 fixture's module (OD-210): it defines the
/// fixture function alone (`sink` and `tick` are declarations), so no
/// runtime routine ([`the_fixture_modules_define_no_routine`]).
pub(crate) fn fixture_module(source: &Function) -> X86ModuleDefinitions {
    X86ModuleDefinitions::of_symbols([source.name.as_str()])
}

/// The production owner of a fixture pair in its own module (OD-210).
pub(crate) fn fixture_owner<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    source_bound_x86_body_in_module(source, machine, SYSV, Some(&fixture_module(source)))
}

#[track_caller]
pub(crate) fn owner<'a>(
    what: &str,
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> SourceBoundX86Body<'a> {
    fixture_owner(source, machine).unwrap_or_else(|refusal| {
        panic!(
            "{what}: {refusal}\n{}{}",
            describe_lir(source),
            describe(machine)
        )
    })
}

/// The theorem's query as the replay renders it.
fn text(obligation: &ProofObligation) -> String {
    generate_smt2_query_raw(obligation, &replay_config())
}

/// Whether an owner's theorem (every part, for one stated in parts) holds on
/// slice 9's keyed samples.
fn owner_holds(owner: &SourceBoundX86Body<'_>) -> Result<(), String> {
    if owner.is_stated_in_parts() {
        parts_hold(owner)
    } else if dag_holds_on_samples(owner.obligation()) {
        Ok(())
    } else {
        Err("the theorem is refuted on samples".into())
    }
}

/// The walk ordinal of every `call` row, in walk order, with its symbol.
fn call_rows(machine: &X86ISelFunction) -> Vec<(usize, String)> {
    find(machine, X86Opcode::Call)
        .into_iter()
        .map(|ordinal| {
            let symbol = match inst(machine, ordinal).operands.first() {
                Some(O::Symbol(symbol)) => symbol.clone(),
                other => panic!("call row {ordinal}: {other:?}"),
            };
            (ordinal, symbol)
        })
        .collect()
}

/// Every slice-22 shape builds a theorem that holds on samples; the
/// selector calls exactly the shape's routines, and the theorem states no
/// division (each is a call of the world, [`every_i128_division_is_a_call_site`]).
#[test]
fn owner_builds_every_slice_twenty_two_shape() {
    for shape in SLICE_TWENTY_TWO {
        let (source, machine) = slice22_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        owner_holds(&owner).unwrap_or_else(|why| {
            panic!(
                "{shape:?}: {why}\n{}{}{}",
                describe_lir(&source),
                describe(&machine),
                text(owner.obligation())
            )
        });
        let symbols: Vec<String> = call_rows(&machine)
            .into_iter()
            .map(|(_, symbol)| symbol)
            .collect();
        assert_eq!(symbols, shape.calls(), "{shape:?}");
        let query = text(owner.obligation());
        for division in ["bvudiv", "bvsdiv", "bvurem", "bvsrem"] {
            assert!(
                !query.contains(&format!("({division} ")),
                "{shape:?}: the theorem states a division\n{query}"
            );
        }
        eprintln!("SLICE22_SHAPE {shape:?}: stated, {} bytes", query.len());
        if cut_everywhere(shape) {
            let parts = slice22_owner(shape, &source, &machine)
                .unwrap_or_else(|refusal| panic!("{shape:?} (cut): {refusal}"));
            parts_hold(&parts).unwrap_or_else(|why| panic!("{shape:?} (cut): {why}"));
        }
    }
}

/// The slice-22 theorems are a function of the pair: built twice, they are
/// the same text.
#[test]
fn slice_twenty_two_theorems_are_deterministic() {
    for shape in SLICE_TWENTY_TWO {
        let (source, machine) = slice22_pair(shape);
        let first = text(owner("first", &source, &machine).obligation());
        let (source, machine) = slice22_pair(shape);
        let second = text(owner("second", &source, &machine).obligation());
        assert_eq!(first, second, "{shape:?}");
    }
}

/// The `I128` guard: a variable divisor's guard is a stop at the carrier
/// `or d, lo, hi; TrapDivZeroExact d`, and a nonzero constant's (one with a
/// high half, which `constants` does not hold) is none.
#[test]
fn the_i128_guard_is_slice_fourteens_guard_at_128_bits() {
    let (source, machine) = slice22_pair(Shape22::I128GuardVar);
    let owner_var = owner("I128GuardVar", &source, &machine);
    let trap = find(&machine, X86Opcode::TrapDivZeroExact);
    assert_eq!(trap.len(), 1, "{}", describe(&machine));
    let or = inst(&machine, trap[0] - 1);
    assert_eq!(or.opcode, X86Opcode::OrRR, "{}", describe(&machine));
    let guard_stops = |owner: &SourceBoundX86Body<'_>, source: &Function| {
        owner
            .source_definitions()
            .iter()
            .filter(|(_, block, index)| {
                source
                    .blocks
                    .get(block)
                    .and_then(|body| body.instructions.get(*index))
                    .is_some_and(|inst| matches!(inst.opcode, L::GuardDivZero { .. }))
            })
            .count()
    };
    assert_eq!(
        guard_stops(&owner_var, &source),
        1,
        "a variable I128 divisor's guard is a stop\n{}",
        text(owner_var.obligation())
    );
    let (source, machine) = slice22_pair(Shape22::I128GuardConst);
    let owner_const = owner("I128GuardConst", &source, &machine);
    assert_eq!(
        guard_stops(&owner_const, &source),
        0,
        "a nonzero I128 constant's guard never fires\n{}",
        text(owner_const.obligation())
    );
}

/// Each `I128` division is a call site of the theorem: the k-th call of the
/// world, paired with the k-th machine `call`.
#[test]
fn every_i128_division_is_a_call_site() {
    for shape in SLICE_TWENTY_TWO {
        let (source, machine) = slice22_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        let divisions: Vec<(Block, usize)> = owner
            .call_sites()
            .iter()
            .filter(|(block, index, _)| {
                matches!(
                    source.blocks[block].instructions[*index].opcode,
                    L::Udiv | L::Sdiv | L::Urem | L::Srem
                )
            })
            .map(|(block, index, _)| (*block, *index))
            .collect();
        assert_eq!(divisions.len(), shape.divisions(), "{shape:?}");
    }
}

/// Wrong lowerings of the slice's fixtures, each as one edit of the
/// selector's real stream: the theorem builds and is refuted.
pub(crate) fn slice_twenty_two_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // The four argument moves before the first call: RDI, RSI, RDX, RCX.
    let argument_rows = |machine: &X86ISelFunction| -> [usize; 4] {
        let call = call_rows(machine)[0].0;
        [call - 4, call - 3, call - 2, call - 1]
    };
    let source_of =
        |machine: &X86ISelFunction, ordinal: usize| inst(machine, ordinal).operands[1].clone();
    // Swapped dividend halves: `mov rdi, a_hi; mov rsi, a_lo`.
    {
        let (source, mut machine) = slice22_pair(Shape22::U128Div);
        let [rdi, rsi, ..] = argument_rows(&machine);
        let (lo, hi) = (source_of(&machine, rdi), source_of(&machine, rsi));
        inst_mut(&mut machine, rdi).operands[1] = hi;
        inst_mut(&mut machine, rsi).operands[1] = lo;
        cases.push(("udiv/dividend-halves-swapped", source, machine));
    }
    // The divisor and the dividend swapped.
    {
        let (source, mut machine) = slice22_pair(Shape22::U128Rem);
        let [rdi, rsi, rdx, rcx] = argument_rows(&machine);
        let (a_lo, a_hi, b_lo, b_hi) = (
            source_of(&machine, rdi),
            source_of(&machine, rsi),
            source_of(&machine, rdx),
            source_of(&machine, rcx),
        );
        inst_mut(&mut machine, rdi).operands[1] = b_lo;
        inst_mut(&mut machine, rsi).operands[1] = b_hi;
        inst_mut(&mut machine, rdx).operands[1] = a_lo;
        inst_mut(&mut machine, rcx).operands[1] = a_hi;
        cases.push(("urem/operands-swapped", source, machine));
    }
    // The result's halves swapped: `mov lo, rdx; mov hi, rax`.
    {
        let (source, mut machine) = slice22_pair(Shape22::I128Rem);
        let call = call_rows(&machine)[0].0;
        let (rax, rdx) = (
            inst(&machine, call + 1).operands[1].clone(),
            inst(&machine, call + 2).operands[1].clone(),
        );
        inst_mut(&mut machine, call + 1).operands[1] = rdx;
        inst_mut(&mut machine, call + 2).operands[1] = rax;
        cases.push(("srem/result-halves-swapped", source, machine));
    }
    // The high half stale: the result's high half is the dividend's.
    {
        let (source, mut machine) = slice22_pair(Shape22::I128Div);
        let rsi = argument_rows(&machine)[1];
        let call = call_rows(&machine)[0].0;
        let a_hi = source_of(&machine, rsi);
        inst_mut(&mut machine, call + 2).operands[1] = a_hi;
        cases.push(("sdiv/high-half-stale", source, machine));
    }
    // The second call of `full_div_rem` passed the first call's dividend
    // low half in its divisor's place.
    {
        let (source, mut machine) = slice22_pair(Shape22::U128DivRem);
        let second = call_rows(&machine)[1].0;
        let first_rdi = argument_rows(&machine)[0];
        let a_lo = source_of(&machine, first_rdi);
        inst_mut(&mut machine, second - 2).operands[1] = a_lo;
        cases.push(("divrem/second-divisor-wrong", source, machine));
    }
    // The constant divisor's high half moved into its low half's place.
    {
        let (source, mut machine) = slice22_pair(Shape22::U128DivConst);
        let [_, _, rdx, rcx] = argument_rows(&machine);
        let b_hi = source_of(&machine, rcx);
        inst_mut(&mut machine, rdx).operands[1] = b_hi;
        cases.push(("udiv-const/divisor-low-is-high", source, machine));
    }
    // The guard's `or` of the low half with itself: at `2^64` the machine
    // traps where the source does not.
    {
        let (source, mut machine) = slice22_pair(Shape22::I128GuardVar);
        let trap = find(&machine, X86Opcode::TrapDivZeroExact)[0];
        let low = inst(&machine, trap - 1).operands[1].clone();
        inst_mut(&mut machine, trap - 1).operands[2] = low;
        cases.push(("guard128/or-low-with-itself", source, machine));
    }
    cases
}

/// Every slice-22 wrong lowering's theorem builds and is refuted on samples,
/// and the production verifier never credits it.
#[test]
fn every_slice_twenty_two_refutation_is_refuted() {
    for (label, source, machine) in slice_twenty_two_refutations() {
        let owner = fixture_owner(&source, &machine).unwrap_or_else(|refusal| {
            panic!(
                "{label}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        let refuted = if owner.is_stated_in_parts() {
            some_part_refuted(&owner)
        } else {
            dag_refuted_on_samples(owner.obligation())
                || (0..super::slice10::EDGE_SAMPLES)
                    .any(|seed| !super::slice10::holds_at_edge(owner.obligation(), seed))
        };
        assert!(
            refuted,
            "{label}: a wrong lowering's theorem holds on samples\n{}{}",
            describe(&machine),
            text(owner.obligation())
        );
        let outcome = super::slice12::never_credited(&source, &machine, label);
        assert_ne!(outcome, "credited", "{label}");
    }
}

/// The routine each opcode calls is checked, not trusted: `__udivti3` where
/// the source divides signed is a named call-target mismatch; a value kept
/// in a caller-saved register across the call (the dividend's high half read
/// from RSI after it) is an undefined read.
#[test]
fn a_wrong_routine_or_a_clobbered_register_is_a_named_mismatch() {
    let (source, mut machine) = slice22_pair(Shape22::I128Div);
    let call = call_rows(&machine)[0].0;
    inst_mut(&mut machine, call).operands[0] = O::Symbol("__udivti3".into());
    match fixture_owner(&source, &machine) {
        Err(X86BodyRefusal::Mismatch(X86BodyMismatch::CallTarget {
            expected, found, ..
        })) => {
            assert!(
                expected.contains("__divti3") && found.contains("__udivti3"),
                "{expected} / {found}"
            );
        }
        other => panic!("__udivti3 for __divti3: {:?}", other.map(|_| "a theorem")),
    }
    let (source, mut machine) = slice22_pair(Shape22::U128Div);
    let call = call_rows(&machine)[0].0;
    inst_mut(&mut machine, call + 2).operands[1] = preg(trust_cg_ir::x86_64_regs::RSI.encoding());
    match fixture_owner(&source, &machine) {
        Err(X86BodyRefusal::Mismatch(X86BodyMismatch::UndefinedRead { .. })) => {}
        other => panic!(
            "RSI read after the call: {:?}\n{}",
            other.map(|_| "a theorem"),
            describe(&machine)
        ),
    }
}

/// Slice 17's liveness reads every escaping slot at an `I128` division, as
/// at any call (the theorem states the division as one), and at no narrower
/// division.
#[test]
fn an_i128_division_is_a_call_for_the_byte_liveness() {
    for shape in SLICE_TWENTY_TWO {
        let source = slice22_lir(shape);
        let wide = split::i128_divisions(&source);
        let divisions: usize = source
            .blocks
            .values()
            .flat_map(|body| &body.instructions)
            .filter(|inst| matches!(inst.opcode, L::Udiv | L::Sdiv | L::Urem | L::Srem))
            .count();
        assert_eq!(
            wide.len(),
            divisions,
            "{shape:?}\n{}",
            describe_lir(&source)
        );
        assert_eq!(divisions, shape.divisions(), "{shape:?}");
    }
    let narrow = super::slice14::slice14_lir(super::slice14::DefinedShape::UdivChecked);
    assert!(split::i128_divisions(&narrow).is_empty());
}

/// Every slice-22 fixture's theorem as the replay renders it (`;;;; <shape>`).
pub(crate) fn slice_twenty_two_snapshots() -> String {
    let mut rendered = String::new();
    for shape in SLICE_TWENTY_TWO {
        let (source, machine) = slice22_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        rendered.push_str(&format!(";;;; {shape:?}\n{}\n", text(owner.obligation())));
    }
    rendered
}

/// The reviewed digest of the slice-22 golden text.
const SLICE_TWENTY_TWO_SNAPSHOT_SHA256: &str =
    "f08d9117dd86d22abcfb39fa1c9ef9da7138060a0141e8dd050171e66e346e1b";

/// The rendered theorems of every slice-22 fixture are the reviewed golden
/// text, pinned by digest, and independent of the function's name.
#[test]
fn slice_twenty_two_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice22_snapshots.smt2");
    let rendered = slice_twenty_two_snapshots();
    for shape in SLICE_TWENTY_TWO {
        let (source, machine) = slice22_pair(shape);
        let (mut renamed_source, mut renamed_machine) = (source.clone(), machine.clone());
        renamed_source.name = "renamed_function".into();
        renamed_machine.name = "renamed_function".into();
        let original = owner("original", &source, &machine);
        let renamed = owner("renamed", &renamed_source, &renamed_machine);
        assert_eq!(
            text(renamed.obligation()),
            text(original.obligation()),
            "{shape:?}"
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice22_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWENTY_TWO_SNAPSHOT_SHA256 to {:x} and \
             re-run without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_TWENTY_TWO_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-22 snapshots drifted");
}

// ---------------------------------------------------------------------------
// OD-202's evidence for the routine contract (statistical, never a proof)
// ---------------------------------------------------------------------------

#[allow(improper_ctypes)]
unsafe extern "C" {
    /// The routines the link binds to these names: in this Rust test binary,
    /// the Trust sysroot's `compiler_builtins` (what every Rust binary binds;
    /// measured with `nm` in the slice-22 design, `native/rustlink/`).
    fn __udivti3(a: u128, b: u128) -> u128;
    fn __umodti3(a: u128, b: u128) -> u128;
    fn __divti3(a: i128, b: i128) -> i128;
    fn __modti3(a: i128, b: i128) -> i128;
}

/// The four routines under test, as one value.
#[derive(Clone, Copy)]
struct Routines {
    udiv: fn(u128, u128) -> u128,
    umod: fn(u128, u128) -> u128,
    sdiv: fn(i128, i128) -> i128,
    smod: fn(i128, i128) -> i128,
}

fn linked_udiv(a: u128, b: u128) -> u128 {
    // SAFETY: the System V `__udivti3` of two `u128` (b != 0 at every call).
    unsafe { __udivti3(a, b) }
}
fn linked_umod(a: u128, b: u128) -> u128 {
    // SAFETY: as `linked_udiv`.
    unsafe { __umodti3(a, b) }
}
fn linked_sdiv(a: i128, b: i128) -> i128 {
    // SAFETY: as `linked_udiv`, never at `MIN / -1`.
    unsafe { __divti3(a, b) }
}
fn linked_smod(a: i128, b: i128) -> i128 {
    // SAFETY: as `linked_sdiv`.
    unsafe { __modti3(a, b) }
}

const LINKED: Routines = Routines {
    udiv: linked_udiv,
    umod: linked_umod,
    sdiv: linked_sdiv,
    smod: linked_smod,
};

/// trust-ir's `UDiv`/`URem` (floor and modulo) of `n` by `d != 0`, computed
/// INDEPENDENTLY of the routines under test: bit-serial restoring division
/// on two `u64` halves, with shifts, compares and subtractions only (no
/// 128-bit division, so no runtime call; trust-ir's own interpreter computes
/// `u128 /`, which lowers to the very `__udivti3` under test, and so is no
/// reference here).
fn reference_udivrem(n: u128, d: u128) -> (u128, u128) {
    let (mut q_hi, mut q_lo, mut r_hi, mut r_lo) = (0u64, 0u64, 0u64, 0u64);
    let (n_hi, n_lo) = ((n >> 64) as u64, n as u64);
    let (d_hi, d_lo) = ((d >> 64) as u64, d as u64);
    for i in (0..128u32).rev() {
        // r = (r << 1) | bit i of n.
        let bit = if i >= 64 {
            (n_hi >> (i - 64)) & 1
        } else {
            (n_lo >> i) & 1
        };
        r_hi = (r_hi << 1) | (r_lo >> 63);
        r_lo = (r_lo << 1) | bit;
        // if r >= d { r -= d; q |= 1 << i }
        if (r_hi, r_lo) >= (d_hi, d_lo) {
            let (low, borrow) = r_lo.overflowing_sub(d_lo);
            r_lo = low;
            r_hi = r_hi.wrapping_sub(d_hi).wrapping_sub(u64::from(borrow));
            if i >= 64 {
                q_hi |= 1 << (i - 64);
            } else {
                q_lo |= 1 << i;
            }
        }
    }
    (
        (u128::from(q_hi) << 64) | u128::from(q_lo),
        (u128::from(r_hi) << 64) | u128::from(r_lo),
    )
}

/// trust-ir's `SDiv`/`SRem` (truncating toward zero; the remainder takes the
/// dividend's sign) where it is defined (`d != 0`, not `MIN / -1`).
fn reference_sdivrem(a: i128, b: i128) -> Option<(i128, i128)> {
    if b == 0 || (a == i128::MIN && b == -1) {
        return None;
    }
    let (q, r) = reference_udivrem(a.unsigned_abs(), b.unsigned_abs());
    let q = if (a < 0) != (b < 0) {
        q.wrapping_neg()
    } else {
        q
    };
    let r = if a < 0 { r.wrapping_neg() } else { r };
    Some((q as i128, r as i128))
}

/// A seeded xoroshiro128+ (the design's `diff_ti3.c`).
struct Xoroshiro([u64; 2]);

impl Xoroshiro {
    fn next(&mut self) -> u64 {
        let [s0, mut s1] = self.0;
        let r = s0.wrapping_add(s1);
        s1 ^= s0;
        self.0 = [s0.rotate_left(24) ^ s1 ^ (s1 << 16), s1.rotate_left(37)];
        r
    }

    /// A value of exactly `bits` significant bits (0: zero).
    fn bits(&mut self, bits: u32) -> u128 {
        if bits == 0 {
            return 0;
        }
        let mut v = (u128::from(self.next()) << 64) | u128::from(self.next());
        if bits < 128 {
            v &= (1u128 << bits) - 1;
        }
        v | (1u128 << (bits - 1))
    }
}

/// The differential of `routines` against the reference on trust-ir's
/// defined domain (the design's `diff_ti3.c`: every pair of an edge set,
/// `per_class` random pairs in each class of dividend and divisor bit
/// lengths, and `q d + r` with `r` at 0, 1 and `d - 1`): `(checks,
/// mismatches)`.
fn differential(routines: Routines, per_class: u64) -> (u64, u64) {
    let (mut checks, mut mismatches) = (0u64, 0u64);
    let mut one = |a: u128, b: u128| {
        if b != 0 {
            let (q, r) = reference_udivrem(a, b);
            mismatches += u64::from((routines.udiv)(a, b) != q);
            mismatches += u64::from((routines.umod)(a, b) != r);
            checks += 2;
        }
        if let Some((q, r)) = reference_sdivrem(a as i128, b as i128) {
            mismatches += u64::from((routines.sdiv)(a as i128, b as i128) != q);
            mismatches += u64::from((routines.smod)(a as i128, b as i128) != r);
            checks += 2;
        }
    };
    let mut edge: Vec<u128> = vec![
        0,
        1,
        2,
        3,
        7,
        10,
        10_000_000_000_000_000,
        10_000_000_000_000_000_000,
    ];
    for k in [31u32, 32, 63, 64, 65, 96, 126, 127] {
        let p = 1u128 << k;
        edge.extend([p - 1, p, p + 1]);
    }
    let min = 1u128 << 127;
    edge.extend([u128::MAX, u128::MAX - 1, min, min + 1, min - 1]);
    let negated: Vec<u128> = edge.iter().map(|v| v.wrapping_neg()).collect();
    edge.extend(negated);
    for &a in &edge {
        for &b in &edge {
            one(a, b);
        }
    }
    let mut rng = Xoroshiro([0x9E37_79B9_7F4A_7C15, 0xD1B5_4A32_D192_ED03]);
    let lengths = [0u32, 1, 2, 8, 31, 32, 33, 63, 64, 65, 96, 127, 128];
    for &a_bits in &lengths {
        for &b_bits in &lengths {
            for _ in 0..per_class {
                let (a, b) = (rng.bits(a_bits), rng.bits(b_bits));
                one(a, b);
            }
        }
    }
    for _ in 0..13 * per_class {
        let d_bits = 1 + (rng.next() % 127) as u32;
        let d = rng.bits(d_bits);
        let q_bits = (rng.next() % u64::from(129 - d_bits)) as u32;
        let q = rng.bits(q_bits);
        let base = q.wrapping_mul(d);
        for r in [0, 1, d - 1] {
            if let Some(v) = base.checked_add(r) {
                one(v, d);
            }
        }
    }
    (checks, mismatches)
}

/// OD-202's evidence (statistical, NEVER credit): the routines this test
/// binary binds to `__udivti3`, `__umodti3`, `__divti3` and `__modti3` (the
/// Trust sysroot's `compiler_builtins`, what a Rust program links) agree with
/// an independent reference of trust-ir's division on trust-ir's defined
/// domain, and the harness reports a wrong routine. The platform's copy (a C
/// link's libSystem) is run by the slice-22 report's `native/run_diff.sh`.
/// `TCG_I128_DIVISION_DIFFERENTIAL_PER_CLASS` sets the random pairs per
/// class (the report's run: 20000, 15.6 M checks).
#[test]
fn the_i128_division_routines_match_an_independent_reference() {
    let per_class = std::env::var("TCG_I128_DIVISION_DIFFERENTIAL_PER_CLASS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(200);
    let (checks, mismatches) = differential(LINKED, per_class);
    eprintln!("SLICE22_DIFFERENTIAL per_class={per_class} checks={checks} mismatches={mismatches}");
    assert_eq!(
        mismatches, 0,
        "a linked i128 routine disagrees with trust-ir"
    );
    assert!(checks > 0);
    // The control: a quotient whose low bit flips for a divisor with a high
    // half must be reported, or the harness checks nothing.
    fn wrong_udiv(a: u128, b: u128) -> u128 {
        linked_udiv(a, b) ^ u128::from(b >> 64 != 0)
    }
    let (_, caught) = differential(
        Routines {
            udiv: wrong_udiv,
            ..LINKED
        },
        per_class.min(50),
    );
    assert!(caught > 0, "the harness misses a wrong __udivti3");
    // The reference against Rust's own operators at a few points (those
    // compile to the same routines, so this checks the reference, not them).
    for (a, b) in [
        (u128::MAX, 3u128),
        (1u128 << 100, (1u128 << 64) + 7),
        (12345, 1),
    ] {
        assert_eq!(reference_udivrem(a, b), (a / b, a % b));
    }
    assert_eq!(reference_sdivrem(-7, 2), Some((-3, -1)));
    assert_eq!(reference_sdivrem(7, -2), Some((-3, 1)));
    assert_eq!(reference_sdivrem(i128::MIN, -1), None);
}

// ---------------------------------------------------------------------------
// OD-203: the 128-bit product by its 64-bit limbs (`limb`, `addhi0`, `acmul`)
// ---------------------------------------------------------------------------

/// Every assignment of `vars` (at most 16 bits in all).
fn every_value(vars: &[(&str, u32)]) -> Vec<HashMap<String, u128>> {
    let bits: u32 = vars.iter().map(|(_, width)| width).sum();
    assert!(bits <= 16, "{bits} bits of inputs");
    (0..1u128 << bits)
        .map(|mut packed| {
            vars.iter()
                .map(|(name, width)| {
                    let value = packed & ((1 << width) - 1);
                    packed >>= width;
                    ((*name).to_owned(), value)
                })
                .collect()
        })
        .collect()
}

/// `term` normalized with `groups` and limbs of `limb` bits, checked against
/// `term` on every assignment of `vars`: the same width and the same value.
/// `Some(inputs checked)` when the normalizer rewrites `term`, `None` when it
/// leaves it as it is.
fn exact_with_limb(term: &E, vars: &[(&str, u32)], groups: Groups, limb: u32) -> Option<usize> {
    use super::slice18::{Val, exact_eval};
    let normal = normal::normalized_term_with_limb(term, groups, limb)
        .unwrap_or_else(|| panic!("{term} is outside the spelling's vocabulary"));
    if normal == *term {
        return None;
    }
    assert_eq!(
        normal.try_bv_width().ok(),
        term.try_bv_width().ok(),
        "{term} -> {normal} changes the width"
    );
    let inputs = every_value(vars);
    for env in &inputs {
        let (mut a, mut b) = (HashMap::new(), HashMap::new());
        let (x, y): (Val, Val) = (
            exact_eval(term, env, &mut a),
            exact_eval(&normal, env, &mut b),
        );
        assert_eq!(x, y, "{term} -> {normal} at {env:?}");
    }
    Some(inputs.len())
}

/// The `limb`, `addhi0` and `acmul` groups with the "v18" groups they rely on
/// to fold their constants.
fn limb_groups() -> Groups {
    Groups::EXT
        .with(Groups::FOLD)
        .with(Groups::ARITH)
        .with(Groups::PRODUCT_LIMBS)
}

/// Whether `expr` has a node `pick` accepts.
fn has_node(expr: &E, pick: &dyn Fn(&E) -> bool) -> bool {
    if pick(expr) {
        return true;
    }
    let mut found = false;
    expr.for_each_child(&mut |child| found = found || has_node(child, pick));
    found
}

/// OD-203's three groups, each exact on every input at small widths: `limb`
/// on every `2n`-bit product shape it rewrites (two variables, a variable by
/// an extension of an `n`-bit one, a variable by every constant) at `n` = 1
/// to 4, every pair of operands; `addhi0` at every width to 6 and every
/// split, either addend order; `acmul` on sums of three and four addends
/// with a product leaf (a limb-wide product, or the high limb of a widening
/// product) at limbs of 1 to 3 bits. The design's C program checked `limb`
/// and `addhi0` exhaustively at `n` = 1 to 8 and z3 at 128 bits in integer
/// arithmetic (the report's `limb/`).
#[test]
fn every_limb_group_is_exact_exhaustively_at_small_widths() {
    let mut rewritten: std::collections::BTreeMap<&str, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut tally = |group: &'static str, checked: Option<usize>| {
        let entry = rewritten.entry(group).or_default();
        if let Some(inputs) = checked {
            entry.0 += 1;
            entry.1 += inputs;
        }
    };
    let groups = limb_groups();
    for n in 1..=4u32 {
        let w = 2 * n;
        let (x, y) = (E::var("x", w), E::var("y", w));
        let checked = exact_with_limb(
            &x.clone().bvmul(y.clone()),
            &[("x", w), ("y", w)],
            groups,
            n,
        );
        assert!(
            checked.is_some(),
            "limb rewrites the {w}-bit product of two variables"
        );
        tally("limb", checked);
        let narrow = E::var("z", n);
        for operand in [narrow.clone().zero_ext(n), narrow.clone().sign_ext(n)] {
            tally(
                "limb",
                exact_with_limb(
                    &x.clone().bvmul(operand.clone()),
                    &[("x", w), ("z", n)],
                    groups,
                    n,
                ),
            );
            tally(
                "limb",
                exact_with_limb(&operand.bvmul(x.clone()), &[("x", w), ("z", n)], groups, n),
            );
        }
        if w <= 6 {
            for c in 0..1u64 << w {
                tally(
                    "limb",
                    exact_with_limb(&x.clone().bvmul(E::bv_const(c, w)), &[("x", w)], groups, n),
                );
            }
        }
        // The low and high limbs of the product read through the rewrite.
        let product = x.clone().bvmul(y.clone());
        tally(
            "limb+addhi0",
            exact_with_limb(
                &product.clone().extract(w - 1, n),
                &[("x", w), ("y", w)],
                groups,
                n,
            ),
        );
        tally(
            "limb+addhi0",
            exact_with_limb(&product.extract(n - 1, 0), &[("x", w), ("y", w)], groups, n),
        );
    }
    for w in 2..=6u32 {
        for k in 1..w {
            let a = E::var("a", w);
            let shifted = E::var("x", w - k).concat(E::bv_const(0, k));
            for sum in [a.clone().bvadd(shifted.clone()), shifted.bvadd(a.clone())] {
                tally(
                    "addhi0",
                    exact_with_limb(
                        &sum.extract(w - 1, k),
                        &[("a", w), ("x", w - k)],
                        groups,
                        64,
                    ),
                );
            }
            // The low bits a nonzero constant: whatever rewrites the term
            // keeps its value (`addhi0` must not apply; a carry may leave).
            for c in 1..1u64 << k {
                let filled = E::var("x", w - k).concat(E::bv_const(c, k));
                let sum = a.clone().bvadd(filled);
                exact_with_limb(
                    &sum.extract(w - 1, k),
                    &[("a", w), ("x", w - k)],
                    groups,
                    64,
                );
            }
        }
    }
    for n in 1..=3u32 {
        let (a, b, c, d) = (
            E::var("a", n),
            E::var("b", n),
            E::var("c", n),
            E::var("d", n),
        );
        let high = a
            .clone()
            .zero_ext(n)
            .bvmul(b.clone().zero_ext(n))
            .extract(2 * n - 1, n);
        let vars = [("a", n), ("b", n), ("c", n), ("d", n)];
        for sum in [
            c.clone().bvadd(a.clone().bvmul(b.clone())).bvadd(d.clone()),
            d.clone().bvadd(c.clone().bvadd(a.clone().bvmul(b.clone()))),
            high.clone()
                .bvadd(c.clone().bvmul(d.clone()))
                .bvadd(a.clone()),
            a.clone()
                .bvadd(high.clone())
                .bvadd(b.clone().bvmul(c.clone())),
            c.clone().bvadd(high.clone()),
        ] {
            tally("acmul", exact_with_limb(&sum, &vars, groups, n));
        }
    }
    eprintln!("SLICE22_LIMB_EXHAUSTIVE (rewritten, inputs) {rewritten:?}");
    for group in ["limb", "limb+addhi0", "addhi0", "acmul"] {
        assert!(
            rewritten.get(group).is_some_and(|(count, _)| *count > 0),
            "{group} rewrote nothing: {rewritten:?}"
        );
    }
}

/// What OD-203's groups leave alone: a widening product (both operands
/// extensions of a limb, or a limb-wide constant), which `ovf`, `ovf2`,
/// `sovf` and `magic` read; a product of another width; the high bits of a
/// sum whose other addend's low bits are not the zero constant (or that the
/// extract does not reach the top of); a sum with no product leaf, or wider
/// than a limb.
#[test]
fn the_limb_groups_leave_what_they_do_not_rewrite() {
    let groups = Groups::CANONICAL;
    let unchanged = |term: E| {
        let normal = normal::normalized_term(&term, groups).expect("in the vocabulary");
        assert!(
            !has_node(&normal, &|node| matches!(node, E::Concat { .. }))
                || has_node(&term, &|node| matches!(node, E::Concat { .. })),
            "{term} -> {normal}"
        );
        normal
    };
    let (a, b) = (E::var("a", 64), E::var("b", 64));
    for widening in [
        a.clone().zero_ext(64).bvmul(b.clone().zero_ext(64)),
        a.clone().sign_ext(64).bvmul(b.clone().sign_ext(64)),
        a.clone()
            .zero_ext(64)
            .bvmul(E::bv_const(10_000_000_000_000_000, 128)),
        E::var("w", 32).zero_ext(96).bvmul(b.clone().zero_ext(64)),
    ] {
        let normal = unchanged(widening.clone());
        assert!(
            matches!(normal, E::BvMul { width: 128, .. }),
            "limb rewrote the widening product {widening} -> {normal}"
        );
    }
    let narrow = E::var("p", 64).bvmul(E::var("q", 64));
    assert_eq!(
        unchanged(narrow.clone()),
        narrow,
        "limb rewrote a 64-bit product"
    );
    let wide = E::var("u", 128);
    let ones = E::var("x", 64).concat(E::bv_const(1, 64));
    let not_zero_low = wide.clone().bvadd(ones).extract(127, 64);
    let normal = normal::normalized_term(&not_zero_low, groups).unwrap();
    assert!(
        !matches!(normal, E::BvAdd { width: 64, .. }),
        "addhi0 rewrote a sum whose low addend bits are not zero: {normal}"
    );
    let below_top = wide
        .bvadd(E::var("x", 64).concat(E::bv_const(0, 64)))
        .extract(126, 64);
    let normal = normal::normalized_term(&below_top, groups).unwrap();
    assert!(
        matches!(normal, E::Extract { .. }),
        "addhi0 rewrote an extract below the top bit: {normal}"
    );
    let (c, d) = (E::var("c", 64), E::var("d", 64));
    let plain = d.clone().bvadd(c.clone()).bvadd(a.clone());
    assert_eq!(
        normal::normalized_term(&plain, groups).unwrap(),
        plain,
        "acmul reordered a sum without a product leaf"
    );
    let (c128, d128) = (E::var("c", 128), E::var("d", 128));
    let wide_sum = d128.bvadd(c128.bvmul(E::var("e", 128)));
    let normal = normal::normalized_term(&wide_sum, groups.without(Groups::LIMB)).unwrap();
    assert!(
        matches!(&normal, E::BvAdd { lhs, .. } if matches!(lhs.as_ref(), E::Var { .. })),
        "acmul reordered a 128-bit sum: {normal}"
    );
}

/// `acmul` orders addends by their structure alone: the same sum is spelled
/// alike whatever the term table created first (the spelling of a sum must
/// not depend on the theorem around it), and a sum and its addends'
/// permutations are spelled alike.
#[test]
fn the_product_sum_order_is_independent_of_creation_order() {
    let (a, b, x, y) = (
        E::var("a", 64),
        E::var("b", 64),
        E::var("x", 64),
        E::var("y", 64),
    );
    let product = a.clone().bvmul(b.clone());
    let sums = [
        x.clone().bvadd(product.clone()).bvadd(y.clone()),
        y.clone().bvadd(x.clone()).bvadd(product.clone()),
        product.clone().bvadd(y.clone().bvadd(x.clone())),
        b.clone().bvmul(a.clone()).bvadd(x.clone()).bvadd(y.clone()),
    ];
    // Each sum normalized alone, and after a table has created its leaves in
    // the reverse order (`normalized_after`): one spelling throughout.
    let reversed = y.clone().bvxor(x.clone()).bvxor(b.clone()).bvxor(a.clone());
    let spellings: std::collections::BTreeSet<String> = sums
        .iter()
        .flat_map(|sum| {
            [
                normal::normalized_term(sum, Groups::CANONICAL).unwrap(),
                normal::normalized_after(&reversed, sum, Groups::CANONICAL).unwrap(),
            ]
        })
        .map(|spelled| spelled.to_string())
        .collect();
    assert_eq!(
        spellings.len(),
        2,
        "a product sum's spelling depends on creation order or addend order: {spellings:?}"
    );
    // (Two spellings: `a*b` and `b*a` are distinct products; `bvmul` is not
    // reordered.)
}

/// The two halves of a product of 128-bit values the selector computes
/// (`mul`, two `imul`s, two `add`s), wrongly: each wrong lowering of slice
/// 11's `MulU128` fixture.
pub(crate) fn wrong_multiplies() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use super::slice11::{WideShape, slice11_pair};
    let rows_of = |machine: &X86ISelFunction, opcode: X86Opcode| find(machine, opcode);
    let mut cases = Vec::new();
    // A cross product omitted: `dst_hi = sum1`.
    {
        let (source, mut machine) = slice11_pair(WideShape::MulU128);
        let last_add = *rows_of(&machine, X86Opcode::AddRR).last().unwrap();
        let row = inst_mut(&mut machine, last_add);
        let (dst, sum) = (row.operands[0].clone(), row.operands[1].clone());
        *row = X86ISelInst::new(X86Opcode::MovRR, vec![dst, sum]);
        cases.push(("mul128/cross-product-omitted", source, machine));
    }
    // A cross product's operands wrong: `aH * bH`.
    {
        let (source, mut machine) = slice11_pair(WideShape::MulU128);
        let [first, second] = rows_of(&machine, X86Opcode::ImulRR)[..] else {
            panic!("two imul rows")
        };
        let a_hi = inst(&machine, second).operands[1].clone();
        inst_mut(&mut machine, first).operands[1] = a_hi;
        cases.push(("mul128/cross-aH-bH", source, machine));
    }
    // The low product's high half from the wrong operands: `mul` by `bH`.
    {
        let (source, mut machine) = slice11_pair(WideShape::MulU128);
        let mul = rows_of(&machine, X86Opcode::Mul)[0];
        let first = rows_of(&machine, X86Opcode::ImulRR)[0];
        let b_hi = inst(&machine, first).operands[2].clone();
        inst_mut(&mut machine, mul).operands[0] = b_hi;
        cases.push(("mul128/low-product-wrong-operand", source, machine));
    }
    // The two cross products' registers swapped between halves: `aL * bL`
    // and `aH * bH`.
    {
        let (source, mut machine) = slice11_pair(WideShape::MulU128);
        let [first, second] = rows_of(&machine, X86Opcode::ImulRR)[..] else {
            panic!("two imul rows")
        };
        let (a_lo, b_hi) = (
            inst(&machine, first).operands[1].clone(),
            inst(&machine, first).operands[2].clone(),
        );
        let (a_hi, b_lo) = (
            inst(&machine, second).operands[1].clone(),
            inst(&machine, second).operands[2].clone(),
        );
        inst_mut(&mut machine, first).operands[2] = b_lo;
        inst_mut(&mut machine, second).operands[2] = b_hi;
        let _ = (a_lo, a_hi);
        cases.push(("mul128/cross-operands-swapped", source, machine));
    }
    // `dst_lo` from RDX.
    {
        let (source, mut machine) = slice11_pair(WideShape::MulU128);
        let mul = rows_of(&machine, X86Opcode::Mul)[0];
        let rdx = inst(&machine, mul + 2).operands[1].clone();
        inst_mut(&mut machine, mul + 1).operands[1] = rdx;
        cases.push(("mul128/low-half-from-rdx", source, machine));
    }
    cases
}

/// Every wrong multiply stays refuted under OD-203's spelling: its theorem
/// builds, keeps a claim and is refuted on samples, and the production
/// verifier never credits it. The correct `MulU128`'s claim drops (both
/// sides spell its high limb alike), so by slice 9's rule its theorem keeps
/// slice 18's spelling.
#[test]
fn a_wrong_multiply_stays_refuted_and_the_correct_one_keeps_slice_eighteens_spelling() {
    use super::slice11::{WideShape, slice11_pair};
    for (label, source, machine) in wrong_multiplies() {
        let owner = fixture_owner(&source, &machine)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(
            dag_refuted_on_samples(owner.obligation())
                || (0..super::slice10::EDGE_SAMPLES)
                    .any(|seed| !super::slice10::holds_at_edge(owner.obligation(), seed)),
            "{label}: a wrong multiply's theorem holds on samples\n{}{}",
            describe(&machine),
            text(owner.obligation())
        );
        let outcome = super::slice12::never_credited(&source, &machine, label);
        assert_ne!(outcome, "credited", "{label}");
    }
    let (source, machine) = slice11_pair(WideShape::MulU128);
    let built = |encoding: PathEncoding| {
        single_theorem_with_encoding(&source, &machine, SYSV, encoding, false)
            .expect("one query")
            .expect("stated")
    };
    let canonical = built(PathEncoding::CANONICAL);
    let slice18 = built(PathEncoding {
        normal: Groups::NONE,
        ..PathEncoding::CANONICAL
    });
    assert_ne!(
        canonical.2,
        Spelling::Normal,
        "MulU128 is spelled by identities alone"
    );
    assert_eq!(canonical.0, slice18.0, "MulU128 keeps slice 18's spelling");
    let without = built(PathEncoding {
        normal: Groups::CANONICAL.without(Groups::PRODUCT_LIMBS),
        ..PathEncoding::CANONICAL
    });
    assert_eq!(
        without.2,
        Spelling::Normal,
        "slice 19's spelling of MulU128"
    );
}

/// Every golden file's digest before OD-203 (main with slice 22a,
/// `40d70a92f`): the canonical spelling without OD-203's groups re-renders
/// each byte for byte (the custody of the golden migration).
const PRE_LIMB_DIGESTS: &[(&str, &str)] = &[
    (
        "snapshots.smt2",
        "d43b7611015fe5cd1799162d4784b7a08b274db431dbf49fbd7fc154809b9480",
    ),
    (
        "memory_snapshots.smt2",
        "45a5b165ca2b0db8fa12fab872072dbb239fa0cea4f5a761c0f3e40ddcf4c55a",
    ),
    (
        "slice5_snapshots.smt2",
        "f573f241a3c82551c74cf9ccc34ef6410f5dfddbeca27c371296a1072756a653",
    ),
    (
        "slice6_snapshots.smt2",
        "d96b1d589ede3069ed9eb4a9bd48ac8147a0c78b2f869cd9c611a60d03940b88",
    ),
    (
        "slice7_snapshots.smt2",
        "e8786dda14882fa0d492712200e22a3e2494070bc6b54ff08b36823ec564ea99",
    ),
    (
        "slice8_snapshots.smt2",
        "5b69318d28c2f0b53f5317648744e8f1e7331bab6475a8c277d743f7d1542212",
    ),
    (
        "slice9_snapshots.smt2",
        "9ad06e11b73f578abcf611f69d5372baa0bcd8b11ae78c149e77f3af294a65e3",
    ),
    (
        "slice10_snapshots.smt2",
        "88b63d82e6cb61916c6921cb51a7cb4b916271871ec02b0a6a539d2a7bf109bf",
    ),
    (
        "slice11_snapshots.smt2",
        "95df1a8b970a84180fbe42e4e9b6a656a2d3a8b1bf88749a880810b36fc45ec9",
    ),
    (
        "slice12_snapshots.smt2",
        "18a4647c1c574879cd1e8b66dbbf6a37a4dece3a03d0c5cf5a72613cea38e26b",
    ),
    (
        "slice13_snapshots.smt2",
        "5e5cd1ef121b9b081b536e592f0c6988037d7c296b8cc0a3796f611a69ecae53",
    ),
    (
        "slice14_snapshots.smt2",
        "48e7d6648a4ba25e330a24d20060ef05ca2dd5482f74b33be50d34c9b33124a1",
    ),
    (
        "slice15_snapshots.smt2",
        "10a4d42227f52869618249b954a9360994c142c8a3c78e60d58daac58d7a9895",
    ),
    (
        "arraygep_snapshots.smt2",
        "144a12d55cde752af8884e1e21d2d4b1e41aa58753e71c112138ea92b67679b4",
    ),
    (
        "slice16_parts_snapshots.smt2",
        "99bf2be7aa534c37d1281944d843b1fbde2235116b04417ea6adcd8ccd159ace",
    ),
    (
        "slice20_snapshots.smt2",
        "cdb89e3a9b9c1bae40c5a6c7744dc1cb2f13658b2a7c4467e3dd7aa52eddd782",
    ),
    (
        "slice21_snapshots.smt2",
        "2b613c0a7e73202462f2a18d630bb485c8defe123cb332ca833ea2d7e18d4da6",
    ),
];

/// Every golden file's digest before OD-204 (`catnf`; with OD-202 and
/// OD-203, `821e448c2`).
const PRE_CATNF_DIGESTS: &[(&str, &str)] = &[
    (
        "snapshots.smt2",
        "d43b7611015fe5cd1799162d4784b7a08b274db431dbf49fbd7fc154809b9480",
    ),
    (
        "memory_snapshots.smt2",
        "45a5b165ca2b0db8fa12fab872072dbb239fa0cea4f5a761c0f3e40ddcf4c55a",
    ),
    (
        "slice5_snapshots.smt2",
        "f573f241a3c82551c74cf9ccc34ef6410f5dfddbeca27c371296a1072756a653",
    ),
    (
        "slice6_snapshots.smt2",
        "d96b1d589ede3069ed9eb4a9bd48ac8147a0c78b2f869cd9c611a60d03940b88",
    ),
    (
        "slice7_snapshots.smt2",
        "e8786dda14882fa0d492712200e22a3e2494070bc6b54ff08b36823ec564ea99",
    ),
    (
        "slice8_snapshots.smt2",
        "5b69318d28c2f0b53f5317648744e8f1e7331bab6475a8c277d743f7d1542212",
    ),
    (
        "slice9_snapshots.smt2",
        "9ad06e11b73f578abcf611f69d5372baa0bcd8b11ae78c149e77f3af294a65e3",
    ),
    (
        "slice10_snapshots.smt2",
        "88b63d82e6cb61916c6921cb51a7cb4b916271871ec02b0a6a539d2a7bf109bf",
    ),
    (
        "slice11_snapshots.smt2",
        "c2a8ca28168c8d7d47810dbd83b0aa5f6799947a09e830e9ba9689d643428864",
    ),
    (
        "slice12_snapshots.smt2",
        "18a4647c1c574879cd1e8b66dbbf6a37a4dece3a03d0c5cf5a72613cea38e26b",
    ),
    (
        "slice13_snapshots.smt2",
        "5e5cd1ef121b9b081b536e592f0c6988037d7c296b8cc0a3796f611a69ecae53",
    ),
    (
        "slice14_snapshots.smt2",
        "732345dfcebc05d80a49743895f7a265de4c8d8ef1f6088db3bc34e63c5fe8bb",
    ),
    (
        "slice15_snapshots.smt2",
        "10a4d42227f52869618249b954a9360994c142c8a3c78e60d58daac58d7a9895",
    ),
    (
        "arraygep_snapshots.smt2",
        "144a12d55cde752af8884e1e21d2d4b1e41aa58753e71c112138ea92b67679b4",
    ),
    (
        "slice16_parts_snapshots.smt2",
        "99bf2be7aa534c37d1281944d843b1fbde2235116b04417ea6adcd8ccd159ace",
    ),
    (
        "slice20_snapshots.smt2",
        "cdb89e3a9b9c1bae40c5a6c7744dc1cb2f13658b2a7c4467e3dd7aa52eddd782",
    ),
    (
        "slice21_snapshots.smt2",
        "2b613c0a7e73202462f2a18d630bb485c8defe123cb332ca833ea2d7e18d4da6",
    ),
    (
        "slice22_snapshots.smt2",
        "2a74cf195dbe025a67bbb55356e4056136986f9c54473634715c6b369f877839",
    ),
];

/// One golden file's name and the function that renders it as its snapshot
/// test does.
type GoldenRenderer = (&'static str, Box<dyn Fn() -> String>);

/// Every golden file and the function that renders it as its snapshot test
/// does (slice 22's included when `with_slice22`).
fn golden_renderers(with_slice22: bool) -> Vec<GoldenRenderer> {
    let mut renderers: Vec<GoldenRenderer> = Vec::new();
    for (file, _, fixtures) in super::slice18::golden_files() {
        renderers.push((file, Box::new(move || super::slice18::render(&fixtures))));
    }
    renderers.push((
        "slice16_parts_snapshots.smt2",
        Box::new(super::slice16::slice_sixteen_parts_snapshots),
    ));
    renderers.push((
        "slice20_snapshots.smt2",
        Box::new(super::slice20::slice_twenty_snapshots),
    ));
    renderers.push((
        "slice21_snapshots.smt2",
        Box::new(super::slice21::slice_twenty_one_snapshots),
    ));
    if with_slice22 {
        renderers.push((
            "slice22_snapshots.smt2",
            Box::new(slice_twenty_two_snapshots),
        ));
    }
    renderers
}

/// Every golden rendered with `groups` is its digest in `before`, and
/// rendered canonically the committed file; prints which theorems moved.
fn custody(groups: Groups, before: &[(&str, &str)], with_slice22: bool, label: &str) {
    use sha2::{Digest, Sha256};
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body");
    let before: std::collections::BTreeMap<&str, &str> = before.iter().copied().collect();
    let mut moved = 0;
    // Every historical rendering selects as the selector did then, every
    // constant `I128` shift on the general path (OD-215 came later), and
    // translates as the adapter did then, every 128-bit checked multiply in
    // the division form (OD-224 came later still): the golden files'
    // fixtures are selected with the fold off and translated in the
    // division form, and the renderers that select as they render run so.
    let historical = |f: &dyn Fn() -> String| {
        super::with_i128_const_shift_fold(false, || {
            trust_cg_lower::with_x86_i128_mulo_division_form(true, f)
        })
    };
    let old_renderers = super::with_i128_const_shift_fold(false, || {
        trust_cg_lower::with_x86_i128_mulo_division_form(true, || golden_renderers(with_slice22))
    });
    for ((file, render), (_, old_render)) in golden_renderers(with_slice22)
        .into_iter()
        .zip(old_renderers)
    {
        let old = historical(&|| with_normal_groups(groups, &old_render));
        assert_eq!(
            format!("{:x}", Sha256::digest(old.as_bytes())),
            before[file],
            "{file}: the spelling without {label} no longer renders the golden before it"
        );
        let canonical = render();
        let committed = std::fs::read_to_string(dir.join(file)).unwrap();
        assert_eq!(
            canonical, committed,
            "{file}: the canonical rendering drifted"
        );
        let (old_sections, new_sections) = (
            super::snapshot_sections(&old),
            super::snapshot_sections(&canonical),
        );
        let changed: Vec<String> = old_sections
            .iter()
            .zip(&new_sections)
            .filter(|(a, b)| a != b)
            .map(|((label, _), _)| label.clone())
            .collect();
        moved += changed.len();
        eprintln!(
            "SLICE22_CUSTODY without={label} file={file} theorems={} changed={} {changed:?} \
             canonical_sha256={:x}",
            new_sections.len(),
            changed.len(),
            Sha256::digest(canonical.as_bytes())
        );
    }
    eprintln!("SLICE22_CUSTODY without={label} moved={moved}");
}

/// THE custody of the golden migrations: every earlier golden, rendered with
/// the canonical groups but OD-203's and OD-204's (`with_normal_groups`), is
/// its digest before OD-203 byte for byte, and with every group but OD-204's
/// its digest before OD-204; rendered canonically it is the committed file.
#[test]
fn the_canonical_spelling_without_the_limb_groups_reproduces_every_earlier_golden() {
    custody(
        Groups::CANONICAL
            .without(Groups::PRODUCT_LIMBS)
            .without(Groups::CATNF),
        PRE_LIMB_DIGESTS,
        false,
        "OD-203 and OD-204",
    );
    custody(
        Groups::CANONICAL.without(Groups::CATNF),
        PRE_CATNF_DIGESTS,
        true,
        "OD-204",
    );
}

/// The guard of OD-203's scope: theorems whose products are widening
/// (`U64CarryingMulAdd`, `u64::carrying_mul_add`'s value, and slice 10's
/// 64-bit checked multiplies) are spelled byte for byte as without the
/// groups; the measured cost of an unscoped sort (design §2.3) was
/// `carrying_mul_add`'s certificate.
///
/// Slice 23's pairing (OD-205) is not this guard's question: a spelling
/// without the canonical groups pairs nothing, so the canonical side is
/// built without it too.
#[test]
fn the_widening_product_theorems_keep_their_spelling() {
    let without = Groups::CANONICAL.without(Groups::PRODUCT_LIMBS);
    let (source, machine) = slice22_pair(Shape22::U64CarryingMulAdd);
    let canonical = with_arithmetic_pairing(false, || {
        text(owner("U64CarryingMulAdd", &source, &machine).obligation())
    });
    let before = with_normal_groups(without, || {
        text(owner("U64CarryingMulAdd", &source, &machine).obligation())
    });
    assert_eq!(canonical, before, "U64CarryingMulAdd");
    for shape in super::slice10::SLICE_TEN {
        let (source, machine) = super::slice10::slice10_pair(shape);
        let Ok(owner) =
            with_arithmetic_pairing(false, || source_bound_x86_body(&source, &machine, SYSV))
        else {
            continue;
        };
        let canonical = text(owner.obligation());
        let before = with_normal_groups(without, || {
            text(
                source_bound_x86_body(&source, &machine, SYSV)
                    .expect("stated")
                    .obligation(),
            )
        });
        assert_eq!(canonical, before, "{shape:?}");
    }
}

/// OD-203's guard step: a guarded item whose guard's double negation was
/// folded (`(or L X)`, `L` no negation) is read back as `(or (not (not L))
/// X)`, the skeleton the structural check reads, and keeps its value; a
/// guarded item, an equation and a negated literal's `or` are left alone;
/// without the step the folded item stays and fails the check.
#[test]
fn a_folded_guard_keeps_its_skeleton() {
    let (r, x, y) = (E::var("r", 1), E::var("x", 8), E::var("y", 8));
    let literal = r.clone().eq_expr(E::bv_const(0, 1));
    let body = x.clone().eq_expr(y.clone());
    let folded = literal.clone().or_expr(body.clone());
    let spelled = normal::normalized_claims_term(&folded, Groups::CANONICAL).expect("a claim");
    let E::Or { lhs, rhs } = &spelled else {
        panic!("{spelled}")
    };
    assert!(
        matches!(lhs.as_ref(), E::Not { operand } if matches!(operand.as_ref(), E::Not { .. })),
        "the guard is (not (not L)): {spelled}"
    );
    assert_eq!(rhs.as_ref(), &body, "{spelled}");
    let without = Groups::CANONICAL.without(Groups::GUARD);
    assert_eq!(
        normal::normalized_claims_term(&folded, without).expect("a claim"),
        folded,
        "without the step the folded item stays"
    );
    // Its value on every input of `r`, `x`, `y` at these widths' corners.
    use super::slice18::{Val, exact_eval};
    for (rv, xv, yv) in [(0u128, 1u128, 1u128), (0, 1, 2), (1, 1, 2), (1, 3, 3)] {
        let env: HashMap<String, u128> = [
            ("r".to_owned(), rv),
            ("x".to_owned(), xv),
            ("y".to_owned(), yv),
        ]
        .into_iter()
        .collect();
        let (a, b): (Val, Val) = (
            exact_eval(&folded, &env, &mut HashMap::new()),
            exact_eval(&spelled, &env, &mut HashMap::new()),
        );
        assert_eq!(a, b);
    }
    // Left alone: a guarded item, an equation.
    let guarded = literal.clone().not_expr().or_expr(body.clone());
    let kept = normal::normalized_claims_term(&guarded, Groups::CANONICAL).unwrap();
    assert!(
        matches!(&kept, E::Or { lhs, .. } if matches!(lhs.as_ref(), E::Not { operand } if !matches!(operand.as_ref(), E::Not { .. }))),
        "{kept}"
    );
    assert_eq!(
        normal::normalized_claims_term(&body, Groups::CANONICAL).unwrap(),
        body
    );
}

/// OD-204's `catnf`, each rule exact on every input at small widths: an
/// extract across a concatenation's halves (every split of every width
/// pair to 4 bits) and across a zero extension's boundary, the right
/// nesting of concatenations, the merge of adjacent extracts at a chain's
/// head, and the `bvor` of a zero extension with a chain ending in zeros
/// (one and two pieces); and what it leaves alone (a chain whose tail is no
/// zero constant, extracts that are not adjacent).
#[test]
fn the_bit_move_normal_form_is_exact_exhaustively() {
    let groups = Groups::EXT
        .with(Groups::FOLD)
        .with(Groups::ARITH)
        .with(Groups::CATNF);
    let mut rewritten: std::collections::BTreeMap<&str, (usize, usize)> =
        std::collections::BTreeMap::new();
    let mut tally = |rule: &'static str, checked: Option<usize>| {
        let entry = rewritten.entry(rule).or_default();
        if let Some(inputs) = checked {
            entry.0 += 1;
            entry.1 += inputs;
        }
    };
    for wa in 1..=4u32 {
        for wb in 1..=4u32 {
            let joined = E::var("a", wa).concat(E::var("b", wb));
            for low in 0..wb {
                for high in wb..wa + wb {
                    tally(
                        "extract-concat",
                        exact_with_limb(
                            &joined.clone().extract(high, low),
                            &[("a", wa), ("b", wb)],
                            groups,
                            64,
                        ),
                    );
                }
            }
        }
    }
    for wy in 1..=4u32 {
        for k in 1..=4u32 {
            let extended = E::var("y", wy).zero_ext(k);
            for low in 0..wy {
                for high in wy..wy + k {
                    tally(
                        "extract-zext",
                        exact_with_limb(
                            &extended.clone().extract(high, low),
                            &[("y", wy)],
                            groups,
                            64,
                        ),
                    );
                }
            }
        }
    }
    for (wa, wb, wc) in [(1, 2, 3), (3, 1, 2), (2, 2, 2), (4, 3, 1)] {
        let nested = E::var("a", wa)
            .concat(E::var("b", wb))
            .concat(E::var("c", wc));
        tally(
            "concat-right",
            exact_with_limb(&nested, &[("a", wa), ("b", wb), ("c", wc)], groups, 64),
        );
    }
    for wt in 3..=6u32 {
        let t = E::var("t", wt);
        for m in 1..wt {
            for low in 0..m {
                let head = t.clone().extract(wt - 1, m);
                let next = t.clone().extract(m - 1, low);
                let chain = head.concat(next.concat(E::var("r", 2)));
                tally(
                    "merge-adjacent",
                    exact_with_limb(&chain, &[("t", wt), ("r", 2)], groups, 64),
                );
            }
        }
    }
    for wx in 1..=3u32 {
        for wc in 1..=3u32 {
            let x = E::var("x", wx);
            let one = E::var("c", wc).concat(E::bv_const(0, wx));
            tally(
                "or-zext-chain",
                exact_with_limb(
                    &x.clone().zero_ext(wc).bvor(one.clone()),
                    &[("x", wx), ("c", wc)],
                    groups,
                    64,
                ),
            );
            tally(
                "or-zext-chain",
                exact_with_limb(
                    &one.bvor(x.clone().zero_ext(wc)),
                    &[("x", wx), ("c", wc)],
                    groups,
                    64,
                ),
            );
            let two = E::var("c", wc).concat(E::var("d", 2).concat(E::bv_const(0, wx)));
            tally(
                "or-zext-chain",
                exact_with_limb(
                    &x.clone().zero_ext(wc + 2).bvor(two),
                    &[("x", wx), ("c", wc), ("d", 2)],
                    groups,
                    64,
                ),
            );
            // Near misses: a tail that is no zero constant is not merged
            // (and whatever else rewrites the term keeps its value).
            let ones = E::var("c", wc).concat(E::bv_const(1, wx));
            let near = x.clone().zero_ext(wc).bvor(ones);
            let normal = normal::normalized_term(&near, groups).unwrap();
            assert!(
                matches!(normal, E::BvOr { .. }),
                "catnf merged a chain whose tail is not zero: {near} -> {normal}"
            );
            tally(
                "near-miss",
                exact_with_limb(&near, &[("x", wx), ("c", wc)], groups, 64).or(Some(0)),
            );
        }
    }
    let t = E::var("t", 6);
    let gap = t
        .clone()
        .extract(5, 4)
        .concat(t.clone().extract(2, 0).concat(E::var("r", 2)));
    let normal = normal::normalized_term(&gap, groups).unwrap();
    assert!(
        matches!(&normal, E::Concat { hi, .. } if matches!(hi.as_ref(), E::Extract { high: 5, low: 4, .. })),
        "catnf merged extracts that are not adjacent: {gap} -> {normal}"
    );
    eprintln!("SLICE22_CATNF (rewritten, inputs) {rewritten:?}");
    for rule in [
        "extract-concat",
        "extract-zext",
        "concat-right",
        "merge-adjacent",
        "or-zext-chain",
    ] {
        assert!(
            rewritten.get(rule).is_some_and(|(count, _)| *count > 0),
            "{rule} rewrote nothing: {rewritten:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The hostile review of slice 22 (2026-10-27): the module's own routine
// (OD-210) and three controls
// ---------------------------------------------------------------------------

/// How a review fixture's module binds `__udivti3`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Routine {
    /// `#[unsafe(no_mangle)] extern "C" fn __udivti3(a: u128, b: u128) ->
    /// u128 { 0 }`: the module's own routine, from which every division of
    /// the module returns 0.
    DefinedZero,
    /// `fn __udivti3(a: u128, b: u128) -> u128 { a / b }`: the routine
    /// divides at `I128`, which is a call of itself.
    Circular,
    /// `__udivti3` declared, not defined: the link binds it elsewhere.
    Declared,
}

/// The review's module: `__udivti3` as `routine` says, and `div(a: u128, b:
/// u128) -> u128 { if b == 0 { trap } a / b }` (`U128Div`'s shape).
pub(crate) fn routine_module(routine: Routine) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice22_routine");
    let signature = builder.add_func_type(vec![Ty::U128, Ty::U128], vec![Ty::U128]);
    if routine == Routine::Declared {
        builder.declare_function("__udivti3", signature);
    } else {
        let mut f = builder.function("__udivti3", signature);
        let entry = f.create_block();
        let a = f.add_block_param(entry, Ty::U128);
        let b = f.add_block_param(entry, Ty::U128);
        f.switch_to_block(entry);
        let value = match routine {
            Routine::Circular => f.binop(BinOp::UDiv, Ty::U128, a, b),
            _ => f.iconst(Ty::U128, 0),
        };
        f.ret(vec![value]);
        f.build();
    }
    let mut f = builder.function("div", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U128);
    let b = f.add_block_param(entry, Ty::U128);
    f.switch_to_block(entry);
    trap_if_zero(&mut f, Ty::U128, b);
    let q = f.binop(BinOp::UDiv, Ty::U128, a, b);
    f.ret(vec![q]);
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The pair of `name` in the review's `routine` module, and the module's
/// definitions.
pub(crate) fn routine_pair(
    routine: Routine,
    name: &str,
) -> (Function, X86ISelFunction, X86ModuleDefinitions) {
    let module = routine_module(routine);
    let source = translated(&module, name);
    let machine = select(&source, X86CallAbi::SystemV);
    (
        source,
        machine,
        X86ModuleDefinitions::of_trust_ir_module(&module),
    )
}

/// The refusal OD-210 gives a theorem that trusts `__udivti3`'s contract.
#[track_caller]
fn assert_routine_refused(
    what: &str,
    refusal: Result<SourceBoundX86Body<'_>, X86BodyRefusal>,
    expected: X86RoutineDefinition,
) {
    match refusal {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::TrustedRoutine {
            routine,
            definition,
        })) => {
            assert_eq!(routine, "__udivti3", "{what}");
            assert_eq!(definition, expected, "{what}");
        }
        Err(other) => panic!("{what}: refused otherwise: {other}"),
        Ok(owner) => panic!(
            "{what}: a theorem trusting {:?} was built",
            owner.trusted_routines().collect::<Vec<_>>()
        ),
    }
}

/// Every slice-22 fixture's module defines no runtime routine, so the
/// fixtures' owner ([`fixture_module`]) is the production owner in their real
/// module.
#[test]
fn the_fixture_modules_define_no_routine() {
    for shape in SLICE_TWENTY_TWO {
        let definitions = X86ModuleDefinitions::of_trust_ir_module(&slice22_module(shape));
        assert_eq!(definitions, X86ModuleDefinitions::default(), "{shape:?}");
        assert_eq!(
            definitions,
            fixture_module(&slice22_lir(shape)),
            "{shape:?}"
        );
    }
}

/// OD-210, the review's soundness finding. A module that defines `__udivti3`
/// (returning 0) and divides a `u128`: the division calls the module's own
/// routine, so every quotient is 0. Before OD-210 the body theorem was built
/// and holds (the call's result is one free input both sides share), and the
/// verifier credited every covered row Formal on the qualification pair
/// (`slice22_qualification::verifier_credits_no_row_whose_routine_the_module_defines`
/// replays it). Now no theorem is built: the module defines the routine
/// ([`X86RoutineDefinition::TheModule`]), or no module is named
/// ([`X86RoutineDefinition::Unnamed`]). A routine the module only declares
/// is bound elsewhere in the link and stays trusted, and a global so named
/// is a definition too.
#[test]
fn a_routine_the_module_defines_is_never_trusted() {
    let (source, machine, definitions) = routine_pair(Routine::DefinedZero, "div");
    assert!(definitions.defines("__udivti3"), "{definitions:?}");
    assert_eq!(
        call_rows(&machine)[0].1,
        "__udivti3",
        "{}",
        describe(&machine)
    );
    // What the owner stated before OD-210: a theorem that holds.
    let unchecked = build_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("before OD-210: {refusal}"));
    assert_eq!(
        unchecked.trusted_routines().collect::<Vec<_>>(),
        ["__udivti3"]
    );
    owner_holds(&unchecked).unwrap_or_else(|why| panic!("before OD-210: {why}"));
    assert_routine_refused(
        "the module's own __udivti3",
        source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&definitions)),
        X86RoutineDefinition::TheModule,
    );
    assert_routine_refused(
        "no module named",
        source_bound_x86_body(&source, &machine, SYSV),
        X86RoutineDefinition::Unnamed,
    );
    // Declared only: the theorem stands, and trusts the routine.
    let (source, machine, definitions) = routine_pair(Routine::Declared, "div");
    assert_eq!(definitions, X86ModuleDefinitions::default());
    let owner = source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&definitions))
        .unwrap_or_else(|refusal| panic!("a declared __udivti3: {refusal}"));
    assert_eq!(owner.trusted_routines().collect::<Vec<_>>(), ["__udivti3"]);
    owner_holds(&owner).unwrap();
    // A global named `__udivti3` defines the symbol the call binds to.
    let mut module = routine_module(Routine::Declared);
    module.globals.push(trust_ir::Global {
        name: "__udivti3".into(),
        ty: Ty::U128,
        mutable: false,
        initializer: Some(trust_ir::Constant::Int(0)),
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    assert!(X86ModuleDefinitions::of_trust_ir_module(&module).defines("__udivti3"));
    // Only the trusted routines are kept, by exact name (OD-217: the C memory
    // routines are trusted routines too).
    let kept = X86ModuleDefinitions::of_symbols(["memcpy", "__udivti3_", "_udivti3", "__modti3"]);
    assert!(kept.defines("__modti3") && !kept.defines("__udivti3") && kept.defines("memcpy"));
    assert!(
        !X86ModuleDefinitions::of_symbols(["_memcpy", "memcpy_", "bcmp", "memcmp"])
            .defines("memcpy")
    );
}

/// OD-216, residual 1 of OD-210: the module is one compile unit, and the
/// rustc bridge compiles a crate in codegen units, often each function alone
/// (a merge-ineligible function, a failed batch, `batch-cgu=0`). A crate's
/// `__udivti3` in a sibling unit binds the division's call unseen: with only
/// the module's definitions (it declares `__udivti3`) the theorem is built
/// and trusts the routine, as before OD-216. The compiler unions the
/// definitions the frontend names for its link unit
/// ([`X86ModuleDefinitions::with_link_unit`]), and the theorem is refused
/// ([`X86RoutineDefinition::TheLinkUnit`]). A routine the module defines
/// itself stays the module's ([`X86RoutineDefinition::TheModule`]); a link
/// unit that names no trusted routine changes nothing.
#[test]
fn a_routine_another_unit_of_the_crate_defines_is_never_trusted() {
    let (source, machine, definitions) = routine_pair(Routine::Declared, "div");
    assert_eq!(definitions, X86ModuleDefinitions::default());
    // The module alone: built, trusting the routine (what a sibling unit's
    // definition bound unseen before OD-216).
    let owner = source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&definitions))
        .unwrap_or_else(|refusal| panic!("the module alone: {refusal}"));
    assert_eq!(owner.trusted_routines().collect::<Vec<_>>(), ["__udivti3"]);
    owner_holds(&owner).unwrap();
    // The crate's other unit defines it.
    let crate_unit = definitions.clone().with_link_unit(["__udivti3", "main"]);
    assert!(crate_unit.defines("__udivti3"), "{crate_unit:?}");
    assert_ne!(crate_unit, definitions);
    assert_routine_refused(
        "a sibling unit's __udivti3",
        source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&crate_unit)),
        X86RoutineDefinition::TheLinkUnit,
    );
    // A link unit naming no trusted routine (or another one) is no reason.
    for names in [
        &["main", "__udivti3_", "udivti3"][..],
        &["__divti3", "memcpy"][..],
    ] {
        let other = definitions.clone().with_link_unit(names.iter().copied());
        assert!(
            source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&other)).is_ok(),
            "{names:?}"
        );
    }
    assert_eq!(
        definitions.clone().with_link_unit(["main", "__udivti3_"]),
        definitions
    );
    // The module's own definition stays the module's.
    let (source, machine, own) = routine_pair(Routine::DefinedZero, "div");
    assert_routine_refused(
        "the module's own __udivti3, named by the crate too",
        source_bound_x86_body_in_module(
            &source,
            &machine,
            SYSV,
            Some(&own.clone().with_link_unit(["__udivti3"])),
        ),
        X86RoutineDefinition::TheModule,
    );
    assert_eq!(own.clone().with_link_unit(["__udivti3"]), own);
}

/// OD-210, the circular case: a `__udivti3` whose body divides at `I128`
/// calls itself (the selector's routine call), and its theorem would assume
/// the contract of the very body under proof. Before OD-210 it was built and
/// holds; now it is refused whatever module is named
/// ([`X86RoutineDefinition::TheFunction`]). The module's `div` is refused
/// too ([`X86RoutineDefinition::TheModule`]).
#[test]
fn the_routine_never_divides_through_itself() {
    let (source, machine, definitions) = routine_pair(Routine::Circular, "__udivti3");
    assert_eq!(
        call_rows(&machine)[0].1,
        "__udivti3",
        "{}",
        describe(&machine)
    );
    let unchecked = build_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("before OD-210: {refusal}"));
    owner_holds(&unchecked).unwrap_or_else(|why| panic!("before OD-210: {why}"));
    for (what, module) in [
        ("its own module", Some(&definitions)),
        (
            "a module said to define nothing",
            Some(&X86ModuleDefinitions::default()),
        ),
        ("no module", None),
    ] {
        assert_routine_refused(
            what,
            source_bound_x86_body_in_module(&source, &machine, SYSV, module),
            X86RoutineDefinition::TheFunction,
        );
    }
    let (source, machine, definitions) = routine_pair(Routine::Circular, "div");
    assert_routine_refused(
        "div beside a circular __udivti3",
        source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&definitions)),
        X86RoutineDefinition::TheModule,
    );
}

/// `I128GuardConst` with its divisor's constant replaced by `Iconst128 { lo,
/// hi }`, and the selector's lowering of it.
fn guard_of_constant(lo: i64, hi: i64) -> (Function, X86ISelFunction) {
    let mut source = slice22_lir(Shape22::I128GuardConst);
    let divisor = source
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .find(|inst| matches!(inst.opcode, L::GuardDivZero { .. }))
        .map(|inst| inst.args[0])
        .expect("the fixture's guard");
    let definition = source
        .blocks
        .values_mut()
        .flat_map(|block| &mut block.instructions)
        .find(|inst| inst.results == [divisor])
        .expect("the divisor's definition");
    assert!(
        matches!(
            definition.opcode,
            L::Iconst128 { .. } | L::Iconst { ty: Type::I128, .. }
        ),
        "{:?}",
        definition.opcode
    );
    definition.opcode = L::Iconst128 { lo, hi };
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// The number of the owner's source definitions that are an `I128` guard's
/// stop.
fn guard_stops(owner: &SourceBoundX86Body<'_>, source: &Function) -> usize {
    owner
        .source_definitions()
        .iter()
        .filter(|(_, block, index)| {
            source
                .blocks
                .get(block)
                .and_then(|body| body.instructions.get(*index))
                .is_some_and(|inst| matches!(inst.opcode, L::GuardDivZero { .. }))
        })
        .count()
}

/// Whether a wrong lowering's theorem is refuted on samples (or the owner
/// names a mismatch); a theorem that holds is a credit.
#[track_caller]
fn refuted_or_mismatch(what: &str, source: &Function, machine: &X86ISelFunction) {
    match fixture_owner(source, machine) {
        Ok(owner) => {
            assert!(
                dag_refuted_on_samples(owner.obligation())
                    || (0..super::slice10::EDGE_SAMPLES)
                        .any(|seed| !super::slice10::holds_at_edge(owner.obligation(), seed)),
                "{what}: a wrong lowering's theorem holds on samples\n{}{}",
                describe(machine),
                text(owner.obligation())
            );
            eprintln!("SLICE22_REVIEW {what}: the theorem is refuted on samples");
        }
        Err(X86BodyRefusal::Mismatch(mismatch)) => {
            eprintln!("SLICE22_REVIEW {what}: a named mismatch: {mismatch}");
        }
        Err(other) => panic!("{what}: no claim, so this control proves nothing: {other}"),
    }
}

/// The review's control for the zero-constant test of the `I128` guard (`lo
/// | hi != 0` in the `GuardDivZero` arm). The guard of `Iconst128 { 0, 0 }`
/// fires on every run. With its trap dropped the machine calls the routine
/// where the source traps, which must be refuted (without the test the guard
/// "never fires" and the dropped trap's theorem holds, so it was credited);
/// the selector's lowering holds, and the guard is a stop.
#[test]
fn an_i128_guard_of_zero_with_its_trap_dropped_is_refuted() {
    let (source, machine) = guard_of_constant(0, 0);
    let trap = find(&machine, X86Opcode::TrapDivZeroExact);
    assert_eq!(trap.len(), 1, "{}", describe(&machine));
    let mut dropped = machine.clone();
    super::remove_at(&mut dropped, trap[0]);
    refuted_or_mismatch("the guard of 0 with its trap dropped", &source, &dropped);
    let zero = owner("guard of 0", &source, &machine);
    owner_holds(&zero).unwrap_or_else(|why| panic!("guard of 0: {why}"));
    assert_eq!(
        guard_stops(&zero, &source),
        1,
        "the guard of 0 is a stop\n{}",
        text(zero.obligation())
    );
}

/// The guard of `2^64` (`Iconst128 { 0, 1 }`: a high half only, no low half)
/// never fires: no stop, the selector's lowering holds, and a carrier that
/// reads the low half alone (it traps on every run) is refuted.
#[test]
fn an_i128_guard_of_a_high_half_only_never_fires() {
    let (source, machine) = guard_of_constant(0, 1);
    let high = owner("guard of 2^64", &source, &machine);
    assert_eq!(
        guard_stops(&high, &source),
        0,
        "the guard of 2^64 never fires\n{}",
        text(high.obligation())
    );
    owner_holds(&high).unwrap_or_else(|why| panic!("guard of 2^64: {why}"));
    let trap = find(&machine, X86Opcode::TrapDivZeroExact);
    assert_eq!(trap.len(), 1, "{}", describe(&machine));
    let or = trap[0] - 1;
    assert_eq!(
        inst(&machine, or).opcode,
        X86Opcode::OrRR,
        "{}",
        describe(&machine)
    );
    let mut low_only = machine.clone();
    let low = inst(&low_only, or).operands[1].clone();
    inst_mut(&mut low_only, or).operands[2] = low;
    refuted_or_mismatch("the guard of 2^64 on its low half", &source, &low_only);
}

/// The review's controls for two checks of `catnf` (OD-204) the exhaustive
/// sweep let a mutant through, each as near misses exact on every input:
///
/// - the merge reads ONE term: `(concat t[h:m] (concat u[m-1:l] r))` keeps
///   both extracts (without the same-term check it is `(concat t[h:l] r)`,
///   wrong at `t = 0, u = 1`);
/// - only a ZERO extension's bits are moved: an extract across a sign
///   extension's boundary is no zero extension (`extract[3:1](sext_2 y)` at
///   `y = 0b10` is `0b111`, not `0b001`), and the `bvor` of a sign extension
///   and a chain ending in zeros is no chain.
///
/// Each under `catnf` alone (no other rule reaches the term first), the
/// test's groups and the canonical ones.
#[test]
fn catnf_moves_only_bits_of_one_term_and_of_zero_extensions() {
    let sets = [
        ("catnf", Groups::CATNF),
        (
            "ext+fold+arith+catnf",
            Groups::EXT
                .with(Groups::FOLD)
                .with(Groups::ARITH)
                .with(Groups::CATNF),
        ),
        ("canonical", Groups::CANONICAL),
    ];
    let mentions = |expr: &E, name: &str| expr.free_vars().iter().any(|var| var == name);
    for (label, groups) in sets {
        // Two terms of one width, adjacent bit ranges.
        for wt in 2..=4u32 {
            let (t, u) = (E::var("t", wt), E::var("u", wt));
            for m in 1..wt {
                for low in 0..m {
                    let chain = t
                        .clone()
                        .extract(wt - 1, m)
                        .concat(u.clone().extract(m - 1, low).concat(E::var("r", 2)));
                    let normal = normal::normalized_term_with_limb(&chain, groups, 64).unwrap();
                    assert!(
                        mentions(&normal, "u"),
                        "{label}: catnf merged extracts of two terms: {chain} -> {normal}"
                    );
                    exact_with_limb(&chain, &[("t", wt), ("u", wt), ("r", 2)], groups, 64);
                }
            }
        }
        // An extract across a sign extension's boundary.
        for wy in 1..=3u32 {
            for k in 1..=3u32 {
                let extended = E::var("y", wy).sign_ext(k);
                for low in 0..wy {
                    for high in wy..wy + k {
                        let term = extended.clone().extract(high, low);
                        let normal = normal::normalized_term_with_limb(&term, groups, 64).unwrap();
                        assert!(
                            !has_node(&normal, &|node| matches!(node, E::ZeroExtend { .. })),
                            "{label}: catnf read a sign extension as a zero extension: \
                             {term} -> {normal}"
                        );
                        exact_with_limb(&term, &[("y", wy)], groups, 64);
                    }
                }
            }
        }
        // The `bvor` of a sign extension and a chain ending in zeros.
        for wx in 1..=3u32 {
            for wc in 1..=3u32 {
                let x = E::var("x", wx).sign_ext(wc);
                let chain = E::var("c", wc).concat(E::bv_const(0, wx));
                for term in [x.clone().bvor(chain.clone()), chain.bvor(x)] {
                    let normal = normal::normalized_term_with_limb(&term, groups, 64).unwrap();
                    assert!(
                        has_node(&normal, &|node| matches!(node, E::BvOr { .. })),
                        "{label}: catnf merged a sign extension into a chain: {term} -> {normal}"
                    );
                    exact_with_limb(&term, &[("x", wx), ("c", wc)], groups, 64);
                }
            }
        }
    }
}
