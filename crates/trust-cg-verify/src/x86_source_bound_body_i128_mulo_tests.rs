// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The x86-64 body theorem of the division-free 128-bit checked multiply
//! (ruling OD-224). The adapter expands `Inst::Overflow { MulOverflow, U128 |
//! I128 }` on x86-64 into the value `Imul` and a limb check of two `I64`
//! `CheckedUmul`s, a carry compare and a both-high-limbs test (the signed form
//! runs it on the magnitudes and adds a sign check), so the theorem states two
//! flag-setting `mul` rows and the compares where slice 22 stated a call of
//! `__udivti3` / `__divti3` (OD-202's routine contract).
//!
//! Fixtures are real: LIR from the trust-ir adapter (translated with an
//! explicit `Permit` for x86-64), the machine stream from the real x86-64
//! instruction selector (`super::select`). Every test here runs without a
//! solver (the `x86_source_bound_body::tests::i128_mulo::` library gate); the
//! replay on AY and Clean is in `i128_mulo_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::slice22::{Shape22, fixture_owner, slice22_pair};
use super::*;
use trust_cg_ir::X86CondCode;
use trust_ir::{ICmpOp, OverflowOp};

/// The OD-224 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MuloShape {
    /// Slice 22's `U128CheckedMul`: `fn(a: u128, b: u128) -> bool {
    /// a.checked_mul(b).is_none() }`.
    U128Flag,
    /// Slice 22's `I128OverflowingMul`: the signed flag returned, the product
    /// stored through a pointer.
    I128OverflowingMul,
    /// `fn(a: u128, b: u128) -> u128 { a.saturating_mul(b) }`: `o ? MAX : p`.
    U128SaturatingMul,
    /// `fn(a: i128, b: i128) -> i128 { a.saturating_mul(b) }`: `o ? ((a ^ b)
    /// < 0 ? MIN : MAX) : p`, as `i128::saturating_mul` reads.
    I128SaturatingMul,
    /// `fn(a: u128) -> bool { a.checked_mul(10^16).is_none() }`: a constant
    /// operand (`div_rem_1e16`'s `quot * 10^16`), the compare with the
    /// constant's limit.
    U128ConstFlag,
}

/// Every OD-224 fixture shape.
pub(crate) const MULO_SHAPES: [MuloShape; 5] = [
    MuloShape::U128Flag,
    MuloShape::I128OverflowingMul,
    MuloShape::U128SaturatingMul,
    MuloShape::I128SaturatingMul,
    MuloShape::U128ConstFlag,
];

/// `10^16`, `div_rem_1e16`'s multiplier.
const TEN_TO_THE_16: u128 = 10_000_000_000_000_000;

impl MuloShape {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::U128Flag => "mulo_u128_flag",
            Self::I128OverflowingMul => "mulo_i128_overflowing_mul",
            Self::U128SaturatingMul => "mulo_u128_saturating_mul",
            Self::I128SaturatingMul => "mulo_i128_saturating_mul",
            Self::U128ConstFlag => "mulo_u128_const_flag",
        }
    }

    /// The `mul` rows of the shape's selection: the value's low limb product,
    /// and each `CheckedUmul` of the limb check (none for a constant
    /// operand, whose flag is one compare).
    fn muls(self) -> usize {
        if self == Self::U128ConstFlag { 1 } else { 3 }
    }

    fn signed(self) -> bool {
        matches!(self, Self::I128OverflowingMul | Self::I128SaturatingMul)
    }
}

/// The trust-ir module of a saturating or constant-operand fixture.
fn saturating_module(shape: MuloShape) -> trust_ir::Module {
    let ty = if shape.signed() { Ty::I128 } else { Ty::U128 };
    let mut builder = ModuleBuilder::new("x86_source_bound_body_i128_mulo");
    if shape == MuloShape::U128ConstFlag {
        let signature = builder.add_func_type(vec![Ty::U128], vec![Ty::Bool]);
        let mut f = builder.function(shape.name(), signature);
        let entry = f.create_block();
        let a = f.add_block_param(entry, Ty::U128);
        f.switch_to_block(entry);
        let c = f.uconst(Ty::U128, TEN_TO_THE_16);
        let (_, overflow) = f.overflow(OverflowOp::MulOverflow, Ty::U128, a, c);
        f.ret(vec![overflow]);
        f.build();
        return builder.build().expect("ModuleBuilder::build: test fixture");
    }
    let signature = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, ty.clone());
    let b = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let (product, overflow) = f.overflow(OverflowOp::MulOverflow, ty.clone(), a, b);
    let saturated = if shape.signed() {
        let sign = f.binop(BinOp::Xor, ty.clone(), a, b);
        let zero = f.iconst(ty.clone(), 0);
        let negative = f.icmp(ICmpOp::Slt, ty.clone(), sign, zero);
        let min = f.iconst(ty.clone(), i128::MIN);
        let max = f.iconst(ty.clone(), i128::MAX);
        f.select(ty.clone(), negative, min, max)
    } else {
        f.uconst(ty.clone(), u128::MAX)
    };
    let result = f.select(ty, overflow, saturated, product);
    f.ret(vec![result]);
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The LIR and the x86-64 selection of `shape`.
pub(crate) fn mulo_pair(shape: MuloShape) -> (Function, X86ISelFunction) {
    match shape {
        MuloShape::U128Flag => slice22_pair(Shape22::U128CheckedMul),
        MuloShape::I128OverflowingMul => slice22_pair(Shape22::I128OverflowingMul),
        MuloShape::U128SaturatingMul | MuloShape::I128SaturatingMul | MuloShape::U128ConstFlag => {
            let module = saturating_module(shape);
            let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &module,
                trust_cg_lower::GuardCarrierArch::X86_64,
                trust_cg_lower::TlsDialect::default(),
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
            .into_iter()
            .map(|(function, _)| function)
            .find(|function| function.name == shape.name())
            .unwrap_or_else(|| panic!("{shape:?}: no translated function"));
            let machine = select(&source, X86CallAbi::SystemV);
            (source, machine)
        }
    }
}

/// The theorem's query as the replay renders it.
fn text(obligation: &ProofObligation) -> String {
    generate_smt2_query_raw(obligation, &replay_config())
}

/// The symbol of every `call` row, in walk order.
fn called(machine: &X86ISelFunction) -> Vec<String> {
    find(machine, X86Opcode::Call)
        .into_iter()
        .map(|ordinal| match inst(machine, ordinal).operands.first() {
            Some(O::Symbol(symbol)) => symbol.clone(),
            other => panic!("call row {ordinal}: {other:?}"),
        })
        .collect()
}

/// The condition of a `setcc` row.
fn setcc_condition(machine: &X86ISelFunction, ordinal: usize) -> Option<X86CondCode> {
    let row = inst(machine, ordinal);
    (row.opcode == X86Opcode::Setcc).then(|| match row.operands.get(1) {
        Some(O::CondCode(cc)) => *cc,
        other => panic!("setcc row {ordinal}: {other:?}"),
    })
}

/// The `setb` of the core's carry compare (`p1 <u t`): the one `setb`
/// directly after a register `cmp` (each `CheckedUmul`'s `setb` follows its
/// `mul` and a move).
fn carry_setb(machine: &X86ISelFunction) -> usize {
    let hits: Vec<usize> = find(machine, X86Opcode::Setcc)
        .into_iter()
        .filter(|&ordinal| {
            setcc_condition(machine, ordinal) == Some(X86CondCode::B)
                && ordinal > 0
                && inst(machine, ordinal - 1).opcode == X86Opcode::CmpRR
        })
        .collect();
    let [only] = hits[..] else {
        panic!(
            "expected one carry setb, found {hits:?}\n{}",
            describe(machine)
        )
    };
    only
}

/// The `or` rows of the core's flag, in order: `o1 | o2`, `| c`, `| both`
/// (the last three of the unsigned fixture, which ends with the core).
fn core_ors(machine: &X86ISelFunction) -> [usize; 3] {
    let ors = find(machine, X86Opcode::OrRR);
    let [.., f1, f2, flag] = ors[..] else {
        panic!("three or rows\n{}", describe(machine))
    };
    [f1, f2, flag]
}

/// Wrong lowerings of the division-free check, each one edit of the
/// selector's real stream: the theorem builds and is refuted.
pub(crate) fn division_free_wrong_lowerings() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // The carry dropped: `f2 = f1 | f1`.
    {
        let (source, mut machine) = mulo_pair(MuloShape::U128Flag);
        let [_, f2, _] = core_ors(&machine);
        let f1 = inst(&machine, f2).operands[1].clone();
        inst_mut(&mut machine, f2).operands[2] = f1;
        cases.push(("mulo/carry-dropped", source, machine));
    }
    // The carry compared signed: `setl` for the carry's `setb`.
    {
        let (source, mut machine) = mulo_pair(MuloShape::U128Flag);
        let setb = carry_setb(&machine);
        inst_mut(&mut machine, setb).operands[1] = O::CondCode(X86CondCode::L);
        cases.push(("mulo/carry-compared-signed", source, machine));
    }
    // The both-high-limbs test dropped: `flag = f2 | f2`.
    {
        let (source, mut machine) = mulo_pair(MuloShape::U128Flag);
        let [_, _, flag] = core_ors(&machine);
        let f2 = inst(&machine, flag).operands[1].clone();
        inst_mut(&mut machine, flag).operands[2] = f2;
        cases.push(("mulo/both-high-dropped", source, machine));
    }
    // A cross product's high-half test dropped: `f1 = o2 | o2`.
    {
        let (source, mut machine) = mulo_pair(MuloShape::U128Flag);
        let [f1, _, _] = core_ors(&machine);
        let o2 = inst(&machine, f1).operands[2].clone();
        inst_mut(&mut machine, f1).operands[1] = o2;
        cases.push(("mulo/cross-overflow-dropped", source, machine));
    }
    // Signed/unsigned swapped: `a`'s sign mask shifted logically (`shr` for
    // the first `sar` by 63), so a negative `a`'s mask is 1, not all ones.
    {
        let (source, mut machine) = mulo_pair(MuloShape::I128OverflowingMul);
        let sar = find(&machine, X86Opcode::SarRI)[0];
        inst_mut(&mut machine, sar).opcode = X86Opcode::ShrRI;
        cases.push(("mulo/sign-mask-logical", source, machine));
    }
    // The constant's limit off by one: its low half's `mov` one more.
    {
        let (source, mut machine) = mulo_pair(MuloShape::U128ConstFlag);
        let limit = u128::MAX / TEN_TO_THE_16;
        let low = find(&machine, X86Opcode::MovRI)
            .into_iter()
            .find(|&ordinal| {
                matches!(inst(&machine, ordinal).operands[1], O::Imm(imm) if imm == limit as u64 as i64)
            })
            .unwrap_or_else(|| panic!("the limit's low half\n{}", describe(&machine)));
        inst_mut(&mut machine, low).operands[1] = O::Imm((limit as u64 as i64).wrapping_add(1));
        cases.push(("mulo/const-limit-off-by-one", source, machine));
    }
    cases
}

/// Every OD-224 fixture builds a theorem that holds on samples, calls no
/// runtime routine, and states no division; its flag is computed by three
/// `mul` rows (the value's low limb product and the two cross products'
/// `CheckedUmul`), each signed fixture's on the magnitudes, or, for a constant
/// operand, by one compare with the constant's limit.
#[test]
fn every_division_free_checked_multiply_builds_a_theorem_that_holds() {
    for shape in MULO_SHAPES {
        let (source, machine) = mulo_pair(shape);
        let owner = fixture_owner(&source, &machine).unwrap_or_else(|refusal| {
            panic!(
                "{shape:?}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        let holds = if owner.is_stated_in_parts() {
            super::slice16::parts_hold(&owner).is_ok()
        } else {
            dag_holds_on_samples(owner.obligation())
        };
        assert!(
            holds,
            "{shape:?}: the theorem is refuted on samples\n{}{}",
            describe(&machine),
            text(owner.obligation())
        );
        assert_eq!(called(&machine), Vec::<String>::new(), "{shape:?}");
        assert_eq!(
            find(&machine, X86Opcode::Mul).len(),
            shape.muls(),
            "{shape:?}\n{}",
            describe(&machine)
        );
        let query = text(owner.obligation());
        for division in ["bvudiv", "bvsdiv", "bvurem", "bvsrem"] {
            assert!(
                !query.contains(&format!("({division} ")),
                "{shape:?}: the theorem states a division"
            );
        }
        eprintln!(
            "I128_MULO_SHAPE {shape:?}: stated, {} machine rows, {} bytes",
            super::rows(&machine).len(),
            query.len()
        );
    }
}

/// FAILS BEFORE: the same trust-ir, translated in the division form OD-224
/// replaced (`with_x86_i128_mulo_division_form`), selects a `call` of
/// `__udivti3` / `__divti3` on x86-64; in the default form it calls nothing.
#[test]
fn the_division_form_called_the_routine_and_the_limb_check_does_not() {
    for (shape, routine) in [
        (MuloShape::U128Flag, "__udivti3"),
        (MuloShape::I128OverflowingMul, "__divti3"),
        (MuloShape::U128SaturatingMul, "__udivti3"),
        (MuloShape::I128SaturatingMul, "__divti3"),
        (MuloShape::U128ConstFlag, "__udivti3"),
    ] {
        let (_, old) = trust_cg_lower::with_x86_i128_mulo_division_form(true, || mulo_pair(shape));
        assert_eq!(called(&old), [routine], "{shape:?} in the division form");
        let (_, new) = mulo_pair(shape);
        assert_eq!(called(&new), Vec::<String>::new(), "{shape:?}");
    }
    for shape in [
        Shape22::U128CheckedMulSmall,
        Shape22::U128CheckedMul,
        Shape22::I128OverflowingMul,
        Shape22::U128MulAcrossCut,
        Shape22::U128MulZextOperand,
    ] {
        assert!(shape.checks_a_multiply());
        let (_, old) =
            trust_cg_lower::with_x86_i128_mulo_division_form(true, || slice22_pair(shape));
        assert_eq!(
            called(&old),
            shape.calls_in_the_division_form(),
            "{shape:?} in the division form"
        );
        let (_, new) = slice22_pair(shape);
        assert_eq!(called(&new), shape.calls(), "{shape:?}");
    }
}

/// Every wrong lowering of the division-free check builds a theorem that is
/// refuted on samples, and the production verifier never credits it.
#[test]
fn every_division_free_wrong_lowering_is_refuted() {
    for (label, source, machine) in division_free_wrong_lowerings() {
        let owner = fixture_owner(&source, &machine).unwrap_or_else(|refusal| {
            panic!(
                "{label}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        let refuted = dag_refuted_on_samples(owner.obligation())
            || (0..super::slice10::EDGE_SAMPLES)
                .any(|seed| !super::slice10::holds_at_edge(owner.obligation(), seed));
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

/// The OD-224 theorems are a function of the pair: built twice, they are the
/// same text.
#[test]
fn the_division_free_theorems_are_deterministic() {
    for shape in MULO_SHAPES {
        let (source, machine) = mulo_pair(shape);
        let first = text(
            fixture_owner(&source, &machine)
                .expect("first")
                .obligation(),
        );
        let (source, machine) = mulo_pair(shape);
        let second = text(
            fixture_owner(&source, &machine)
                .expect("second")
                .obligation(),
        );
        assert_eq!(first, second, "{shape:?}");
    }
}

/// A diagnostic, not a check: every OD-224 fixture's LIR, machine rows and
/// theorem, and every wrong lowering's machine rows.
#[test]
#[ignore]
fn print_i128_mulo_fixtures() {
    for shape in MULO_SHAPES {
        let (source, machine) = mulo_pair(shape);
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match fixture_owner(&source, &machine) {
            Ok(owner) => println!("{}", text(owner.obligation())),
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
    for (label, _, machine) in division_free_wrong_lowerings() {
        println!("==== {label} (wrong lowering)\n{}", describe(&machine));
    }
}
