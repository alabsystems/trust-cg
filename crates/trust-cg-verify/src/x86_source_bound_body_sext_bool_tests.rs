// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The sign extension of a `bool` in the x86-64 source-bound body theorem
//! (ruling OD-BODY-SEXT-BOOL-20261016): LIR `Sextend { from_ty: B1, to_ty }`
//! is trust-ir's `SExt` of a `Bool`, which makes `true` all ones at every
//! width (the reference interpreter widens `as_signed()` of the 1-bit value),
//! and the selector's rows for it are `-zext(b)`: the zero extension of the
//! bool's low byte (`movzx`, or the 32-bit copy of a System V parameter's
//! entry `movzx`), then `neg` at the destination carrier's width; an `I128`'s
//! high half is the sign fill (`mov; sar 63`) of that low half.
//!
//! Until 2026-10-16 the selector emitted a `movsx` of the 0/1 byte, +1 for
//! `true` (`(1, 0)` for an `I128`), and the owner kept the cast outside its
//! domain; that lowering is now the first wrong-lowering control of every
//! shape, refuted here on samples and, in `sext_bool_qualification`, with an
//! AY counterexample.
//!
//! Fixtures are real: LIR from the trust-ir adapter and the machine stream
//! from the real x86-64 instruction selector (`super::select`). Every test
//! here runs without a solver (the
//! `x86_source_bound_body::tests::sext_bool::` library gate).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice11::{eval_word, evaluate_premises, theorem_holds, theorem_refuted};
use super::*;

/// The sign-extension fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SextBoolShape {
    /// `fn(b: bool) -> i8 { sext(b) }` (the adapter then widens the `i8`
    /// return with its own `movsx`).
    BoolI8,
    /// `fn(b: bool) -> i16 { sext(b) }`.
    BoolI16,
    /// `fn(b: bool) -> i32 { sext(b) }`.
    BoolI32,
    /// `fn(b: bool) -> i64 { sext(b) }`.
    BoolI64,
    /// `fn(b: bool) -> i128 { sext(b) }`: RAX and RDX.
    BoolI128,
    /// `fn(a: i64, b: i64) -> i64 { sext(a < b) }`: of a compare's result.
    LessI64,
    /// `fn(x: i32) -> i32 { x ^ sext(x < 0) }`: the branchless `x < 0 ? !x
    /// : x` (gcc-c-torture pr68376-2).
    FlipIfNegative,
}

/// Every shape; each builds a theorem that holds
/// ([`every_bool_sign_extension_fixture_is_qualified`]).
pub(crate) const SEXT_BOOL: [SextBoolShape; 7] = [
    SextBoolShape::BoolI8,
    SextBoolShape::BoolI16,
    SextBoolShape::BoolI32,
    SextBoolShape::BoolI64,
    SextBoolShape::BoolI128,
    SextBoolShape::LessI64,
    SextBoolShape::FlipIfNegative,
];

impl SextBoolShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("sext_bool_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }

    /// The cast's destination.
    fn to_ty(self) -> Type {
        use SextBoolShape::*;
        match self {
            BoolI8 => Type::I8,
            BoolI16 => Type::I16,
            BoolI32 | FlipIfNegative => Type::I32,
            BoolI64 | LessI64 => Type::I64,
            BoolI128 => Type::I128,
        }
    }

    /// The function's result for the argument registers `rdi` and `rsi`, at
    /// 128 bits (only the returned width is observed): trust-ir's meaning,
    /// with `true` widened to all ones.
    fn expected(self, rdi: u64, rsi: u64) -> u128 {
        use SextBoolShape::*;
        let all_ones = |b: bool| if b { u128::MAX } else { 0 };
        match self {
            BoolI8 | BoolI16 | BoolI32 | BoolI64 | BoolI128 => all_ones(rdi & 1 == 1),
            LessI64 => all_ones((rdi as i64) < (rsi as i64)),
            FlipIfNegative => {
                let x = rdi as u32 as i32;
                u128::from((x ^ if x < 0 { -1 } else { 0 }) as u32)
            }
        }
    }
}

/// The LIR the trust-ir adapter produces for `shape`.
pub(crate) fn sext_bool_lir(shape: SextBoolShape) -> Function {
    use SextBoolShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_sext_bool");
    let (params, result) = match shape {
        BoolI8 => (vec![Ty::Bool], Ty::I8),
        BoolI16 => (vec![Ty::Bool], Ty::I16),
        BoolI32 => (vec![Ty::Bool], Ty::I32),
        BoolI64 => (vec![Ty::Bool], Ty::I64),
        BoolI128 => (vec![Ty::Bool], Ty::I128),
        LessI64 => (vec![Ty::I64, Ty::I64], Ty::I64),
        FlipIfNegative => (vec![Ty::I32], Ty::I32),
    };
    let signature = builder.add_func_type(params.clone(), vec![result.clone()]);
    let name = shape.name();
    let mut f = builder.function(name.clone(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let value = match shape {
        BoolI8 | BoolI16 | BoolI32 | BoolI64 | BoolI128 => f.sext(Ty::Bool, result, args[0]),
        LessI64 => {
            let less = f.icmp(trust_ir::ICmpOp::Slt, Ty::I64, args[0], args[1]);
            f.sext(Ty::Bool, Ty::I64, less)
        }
        FlipIfNegative => {
            let zero = f.iconst(Ty::I32, 0);
            let negative = f.icmp(trust_ir::ICmpOp::Slt, Ty::I32, args[0], zero);
            let mask = f.sext(Ty::Bool, Ty::I32, negative);
            f.binop(BinOp::Xor, Ty::I32, args[0], mask)
        }
    };
    f.ret(vec![value]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
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

/// `shape`'s LIR and its System V selection.
pub(crate) fn sext_bool_pair(shape: SextBoolShape) -> (Function, X86ISelFunction) {
    let source = sext_bool_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

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

/// The `neg` of the cast (the shape's one `neg` row).
fn negation(machine: &X86ISelFunction) -> usize {
    let negs = find(machine, X86Opcode::Neg);
    assert_eq!(negs.len(), 1, "one neg\n{}", describe(machine));
    negs[0]
}

/// The zero extension the `neg` reads: the row defining its source.
fn zero_extension(machine: &X86ISelFunction) -> usize {
    let neg = negation(machine);
    let read = inst(machine, neg).operands[1].clone();
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .rfind(|row| *row < neg && inst(machine, *row).operands.first() == Some(&read))
        .expect("the zero extension the neg reads")
}

// ---------------------------------------------------------------------------
// Fixtures and the theorem (no solver)
// ---------------------------------------------------------------------------

/// Each shape's LIR holds exactly one `Sextend` from `B1`, and its selection
/// is `-zext(b)`: a `movzx` (or the 32-bit copy of a parameter's entry
/// `movzx`) of the bool, then `neg` at the destination carrier's width, and
/// for an `I128` the `mov; sar 63` sign fill of that low half. No `movsx`
/// reads the bool.
#[test]
fn bool_sign_extension_fixtures_have_the_expected_lir_and_pre_ra_shapes() {
    for shape in SEXT_BOOL {
        let (source, machine) = sext_bool_pair(shape);
        let extensions: Vec<&Instruction> = source
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .filter(|inst| {
                matches!(
                    inst.opcode,
                    L::Sextend {
                        from_ty: Type::B1,
                        ..
                    }
                )
            })
            .collect();
        assert_eq!(extensions.len(), 1, "{shape:?}\n{}", describe_lir(&source));
        assert_eq!(
            extensions[0].opcode,
            L::Sextend {
                from_ty: Type::B1,
                to_ty: shape.to_ty(),
            },
            "{shape:?}"
        );
        let neg = negation(&machine);
        let extension = zero_extension(&machine);
        let parameter = matches!(
            shape,
            SextBoolShape::BoolI8
                | SextBoolShape::BoolI16
                | SextBoolShape::BoolI32
                | SextBoolShape::BoolI64
                | SextBoolShape::BoolI128
        );
        assert_eq!(
            inst(&machine, extension).opcode,
            if parameter {
                X86Opcode::MovRR32
            } else {
                X86Opcode::Movzx
            },
            "{shape:?}\n{}",
            describe(&machine)
        );
        let class = |operand: &O| match operand {
            O::VReg(vreg) => vreg.class,
            other => panic!("{shape:?}: not a register: {other:?}"),
        };
        let wide = matches!(shape.to_ty(), Type::I64 | Type::I128);
        assert_eq!(
            class(&inst(&machine, neg).operands[0]),
            if wide {
                RegClass::Gpr64
            } else {
                RegClass::Gpr32
            },
            "{shape:?}"
        );
        let bool_reg = inst(&machine, extension).operands[1].clone();
        assert!(
            !find(&machine, X86Opcode::MovsxB)
                .into_iter()
                .any(|row| inst(&machine, row).operands[1] == bool_reg),
            "{shape:?}: no movsx of the bool\n{}",
            describe(&machine)
        );
        if shape == SextBoolShape::BoolI128 {
            let sar = find(&machine, X86Opcode::SarRI);
            assert_eq!(sar.len(), 1, "{}", describe(&machine));
            assert_eq!(inst(&machine, sar[0]).operands[2], O::Imm(63));
        }
    }
}

#[test]
fn owner_builds_for_every_bool_sign_extension_and_covers_every_value_row() {
    for shape in SEXT_BOOL {
        let (source, machine) = sext_bool_pair(shape);
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
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
                !opcode.is_pseudo() && !matches!(opcode, X86Opcode::Jmp | X86Opcode::Ret)
            })
            .map(|(ordinal, _, _)| ordinal)
            .collect();
        assert_eq!(
            body.bound_rows(),
            expected,
            "{shape:?}\n{}",
            describe(&machine)
        );
        assert!(body.covers(negation(&machine)), "{shape:?}");
        assert!(body.covers(zero_extension(&machine)), "{shape:?}");
        let entries = free_inputs_of(body.obligation());
        assert_eq!(
            owner_check(&source, &machine, body.obligation(), &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(body.obligation().is_genuinely_proven(), "{shape:?}");
    }
}

#[test]
fn bool_sign_extension_theorems_hold_on_samples() {
    for shape in SEXT_BOOL {
        let (source, machine) = sext_bool_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The owner, credit and host-qualification tests run over [`SEXT_BOOL`]:
/// every shape's real selection builds a theorem that holds.
#[test]
fn every_bool_sign_extension_fixture_is_qualified() {
    use SextBoolShape::*;
    for shape in SEXT_BOOL {
        // Exhaustive: a new shape does not compile until it is listed here.
        match shape {
            BoolI8 | BoolI16 | BoolI32 | BoolI64 | BoolI128 | LessI64 | FlipIfNegative => {}
        }
        let (source, machine) = sext_bool_pair(shape);
        assert!(
            source_bound_x86_body(&source, &machine, SYSV)
                .is_ok_and(|owner| theorem_holds(owner.obligation())),
            "{shape:?}"
        );
    }
}

/// The theorem's source side IS trust-ir's sign extension, `true` all ones
/// at the returned width, at concrete arguments: a `bool` argument register
/// with bits 1..7 clear and bits 8..63 `0xA5` (all System V defines), and
/// edge values of the compared and flipped integers. The machine side agrees
/// at each.
#[test]
fn the_source_side_makes_true_all_ones_at_every_width() {
    let dirty = 0xa5a5_a5a5_a5a5_a500_u64;
    let words = [
        0,
        1,
        u64::MAX,
        u64::MAX - 1,
        i64::MAX as u64,
        i64::MIN as u64,
        0x8000_0000,
        0x7fff_ffff,
        dirty,
    ];
    for shape in SEXT_BOOL {
        let (source, machine) = sext_bool_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        let items = observable_items(&obligation);
        let arguments: Vec<(u64, u64)> = match shape {
            SextBoolShape::LessI64 => words
                .iter()
                .flat_map(|&a| words.iter().map(move |&b| (a, b)))
                .collect(),
            SextBoolShape::FlipIfNegative => words.iter().map(|&x| (x, dirty)).collect(),
            _ => vec![(0, dirty), (1, dirty), (dirty, dirty), (dirty | 1, dirty)],
        };
        for (rdi, rsi) in arguments {
            let fixed = [("e_rdi", rdi), ("e_rsi", rsi)];
            let premises = evaluate_premises(&obligation, &fixed);
            let want = shape.expected(rdi, rsi);
            let mut got = 0u128;
            let mut shift = 0;
            for (source_side, machine_side) in &items {
                let width = source_side.bv_width();
                let value = eval_word(source_side, &premises);
                assert_eq!(
                    value,
                    eval_word(machine_side, &premises),
                    "{shape:?} rdi={rdi:#x} rsi={rsi:#x}: the sides differ"
                );
                got |= u128::from(value) << shift;
                shift += width;
            }
            let mask = if shift >= 128 {
                u128::MAX
            } else {
                (1u128 << shift) - 1
            };
            assert_eq!(
                got,
                want & mask,
                "{shape:?} rdi={rdi:#x} rsi={rsi:#x} ({shift} observed bits)"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Wrong lowerings (no solver here; AY counterexamples in
// `sext_bool_qualification`)
// ---------------------------------------------------------------------------

/// Wrong lowerings of real selections, each bound by the owner: the old
/// `movsx` of the 0/1 byte (+1 for `true`) at every shape, a `not` for the
/// `neg`, the extension of the bool's bit 1, and an `I128` high half that is
/// the logical (not the arithmetic) shift of the low half.
pub(crate) fn sext_bool_refutations() -> Vec<(String, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    for shape in SEXT_BOOL {
        // The lowering the selector emitted before 2026-10-16: `movsx d, b`
        // of the bool's register, where `neg d, t` stands.
        let (source, mut machine) = sext_bool_pair(shape);
        let neg = negation(&machine);
        let extension = zero_extension(&machine);
        let bool_reg = inst(&machine, extension).operands[1].clone();
        let row = inst_mut(&mut machine, neg);
        row.opcode = X86Opcode::MovsxB;
        row.operands[1] = bool_reg;
        cases.push((format!("{shape:?}/movsx-of-the-byte"), source, machine));
        // `not` for `neg`: `false` all ones and `true` all ones but bit 0.
        let (source, mut machine) = sext_bool_pair(shape);
        let neg = negation(&machine);
        inst_mut(&mut machine, neg).opcode = X86Opcode::Not;
        cases.push((format!("{shape:?}/not-instead-of-neg"), source, machine));
    }
    // The extension of bit 1 of the bool (always 0) instead of bit 0.
    let (source, mut machine) = sext_bool_pair(SextBoolShape::LessI64);
    let extension = zero_extension(&machine);
    let bool_reg = inst(&machine, extension).operands[1].clone();
    let shifted = O::VReg(VReg::new(machine.next_vreg + 10, RegClass::Gpr32));
    let (_, block, index) = rows(&machine)[extension];
    let body = &mut machine.blocks.get_mut(&block).unwrap().insts;
    body.insert(
        index,
        X86ISelInst::new(X86Opcode::ShrRI, vec![shifted.clone(), bool_reg, O::Imm(1)]),
    );
    body[index + 1].operands[1] = shifted;
    cases.push(("LessI64/bit-1-extended".to_string(), source, machine));
    // An `I128` high half shifted in with zeros: `(-1, 1)` for `true`.
    let (source, mut machine) = sext_bool_pair(SextBoolShape::BoolI128);
    let sar = find(&machine, X86Opcode::SarRI)[0];
    inst_mut(&mut machine, sar).opcode = X86Opcode::ShrRI;
    cases.push(("BoolI128/high-half-logical".to_string(), source, machine));
    cases
}

#[test]
fn every_bool_sign_extension_refutation_is_refuted_on_samples() {
    let cases = sext_bool_refutations();
    assert_eq!(cases.len(), 2 * SEXT_BOOL.len() + 2);
    for (label, source, machine) in cases {
        let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(theorem_refuted(&theorem), "{label}\n{}", describe(&machine));
    }
}

/// The real x86 optimizer's output at O1, O2 and O3 for every fixture: the
/// owner never names a mismatch for a correct lowering, and every theorem it
/// builds holds.
#[test]
fn optimized_bool_sign_extensions_are_judged_without_false_mismatches() {
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
        for shape in SEXT_BOOL {
            let (source, mut machine) = sext_bool_pair(shape);
            pipeline.run_x86_optimization_passes(&mut machine);
            match source_bound_x86_body(&source, &machine, SYSV) {
                Ok(owner) => {
                    built += 1;
                    assert!(
                        theorem_holds(owner.obligation()),
                        "{shape:?} at {opt_level:?}\n{}",
                        describe(&machine)
                    );
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
