// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 23 of the x86-64 source-bound body theorem: arithmetic congruence
//! pairing (OD-205: a machine row of operator key K whose stamp names a
//! source operation of key K, and whose own transcription is `K(c, d)`, is
//! spelled as the source's `K(a, b)`, the theorem claiming `a = c` and `b =
//! d`) and the generalization over arithmetic leaves (OD-206: an obligation
//! whose exact replay is neither Valid nor refuted is replayed once with
//! every product, quotient, remainder and variable shift a fresh free input).
//!
//! Fixtures are real: LIR from the trust-ir adapter (translated with an
//! explicit `Permit`), the machine stream from the real x86-64 instruction
//! selector (`super::select`). Every test here runs without a solver (the
//! `x86_source_bound_body::tests::slice23::` library gate); the replay on AY
//! and Clean is in `slice23_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice9::{dag_holds_on_samples, dag_refuted_on_samples};
use super::*;
use crate::verify::VerificationResult;
use trust_ir::{ICmpOp, OverflowOp};

/// Slice-23 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape23 {
    // ---- OD-205: arithmetic congruence pairing
    /// `i32::wrapping_mul`: `fn(a: i32, b: i32) -> i32 { a * b }`, an
    /// `imul r32, r32` whose operands are spelled through the 64-bit
    /// registers (the census's operand spelling).
    ImulPairedOperandSpelling,
    /// `fn(a: u64, b: u64) -> bool { a.overflowing_mul(b).1 }`: `mul`, its
    /// RDX the high half of the widening product.
    MulOverflowPaired,
    /// `fn(x: u64, k: u64) -> u64 { x >> (k & 63) }` lowered with the count
    /// left unmasked (the selector's `and` of the count edited into a copy:
    /// `shr r, cl` reads 6 bits of CL, so the lowering stays correct): the
    /// source's amount and the machine's count are spelled apart, equal in
    /// their low 6 bits only (`align_offset`'s `s23` and `m40`). The
    /// completeness fixture of the shift key's count bits.
    ShrClPaired,
    /// `fn(x: i64, k: i64) -> i64 { x >> (k & 63) }`, the count unmasked: a
    /// variable `sar` (no census root exercised one; its key is in the rule
    /// by symmetry).
    SarClPaired,
    /// `fn(x: u32, k: u32) -> u32 { x << (k & 31) }`, the count unmasked: a
    /// variable 32-bit `shl`.
    ShlClPaired,
    /// `fn(a: u64, b: u64) -> u64 { if b == 0 { trap } a / b }`: `div`.
    UdivPaired,
    /// `fn(a: i64, b: i64) -> i64 { if b == 0 { trap } if a == MIN && b == -1
    /// { trap } a % b }`: `idiv` by the selector's fixup of the divisor (1
    /// where the source divides by -1, the same remainder). A CORRECT lowering
    /// whose divisor operand differs from the source's at -1, so an `idiv`
    /// row is never paired. Paired anyway (tests only,
    /// [`with_signed_division_pairing`]), its unconditional divisor claim fails
    /// there: the paired theorem is refuted on samples, and the theorem
    /// without the pairing, which holds, decides (OD-205's arbiter).
    SremPaired,
    // ---- OD-206: the generalization over arithmetic leaves
    /// `u64::overflowing_pow`'s claim: `fn(x: u64) -> bool { let (a, o1) =
    /// x.overflowing_mul(x); let (_, o2) = a.overflowing_mul(x); o1 | o2 }`,
    /// two widening products' high halves.
    U64OverflowingPowLeaf,
    /// `wide_mul_u128::scalar_mul`'s claims: `fn(a: u128, b: u128, c: u128)
    /// -> bool { a.wrapping_mul(b).checked_add(c).is_none() }`, a 128-bit
    /// product by its limbs, then an add with carry and an unsigned compare.
    ScalarMulLeaf,
    /// `core::ptr::align_offset::<u8>`'s claims: `fn(a: u64, b: u64, y: u64,
    /// k: u64) -> u64 { ((a >> (k & 63)) - (b >> (k & 63))) * y }` with
    /// `ShrClPaired`'s unmasked count: two shifts whose source amount and
    /// machine count are spelled apart, and a product of their difference.
    AlignOffsetU8,
    /// `fn(x: u64, z: u64, a: u64, b: u64, y: u64) -> u64 { let k =
    /// min(x.count_ones() as u32, z.count_ones() as u32) as u64; ((a >> k) -
    /// (b >> k)) * y }`: `align_offset::<u8>`'s merged amount, a 32-bit block
    /// parameter read by two shifts, the machine's count the 64-bit extension
    /// of the merged register; nothing is masked or edited. Here the
    /// theorem's own spelling already names each shift once with the
    /// source's (value numbering through the merge), so the pairing changes
    /// nothing the theorem states (its operand claims are identities the
    /// spelling drops) and the owner keeps slices 1 to 22's bytes
    /// ([`owner_theorems`]). On `align_offset`'s real bytes the spelling keeps
    /// the barrels apart, and the pairing stays.
    MergedAmountAbsorbed,
    /// u8 `carrying_mul_add`'s value: `fn(a: u8, b: u8, c: u8, d: u8) -> u16
    /// { (a as u16) * (b as u16) + (c as u16) + (d as u16) }`. Its claim
    /// relies on the product's range (`u8 * u8 < 2^16`): the generalization
    /// is satisfiable and only the exact theorem credits it.
    U8CarryingMulAdd,
    /// `fn(x: u64, k: u64, b: bool) -> bool { (x >> (k & 63) == 0) ^ b }`,
    /// the count unmasked: a bool parameter and a bool result, so the theorem
    /// states the psABI walk and the clean-bool walk (`n` names), and the
    /// shift pairs in both ([`the_clean_bool_walk_pairs_its_rows_too`]).
    ShrClCleanBool,
}

/// Every slice-23 fixture shape.
pub(crate) const SLICE_TWENTY_THREE: [Shape23; 13] = [
    Shape23::ImulPairedOperandSpelling,
    Shape23::MulOverflowPaired,
    Shape23::ShrClPaired,
    Shape23::SarClPaired,
    Shape23::ShlClPaired,
    Shape23::UdivPaired,
    Shape23::SremPaired,
    Shape23::U64OverflowingPowLeaf,
    Shape23::ScalarMulLeaf,
    Shape23::AlignOffsetU8,
    Shape23::MergedAmountAbsorbed,
    Shape23::U8CarryingMulAdd,
    Shape23::ShrClCleanBool,
];

/// The shapes OD-205 pairs a row of: those whose theorem the pairing changes
/// ([`owner_theorems`]: the theorem's spelling does not absorb it). Every
/// other shape pairs nothing, or a pairing its spelling absorbs, and keeps
/// its bytes.
pub(crate) const PAIRED: [Shape23; 6] = [
    Shape23::ImulPairedOperandSpelling,
    Shape23::ShrClPaired,
    Shape23::SarClPaired,
    Shape23::ShlClPaired,
    Shape23::AlignOffsetU8,
    Shape23::ShrClCleanBool,
];

/// The shapes lowered with the count of a variable shift left unmasked
/// ([`unmask_count`]).
const UNMASKED: [Shape23; 5] = [
    Shape23::ShrClPaired,
    Shape23::SarClPaired,
    Shape23::ShlClPaired,
    Shape23::AlignOffsetU8,
    Shape23::ShrClCleanBool,
];

impl Shape23 {
    pub(crate) fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s23_");
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

fn slice23_function(shape: Shape23) -> Function {
    use Shape23::*;
    let name = shape.name();
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice23");
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        ImulPairedOperandSpelling => (vec![Ty::I32, Ty::I32], vec![Ty::I32]),
        MulOverflowPaired => (vec![Ty::U64, Ty::U64], vec![Ty::Bool]),
        ShrClPaired => (vec![Ty::U64; 2], vec![Ty::U64]),
        SarClPaired => (vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        ShlClPaired => (vec![Ty::U32, Ty::U32], vec![Ty::U32]),
        UdivPaired => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        SremPaired => (vec![Ty::I64, Ty::I64], vec![Ty::I64]),
        U64OverflowingPowLeaf => (vec![Ty::U64], vec![Ty::Bool]),
        ScalarMulLeaf => (vec![Ty::U128, Ty::U128, Ty::U128], vec![Ty::Bool]),
        AlignOffsetU8 => (vec![Ty::U64; 4], vec![Ty::U64]),
        MergedAmountAbsorbed => (vec![Ty::U64; 5], vec![Ty::U64]),
        U8CarryingMulAdd => (vec![Ty::U8; 4], vec![Ty::U16]),
        ShrClCleanBool => (vec![Ty::U64, Ty::U64, Ty::Bool], vec![Ty::Bool]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(name.clone(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        ImulPairedOperandSpelling => {
            let p = f.mul(Ty::I32, args[0], args[1]);
            f.ret(vec![p]);
        }
        MulOverflowPaired => {
            let (_, overflow) = f.overflow(OverflowOp::MulOverflow, Ty::U64, args[0], args[1]);
            f.ret(vec![overflow]);
        }
        ShrClPaired | SarClPaired | ShlClPaired => {
            let (ty, op, mask) = match shape {
                ShrClPaired => (Ty::U64, BinOp::LShr, 63),
                SarClPaired => (Ty::I64, BinOp::AShr, 63),
                _ => (Ty::U32, BinOp::Shl, 31),
            };
            let mask = f.iconst(ty.clone(), mask);
            let amount = f.binop(BinOp::And, ty.clone(), args[1], mask);
            let shifted = f.binop(op, ty, args[0], amount);
            f.ret(vec![shifted]);
        }
        UdivPaired | SremPaired => {
            let (ty, op) = if shape == UdivPaired {
                (Ty::U64, BinOp::UDiv)
            } else {
                (Ty::I64, BinOp::SRem)
            };
            trap_if_zero(&mut f, ty.clone(), args[1]);
            if shape == SremPaired {
                // rustc's second check: `MIN % -1` overflows.
                let (check, trap, go) = (f.create_block(), f.create_block(), f.create_block());
                let min = f.iconst(Ty::I64, i128::from(i64::MIN));
                let is_min = f.icmp(ICmpOp::Eq, Ty::I64, args[0], min);
                f.condbr(is_min, check, vec![], go, vec![]);
                f.switch_to_block(check);
                let minus_one = f.iconst(Ty::I64, -1);
                let is_minus_one = f.icmp(ICmpOp::Eq, Ty::I64, args[1], minus_one);
                f.condbr(is_minus_one, trap, vec![], go, vec![]);
                f.switch_to_block(trap);
                f.unreachable();
                f.switch_to_block(go);
            }
            let q = f.binop(op, ty, args[0], args[1]);
            f.ret(vec![q]);
        }
        U64OverflowingPowLeaf => {
            let (a, first) = f.overflow(OverflowOp::MulOverflow, Ty::U64, args[0], args[0]);
            let (_, second) = f.overflow(OverflowOp::MulOverflow, Ty::U64, a, args[0]);
            let either = f.binop(BinOp::Or, Ty::Bool, first, second);
            f.ret(vec![either]);
        }
        ScalarMulLeaf => {
            let p = f.mul(Ty::U128, args[0], args[1]);
            let (_, carry) = f.overflow(OverflowOp::AddOverflow, Ty::U128, p, args[2]);
            f.ret(vec![carry]);
        }
        AlignOffsetU8 => {
            let mask = f.iconst(Ty::U64, 63);
            let k = f.binop(BinOp::And, Ty::U64, args[3], mask);
            let a = f.binop(BinOp::LShr, Ty::U64, args[0], k);
            let b = f.binop(BinOp::LShr, Ty::U64, args[1], k);
            let d = f.sub(Ty::U64, a, b);
            let p = f.mul(Ty::U64, d, args[2]);
            f.ret(vec![p]);
        }
        MergedAmountAbsorbed => {
            let (less, more, join) = (f.create_block(), f.create_block(), f.create_block());
            let k = f.add_block_param(join, Ty::U32);
            let counts: Vec<V> = args[..2]
                .iter()
                .map(|arg| {
                    let count = f.ctpop(Ty::U64, *arg);
                    f.trunc(Ty::U64, Ty::U32, count)
                })
                .collect();
            let below = f.icmp(ICmpOp::Ult, Ty::U32, counts[0], counts[1]);
            f.condbr(below, less, vec![], more, vec![]);
            f.switch_to_block(less);
            f.br(join, vec![counts[0]]);
            f.switch_to_block(more);
            f.br(join, vec![counts[1]]);
            f.switch_to_block(join);
            let amount = f.zext(Ty::U32, Ty::U64, k);
            let a = f.binop(BinOp::LShr, Ty::U64, args[2], amount);
            let amount = f.zext(Ty::U32, Ty::U64, k);
            let b = f.binop(BinOp::LShr, Ty::U64, args[3], amount);
            let d = f.sub(Ty::U64, a, b);
            let p = f.mul(Ty::U64, d, args[4]);
            f.ret(vec![p]);
        }
        ShrClCleanBool => {
            let mask = f.iconst(Ty::U64, 63);
            let amount = f.binop(BinOp::And, Ty::U64, args[1], mask);
            let shifted = f.binop(BinOp::LShr, Ty::U64, args[0], amount);
            let zero = f.iconst(Ty::U64, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U64, shifted, zero);
            let flipped = f.binop(BinOp::Xor, Ty::Bool, is_zero, args[2]);
            f.ret(vec![flipped]);
        }
        U8CarryingMulAdd => {
            let wide: Vec<V> = args
                .iter()
                .map(|arg| f.zext(Ty::U8, Ty::U16, *arg))
                .collect();
            let p = f.mul(Ty::U16, wide[0], wide[1]);
            let s = f.add(Ty::U16, p, wide[2]);
            let t = f.add(Ty::U16, s, wide[3]);
            f.ret(vec![t]);
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
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"))
}

pub(crate) fn slice23_pair(shape: Shape23) -> (Function, X86ISelFunction) {
    let source = slice23_function(shape);
    let mut machine = select(&source, X86CallAbi::SystemV);
    if UNMASKED.contains(&shape) {
        unmask_count(&mut machine);
    }
    (source, machine)
}

/// The selector's `and` of a variable shift's count with the constant `w - 1`
/// (the source's `k & (w - 1)`: `mov m, imm; and d, k, m`) edited into a copy
/// `mov d, k`, so the count reaches CL unmasked. Still a correct lowering:
/// `shl`/`shr`/`sar r, cl` reads the count's low log2(w) bits only (5 or 6),
/// which the mask keeps.
fn unmask_count(machine: &mut X86ISelFunction) {
    let rows = super::rows(machine).len();
    let constant = |machine: &X86ISelFunction, operand: &O, before: usize| {
        (0..before).rev().find_map(|ordinal| {
            let row = inst(machine, ordinal);
            (row.operands.first() == Some(operand)).then(|| {
                match (row.opcode, row.operands.get(1)) {
                    (X86Opcode::MovRI, Some(O::Imm(imm))) => Some(*imm),
                    _ => None,
                }
            })
        })?
    };
    let and = (0..rows)
        .find(|&ordinal| {
            let row = inst(machine, ordinal);
            row.opcode == X86Opcode::AndRR
                && row.operands.len() == 3
                && matches!(constant(machine, &row.operands[2], ordinal), Some(31 | 63))
        })
        .unwrap_or_else(|| panic!("no count mask\n{}", describe(machine)));
    let row = inst_mut(machine, and);
    let (dst, count) = (row.operands[0].clone(), row.operands[1].clone());
    row.opcode = if matches!(&dst, O::VReg(vreg) if vreg.class == RegClass::Gpr32) {
        X86Opcode::MovRR32
    } else {
        X86Opcode::MovRR
    };
    row.operands = vec![dst, count];
}

#[track_caller]
pub(crate) fn owner<'a>(
    what: &str,
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> SourceBoundX86Body<'a> {
    source_bound_x86_body(source, machine, SYSV).unwrap_or_else(|refusal| {
        panic!(
            "{what}: {refusal}\n{}{}",
            describe_lir(source),
            describe(machine)
        )
    })
}

/// The theorem's query as the replay renders it.
pub(crate) fn text(obligation: &ProofObligation) -> String {
    generate_smt2_query_raw(obligation, &replay_config())
}

/// The owner's theorem without slice 23's pairing (the spelling of slices 1
/// to 22).
fn unpaired_text(source: &Function, machine: &X86ISelFunction) -> String {
    with_arithmetic_pairing(false, || {
        text(owner("unpaired", source, machine).obligation())
    })
}

/// Whether an obligation holds on slice 9's keyed samples, its free inputs
/// wider than 64 bits (a 128-bit leaf of a generalization) sampled as two
/// 64-bit halves (the sampler assigns 64-bit words).
pub(crate) fn holds_on_samples(obligation: &ProofObligation) -> bool {
    dag_holds_on_samples(&halved(obligation))
}

/// Whether some sample refutes an obligation ([`holds_on_samples`]'s inputs).
pub(crate) fn refuted_on_samples(obligation: &ProofObligation) -> bool {
    dag_refuted_on_samples(&halved(obligation))
}

/// `expr` with each name `env` maps replaced by its term.
pub(crate) fn subst(expr: &E, env: &HashMap<String, E>) -> E {
    expr.try_rewrite_dag::<std::convert::Infallible>(&mut |node| {
        Ok(match node {
            E::Var { name, .. } => env.get(name).cloned(),
            _ => None,
        })
    })
    .unwrap_or_else(|never| match never {})
    .unwrap_or_else(|| expr.clone())
}

/// `obligation` with each free input of 128 bits `x` replaced by `(concat
/// x_hi x_lo)` of two 64-bit free inputs (the same theorem over the same
/// values).
fn halved(obligation: &ProofObligation) -> ProofObligation {
    let defined: HashSet<String> = obligation
        .preconditions
        .iter()
        .filter_map(|premise| match premise {
            E::Eq { lhs, .. } => match lhs.as_ref() {
                E::Var { name, .. } => Some(name.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let wide: Vec<String> = obligation
        .inputs
        .iter()
        .filter(|(name, width)| *width == 128 && !defined.contains(name))
        .map(|(name, _)| name.clone())
        .collect();
    if wide.is_empty() {
        return obligation.clone();
    }
    let halves: HashMap<String, E> = wide
        .iter()
        .map(|name| {
            (
                name.clone(),
                E::var(format!("{name}_hi"), 64).concat(E::var(format!("{name}_lo"), 64)),
            )
        })
        .collect();
    let split = |expr: &E| -> E { subst(expr, &halves) };
    ProofObligation {
        trust_ir_expr: split(&obligation.trust_ir_expr),
        aarch64_expr: split(&obligation.aarch64_expr),
        inputs: obligation
            .inputs
            .iter()
            .flat_map(|(name, width)| {
                if wide.contains(name) {
                    vec![(format!("{name}_lo"), 64), (format!("{name}_hi"), 64)]
                } else {
                    vec![(name.clone(), *width)]
                }
            })
            .collect(),
        preconditions: obligation.preconditions.iter().map(split).collect(),
        ..obligation.clone()
    }
}

/// A diagnostic, not a check: every slice-23 fixture's LIR, machine rows,
/// theorem (and without the pairing) and generalization, and every wrong
/// lowering's rows.
pub(super) fn print_slice_twenty_three_fixtures() {
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match source_bound_x86_body(&source, &machine, SYSV) {
            Ok(owner) => {
                println!("{}", text(owner.obligation()));
                println!("-- unpaired\n{}", unpaired_text(&source, &machine));
                match owner.replay_generalized(0) {
                    Ok(general) => println!("-- generalized\n{}", text(general.obligation())),
                    Err(why) => println!("-- no generalization: {why}"),
                }
            }
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
    for (label, _, machine) in slice_twenty_three_refutations() {
        println!("==== {label} (wrong lowering)\n{}", describe(&machine));
    }
}

/// Every slice-23 shape builds a theorem that holds on samples, the same
/// text twice.
#[test]
fn owner_builds_every_slice_twenty_three_shape() {
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        let judged = owner.obligation().clone();
        assert!(
            holds_on_samples(&judged),
            "{shape:?}: refuted on samples\n{}{}{}",
            describe_lir(&source),
            describe(&machine),
            text(&judged)
        );
        let (source2, machine2) = slice23_pair(shape);
        assert_eq!(
            text(owner.obligation()),
            text(self::owner("again", &source2, &machine2).obligation()),
            "{shape:?}: deterministic"
        );
        eprintln!(
            "SLICE23_SHAPE {shape:?}: stated, {} bytes",
            text(owner.obligation()).len()
        );
    }
}

/// OD-205 moves the theorem of every shape it pairs a row of (the source's
/// operation spells the machine's; the operand claims are stated, or drop
/// as identities), and of no other; the theorem without the pairing (slices
/// 1 to 22) also holds.
#[test]
fn pairing_moves_exactly_the_paired_shapes() {
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
        let paired = text(owner(&format!("{shape:?}"), &source, &machine).obligation());
        let unpaired = unpaired_text(&source, &machine);
        assert_eq!(
            paired != unpaired,
            PAIRED.contains(&shape),
            "{shape:?}\n-- paired\n{paired}\n-- unpaired\n{unpaired}"
        );
        let before = with_arithmetic_pairing(false, || {
            owner("unpaired", &source, &machine).obligation().clone()
        });
        assert!(holds_on_samples(&before), "{shape:?} without the pairing");
    }
}

/// OD-205's arbiter: a correct lowering may compute a paired operand apart
/// from the source's (the selector's signed remainder divides by 1 where the
/// source divides by -1; such a row is never paired, but is here, tests
/// only), so the paired theorem's unconditional operand claim fails: it is
/// refuted on samples. The owner keeps the theorem
/// without the pairing, which holds; only it decides a refutation. A paired
/// shape with no false claim holds both ways; an unpaired one has no second
/// theorem.
#[test]
fn a_refuted_paired_theorem_is_decided_by_the_theorem_without_the_pairing() {
    let (source, machine) = slice23_pair(Shape23::SremPaired);
    assert!(
        !owner("SremPaired", &source, &machine).is_paired(),
        "an idiv row is never paired"
    );
    let owner = with_signed_division_pairing(|| owner("SremPaired", &source, &machine));
    assert!(owner.is_paired() && owner.has_unpaired());
    assert!(
        refuted_on_samples(owner.obligation()),
        "the divisor claim fails at -1\n{}",
        text(owner.obligation())
    );
    let unpaired = owner.statement_of(X86Theorem::Unpaired).expect("built");
    assert!(holds_on_samples(&unpaired), "{}", text(&unpaired));
    assert_eq!(text(&unpaired), unpaired_text(&source, &machine));
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
        let owner = self::owner(&format!("{shape:?}"), &source, &machine);
        assert_eq!(owner.is_paired(), PAIRED.contains(&shape), "{shape:?}");
        assert_eq!(owner.has_unpaired(), owner.is_paired(), "{shape:?}");
        if owner.has_unpaired() && shape != Shape23::SremPaired {
            assert!(holds_on_samples(owner.obligation()), "{shape:?}");
        }
    }
}

/// OD-205's pairing is the theorem's question ([`owner_theorems`]): a
/// pairing the theorem's spelling absorbs is dropped. `MulOverflowPaired`
/// (`a.overflowing_mul(b).1` by `mul`): its paired build states its operand
/// claims, identities the spelling drops, but as a conjunction against `true`
/// where the theorem without the pairing is the one equation `(= S M)`; its
/// paired definitions alone give that theorem byte for byte (value numbering
/// already names the widening product once), so the owner states it,
/// unpaired. `MergedAmountAbsorbed`'s paired build is that theorem already.
/// `AlignOffsetU8` (the source's masked amount and the machine's unmasked
/// count stay two barrels) and slice 18's `Mul/commuted` (`imul b, a`) are
/// not absorbed, and the owner pairs. Every owner's theorem holds.
#[test]
fn a_pairing_the_spelling_absorbs_leaves_the_theorem_without_it() {
    use super::slice18::built;
    let (_, commuted_source, commuted_machine) = super::commuted_variants()
        .into_iter()
        .find(|(label, ..)| label == "Mul/commuted")
        .expect("slice 18's commuted product");
    let (overflow_source, overflow_machine) = slice23_pair(Shape23::MulOverflowPaired);
    let (merged_source, merged_machine) = slice23_pair(Shape23::MergedAmountAbsorbed);
    let (align_source, align_machine) = slice23_pair(Shape23::AlignOffsetU8);
    // (label, source, machine, the paired build differs, absorbed)
    for (label, source, machine, differs, absorbed) in [
        (
            "MulOverflowPaired",
            &overflow_source,
            &overflow_machine,
            true,
            true,
        ),
        (
            "MergedAmountAbsorbed",
            &merged_source,
            &merged_machine,
            false,
            true,
        ),
        ("AlignOffsetU8", &align_source, &align_machine, true, false),
        (
            "Mul/commuted",
            &commuted_source,
            &commuted_machine,
            true,
            false,
        ),
    ] {
        let encoded = |encoding| built(source, machine, encoding, false).expect("built").0;
        let unpaired = encoded(PathEncoding::UNPAIRED);
        assert_eq!(
            encoded(PathEncoding::CANONICAL) != unpaired,
            differs,
            "{label}: the paired build"
        );
        assert_eq!(
            encoded(PathEncoding::PAIRED_DEFINITIONS_ONLY) == unpaired,
            absorbed,
            "{label}: the paired definitions alone"
        );
        let owner = owner(label, source, machine);
        assert_eq!(owner.is_paired(), !absorbed, "{label}");
        assert_eq!(owner.has_unpaired(), !absorbed, "{label}");
        assert_eq!(*owner.obligation() == unpaired, absorbed, "{label}");
        assert!(holds_on_samples(owner.obligation()), "{label}");
    }
}

/// OD-205's shift key reads the count at log2(w) bits: `ShrClPaired`'s
/// masked source amount and the machine's unmasked count (equal in their low
/// 6 bits only) pair, and the theorem holds; the one barrel left reads the
/// source's amount. Claiming the whole counts equal (the mutant
/// `shift-key-full-count`) would refute this correct lowering.
#[test]
fn a_shift_pairs_at_its_count_bits() {
    let (source, machine) = slice23_pair(Shape23::ShrClPaired);
    assert!(
        !refuted_on_samples(&with_arithmetic_pairing(false, || {
            owner("unpaired", &source, &machine).obligation().clone()
        })),
        "the unmasked count is a correct lowering"
    );
    let owner = owner("ShrClPaired", &source, &machine);
    let query = text(owner.obligation());
    assert!(holds_on_samples(owner.obligation()), "{query}");
    let unpaired = unpaired_text(&source, &machine);
    // The unpaired theorem states two barrels (each tests bit 5 of its
    // amount), the paired one a single barrel.
    let stage_tests = |query: &str| query.matches("((_ extract 5 5)").count();
    assert!(
        stage_tests(&query) < stage_tests(&unpaired),
        "the paired theorem keeps both barrels\n{query}\n-- unpaired\n{unpaired}"
    );
}

// ---------------------------------------------------------------------------
// OD-205: the operator keys and the canonical identities, exhaustively
// ---------------------------------------------------------------------------

/// Evaluate a bit-vector term of the variables `a` and `b` at `(x, y)`.
fn eval2(expr: &E, x: u64, y: u64) -> u64 {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    env.insert("a".into(), x);
    env.insert("b".into(), y);
    match expr.eval(&env) {
        EvalResult::Bv(value) => value,
        EvalResult::Bv128(value) => value as u64,
        other => panic!("{expr}: {other:?}"),
    }
}

/// THE key discipline (OD-205), exhaustively at 1 to 6 bits: two keys that
/// differ in signedness or width are different functions (each pair differs
/// on some operand pair from 2 bits on), and a product's low half is
/// sign-agnostic (`mullo` has no signedness: the low half of either
/// widening product is the product).
#[test]
fn the_operator_keys_are_distinct_functions() {
    for n in 1..=6u32 {
        let (x, y) = (E::var("a", n), E::var("b", n));
        let key = |op: ArithOp| ArithKey::new(op, n).apply(x.clone(), y.clone());
        let pairs: [(ArithOp, ArithOp); 5] = [
            (ArithOp::UMulWide, ArithOp::SMulWide),
            (ArithOp::Udiv, ArithOp::Sdiv),
            (ArithOp::Urem, ArithOp::Srem),
            (ArithOp::Lshr, ArithOp::Ashr),
            (ArithOp::Shl, ArithOp::Lshr),
        ];
        let all = 1u64 << n;
        for (one, other) in pairs {
            if n < 2 || (matches!(one, ArithOp::Lshr | ArithOp::Shl) && !n.is_power_of_two()) {
                continue;
            }
            let (f, g) = (key(one), key(other));
            let differ = (0..all).any(|p| (0..all).any(|q| eval2(&f, p, q) != eval2(&g, p, q)));
            assert!(differ, "{one:?} and {other:?} agree everywhere at {n} bits");
        }
        // mullo: the low half of either widening product is the product.
        let lo = key(ArithOp::MulLo);
        for wide in [ArithOp::UMulWide, ArithOp::SMulWide] {
            let low = key(wide).extract(n - 1, 0);
            for p in 0..all {
                for q in 0..all {
                    assert_eq!(eval2(&lo, p, q), eval2(&low, p, q), "{wide:?} at {n} bits");
                }
            }
        }
        // A width is part of the key: the n-bit product against the
        // extension of the n/2-bit product of the low halves.
        if n >= 2 && n % 2 == 0 {
            let half = (x.clone().extract(n / 2 - 1, 0))
                .bvmul(y.clone().extract(n / 2 - 1, 0))
                .zero_ext(n / 2);
            let differ = (0..all).any(|p| (0..all).any(|q| eval2(&lo, p, q) != eval2(&half, p, q)));
            assert!(differ, "the {n}-bit product is the narrow one's extension");
        }
    }
}

/// OD-206's canonical forms are identities on every input, exhaustively at
/// 1 to 6 bits: `comm` (a product's operands in either order, for `mullo`,
/// `umulwide` and `smulwide`) and `wide` (the n-bit product is the low half
/// of either widening product of the same operands).
#[test]
fn the_canonical_forms_are_identities_exhaustively() {
    for n in 1..=6u32 {
        let (x, y) = (E::var("a", n), E::var("b", n));
        let all = 1u64 << n;
        for op in [ArithOp::MulLo, ArithOp::UMulWide, ArithOp::SMulWide] {
            let key = ArithKey::new(op, n);
            let (f, g) = (
                key.apply(x.clone(), y.clone()),
                key.apply(y.clone(), x.clone()),
            );
            for p in 0..all {
                for q in 0..all {
                    assert_eq!(eval2(&f, p, q), eval2(&g, p, q), "comm {op:?} at {n} bits");
                }
            }
        }
        let product = x.clone().bvmul(y.clone());
        for op in [ArithOp::UMulWide, ArithOp::SMulWide] {
            let wide = ArithKey::new(op, n)
                .apply(x.clone(), y.clone())
                .extract(n - 1, 0);
            for p in 0..all {
                for q in 0..all {
                    assert_eq!(
                        eval2(&product, p, q),
                        eval2(&wide, p, q),
                        "wide {op:?} at {n} bits"
                    );
                }
            }
        }
    }
}

/// A key reads exactly the operand bits its operand claims state
/// ([`ArithKey::read_operand`], what the pairing record's re-derivation
/// asks to be claimed): every operand whole, but a shift's amount, read at
/// its low log2(w) bits. Exhaustively at 4 and 8 bits (every value and every
/// 8-bit amount: the shift equals the shift by the amount's read bits); at
/// the admitted 32 and 64 bits, the barrel reads its amount only through
/// single-bit extracts of those bits.
#[test]
fn a_shift_key_reads_its_amount_at_its_claimed_bits() {
    for op in [ArithOp::Shl, ArithOp::Lshr, ArithOp::Ashr] {
        for n in [4u32, 8] {
            let key = ArithKey::new(op, n);
            let (value, amount) = (E::var("a", n), E::var("b", 8));
            let shift = key.apply(value.clone(), amount.clone());
            let read = key.apply(value, key.read_operand(1, amount));
            for v in 0..(1u64 << n) {
                for k in 0..256u64 {
                    assert_eq!(
                        eval2(&shift, v, k),
                        eval2(&read, v, k),
                        "{op:?} at {n} bits: {v} by {k}"
                    );
                }
            }
        }
        for n in [32u32, 64] {
            let key = ArithKey::new(op, n);
            let shift = key.apply(E::var("a", n), E::var("b", 64));
            let stages = n.trailing_zeros();
            let mut reads: Vec<(u32, u32)> = Vec::new();
            let mut pending = vec![&shift];
            while let Some(term) = pending.pop() {
                if let E::Extract {
                    high, low, operand, ..
                } = term
                    && matches!(operand.as_ref(), E::Var { name, .. } if name == "b")
                {
                    reads.push((*high, *low));
                    continue;
                }
                assert!(
                    !matches!(term, E::Var { name, .. } if name == "b"),
                    "{op:?} at {n} bits reads its whole amount"
                );
                term.for_each_child(&mut |child| pending.push(child));
            }
            reads.sort_unstable();
            reads.dedup();
            assert_eq!(
                reads,
                (0..stages).map(|bit| (bit, bit)).collect::<Vec<_>>(),
                "{op:?} at {n} bits"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// OD-205: wrong lowerings stay refuted; a row of another key is not paired
// ---------------------------------------------------------------------------

/// The register operand `operand` of row `ordinal` replaced by the register
/// operand `with` of row `from`.
fn replace_operand(machine: &mut X86ISelFunction, ordinal: usize, operand: usize, with: O) {
    inst_mut(machine, ordinal).operands[operand] = with;
}

/// Another value to read in place of `like` at row `at`: the destination
/// of an earlier row, a virtual register of `like`'s class that is neither
/// `like` nor in `avoid` (defined before `at`, so the read is defined).
fn other_value(machine: &X86ISelFunction, at: usize, like: &O, avoid: &[O]) -> O {
    let class = match like {
        O::VReg(vreg) => vreg.class,
        other => panic!("{other:?} is no virtual register\n{}", describe(machine)),
    };
    (0..at)
        .rev()
        .filter_map(|ordinal| inst(machine, ordinal).operands.first().cloned())
        .find(|dst| {
            matches!(dst, O::VReg(vreg) if vreg.class == class)
                && dst != like
                && !avoid.contains(dst)
        })
        .unwrap_or_else(|| panic!("no other value before row {at}\n{}", describe(machine)))
}

/// §5's wrong lowerings of the design, each as one edit of the selector's
/// real stream: a wrong operand, a wrong divisor, signed for unsigned (an
/// `idiv` for a `div`, a `sar` for a `shr`), a shift count from another
/// register, and a division whose dividend's high half is stale (its own
/// transcription is not the key's: the `pair-stamp-only` control). A 32-bit
/// product where the source multiplies at 64 bits is no edit the walk
/// admits (an `imul` of 32-bit registers holding 64-bit values is outside
/// the body domain); the key's width is checked by
/// `the_keys_pair_only_at_one_width_and_signedness`.
pub(crate) fn slice_twenty_three_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // `imul a, c` for `imul a, b` (the census's `* r1` for `* r2`).
    {
        let (source, mut machine) = slice23_pair(Shape23::AlignOffsetU8);
        let imul = find(&machine, X86Opcode::ImulRR)[0];
        let ops = inst(&machine, imul).operands.clone();
        let other = other_value(&machine, imul, &ops[2], &ops);
        replace_operand(&mut machine, imul, 2, other);
        cases.push(("product/wrong-operand", source, machine));
    }
    // `imul r32, r32` of the operands' low halves, zero-extended, for the
    // source's 64-bit product: a product of another key (`mullo(32)`), which
    // is not paired and keeps its exact term.
    {
        let (source, mut machine) = slice23_pair(Shape23::AlignOffsetU8);
        let imul = find(&machine, X86Opcode::ImulRR)[0];
        let (_, block, index) = super::rows(&machine)[imul];
        let ops = inst(&machine, imul).operands.clone();
        let narrow = |k: u32| O::VReg(VReg::new(machine.next_vreg + 10 + k, RegClass::Gpr32));
        let (lhs, rhs, product) = (narrow(0), narrow(1), narrow(2));
        let insts = &mut machine.blocks.get_mut(&block).unwrap().insts;
        insts[index].operands = vec![product.clone(), lhs.clone(), rhs.clone()];
        insts.insert(
            index + 1,
            X86ISelInst::new(X86Opcode::MovRR32, vec![ops[0].clone(), product]),
        );
        insts.insert(
            index,
            X86ISelInst::new(X86Opcode::MovRR32, vec![rhs, ops[2].clone()]),
        );
        insts.insert(
            index,
            X86ISelInst::new(X86Opcode::MovRR32, vec![lhs, ops[1].clone()]),
        );
        machine.next_vreg += 13;
        cases.push(("product/32-bit-for-64-bit", source, machine));
    }
    // The shifted value from another register (`shr k, cl` for `shr x,
    // cl`), at 64 and at 32 bits, and in a function the clean-bool walk
    // states too: only the shifted value's operand claim refutes the paired
    // theorem (the count's is right).
    for (label, shape, opcode) in [
        (
            "shr/wrong-shifted-value",
            Shape23::ShrClPaired,
            X86Opcode::ShrRR,
        ),
        (
            "shl32/wrong-shifted-value",
            Shape23::ShlClPaired,
            X86Opcode::ShlRR,
        ),
        (
            "clean-bool/wrong-shifted-value",
            Shape23::ShrClCleanBool,
            X86Opcode::ShrRR,
        ),
    ] {
        let (source, mut machine) = slice23_pair(shape);
        let shift = find(&machine, opcode)[0];
        let ops = inst(&machine, shift).operands.clone();
        let other = other_value(&machine, shift, &ops[1], &ops);
        replace_operand(&mut machine, shift, 1, other);
        cases.push((label, source, machine));
    }
    // `div c` for `div b`.
    {
        let (source, mut machine) = slice23_pair(Shape23::UdivPaired);
        let div = find(&machine, X86Opcode::Div)[0];
        let ops = inst(&machine, div).operands.clone();
        let other = other_value(&machine, div, &ops[0], &ops);
        replace_operand(&mut machine, div, 0, other);
        cases.push(("udiv/wrong-divisor", source, machine));
    }
    // `idiv b` for `div b`: signed for unsigned.
    {
        let (source, mut machine) = slice23_pair(Shape23::UdivPaired);
        let div = find(&machine, X86Opcode::Div)[0];
        inst_mut(&mut machine, div).opcode = X86Opcode::Idiv;
        cases.push(("udiv/signed-idiv", source, machine));
    }
    // `sar x, cl` for `shr x, cl`.
    {
        let (source, mut machine) = slice23_pair(Shape23::ShrClPaired);
        let shr = find(&machine, X86Opcode::ShrRR)[0];
        inst_mut(&mut machine, shr).opcode = X86Opcode::SarRR;
        cases.push(("shr/signed-sar", source, machine));
    }
    // The count moved into RCX from another register.
    {
        let (source, mut machine) = slice23_pair(Shape23::ShrClPaired);
        let shr = find(&machine, X86Opcode::ShrRR)[0];
        let count = (0..shr)
            .rev()
            .find(|&ordinal| {
                let inst = inst(&machine, ordinal);
                matches!(inst.opcode, X86Opcode::MovRR | X86Opcode::MovRR32)
                    && matches!(&inst.operands[0], O::PReg(reg) if [1u16, 17, 49].map(X86PReg::new).contains(reg))
            })
            .unwrap_or_else(|| panic!("the count's move into RCX\n{}", describe(&machine)));
        let value = inst(&machine, shr).operands.clone();
        let read = inst(&machine, count).operands[1].clone();
        let other = other_value(&machine, count, &read, &value);
        replace_operand(&mut machine, count, 1, other);
        cases.push(("shr/count-from-another-register", source, machine));
    }
    // The dividend's high half stale: RDX holds the divisor, not zero.
    {
        let (source, mut machine) = slice23_pair(Shape23::UdivPaired);
        let div = find(&machine, X86Opcode::Div)[0];
        let zero = (0..div)
            .rev()
            .find(|&ordinal| {
                let inst = inst(&machine, ordinal);
                matches!(inst.opcode, X86Opcode::XorRR | X86Opcode::MovRI)
            })
            .expect("the dividend's zero high half");
        let rdx = inst(&machine, zero).operands[0].clone();
        let divisor = inst(&machine, div).operands[0].clone();
        let row = inst_mut(&mut machine, zero);
        row.opcode = X86Opcode::MovRR;
        row.operands = vec![rdx, divisor];
        cases.push(("udiv/stale-high-half", source, machine));
    }
    // The dividend's high half the divisor minus one (`mov rdx, b; sub rdx,
    // 1; div b` for `xor edx, edx; div b`): the `div` never faults (its high
    // half is below the divisor) and divides `(b - 1) * 2^64 + a`, not `a`.
    // The row is a `div` stamped with the source's `Udiv`, of the source's
    // dividend and divisor, but its own transcription is no `udiv(a, b)`, so
    // check (3) of [`pair_arithmetic`] leaves it unpaired and the exact
    // theorem refutes it; paired on its stamp alone (the `pair-stamp-only`
    // mutant), its quotient would be `udiv(a, b)` and the theorem would hold.
    {
        let (source, mut machine) = slice23_pair(Shape23::UdivPaired);
        let div = find(&machine, X86Opcode::Div)[0];
        let zero = (0..div)
            .rev()
            .find(|&ordinal| {
                let inst = inst(&machine, ordinal);
                matches!(inst.opcode, X86Opcode::XorRR | X86Opcode::MovRI)
            })
            .expect("the dividend's zero high half");
        let rdx = inst(&machine, zero).operands[0].clone();
        let divisor = inst(&machine, div).operands[0].clone();
        let row = inst_mut(&mut machine, zero);
        row.opcode = X86Opcode::MovRR;
        row.operands = vec![rdx.clone(), divisor];
        let (_, block, index) = super::rows(&machine)[zero];
        machine.blocks.get_mut(&block).unwrap().insts.insert(
            index + 1,
            X86ISelInst::new(X86Opcode::SubRI, vec![rdx.clone(), rdx, O::Imm(1)]),
        );
        cases.push(("udiv/high-half-divisor-minus-one", source, machine));
    }
    cases
}

/// OD-205 over every earlier fixture and wrong lowering (slice 18's
/// inventory, slices 14 and 22): each pair whose theorem the pairing moves is
/// listed; a CORRECT one's paired theorem still holds on samples (no operand
/// claim of the canonical walk is false: `idiv` rows, whose divisor the
/// selector fixes up, are never paired), and a wrong one's is still refuted.
#[test]
fn every_fixture_the_pairing_moves_keeps_its_verdict() {
    use super::slice18::{built, every_fixture, every_refutation};
    let mut correct: Vec<(String, Function, X86ISelFunction, bool)> = every_fixture()
        .into_iter()
        .map(|(label, source, machine)| (label, source, machine, false))
        .collect();
    for shape in super::slice14::SLICE_FOURTEEN {
        let (source, machine) = super::slice14::slice14_pair(shape);
        correct.push((format!("s14 {shape:?}"), source, machine, false));
    }
    for shape in super::slice22::SLICE_TWENTY_TWO {
        let (source, machine) = super::slice22::slice22_pair(shape);
        correct.push((format!("s22 {shape:?}"), source, machine, false));
    }
    let fixtures = correct.len();
    correct.extend(every_refutation());
    for (label, source, machine) in super::slice14::slice_fourteen_refutations() {
        correct.push((format!("s14 {label}"), source, machine, false));
    }
    for (label, source, machine) in super::slice10::slice_ten_refutations() {
        correct.push((format!("s10 {label}"), source, machine, false));
    }
    let mut moved: Vec<String> = Vec::new();
    for (k, (label, source, machine, unbounded)) in correct.iter().enumerate() {
        let wrong = k >= fixtures;
        let (Some(paired), Some(unpaired)) = (
            built(source, machine, PathEncoding::CANONICAL, *unbounded),
            built(source, machine, PathEncoding::UNPAIRED, *unbounded),
        ) else {
            continue;
        };
        if paired.0 == unpaired.0 {
            continue;
        }
        moved.push(format!("{}{label}", if wrong { "wrong " } else { "" }));
        if wrong {
            assert!(
                refuted_on_samples(&paired.0),
                "{label}: the paired theorem holds\n{}",
                text(&paired.0)
            );
        } else {
            assert!(
                holds_on_samples(&paired.0),
                "{label}: a correct lowering's paired theorem is refuted\n{}",
                text(&paired.0)
            );
        }
    }
    eprintln!("SLICE23_MOVED {} {moved:?}", moved.len());
}

/// The key comparison (OD-205): a machine row pairs with a source operation
/// only at the same operation, signedness and width: every two distinct keys
/// of the rule (each operation at 8, 16, 32 and 64 bits) are apart, every
/// key is its own.
#[test]
fn the_keys_pair_only_at_one_width_and_signedness() {
    let ops = [
        ArithOp::MulLo,
        ArithOp::UMulWide,
        ArithOp::SMulWide,
        ArithOp::Udiv,
        ArithOp::Urem,
        ArithOp::Sdiv,
        ArithOp::Srem,
        ArithOp::Shl,
        ArithOp::Lshr,
        ArithOp::Ashr,
    ];
    let keys: Vec<ArithKey> = ops
        .iter()
        .flat_map(|op| [8, 16, 32, 64].map(|bits| ArithKey::new(*op, bits)))
        .collect();
    for machine in &keys {
        for source in &keys {
            assert_eq!(
                same_key(*machine, *source),
                machine == source,
                "{machine:?} against {source:?}"
            );
        }
    }
}

/// Every slice-23 wrong lowering builds a theorem (the pairing applies to
/// the rows of the source's key) and is refuted on samples.
#[test]
fn every_slice_twenty_three_refutation_is_refuted() {
    for (label, source, machine) in slice_twenty_three_refutations() {
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap_or_else(|refusal| {
            panic!(
                "{label}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        assert!(
            refuted_on_samples(owner.obligation()),
            "{label}: a wrong lowering holds on samples\n{}{}",
            describe(&machine),
            text(owner.obligation())
        );
    }
}

/// A row of another key is never paired: a wrong lowering whose row's key
/// differs from the source operation's (signed for unsigned, a 32-bit
/// product for a 64-bit one) or whose row is not its key's transcription (a
/// stale high half) is stated exactly as without the pairing.
#[test]
fn a_row_of_another_key_is_not_paired() {
    for (label, source, machine) in slice_twenty_three_refutations() {
        let keyed_apart = matches!(
            label,
            "udiv/signed-idiv"
                | "shr/signed-sar"
                | "udiv/stale-high-half"
                | "udiv/high-half-divisor-minus-one"
        );
        if !keyed_apart {
            continue;
        }
        let paired = text(owner(label, &source, &machine).obligation());
        assert_eq!(paired, unpaired_text(&source, &machine), "{label}");
    }
}

// ---------------------------------------------------------------------------
// OD-205: the pairing record, re-derived by every consumer
// ---------------------------------------------------------------------------

/// Check (3)'s meaning-level control: `udiv/high-half-divisor-minus-one`
/// (`div` with RDX the divisor minus one, so it never faults and its quotient
/// is no `udiv(a, b)`; `stale_rdx.py` of the review). Its row is a `div`
/// stamped with the source's `Udiv`, of the source's dividend and divisor:
/// check (3) alone keeps it unpaired, and its exact theorem is refuted.
/// Paired on its stamp alone (check (3) skipped, [`with_stamp_only_pairing`],
/// the pairing of the `pair-stamp-only` mutant), its theorem holds on samples:
/// the wrong quotient would be credited. Every consumer re-derives check (3)
/// from the pairing record, and refuses that record.
#[test]
fn check_three_keeps_a_stamped_div_of_another_dividend_unpaired() {
    let (label, source, machine) = slice_twenty_three_refutations()
        .into_iter()
        .find(|(label, ..)| *label == "udiv/high-half-divisor-minus-one")
        .expect("the control");
    let exact = owner(label, &source, &machine);
    assert!(!exact.is_paired(), "a stamp alone never pairs");
    assert!(
        refuted_on_samples(exact.obligation()),
        "the wrong quotient is refuted\n{}",
        text(exact.obligation())
    );
    let stamped = with_stamp_only_pairing(|| owner(label, &source, &machine));
    assert!(stamped.is_paired(), "paired on its stamp alone");
    assert!(
        holds_on_samples(stamped.obligation()),
        "paired on its stamp alone, the wrong quotient holds\n{}",
        text(stamped.obligation())
    );
    let refusal = stamped
        .check_pairing()
        .expect_err("a consumer re-derives check (3)");
    assert!(refusal.contains("check (3)"), "{refusal}");
    let export = crate::SourceBoundArithmeticObligation::x86_body_export_for_tests(&stamped);
    assert!(export.is_x86_body_paired());
    assert!(export.check_x86_body_pairing().is_err());
    assert!(export.replayed_obligations().is_err());
}

/// Every paired owner carries its pairing record, and the record re-derives
/// the pairing and the statement ([`X86BodyPairing::check`]): the owner's
/// check, the export's and its publication pass. `ShrClCleanBool` pairs its
/// shift in the psABI walk and in the clean-bool walk (two rows; one only,
/// under the mutant `pair-psabi-walk-only`); slice 18's `Mul/commuted` pairs
/// its product crossed; a statement in parts (`srem_in_parts_pair`, its
/// `idiv` paired in tests only) re-derives too. An owner that pairs nothing
/// carries no record.
#[test]
fn every_paired_owner_re_derives_its_pairing() {
    let mut cases: Vec<(String, Function, X86ISelFunction)> = SLICE_TWENTY_THREE
        .iter()
        .map(|shape| {
            let (source, machine) = slice23_pair(*shape);
            (format!("{shape:?}"), source, machine)
        })
        .collect();
    let (_, commuted_source, commuted_machine) = super::commuted_variants()
        .into_iter()
        .find(|(label, ..)| label == "Mul/commuted")
        .expect("slice 18's commuted product");
    cases.push(("Mul/commuted".into(), commuted_source, commuted_machine));
    let mut crossed = 0;
    for (label, source, machine) in &cases {
        let owner = owner(label, source, machine);
        assert_eq!(owner.pairing().is_some(), owner.is_paired(), "{label}");
        if let Err(why) = owner.check_pairing() {
            panic!("{label}: {why}");
        }
        crossed += owner.pairing().map_or(0, |pairing| {
            pairing.rows.iter().filter(|row| row.crossed).count()
        });
        let export = crate::SourceBoundArithmeticObligation::x86_body_export_for_tests(&owner);
        assert_eq!(export.is_x86_body_paired(), owner.is_paired(), "{label}");
        assert_eq!(
            export.x86_body_pairing().is_some(),
            owner.is_paired(),
            "{label}"
        );
        assert!(export.check_x86_body_pairing().is_ok(), "{label}");
        assert!(export.replayed_obligations().is_ok(), "{label}");
        eprintln!(
            "SLICE23_PAIRING {label}: {} paired rows",
            owner.pairing().map_or(0, X86BodyPairing::paired_rows)
        );
    }
    assert!(crossed > 0, "`Mul/commuted` pairs its product crossed");
    let (source, machine) = slice23_pair(Shape23::ShrClCleanBool);
    assert_eq!(
        owner("ShrClCleanBool", &source, &machine)
            .pairing()
            .map(X86BodyPairing::paired_rows),
        Some(2),
        "the psABI walk's shift and the clean-bool walk's"
    );
    let (source, machine) = srem_in_parts_pair();
    let owner = with_signed_division_pairing(|| owner("SremInParts", &source, &machine));
    assert!(owner.is_stated_in_parts() && owner.is_paired());
    if let Err(why) = owner.check_pairing() {
        panic!("SremInParts: {why}");
    }
    let export = crate::SourceBoundArithmeticObligation::x86_body_export_for_tests(&owner);
    assert_eq!(
        export.replayed_obligations().expect("its parts publish"),
        owner.replayed_units()
    );
}

/// The conjuncts of a claim conjunction (right-nested `and`).
fn conjuncts_of(claims: &E) -> Vec<E> {
    let mut terms = Vec::new();
    let mut rest = claims;
    while let E::And { lhs, rhs } = rest {
        terms.push(lhs.as_ref().clone());
        rest = rhs.as_ref();
    }
    terms.push(rest.clone());
    terms
}

/// The pairing record is re-derived by every consumer (OD-205): a record
/// forged in any of its parts (a walk definition that is not `K(c, d)`, a
/// paired name not defined as `K(a, b)`, an operand claim dropped, a
/// non-commuting key's operands crossed, a name paired twice), an absent
/// record, and a record checked against a statement it does not spell (the
/// theorem without the pairing, a premise dropped, a claim changed) are each
/// refused, by the owner's check, the export's and its publication. The
/// mutant `pairing-not-rederived` (the check skipped) fails here.
#[test]
fn a_forged_pairing_record_is_refused() {
    let (source, machine) = slice23_pair(Shape23::AlignOffsetU8);
    let paired = owner("AlignOffsetU8", &source, &machine);
    let record = paired.pairing().expect("a paired owner's record").clone();
    assert!(record.check(paired.obligation()).is_ok());
    // The first operand claim the record states (no identity).
    let (claimed_row, claim) = record
        .rows
        .iter()
        .enumerate()
        .find_map(|(k, row)| {
            let (c, d) = if row.crossed {
                (&row.machine.1, &row.machine.0)
            } else {
                (&row.machine.0, &row.machine.1)
            };
            [(&row.source.0, c), (&row.source.1, d)]
                .into_iter()
                .enumerate()
                .map(|(operand, (a, c))| {
                    (
                        row.key.read_operand(operand, a.clone()),
                        row.key.read_operand(operand, c.clone()),
                    )
                })
                .find(|(a, c)| a != c)
                .map(|(a, c)| (k, a.eq_expr(c)))
        })
        .expect("an operand claim");
    let shift = record
        .rows
        .iter()
        .position(|row| row.key.is_shift())
        .expect("a paired shift");
    let forgeries: Vec<(&str, X86BodyPairing, &str)> = vec![
        (
            "a walk definition that is not K(c, d)",
            record.forged(|rows, _, _| rows[0].results[0].2 = E::bv_const(0, 64)),
            "check (3)",
        ),
        (
            "a paired name defined as its walk definition",
            record.forged(|rows, definitions, _| {
                let (name, _, walked) = rows[0].results[0].clone();
                definitions
                    .iter_mut()
                    .find(|(defined, _)| *defined == name)
                    .expect("defined")
                    .1 = walked;
            }),
            "not defined as its part of the source's K(a, b)",
        ),
        (
            "an operand claim dropped",
            record.forged(|_, _, machine_side| {
                let kept: Vec<E> = conjuncts_of(machine_side)
                    .into_iter()
                    .filter(|term| *term != claim)
                    .collect();
                *machine_side = kept
                    .into_iter()
                    .rev()
                    .reduce(|tail, term| term.and_expr(tail))
                    .expect("other claims");
            }),
            "not claimed equal",
        ),
        (
            "a shift's operands crossed",
            record.forged(|rows, _, _| rows[shift].crossed = true),
            "does not commute",
        ),
        (
            "a row paired twice",
            record.forged(|rows, _, _| {
                let again = rows[0].clone();
                rows.push(again);
            }),
            "paired twice",
        ),
    ];
    assert!(claimed_row < record.rows.len());
    for (label, forged, reason) in forgeries {
        let refusal = forged.check(paired.obligation()).expect_err(label);
        assert!(refusal.contains(reason), "{label}: {refusal}");
        let owner = owner(label, &source, &machine).with_pairing_record(Some(forged.clone()));
        assert!(owner.check_pairing().is_err(), "{label}");
        let export = crate::SourceBoundArithmeticObligation::x86_body_export_for_tests(&paired)
            .with_x86_body_pairing(X86ExportPairing::Paired(Some(std::sync::Arc::new(forged))));
        assert!(export.check_x86_body_pairing().is_err(), "{label}");
        assert!(export.replayed_obligations().is_err(), "{label}");
    }
    // No record.
    let absent = owner("absent", &source, &machine).with_pairing_record(None);
    let refusal = absent.check_pairing().expect_err("no record");
    assert!(refusal.contains("without its pairing record"), "{refusal}");
    let export = crate::SourceBoundArithmeticObligation::x86_body_export_for_tests(&paired)
        .with_x86_body_pairing(X86ExportPairing::Paired(None));
    assert!(export.check_x86_body_pairing().is_err());
    assert!(export.replayed_obligations().is_err());
    // A statement the record does not spell.
    let unpaired = paired
        .statement_of(X86Theorem::Unpaired)
        .expect("its arbiter");
    let mut fewer = paired.obligation().clone();
    fewer.preconditions.pop();
    let mut changed = paired.obligation().clone();
    changed.aarch64_expr = E::bool_const(true).and_expr(changed.aarch64_expr);
    for (label, statement) in [
        ("the theorem without the pairing", unpaired.as_ref()),
        ("a premise dropped", &fewer),
        ("a claim changed", &changed),
    ] {
        let refusal = record.check(statement).expect_err(label);
        assert!(refusal.contains("not the spelling"), "{label}: {refusal}");
    }
}

/// OD-205's shift keys are 32- and 64-bit ones only: there x86 masks CL to
/// log2 of the width, which is what the barrel reads. At 8 and 16 bits x86
/// masks it to 5 bits (`shl al, cl` with CL = 8 is zero; a 3-stage barrel
/// leaves AL whole), so no key of those widths is admitted.
#[test]
fn a_shift_key_is_a_32_or_64_bit_one() {
    for op in [ShiftOp::Shl, ShiftOp::Lshr, ShiftOp::Ashr] {
        for bits in [8u32, 16, 32, 64] {
            let key = ArithKey::shift(op, bits);
            let admitted = key.admits(&E::var("v", bits), &E::var("k", 8));
            assert_eq!(admitted, matches!(bits, 32 | 64), "{op:?} at {bits}");
        }
    }
}

/// An 8- or 16-bit variable shift row (`shr al, cl`) is refused by name:
/// x86 masks its count to 5 bits, not to log2 of its width, which the walk's
/// barrel reads; the walk states variable shifts at 32 and 64 bits only.
#[test]
fn a_narrow_variable_shift_row_is_refused_by_name() {
    for (bits, base) in [(8u32, GPR8_ALIAS_BASE), (16, GPR16_ALIAS_BASE)] {
        let (source, mut machine) = slice23_pair(Shape23::ShrClPaired);
        let shr = find(&machine, X86Opcode::ShrRR)[0];
        // `shr al, dil` (`ax`, `di`): RAX's and RDI's aliases.
        let alias = |root: u16| O::PReg(X86PReg::new(base + root));
        inst_mut(&mut machine, shr).operands = vec![alias(0), alias(7)];
        let refusal = source_bound_x86_body(&source, &machine, SYSV)
            .err()
            .unwrap_or_else(|| panic!("a {bits}-bit variable shift was stated"));
        let named = format!("is a {bits}-bit variable shift");
        assert!(
            matches!(
                &refusal,
                X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineRow { row, detail })
                    if *row == shr && detail.contains(&named)
            ),
            "{bits} bits: {refusal}"
        );
    }
}

/// The clean-bool walk pairs its rows too: `ShrClCleanBool` (a bool
/// parameter and a bool result) states the psABI walk and the clean-bool
/// walk, each with its own name for the machine's shift (one barrel once
/// value-numbered, apart from the source's) when nothing is paired. Paired
/// in both, every machine barrel is the source's, one term. Pairing only the
/// psABI walk (the mutant `pair-psabi-walk-only`) leaves the clean-bool
/// walk's barrel apart. Both theorems hold.
#[test]
fn the_clean_bool_walk_pairs_its_rows_too() {
    let (source, machine) = slice23_pair(Shape23::ShrClCleanBool);
    let owner = owner("ShrClCleanBool", &source, &machine);
    assert!(owner.is_paired() && owner.has_unpaired());
    let query = text(owner.obligation());
    let unpaired = unpaired_text(&source, &machine);
    let stage_tests = |query: &str| query.matches("((_ extract 5 5)").count();
    assert!(
        stage_tests(&unpaired) >= 2,
        "the theorem without the pairing states the source's barrel and the machine's\n{unpaired}"
    );
    assert!(
        stage_tests(&query) <= 1,
        "a machine barrel stays apart from the source's\n{query}\n-- unpaired\n{unpaired}"
    );
    assert!(holds_on_samples(owner.obligation()), "{query}");
    assert!(
        holds_on_samples(&with_arithmetic_pairing(false, || {
            self::owner("unpaired", &source, &machine)
                .obligation()
                .clone()
        })),
        "{unpaired}"
    );
}

// ---------------------------------------------------------------------------
// OD-205: the arbiter of a theorem stated in parts
// ---------------------------------------------------------------------------

/// `fn(a: i64, b: i64, p: *mut i64) -> i64 { let mut acc = a % b; for i in
/// 0..90 { acc = (acc ^ (acc << 3)) + k_i; p[i] = acc } acc }` (both of
/// rustc's checks before the remainder; the chain in a block of its own,
/// slice 16's `LongChain`, where the planner finds its clean cuts): past the
/// single-query bounds, so the production owner states it in parts. Its `idiv` pairs only inside
/// [`with_signed_division_pairing`] (tests only), where the divisor claim
/// fails at -1: the paired part stating it is refuted, and the theorem
/// without the pairing, in its own parts, decides (OD-205's arbiter).
pub(crate) fn srem_in_parts_pair() -> (Function, X86ISelFunction) {
    let name = "s23_srem_in_parts".to_owned();
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice23_parts");
    let params = vec![Ty::I64, Ty::I64, Ty::PtrMut(Box::new(Ty::I64))];
    let signature = builder.add_func_type(params.clone(), vec![Ty::I64]);
    let mut f = builder.function(name.clone(), signature);
    let entry = f.create_block();
    let args: Vec<V> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    trap_if_zero(&mut f, Ty::I64, args[1]);
    let (check, trap, go) = (f.create_block(), f.create_block(), f.create_block());
    let min = f.iconst(Ty::I64, i128::from(i64::MIN));
    let is_min = f.icmp(ICmpOp::Eq, Ty::I64, args[0], min);
    f.condbr(is_min, check, vec![], go, vec![]);
    f.switch_to_block(check);
    let minus_one = f.iconst(Ty::I64, -1);
    let is_minus_one = f.icmp(ICmpOp::Eq, Ty::I64, args[1], minus_one);
    f.condbr(is_minus_one, trap, vec![], go, vec![]);
    f.switch_to_block(trap);
    f.unreachable();
    f.switch_to_block(go);
    let remainder = f.binop(BinOp::SRem, Ty::I64, args[0], args[1]);
    let chain = f.create_block();
    let mut acc = f.add_block_param(chain, Ty::I64);
    f.br(chain, vec![remainder]);
    f.switch_to_block(chain);
    for i in 0..90u64 {
        let three = f.iconst(Ty::I64, 3);
        let shifted = f.binop(BinOp::Shl, Ty::I64, acc, three);
        let mixed = f.binop(BinOp::Xor, Ty::I64, acc, shifted);
        let constant = f.iconst(Ty::I64, i128::from(0x9e37 + 7 * i));
        acc = f.add(Ty::I64, mixed, constant);
        let at = f.gep_byte_offset(args[2], 8 * i);
        f.store(Ty::I64, at, acc);
    }
    f.ret(vec![acc]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"));
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// The arbiter in parts, on samples: the production owner states
/// [`srem_in_parts_pair`] in parts, unpaired; paired (tests only), one of its
/// parts is refuted on samples (the divisor claim at -1), every part of the
/// theorem without the pairing holds, and those parts are its own split, not
/// the paired theorem's (the mutant `unpaired-units-are-paired` fails here).
#[test]
fn a_refuted_paired_theorem_in_parts_has_an_unpaired_theorem_in_parts() {
    let (source, machine) = srem_in_parts_pair();
    let production = owner("SremInParts", &source, &machine);
    assert!(production.is_stated_in_parts() && !production.is_paired());
    let owner = with_signed_division_pairing(|| owner("SremInParts", &source, &machine));
    assert!(owner.is_stated_in_parts() && owner.is_paired() && owner.has_unpaired());
    let paired = owner.replayed_units_of(X86Theorem::Paired);
    let unpaired = owner.replayed_units_of(X86Theorem::Unpaired);
    assert!(
        paired.iter().any(|part| refuted_on_samples(part)),
        "no paired part is refuted"
    );
    // The theorem without the pairing is stated in parts, its own split (a
    // region whose claims are identities once value-numbered, here every
    // region of the chain, is no part), never the paired theorem's parts.
    assert!(!unpaired.is_empty() && owner.parts_of(X86Theorem::Unpaired).is_some());
    assert_ne!(unpaired, paired, "the paired theorem's parts");
    eprintln!(
        "SLICE23_IN_PARTS paired parts={} unpaired parts={}",
        paired.len(),
        unpaired.len()
    );
    for (k, part) in unpaired.iter().enumerate() {
        assert!(holds_on_samples(part), "unpaired part {}", k + 1);
    }
    assert!(owner.check_parts_of(X86Theorem::Unpaired).is_ok());
    assert_eq!(
        owner.statement_of(X86Theorem::Unpaired).as_deref(),
        Some(production.obligation())
    );
    assert_eq!(unpaired, production.replayed_units());
}

// ---------------------------------------------------------------------------
// OD-206: the generalization
// ---------------------------------------------------------------------------

/// Every arithmetic node the generalization abstracts, by kind; and the near
/// misses it leaves: a product or division by a constant, a single shift
/// stage, a barrel whose stages test two amounts.
#[test]
fn the_arithmetic_nodes_are_the_keys() {
    let (x, y, k) = (E::var("x", 64), E::var("y", 64), E::var("k", 32));
    let node = |expr: &E| normal::is_arithmetic_node(expr).expect("in the vocabulary");
    for expr in [
        x.clone().bvmul(y.clone()),
        x.clone().zero_ext(64).bvmul(y.clone().zero_ext(64)),
        x.clone().sign_ext(64).bvmul(y.clone().sign_ext(64)),
        x.clone().bvudiv(y.clone()),
        x.clone().bvurem(y.clone()),
        x.clone().bvsdiv(y.clone()),
    ] {
        assert!(node(&expr), "{expr}");
    }
    for op in [ShiftOp::Shl, ShiftOp::Lshr, ShiftOp::Ashr] {
        for bits in [8u32, 16, 32, 64] {
            let value = E::var("v", bits);
            let barrel = shift_modulo_width(op, value.clone(), k.clone());
            assert!(node(&barrel), "{op:?} at {bits}: {barrel}");
            // After the canonical spelling too.
            let spelled =
                normal::normalized_term(&barrel, normal::Groups::CANONICAL).expect("spelled");
            assert!(node(&spelled), "{op:?} at {bits}, spelled: {spelled}");
        }
    }
    let ten = E::bv_const(10, 64);
    for expr in [
        x.clone().bvmul(ten.clone()),
        ten.clone().bvmul(y.clone()),
        x.clone().bvudiv(ten.clone()),
        x.clone().bvurem(ten.clone()),
        // One stage of a barrel.
        E::ite(
            k.clone().extract(0, 0).eq_expr(E::bv_const(1, 1)),
            x.clone().extract(63, 1).zero_ext(1),
            x.clone(),
        ),
    ] {
        assert!(!node(&expr), "{expr}");
    }
    // Two stages testing two amounts.
    let other = E::var("j", 32);
    let inner = E::ite(
        k.clone().extract(0, 0).eq_expr(E::bv_const(1, 1)),
        x.clone().extract(63, 1).zero_ext(1),
        x.clone(),
    );
    let mixed = E::ite(
        other.extract(1, 1).eq_expr(E::bv_const(1, 1)),
        inner.clone().extract(63, 2).zero_ext(2),
        inner,
    );
    assert!(!node(&mixed), "{mixed}");
}

/// Re-derive the generalization of `obligation` and check it is an
/// instantiation: with each leaf at the value its node computes (the
/// original definitions evaluated first), every definition the
/// generalization keeps has the original's value and its claims have the
/// original's value, on slice 9's samples.
fn assert_instantiation(obligation: &ProofObligation, what: &str) -> Option<ProofObligation> {
    use crate::smt::{EvalEnv, EvalResult};
    let (general, nodes) = split::generalize_traced(obligation).ok()?;
    let free: Vec<(String, u32)> = free_inputs_of(obligation);
    let definitions = |o: &ProofObligation| -> Vec<(String, E)> {
        o.preconditions
            .iter()
            .rev()
            .map(|premise| match premise {
                E::Eq { lhs, rhs } => match lhs.as_ref() {
                    E::Var { name, .. } => (name.clone(), rhs.as_ref().clone()),
                    _ => panic!("{premise}"),
                },
                _ => panic!("{premise}"),
            })
            .collect()
    };
    let original = definitions(obligation);
    let kept = definitions(&general);
    let leaves: HashMap<String, E> = nodes.into_iter().collect();
    let instantiate = |expr: &E| -> E { subst(expr, &leaves) };
    let value = |expr: &E, env: &EvalEnv| match expr.eval(env) {
        EvalResult::Bv(v) => u128::from(v),
        EvalResult::Bv128(v) => v,
        EvalResult::Bool(b) => u128::from(b),
        other => panic!("{what}: {expr}: {other:?}"),
    };
    for seed in 0..256u64 {
        let mut env = EvalEnv::default();
        let mut state = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(23);
        for (name, width) in &free {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let sampled = match seed % 4 {
                0 => state & 0xff,
                1 => state >> 61,
                _ => state,
            };
            env.insert(name.clone(), crate::smt::mask(sampled, *width));
        }
        let mut values: HashMap<String, u128> = HashMap::new();
        for (name, rhs) in &original {
            let v = value(rhs, &env);
            values.insert(name.clone(), v);
            let v = u64::try_from(v).unwrap_or_else(|_| panic!("{what}: {name} is wider than 64"));
            env.insert(name.clone(), v);
        }
        for (name, rhs) in &kept {
            assert_eq!(
                value(&instantiate(rhs), &env),
                values[name],
                "{what}: {name} differs at sample {seed}"
            );
        }
        let original_holds =
            value(&obligation.trust_ir_expr, &env) == value(&obligation.aarch64_expr, &env);
        let general_holds = value(&instantiate(&general.trust_ir_expr), &env)
            == value(&instantiate(&general.aarch64_expr), &env);
        assert_eq!(
            original_holds, general_holds,
            "{what}: the instantiated generalization's claims differ at sample {seed}"
        );
    }
    Some(general)
}

/// OD-206 is an instantiation on every fixture of every slice that has an
/// arithmetic node (correct lowerings and wrong ones): the generalization
/// with its leaves at their nodes' values is the obligation, on samples; and
/// the generalization of every slice-23 leaf shape exists.
#[test]
fn the_generalization_is_an_instantiation() {
    let mut checked = 0usize;
    let mut obligations: Vec<(String, ProofObligation)> = Vec::new();
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        for (k, unit) in owner.replayed_units().into_iter().enumerate() {
            obligations.push((format!("{shape:?} {k}"), unit.clone()));
        }
    }
    for (label, source, machine) in slice_twenty_three_refutations() {
        if let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) {
            obligations.push((label.to_owned(), owner.obligation().clone()));
        }
    }
    for shape in super::slice22::SLICE_TWENTY_TWO {
        let (source, machine) = super::slice22::slice22_pair(shape);
        if let Ok(owner) = source_bound_x86_body(&source, &machine, SYSV) {
            for (k, unit) in owner.replayed_units().into_iter().enumerate() {
                obligations.push((format!("{shape:?} {k}"), unit.clone()));
            }
        }
    }
    for (label, obligation) in &obligations {
        if assert_instantiation(obligation, label).is_some() {
            checked += 1;
        }
    }
    eprintln!(
        "SLICE23_INSTANTIATION checked={checked} of {}",
        obligations.len()
    );
    for shape in [
        Shape23::U64OverflowingPowLeaf,
        Shape23::ScalarMulLeaf,
        Shape23::U8CarryingMulAdd,
    ] {
        let (source, machine) = slice23_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        assert!(
            owner.replay_generalized(0).is_ok(),
            "{shape:?}: no generalization\n{}",
            text(owner.obligation())
        );
    }
    assert!(checked >= 8, "{checked}");
}

/// The claims of `overflowing_pow`'s and `scalar_mul`'s shapes hold for
/// every value of their arithmetic leaves (each generalization holds on
/// samples): what lets OD-206 credit them where AY bit-blasts a multiplier
/// the claim needs only as a value. (`AlignOffsetU8`'s paired theorem states
/// no arithmetic node at all: OD-205 alone spells its operations alike, and
/// only its count claims remain.)
#[test]
fn the_root_shapes_generalizations_hold() {
    let (source, machine) = slice23_pair(Shape23::AlignOffsetU8);
    let align = owner("AlignOffsetU8", &source, &machine);
    assert!(
        align.replay_generalized(0).is_err(),
        "{}",
        text(align.obligation())
    );
    for shape in [Shape23::U64OverflowingPowLeaf, Shape23::ScalarMulLeaf] {
        let (source, machine) = slice23_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        let general = owner
            .replay_generalized(0)
            .unwrap_or_else(|why| panic!("{shape:?}: {why}"));
        assert!(
            holds_on_samples(general.obligation()),
            "{shape:?}: the generalization is refuted on samples\n{}",
            text(general.obligation())
        );
        assert!(
            general
                .obligation()
                .name
                .ends_with(X86_BODY_GENERALIZED_SUFFIX),
            "{}",
            general.obligation().name
        );
    }
}

/// u8 `carrying_mul_add`'s range fact: its claim needs `hi16(product) = 0`,
/// so its generalization (the two sides' products independent leaves) is
/// refuted on samples while the exact theorem holds. A generalization is
/// therefore never the default spelling (OD-206): it only follows an exact
/// replay that has no verdict, and its satisfying model is no counterexample.
#[test]
fn the_range_fact_generalization_is_satisfiable_and_the_exact_theorem_holds() {
    let (source, machine) = slice23_pair(Shape23::U8CarryingMulAdd);
    let owner = owner("U8CarryingMulAdd", &source, &machine);
    assert!(holds_on_samples(owner.obligation()));
    let general = owner
        .replay_generalized(0)
        .unwrap_or_else(|why| panic!("no generalization: {why}\n{}", text(owner.obligation())));
    assert!(
        refuted_on_samples(general.obligation()),
        "the range fact's generalization holds\n{}",
        text(general.obligation())
    );
}

/// The leaves are numbered in structural first occurrence: definitions in
/// order, children first, then the claims; never in the order the table
/// created the nodes (`comm` creates the first definition's product AFTER
/// the second's).
#[test]
fn the_leaves_are_numbered_by_first_occurrence() {
    let (a, b, c, d) = (
        E::var("a", 64),
        E::var("b", 64),
        E::var("c", 64),
        E::var("d", 64),
    );
    // `s1` multiplies in the order `comm` rewrites (its product is created
    // again, after `s2`'s), `s2` in `comm`'s own order.
    let canonical = |product: E| {
        normal::commuted_after(&E::bool_const(true), &product).expect("in the vocabulary")
    };
    let ab = a.clone().bvmul(b.clone());
    let first = if canonical(ab.clone()) == ab {
        b.clone().bvmul(a.clone())
    } else {
        ab
    };
    let second = canonical(c.clone().bvmul(d.clone()));
    let definitions = vec![
        ("s1".to_owned(), first.bvadd(E::bv_const(1, 64))),
        ("s2".to_owned(), second.bvadd(E::bv_const(2, 64))),
    ];
    let claims = E::var("s1", 64).eq_expr(E::var("s2", 64));
    let general = normal::generalized_after(&E::bool_const(true), &definitions, &claims)
        .expect("generalized");
    let rendered: Vec<String> = general
        .definitions
        .iter()
        .map(|(name, expr)| format!("{name} := {expr}"))
        .collect();
    assert!(
        rendered[0].contains("ar0") && rendered[1].contains("ar1"),
        "{rendered:?}"
    );
}

/// `comm`'s operand order is a function of the operands' structure alone:
/// the same product spelled the same in tables that created its operands in
/// opposite orders, and `a*b` and `b*a` one term.
#[test]
fn the_product_operand_order_is_independent_of_creation_order() {
    let (a, b) = (E::var("a", 64), E::var("b", 64));
    let ab = a.clone().bvmul(b.clone());
    let ba = b.clone().bvmul(a.clone());
    let spellings: Vec<E> = [a.clone(), b.clone()]
        .iter()
        .flat_map(|first| {
            [&ab, &ba]
                .into_iter()
                .map(|product| normal::commuted_after(first, product).expect("spelled"))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(
        spellings.iter().all(|spelled| *spelled == spellings[0]),
        "{spellings:?}"
    );
}

/// Not stated: an obligation with no arithmetic node, or whose generalized
/// claims are all identities (slice 9's rule).
#[test]
fn a_generalization_needs_an_arithmetic_node_and_a_claim() {
    let x = E::var("x", 64);
    let no_node = ProofObligation {
        name: X86_BODY_OBLIGATION_NAME.into(),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: x
            .clone()
            .bvadd(E::bv_const(1, 64))
            .eq_expr(E::var("m0", 64)),
        inputs: vec![("x".into(), 64), ("m0".into(), 64)],
        preconditions: vec![],
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    assert!(split::generalize(&no_node).is_err());
    // `s0 := x*y`, `m0 := x*y` (two definitions, one node): the claim
    // `s0 = m0` is the identity `ar0 = ar0`.
    let y = E::var("y", 64);
    let identity = ProofObligation {
        aarch64_expr: E::var("s0", 64).eq_expr(E::var("m0", 64)),
        inputs: vec![
            ("x".into(), 64),
            ("y".into(), 64),
            ("s0".into(), 64),
            ("m0".into(), 64),
        ],
        preconditions: vec![
            E::var("m0", 64).eq_expr(y.clone().bvmul(x.clone())),
            E::var("s0", 64).eq_expr(x.clone().bvmul(y.clone())),
        ],
        ..no_node.clone()
    };
    assert!(
        split::generalize(&identity).is_err(),
        "{:?}",
        split::generalize(&identity).map(|o| text(&o))
    );
}

/// THE verdict rule of a generalization (OD-206, OD-200's rule): a Valid
/// generalization credits an obligation whose exact replay had no verdict;
/// a refuted generalization neither credits nor refutes (the exact outcome
/// stands, with the reason); an exact Valid or refuted replay is never
/// replaced.
#[test]
fn the_generalization_verdict_rule() {
    use crate::function_request::x86_generalized_verdict;
    let refuted = || {
        Some(VerificationResult::Invalid {
            counterexample: "x = 1".into(),
        })
    };
    let none = || (None, Some("timeout".to_owned()));
    let valid = || (Some(VerificationResult::Valid), None);
    let (verdict, why, credited) = x86_generalized_verdict(none(), valid());
    assert!(matches!(verdict, Some(VerificationResult::Valid)) && why.is_none() && credited);
    let (verdict, why, credited) = x86_generalized_verdict(none(), (refuted(), None));
    assert!(
        verdict.is_none(),
        "a satisfiable generalization refutes nothing"
    );
    assert!(!credited);
    assert!(
        why.as_deref()
            .is_some_and(|why| why.starts_with("timeout; generalized (OD-206)")),
        "{why:?}"
    );
    let (verdict, _, credited) = x86_generalized_verdict(none(), (None, None));
    assert!(verdict.is_none() && !credited);
    let (verdict, _, credited) = x86_generalized_verdict((refuted(), None), valid());
    assert!(
        matches!(verdict, Some(VerificationResult::Invalid { .. })) && !credited,
        "an exact refutation is never generalized"
    );
    let (verdict, _, credited) = x86_generalized_verdict(valid(), (refuted(), None));
    assert!(matches!(verdict, Some(VerificationResult::Valid)) && !credited);
}

/// The generalization record is re-derived by every consumer: an export
/// whose record names the obligation's generalization checks and publishes
/// it in the obligation's place; a record whose generalization was changed
/// (a definition, a claim, a leaf), or that names a generalization AND a
/// claim split of one obligation, is refused.
#[test]
fn a_forged_generalization_record_is_refused() {
    let (source, machine) = slice23_pair(Shape23::ScalarMulLeaf);
    let owner = owner("ScalarMulLeaf", &source, &machine);
    assert!(!owner.is_stated_in_parts());
    let general = owner.replay_generalized(0).expect("a generalization");
    let export = crate::SourceBoundArithmeticObligation::x86_body_export_for_tests(&owner);
    let record = |whole: ProofObligation| {
        X86BodyClaims::new(vec![None]).with_generalized(vec![X86UnitGeneralized::whole(whole)])
    };
    let good = export.with_x86_body_claims(record(general.obligation().clone()));
    assert!(good.check_x86_body_claims().is_ok());
    assert!(good.check_x86_body_generalized().is_ok());
    let published = good.replayed_obligations().expect("the record checks");
    assert_eq!(published, vec![general.obligation()]);
    let forged: Vec<ProofObligation> = {
        let mut changed_claim = general.obligation().clone();
        changed_claim.aarch64_expr = E::bool_const(true).and_expr(changed_claim.aarch64_expr);
        let mut fewer_premises = general.obligation().clone();
        fewer_premises.preconditions.pop();
        let mut renamed = general.obligation().clone();
        renamed.name = owner.obligation().name.clone();
        vec![changed_claim, fewer_premises, renamed]
    };
    for (k, bad) in forged.into_iter().enumerate() {
        let export = export.with_x86_body_claims(record(bad));
        assert!(export.check_x86_body_claims().is_err(), "forgery {k}");
        assert!(export.check_x86_body_generalized().is_err(), "forgery {k}");
        assert!(export.replayed_obligations().is_err(), "forgery {k}");
    }
    // Generalized whole and split claim by claim at once.
    if let Ok(claims) = owner.replay_claims(0) {
        let both = X86BodyClaims::new(vec![Some(
            claims
                .iter()
                .map(|claim| claim.obligation().clone())
                .collect(),
        )])
        .with_generalized(vec![X86UnitGeneralized::whole(
            general.obligation().clone(),
        )]);
        assert!(
            export
                .with_x86_body_claims(both)
                .check_x86_body_claims()
                .is_err()
        );
    }
}

/// The negative memo's key carries the generalization route: a replay of
/// the same bytes as a generalization is another key.
#[test]
fn the_generalization_is_a_replay_route_of_its_own() {
    let (source, machine) = slice23_pair(Shape23::ScalarMulLeaf);
    let owner = owner("ScalarMulLeaf", &source, &machine);
    let general = owner.replay_generalized(0).expect("a generalization");
    use crate::source_bound_replay::SourceBoundReplay;
    assert!(general.generalized() && general.fresh_after_resident_timeout());
    assert!(!owner.generalized());
}

// ---------------------------------------------------------------------------
// The golden text
// ---------------------------------------------------------------------------

/// The golden text of every slice-23 fixture: its theorem, and (a shape
/// with one) its generalization.
pub(crate) fn slice_twenty_three_snapshots() -> String {
    let mut rendered = String::new();
    for shape in SLICE_TWENTY_THREE {
        let (source, machine) = slice23_pair(shape);
        let owner = owner(&format!("{shape:?}"), &source, &machine);
        rendered.push_str(&format!(";;;; {shape:?}\n{}\n", text(owner.obligation())));
        if let Ok(general) = owner.replay_generalized(0) {
            rendered.push_str(&format!(
                ";;;; {shape:?} | generalized\n{}\n",
                text(general.obligation())
            ));
        }
    }
    rendered
}

/// The reviewed digest of the slice-23 golden text.
const SLICE_TWENTY_THREE_SNAPSHOT_SHA256: &str =
    "60e5b2e22d619b7f45da9a29c1ed2202766c9a5c1fc0b86b2e9d9c0ed33cc847";

/// The rendered theorems of every slice-23 fixture are the reviewed golden
/// text, pinned by digest.
#[test]
fn slice_twenty_three_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body/slice23_snapshots.smt2");
    let rendered = slice_twenty_three_snapshots();
    let digest = format!("{:x}", Sha256::digest(rendered.as_bytes()));
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWENTY_THREE_SNAPSHOT_SHA256 to {digest} and \
             re-run without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display()
        );
    }
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    assert_eq!(rendered, golden, "slice23_snapshots.smt2 drifted");
    assert_eq!(digest, SLICE_TWENTY_THREE_SNAPSHOT_SHA256);
}
