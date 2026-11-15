// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The x86-64 selector's constant-amount `I128` shift fold (ruling OD-215)
//! under the source-bound body theorem. A 128-bit `Ishl`, `Ushr` or `Sshr` by
//! a constant amount trust-ir defines (below 128) is selected as immediate
//! shifts of the 64-bit halves, an `or` and moves, with no count register,
//! compare or `cmov`:
//!
//! ```text
//! k == 0      : two copies
//! 0 < k < 64  : shl/shr imm of each half, the other half's spill, an or
//! k == 64     : a move of one half and a fill (0, or sar 63 of the high half)
//! 64 < k < 128: one shift of the other half by k - 64 and the fill
//! ```
//!
//! Every row is one slice 1 and slice 11 already admit (`mov`, `mov imm`,
//! `shl`/`shr`/`sar r64, imm8` with the 6-bit count mask, `or`), so the
//! theorem gains no row kind: what this module adds is fixtures of every
//! case on the real selector and the wrong lowerings the theorem must refute
//! (a wrong half, a wrong fill, an amount off by one).
//!
//! Fixtures are real: LIR from the trust-ir adapter (the count spelled as the
//! rustc bridge spells a constant 128-bit amount: an in-range constant at the
//! shifted value's type) and the machine stream from the real x86-64
//! instruction selector (`super::select`). Every test here runs without a
//! solver; the replay on AY and Clean and the verifier-credit tests are in
//! `i128_const_shift_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice11::{eval_word, evaluate_premises, holds_at_pool};
use super::slice11::{theorem_holds, theorem_refuted};
use super::*;

/// The three 128-bit shifts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ShiftKind {
    /// `Ishl` of a `u128`.
    Shl,
    /// `Ushr` of a `u128`.
    Lshr,
    /// `Sshr` of an `i128`.
    Ashr,
}

impl ShiftKind {
    const ALL: [ShiftKind; 3] = [ShiftKind::Shl, ShiftKind::Lshr, ShiftKind::Ashr];

    fn ty(self) -> Ty {
        match self {
            Self::Ashr => Ty::I128,
            _ => Ty::U128,
        }
    }

    fn op(self) -> BinOp {
        match self {
            Self::Shl => BinOp::Shl,
            Self::Lshr => BinOp::LShr,
            Self::Ashr => BinOp::AShr,
        }
    }

    /// Rust's shift of the 128-bit pattern `x` by `amount` (below 128).
    pub(crate) fn rust(self, x: u128, amount: u32) -> u128 {
        match self {
            Self::Shl => x << amount,
            Self::Lshr => x >> amount,
            Self::Ashr => ((x as i128) >> amount) as u128,
        }
    }
}

/// One fixture: `fn(a: u128) -> u128 { a << k }` (or `a >> k`, or
/// `(a: i128) >> k`), or with `truncated` the result's low limb only,
/// `fn(a: u128) -> u64 { (a >> k) as u64 }`: the high-limb extraction of
/// `u128::widening_mul`, `carrying_mul` and Display at `k == 64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ConstShift {
    pub(crate) kind: ShiftKind,
    pub(crate) amount: u32,
    pub(crate) truncated: bool,
}

impl ConstShift {
    const fn new(kind: ShiftKind, amount: u32) -> Self {
        Self {
            kind,
            amount,
            truncated: false,
        }
    }

    /// The fixture's label (and function name): `Lshr64`, `Lshr64AsU64`.
    pub(crate) fn label(self) -> String {
        format!(
            "{:?}{}{}",
            self.kind,
            self.amount,
            if self.truncated { "AsU64" } else { "" }
        )
    }
}

/// The amounts of the case split: zero, both ends below 64, 64, both ends
/// above it.
pub(crate) const AMOUNTS: [u32; 6] = [0, 1, 63, 64, 65, 127];

/// Every fixture: each shift by each of [`AMOUNTS`], then the high-limb
/// extraction.
pub(crate) fn const_shift_fixtures() -> Vec<ConstShift> {
    let mut fixtures = Vec::new();
    for kind in ShiftKind::ALL {
        for amount in AMOUNTS {
            fixtures.push(ConstShift::new(kind, amount));
        }
    }
    fixtures.push(ConstShift {
        truncated: true,
        ..ConstShift::new(ShiftKind::Lshr, 64)
    });
    fixtures
}

/// The LIR the trust-ir adapter produces for `shape`, named `name`.
pub(crate) fn const_shift_lir_named(shape: ConstShift, name: &str) -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_i128_const_shift");
    let ty = shape.kind.ty();
    let result = if shape.truncated { Ty::U64 } else { ty.clone() };
    let signature = builder.add_func_type(vec![ty.clone()], vec![result.clone()]);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    // The count as the rustc bridge spells a constant 128-bit amount: the
    // constant, reduced to `[0, 127]`, at the shifted value's type
    // (`emit_typed_const(.., lhs_trust_ir_ty, raw & 127)`).
    let count = f.iconst(ty.clone(), i128::from(shape.amount));
    let shifted = f.binop(shape.kind.op(), ty.clone(), a, count);
    let value = if shape.truncated {
        f.trunc(ty, Ty::U64, shifted)
    } else {
        shifted
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
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn const_shift_lir(shape: ConstShift) -> Function {
    const_shift_lir_named(shape, &shape.label())
}

/// The fixture's LIR and the real selector's pre-RA stream (the fold on).
pub(crate) fn const_shift_pair(shape: ConstShift) -> (Function, X86ISelFunction) {
    let source = const_shift_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
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

/// The walk ordinal of the first row satisfying `predicate`.
#[track_caller]
fn row_where(machine: &X86ISelFunction, predicate: impl Fn(&X86ISelInst) -> bool) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| predicate(inst(machine, *ordinal)))
        .unwrap_or_else(|| panic!("no such row\n{}", describe(machine)))
}

/// The registers the entry copies the parameter's two halves into: `(lo,
/// hi)`, the destinations of the copies of RDI and RSI.
fn parameter_halves(machine: &X86ISelFunction) -> (O, O) {
    let half = |root: u16| {
        let copy = row_where(machine, |i| {
            i.opcode == X86Opcode::MovRR && i.operands.get(1) == Some(&preg(root))
        });
        inst(machine, copy).operands[0].clone()
    };
    (half(RDI), half(RSI))
}

/// The shift rows (by opcode) the fold emits for `kind` by `amount`.
fn folded_shift_rows(kind: ShiftKind, amount: u32) -> Vec<(X86Opcode, usize)> {
    use X86Opcode::{OrRR, SarRI, ShlRI, ShrRI};
    match (kind, amount) {
        (_, 0) => vec![],
        (ShiftKind::Shl, 1..=63) => vec![(ShlRI, 2), (ShrRI, 1), (OrRR, 1)],
        (ShiftKind::Lshr, 1..=63) => vec![(ShrRI, 2), (ShlRI, 1), (OrRR, 1)],
        (ShiftKind::Ashr, 1..=63) => vec![(ShrRI, 1), (ShlRI, 1), (OrRR, 1), (SarRI, 1)],
        (ShiftKind::Shl | ShiftKind::Lshr, 64) => vec![],
        (ShiftKind::Shl, _) => vec![(ShlRI, 1)],
        (ShiftKind::Lshr, _) => vec![(ShrRI, 1)],
        (ShiftKind::Ashr, 64) => vec![(SarRI, 1)],
        (ShiftKind::Ashr, _) => vec![(SarRI, 2)],
    }
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

/// Each fixture's stream is the fold's: its shift rows exactly the case
/// split's, no shift by CL, no compare, no `cmov` and no subtract; with the
/// fold off the same source takes the general path (three `cmov`s).
#[test]
fn every_constant_shift_fixture_selects_the_folded_rows() {
    for shape in const_shift_fixtures() {
        let (source, machine) = const_shift_pair(shape);
        let text = format!("{shape:?}\n{}{}", describe_lir(&source), describe(&machine));
        for opcode in [
            X86Opcode::Cmovcc,
            X86Opcode::CmpRI,
            X86Opcode::SubRR,
            X86Opcode::ShlRR,
            X86Opcode::ShrRR,
            X86Opcode::SarRR,
        ] {
            assert!(find(&machine, opcode).is_empty(), "{opcode:?}: {text}");
        }
        for opcode in [
            X86Opcode::ShlRI,
            X86Opcode::ShrRI,
            X86Opcode::SarRI,
            X86Opcode::OrRR,
        ] {
            let want = folded_shift_rows(shape.kind, shape.amount)
                .into_iter()
                .find(|(row, _)| *row == opcode)
                .map_or(0, |(_, count)| count);
            assert_eq!(find(&machine, opcode).len(), want, "{opcode:?}: {text}");
        }
        let general = super::with_i128_const_shift_fold(false, || {
            select(&const_shift_lir(shape), X86CallAbi::SystemV)
        });
        assert_eq!(find(&general, X86Opcode::Cmovcc).len(), 3, "{shape:?}");
    }
}

/// The owner binds every value row of every fixture, the structural check
/// it ran passes, the theorem is genuinely proven (not degenerate), and
/// every name it defines is at most 64 bits wide.
#[test]
fn owner_binds_every_row_of_every_constant_shift() {
    for shape in const_shift_fixtures() {
        let (source, machine) = const_shift_pair(shape);
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
        let entries = free_inputs_of(body.obligation());
        assert_eq!(
            owner_check(&source, &machine, body.obligation(), &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(body.obligation().is_genuinely_proven(), "{shape:?}");
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
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
fn constant_shift_theorems_hold_on_samples() {
    for shape in const_shift_fixtures() {
        let (source, machine) = const_shift_pair(shape);
        let obligation = owner(&source, &machine, &shape.label());
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// Edge and patterned 64-bit halves: both sign bits set and clear, the limb
/// boundary, patterns and seeded words.
fn halves() -> Vec<u64> {
    let mut values = vec![
        0,
        1,
        2,
        u64::MAX,
        u64::MAX - 1,
        1 << 63,
        (1 << 63) - 1,
        (1 << 63) | 1,
        0x5555_5555_5555_5555,
        0xaaaa_aaaa_aaaa_aaaa,
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
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

/// Each fixture's theorem states Rust's 128-bit shift (its source side at
/// every pair of edge halves, the machine side equal to it being the
/// theorem), each half of the result its own observed item (RAX, then RDX;
/// the truncated fixture RAX alone).
#[test]
fn constant_shift_theorems_state_rusts_shift() {
    let values = halves();
    for shape in const_shift_fixtures() {
        let (source, machine) = const_shift_pair(shape);
        // Each half's item as built (slice 18's spelling), as slice 11 reads
        // them.
        let obligation = with_normal_groups(normal::Groups::NONE, || {
            owner(&source, &machine, &shape.label())
        });
        let items = observable_items(&obligation);
        assert_eq!(
            items.len(),
            if shape.truncated { 1 } else { 2 },
            "{shape:?}"
        );
        for (k, &a_lo) in values.iter().enumerate() {
            for &a_hi in [values[(k * 7 + 3) % values.len()], a_lo ^ (1 << 63)].iter() {
                let fixed = [("e_rdi", a_lo), ("e_rsi", a_hi)];
                let a = (u128::from(a_hi) << 64) | u128::from(a_lo);
                let want = shape.kind.rust(a, shape.amount);
                let premises = evaluate_premises(&obligation, &fixed);
                let got_lo = eval_word(&items[0].0, &premises);
                assert_eq!(got_lo, want as u64, "{shape:?} a={a:#x}");
                if !shape.truncated {
                    let got_hi = eval_word(&items[1].0, &premises);
                    assert_eq!(got_hi, (want >> 64) as u64, "{shape:?} a={a:#x}");
                }
                assert!(
                    super::sides_agree_with(&obligation, k as u64, &fixed),
                    "{shape:?} a={a:#x}"
                );
            }
        }
    }
}

/// Every DEFINED amount (0 to 127) of every shift, beyond the fixtures:
/// with the fold on (the folded rows) and off (the general CL/CMOV path,
/// which a constant the selector does not track still takes), the owner
/// binds the real selection and its theorem holds on pooled samples.
/// Exhaustive in the amount; sampled in the value. Never credit.
#[test]
fn every_defined_amount_is_bound_and_holds_on_samples_with_the_fold_on_and_off() {
    const SAMPLES: u64 = 256;
    let mut checked = 0;
    for kind in ShiftKind::ALL {
        for amount in 0..128 {
            let shape = ConstShift::new(kind, amount);
            let source = const_shift_lir(shape);
            for fold in [true, false] {
                let machine = super::with_i128_const_shift_fold(fold, || {
                    select(&source, X86CallAbi::SystemV)
                });
                assert_eq!(
                    find(&machine, X86Opcode::Cmovcc).is_empty(),
                    fold,
                    "{shape:?} fold={fold}"
                );
                let what = format!("{shape:?} fold={fold}");
                let obligation = owner(&source, &machine, &what);
                assert!(
                    (0..SAMPLES).all(|seed| holds_at_pool(&obligation, seed * 16 + 1)),
                    "{what}\n{}",
                    describe(&machine)
                );
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 3 * 128 * 2);
}

/// An amount trust-ir leaves undefined (128) stays outside the theorem by
/// name, as before the fold, and the selector does not fold it: the
/// general path, three `cmov`s.
#[test]
fn an_undefined_constant_amount_stays_outside_and_unfolded() {
    for kind in ShiftKind::ALL {
        let mut builder = ModuleBuilder::new("x86_source_bound_body_i128_const_shift_outside");
        let ty = kind.ty();
        let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut f = builder.function("by_128", signature);
        let entry = f.create_block();
        let a = f.add_block_param(entry, ty.clone());
        f.switch_to_block(entry);
        let count = f.iconst(ty.clone(), 128);
        let shifted = f.binop(kind.op(), ty, a, count);
        f.ret(vec![shifted]);
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
        .find(|function| function.name == "by_128")
        .expect("translated");
        let machine = select(&source, X86CallAbi::SystemV);
        assert_eq!(find(&machine, X86Opcode::Cmovcc).len(), 3, "{kind:?}");
        let refusal = match source_bound_x86_body(&source, &machine, SYSV) {
            Ok(_) => panic!("{kind:?}: a shift by 128 is admitted"),
            Err(refusal) => refusal.to_string(),
        };
        assert!(
            refusal.contains("shifts by an out-of-range constant amount"),
            "{kind:?}: {refusal}"
        );
    }
}

// ---------------------------------------------------------------------------
// Wrong lowerings the theorem must refute
// ---------------------------------------------------------------------------

/// Each wrong lowering of a fixture, labelled `<fixture>/<mutation>`:
///
/// - `amount-off-by-one`: the real selection of the amount one above (one
///   below at 127) under the fixture's source;
/// - `wrong-fill`: for a right shift by a nonzero amount, the real selection
///   of the other right shift (zero fill for sign fill, a logical high-limb
///   shift for an arithmetic one, and back); for a left shift by 64 or
///   more, the zeroed low half filled with the sign of the low half
///   (`sar lo, 63`) instead;
/// - `wrong-half`: the first row that reads a half of the parameter reads
///   the other half.
///
/// Every one changes the result for some input, so its theorem must be
/// refuted; `i128_const_shift_qualification` replays each to an AY
/// counterexample.
pub(crate) fn const_shift_refutations() -> Vec<(String, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    for shape in const_shift_fixtures() {
        let label = shape.label();
        let source = const_shift_lir(shape);
        // The amount off by one: the selector's own stream for k +- 1.
        let off = ConstShift {
            amount: if shape.amount == 127 {
                126
            } else {
                shape.amount + 1
            },
            ..shape
        };
        let machine = select(&const_shift_lir_named(off, &label), X86CallAbi::SystemV);
        cases.push((
            format!("{label}/amount-off-by-one"),
            source.clone(),
            machine,
        ));
        // The wrong fill (none the truncated fixture observes: its one item
        // is the low limb, the high half beside it the fill).
        if shape.amount > 0 && shape.kind != ShiftKind::Shl && !shape.truncated {
            let other = ConstShift {
                kind: if shape.kind == ShiftKind::Lshr {
                    ShiftKind::Ashr
                } else {
                    ShiftKind::Lshr
                },
                ..shape
            };
            let machine = select(&const_shift_lir_named(other, &label), X86CallAbi::SystemV);
            cases.push((format!("{label}/wrong-fill"), source.clone(), machine));
        }
        if shape.kind == ShiftKind::Shl && shape.amount >= 64 {
            let (_, mut machine) = const_shift_pair(shape);
            let (lo, _) = parameter_halves(&machine);
            // The fold's zero low half: the LAST `mov r, 0` (the count's
            // high half, a dead `mov r, 0` too, comes before it).
            let zero = rows(&machine)
                .into_iter()
                .map(|(ordinal, _, _)| ordinal)
                .rev()
                .find(|ordinal| {
                    let row = inst(&machine, *ordinal);
                    row.opcode == X86Opcode::MovRI && row.operands.get(1) == Some(&O::Imm(0))
                })
                .unwrap_or_else(|| panic!("{label}: no zero fill\n{}", describe(&machine)));
            let row = inst_mut(&mut machine, zero);
            row.opcode = X86Opcode::SarRI;
            row.flags = X86Opcode::SarRI.default_flags();
            let dst = row.operands[0].clone();
            row.operands = vec![dst, lo, O::Imm(63)];
            cases.push((format!("{label}/wrong-fill"), source.clone(), machine));
        }
        // The wrong half.
        let (_, mut machine) = const_shift_pair(shape);
        let (lo, hi) = parameter_halves(&machine);
        let reader = rows(&machine)
            .into_iter()
            .map(|(ordinal, _, _)| ordinal)
            .find(|ordinal| {
                let row = inst(&machine, *ordinal);
                row.operands.first() != Some(&lo)
                    && row.operands.first() != Some(&hi)
                    && matches!(row.operands.get(1), Some(read) if *read == lo || *read == hi)
            })
            .unwrap_or_else(|| panic!("{label}: no reader of a half\n{}", describe(&machine)));
        let row = inst_mut(&mut machine, reader);
        row.operands[1] = if row.operands[1] == lo {
            hi.clone()
        } else {
            lo.clone()
        };
        cases.push((format!("{label}/wrong-half"), source, machine));
    }
    cases
}

#[test]
fn every_constant_shift_refutation_is_refuted_on_samples() {
    let cases = const_shift_refutations();
    // 19 amounts off by one, 10 right-shift fills (5 nonzero amounts of
    // each), 3 left-shift fills (64, 65 and 127) and 19 wrong halves.
    let labels: Vec<&String> = cases.iter().map(|(label, ..)| label).collect();
    assert_eq!(cases.len(), 19 + 10 + 3 + 19, "{labels:?}");
    for (label, source, machine) in cases {
        let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(
            theorem_refuted(&theorem),
            "{label}: the theorem must refute the wrong lowering\n{}",
            describe(&machine)
        );
    }
}

// ---------------------------------------------------------------------------
// Golden snapshots
// ---------------------------------------------------------------------------

/// SHA-256 of the golden file below. The golden bytes can change only
/// together with this reviewed constant: a regenerated file alone fails.
const I128_CONST_SHIFT_SNAPSHOT_SHA256: &str =
    "7b0563065ca7c4995ae297bdc3c067370a66cbe051d1ff64b8fe65d7ced43138";

/// The exact replayed SMT2 of every fixture, pinned in one golden file whose
/// digest is pinned here; a renamed function renders the same query.
#[test]
fn i128_const_shift_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/i128_const_shift_snapshots.smt2");
    let mut rendered = String::new();
    for shape in const_shift_fixtures() {
        let (source, machine) = const_shift_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {}\n{smt2}\n", shape.label()));
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
            .join("tests/fixtures/x86_source_bound_body/i128_const_shift_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set I128_CONST_SHIFT_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        I128_CONST_SHIFT_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "the constant-shift snapshots drifted");
}
