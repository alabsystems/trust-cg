// trust-cg-opt - Per-pass translation validation tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::pass_manager::MachinePass;
use crate::scheduler::{InstructionScheduler, PressureAwareScheduler};
use trust_cg_ir::regs::{X0, X1};
use trust_cg_ir::{
    AArch64Opcode, InstFlags, InstId, MachFunction, MachInst, MachOperand, RegClass, Signature,
    VReg,
};

fn vreg(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

fn reorderable(mut inst: MachInst) -> MachInst {
    inst.flags.insert(InstFlags::PROOF_REORDERABLE);
    inst
}

fn func_with(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new("pv_test".to_string(), Signature::new(vec![], vec![]));
    let block = func.entry;
    for inst in insts {
        let id = func.push_inst(inst);
        func.append_inst(block, id);
    }
    // Passes refuse a register outside the function's arena.
    func.try_sync_vreg_counter()
        .expect("bounded fixture register arena");
    func
}

/// Replace the entry block's order with `order` (indices into the original
/// order) and validate it against the original.
fn permute(insts: Vec<MachInst>, order: &[usize]) -> ValidationVerdict {
    let mut func = func_with(insts);
    let before = PermutationSnapshot::capture(&func);
    let entry = func.entry;
    let old = func.block(entry).insts.clone();
    func.block_mut(entry).insts = order.iter().map(|&i| old[i]).collect();
    validate_permutation(&before, &func).verdict
}

fn assert_refuted(verdict: &ValidationVerdict, needle: &str) {
    match verdict {
        ValidationVerdict::Refuted(reason) => assert!(
            reason.contains(needle),
            "refutation `{reason}` does not name `{needle}`"
        ),
        other => panic!("expected a refutation naming `{needle}`, got {other:?}"),
    }
}

fn ret() -> MachInst {
    inst(AArch64Opcode::Ret, vec![])
}

#[test]
fn scheduler_output_validates() {
    // Independent chains the list scheduler interleaves.
    let insts = vec![
        inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)]),
        inst(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]),
        inst(AArch64Opcode::MulRR, vec![vreg(3), vreg(11), vreg(12)]),
        inst(AArch64Opcode::AddRR, vec![vreg(4), vreg(2), vreg(3)]),
        inst(AArch64Opcode::StrRI, vec![vreg(4), vreg(10), imm(8)]),
        inst(AArch64Opcode::MulRR, vec![vreg(5), vreg(13), vreg(14)]),
        ret(),
    ];
    let mut reordered = 0;
    for pressure in [false, true] {
        let mut func = func_with(insts.clone());
        let before = PermutationSnapshot::capture(&func);
        let changed = if pressure {
            PressureAwareScheduler.run(&mut func)
        } else {
            InstructionScheduler.run(&mut func)
        };
        reordered += usize::from(changed);
        let outcome = validate_permutation(&before, &func);
        assert_eq!(
            outcome.verdict,
            ValidationVerdict::Validated,
            "pressure={pressure} changed={changed}"
        );
    }
    assert!(reordered > 0, "a scheduler reorders this block");
}

#[test]
fn identity_permutation_validates() {
    let insts = vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        inst(AArch64Opcode::MovI, vec![vreg(2), imm(2)]),
        ret(),
    ];
    assert_eq!(permute(insts, &[0, 1, 2]), ValidationVerdict::Validated);
}

#[test]
fn independent_instructions_may_swap() {
    let insts = vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        inst(AArch64Opcode::MovI, vec![vreg(2), imm(2)]),
        ret(),
    ];
    assert_eq!(permute(insts, &[1, 0, 2]), ValidationVerdict::Validated);
}

#[test]
fn corruption_use_before_its_definition_is_refuted() {
    let insts = vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        inst(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(1)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "read-after-write");
}

#[test]
fn corruption_redefinition_before_an_earlier_read_is_refuted() {
    // Phi-resolution copies: `v20 = v21; v21 = v23` must not swap.
    let insts = vec![
        inst(AArch64Opcode::MovR, vec![vreg(20), vreg(21)]),
        inst(AArch64Opcode::MovR, vec![vreg(21), vreg(23)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "write-after-read");
}

#[test]
fn corruption_dependent_store_then_load_reordered_is_refuted() {
    // A store and a load of the same bytes: the load must stay after it.
    let insts = vec![
        inst(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]),
        inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(0)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "memory dependence reversed");
}

#[test]
fn corruption_dependent_load_then_store_reordered_is_refuted() {
    let insts = vec![
        inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(0)]),
        inst(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "memory dependence reversed");
}

#[test]
fn reorderable_loads_may_swap_but_ordinary_loads_may_not() {
    let proven = vec![
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)])),
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(8)])),
        ret(),
    ];
    assert_eq!(permute(proven, &[1, 0, 2]), ValidationVerdict::Validated);
    let ordinary = vec![
        inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)]),
        inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(8)]),
        ret(),
    ];
    assert_refuted(&permute(ordinary, &[1, 0, 2]), "memory");
}

#[test]
fn corruption_reorderable_load_sunk_past_a_later_store_is_refuted() {
    // A proof-reorderable load is unordered only against other such loads
    // (and a proven-disjoint earlier store): it may not move after the next
    // ordered access, here a store to the very bytes it reads. No register
    // links the two, so only the memory rule can refuse this.
    let insts = vec![
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)])),
        inst(AArch64Opcode::StrRI, vec![vreg(2), vreg(10), imm(0)]),
        ret(),
    ];
    assert_refuted(&permute(insts.clone(), &[1, 0, 2]), "memory");
    assert_eq!(permute(insts, &[0, 1, 2]), ValidationVerdict::Validated);
    // The same holds behind another reorderable load the store follows.
    let behind = vec![
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)])),
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(3), vreg(10), imm(8)])),
        inst(AArch64Opcode::StrRI, vec![vreg(2), vreg(10), imm(0)]),
        ret(),
    ];
    assert_eq!(
        permute(behind.clone(), &[1, 0, 2, 3]),
        ValidationVerdict::Validated
    );
    assert_refuted(&permute(behind, &[1, 2, 0, 3]), "memory");
}

#[test]
fn proven_disjoint_store_load_may_swap_only_when_disjoint() {
    let disjoint = vec![
        reorderable(inst(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)])),
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(8)])),
        ret(),
    ];
    assert_eq!(permute(disjoint, &[1, 0, 2]), ValidationVerdict::Validated);
    let overlapping = vec![
        reorderable(inst(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)])),
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(4)])),
        ret(),
    ];
    assert_refuted(&permute(overlapping, &[1, 0, 2]), "memory");
    // Same operand, but the base is redefined between: a different address.
    let rebased = vec![
        reorderable(inst(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)])),
        inst(AArch64Opcode::AddRI, vec![vreg(10), vreg(11), imm(8)]),
        reorderable(inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(8)])),
        ret(),
    ];
    assert_refuted(&permute(rebased, &[0, 2, 1, 3]), "read-after-write");
}

#[test]
fn corruption_flag_reader_before_its_writer_is_refuted() {
    let insts = vec![
        inst(AArch64Opcode::CmpRR, vec![vreg(1), vreg(2)]),
        inst(AArch64Opcode::CSet, vec![vreg(3), imm(0)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "Flags read-after-write");
}

#[test]
fn corruption_load_hoisted_above_a_trap_carrier_is_refuted() {
    let insts = vec![
        inst(AArch64Opcode::TrapBoundsCheckExact, vec![vreg(1), vreg(2)]),
        inst(AArch64Opcode::LdrRO, vec![vreg(3), vreg(10), vreg(1)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "fence");
}

#[test]
fn corruption_work_moved_across_a_call_is_refuted() {
    let call = inst(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("callee".to_string())],
    );
    let insts = vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        call,
        inst(AArch64Opcode::MovI, vec![vreg(2), imm(2)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[0, 2, 1, 3]), "fence");
}

#[test]
fn corruption_fixed_register_read_delayed_past_a_virtual_definition_is_refuted() {
    // `v1 = copy x0` must read x0 before any virtual definition the
    // allocator could place in x0.
    let insts = vec![
        inst(AArch64Opcode::MovR, vec![vreg(1), MachOperand::PReg(X0)]),
        inst(AArch64Opcode::MovI, vec![vreg(2), imm(7)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "fixed-register");
}

#[test]
fn corruption_physical_register_reorder_is_refuted() {
    let insts = vec![
        inst(AArch64Opcode::MovR, vec![MachOperand::PReg(X1), vreg(1)]),
        inst(AArch64Opcode::MovR, vec![vreg(2), MachOperand::PReg(X1)]),
        ret(),
    ];
    assert_refuted(&permute(insts, &[1, 0, 2]), "Gpr(1)");
}

#[test]
fn corruption_instruction_rewritten_in_place_is_refuted() {
    let mut func = func_with(vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        ret(),
    ]);
    let before = PermutationSnapshot::capture(&func);
    func.inst_mut(InstId(0)).operands[1] = imm(2);
    assert_refuted(
        &validate_permutation(&before, &func).verdict,
        "rewritten in place",
    );
}

#[test]
fn corruption_dropped_instruction_is_refuted() {
    let mut func = func_with(vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        inst(AArch64Opcode::MovI, vec![vreg(2), imm(2)]),
        ret(),
    ]);
    let before = PermutationSnapshot::capture(&func);
    let entry = func.entry;
    func.block_mut(entry).insts.remove(0);
    assert_refuted(&validate_permutation(&before, &func).verdict, "length");
}

/// A permutation pass that swaps the first two instructions of the entry
/// block whatever they are, and reports `report` as its change claim.
struct SwapFirstTwo {
    name: &'static str,
    report: bool,
}

impl MachinePass for SwapFirstTwo {
    fn name(&self) -> &str {
        self.name
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        let entry = func.entry;
        func.block_mut(entry).insts.swap(0, 1);
        self.report
    }
}

fn dependent_pair() -> MachFunction {
    func_with(vec![
        inst(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]),
        inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(0)]),
        ret(),
    ])
}

#[test]
fn hook_records_a_refuted_scheduler_run_and_enforce_refuses_it() {
    let mut hook = PassValidationHook::new(PassValidationConfig::enforce());
    let mut summary = PassValidationSummary::new(hook.config());
    let mut func = dependent_pair();
    let mut pass = SwapFirstTwo {
        name: "pressure-aware-scheduler",
        report: true,
    };
    let snapshot = hook.snapshot(pass.name(), &func);
    let changed = pass.run(&mut func);
    hook.conclude(pass.name(), snapshot, changed, &func, &mut summary);
    assert_eq!(summary.refuted(), 1);
    let refusal = summary
        .first_refusal(PassValidationPolicy::Enforce)
        .expect("enforce refuses a refuted run");
    assert_eq!(refusal.pass_name, "pressure-aware-scheduler");
    assert_eq!(
        refusal.validator,
        Some(ValidatorKind::DependencePreservation)
    );
    assert!(
        summary
            .first_refusal(PassValidationPolicy::Diagnostic)
            .is_none()
    );
}

#[test]
fn hook_refutes_a_silent_mutation() {
    let mut hook = PassValidationHook::new(PassValidationConfig::diagnostic());
    let mut summary = PassValidationSummary::new(hook.config());
    let mut func = dependent_pair();
    let mut pass = SwapFirstTwo {
        name: "instruction-scheduler",
        report: false,
    };
    let snapshot = hook.snapshot(pass.name(), &func);
    let changed = pass.run(&mut func);
    hook.conclude(pass.name(), snapshot, changed, &func, &mut summary);
    assert_eq!(summary.refuted(), 1);
    assert_eq!(
        summary.failures[0].validator,
        Some(ValidatorKind::UnchangedClaim)
    );
}

#[test]
fn hook_records_uncovered_changed_runs_and_require_coverage_refuses_them() {
    let mut hook = PassValidationHook::new(PassValidationConfig::enforce());
    let mut summary = PassValidationSummary::new(hook.config());
    let mut func = func_with(vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        inst(AArch64Opcode::MovI, vec![vreg(2), imm(2)]),
        ret(),
    ]);
    let mut pass = SwapFirstTwo {
        name: "some-uncovered-pass",
        report: true,
    };
    let snapshot = hook.snapshot(pass.name(), &func);
    assert!(snapshot.check.is_none());
    let changed = pass.run(&mut func);
    hook.conclude(pass.name(), snapshot, changed, &func, &mut summary);
    assert_eq!(summary.uncovered(), 1);
    assert!(
        summary
            .first_refusal(PassValidationPolicy::Enforce)
            .is_none()
    );
    let refusal = summary
        .first_refusal(PassValidationPolicy::RequireCoverage)
        .expect("require-coverage refuses an uncovered run");
    assert_eq!(refusal.verdict, ValidationVerdict::Uncovered);
}

#[test]
fn off_policy_records_nothing() {
    let mut hook = PassValidationHook::new(PassValidationConfig::off());
    let mut summary = PassValidationSummary::new(hook.config());
    let mut func = dependent_pair();
    let mut pass = SwapFirstTwo {
        name: "pressure-aware-scheduler",
        report: true,
    };
    let snapshot = hook.snapshot(pass.name(), &func);
    let changed = pass.run(&mut func);
    hook.conclude(pass.name(), snapshot, changed, &func, &mut summary);
    assert!(summary.passes.is_empty());
}

#[test]
fn policy_spellings_round_trip_and_order() {
    for policy in [
        PassValidationPolicy::Off,
        PassValidationPolicy::Diagnostic,
        PassValidationPolicy::Enforce,
        PassValidationPolicy::RequireCoverage,
    ] {
        assert_eq!(PassValidationPolicy::parse(policy.as_str()), Some(policy));
    }
    assert_eq!(PassValidationPolicy::parse("bogus"), None);
    assert_eq!(
        PassValidationPolicy::Diagnostic.strongest(PassValidationPolicy::Enforce),
        PassValidationPolicy::Enforce
    );
    assert_eq!(
        PassValidationPolicy::RequireCoverage.strongest(PassValidationPolicy::Off),
        PassValidationPolicy::RequireCoverage
    );
}

#[test]
fn summary_merge_keeps_counts_exact() {
    let mut a = PassValidationSummary::new(PassValidationConfig::diagnostic());
    a.record(
        PassValidationRecord {
            pass_name: "p".into(),
            function_name: "f".into(),
            validator: Some(ValidatorKind::DependencePreservation),
            verdict: ValidationVerdict::Validated,
        },
        true,
    );
    let mut b = PassValidationSummary::new(PassValidationConfig::diagnostic());
    b.record(
        PassValidationRecord {
            pass_name: "p".into(),
            function_name: "g".into(),
            validator: Some(ValidatorKind::DependencePreservation),
            verdict: ValidationVerdict::Unproved("x".into()),
        },
        true,
    );
    a.merge(&b);
    assert_eq!(a.passes.len(), 1);
    assert_eq!(a.passes[0].changed_runs, 2);
    assert_eq!(a.validated(), 1);
    assert_eq!(a.unproved(), 1);
    assert_eq!(a.failures.len(), 1);
}

fn uncovered(pass: &str) -> PassValidationRecord {
    PassValidationRecord {
        pass_name: pass.into(),
        function_name: "f".into(),
        validator: None,
        verdict: ValidationVerdict::Uncovered,
    }
}

fn unproved_licm() -> PassValidationRecord {
    PassValidationRecord {
        pass_name: "licm".into(),
        function_name: "f".into(),
        validator: Some(ValidatorKind::HoistConditions),
        verdict: ValidationVerdict::Unproved("not guaranteed to execute".into()),
    }
}

#[test]
fn enforce_refuses_a_failed_run_behind_a_full_record_list() {
    // A full list of uncovered records must not hide a later failed run
    // from the refusing policy, whether it is recorded directly or merged
    // from another stage's summary.
    let mut direct = PassValidationSummary::new(PassValidationConfig::enforce());
    for _ in 0..MAX_RECORDED_FAILURES {
        direct.record(uncovered("gvn"), true);
    }
    assert!(
        direct
            .first_refusal(PassValidationPolicy::Enforce)
            .is_none()
    );
    direct.record(unproved_licm(), true);
    assert_eq!(direct.failures.len(), MAX_RECORDED_FAILURES);
    assert_eq!(direct.dropped_failures, 1);
    let refusal = direct
        .first_refusal(PassValidationPolicy::Enforce)
        .expect("enforce refuses the unproved run");
    assert_eq!(refusal.pass_name, "licm");
    assert_eq!(refusal.validator, Some(ValidatorKind::HoistConditions));

    let mut merged = PassValidationSummary::new(PassValidationConfig::enforce());
    for _ in 0..MAX_RECORDED_FAILURES {
        merged.record(uncovered("gvn"), true);
    }
    let mut stage = PassValidationSummary::new(PassValidationConfig::enforce());
    stage.record(unproved_licm(), true);
    merged.merge(&stage);
    assert_eq!(
        merged
            .first_refusal(PassValidationPolicy::Enforce)
            .map(|r| r.pass_name),
        Some("licm".to_string())
    );
}

#[test]
fn refusal_is_decided_from_the_counters_not_the_records() {
    // Counters with no kept record (every record dropped) still refuse,
    // with a record rebuilt from the counters.
    let summary = PassValidationSummary {
        config: PassValidationConfig::enforce(),
        passes: vec![
            PassValidationCounts {
                pass_name: "gvn".into(),
                changed_runs: 3,
                uncovered: 3,
                ..PassValidationCounts::default()
            },
            PassValidationCounts {
                pass_name: "mem-pair-formation".into(),
                changed_runs: 2,
                validated: 1,
                unproved: 1,
                ..PassValidationCounts::default()
            },
        ],
        failures: Vec::new(),
        dropped_failures: 4,
        examined_instructions: 0,
        transitions: Vec::new(),
    };
    let refusal = summary
        .first_refusal(PassValidationPolicy::Enforce)
        .expect("an unproved count refuses");
    assert_eq!(refusal.pass_name, "mem-pair-formation");
    assert_eq!(
        refusal.validator,
        Some(ValidatorKind::SymbolicRegionEquivalence)
    );
    assert!(
        refusal
            .verdict
            .reason()
            .is_some_and(|r| r.contains("dropped")),
        "{refusal:?}"
    );
    let coverage = summary
        .first_refusal(PassValidationPolicy::RequireCoverage)
        .expect("an uncovered count refuses under require-coverage");
    assert_eq!(coverage.pass_name, "gvn");
    assert_eq!(coverage.verdict, ValidationVerdict::Uncovered);
    assert!(
        summary
            .first_refusal(PassValidationPolicy::Diagnostic)
            .is_none()
    );
}

// ---------------------------------------------------------------------------
// Symbolic terms: every normalization agrees with concrete evaluation.
// ---------------------------------------------------------------------------

mod terms {
    use super::super::term::{Atom, Cmp, FlagKind, Loc, Prim, TermArena, TermId};

    /// A small deterministic generator (xorshift64*).
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }

        fn interesting(&mut self) -> u64 {
            match self.next() % 6 {
                0 => 0,
                1 => u64::MAX,
                2 => 1u64 << (self.next() % 64),
                3 => self.next() & 0xFFFF,
                4 => (1u64 << 63).wrapping_sub(self.next() % 3),
                _ => self.next(),
            }
        }
    }

    fn mask(width: u8) -> u128 {
        if width >= 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        }
    }

    fn sx(v: u128, bits: u8) -> i128 {
        let shift = 128 - u32::from(bits);
        ((v << shift) as i128) >> shift
    }

    /// Evaluate `t` with atom `i` (by creation order) bound to `vals[i]`.
    fn eval(arena: &TermArena, atoms: &[TermId], vals: &[u64], t: TermId) -> u128 {
        arena
            .eval(t, &|id| {
                atoms
                    .iter()
                    .position(|a| *a == id)
                    .map(|i| u128::from(vals[i]))
            })
            .expect("evaluable term")
    }

    fn atoms(arena: &mut TermArena, n: u32) -> Vec<TermId> {
        (0..n)
            .map(|i| {
                arena.atom(
                    Atom::Input {
                        block: 0,
                        loc: Loc::VReg(i),
                        fpr: false,
                    },
                    Some(64),
                )
            })
            .collect()
    }

    #[test]
    fn constructors_agree_with_concrete_arithmetic() {
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for round in 0..400 {
            let mut arena = TermArena::new();
            let xs = atoms(&mut arena, 3);
            let vals: Vec<u64> = (0..3).map(|_| rng.interesting()).collect();
            let width = if round % 2 == 0 { 64 } else { 32 };
            let m = mask(width);
            let (a, b, c) = (xs[0], xs[1], xs[2]);
            let (va, vb, vc) = (
                u128::from(vals[0]) & m,
                u128::from(vals[1]) & m,
                u128::from(vals[2]) & m,
            );
            let k = rng.interesting();
            let kt = arena.konst(k);
            let vk = u128::from(k) & m;
            let shift = (rng.next() % u64::from(width)) as u32;
            let checks: Vec<(&str, TermId, u128)> = vec![
                ("add", arena.add(width, a, b), (va + vb) & m),
                ("sub", arena.sub(width, a, b), va.wrapping_sub(vb) & m),
                ("add-const", arena.add_const(width, a, k), (va + vk) & m),
                (
                    "mul-const",
                    arena.mul(width, a, kt),
                    va.wrapping_mul(vk) & m,
                ),
                ("mul", arena.mul(width, a, b), va.wrapping_mul(vb) & m),
                ("and-const", arena.and(width, a, kt), va & vk),
                ("or-const", arena.or(width, a, kt), (va | vk) & m),
                ("xor", arena.xor(width, a, b), va ^ vb),
                ("not", arena.not(width, a), !va & m),
                ("neg", arena.neg(width, a), va.wrapping_neg() & m),
                (
                    "shl",
                    if shift == 0 {
                        arena.zext(a, width)
                    } else {
                        arena.shl(width, a, shift)
                    },
                    (va << shift) & m,
                ),
                (
                    "lshr",
                    arena.shift_const(Prim::Lshr, width, a, shift),
                    va >> shift,
                ),
                (
                    "ashr",
                    arena.shift_const(Prim::Ashr, width, a, shift),
                    (sx(va, width) >> shift) as u128 & m,
                ),
                ("zext8", arena.zext(a, 8), va & 0xFF),
                ("sext16", arena.sext(width, a, 16), sx(va, 16) as u128 & m),
                (
                    "madd-shape",
                    {
                        let p = arena.mul(width, a, b);
                        arena.add(width, c, p)
                    },
                    (vc + va.wrapping_mul(vb)) & m,
                ),
                (
                    "sub-add-cancels",
                    {
                        let s = arena.sub(width, a, b);
                        arena.add(width, s, b)
                    },
                    va,
                ),
            ];
            for (name, term, expected) in checks {
                assert_eq!(
                    eval(&arena, &xs, &vals, term),
                    expected,
                    "{name} at width {width} with {vals:x?} k={k:#x} shift={shift}"
                );
            }
            // Comparisons and the flag conditions they normalize to.
            let lt = arena.cmp(Cmp::Ult, width, a, b);
            assert_eq!(eval(&arena, &xs, &vals, lt), u128::from(va < vb));
            let slt = arena.cmp(Cmp::Slt, width, a, b);
            assert_eq!(
                eval(&arena, &xs, &vals, slt),
                u128::from(sx(va, width) < sx(vb, width))
            );
            let flags = arena.flags(FlagKind::Sub, width, a, b);
            for (cc, expected) in [
                (0u8, va == vb),
                (1, va != vb),
                (2, va >= vb),
                (3, va < vb),
                (8, va > vb),
                (9, va <= vb),
                (10, sx(va, width) >= sx(vb, width)),
                (11, sx(va, width) < sx(vb, width)),
                (12, sx(va, width) > sx(vb, width)),
                (13, sx(va, width) <= sx(vb, width)),
            ] {
                let cond = arena.cond(cc, flags);
                assert_eq!(
                    eval(&arena, &xs, &vals, cond),
                    u128::from(expected),
                    "cc {cc} at width {width} with {vals:x?}"
                );
            }
        }
    }

    #[test]
    fn equal_ids_are_the_only_verdict_and_cancellation_normalizes() {
        let mut arena = TermArena::new();
        let xs = atoms(&mut arena, 2);
        let s = arena.sub(64, xs[0], xs[1]);
        let back = arena.add(64, s, xs[1]);
        assert_eq!(back, xs[0]);
        let ab = arena.add(64, xs[0], xs[1]);
        let ba = arena.add(64, xs[1], xs[0]);
        assert_eq!(ab, ba);
        let not_c = {
            let c = arena.cmp(Cmp::Eq, 64, xs[0], xs[1]);
            arena.bool_not(c)
        };
        // ite(!c, x, y) == ite(c, y, x)
        let c = arena.cmp(Cmp::Eq, 64, xs[0], xs[1]);
        let i1 = arena.ite(not_c, xs[0], xs[1]);
        let i2 = arena.ite(c, xs[1], xs[0]);
        assert_eq!(i1, i2);
        // A 32-bit add is not a 64-bit add.
        let a32 = arena.add(32, xs[0], xs[1]);
        assert_ne!(a32, ab);
    }

    #[test]
    fn guarded_division_folds_to_the_division_only_at_the_tested_width() {
        let mut rng = Rng(0x0123_4567_89AB_CDEF);
        for width in [32u8, 64] {
            let mut arena = TermArena::new();
            let xs = atoms(&mut arena, 2);
            let zero = arena.konst(0);
            let div = arena.binop(Prim::Udiv, width, xs[0], xs[1]);
            let is_zero = arena.cmp(Cmp::Eq, width, xs[1], zero);
            let guarded = arena.ite(is_zero, zero, div);
            assert_eq!(guarded, div, "width {width}");
            for _ in 0..64 {
                let vals = [
                    rng.interesting(),
                    if rng.next().is_multiple_of(2) {
                        0
                    } else {
                        rng.interesting()
                    },
                ];
                let m = mask(width);
                let (a, b) = (u128::from(vals[0]) & m, u128::from(vals[1]) & m);
                let expected = a.checked_div(b).unwrap_or(0);
                assert_eq!(eval(&arena, &xs, &vals, guarded), expected);
            }
            // A test of other bits than the division reads does not fold.
            let narrow = arena.cmp(Cmp::Eq, 8, xs[1], zero);
            let other = arena.ite(narrow, zero, div);
            assert_ne!(other, div, "width {width}");
            // Nor does a non-zero arm.
            let one = arena.konst(1);
            let wrong = arena.ite(is_zero, one, div);
            assert_ne!(wrong, div, "width {width}");
        }
    }
}

// ---------------------------------------------------------------------------
// Symbolic region equivalence.
// ---------------------------------------------------------------------------

mod regions {
    use super::super::region::validate_regions;
    use super::super::*;
    use super::{imm, inst, vreg};
    use crate::if_convert::IfConversion;
    use crate::mem_pair::MemPairFormation;
    use crate::pass_manager::MachinePass;
    use trust_cg_ir::regs::X0;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PReg,
        RegClass, Signature, VReg,
    };

    static RET_X0: [PReg; 1] = [X0];

    fn fpr(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Fpr64))
    }

    fn ret_x0() -> MachInst {
        let mut ret = inst(AArch64Opcode::Ret, vec![]);
        ret.implicit_uses = &RET_X0;
        ret
    }

    fn block_func(insts: Vec<MachInst>) -> MachFunction {
        let mut func = MachFunction::new("pv_region".to_string(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        for i in insts {
            let id = func.push_inst(i);
            func.append_inst(entry, id);
        }
        func.try_sync_vreg_counter()
            .expect("bounded fixture register arena");
        func
    }

    fn assert_validated(before: &MachFunction, after: &MachFunction) {
        let outcome = validate_regions(before, after);
        assert_eq!(outcome.verdict, ValidationVerdict::Validated);
    }

    fn assert_unproved(before: &MachFunction, after: &MachFunction, needle: &str) {
        match validate_regions(before, after).verdict {
            ValidationVerdict::Unproved(reason) => assert!(
                reason.contains(needle),
                "reason `{reason}` does not mention `{needle}`"
            ),
            other => panic!("expected an unproved verdict mentioning `{needle}`, got {other:?}"),
        }
    }

    /// Two adjacent FP loads summed and stored: the mem-pair input shape.
    fn adjacent_loads(second_offset: i64) -> MachFunction {
        block_func(vec![
            inst(AArch64Opcode::LdrRI, vec![fpr(1), vreg(10), imm(0)]),
            inst(
                AArch64Opcode::LdrRI,
                vec![fpr(2), vreg(10), imm(second_offset)],
            ),
            inst(AArch64Opcode::FaddRR, vec![fpr(3), fpr(1), fpr(2)]),
            inst(AArch64Opcode::StrRI, vec![fpr(3), vreg(11), imm(0)]),
            inst(AArch64Opcode::Ret, vec![]),
        ])
    }

    #[test]
    fn mem_pair_formation_validates() {
        let before = adjacent_loads(8);
        let mut after = before.clone();
        assert!(MemPairFormation.run(&mut after), "the pair forms");
        assert!(after.insts.iter().any(|i| i.opcode == AArch64Opcode::LdpRI));
        assert_validated(&before, &after);
    }

    #[test]
    fn corruption_pairing_non_adjacent_accesses_is_rejected() {
        // The loads read [v10] and [v10 + 16]; an LDP at #0 reads [v10 + 8].
        let before = adjacent_loads(16);
        let mut after = before.clone();
        let entry = after.entry;
        let ldp = after.push_inst(inst(
            AArch64Opcode::LdpRI,
            vec![fpr(1), fpr(2), vreg(10), imm(0)],
        ));
        let old = after.block(entry).insts.clone();
        after.block_mut(entry).insts = std::iter::once(ldp)
            .chain(old[2..].iter().copied())
            .collect();
        assert_unproved(&before, &after, "differs");
    }

    #[test]
    fn corruption_load_paired_across_an_aliasing_store_is_rejected() {
        // `ldr [v10]; str [v10+8]; ldr [v10+8]`: hoisting the second load
        // into an LDP reads memory before the store.
        let before = block_func(vec![
            inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)]),
            inst(AArch64Opcode::StrRI, vec![vreg(5), vreg(10), imm(8)]),
            inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(8)]),
            inst(AArch64Opcode::AddRR, vec![vreg(3), vreg(1), vreg(2)]),
            inst(AArch64Opcode::StrRI, vec![vreg(3), vreg(11), imm(0)]),
            inst(AArch64Opcode::Ret, vec![]),
        ]);
        let mut after = before.clone();
        let entry = after.entry;
        let ldp = after.push_inst(inst(
            AArch64Opcode::LdpRI,
            vec![vreg(1), vreg(2), vreg(10), imm(0)],
        ));
        let old = after.block(entry).insts.clone();
        after.block_mut(entry).insts = vec![ldp, old[1], old[3], old[4], old[5]];
        assert_unproved(&before, &after, "differs");
        // The faithful reordering (store first) is still fine: the pair
        // reads the stored value forwarded through the memory model.
        let mut faithful = before.clone();
        let old = faithful.block(entry).insts.clone();
        let ldp = faithful.push_inst(inst(
            AArch64Opcode::LdpRI,
            vec![vreg(1), vreg(2), vreg(10), imm(0)],
        ));
        faithful.block_mut(entry).insts = vec![old[1], ldp, old[3], old[4], old[5]];
        assert_validated(&before, &faithful);
    }

    /// `if v0 < v1 { v2 = v3 } else { v2 = v4 }; x0 = v2; ret`, in the
    /// fallthrough form the general if-conversion admits: the header falls
    /// through to the false arm, laid out next.
    fn diamond(true_inst: MachInst, false_inst: MachInst) -> MachFunction {
        let mut func = MachFunction::new("pv_diamond".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let push = |func: &mut MachFunction, b: BlockId, i: MachInst| {
            let id = func.push_inst(i);
            func.append_inst(b, id);
        };
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::CmpRR, vec![vreg(0), vreg(1)]),
        );
        push(
            &mut func,
            bb0,
            inst(
                AArch64Opcode::BCond,
                vec![imm(CondCode::LT.encoding() as i64), MachOperand::Block(bb1)],
            ),
        );
        push(&mut func, bb1, true_inst);
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );
        push(&mut func, bb2, false_inst);
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::B, vec![MachOperand::Block(bb3)]),
        );
        push(
            &mut func,
            bb3,
            inst(AArch64Opcode::MovR, vec![MachOperand::PReg(X0), vreg(2)]),
        );
        push(&mut func, bb3, ret_x0());
        func.add_edge(bb0, bb1);
        func.add_edge(bb0, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb2, bb3);
        func.block_order = vec![bb0, bb2, bb1, bb3];
        func
    }

    #[test]
    fn if_conversion_of_a_value_diamond_validates() {
        let before = diamond(
            inst(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]),
            inst(AArch64Opcode::AddRI, vec![vreg(2), vreg(4), imm(1)]),
        );
        let mut after = before.clone();
        assert!(IfConversion.run(&mut after), "the diamond converts");
        assert!(after.block(after.entry).insts.iter().any(|&id| matches!(
            after.inst(id).opcode,
            AArch64Opcode::Csel | AArch64Opcode::Csinc
        )));
        assert_validated(&before, &after);
    }

    #[test]
    fn corruption_inverted_select_is_rejected() {
        let before = diamond(
            inst(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]),
            inst(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]),
        );
        let mut after = before.clone();
        assert!(IfConversion.run(&mut after));
        // Swap the select's arms.
        let entry = after.entry;
        let sel = after
            .block(entry)
            .insts
            .iter()
            .copied()
            .find(|&id| after.inst(id).opcode == AArch64Opcode::Csel)
            .expect("a CSEL");
        after.inst_mut(sel).operands.swap(1, 2);
        assert_unproved(&before, &after, "differs");
    }

    #[test]
    fn corruption_if_converting_an_arm_with_a_side_effect_is_rejected() {
        // The true arm also stores; a converted form that stores
        // unconditionally changes memory on the false path.
        let mut before = diamond(
            inst(AArch64Opcode::MovR, vec![vreg(2), vreg(3)]),
            inst(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]),
        );
        let store = before.push_inst(inst(AArch64Opcode::StrRI, vec![vreg(3), vreg(12), imm(0)]));
        before.block_mut(BlockId(1)).insts.insert(0, store);
        let mut after = before.clone();
        // cmp; str; csel; b join
        let entry = after.entry;
        let cmp = after.block(entry).insts[0];
        let store = after.push_inst(inst(AArch64Opcode::StrRI, vec![vreg(3), vreg(12), imm(0)]));
        let csel = after.push_inst(inst(
            AArch64Opcode::Csel,
            vec![
                vreg(2),
                vreg(3),
                vreg(4),
                imm(CondCode::LT.encoding() as i64),
            ],
        ));
        let jump = after.push_inst(inst(AArch64Opcode::B, vec![MachOperand::Block(BlockId(3))]));
        after.block_mut(entry).insts = vec![cmp, store, csel, jump];
        after.block_order.retain(|b| b.0 != 1 && b.0 != 2);
        assert_unproved(&before, &after, "differs");
    }

    #[test]
    fn corruption_if_converting_an_arm_with_a_load_is_rejected_as_speculation() {
        // The true arm loads; converting it executes the load on both paths.
        let before = diamond(
            inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]),
            inst(AArch64Opcode::MovR, vec![vreg(2), vreg(4)]),
        );
        let mut after = before.clone();
        let entry = after.entry;
        let cmp = after.block(entry).insts[0];
        let load = after.push_inst(inst(AArch64Opcode::LdrRI, vec![vreg(5), vreg(3), imm(0)]));
        let csel = after.push_inst(inst(
            AArch64Opcode::Csel,
            vec![
                vreg(2),
                vreg(5),
                vreg(4),
                imm(CondCode::LT.encoding() as i64),
            ],
        ));
        let jump = after.push_inst(inst(AArch64Opcode::B, vec![MachOperand::Block(BlockId(3))]));
        after.block_mut(entry).insts = vec![cmp, load, csel, jump];
        after.block_order.retain(|b| b.0 != 1 && b.0 != 2);
        assert_unproved(&before, &after, "speculates");
    }

    #[test]
    fn dead_definition_removal_validates_but_a_live_one_does_not() {
        let before = block_func(vec![
            inst(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(1)]),
            inst(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(2)]),
            inst(AArch64Opcode::MovR, vec![MachOperand::PReg(X0), vreg(1)]),
            ret_x0(),
        ]);
        let mut dead = before.clone();
        let entry = dead.entry;
        dead.block_mut(entry).insts.remove(1);
        assert_validated(&before, &dead);
        let mut live = before.clone();
        live.block_mut(entry).insts.remove(0);
        assert_unproved(&before, &live, "differs");
    }

    #[test]
    fn region_with_a_loop_is_unproved_not_validated() {
        // A new self-loop block.
        let before = block_func(vec![
            inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
            inst(AArch64Opcode::Ret, vec![]),
        ]);
        let mut after = before.clone();
        let entry = after.entry;
        let lp = after.create_block();
        let back = after.push_inst(inst(AArch64Opcode::B, vec![MachOperand::Block(lp)]));
        after.append_inst(lp, back);
        let jump = after.push_inst(inst(AArch64Opcode::B, vec![MachOperand::Block(lp)]));
        after.block_mut(entry).insts = vec![jump];
        assert_unproved(&before, &after, "loops");
    }

    /// A block that leaves through two conditional exits with work between
    /// them (`cbz; cmp; b.eq; b`), paired in its body.
    #[test]
    fn pairing_in_a_block_with_a_conditional_exit_chain_validates() {
        let mut func =
            MachFunction::new("pv_chain_exit".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let targets: Vec<BlockId> = (0..3).map(|_| func.create_block()).collect();
        let push = |func: &mut MachFunction, b: BlockId, i: MachInst| {
            let id = func.push_inst(i);
            func.append_inst(b, id);
        };
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)]),
        );
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::LdrRI, vec![vreg(2), vreg(10), imm(8)]),
        );
        push(
            &mut func,
            bb0,
            inst(
                AArch64Opcode::Cbz,
                vec![vreg(1), MachOperand::Block(targets[0])],
            ),
        );
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::CmpRI, vec![vreg(2), imm(1)]),
        );
        push(
            &mut func,
            bb0,
            inst(
                AArch64Opcode::BCond,
                vec![
                    imm(CondCode::EQ.encoding() as i64),
                    MachOperand::Block(targets[1]),
                ],
            ),
        );
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::B, vec![MachOperand::Block(targets[2])]),
        );
        for (k, &t) in targets.iter().enumerate() {
            push(
                &mut func,
                t,
                inst(
                    AArch64Opcode::AddRI,
                    vec![
                        MachOperand::PReg(X0),
                        vreg(if k == 0 { 2 } else { 1 }),
                        imm(k as i64),
                    ],
                ),
            );
            push(&mut func, t, ret_x0());
        }
        func.try_sync_vreg_counter()
            .expect("bounded fixture register arena");
        let before = func.clone();
        let mut after = func;
        assert!(MemPairFormation.run(&mut after));
        assert_validated(&before, &after);
        // The same pair reading the wrong second word is still refused at
        // every exit.
        let mut wrong = before.clone();
        let ldp = wrong.push_inst(inst(
            AArch64Opcode::LdpRI,
            vec![vreg(1), vreg(2), vreg(10), imm(8)],
        ));
        let old = wrong.block(bb0).insts.clone();
        wrong.block_mut(bb0).insts = std::iter::once(ldp)
            .chain(old[2..].iter().copied())
            .collect();
        assert_unproved(&before, &wrong, "differs");
    }

    #[test]
    fn unchanged_function_validates() {
        let before = adjacent_loads(8);
        assert_validated(&before, &before.clone());
        let _ = InstId(0);
    }

    fn push(func: &mut MachFunction, b: BlockId, i: MachInst) -> InstId {
        let id = func.push_inst(i);
        func.append_inst(b, id);
        id
    }

    pub(super) fn call(symbol: &str) -> MachInst {
        inst(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol(symbol.to_string())],
        )
    }

    fn jump(target: BlockId) -> MachInst {
        inst(AArch64Opcode::B, vec![MachOperand::Block(target)])
    }

    fn mov_x0(value: u32) -> MachInst {
        inst(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X0), vreg(value)],
        )
    }

    /// Record `call_block`'s call as an invoke landing at `pad`.
    pub(super) fn add_invoke(func: &mut MachFunction, call_block: BlockId, pad: BlockId) {
        use trust_cg_ir::function::{EhCallSiteEntry, LandingPadEntry};
        func.eh_metadata.personality = Some("__gxx_personality_v0".to_string());
        func.eh_metadata.add_landing_pad(LandingPadEntry {
            block: pad,
            offset: 0,
            catch_type_indices: vec![0],
            is_cleanup: false,
        });
        func.eh_metadata.add_call_site(EhCallSiteEntry {
            call_block,
            start_offset: 0,
            length: 0,
            landing_pad_block: Some(pad),
        });
    }

    /// `bb0: v1 = 1; bl callee; b bb1` (an invoke landing at bb2);
    /// `bb1: return v1`; `bb2: v6 = [v5]; v9 = [v5 + 8]; return v6 + v9`.
    fn invoke_with_pad() -> MachFunction {
        let mut func = MachFunction::new("pv_eh".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        );
        push(&mut func, bb0, call("callee"));
        push(&mut func, bb0, jump(bb1));
        push(&mut func, bb1, mov_x0(1));
        push(&mut func, bb1, ret_x0());
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::LdrRI, vec![vreg(6), vreg(5), imm(0)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::LdrRI, vec![vreg(9), vreg(5), imm(8)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::AddRR, vec![vreg(11), vreg(6), vreg(9)]),
        );
        push(&mut func, bb2, mov_x0(11));
        push(&mut func, bb2, ret_x0());
        add_invoke(&mut func, bb0, bb2);
        func
    }

    /// Replace the `index`th instruction of `block` with `with`.
    fn replace(func: &mut MachFunction, block: BlockId, index: usize, with: MachInst) {
        let id = func.push_inst(with);
        func.block_mut(block).insts[index] = id;
    }

    #[test]
    fn pairing_loads_in_a_landing_pad_validates() {
        // Before exception edges were modeled, any function with an invoke
        // was refused; the pad is now a reachable region of its own.
        let before = invoke_with_pad();
        let mut after = before.clone();
        let pad = BlockId(2);
        let ldp = after.push_inst(inst(
            AArch64Opcode::LdpRI,
            vec![vreg(6), vreg(9), vreg(5), imm(0)],
        ));
        let old = after.block(pad).insts.clone();
        after.block_mut(pad).insts = std::iter::once(ldp)
            .chain(old[2..].iter().copied())
            .collect();
        assert_validated(&before, &after);
    }

    #[test]
    fn corruption_a_rewrite_in_a_landing_pad_is_rejected() {
        // The pad is reached only by its exception edge: without that edge
        // it would be unreachable and its change would go unchecked.
        let before = invoke_with_pad();
        let mut after = before.clone();
        replace(
            &mut after,
            BlockId(2),
            2,
            inst(AArch64Opcode::SubRR, vec![vreg(11), vreg(6), vreg(9)]),
        );
        assert_unproved(&before, &after, "differs");
    }

    #[test]
    fn a_region_through_an_invoke_block_is_unproved() {
        let before = invoke_with_pad();
        let mut after = before.clone();
        replace(
            &mut after,
            BlockId(0),
            0,
            inst(AArch64Opcode::MovI, vec![vreg(1), imm(2)]),
        );
        assert_unproved(&before, &after, "invoke block");
    }

    #[test]
    fn corruption_a_value_only_a_landing_pad_reads_is_rejected() {
        // `bb0: v12 = 1; b bb1`, `bb1: bl callee; v12 = 5; b bb3` (an invoke
        // landing at bb2), `bb2: return v12`, `bb3: return v12`. The pad
        // reads bb0's v12 through the exception edge even though bb1
        // overwrites it after the call, so changing it in bb0 is observable.
        let mut before =
            MachFunction::new("pv_eh_live".to_string(), Signature::new(vec![], vec![]));
        let bb0 = before.entry;
        let bb1 = before.create_block();
        let bb2 = before.create_block();
        let bb3 = before.create_block();
        push(
            &mut before,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(12), imm(1)]),
        );
        push(&mut before, bb0, jump(bb1));
        push(&mut before, bb1, call("callee"));
        push(
            &mut before,
            bb1,
            inst(AArch64Opcode::MovI, vec![vreg(12), imm(5)]),
        );
        push(&mut before, bb1, jump(bb3));
        push(&mut before, bb2, mov_x0(12));
        push(&mut before, bb2, ret_x0());
        push(&mut before, bb3, mov_x0(12));
        push(&mut before, bb3, ret_x0());
        add_invoke(&mut before, bb1, bb2);
        let mut after = before.clone();
        replace(
            &mut after,
            bb0,
            0,
            inst(AArch64Opcode::MovI, vec![vreg(12), imm(2)]),
        );
        assert_unproved(&before, &after, "differs");
    }

    #[test]
    fn corruption_changed_exception_metadata_is_rejected() {
        let before = invoke_with_pad();
        let mut after = before.clone();
        after.eh_metadata.call_sites.clear();
        assert_unproved(&before, &after, "exception-handling metadata changed");
    }
}

// ---------------------------------------------------------------------------
// Code-motion side conditions.
// ---------------------------------------------------------------------------

mod hoists {
    use super::super::hoist::validate_hoists;
    use super::super::*;
    use super::{imm, inst, vreg};
    use crate::licm::LoopInvariantCodeMotion;
    use crate::pass_manager::MachinePass;
    use trust_cg_ir::regs::X0;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PReg,
        Signature, SpecialReg, StackSlot, StackSlotId,
    };

    static RET_X0: [PReg; 1] = [X0];

    fn push(func: &mut MachFunction, b: BlockId, i: MachInst) -> InstId {
        let id = func.push_inst(i);
        func.append_inst(b, id);
        id
    }

    fn branch(cc: CondCode, target: BlockId) -> MachInst {
        inst(
            AArch64Opcode::BCond,
            vec![imm(cc.encoding() as i64), MachOperand::Block(target)],
        )
    }

    fn jump(target: BlockId) -> MachInst {
        inst(AArch64Opcode::B, vec![MachOperand::Block(target)])
    }

    fn exit_block(func: &mut MachFunction, b: BlockId, value: u32) {
        push(
            func,
            b,
            inst(
                AArch64Opcode::MovR,
                vec![MachOperand::PReg(X0), vreg(value)],
            ),
        );
        let mut ret = inst(AArch64Opcode::Ret, vec![]);
        ret.implicit_uses = &RET_X0;
        push(func, b, ret);
    }

    /// `v4 = 0; loop { v2 = v0 + v1; v4 += v2 } while v4 <u 100; return v4`.
    fn simple_loop() -> MachFunction {
        let mut func = MachFunction::new("pv_licm".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(0), imm(10)]),
        );
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(1), imm(20)]),
        );
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(4), imm(0)]),
        );
        push(&mut func, bb0, jump(bb1));
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
        );
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRR, vec![vreg(4), vreg(4), vreg(2)]),
        );
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(100)]),
        );
        push(&mut func, bb1, branch(CondCode::LO, bb1));
        push(&mut func, bb1, jump(bb2));
        exit_block(&mut func, bb2, 4);
        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb1);
        func.add_edge(bb1, bb2);
        func
    }

    /// Move `id` to block `to` just before its last instruction.
    fn hoist(func: &mut MachFunction, id: InstId, to: BlockId) {
        for b in func.block_order.clone() {
            func.block_mut(b).insts.retain(|&x| x != id);
        }
        let n = func.block(to).insts.len();
        func.block_mut(to).insts.insert(n - 1, id);
    }

    fn assert_unproved(before: &MachFunction, after: &MachFunction, needle: &str) {
        match validate_hoists(before, after).verdict {
            ValidationVerdict::Unproved(reason) => assert!(
                reason.contains(needle),
                "reason `{reason}` does not mention `{needle}`"
            ),
            other => panic!("expected unproved mentioning `{needle}`, got {other:?}"),
        }
    }

    #[test]
    fn licm_hoist_validates() {
        let before = simple_loop();
        let mut after = before.clone();
        assert!(
            LoopInvariantCodeMotion::new().run(&mut after),
            "LICM hoists"
        );
        assert!(after.block(BlockId(0)).insts.contains(&InstId(4)));
        assert_eq!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_hoisting_a_loop_variant_operand_is_rejected() {
        let before = simple_loop();
        let mut after = before.clone();
        // `v4 = v4 + v2` reads the loop-carried v4.
        hoist(&mut after, InstId(5), BlockId(0));
        assert_unproved(&before, &after, "written in the loop");
    }

    #[test]
    fn corruption_hoisting_a_definition_live_into_the_header_is_rejected() {
        // `v13 = 7; loop { v3 = v13 + v0; v13 = 5; ... }`: the first
        // iteration reads the pre-loop v13.
        let mut before = simple_loop();
        let header = BlockId(1);
        let pre_def = before.push_inst(inst(AArch64Opcode::MovI, vec![vreg(13), imm(7)]));
        before.block_mut(BlockId(0)).insts.insert(0, pre_def);
        let read = before.push_inst(inst(AArch64Opcode::AddRR, vec![vreg(3), vreg(13), vreg(0)]));
        let def = before.push_inst(inst(AArch64Opcode::MovI, vec![vreg(13), imm(5)]));
        before.block_mut(header).insts.insert(0, def);
        before.block_mut(header).insts.insert(0, read);
        let mut after = before.clone();
        hoist(&mut after, def, BlockId(0));
        assert_unproved(&before, &after, "live into the loop header");
        // Without the pre-loop definition the first iteration read an
        // undefined register, which the hoisted definition refines.
        let mut undefined = before.clone();
        undefined
            .block_mut(BlockId(0))
            .insts
            .retain(|&x| x != pre_def);
        let mut hoisted = undefined.clone();
        hoist(&mut hoisted, def, BlockId(0));
        assert_eq!(
            validate_hoists(&undefined, &hoisted).verdict,
            ValidationVerdict::Validated
        );
    }

    /// A loop whose body has a guarded arm:
    /// `bb1: cmp v5, 0; b.eq bb3; b bb2`, `bb2: v7 = load [base]; v11 = v7 + 1;
    /// b bb3`, `bb3: v4 += 1; cmp; b.lo bb1; b bb4`, `bb4: return v4`.
    fn guarded_loop(base: MachOperand) -> MachFunction {
        let mut func =
            MachFunction::new("pv_licm_guard".to_string(), Signature::new(vec![], vec![]));
        func.stack_slots.push(StackSlot::new(16, 8));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        let bb4 = func.create_block();
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(4), imm(0)]),
        );
        push(
            &mut func,
            bb0,
            inst(
                AArch64Opcode::AddPCRel,
                vec![
                    vreg(20),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::StackSlot(StackSlotId(0)),
                ],
            ),
        );
        push(&mut func, bb0, jump(bb1));
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::CmpRI, vec![vreg(5), imm(0)]),
        );
        push(&mut func, bb1, branch(CondCode::EQ, bb3));
        push(&mut func, bb1, jump(bb2));
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::LdrRI, vec![vreg(7), base, imm(8)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::AddRI, vec![vreg(11), vreg(7), imm(1)]),
        );
        push(&mut func, bb2, jump(bb3));
        push(
            &mut func,
            bb3,
            inst(AArch64Opcode::AddRI, vec![vreg(4), vreg(4), imm(1)]),
        );
        push(
            &mut func,
            bb3,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(100)]),
        );
        push(&mut func, bb3, branch(CondCode::LO, bb1));
        push(&mut func, bb3, jump(bb4));
        exit_block(&mut func, bb4, 4);
        func
    }

    fn guarded_load_id(func: &MachFunction) -> InstId {
        func.block(BlockId(2)).insts[0]
    }

    #[test]
    fn corruption_hoisting_a_faulting_load_out_of_a_guarded_block_is_rejected() {
        let before = guarded_loop(vreg(8));
        let mut after = before.clone();
        hoist(&mut after, guarded_load_id(&before), BlockId(0));
        assert_unproved(&before, &after, "not guaranteed to execute");
    }

    #[test]
    fn guarded_in_bounds_frame_load_may_be_hoisted() {
        // The same shape reading bytes 8..16 of a 16-byte stack slot.
        let before = guarded_loop(vreg(20));
        let mut after = before.clone();
        hoist(&mut after, guarded_load_id(&before), BlockId(0));
        assert_eq!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_hoisting_a_load_above_a_preheader_store_is_rejected() {
        // The Wave 11 LICM placement defect: the preheader stores the cell the
        // loop loads, and the hoisted load lands before that store.
        let mut before = simple_loop();
        let pre = BlockId(0);
        let header = BlockId(1);
        let store = before.push_inst(inst(AArch64Opcode::StrRI, vec![vreg(0), vreg(20), imm(0)]));
        let n = before.block(pre).insts.len();
        before.block_mut(pre).insts.insert(n - 1, store);
        let load = before.push_inst(inst(AArch64Opcode::LdrRI, vec![vreg(21), vreg(20), imm(0)]));
        before.block_mut(header).insts.insert(0, load);
        let mut after = before.clone();
        for b in after.block_order.clone() {
            after.block_mut(b).insts.retain(|&x| x != load);
        }
        let at = after
            .block(pre)
            .insts
            .iter()
            .position(|&x| x == store)
            .expect("the store");
        after.block_mut(pre).insts.insert(at, load);
        assert_unproved(&before, &after, "writes memory after its new position");
        // After the store it is fine.
        let mut placed = before.clone();
        hoist(&mut placed, load, pre);
        assert_eq!(
            validate_hoists(&before, &placed).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_hoisting_a_load_out_of_a_loop_that_stores_is_rejected() {
        let mut before = simple_loop();
        let header = BlockId(1);
        let load = before.push_inst(inst(AArch64Opcode::LdrRI, vec![vreg(21), vreg(20), imm(0)]));
        let store = before.push_inst(inst(AArch64Opcode::StrRI, vec![vreg(4), vreg(22), imm(0)]));
        before.block_mut(header).insts.insert(0, store);
        before.block_mut(header).insts.insert(0, load);
        let mut after = before.clone();
        hoist(&mut after, load, BlockId(0));
        assert_unproved(&before, &after, "may write what it loads");
    }

    /// [`simple_loop`] with `str v4, [v22]` after the invariant add in the
    /// header; returns the function and the store.
    fn loop_with_store() -> (MachFunction, InstId) {
        let mut func = simple_loop();
        let store = func.push_inst(inst(AArch64Opcode::StrRI, vec![vreg(4), vreg(22), imm(0)]));
        func.block_mut(BlockId(1)).insts.insert(1, store);
        (func, store)
    }

    #[test]
    fn corruption_a_hoist_that_also_deletes_a_store_is_rejected() {
        let (before, store) = loop_with_store();
        let invariant = InstId(4);
        let mut hoisted = before.clone();
        hoist(&mut hoisted, invariant, BlockId(0));
        assert_eq!(
            validate_hoists(&before, &hoisted).verdict,
            ValidationVerdict::Validated,
            "the move alone validates"
        );
        let mut after = hoisted.clone();
        after.block_mut(BlockId(1)).insts.retain(|&x| x != store);
        assert_unproved(&before, &after, "changed besides the moved instructions");
    }

    #[test]
    fn corruption_a_hoist_that_also_replaces_an_instruction_is_rejected() {
        let (before, _) = loop_with_store();
        let mut after = before.clone();
        hoist(&mut after, InstId(4), BlockId(0));
        // `v4 = v4 + v2` replaced by a new `v4 = v4 - v2`.
        let replacement =
            after.push_inst(inst(AArch64Opcode::SubRR, vec![vreg(4), vreg(4), vreg(2)]));
        for x in after.block_mut(BlockId(1)).insts.iter_mut() {
            if *x == InstId(5) {
                *x = replacement;
            }
        }
        assert_unproved(&before, &after, "changed besides the moved instructions");
    }

    #[test]
    fn a_hoist_with_a_missing_loop_store_is_unproved_not_a_panic() {
        let (mut before, store) = loop_with_store();
        let load = before.push_inst(inst(AArch64Opcode::LdrRI, vec![vreg(7), vreg(8), imm(0)]));
        before.block_mut(BlockId(1)).insts.insert(0, load);
        let mut after = before.clone();
        hoist(&mut after, load, BlockId(0));
        after.block_mut(BlockId(1)).insts.retain(|&x| x != store);
        let verdict = std::panic::catch_unwind(|| validate_hoists(&before, &after).verdict)
            .expect("the validator returns a verdict");
        assert!(
            matches!(verdict, ValidationVerdict::Unproved(_)),
            "{verdict:?}"
        );
    }

    #[test]
    fn corruption_copying_an_instruction_instead_of_moving_it_is_rejected() {
        let before = simple_loop();
        let mut after = before.clone();
        let n = after.block(BlockId(0)).insts.len();
        after.block_mut(BlockId(0)).insts.insert(n - 1, InstId(4));
        assert_unproved(&before, &after, "laid out more than once");
    }

    #[test]
    fn corruption_hoisting_a_load_above_a_trap_carrier_is_rejected() {
        // `loop { trap_bounds(v5, v6); v7 = load [v8]; ... }`: the load is
        // guaranteed to run only after the carrier passes, so it may not run
        // in the preheader, where an out-of-bounds index would fault instead
        // of trapping.
        let mut before = simple_loop();
        let header = BlockId(1);
        let load = before.push_inst(inst(AArch64Opcode::LdrRI, vec![vreg(7), vreg(8), imm(0)]));
        before.block_mut(header).insts.insert(0, load);
        let mut unguarded = before.clone();
        hoist(&mut unguarded, load, BlockId(0));
        assert_eq!(
            validate_hoists(&before, &unguarded).verdict,
            ValidationVerdict::Validated,
            "the load heads every iteration without the carrier"
        );
        let trap = before.push_inst(inst(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(5), vreg(6)],
        ));
        before.block_mut(header).insts.insert(0, trap);
        let mut after = before.clone();
        hoist(&mut after, load, BlockId(0));
        assert_unproved(&before, &after, "can end execution before it");
    }

    /// A guard preheader: `bb0: v4 = 0; cmp v5, 0; b.eq bb2; b bb1`,
    /// `bb1: v2 = 7; v4 += v2; cmp v4, 100; b.lo bb1; b bb2`,
    /// `bb2: return v4`. Returns it and the invariant `v2 = 7`.
    fn guard_preheader_loop() -> (MachFunction, InstId) {
        let mut func = MachFunction::new(
            "pv_licm_guard_pre".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(4), imm(0)]),
        );
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::CmpRI, vec![vreg(5), imm(0)]),
        );
        push(&mut func, bb0, branch(CondCode::EQ, bb2));
        push(&mut func, bb0, jump(bb1));
        let invariant = push(
            &mut func,
            bb1,
            inst(AArch64Opcode::Movz, vec![vreg(2), imm(7)]),
        );
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRR, vec![vreg(4), vreg(4), vreg(2)]),
        );
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(100)]),
        );
        push(&mut func, bb1, branch(CondCode::LO, bb1));
        push(&mut func, bb1, jump(bb2));
        exit_block(&mut func, bb2, 4);
        (func, invariant)
    }

    /// Move `id` to block `to` at `index`.
    fn move_to(func: &mut MachFunction, id: InstId, to: BlockId, index: usize) {
        for b in func.block_order.clone() {
            func.block_mut(b).insts.retain(|&x| x != id);
        }
        func.block_mut(to).insts.insert(index, id);
    }

    #[test]
    fn a_constant_hoisted_into_a_guard_preheader_validates() {
        // The preheader also branches around the loop, so it is not the
        // loop's straight-line entry; the move is shown as a dominating move.
        let (before, invariant) = guard_preheader_loop();
        let mut after = before.clone();
        move_to(&mut after, invariant, BlockId(0), 1);
        assert_eq!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_a_hoist_behind_the_guard_branch_is_rejected() {
        // Placed after `b.eq`, it runs only when the loop is entered from
        // the fall-through; that happens to be every entry here, but the
        // check requires it ahead of every exit of the block.
        let (before, invariant) = guard_preheader_loop();
        let mut after = before.clone();
        move_to(&mut after, invariant, BlockId(0), 3);
        assert_unproved(&before, &after, "which leaves block 0");
    }

    #[test]
    fn corruption_a_hoisted_definition_read_where_the_loop_is_skipped_is_rejected() {
        // `bb2` also reads v2: on the path that skips the loop the input
        // read no definition of this run, so the move is not shown.
        let (mut before, invariant) = guard_preheader_loop();
        let read = before.push_inst(inst(AArch64Opcode::AddRR, vec![vreg(4), vreg(4), vreg(2)]));
        before.block_mut(BlockId(2)).insts.insert(0, read);
        let mut after = before.clone();
        move_to(&mut after, invariant, BlockId(0), 1);
        assert_unproved(&before, &after, "is live into block");
    }

    #[test]
    fn corruption_hoisting_into_a_block_that_does_not_dominate_is_rejected() {
        let (before, invariant) = guard_preheader_loop();
        let mut after = before.clone();
        move_to(&mut after, invariant, BlockId(2), 0);
        assert_unproved(&before, &after, "does not dominate");
    }

    /// Two loops in sequence: `bb0: v20 = 5; v21 = 0; v8 = 0; b bb1`,
    /// `bb1: v21 += 1; cmp v21, 10; b.lo bb1; b bb2`,
    /// `bb2: v7 = v20; v8 += v7; cmp v8, 100; b.lo bb2; b bb3`,
    /// `bb3: return v8`. Returns it and `v7 = v20`.
    fn two_loops(first_loop_writes_v20: bool) -> (MachFunction, InstId) {
        let mut func = MachFunction::new("pv_licm_two".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();
        for (dst, value) in [(20, 5), (21, 0), (8, 0)] {
            push(
                &mut func,
                bb0,
                inst(AArch64Opcode::MovI, vec![vreg(dst), imm(value)]),
            );
        }
        push(&mut func, bb0, jump(bb1));
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRI, vec![vreg(21), vreg(21), imm(1)]),
        );
        if first_loop_writes_v20 {
            push(
                &mut func,
                bb1,
                inst(AArch64Opcode::AddRI, vec![vreg(20), vreg(20), imm(1)]),
            );
        }
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::CmpRI, vec![vreg(21), imm(10)]),
        );
        push(&mut func, bb1, branch(CondCode::LO, bb1));
        push(&mut func, bb1, jump(bb2));
        let invariant = push(
            &mut func,
            bb2,
            inst(AArch64Opcode::MovR, vec![vreg(7), vreg(20)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::AddRR, vec![vreg(8), vreg(8), vreg(7)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::CmpRI, vec![vreg(8), imm(100)]),
        );
        push(&mut func, bb2, branch(CondCode::LO, bb2));
        push(&mut func, bb2, jump(bb3));
        exit_block(&mut func, bb3, 8);
        (func, invariant)
    }

    #[test]
    fn a_copy_hoisted_ahead_of_an_earlier_loop_validates() {
        // The vectorized-then-remainder shape: LICM put the second loop's
        // invariant in the block ahead of the first loop.
        let (before, invariant) = two_loops(false);
        let mut after = before.clone();
        hoist(&mut after, invariant, BlockId(0));
        assert_eq!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_an_operand_the_earlier_loop_writes_is_rejected() {
        let (before, invariant) = two_loops(true);
        let mut after = before.clone();
        hoist(&mut after, invariant, BlockId(0));
        assert_unproved(&before, &after, "is written between blocks 0 and 2");
    }

    /// An inner loop whose preheader is an outer loop's header, with the
    /// invariant in a conditional arm the inner loop skips once its counter
    /// passes 50 (the counter is never reset):
    /// `bb0: v0 = 10; v4 = 0; v9 = 0; b bb1`, `bb1: v0 += 1; b bb2`,
    /// `bb2: cmp v4, 50; b.hs bb4; b bb3`, `bb3: v2 = v0 + 7; b bb4`,
    /// `bb4: v4 += 1; cmp v4, 100; b.lo bb2; b bb5`,
    /// `bb5: v9 += v2; cmp v9, 1000; b.lo bb1; b bb6`, `bb6: return v9`.
    /// Returns it and `v2 = v0 + 7`.
    fn outer_loop_skipping_the_arm() -> (MachFunction, InstId) {
        let mut func =
            MachFunction::new("pv_licm_outer".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let [bb1, bb2, bb3, bb4, bb5, bb6] = std::array::from_fn(|_| func.create_block());
        for (dst, value) in [(0, 10), (4, 0), (9, 0)] {
            push(
                &mut func,
                bb0,
                inst(AArch64Opcode::MovI, vec![vreg(dst), imm(value)]),
            );
        }
        push(&mut func, bb0, jump(bb1));
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(1)]),
        );
        push(&mut func, bb1, jump(bb2));
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(50)]),
        );
        push(&mut func, bb2, branch(CondCode::HS, bb4));
        push(&mut func, bb2, jump(bb3));
        let invariant = push(
            &mut func,
            bb3,
            inst(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(7)]),
        );
        push(&mut func, bb3, jump(bb4));
        push(
            &mut func,
            bb4,
            inst(AArch64Opcode::AddRI, vec![vreg(4), vreg(4), imm(1)]),
        );
        push(
            &mut func,
            bb4,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(100)]),
        );
        push(&mut func, bb4, branch(CondCode::LO, bb2));
        push(&mut func, bb4, jump(bb5));
        push(
            &mut func,
            bb5,
            inst(AArch64Opcode::AddRR, vec![vreg(9), vreg(9), vreg(2)]),
        );
        push(
            &mut func,
            bb5,
            inst(AArch64Opcode::CmpRI, vec![vreg(9), imm(1000)]),
        );
        push(&mut func, bb5, branch(CondCode::LO, bb1));
        push(&mut func, bb5, jump(bb6));
        exit_block(&mut func, bb6, 9);
        (func, invariant)
    }

    #[test]
    fn corruption_hoisting_into_a_repeating_preheader_a_value_read_where_the_arm_is_skipped_is_rejected()
     {
        // The second outer iteration enters the inner loop with v4 = 100,
        // skips bb3 and adds the first iteration's v2 (11 + 7) in the input,
        // but 12 + 7 once the add runs in bb1.
        let (before, invariant) = outer_loop_skipping_the_arm();
        let mut after = before.clone();
        hoist(&mut after, invariant, BlockId(1));
        assert_unproved(&before, &after, "is live into the loop header");
        // With bb5 back to the function's return (no outer loop), bb1 runs
        // once: a read where the arm was skipped read an undefined register,
        // which the hoisted definition refines.
        let mut once = before.clone();
        let tail = once.block(BlockId(5)).insts.clone();
        once.block_mut(BlockId(5)).insts = vec![tail[0], *tail.last().expect("the jump")];
        let mut hoisted = once.clone();
        hoist(&mut hoisted, invariant, BlockId(1));
        assert_eq!(
            validate_hoists(&once, &hoisted).verdict,
            ValidationVerdict::Validated
        );
    }

    // ---- exception edges of an invoke target ----

    /// `bb0: v0 = 5; bl callee; b bb1` (an invoke landing at `pad_to`'s
    /// pad, bb2), `bb1: v2 = v0 + 1; return v2`, and the pad
    /// `bb2: b bb1` when `pad_reaches_source`, else `bb2: return v0`.
    /// Returns it and `v2 = v0 + 1`.
    fn invoke_ahead_of_use(pad_reaches_source: bool) -> (MachFunction, InstId) {
        use super::regions::{add_invoke, call};
        let mut func = MachFunction::new(
            "pv_licm_eh_move".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(0), imm(5)]),
        );
        push(&mut func, bb0, call("callee"));
        push(&mut func, bb0, jump(bb1));
        let moved = push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRI, vec![vreg(2), vreg(0), imm(1)]),
        );
        exit_block(&mut func, bb1, 2);
        if pad_reaches_source {
            push(&mut func, bb2, jump(bb1));
        } else {
            exit_block(&mut func, bb2, 0);
        }
        add_invoke(&mut func, bb0, bb2);
        (func, moved)
    }

    #[test]
    fn corruption_a_dominating_move_behind_an_invoke_call_is_rejected() {
        // If the callee unwinds, `bb0 -> bb2 -> bb1` returns v2 without the
        // moved add having run: the input returns 6.
        let (before, moved) = invoke_ahead_of_use(true);
        let mut behind = before.clone();
        move_to(&mut behind, moved, BlockId(0), 2);
        assert_unproved(
            &before,
            &behind,
            "whose exception edge leaves invoke block 0",
        );
        // Ahead of the call it runs on both edges.
        let mut ahead = before.clone();
        move_to(&mut ahead, moved, BlockId(0), 1);
        assert_eq!(
            validate_hoists(&before, &ahead).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn a_dominating_move_behind_an_invoke_call_whose_pad_leaves_validates() {
        // LICM's placement (after every call in the block) is shown when the
        // landing pad cannot reach the source without the block again.
        let (before, moved) = invoke_ahead_of_use(false);
        let mut behind = before.clone();
        move_to(&mut behind, moved, BlockId(0), 2);
        assert_eq!(
            validate_hoists(&before, &behind).verdict,
            ValidationVerdict::Validated
        );
    }

    /// An outer loop whose header is an invoke block and the inner loop's
    /// preheader: `bb0: v0 = 10; v1 = 20; v4 = 0; b bb1`,
    /// `bb1: v0 += 1; bl callee; b bb2` (an invoke landing at bb4),
    /// `bb2: v2 = v0 + v1; v4 += v2; cmp v4, 100; b.lo bb2; b bb3`,
    /// `bb3: cmp v4, 1000; b.lo bb1; b bb5`, `bb4: return v2`,
    /// `bb5: return v4`. Returns it and `v2 = v0 + v1`.
    fn invoke_preheader_loop() -> (MachFunction, InstId) {
        use super::regions::{add_invoke, call};
        let mut func =
            MachFunction::new("pv_licm_eh_pre".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let [bb1, bb2, bb3, bb4, bb5] = std::array::from_fn(|_| func.create_block());
        for (dst, value) in [(0, 10), (1, 20), (4, 0)] {
            push(
                &mut func,
                bb0,
                inst(AArch64Opcode::MovI, vec![vreg(dst), imm(value)]),
            );
        }
        push(&mut func, bb0, jump(bb1));
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRI, vec![vreg(0), vreg(0), imm(1)]),
        );
        push(&mut func, bb1, call("callee"));
        push(&mut func, bb1, jump(bb2));
        let invariant = push(
            &mut func,
            bb2,
            inst(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::AddRR, vec![vreg(4), vreg(4), vreg(2)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(100)]),
        );
        push(&mut func, bb2, branch(CondCode::LO, bb2));
        push(&mut func, bb2, jump(bb3));
        push(
            &mut func,
            bb3,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(1000)]),
        );
        push(&mut func, bb3, branch(CondCode::LO, bb1));
        push(&mut func, bb3, jump(bb5));
        exit_block(&mut func, bb4, 2);
        exit_block(&mut func, bb5, 4);
        add_invoke(&mut func, bb1, bb4);
        (func, invariant)
    }

    #[test]
    fn corruption_a_preheader_hoist_ahead_of_a_call_whose_pad_reads_it_is_rejected() {
        // On the second outer iteration an unwinding callee reaches bb4,
        // which returns the inner loop's last v2 (old v0 + v1) in the input
        // and the new v0 + v1 once the add runs ahead of the call.
        let (before, invariant) = invoke_preheader_loop();
        let mut ahead = before.clone();
        move_to(&mut ahead, invariant, BlockId(1), 1);
        assert_unproved(&before, &ahead, "is live into landing pad 4");
        // LICM's placement, after the call, is the loop-preheader move.
        let mut behind = before.clone();
        hoist(&mut behind, invariant, BlockId(1));
        assert_eq!(
            validate_hoists(&before, &behind).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_a_preheader_hoist_behind_a_call_landing_at_the_header_is_rejected() {
        // `bb0: v0 = 10; v1 = 20; v4 = 0; bl callee; b bb1`, an invoke
        // landing at the loop header bb1 itself: an unwinding callee enters
        // the loop without running what was placed after the call.
        use super::regions::{add_invoke, call};
        let mut before = simple_loop();
        let pre = BlockId(0);
        let header = BlockId(1);
        let bl = before.push_inst(call("callee"));
        let n = before.block(pre).insts.len();
        before.block_mut(pre).insts.insert(n - 1, bl);
        add_invoke(&mut before, pre, header);
        let mut behind = before.clone();
        hoist(&mut behind, InstId(4), pre);
        assert_unproved(
            &before,
            &behind,
            "whose exception edge leaves invoke block 0",
        );
        let mut ahead = before.clone();
        move_to(&mut ahead, InstId(4), pre, n - 1);
        assert_eq!(
            validate_hoists(&before, &ahead).verdict,
            ValidationVerdict::Validated
        );
    }

    // ---- memory disjointness (OD-127: bounded direct slot accesses only) ----

    /// [`simple_loop`] with two 16-byte fixed slots and two globals, their
    /// addresses in the preheader (`v20`, `v30` = slots 0 and 1; `v40`,
    /// `v41` = `g_a`, `g_b`), and `v21 = ldr [load]; str v4, [store]` at
    /// the head of the loop. Returns it and the load.
    fn loop_load_past_store(load: (u32, i64), store: (u32, i64)) -> (MachFunction, InstId) {
        let mut func = simple_loop();
        func.stack_slots.push(StackSlot::new(16, 8));
        func.stack_slots.push(StackSlot::new(16, 8));
        let pre = BlockId(0);
        let header = BlockId(1);
        let mut addresses = Vec::new();
        for (dst, slot) in [(20, 0), (30, 1)] {
            addresses.push(func.push_inst(inst(
                AArch64Opcode::AddPCRel,
                vec![
                    vreg(dst),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::StackSlot(StackSlotId(slot)),
                ],
            )));
        }
        for (dst, name) in [(40, "g_a"), (41, "g_b")] {
            addresses.push(func.push_inst(inst(
                AArch64Opcode::AddPCRel,
                vec![
                    vreg(dst),
                    vreg(dst + 10),
                    MachOperand::Symbol(name.to_string()),
                ],
            )));
        }
        for id in addresses.into_iter().rev() {
            func.block_mut(pre).insts.insert(0, id);
        }
        let load_id = func.push_inst(inst(
            AArch64Opcode::LdrRI,
            vec![vreg(21), vreg(load.0), imm(load.1)],
        ));
        let store_id = func.push_inst(inst(
            AArch64Opcode::StrRI,
            vec![vreg(4), vreg(store.0), imm(store.1)],
        ));
        func.block_mut(header).insts.insert(0, store_id);
        func.block_mut(header).insts.insert(0, load_id);
        (func, load_id)
    }

    fn hoist_load_past_store(load: (u32, i64), store: (u32, i64)) -> ValidationVerdict {
        let (before, load_id) = loop_load_past_store(load, store);
        let mut after = before.clone();
        hoist(&mut after, load_id, BlockId(0));
        validate_hoists(&before, &after).verdict
    }

    #[test]
    fn a_load_hoisted_past_a_store_to_another_bounded_slot_validates() {
        assert_eq!(
            hoist_load_past_store((20, 8), (30, 0)),
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_a_load_hoisted_past_a_store_without_bounded_slot_custody_is_rejected() {
        for (load, store, what) in [
            ((40, 0), (41, 0), "distinct symbols"),
            ((20, 0), (41, 0), "a slot against a global"),
            ((40, 0), (30, 0), "a global against a slot"),
            ((20, 0), (30, 16), "a store past its slot's end"),
            ((20, 0), (30, -8), "a store before its slot's start"),
            ((20, 12), (30, 0), "a load straddling its slot's end"),
            ((20, 0), (20, 8), "the same slot"),
        ] {
            match hoist_load_past_store(load, store) {
                ValidationVerdict::Unproved(reason) => assert!(
                    reason.contains("may write what it loads"),
                    "{what}: {reason}"
                ),
                other => panic!("{what}: expected unproved, got {other:?}"),
            }
        }
    }
}

#[test]
fn certified_records_cover_validated_passes_only() {
    let mut summary = PassValidationSummary::new(PassValidationConfig::enforce());
    let record = |pass: &str, validator: Option<ValidatorKind>, verdict: ValidationVerdict| {
        PassValidationRecord {
            pass_name: pass.to_string(),
            function_name: "f".to_string(),
            validator,
            verdict,
        }
    };
    summary.record(
        record(
            "pressure-aware-scheduler",
            Some(ValidatorKind::DependencePreservation),
            ValidationVerdict::Validated,
        ),
        true,
    );
    summary.record(
        record(
            "mem-pair-formation",
            Some(ValidatorKind::SymbolicRegionEquivalence),
            ValidationVerdict::Unproved("x differs".to_string()),
        ),
        true,
    );
    summary.record(record("gvn", None, ValidationVerdict::Uncovered), true);
    let runs = summary.certified_pass_runs("f");
    assert_eq!(runs.len(), 2, "uncovered passes get no record");
    let sched = runs
        .iter()
        .find(|r| r.pass_name == "pressure-aware-scheduler")
        .expect("scheduler record");
    assert!(sched.is_verified());
    assert_eq!(sched.local_checker.name, "dependence-preservation");
    assert_eq!(
        sched.local_checker.kind,
        "trust-cg-opt-translation-validation"
    );
    let pair = runs
        .iter()
        .find(|r| r.pass_name == "mem-pair-formation")
        .expect("mem-pair record");
    assert!(!pair.is_verified());
    assert_eq!(pair.failure_count, 1);
    assert_ne!(sched.obligation_hash, pair.obligation_hash);
}

/// The windowed load pairing once hoisted a load above the trap carrier
/// guarding it; the region check refuses that form, and mem-pair no longer
/// produces it.
#[test]
fn mem_pair_across_a_trap_carrier_is_refused_and_no_longer_formed() {
    let insts = vec![
        inst(AArch64Opcode::LdrRI, vec![vreg(1), vreg(10), imm(0)]),
        inst(AArch64Opcode::TrapBoundsCheckExact, vec![vreg(2), vreg(3)]),
        inst(AArch64Opcode::LdrRI, vec![vreg(4), vreg(10), imm(8)]),
        inst(AArch64Opcode::AddRR, vec![vreg(5), vreg(1), vreg(4)]),
        inst(AArch64Opcode::StrRI, vec![vreg(5), vreg(11), imm(0)]),
        ret(),
    ];
    let before = func_with(insts);
    // The form the pass used to produce: LDP ahead of the check.
    let mut paired = before.clone();
    let entry = paired.entry;
    let ldp = paired.push_inst(inst(
        AArch64Opcode::LdpRI,
        vec![vreg(1), vreg(4), vreg(10), imm(0)],
    ));
    let old = paired.block(entry).insts.clone();
    paired.block_mut(entry).insts = vec![ldp, old[1], old[3], old[4], old[5]];
    assert!(matches!(
        region::validate_regions(&before, &paired).verdict,
        ValidationVerdict::Unproved(_)
    ));
    // The pass leaves this block alone now, and pairs the same loads with
    // the check removed (so the refusal is the check's, not the fixture's).
    let mut after = before.clone();
    assert!(!crate::mem_pair::MemPairFormation.run(&mut after));
    let mut unchecked = before.clone();
    let check = unchecked.block(entry).insts[1];
    unchecked.block_mut(entry).insts.retain(|&x| x != check);
    assert!(crate::mem_pair::MemPairFormation.run(&mut unchecked));
}

#[test]
fn scope_spellings_round_trip() {
    for scope in [
        PassValidationScope::Schedulers,
        PassValidationScope::Dedicated,
        PassValidationScope::AllPasses,
    ] {
        assert_eq!(PassValidationScope::parse(scope.as_str()), Some(scope));
    }
    assert_eq!(PassValidationScope::parse("everything"), None);
}

#[test]
fn schedulers_scope_snapshots_only_permutation_passes() {
    let func = dependent_pair();
    let config = PassValidationConfig::diagnostic().with_scope(PassValidationScope::Schedulers);
    assert_eq!(
        config,
        PassValidationConfig::diagnostic(),
        "the default is the cheap tier"
    );
    let mut hook = PassValidationHook::new(config);
    assert!(matches!(
        hook.snapshot("pressure-aware-scheduler", &func).check,
        Some(PassSnapshot::Permutation(_))
    ));
    assert!(hook.snapshot("mem-pair-formation", &func).check.is_none());
    assert!(hook.snapshot("licm", &func).check.is_none());
    let mut all = PassValidationHook::new(
        PassValidationConfig::diagnostic().with_scope(PassValidationScope::AllPasses),
    );
    assert!(matches!(
        all.snapshot("gvn", &func).check,
        Some(PassSnapshot::Function(..))
    ));
    let mut dedicated = PassValidationHook::new(
        PassValidationConfig::diagnostic().with_scope(PassValidationScope::Dedicated),
    );
    assert!(dedicated.snapshot("gvn", &func).check.is_none());
    assert!(matches!(
        dedicated.snapshot("licm", &func).check,
        Some(PassSnapshot::Function(..))
    ));
    assert_eq!(
        PassValidationScope::Schedulers.widest(PassValidationScope::Dedicated),
        PassValidationScope::Dedicated
    );
    assert_eq!(
        PassValidationScope::AllPasses.widest(PassValidationScope::Dedicated),
        PassValidationScope::AllPasses
    );
}

/// A pass that leaves the function alone and says so.
struct Quiet(&'static str);

impl MachinePass for Quiet {
    fn name(&self) -> &str {
        self.0
    }

    fn run(&mut self, _func: &mut MachFunction) -> bool {
        false
    }
}

/// A function copy survives an unchanged run for the next snapshot, is
/// dropped when an unchanged claim is refuted, an unreported edit between
/// runs is not blamed on the next pass, and CFG lists are metadata.
#[test]
fn function_copy_is_reused_only_while_the_function_is_unchanged() {
    let config = PassValidationConfig::enforce();
    let mut hook = PassValidationHook::new(config);
    let mut summary = PassValidationSummary::new(config);
    let mut func = dependent_pair();
    let mut quiet = Quiet("licm");
    let snapshot = hook.snapshot(quiet.name(), &func);
    let changed = quiet.run(&mut func);
    hook.conclude(quiet.name(), snapshot, changed, &func, &mut summary);
    assert!(hook.shadow.is_some(), "an unchanged run keeps the copy");
    // An edit between runs makes the copy stale: the next snapshot copies
    // afresh, so this unchanged run validates.
    func.inst_mut(InstId(0)).operands[2] = imm(8);
    let snapshot = hook.snapshot(quiet.name(), &func);
    let changed = quiet.run(&mut func);
    hook.conclude(quiet.name(), snapshot, changed, &func, &mut summary);
    assert_eq!(summary.refuted(), 0);
    // A run that edits the function and reports no change is refuted.
    let mut liar = SwapFirstTwo {
        name: "licm",
        report: false,
    };
    let snapshot = hook.snapshot(liar.name(), &func);
    let changed = liar.run(&mut func);
    hook.conclude(liar.name(), snapshot, changed, &func, &mut summary);
    assert_eq!(summary.refuted(), 1);
    assert!(hook.shadow.is_none(), "a refuted copy is not kept");
    // Reordering CFG lists is not a change.
    let mut func = dependent_pair();
    let b = func.create_block();
    let entry = func.entry;
    func.add_edge(entry, b);
    let other = func.create_block();
    func.add_edge(entry, other);
    let snapshot = hook.snapshot("licm", &func);
    func.block_mut(entry).succs.reverse();
    hook.conclude("licm", snapshot, false, &func, &mut summary);
    assert_eq!(summary.refuted(), 1);
}

mod hoist_chains {
    use super::super::hoist::validate_hoists;
    use super::super::*;
    use super::{imm, inst, vreg};
    use trust_cg_ir::regs::X0;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, CondCode, InstId, MachFunction, MachInst, MachOperand, PReg,
        Signature,
    };

    static RET_X0: [PReg; 1] = [X0];

    fn push(func: &mut MachFunction, b: BlockId, i: MachInst) -> InstId {
        let id = func.push_inst(i);
        func.append_inst(b, id);
        id
    }

    /// `loop { v9 = movz #0x1234; v9 = movk #0x5678, lsl 16; v4 += v9 }`.
    fn chain_loop(read_between: bool) -> (MachFunction, Vec<InstId>) {
        let mut func = MachFunction::new("pv_chain".to_string(), Signature::new(vec![], vec![]));
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::MovI, vec![vreg(4), imm(0)]),
        );
        push(
            &mut func,
            bb0,
            inst(AArch64Opcode::B, vec![MachOperand::Block(bb1)]),
        );
        let movz = push(
            &mut func,
            bb1,
            inst(AArch64Opcode::Movz, vec![vreg(9), imm(0x1234)]),
        );
        if read_between {
            push(
                &mut func,
                bb1,
                inst(AArch64Opcode::AddRR, vec![vreg(4), vreg(4), vreg(9)]),
            );
        }
        let movk = push(
            &mut func,
            bb1,
            inst(AArch64Opcode::Movk, vec![vreg(9), imm(0x5678), imm(16)]),
        );
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::AddRR, vec![vreg(4), vreg(4), vreg(9)]),
        );
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::CmpRI, vec![vreg(4), imm(1000)]),
        );
        push(
            &mut func,
            bb1,
            inst(
                AArch64Opcode::BCond,
                vec![imm(CondCode::LO.encoding() as i64), MachOperand::Block(bb1)],
            ),
        );
        push(
            &mut func,
            bb1,
            inst(AArch64Opcode::B, vec![MachOperand::Block(bb2)]),
        );
        push(
            &mut func,
            bb2,
            inst(AArch64Opcode::MovR, vec![MachOperand::PReg(X0), vreg(4)]),
        );
        let mut ret = inst(AArch64Opcode::Ret, vec![]);
        ret.implicit_uses = &RET_X0;
        push(&mut func, bb2, ret);
        (func, vec![movz, movk])
    }

    fn hoist_all(func: &mut MachFunction, ids: &[InstId]) {
        let pre = BlockId(0);
        for &id in ids {
            for b in func.block_order.clone() {
                func.block_mut(b).insts.retain(|&x| x != id);
            }
            let n = func.block(pre).insts.len();
            func.block_mut(pre).insts.insert(n - 1, id);
        }
    }

    #[test]
    fn a_constant_chain_hoisted_as_a_unit_validates() {
        let (before, chain) = chain_loop(false);
        let mut after = before.clone();
        hoist_all(&mut after, &chain);
        assert_eq!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Validated
        );
    }

    #[test]
    fn corruption_a_chain_with_a_reader_between_its_members_is_rejected() {
        // The loop reads the half-built constant between MOVZ and MOVK.
        let (before, chain) = chain_loop(true);
        let mut after = before.clone();
        hoist_all(&mut after, &chain);
        assert!(matches!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Unproved(_)
        ));
    }

    #[test]
    fn corruption_half_a_chain_hoisted_is_rejected() {
        let (before, chain) = chain_loop(false);
        let mut after = before.clone();
        hoist_all(&mut after, &chain[..1]);
        assert!(matches!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Unproved(_)
        ));
    }

    #[test]
    fn corruption_a_reordered_chain_is_rejected() {
        let (before, chain) = chain_loop(false);
        let mut after = before.clone();
        hoist_all(&mut after, &[chain[1], chain[0]]);
        assert!(matches!(
            validate_hoists(&before, &after).verdict,
            ValidationVerdict::Unproved(_)
        ));
    }
}

/// A 256-bit interface digest for these tests: the 128-bit validator digest
/// of [`hash_function_interface`], zero-extended (trust-cg-verify supplies
/// SHA-256 in production).
fn test_interface_digest(func: &MachFunction) -> [u8; 32] {
    let mut h = Digest128::default();
    hash_function_interface(func, &mut h);
    let mut out = [0u8; 32];
    out[..16].copy_from_slice(&h.finish128().to_le_bytes());
    out
}

/// Two independent constants, each stored: swapping them preserves the
/// stores' values; changing a constant does not.
fn two_stored_constants() -> MachFunction {
    func_with(vec![
        inst(AArch64Opcode::MovI, vec![vreg(1), imm(1)]),
        inst(AArch64Opcode::MovI, vec![vreg(2), imm(2)]),
        inst(AArch64Opcode::StrRI, vec![vreg(1), vreg(10), imm(0)]),
        inst(AArch64Opcode::StrRI, vec![vreg(2), vreg(10), imm(8)]),
        ret(),
    ])
}

/// Adds one to the first `MovI`'s immediate and reports `report`.
struct BumpFirstConstant {
    name: &'static str,
    report: bool,
}

impl MachinePass for BumpFirstConstant {
    fn name(&self) -> &str {
        self.name
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        if let Some(inst) = func
            .insts
            .iter_mut()
            .find(|inst| inst.opcode == AArch64Opcode::MovI)
            && let Some(MachOperand::Imm(value)) = inst.operands.get_mut(1)
        {
            *value += 1;
        }
        self.report
    }
}

/// Run `pass` once through a hook under `config`, with or without
/// transitions, and return the summary.
fn run_hooked(
    config: PassValidationConfig,
    transitions: bool,
    func: &mut MachFunction,
    pass: &mut dyn MachinePass,
    summary: &mut PassValidationSummary,
) {
    let mut hook = PassValidationHook::new(config)
        .with_transitions(transitions.then_some(test_interface_digest as FunctionInterfaceDigest));
    let snapshot = hook.snapshot(pass.name(), func);
    let changed = pass.run(func);
    hook.conclude(pass.name(), snapshot, changed, func, summary);
}

#[test]
fn transitions_record_each_interface_change_with_its_verdict() {
    let config = PassValidationConfig::enforce();
    let mut summary = PassValidationSummary::new(config);
    let mut func = two_stored_constants();
    let start = test_interface_digest(&func);

    // A dedicated validator in scope: the summary and the transition agree.
    run_hooked(
        config,
        true,
        &mut func,
        &mut SwapFirstTwo {
            name: "pressure-aware-scheduler",
            report: true,
        },
        &mut summary,
    );
    // No validator in the dedicated scope: the summary records it uncovered,
    // the transition carries the generic region check's verdict.
    run_hooked(
        config,
        true,
        &mut func,
        &mut SwapFirstTwo {
            name: "some-uncovered-pass",
            report: true,
        },
        &mut summary,
    );
    // A rewrite of a stored constant: not shown equal.
    run_hooked(
        config,
        true,
        &mut func,
        &mut BumpFirstConstant {
            name: "some-other-pass",
            report: true,
        },
        &mut summary,
    );
    // A run that reports no change but rewrites a constant (silent).
    run_hooked(
        config,
        true,
        &mut func,
        &mut BumpFirstConstant {
            name: "idle-pass",
            report: false,
        },
        &mut summary,
    );

    let t = &summary.transitions;
    assert_eq!(
        t.len(),
        4,
        "the idle run changed the constant without a report: {t:?}"
    );
    assert_eq!(t[0].before, start);
    for pair in t.windows(2) {
        assert_eq!(pair[0].after, pair[1].before, "consecutive runs chain");
    }
    assert_eq!(t[0].validator, Some(ValidatorKind::DependencePreservation));
    assert_eq!(t[0].verdict, ValidationVerdict::Validated);
    assert_eq!(t[1].pass_name, "some-uncovered-pass");
    assert_eq!(
        t[1].validator,
        Some(ValidatorKind::SymbolicRegionEquivalence)
    );
    assert_eq!(t[1].verdict, ValidationVerdict::Validated);
    assert_eq!(
        t[2].validator,
        Some(ValidatorKind::SymbolicRegionEquivalence)
    );
    assert!(
        !t[2].verdict.is_validated(),
        "a changed stored constant is not shown equal: {:?}",
        t[2].verdict
    );
    // The idle pass bumped the constant while reporting no change.
    assert!(!t[3].reported_change);
    assert_eq!(t[3].validator, Some(ValidatorKind::UnchangedClaim));
    assert_refuted(&t[3].verdict, "interface");

    // The summary is the dedicated scope's alone: composition-only verdicts
    // change no counter and no refusal.
    assert_eq!(summary.validated(), 1);
    assert_eq!(summary.uncovered(), 2);
    assert_eq!(summary.refuted() + summary.unproved(), 0);
    assert!(
        summary
            .first_refusal(PassValidationPolicy::Enforce)
            .is_none()
    );
}

#[test]
fn transitions_leave_the_summary_unchanged() {
    for config in [
        PassValidationConfig::diagnostic(),
        PassValidationConfig::enforce(),
        PassValidationConfig::enforce().with_scope(PassValidationScope::AllPasses),
    ] {
        let mut plain = PassValidationSummary::new(config);
        let mut recorded = PassValidationSummary::new(config);
        for (summary, transitions) in [(&mut plain, false), (&mut recorded, true)] {
            let mut func = two_stored_constants();
            for name in ["pressure-aware-scheduler", "gvn", "licm"] {
                run_hooked(
                    config,
                    transitions,
                    &mut func,
                    &mut SwapFirstTwo { name, report: true },
                    summary,
                );
            }
            run_hooked(
                config,
                transitions,
                &mut func,
                &mut BumpFirstConstant {
                    name: "cse",
                    report: true,
                },
                summary,
            );
        }
        assert!(plain.transitions.is_empty());
        assert_eq!(recorded.transitions.len(), 4, "{config:?}");
        recorded.transitions.clear();
        assert_eq!(plain, recorded, "{config:?}");
    }
}

#[test]
fn transitions_run_without_an_active_policy() {
    let config = PassValidationConfig::off();
    let mut summary = PassValidationSummary::new(config);
    let mut func = two_stored_constants();
    run_hooked(
        config,
        true,
        &mut func,
        &mut SwapFirstTwo {
            name: "gvn",
            report: true,
        },
        &mut summary,
    );
    assert!(summary.passes.is_empty(), "off records no counter");
    assert_eq!(summary.transitions.len(), 1);
    assert_eq!(summary.transitions[0].verdict, ValidationVerdict::Validated);
}

#[test]
fn unvalidated_steps_outside_a_manager_record_uncovered_transitions() {
    let mut summary = PassValidationSummary::new(PassValidationConfig::enforce());
    let mut func = two_stored_constants();
    let digest = Some(test_interface_digest as FunctionInterfaceDigest);
    let before = digest.map(|d| d(&func));
    record_unvalidated_transition(digest, "cegis-superopt", before, &func, &mut summary);
    assert!(summary.transitions.is_empty(), "no change, no transition");
    BumpFirstConstant {
        name: "x",
        report: true,
    }
    .run(&mut func);
    record_unvalidated_transition(digest, "cegis-superopt", before, &func, &mut summary);
    assert_eq!(summary.transitions.len(), 1);
    assert_eq!(summary.transitions[0].verdict, ValidationVerdict::Uncovered);
    assert_eq!(summary.transitions[0].validator, None);
    record_unvalidated_transition(None, "cegis-superopt", before, &func, &mut summary);
    assert_eq!(summary.transitions.len(), 1, "no digest, nothing recorded");

    let mut scheduled = two_stored_constants();
    run_validated_with_transitions(
        PassValidationConfig::diagnostic(),
        digest,
        &mut SwapFirstTwo {
            name: "pressure-aware-scheduler",
            report: true,
        },
        &mut scheduled,
        &mut summary,
    );
    assert_eq!(summary.transitions.len(), 2);
    assert_eq!(summary.transitions[1].verdict, ValidationVerdict::Validated);
}

#[test]
fn pass_manager_records_a_contiguous_transition_chain() {
    let mut func = two_stored_constants();
    let start = test_interface_digest(&func);
    let mut pm = crate::PassManager::new()
        .with_pass(Box::new(SwapFirstTwo {
            name: "gvn",
            report: true,
        }))
        .with_pass(Box::new(SwapFirstTwo {
            name: "pressure-aware-scheduler",
            report: true,
        }))
        .with_pass_validation(PassValidationConfig::enforce());
    pm.set_transition_digest(Some(test_interface_digest));
    let stats = pm.run_once_with_stats(&mut func);
    let t = &stats.pass_validation.transitions;
    assert_eq!(t.len(), 2);
    assert_eq!(t[0].before, start);
    assert_eq!(t[0].after, t[1].before);
    assert_eq!(t[1].after, test_interface_digest(&func));
    assert!(t.iter().all(|t| t.verdict.is_validated()), "{t:?}");
}

#[test]
fn the_interface_digest_names_the_function_and_ignores_metadata() {
    let func = two_stored_constants();
    let mut renamed = func.clone();
    renamed.name = "other".to_string();
    assert_ne!(
        test_interface_digest(&func),
        test_interface_digest(&renamed)
    );
    let mut annotated = func.clone();
    let entry = annotated.entry;
    annotated.block_mut(entry).preds.push(entry);
    annotated.next_vreg += 7;
    annotated.text_align_log2 = 5;
    annotated.lowering_provenance.insert(
        trust_cg_ir::InstId(0),
        trust_cg_ir::LoweringProvenance::UNATTRIBUTED,
    );
    assert_eq!(
        test_interface_digest(&func),
        test_interface_digest(&annotated),
        "CFG lists, ID counters, the alignment hint and provenance are not part of the interface"
    );
}

/// Every side table a later stage check or the encoder reads is part of the
/// interface: changing one between two links breaks the chain.
#[test]
fn the_interface_digest_covers_the_side_tables_later_checks_read() {
    let func = two_stored_constants();
    let base = test_interface_digest(&func);
    type Mutation = (&'static str, fn(&mut MachFunction));
    let mutations: [Mutation; 8] = [
        ("stack_limit_overflow_block", |f| {
            f.stack_limit_overflow_block = Some(f.entry)
        }),
        ("trap_expansions", |f| {
            f.trap_expansions.push(trust_cg_ir::TrapExpansionRecord {
                carrier: f.insts[0].clone(),
                insts: vec![trust_cg_ir::InstId(1)],
            })
        }),
        ("call_abi_facts", |f| {
            f.call_abi_facts.insert(
                trust_cg_ir::InstId(0),
                trust_cg_ir::CallAbiFacts {
                    callee: Some("g".to_string()),
                    stack_arg_bytes: 0,
                    stack_stores: Vec::new(),
                    aggregate_stack_args: false,
                    hidden_result_pointer: false,
                    by_reference_argument_copies: false,
                    variadic: false,
                    callee_saved: trust_cg_ir::CalleeSavedSet::Aapcs64,
                },
            );
        }),
        ("incoming_stack_arg_bytes", |f| {
            f.incoming_stack_arg_bytes = Some(16)
        }),
        ("function_target_features", |f| {
            f.function_target_features = trust_cg_ir::TargetFeatureSet::EMPTY
                .with_feature(trust_cg_ir::AArch64IsaFeature::Lse)
                .expect("a declared feature");
        }),
        ("noalias_params", |f| f.noalias_params.push(3)),
        ("source_fusion_targets", |f| {
            f.source_fusion_targets.insert(
                trust_cg_ir::SourceInstId { block: 0, index: 0 },
                trust_cg_ir::SourceInstId { block: 0, index: 1 },
            );
        }),
        ("profile_ordered", |f| f.profile_ordered = true),
    ];
    for (field, mutate) in mutations {
        let mut changed = func.clone();
        mutate(&mut changed);
        assert_ne!(base, test_interface_digest(&changed), "{field}");
    }
}
