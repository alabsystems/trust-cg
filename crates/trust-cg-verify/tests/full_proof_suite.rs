// trust-cg-verify/tests/full_proof_suite.rs - Full ProofDatabase verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Integration tests for ProofDatabase verification. The default lane keeps
// expensive checks bounded with representative subsets and report/category
// accounting. Enable the slow-full-database feature for full-database
// verification lanes.
//
// These tests exercise the verification pipeline end-to-end:
//   ProofDatabase -> VerificationRunner::run_all() -> VerificationRunReport
//
// Reference: crates/trust-cg-verify/src/proof_database.rs
//            crates/trust-cg-verify/src/verification_runner.rs

use trust_cg_verify::VerificationStrength;
use trust_cg_verify::proof_database::{ProofCategory, ProofDatabase};
use trust_cg_verify::regalloc_proofs::{
    proof_greedy_fixed_register_respect, proof_greedy_no_interference,
    proof_greedy_stack_offset_correctness,
};
use trust_cg_verify::source_bound_frame::FRAME_OBLIGATION_NAME;
use trust_cg_verify::verification_runner::{
    AYVerificationMode, VerificationRunReport, VerificationRunner, select_auto_mode,
};
use trust_cg_verify::verify::VerificationResult;

/// The registry rows concrete evaluation cannot decide, each with the reason
/// it must give. The set is exact: a row that leaves it (evaluation decides
/// it) or joins it fails the lanes below.
///
/// * The source-bound AArch64 leaf-frame theorem quantifies over an ARBITRARY
///   initial memory, the zero-argument uninterpreted array `entry_memory`. The
///   evaluator samples bitvector inputs only, and declining an uninterpreted
///   function is its pinned contract (`lowering_proof`'s
///   `evaluator_declines_the_registry_frame_theorem_naming_its_uninterpreted_memory`):
///   a constant-default memory would prove the theorem for one memory, not
///   all. The row's proof belongs to the strict AY gate, whose
///   `source_bound_leaf_frame_corpus_addition_is_exact_live_and_nondegenerate`
///   keeps it in that corpus with no solver-capacity debt (NEW-CG-FULLDB).
///
/// The fifteen relational-precondition rows that were the vacuous-sample
/// `Unknown` here (TRUSTCG-02) are not in this set: the multi-input sweep's
/// precondition-directed trials reach them, so they are `Valid` like any
/// other sampled row (NEW-CG-SAMPLER).
fn expected_unknowns() -> Vec<(&'static str, &'static str)> {
    vec![(
        FRAME_OBLIGATION_NAME,
        "cannot concretely evaluate uninterpreted function 'entry_memory'",
    )]
}

/// The report's `Unknown` rows must be exactly the [`expected_unknowns`]
/// present in the run, each with its reason. Returns how many there are.
fn assert_unknowns_are_exactly_the_expected(report: &VerificationRunReport) -> usize {
    let expected = expected_unknowns();
    let mut seen = 0;
    for r in &report.results {
        let reason_for = expected
            .iter()
            .find(|(name, _)| *name == r.name)
            .map(|(_, reason)| *reason);
        match (&r.result, reason_for) {
            (VerificationResult::Unknown { reason }, Some(required)) => assert!(
                reason.contains(required),
                "'{}' must be Unknown because {required:?}, got: {reason}",
                r.name
            ),
            (VerificationResult::Unknown { reason }, None) => panic!(
                "STRICT: '{}' was UNKNOWN (could not be decided): {reason}",
                r.name
            ),
            (other, Some(_)) => panic!(
                "'{}' is in the audited evaluation-Unknown set but returned {other:?}; if \
                 evaluation now decides it, remove it from the set",
                r.name
            ),
            (_, None) => continue,
        }
        seen += 1;
    }
    seen
}

/// Number of GENUINELY-provable (structurally non-degenerate, `trust_ir_expr !=
/// aarch64_expr`) obligations in `cat`. Under the STRICT proven-honesty rule
/// (task #61), ONLY these count as passed — a degenerate X==X obligation is a
/// model-consistency check that proves nothing, so it is neither passed nor a
/// failure (it is reported separately as degenerate debt).
fn genuine_count_in_category(db: &ProofDatabase, cat: ProofCategory) -> usize {
    db.by_category(cat)
        .iter()
        .filter(|p| p.obligation.is_genuinely_proven())
        .count()
}

fn assert_report_matches_database(report: &VerificationRunReport, db: &ProofDatabase) {
    assert_eq!(
        report.total(),
        db.len(),
        "Report total ({}) does not match database size ({})",
        report.total(),
        db.len()
    );

    let breakdowns = report.by_category();
    let bd_sum: usize = breakdowns.iter().map(|b| b.total).sum();
    assert_eq!(
        bd_sum,
        report.total(),
        "Sum of per-category proof counts ({}) != total ({})",
        bd_sum,
        report.total()
    );

    for cat in ProofCategory::all_categories() {
        let expected = db.count_by_category(*cat);
        let actual = breakdowns
            .iter()
            .find(|b| b.category == *cat)
            .map(|b| b.total)
            .unwrap_or(0);
        assert_eq!(
            actual, expected,
            "Category {:?}: report has {} proofs, db has {}",
            cat, actual, expected
        );

        if expected == 0 {
            continue;
        }

        let bd = breakdowns
            .iter()
            .find(|b| b.category == *cat)
            .expect("non-empty category should have a report breakdown");

        // STRICT (task #61): `bd.passed` credits ONLY genuinely-provable
        // (non-degenerate) obligations. A degenerate X==X obligation evaluates
        // Valid trivially but proves nothing, so it is excluded from `passed`
        // (and is NOT a failure/unknown). The honest invariant: every
        // non-degenerate obligation passes, NONE fails, NONE is unknown.
        //
        // The audited evaluation-Unknown rows (`expected_unknowns`) are the
        // one exception: evaluation cannot decide them, so they are neither
        // passed nor failed but Unknown.
        let unknown_names: Vec<&str> = expected_unknowns().iter().map(|(n, _)| *n).collect();
        let in_cat = db.by_category(*cat);
        let unknown_in_cat: Vec<_> = in_cat
            .iter()
            .filter(|p| unknown_names.contains(&p.obligation.name.as_str()))
            .collect();
        let genuine = genuine_count_in_category(db, *cat);
        let expected_genuine = genuine
            - unknown_in_cat
                .iter()
                .filter(|p| p.obligation.is_genuinely_proven())
                .count();
        assert_eq!(
            bd.passed,
            expected_genuine,
            "Category {:?}: expected all {} GENUINE (non-degenerate) proofs outside the \
             audited evaluation-Unknown rows to pass, got {} passed (total {} incl. {} \
             degenerate X==X that prove nothing and {} audited Unknown)",
            cat,
            expected_genuine,
            bd.passed,
            expected,
            expected - genuine,
            unknown_in_cat.len()
        );
        assert_eq!(bd.failed, 0, "Category {:?} had failed proofs", cat);
        assert_eq!(
            bd.unknown,
            unknown_in_cat.len(),
            "Category {:?}: the only unknown proofs may be its audited evaluation-Unknown rows",
            cat
        );
    }
}

fn assert_report_has_exhaustive_and_statistical(report: &VerificationRunReport) {
    let exhaustive = report.exhaustive_count();
    let statistical = report.statistical_count();

    assert!(
        exhaustive > 0,
        "Expected some exhaustive proofs (8-bit), got 0"
    );
    assert!(
        statistical > 0,
        "Expected some statistical proofs (32/64-bit), got 0"
    );

    println!();
    println!("Verification strength distribution:");
    println!(
        "  Exhaustive:  {} proofs (small-width, complete)",
        exhaustive
    );
    println!(
        "  Statistical: {} proofs (large-width, 100K+ samples)",
        statistical
    );
    println!("  Total:       {} proofs", report.total());
}

fn representative_default_database() -> ProofDatabase {
    let full_db = ProofDatabase::new();
    let mut subset = Vec::new();

    for cat in ProofCategory::all_categories() {
        let proof = full_db
            .by_category(*cat)
            .into_iter()
            .next()
            .unwrap_or_else(|| panic!("Category {:?} ({}) has 0 proofs", cat, cat.name()));
        subset.push(proof.clone());
    }

    assert_eq!(
        subset.len(),
        ProofCategory::all_categories().len(),
        "representative default database should include one proof per category"
    );
    assert!(
        subset.iter().any(|proof| {
            matches!(
                VerificationStrength::for_obligation(&proof.obligation),
                VerificationStrength::Exhaustive
            )
        }),
        "representative default database should include an exhaustive proof"
    );
    assert!(
        subset.iter().any(|proof| {
            matches!(
                VerificationStrength::for_obligation(&proof.obligation),
                VerificationStrength::Statistical { .. }
            )
        }),
        "representative default database should include a statistical proof"
    );

    ProofDatabase::from_proofs(subset)
}

fn run_and_assert_all_pass(db: &ProofDatabase, summary_title: &str, report_title: &str) {
    let summary = db.summary();

    println!();
    println!("================================================================");
    println!("  {}", summary_title);
    println!("================================================================");
    println!();
    println!("{}", summary);

    let runner = VerificationRunner::new(db);
    let report = runner.run_all();

    println!();
    println!("================================================================");
    println!("  {}", report_title);
    println!("================================================================");
    println!();
    println!("{}", report);

    // STRICT proven-honesty (task #61): the honest invariant is NOT "every
    // obligation is genuinely proven" — the database deliberately KEEPS degenerate
    // X==X obligations as documented model-consistency / debt, and those prove
    // nothing. The honest, non-weakened invariant is:
    //   (a) ZERO soundness failures and ZERO unknowns (nothing the evaluator
    //       disproved or could not decide), AND
    //   (b) every NON-degenerate obligation passes — i.e.
    //       genuinely_passed() == (total - degenerate_debt_count()), with the
    //       degenerate count accounted SEPARATELY (never as a pass).
    // This makes the drop VISIBLE (genuinely_passed < total) rather than hiding it.
    // The single exception to (a) is the audited evaluation-Unknown set
    // (`expected_unknowns`): exactly those rows, each for its stated reason.
    assert_eq!(
        report.failed(),
        0,
        "STRICT: {} obligation(s) were DISPROVED (soundness failure):\n{}",
        report.failed(),
        report
    );
    let unknown = assert_unknowns_are_exactly_the_expected(&report);
    let degenerate = report.degenerate_debt_count();
    assert_eq!(
        report.genuinely_passed(),
        report.total() - degenerate - unknown,
        "STRICT: every NON-degenerate obligation must pass. genuinely_passed={} but \
         total - degenerate_debt - audited_unknown = {} - {} - {} = {}:\n{}",
        report.genuinely_passed(),
        report.total(),
        degenerate,
        unknown,
        report.total() - degenerate - unknown,
        report
    );

    assert_report_matches_database(&report, db);
    assert_report_has_exhaustive_and_statistical(&report);

    println!("================================================================");
    println!(
        "  RESULT (STRICT): {}/{} GENUINELY proven; {} degenerate X==X excluded (prove nothing)",
        report.genuinely_passed(),
        report.total(),
        degenerate,
    );
    println!("================================================================");
}

// ===========================================================================
// Core integration test: run a representative proof subset
// ===========================================================================

#[test]
fn full_proof_suite_all_pass() {
    let db = representative_default_database();
    run_and_assert_all_pass(
        &db,
        "Trust Codegen Default Proof Suite - Representative Summary",
        "Trust Codegen Default Proof Suite - Verification Run Report",
    );
}

// Explicit slow lane for full-database verification:
// scripts/trust_cargo.sh test -p trust-cg-verify --features slow-full-database \
//   --test full_proof_suite full_proof_suite_all_pass_full_database -- --nocapture
#[cfg(feature = "slow-full-database")]
#[test]
fn full_proof_suite_all_pass_full_database() {
    let db = ProofDatabase::new();

    // Verify the database has a meaningful number of proofs.
    assert!(
        db.len() >= 300,
        "Expected at least 300 proofs in the database, got {}. \
         New proof categories may need to be wired into ProofDatabase.",
        db.len()
    );

    run_and_assert_all_pass(
        &db,
        "Trust Codegen Full Proof Suite - ProofDatabase Summary",
        "Trust Codegen Full Proof Suite - Verification Run Report",
    );
}

// ===========================================================================
// Every category must be represented in the database
// ===========================================================================

#[test]
fn full_proof_suite_every_category_populated() {
    let db = ProofDatabase::new();
    let categories = ProofCategory::all_categories();

    // 35 categories (was 34): #71 added WebAssembly Lowering — the 54 GENUINE
    // non-degenerate wasm scalar refinement proofs (shifts/comparisons/float
    // comparisons/negate/casts). (The 5 fully-vacuous categories whose every
    // proof was a retracted X==X self-equality were removed in #62 — NzcvFlags,
    // CopyPropagation, DeadCodeElimination, AnePrecision, TailCallOptimization.)
    // Remaining: Arithmetic, Division, FloatingPoint, Comparison, Branch,
    // Peephole, Optimization, ConstantFolding, CseLicm, CfgSimplification,
    // Memory, LoadStoreLowering (#422), NeonLowering, NeonEncoding,
    // Vectorization, RegAlloc, BitwiseShift, ConstantMaterialization,
    // AddressMode, FrameLayout, InstructionScheduling, MachOEmission,
    // LoopOptimization, StrengthReduction, CmpCombine, Gvn, IfConversion,
    // FpConversion, ExtensionTruncation, AtomicOperations, CallLowering,
    // x86-64 Lowering, Switch Lowering, RISC-V Lowering, WebAssembly Lowering.
    assert_eq!(
        categories.len(),
        35,
        "Expected 35 proof categories, got {}",
        categories.len()
    );

    for cat in categories {
        let count = db.count_by_category(*cat);
        assert!(
            count > 0,
            "Category {:?} ({}) has 0 proofs — it should have at least one",
            cat,
            cat.name()
        );
    }
}

// ===========================================================================
// Every category is accounted for independently
// ===========================================================================

#[test]
fn full_proof_suite_each_category_passes() {
    let db = ProofDatabase::new();
    let mut counted_total = 0;

    // full_proof_suite_all_pass verifies one representative proof per category
    // and checks report pass counts. The opt-in slow lane verifies the full
    // database explicitly, so this test only guards category partitioning.
    for cat in ProofCategory::all_categories() {
        let proofs = db.by_category(*cat);
        let count = proofs.len();
        let expected = db.count_by_category(*cat);

        assert_eq!(
            count, expected,
            "Category {:?}: category filter returned {} proofs, db has {}",
            cat, count, expected
        );

        assert!(
            count > 0,
            "Category {:?} ({}) has 0 proofs",
            cat,
            cat.name()
        );

        for proof in proofs {
            assert_eq!(
                proof.category, *cat,
                "Category {:?}: proof '{}' was returned with category {:?}",
                cat, proof.obligation.name, proof.category
            );
        }

        counted_total += count;
    }

    assert_eq!(
        counted_total,
        db.len(),
        "Sum of per-category proof counts ({}) != database size ({})",
        counted_total,
        db.len()
    );
}

// ===========================================================================
// Parallel verification produces same results as sequential
// ===========================================================================

#[test]
fn full_proof_suite_parallel_matches_sequential() {
    // Exercise the parallel runner's chunking/threading on a bounded subset.
    // The full-database sequential+parallel comparison is available in the
    // opt-in slow-full-database lane.
    let full_db = ProofDatabase::new();
    let subset: Vec<_> = full_db
        .by_category(ProofCategory::Arithmetic)
        .into_iter()
        .take(8)
        .cloned()
        .collect();
    assert!(
        subset.len() >= 5,
        "need at least 5 Arithmetic proofs for meaningful parallel test, got {}",
        subset.len()
    );

    let db = ProofDatabase::from_proofs(subset);
    let runner = VerificationRunner::new(&db);

    let sequential = runner.run_all();
    let parallel = runner.run_parallel(4);

    assert_eq!(
        sequential.total(),
        parallel.total(),
        "Parallel run returned different proof count: seq={}, par={}",
        sequential.total(),
        parallel.total()
    );
    assert_eq!(
        sequential.passed(),
        parallel.passed(),
        "Parallel run has different pass count: seq={}, par={}",
        sequential.passed(),
        parallel.passed()
    );
    // STRICT (task #61): the Arithmetic subset includes degenerate X==X ALU
    // identities (Iadd_I8 -> ADD etc.) that prove nothing, so all_passed() (which
    // now requires every obligation be GENUINELY proven) is honestly false. The
    // parity invariant we care about is: ZERO disproved/unknown in BOTH runs, and
    // identical genuine + degenerate accounting across seq/parallel.
    assert_eq!(
        sequential.failed(),
        0,
        "Sequential subset had failures:\n{}",
        sequential
    );
    assert_eq!(
        parallel.failed(),
        0,
        "Parallel subset had failures:\n{}",
        parallel
    );
    assert_eq!(
        sequential.unknown(),
        0,
        "Sequential subset had unknowns:\n{}",
        sequential
    );
    assert_eq!(
        parallel.unknown(),
        0,
        "Parallel subset had unknowns:\n{}",
        parallel
    );
    assert_eq!(
        sequential.genuinely_passed(),
        parallel.genuinely_passed(),
        "seq/parallel disagree on genuinely_passed: {} vs {}",
        sequential.genuinely_passed(),
        parallel.genuinely_passed()
    );
    assert_eq!(
        sequential.degenerate_debt_count(),
        parallel.degenerate_debt_count(),
        "seq/parallel disagree on degenerate_debt_count: {} vs {}",
        sequential.degenerate_debt_count(),
        parallel.degenerate_debt_count()
    );
}

// Explicit slow lane for full-database sequential-vs-parallel parity:
// scripts/trust_cargo.sh test -p trust-cg-verify --features slow-full-database \
//   --test full_proof_suite full_proof_suite_parallel_matches_sequential_full_database
#[cfg(feature = "slow-full-database")]
#[test]
fn full_proof_suite_parallel_matches_sequential_full_database() {
    let db = ProofDatabase::new();
    let runner = VerificationRunner::new(&db);

    let sequential = runner.run_all();
    let parallel = runner.run_parallel(4);

    assert_eq!(
        sequential.total(),
        parallel.total(),
        "Parallel run returned different proof count: seq={}, par={}",
        sequential.total(),
        parallel.total()
    );
    assert_eq!(
        sequential.passed(),
        parallel.passed(),
        "Parallel run has different pass count: seq={}, par={}",
        sequential.passed(),
        parallel.passed()
    );
    // STRICT (task #61): the full database keeps degenerate X==X obligations
    // (documented model-consistency / debt) that prove nothing, so all_passed()
    // is honestly false. The full-DB parity invariant: ZERO disproved in both
    // runs, no unknown but the audited evaluation-Unknown rows, identical
    // genuine + degenerate accounting across seq/parallel.
    assert_eq!(
        sequential.failed(),
        0,
        "Sequential full-DB had failures:\n{}",
        sequential
    );
    assert_eq!(
        parallel.failed(),
        0,
        "Parallel full-DB had failures:\n{}",
        parallel
    );
    assert_eq!(
        assert_unknowns_are_exactly_the_expected(&sequential),
        expected_unknowns().len(),
        "Sequential full-DB: every audited evaluation-Unknown row must be registered and Unknown"
    );
    assert_eq!(
        assert_unknowns_are_exactly_the_expected(&parallel),
        expected_unknowns().len(),
        "Parallel full-DB: every audited evaluation-Unknown row must be registered and Unknown"
    );
    assert_eq!(
        sequential.genuinely_passed(),
        parallel.genuinely_passed(),
        "seq/parallel disagree on genuinely_passed: {} vs {}",
        sequential.genuinely_passed(),
        parallel.genuinely_passed()
    );
    assert_eq!(
        sequential.degenerate_debt_count(),
        parallel.degenerate_debt_count(),
        "seq/parallel disagree on degenerate_debt_count: {} vs {}",
        sequential.degenerate_debt_count(),
        parallel.degenerate_debt_count()
    );
}

// ===========================================================================
// Specific category count assertions (regression guards)
// ===========================================================================

#[test]
fn full_proof_suite_known_category_counts() {
    let db = ProofDatabase::new();

    // These are regression guards based on known proof registrations.
    // If a count changes, update the expected value after verifying
    // the change is intentional.

    // Arithmetic: 4 ops (add/sub/mul/neg) x 4 widths (I8/I16/I32/I64) = 16
    let arith = db.count_by_category(ProofCategory::Arithmetic);
    assert!(arith >= 16, "Arithmetic: expected >= 16, got {}", arith);

    // Division: sdiv/udiv x I32/I64 plus urem/srem at I8/I16/I32/I64.
    // Keep this as a floor so future proof growth does not churn the
    // integration suite.
    let division = db.count_by_category(ProofCategory::Division);
    assert!(division >= 12, "Division: expected >= 12, got {}", division);

    // Bitwise/Shift: core bitwise/BIC/ORN proofs plus bitfield
    // ExtractBits/SextractBits/InsertBits at I8/I16/I32/I64. The 12 scalar shift
    // (Ishl/Ushr/Sshr) proofs were degenerate X==X and were RETRACTED in #62
    // (those opcodes are reconstruction-credited), so the floor drops to 34.
    let bitwise = db.count_by_category(ProofCategory::BitwiseShift);
    assert!(
        bitwise >= 34,
        "BitwiseShift: expected >= 34, got {}",
        bitwise
    );

    // FP: historic baseline 38 (fadd/fsub/fmul/fdiv/fneg x F32/F64 = 10, plus 14
    // fcmp conditions x 2 sizes = 28; total 38). Relaxed to floor so new FP
    // lowerings don't break this suite (#418). Matches the Arithmetic/Memory
    // pattern above.
    let fp = db.count_by_category(ProofCategory::FloatingPoint);
    assert!(fp >= 38, "FloatingPoint: expected >= 38, got {}", fp);

    // Comparison (exact, per family): 502 = 20 + 40 + 414 + 28. Each family is
    // pinned on its own and together they must account for every row, so one
    // family's growth cannot mask another's loss inside a single total.
    // * 20 `Icmp_<cc>_I{32,64} -> CMP+CSET_<cc>`: 10 conditions x 2 widths. The
    //   UGE/HS pair #62 retracted as degenerate is genuine again now that nzcv.rs
    //   derives the C flag from the adder carry-out instead of spelling it `bvuge`.
    // * 40 `Select_* -> CMP+CSEL_*` (aarch64_select_proofs): 10 conditions x
    //   cmp{32,64} x sel{32,64}; the comparison and select widths are independent.
    // * 414 per-instruction NZCV producer/consumer obligations of
    //   aarch64_flag_consumer_proofs (e152b164d, pinned in cea76ae56):
    //   - 2 FCMP packed NZCV (f32, f64);
    //   - 28 FCMP -> CSET (14 conditions x f32/f64);
    //   - 384 CSEL/CSINC/CSNEG x W/X destination x reaching producer: CMP
    //     w32/w64 (10 conditions each), TST w32/w64 (8), FCMP f32/f64 (14),
    //     i.e. 3 x 2 x 64.
    // * 28 `A64 decoded CSET` (aarch64_value_decode_proofs): 14 condition codes x
    //   2 destination widths; AL/NV are absent because the alias cannot carry them.
    let comparison_rows = db.by_category(ProofCategory::Comparison);
    let comparison_family = |prefix: &str| {
        comparison_rows
            .iter()
            .filter(|p| p.obligation.name.starts_with(prefix))
            .count()
    };
    let icmp = comparison_family("Icmp_");
    assert_eq!(
        icmp, 20,
        "Comparison: expected exactly 20 Icmp CMP+CSET, got {icmp}"
    );
    let select = comparison_family("Select_");
    assert_eq!(
        select, 40,
        "Comparison: expected exactly 40 Select CMP+CSEL, got {select}"
    );
    let nzcv = comparison_family("A64 NZCV ");
    assert_eq!(
        nzcv, 414,
        "Comparison: expected exactly 414 NZCV flag-consumer, got {nzcv}"
    );
    let decoded_cset = comparison_family("A64 decoded CSET ");
    assert_eq!(
        decoded_cset, 28,
        "Comparison: expected exactly 28 decoded-word CSET, got {decoded_cset}"
    );
    let comparison = comparison_rows.len();
    assert_eq!(
        comparison,
        icmp + select + nzcv + decoded_cset,
        "Comparison: an unclassified proof entered the category ({comparison} rows, \
         {icmp} Icmp + {select} Select + {nzcv} NZCV + {decoded_cset} decoded CSET)"
    );
    assert_eq!(
        comparison, 502,
        "Comparison: expected exactly 502 (20 Icmp + 40 Select + 414 NZCV + 28 decoded CSET), \
         got {comparison}"
    );

    // Branch: 10 conditions x 2 widths = 20 (same UGE/B.HS return as above).
    assert_eq!(db.count_by_category(ProofCategory::Branch), 20);

    // Peephole: historic baseline 18 (9 rules x 2 widths). Relaxed to floor so
    // new peephole patterns don't break this suite (#418). Matches the
    // Arithmetic/Memory/FloatingPoint pattern above.
    let peephole = db.count_by_category(ProofCategory::Peephole);
    assert!(peephole >= 18, "Peephole: expected >= 18, got {}", peephole);

    // NEON Lowering: historic baseline 22 (11 ops x 2 arrangements). Relaxed to
    // floor so new NEON lowerings don't break this suite (#418). Matches the
    // Arithmetic/Memory/FloatingPoint/Peephole pattern.
    let neon = db.count_by_category(ProofCategory::NeonLowering);
    assert!(neon >= 22, "NeonLowering: expected >= 22, got {}", neon);

    // Memory: floor 52. The static degenerate X==X Load_I*/Store_I* [Xn,#imm]
    // self-equalities, WriteCombine_I32, and Aligned_ScaledOffset_I32 (14 total)
    // were RETRACTED in #62. The I32/I64 roundtrips are counted once in their
    // dedicated LoadStoreLowering category; the remaining GENUINE roundtrip +
    // QF_ABV array theory + non-interference/endianness/forwarding/subword/LDP
    // proofs carry the real load/store coverage.
    assert!(
        db.count_by_category(ProofCategory::Memory) >= 52,
        "expected >= 52 memory proofs, got {}",
        db.count_by_category(ProofCategory::Memory)
    );

    // Vectorization: historic baseline 31. Relaxed to floor so new vectorization
    // proofs don't break this suite (#418). Matches surrounding pattern.
    let vect = db.count_by_category(ProofCategory::Vectorization);
    assert!(vect >= 31, "Vectorization: expected >= 31, got {}", vect);

    // RegAlloc: 43 proofs (16 Phase 1 + 15 Phase 2 + 12 Phase 3/greedy)
    assert!(
        db.count_by_category(ProofCategory::RegAlloc) >= 16,
        "expected >= 16 regalloc proofs, got {}",
        db.count_by_category(ProofCategory::RegAlloc)
    );
}

// ===========================================================================
// Verification strength distribution
// ===========================================================================

#[test]
fn full_proof_suite_has_exhaustive_and_statistical() {
    let db = ProofDatabase::new();

    // full_proof_suite_all_pass asserts this distribution on the actual
    // verification report. This metadata check keeps the filtered test bounded.
    let exhaustive = db
        .all()
        .iter()
        .filter(|proof| {
            matches!(
                VerificationStrength::for_obligation(&proof.obligation),
                VerificationStrength::Exhaustive
            )
        })
        .count();
    let statistical = db
        .all()
        .iter()
        .filter(|proof| {
            matches!(
                VerificationStrength::for_obligation(&proof.obligation),
                VerificationStrength::Statistical { .. }
            )
        })
        .count();

    assert!(
        exhaustive > 0,
        "Expected some exhaustive proofs (8-bit), got 0"
    );
    assert!(
        statistical > 0,
        "Expected some statistical proofs (32/64-bit), got 0"
    );

    // Print distribution for documentation.
    println!();
    println!("Verification strength distribution:");
    println!(
        "  Exhaustive:  {} proofs (small-width, complete)",
        exhaustive
    );
    println!(
        "  Statistical: {} proofs (large-width, 100K+ samples)",
        statistical
    );
    println!("  Total:       {} proofs", db.len());
}

// ===========================================================================
// RegAlloc-specific verification (new in Wave 15+)
// ===========================================================================

#[test]
fn full_proof_suite_regalloc_proofs_comprehensive() {
    let db = ProofDatabase::new();
    let runner = VerificationRunner::new(&db);

    let results = runner.run_category(ProofCategory::RegAlloc);
    assert!(
        results.len() >= 16,
        "Expected >= 16 regalloc proofs, got {}",
        results.len()
    );

    // Verify all pass, the three Greedy RA proofs whose paired equalities or
    // paired 8-alignment only the multi-input sweep's precondition-directed
    // trials reach included (NEW-CG-SAMPLER; they were the vacuous-sample
    // Unknown under TRUSTCG-02).
    for (name, result) in &results {
        assert!(
            matches!(result, trust_cg_verify::VerificationResult::Valid),
            "RegAlloc proof '{}' failed: {:?}",
            name,
            result
        );
    }
    let names: Vec<&str> = results.iter().map(|(n, _)| n.as_str()).collect();
    for relational in [
        proof_greedy_no_interference().name,
        proof_greedy_fixed_register_respect().name,
        proof_greedy_stack_offset_correctness().name,
    ] {
        assert!(
            names.contains(&relational.as_str()),
            "Greedy RA proof '{relational}' must be in the RegAlloc category"
        );
    }

    // Check that specific proof names exist.
    assert!(
        names.iter().any(|n| n.contains("non-interference")),
        "Missing non-interference proof"
    );
    assert!(
        names.iter().any(|n| n.contains("completeness")),
        "Missing completeness proof"
    );
    assert!(
        names.iter().any(|n| n.contains("spill")),
        "Missing spill proof"
    );
    // #62: the degenerate "phi elimination preserves predecessor value" X==X
    // proofs were RETRACTED; the genuine spill/reload roundtrip + coalescing
    // proofs carry the SSA-destruction correctness. Pin a genuine survivor.
    assert!(
        names.iter().any(|n| n.contains("roundtrip")),
        "Missing spill/reload roundtrip proof"
    );
    assert!(
        names.iter().any(|n| n.contains("callee-saved")),
        "Missing callee-saved proof"
    );
    assert!(
        names.iter().any(|n| n.contains("do not alias")),
        "Missing spill slot non-aliasing proof"
    );
}

// ===========================================================================
// Auto-mode verification (ay enabled by default)
// ===========================================================================

#[test]
fn full_proof_suite_auto_mode_selects_backend() {
    // select_auto_mode() should return MockThenAY when a solver binary is
    // available, or MockOnly otherwise. Either way it must not panic.
    let mode = select_auto_mode();
    let label = match &mode {
        AYVerificationMode::MockOnly => "MockOnly (no solver binary found)",
        AYVerificationMode::MockThenAY(_) => "MockThenAY (solver binary found)",
        AYVerificationMode::AYCli(_) => "AYCli",
        AYVerificationMode::Auto => "Auto",
    };
    println!("select_auto_mode() -> {}", label);
}

#[test]
fn full_proof_suite_run_auto_passes_subset() {
    // Exercise run_auto() on a small proof subset to verify the auto-selection
    // pipeline works end-to-end. Uses a subset to avoid long runtimes.
    let full_db = ProofDatabase::new();
    let subset: Vec<_> = full_db
        .by_category(ProofCategory::Arithmetic)
        .into_iter()
        .take(5)
        .cloned()
        .collect();

    let db = ProofDatabase::from_proofs(subset);
    let runner = VerificationRunner::new(&db);
    let report = runner.run_auto();

    assert_eq!(
        report.total(),
        db.len(),
        "run_auto report total ({}) != db size ({})",
        report.total(),
        db.len()
    );
    // STRICT (task #61): the arithmetic subset may include degenerate X==X ALU
    // identities, so all_passed() (genuine-only) can be false. The honest
    // invariant: nothing disproved/unknown, and every non-degenerate obligation
    // passes.
    assert_eq!(
        report.failed(),
        0,
        "run_auto disproved a proof:\n{}",
        report
    );
    assert_eq!(
        report.unknown(),
        0,
        "run_auto left a proof unknown:\n{}",
        report
    );
    assert_eq!(
        report.genuinely_passed(),
        report.total() - report.degenerate_debt_count(),
        "run_auto: every non-degenerate arithmetic proof must pass:\n{}",
        report
    );

    println!(
        "run_auto: {}/{} GENUINELY proven, {} degenerate excluded (mode: auto-selected)",
        report.genuinely_passed(),
        report.total(),
        report.degenerate_debt_count(),
    );
}
