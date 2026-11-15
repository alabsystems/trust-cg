// trust-cg-codegen/tests/clean_fixture_host_lowering.rs - the x86-64 lowering
// floor for the frozen Clean-kernel fixtures.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHY THIS TARGET EXISTS. The `e2e_*` Clean consumers execute these modules
// through the in-process JIT, whose proof-carrying publication gate can refuse
// a module before any lowering defect would show. This target separates the two
// questions: it drives each committed `clean_*.tir` / `clean_*.trust.tir`
// fixture through `Compiler::compile` (lowering -> regalloc -> encoding ->
// object emission) for the host at O0 and O1, with no JIT and no proof
// publication. It executes nothing.
//
// WHY IT IS x86-64 ONLY. On AArch64 these same fixtures are already executed
// end to end by the `e2e_*` lanes, so an extra AOT sweep there measures
// nothing new; x86-64 had no Clean coverage at all, which is what this target
// supplies. The behaviour of this sweep on an AArch64 host is UNMEASURED —
// widening the gate needs a run on that host, not an assumption.
//
// WHAT IT ASSERTS. A floor, in the same shape as the repository's other
// floors, strict in BOTH directions:
//
//   * every fixture in `LOWERING_FLOOR` must still lower, at both opt levels
//     (a regression is red);
//   * every fixture NOT in `LOWERING_FLOOR` must still be refused (closing a
//     gap is red, and the fix is to move the name into the floor);
//   * every refusal must match one of the `REFUSAL_CLASSES` signatures below.
//     A refusal that matches none of them is a NEW kind of refusal and is red.
//
// Nothing here excuses a fixture: the refusal classes are recorded WITH their
// exact diagnostic substring, and the census is printed on every run. This is
// a record of a measured gap, not a pass.
//
// WHY THE FLOOR PINS OUTCOMES AND NOT CLASSES. Which refusal a fixture
// surfaces is NOT stable across runs of the same binary. Measured 2026-09-27
// over three runs BEFORE this host was qualified for the portable certificate
// tier: `clean_binding_defeq.blind.trust.tir` at O0 refused with the
// guard-carrier canary on one and with the formal-arg prefix gap on another,
// `clean_phase_completion.gate.trust.tir` at O0 refused in 0.6s on one run and
// reached no decision in 120s on the next, the per-class counts moved every
// time (O0: 17/15/2, 19/14/1 canary/prefix/deadline) and the whole target took
// 986s, 606s and 433s. Several fixtures carry BOTH shapes, and which refusal is
// reached first varies. What IS stable WITHIN a build is exactly which fixtures
// lower — it moved when each of the two gaps below closed, and only then — so the
// floor pins that, and pins only that every refusal belongs to a recorded class. A per-fixture class
// table would be flaky, and tightening it to one would be pinning noise. Both
// surviving outcomes are fail-closed refusals, so nothing unsound rides on the
// drift; it is recorded here because it is also why this target is not a row in
// scripts/check_linux_x86_64.py.
//
// WHAT CLOSED ON 2026-09-27, AND WHY THE FLOOR MOVED 4 -> 15. The largest
// refusal class here was never an x86-64 codegen fact. The x86-64
// guard-carrier expansion canary proves, before it emits them, that the
// condition code each Sentinel-S5 guard expands to traps on exactly the
// carrier's intended set; its `DivZero` i32/i64 rows are wider than the
// exhaustive lane and are meant to discharge through the committed portable
// certificates (`guard_div_zero_{32,64}.lratcert`). This host has no AY at all
// (stock 1.97.1's sysroot ships none) AND its bundled `drat-trim` identity was
// not in `verdict_db/canary_certs/manifest.v1`, so the certificate could not be
// consumed, the query fell to the live lane, and the canary correctly REFUSED to
// confirm the expansion — 19 fixtures at O0 and 19 at O1 in the run archived as
// `clean-fixture-census-before.log`, which lowered 4 of 38 at both levels.
// Qualifying this host's checker
// (`docs/portable-checker-host-qualification.md`, 2026-09-27) closed that class
// to ZERO at both opt levels, and the floor was raised in the same change.
// The canary itself was not changed, widened or bypassed: the same obligation is
// now DISCHARGED by an independently replayed certificate instead of being
// unknowable, and a wrong condition code still misses every certificate and
// still fails closed.
//
// WHAT ELSE CLOSED THE SAME DAY: THE FORMAL-ARG PREFIX GAP, AND WHY THE FLOOR
// MOVED 15 -> 31. `fixup_formal_arg_parallel_copy` refused, on its segment-wise
// path, any formal-argument prologue that mixed intake-interleaved split
// connectors with stack-argument loads: "stack-arg loads cannot be ordered
// against barriers without per-instruction dependence analysis — fail closed on
// the combination rather than guess". After the host qualification above that was
// the LARGEST remaining class, 21-22 fixtures at O0 and 20 at O1.
// `crates/trust-cg-codegen/src/x86_64/pipeline.rs` now carries the analysis
// (`prove_formal_arg_prefix_admits_loads`). Each load is emitted at its OWN
// position among the segments and connectors — after the resolved copies of the
// segment it was scanned inside, before that segment's closing connector — so
// relative to every connector, every other segment and every other load the
// emitted order is IDENTICAL to the one ISel emitted. A prefix is admitted either
// because the pass reorders nothing at all (and the prologue it received already
// satisfies the pass's contract that every intake delivers its argument
// register's function-entry contents) or because running both orders over a
// syntactic value domain shows they compute the same thing. Nothing was widened:
// shapes the analysis cannot clear are still refused, by name, and none of those
// refusals is reached by this corpus — so none is recorded below, and one
// appearing would correctly read as a NEW class. A SINGLE function,
// `ExprMeta__pack`, carried the whole gap in every fixture that hit it: it is the
// shape SysV produces and AAPCS64 does not, because six integer argument
// registers against AAPCS64's eight push these many-argument kernel entries onto
// the stack here and not on AArch64.
//
// THE REMAINING GAP, measured 2026-09-27 on x86_64-unknown-linux-gnu with stock
// rustc 1.97.1 after both closures (1844s for the whole target): 31 of 38
// fixtures lower at O0 and at O1, and the lowered set is identical across the
// two opt levels. The remaining seven reached no decision inside
// `FIXTURE_DEADLINE` — `clean_eta_ext.trust.tir`, `clean_expand_eta.trust.tir`,
// `clean_lazy_delta.{blind,gate,probe}.trust.tir`,
// `clean_phase_completion.gate.trust.tir` and `clean_tc_stitch.trust.tir` — and
// that was then the ONLY class.
//
// WHAT CLOSED ON 2026-09-28, AND WHY THE FLOOR MOVED 31 -> 38. The deadline class
// was one allocator defect, not seven fixtures’ worth of missing support. Each of
// the seven spent 95-99.9% of its compile inside a SINGLE function’s register
// allocation: `GreedyAllocator::apply_split` re-enqueued BOTH halves of a split at
// `Stage::New`, so a piece produced by splitting was itself eligible for unbounded
// splitting, and a high-pressure range was split until its fragments were too
// short to split again. Every realized split also appends a `PSEUDO_COPY` to the
// instruction list that later attempts re-scan, so the cost was quadratic in the
// split count — `build_env` in `clean_lazy_delta.gate.trust.tir` performed 159 813
// splits, grew its instruction list from ~1.8k to 161 653, and SPILLED 157 852 of
// the 160 589 resulting pieces.
//
// `split_depth_cap` now bounds that the way LLVM’s greedy allocator does (a split
// product advances to `RS_Split2`/`RS_Spill` instead of returning to the unbounded
// stage). All 38 fixtures lower at O0 and at O1, the whole target takes 60s rather
// than 1844s, and the slowest single decision is 2.6s. Two things about that are
// worth recording. The bound is a QUALITY decision, not a correctness one — every
// allocation it produces still goes through the always-on regalloc translation
// validator and the x86 TV-4/TV-5 recheck — and on this corpus it makes the code
// SMALLER, by ~10x (gate at O1: 2 791 592 -> 356 904 object bytes), because the
// cascade’s copies were themselves being spilled: a spilled split copy is a store
// plus a reload, strictly worse than spilling its parent.
//
// Bounding it also needed one fail-closed gap closed first, because at a cascade
// depth near 4 every fixture refused on it: `prove_formal_arg_prefix_admits_loads`
// had no model of a split connector whose end the allocator SPILLED. It now models
// that end by the spill SLOT its replay touches
// (`formal_barrier_ends_for_value_proof`), which is sound because
// `materialize_x86_spills` emits each instruction’s replay as one contiguous group
// whose scratch registers are non-allocatable and dead outside it. Two shapes that
// argument does not cover — a partial-write connector into a spilled destination,
// and a connector between one slot and itself — are still refused, by name, and
// neither is reached by this corpus.
//
// A QUALIFIED HOST IS NOW A PRECONDITION OF THIS FLOOR, not a recorded class.
// Eleven of the floor's fixtures lower only because the guard-carrier
// canary can confirm its expansion here, which needs
// `host-checker: x86_64-unknown-linux-gnu
// 6bd14b38eac39bff41450ebac9e3c9436009ec478ffca537c47dae214bdb83ca` in the
// certificate manifest — the exact bytes GCC builds from the vendored
// `drat-trim` source. A host whose checker bytes differ (another compiler, or
// the `cc` wrapper some PATHs put ahead of `/usr/bin`) is an authorization miss
// that fails closed, and the `No AY solver admitted ... checker-identity miss`
// refusal deliberately matches NO class below any more: it must come back as an
// unrecorded refusal AND as a floor regression, rather than being filed as a
// known gap on a host where this sweep measures nothing.
//
// THE JIT HALF, AND WHY IT IS NOT SHIPPED AS 16 RED TARGETS. The other half of
// the question — whether these fixtures EXECUTE on x86-64 — was measured the
// same day by widening the `e2e_*` Clean consumers' `target_arch` gate
// locally, BEFORE the certificate host qualification above. Result: 9 more
// tests passed and 91 more failed, and every one of those 91 was one of the
// two classes this target then had (the verifying JIT's proof-promotion
// refusal, or the unqualified-host canary). No third class, no wrong answer,
// no miscompile. How many of the 91 the qualification moves was NOT
// re-measured. Since that says nothing this target does not
// already say, the eight consumers that upstream gates to AArch64
// (`e2e_binding_defeq`, `e2e_ctx_whnf_defeq`, `e2e_eta_struct_ext`,
// `e2e_frontend_roundtrip`, `e2e_fvar_opening`, `e2e_tc_stitching`,
// `e2e_universe_integration`, `e2e_universe_realnames`) were left gated rather
// than shipped red. The other eight Clean consumers were never arch-gated and
// do run here: they take the host JIT target and the host fixture loader, at
// the same pass/fail counts as upstream, so their diagnostic is now the real
// refusal instead of the `JitTargetMismatch` that used to mask it.
//
// The fixtures carry the `target` header they were emitted with;
// `kernel_fixture::parse_host_module` rewrites that one line to the host
// triple (the evidence, and what the rewrite does and does not establish, is
// in that module). Externs stay unbound: object emission records them as
// relocations.

#![cfg(target_arch = "x86_64")]

#[path = "common/kernel_fixture.rs"]
mod kernel_fixture;

use std::collections::BTreeMap;
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

/// Per-fixture deadline. Re-measured on this host (2026-09-28,
/// `x86_64-unknown-linux-gnu`, debug build) after the split-cascade bound: every
/// one of the 38 fixtures now reaches a decision, and the slowest is
/// `clean_phase_completion.gate.trust.tir` at 1.4s (O0) / 2.6s (O1) — so this is
/// ~46x headroom over the worst measured decision, where before the bound it was
/// ~5x over 24.7s and seven fixtures blew through it entirely. It is kept, not
/// tightened: it exists so that a future regression of that class comes back as a
/// red run instead of an unbounded wait, and tightening it to the current worst
/// case would make the sweep a timing test on a shared machine.
const FIXTURE_DEADLINE: Duration = Duration::from_secs(120);

/// The x86-64 lowering floor: fixtures that lower, allocate and encode for
/// this host at O0 AND O1. Measured 2026-09-27. Adding a name here requires a
/// measurement; removing one is a regression.
///
/// The eleven `clean_inductive_*` / `clean_nat_reduce_*` / `clean_quot_*` /
/// `clean_ri_*` names were added by the 2026-09-27 portable-checker host
/// qualification, which let the guard-carrier canary CONFIRM the expansion
/// these fixtures' division guards need instead of refusing it; the same
/// eleven, at both opt levels, in one measured run.
///
/// The rest were added the same day by closing the formal-arg prefix gap below.
/// Both raises are still one list, because the lowered set is still the SAME at
/// both opt levels — that is measured, not assumed, and a future change that
/// moves only one level has to split this list rather than pick a side.
///
/// THE LAST SEVEN, added 2026-09-28 by bounding the greedy allocator’s split
/// cascade (`trust-cg-regalloc/src/greedy.rs`, `split_depth_cap`). They were the
/// whole of the deadline class: each spent 95-99.9% of its compile inside ONE
/// function’s register allocation, splitting a live range until its fragments
/// were too short to split again. With a split PRODUCT no longer eligible for
/// unbounded re-splitting they lower in 0.4-2.6s, and this list is now every
/// fixture in the corpus at both opt levels — measured on this host at 38 of 38,
/// O0 and O1, in one 60s run.
const LOWERING_FLOOR: &[&str] = &[
    "clean_binding_defeq.blind.trust.tir",
    "clean_binding_defeq.gate.trust.tir",
    "clean_binding_defeq.probe.trust.tir",
    "clean_ctx_whnf.blind.trust.tir",
    "clean_ctx_whnf.gate.trust.tir",
    "clean_ctx_whnf.probe.trust.tir",
    "clean_decl_check.trust.tir",
    "clean_decl_universe.trust.tir",
    "clean_defeq_cache.tir",
    "clean_defeq_cache.trust.tir",
    "clean_eta_ext.trust.tir",
    "clean_expand_eta.trust.tir",
    "clean_expr_infer.trust.tir",
    "clean_expr_infer_ext.trust.tir",
    "clean_fvar_opening_gate.trust.tir",
    "clean_fvar_opening_probe.trust.tir",
    "clean_inductive_ctor_return.tir",
    "clean_inductive_elim.tir",
    "clean_inductive_positivity.tir",
    "clean_lazy_delta.blind.trust.tir",
    "clean_lazy_delta.gate.trust.tir",
    "clean_lazy_delta.probe.trust.tir",
    "clean_nat_reduce_arith.tir",
    "clean_nat_reduce_defeq.tir",
    "clean_nat_reduce_mulpow.tir",
    "clean_phase_completion.gate.trust.tir",
    "clean_phase_completion.probe.trust.tir",
    "clean_proof_irrel.trust.tir",
    "clean_quot_axiom.tir",
    "clean_quot_iota.tir",
    "clean_quot_names.tir",
    "clean_ri_names.tir",
    "clean_ri_reduce.tir",
    "clean_sprop_defeq.tir",
    "clean_sprop_infer_sort.tir",
    "clean_tc_stitch.trust.tir",
    "clean_universe_realnames_main.trust.tir",
    "clean_universe_realnames_probe.trust.tir",
];

/// The refusal classes this host produces, as (name, exact diagnostic
/// substring). A refusal matching none of these is a new kind of refusal and
/// fails the sweep; see the module header for what each class means.
///
/// UNEXERCISED on this host since 2026-09-28: the floor is now the whole corpus,
/// so a clean run produces no refusal at all and reaches none of these. The
/// deadline is kept because it is still the mechanism that bounds the sweep on a
/// slower host, and keeping it recorded means a deadline hit reads as the known
/// mechanism rather than as an unrecorded class. A refusal of ANY other shape
/// now fails twice over — once here and once as a floor regression.
const REFUSAL_CLASSES: &[(&str, &str)] = &[(
    "no decision inside the per-fixture deadline",
    "did not finish within",
)];

const FIXTURES: &[(&str, &str)] = &[
    (
        "clean_binding_defeq.blind.trust.tir",
        include_str!("clean_binding_defeq.blind.trust.tir"),
    ),
    (
        "clean_binding_defeq.gate.trust.tir",
        include_str!("clean_binding_defeq.gate.trust.tir"),
    ),
    (
        "clean_binding_defeq.probe.trust.tir",
        include_str!("clean_binding_defeq.probe.trust.tir"),
    ),
    (
        "clean_ctx_whnf.blind.trust.tir",
        include_str!("clean_ctx_whnf.blind.trust.tir"),
    ),
    (
        "clean_ctx_whnf.gate.trust.tir",
        include_str!("clean_ctx_whnf.gate.trust.tir"),
    ),
    (
        "clean_ctx_whnf.probe.trust.tir",
        include_str!("clean_ctx_whnf.probe.trust.tir"),
    ),
    (
        "clean_decl_check.trust.tir",
        include_str!("clean_decl_check.trust.tir"),
    ),
    (
        "clean_decl_universe.trust.tir",
        include_str!("clean_decl_universe.trust.tir"),
    ),
    (
        "clean_defeq_cache.tir",
        include_str!("clean_defeq_cache.tir"),
    ),
    (
        "clean_defeq_cache.trust.tir",
        include_str!("clean_defeq_cache.trust.tir"),
    ),
    (
        "clean_eta_ext.trust.tir",
        include_str!("clean_eta_ext.trust.tir"),
    ),
    (
        "clean_expand_eta.trust.tir",
        include_str!("clean_expand_eta.trust.tir"),
    ),
    (
        "clean_expr_infer.trust.tir",
        include_str!("clean_expr_infer.trust.tir"),
    ),
    (
        "clean_expr_infer_ext.trust.tir",
        include_str!("clean_expr_infer_ext.trust.tir"),
    ),
    (
        "clean_fvar_opening_gate.trust.tir",
        include_str!("clean_fvar_opening_gate.trust.tir"),
    ),
    (
        "clean_fvar_opening_probe.trust.tir",
        include_str!("clean_fvar_opening_probe.trust.tir"),
    ),
    (
        "clean_inductive_ctor_return.tir",
        include_str!("clean_inductive_ctor_return.tir"),
    ),
    (
        "clean_inductive_elim.tir",
        include_str!("clean_inductive_elim.tir"),
    ),
    (
        "clean_inductive_positivity.tir",
        include_str!("clean_inductive_positivity.tir"),
    ),
    (
        "clean_lazy_delta.blind.trust.tir",
        include_str!("clean_lazy_delta.blind.trust.tir"),
    ),
    (
        "clean_lazy_delta.gate.trust.tir",
        include_str!("clean_lazy_delta.gate.trust.tir"),
    ),
    (
        "clean_lazy_delta.probe.trust.tir",
        include_str!("clean_lazy_delta.probe.trust.tir"),
    ),
    (
        "clean_nat_reduce_arith.tir",
        include_str!("clean_nat_reduce_arith.tir"),
    ),
    (
        "clean_nat_reduce_defeq.tir",
        include_str!("clean_nat_reduce_defeq.tir"),
    ),
    (
        "clean_nat_reduce_mulpow.tir",
        include_str!("clean_nat_reduce_mulpow.tir"),
    ),
    (
        "clean_phase_completion.gate.trust.tir",
        include_str!("clean_phase_completion.gate.trust.tir"),
    ),
    (
        "clean_phase_completion.probe.trust.tir",
        include_str!("clean_phase_completion.probe.trust.tir"),
    ),
    (
        "clean_proof_irrel.trust.tir",
        include_str!("clean_proof_irrel.trust.tir"),
    ),
    ("clean_quot_axiom.tir", include_str!("clean_quot_axiom.tir")),
    ("clean_quot_iota.tir", include_str!("clean_quot_iota.tir")),
    ("clean_quot_names.tir", include_str!("clean_quot_names.tir")),
    ("clean_ri_names.tir", include_str!("clean_ri_names.tir")),
    ("clean_ri_reduce.tir", include_str!("clean_ri_reduce.tir")),
    (
        "clean_sprop_defeq.tir",
        include_str!("clean_sprop_defeq.tir"),
    ),
    (
        "clean_sprop_infer_sort.tir",
        include_str!("clean_sprop_infer_sort.tir"),
    ),
    (
        "clean_tc_stitch.trust.tir",
        include_str!("clean_tc_stitch.trust.tir"),
    ),
    (
        "clean_universe_realnames_main.trust.tir",
        include_str!("clean_universe_realnames_main.trust.tir"),
    ),
    (
        "clean_universe_realnames_probe.trust.tir",
        include_str!("clean_universe_realnames_probe.trust.tir"),
    ),
];

fn compile_for_host(name: &str, text: &str, opt_level: OptLevel) -> Result<(usize, usize), String> {
    let module = kernel_fixture::parse_host_module(text)
        .map_err(|err| format!("{name}: parse for host failed: {err:?}"))?;
    let result = Compiler::new(CompilerConfig {
        opt_level,
        target: kernel_fixture::host_jit_target(),
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .map_err(|err| format!("{name} at {opt_level:?}: {err:?}"))?;
    if result.metrics.function_count == 0 || result.object_code.is_empty() {
        return Err(format!(
            "{name} at {opt_level:?}: compiled to an empty object"
        ));
    }
    Ok((result.metrics.function_count, result.object_code.len()))
}

/// Compile one fixture on a worker thread and bound the wait.
///
/// A fixture that does not finish inside [`FIXTURE_DEADLINE`] is reported as a
/// refusal naming the deadline, exactly as a diagnostic would be. The worker
/// cannot be cancelled, so it keeps running until the process exits.
fn compile_for_host_bounded(
    name: &'static str,
    text: &'static str,
    opt_level: OptLevel,
) -> Result<(usize, usize), String> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(compile_for_host(name, text, opt_level));
    });
    match rx.recv_timeout(FIXTURE_DEADLINE) {
        Ok(outcome) => outcome,
        Err(RecvTimeoutError::Timeout) => Err(format!(
            "{name} at {opt_level:?}: did not finish within {FIXTURE_DEADLINE:?} \
             (the worker is not cancelled)"
        )),
        Err(RecvTimeoutError::Disconnected) => Err(format!(
            "{name} at {opt_level:?}: compile worker panicked without an outcome"
        )),
    }
}

/// Name of the recorded refusal class a diagnostic belongs to, or `None` when
/// it belongs to none of them.
fn refusal_class(diagnostic: &str) -> Option<&'static str> {
    REFUSAL_CLASSES
        .iter()
        .find(|(_, signature)| diagnostic.contains(signature))
        .map(|(class, _)| *class)
}

fn sweep(opt_level: OptLevel) {
    let mut lowered: Vec<&str> = Vec::new();
    let mut refused: Vec<(&str, String)> = Vec::new();
    for (name, text) in FIXTURES {
        let started = std::time::Instant::now();
        match compile_for_host_bounded(name, text, opt_level) {
            Ok((functions, bytes)) => {
                println!(
                    "{name} {opt_level:?}: {functions} functions, {bytes} object bytes, {:.1}s",
                    started.elapsed().as_secs_f64()
                );
                lowered.push(name);
            }
            Err(diagnostic) => {
                // Name every diagnostic here as well as in the assertions: a
                // reader of a run needs to see WHICH shape each refusal is
                // about, not only the ones that break the floor.
                println!(
                    "{name} {opt_level:?}: REFUSED after {:.1}s [{}]: {diagnostic}",
                    started.elapsed().as_secs_f64(),
                    refusal_class(&diagnostic).unwrap_or("UNRECORDED CLASS"),
                );
                refused.push((name, diagnostic));
            }
        }
    }

    let mut census: BTreeMap<&str, usize> = BTreeMap::new();
    for (_, diagnostic) in &refused {
        *census
            .entry(refusal_class(diagnostic).unwrap_or("UNRECORDED CLASS"))
            .or_default() += 1;
    }
    println!(
        "{opt_level:?} census for {}: {} of {} lowered; refusals by class: {census:?}",
        kernel_fixture::host_target_triple(),
        lowered.len(),
        FIXTURES.len(),
    );

    // 1. Every refusal belongs to a recorded class. An unrecorded refusal is a
    //    new kind of refusal, which this floor exists to catch.
    let unrecorded: Vec<String> = refused
        .iter()
        .filter(|(_, diagnostic)| refusal_class(diagnostic).is_none())
        .map(|(name, diagnostic)| format!("{name}: {diagnostic}"))
        .collect();
    assert!(
        unrecorded.is_empty(),
        "{} refusal(s) at {opt_level:?} match none of the recorded classes in \
         REFUSAL_CLASSES — a new kind of refusal, not a known gap:\n{}",
        unrecorded.len(),
        unrecorded.join("\n")
    );

    // 2. Every fixture on the floor still lowers.
    let regressed: Vec<String> = refused
        .iter()
        .filter(|(name, _)| LOWERING_FLOOR.contains(name))
        .map(|(name, diagnostic)| format!("{name}: {diagnostic}"))
        .collect();
    assert!(
        regressed.is_empty(),
        "{} fixture(s) in LOWERING_FLOOR stopped lowering for {} at {opt_level:?}:\n{}",
        regressed.len(),
        kernel_fixture::host_target_triple(),
        regressed.join("\n")
    );

    // 3. No fixture lowers that the floor does not record. Closing a gap is
    //    red on purpose: the floor must be raised in the same change.
    let unrecorded_pass: Vec<&str> = lowered
        .iter()
        .copied()
        .filter(|name| !LOWERING_FLOOR.contains(name))
        .collect();
    assert!(
        unrecorded_pass.is_empty(),
        "{} fixture(s) now lower for {} at {opt_level:?} but are not in \
         LOWERING_FLOOR — raise the floor in the same change: {unrecorded_pass:?}",
        unrecorded_pass.len(),
        kernel_fixture::host_target_triple(),
    );
}

#[test]
fn clean_fixture_host_lowering_floor_at_o0() {
    sweep(OptLevel::O0);
}

#[test]
fn clean_fixture_host_lowering_floor_at_o1() {
    sweep(OptLevel::O1);
}

/// The loader's contract, over the whole corpus and without compiling
/// anything: retargeting a fixture for the host rewrites the module header's
/// `target` line and NOTHING else, and the module the consumers then parse
/// declares this host's machine.
///
/// This is the assertion that justifies calling the rewrite a loading step.
/// It is byte-exact in both directions: every line except the header must be
/// identical, and the header must be exactly the host's.
#[test]
fn host_loading_rewrites_only_the_target_header_line() {
    let host = kernel_fixture::host_target_triple();
    let expected_header = format!("target \"{host}\" 8 little");
    for (name, text) in FIXTURES {
        let loaded = kernel_fixture::host_kernel_fixture(text);
        let before: Vec<&str> = text.lines().collect();
        let after: Vec<&str> = loaded.lines().collect();
        assert_eq!(
            before.len(),
            after.len(),
            "{name}: host loading changed the line count"
        );
        let rewritten: Vec<(usize, &str, &str)> = before
            .iter()
            .zip(after.iter())
            .enumerate()
            .filter(|(_, (b, a))| b != a)
            .map(|(index, (b, a))| (index, *b, *a))
            .collect();
        assert_eq!(
            rewritten.len(),
            1,
            "{name}: host loading rewrote {} line(s), expected exactly the \
             `target` header: {rewritten:?}",
            rewritten.len(),
        );
        let (index, original, replacement) = rewritten[0];
        assert!(
            original.starts_with("target \""),
            "{name}: line {index} is not a `target` header: {original}"
        );
        assert_eq!(
            replacement, expected_header,
            "{name}: line {index} was not retargeted to this host"
        );

        let module = kernel_fixture::parse_host_module(text)
            .unwrap_or_else(|err| panic!("{name}: parse for host failed: {err:?}"));
        let info = module
            .target_info
            .as_ref()
            .unwrap_or_else(|| panic!("{name}: retargeted module declares no target"));
        assert_eq!(info.triple, host, "{name}: parsed triple is not the host's");
        assert_eq!(info.pointer_size, 8, "{name}: parsed pointer size moved");
        assert_eq!(
            info.endianness,
            trust_ir::Endianness::Little,
            "{name}: parsed byte order moved"
        );
        assert!(
            info.abi.is_none(),
            "{name}: fixture pins an ABI ({:?}); the loader must not retarget it",
            info.abi
        );
    }
}

/// The listing above is complete: every `clean_*.tir` next to this file is
/// in `FIXTURES`, and every listed name exists.
#[test]
fn every_committed_clean_fixture_is_listed() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut on_disk: Vec<String> = std::fs::read_dir(&dir)
        .expect("read tests dir")
        .map(|entry| {
            entry
                .expect("dir entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|name| name.starts_with("clean_") && name.ends_with(".tir"))
        .collect();
    on_disk.sort();
    let mut listed: Vec<String> = FIXTURES
        .iter()
        .map(|(name, _)| (*name).to_owned())
        .collect();
    listed.sort();
    assert_eq!(
        on_disk, listed,
        "committed Clean fixtures and FIXTURES differ"
    );
}

/// Every name in `LOWERING_FLOOR` is a fixture this target actually sweeps.
#[test]
fn lowering_floor_names_are_swept_fixtures() {
    for name in LOWERING_FLOOR {
        assert!(
            FIXTURES.iter().any(|(fixture, _)| fixture == name),
            "LOWERING_FLOOR names `{name}`, which is not in FIXTURES"
        );
    }
}

/// This file's fixtures carry no codegen license (`body_gate: None`), which
/// trust-cg REFUSES by default (roadmap WS7.5, decision gate DG-73). Its
/// compiles state `Permit` explicitly, so no fixture lowers or is refused
/// because it was silently refused by the license.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
