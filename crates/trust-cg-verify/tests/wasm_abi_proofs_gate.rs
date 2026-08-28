// trust-cg-verify/tests/wasm_abi_proofs_gate.rs - the live gate for P4
// families (2) and (3)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
//! Runs `crate::wasm_abi_proofs` against the REAL wasm backend.
//!
//! `src/wasm_abi_proofs.rs` deliberately has no dependency on the backend: the
//! dependency direction is codegen -> verify, so it cannot have one, and its
//! corpus therefore carries FROZEN emitted bytes. This file is what keeps that
//! honest. It:
//!
//!  1. re-compiles every fixture's trust-ir text with the live backend and
//!     requires BYTE EQUALITY, so a backend change that moves an emission fails
//!     here instead of quietly leaving the family proving things about a module
//!     nobody emits any more;
//!  2. runs every anti-tautology guard against the FRESHLY COMPILED bytes, not
//!     only the frozen ones, so a guard cannot be disarmed by fixture drift;
//!  3. runs the whole family over LIVE modules that are NOT in the frozen
//!     corpus — a loop with a frame, a call inside a branch, a frameless island
//!     — so the evidence is not over-fitted to four fixtures;
//!  4. prints the REAL numbers: proven / refuted / inconclusive obligations,
//!     passing and failing structural checks, guard outcomes including the
//!     declared blind spot, and the named deferrals that stay RED.
//!
//! `trust-cg-codegen` and `trust-ir-build` are DEV-dependencies of this crate
//! for exactly this file's sake. They must never become normal dependencies:
//! trust-cg-codegen depends on trust-cg-verify, so the cycle is legal only
//! through `[dev-dependencies]`.

use trust_cg_codegen::wasm;
use trust_cg_verify::coverage_gate::{CoverageFinding, CoverageGate, GateArch};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_cg_verify::wasm_abi_proofs::{
    AbiGuard, GuardExpectation, WASM_ABI_DEFERRALS, WASM_ABI_FIXTURES, WASM_ABI_GUARDS,
    all_wasm_abi_guards, decode_module, discharge_by_evaluation, intended_module, run_guard,
    wasm_abi_evidence, wasm_abi_family_report,
};
use trust_ir::{ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;
use wasm::{WasmFuncImportPolicy, WasmModulePolicy, island_host_namespace};

fn cfg() -> VerificationConfig {
    VerificationConfig::default()
}

/// Re-create the compile policy a fixture's `policy` tag names.
fn policy_for(tag: &str) -> WasmModulePolicy {
    match tag {
        "closed" => WasmModulePolicy::closed(),
        "func-imports:trust:island/calls@1" => WasmModulePolicy {
            func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("calls")),
            ..WasmModulePolicy::closed()
        },
        "island:abi" => WasmModulePolicy::island("abi"),
        other => panic!("unknown fixture policy tag `{other}`"),
    }
}

fn finish_wasm32(mb: ModuleBuilder) -> trust_ir::Module {
    let mut module = mb.build();
    module.target_info = Some(wasm::target::wasm32_target_info());
    module
}

// ---------------------------------------------------------------------------
// 1. Fixture freshness
// ---------------------------------------------------------------------------

/// THE FRESHNESS GATE. Every frozen fixture must still be EXACTLY what the live
/// backend emits for its trust-ir text under its policy.
///
/// This is the load-bearing test of the whole family: without it, the frozen
/// bytes could drift away from the shipping backend and every obligation below
/// would be proving things about a module that no longer exists.
#[test]
fn frozen_fixtures_are_what_the_backend_emits_today() {
    for f in WASM_ABI_FIXTURES {
        let module = trust_ir::parser::parse_module(f.tir).unwrap_or_else(|e| {
            panic!("fixture `{}`: trust-ir text does not parse: {e:?}", f.name)
        });
        let fresh = wasm::compile_module_with_policy(&module, &policy_for(f.policy))
            .unwrap_or_else(|e| panic!("fixture `{}`: live compile failed: {e}", f.name));
        assert_eq!(
            fresh.len(),
            f.wasm.len(),
            "fixture `{}` DRIFTED: live compile is {} bytes, the frozen fixture is {}. Re-freeze \
             it (and re-check every guard needle) before trusting this family again.",
            f.name,
            fresh.len(),
            f.wasm.len()
        );
        assert_eq!(
            fresh, f.wasm,
            "fixture `{}` DRIFTED: the live backend emits different bytes",
            f.name
        );
    }
}

/// The frozen fixtures are also reachable from the live IR BUILDER, not only
/// from their own text: the builder shapes below must round-trip to exactly the
/// fixture text, so the corpus describes programs somebody can still construct.
#[test]
fn fixture_text_matches_a_live_builder_shape() {
    let mut mb = ModuleBuilder::new("abi_frame");
    let elem = mb.add_type(Ty::I32);
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("frame3", ft);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::I32);
    let y = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let a = fb.alloca(Ty::I32);
    let b = fb.alloca(Ty::I64);
    let c = fb.alloca(Ty::Array(elem, 3));
    fb.store(Ty::I32, a, x);
    fb.store(Ty::I64, b, x);
    fb.store(Ty::I32, c, y);
    let ra = fb.load(Ty::I32, a);
    let rc = fb.load(Ty::I32, c);
    let s = fb.add(Ty::I32, ra, rc);
    fb.ret(vec![s]);
    fb.build();
    let built = finish_wasm32(mb);
    let frozen = WASM_ABI_FIXTURES
        .iter()
        .find(|f| f.name == "abi_frame")
        .expect("abi_frame fixture");
    assert_eq!(
        format!("{built}"),
        frozen.tir,
        "the abi_frame fixture text no longer matches the builder shape it was frozen from"
    );
}

// ---------------------------------------------------------------------------
// 2. The family over the frozen corpus, with real numbers
// ---------------------------------------------------------------------------

/// The corpus report, printed with the REAL split. Nothing here is a bare
/// headline count: every refuted or inconclusive obligation is named, and every
/// failing structural check is named.
#[test]
fn corpus_report_is_clean_and_prints_real_numbers() {
    let report = wasm_abi_family_report();
    assert!(report.errors.is_empty(), "{:#?}", report.errors);

    let obligations = report.obligations();
    let counts = discharge_by_evaluation(&obligations, &cfg());
    let structural = report.structural();
    let failed: Vec<String> = structural
        .iter()
        .filter(|c| !c.ok)
        .map(|c| format!("{}: {}", c.name, c.detail))
        .collect();

    // How many obligations have STRUCTURALLY DISTINCT sides (so the evaluator
    // really samples them) versus how many reconstruct to the same tree on a
    // CORRECT emission (credited by provenance, exactly like the reconstructed
    // ALU obligations). Printed rather than hidden: the second group's
    // non-vacuity comes entirely from the guards below.
    let distinct = obligations
        .iter()
        .filter(|o| o.is_genuinely_proven())
        .count();

    eprintln!(
        "wasm_abi family over the frozen corpus ({} fixture(s)):\n  \
         SMT obligations: {} proven / {} refuted / {} inconclusive (of {})\n  \
         ... of which {} have structurally distinct sides (sampled) and {} reconstruct to the \
         same tree on a correct emission (credited by RECONSTRUCTION provenance)\n  \
         structural checks: {} passed / {} failed (of {})\n  \
         fail-closed refusals: {}\n  \
         named deferrals (stay RED): {}",
        report.per_fixture.len(),
        counts.proven,
        counts.refuted.len(),
        counts.inconclusive.len(),
        obligations.len(),
        distinct,
        obligations.len() - distinct,
        structural.len() - failed.len(),
        failed.len(),
        structural.len(),
        report.refusals().len(),
        WASM_ABI_DEFERRALS.len(),
    );
    for (name, ev) in &report.per_fixture {
        eprintln!(
            "    {name}: {} obligation(s), {} structural check(s)",
            ev.obligations.len(),
            ev.structural.len()
        );
    }

    assert!(
        counts.refuted.is_empty(),
        "refuted on the UNMUTATED corpus: {:#?}",
        counts.refuted
    );
    assert!(
        counts.inconclusive.is_empty(),
        "inconclusive on the UNMUTATED corpus: {:#?}",
        counts.inconclusive
    );
    assert!(failed.is_empty(), "failing structural checks: {failed:#?}");
    assert!(
        report.refusals().is_empty(),
        "fail-closed refusals: {:#?}",
        report.refusals()
    );
    assert_eq!(counts.proven, obligations.len());
}

// ---------------------------------------------------------------------------
// 3. Anti-tautology guards, against LIVE bytes
// ---------------------------------------------------------------------------

/// THE TEETH, run against the bytes the backend emits RIGHT NOW rather than the
/// frozen copy. Every `MustRefute` guard must be caught; the one `KnownBlind`
/// guard must NOT be, and is reported as such.
#[test]
fn guards_bite_the_live_backend_output() {
    let mut must_refute = 0usize;
    let mut known_blind = 0usize;
    for g in WASM_ABI_GUARDS {
        let f = WASM_ABI_FIXTURES
            .iter()
            .find(|f| f.name == g.fixture)
            .unwrap_or_else(|| panic!("guard `{}` names unknown fixture `{}`", g.name, g.fixture));
        let module = trust_ir::parser::parse_module(f.tir).expect("fixture parses");
        let live = wasm::compile_module_with_policy(&module, &policy_for(f.policy))
            .unwrap_or_else(|e| panic!("fixture `{}`: live compile failed: {e}", f.name));
        let outcome = run_guard(g, &live, &module, &cfg())
            .unwrap_or_else(|e| panic!("guard `{}` could not run on live bytes: {e}", g.name));
        match g.expectation {
            GuardExpectation::MustRefute => {
                assert!(
                    outcome.refuted,
                    "guard `{}` was NOT refuted — the family is vacuous for it. {}",
                    g.name, outcome.detail
                );
                must_refute += 1;
                eprintln!("  REFUTED   {}  [{}]", g.name, outcome.detail);
            }
            GuardExpectation::KnownBlind { deferral } => {
                assert!(
                    !outcome.refuted,
                    "guard `{}` WAS refuted although it is registered KnownBlind — retire the \
                     deferral `{deferral}` and promote the guard. {}",
                    g.name, outcome.detail
                );
                known_blind += 1;
                eprintln!("  BLIND     {}  (owned by deferral `{deferral}`)", g.name);
            }
        }
    }
    eprintln!(
        "wasm_abi guards on live backend output: {must_refute} refuted as required, \
         {known_blind} declared-blind and reported as NOT refuted"
    );
    assert_eq!(must_refute + known_blind, WASM_ABI_GUARDS.len());
    assert!(must_refute >= 13, "the guard corpus shrank");
    assert_eq!(known_blind, 1, "exactly one blind spot is declared");
}

/// The frozen-byte guard run agrees with the live one — a cheap cross-check
/// that the frozen corpus has not silently diverged in a way byte equality
/// somehow missed.
#[test]
fn guards_agree_between_frozen_and_live_bytes() {
    for outcome in all_wasm_abi_guards(&cfg()) {
        let outcome = outcome.unwrap_or_else(|e| panic!("guard could not run: {e}"));
        assert!(
            outcome.as_declared(),
            "guard `{}` did not behave as declared on frozen bytes: {}",
            outcome.name,
            outcome.detail
        );
    }
}

// ---------------------------------------------------------------------------
// 4. Generality: LIVE modules that are not in the frozen corpus
// ---------------------------------------------------------------------------

/// A framed function with a LOOP and two returns, compiled live. The family
/// must recognize its prologue, both allocas and its restore window, and every
/// obligation must discharge — evidence that the recognition is not over-fitted
/// to the four straight-line fixtures.
#[test]
fn a_live_loop_with_a_frame_is_covered() {
    let mut mb = ModuleBuilder::new("abi_live_loop");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("countdown", ft);
    let entry = fb.create_block();
    let head = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let n0 = fb.add_block_param(entry, Ty::I32);
    let acc_p = fb.add_block_param(head, Ty::I32);
    let n_p = fb.add_block_param(head, Ty::I32);

    fb.switch_to_block(entry);
    let cell = fb.alloca(Ty::I32);
    let scratch = fb.alloca(Ty::I64);
    fb.store(Ty::I32, cell, n0);
    let zero = fb.iconst(Ty::I32, 0);
    let zero64 = fb.iconst(Ty::I64, 0);
    fb.store(Ty::I64, scratch, zero64);
    fb.br(head, vec![zero, n0]);

    fb.switch_to_block(head);
    let k0 = fb.iconst(Ty::I32, 0);
    let more = fb.icmp(ICmpOp::Sgt, Ty::I32, n_p, k0);
    fb.condbr(more, body, vec![], exit, vec![acc_p]);

    fb.switch_to_block(body);
    let acc1 = fb.add(Ty::I32, acc_p, n_p);
    let one = fb.iconst(Ty::I32, 1);
    let n1 = fb.sub(Ty::I32, n_p, one);
    fb.br(head, vec![acc1, n1]);

    fb.switch_to_block(exit);
    let out = fb.add_block_param(exit, Ty::I32);
    let saved = fb.load(Ty::I32, cell);
    let total = fb.add(Ty::I32, out, saved);
    fb.ret(vec![total]);
    fb.build();

    let module = finish_wasm32(mb);
    let bytes = wasm::compile_module(&module).expect("live compile");
    let ev = wasm_abi_evidence(&bytes, &module).expect("evidence");
    assert!(
        ev.refusals.is_empty(),
        "the family REFUSED a live loop-with-frame shape: {:#?}",
        ev.refusals
    );
    let failed: Vec<&str> = ev
        .failed_structural()
        .iter()
        .map(|c| c.name.as_str())
        .collect();
    assert!(failed.is_empty(), "{failed:#?}");
    let counts = discharge_by_evaluation(&ev.obligations, &cfg());
    eprintln!(
        "live loop-with-frame: {} obligation(s), {} proven / {} refuted / {} inconclusive; {} \
         structural check(s)",
        ev.obligations.len(),
        counts.proven,
        counts.refuted.len(),
        counts.inconclusive.len(),
        ev.structural.len()
    );
    assert!(
        ev.obligations.len() >= 8,
        "two allocas should yield at least 8 obligations, got {}",
        ev.obligations.len()
    );
    assert_eq!(counts.proven, ev.obligations.len(), "{counts:#?}");
}

/// A live module whose calls sit INSIDE a branch, with two host imports of
/// different signatures. The index space is import-shifted and the call sites
/// are not in trust-ir order in the emitted body — exactly the case the
/// multiset statement is written for.
#[test]
fn live_calls_inside_a_branch_are_covered() {
    let mut mb = ModuleBuilder::new("abi_live_branch");
    let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let ft1 = mb.add_func_type(vec![Ty::I64], vec![Ty::I32]);
    let host_a = mb.function("host_a", ft2).build();
    let host_b = mb.function("host_b", ft1).build();
    let mut fb = mb.function("pick", ft2);
    let entry = fb.create_block();
    let lhs = fb.create_block();
    let rhs = fb.create_block();
    let join = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I32);
    let y = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let k = fb.iconst(Ty::I32, 0);
    let c = fb.icmp(ICmpOp::Sgt, Ty::I32, x, k);
    fb.condbr(c, lhs, vec![], rhs, vec![]);

    fb.switch_to_block(lhs);
    let a = fb.call(host_a, vec![x, y]);
    fb.br(join, vec![a]);

    fb.switch_to_block(rhs);
    let w = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, y);
    let b = fb.call(host_b, vec![w]);
    fb.br(join, vec![b]);

    fb.switch_to_block(join);
    let r = fb.add_block_param(join, Ty::I32);
    fb.ret(vec![r]);
    fb.build();

    let module = finish_wasm32(mb);
    let policy = WasmModulePolicy {
        func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("live")),
        ..WasmModulePolicy::closed()
    };
    let bytes = wasm::compile_module_with_policy(&module, &policy).expect("live compile");

    // The decode must independently agree that the import space is 2 wide and
    // that `pick` is function 2.
    let dec = decode_module(&bytes).expect("decode");
    assert_eq!(dec.func_import_count(), 2);
    let intended = intended_module(&module).expect("model");
    assert_eq!(intended.defined[0].index, 2);

    let ev = wasm_abi_evidence(&bytes, &module).expect("evidence");
    assert!(ev.refusals.is_empty(), "{:#?}", ev.refusals);
    let failed: Vec<String> = ev
        .failed_structural()
        .iter()
        .map(|c| format!("{}: {}", c.name, c.detail))
        .collect();
    assert!(failed.is_empty(), "{failed:#?}");
    eprintln!(
        "live branchy calls: {} structural check(s), {} obligation(s)",
        ev.structural.len(),
        ev.obligations.len()
    );

    // And the import-shift bug is still caught on THIS module: rewriting
    // `call 0` (host_a) to `call 2` (pick, a same-signature recursion) changes
    // the multiset of targets, so C1 fails.
    let swap = AbiGuard {
        name: "live: call 0 -> call 2 (a target outside the call set)",
        fixture: "abi_live_branch",
        needle: &[0x10, 0x00],
        patch: &[0x10, 0x02],
        expectation: GuardExpectation::MustRefute,
    };
    let outcome = run_guard(&swap, &bytes, &module, &cfg()).expect("guard runs");
    assert!(
        outcome.refuted,
        "a wrong call target on a LIVE branchy module was not caught: {}",
        outcome.detail
    );
}

/// A frameless island under an IMPORTED memory: no prologue, no stack global,
/// and the family must say so positively rather than silently crediting the
/// absence of evidence.
#[test]
fn a_frameless_island_is_positively_covered() {
    let mut mb = ModuleBuilder::new("abi_live_pure");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("read_word", ft);
    let e = fb.create_block();
    let p = fb.add_block_param(e, Ty::Ptr);
    let i = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let q = fb.gep(Ty::I32, p, vec![i]);
    let v = fb.load(Ty::I32, q);
    fb.ret(vec![v]);
    fb.build();
    let module = finish_wasm32(mb);
    let bytes = wasm::compile_module_with_policy(&module, &WasmModulePolicy::island("pure"))
        .expect("compile");

    let ev = wasm_abi_evidence(&bytes, &module).expect("evidence");
    assert!(ev.refusals.is_empty(), "{:#?}", ev.refusals);
    let failed: Vec<String> = ev
        .failed_structural()
        .iter()
        .map(|c| format!("{}: {}", c.name, c.detail))
        .collect();
    assert!(failed.is_empty(), "{failed:#?}");
    // A frameless function states NO frame obligation — and that is reported as
    // "no obligation", never as a satisfied one.
    assert!(
        ev.obligations.is_empty(),
        "a frameless island stated frame obligations: {:#?}",
        ev.obligations.iter().map(|o| &o.name).collect::<Vec<_>>()
    );
    assert!(
        ev.structural
            .iter()
            .any(|c| c.name.contains("a frameless function emits no prologue")),
        "the frameless case must be stated POSITIVELY"
    );
    let dec = decode_module(&bytes).expect("decode");
    assert!(dec.imports_memory(), "the island must import its memory");
    assert!(
        dec.memory_min_pages.is_none(),
        "an island under an imported memory must not DEFINE one"
    );
}

// ---------------------------------------------------------------------------
// 5. The deferral ledger
// ---------------------------------------------------------------------------

/// The named deferrals stay RED and stay auditable. Print them, so a reader of
/// the test output sees what this family does NOT cover next to what it does.
#[test]
fn deferrals_stay_red_and_named() {
    assert_eq!(
        WASM_ABI_DEFERRALS.len(),
        9,
        "the deferral ledger changed; landing evidence for one is good, but it must be a \
         deliberate edit"
    );
    eprintln!("wasm_abi NAMED DEFERRALS (RED, never allowlisted out):");
    for d in WASM_ABI_DEFERRALS {
        eprintln!("  [{}] {}  ({})", d.owner, d.name, d.citation);
        assert!(
            d.reason.len() > 120,
            "deferral `{}` has a token reason, not an auditable one",
            d.name
        );
    }
    // Four of the nine are HOST obligations under the ownership map; the file
    // must keep citing it rather than paraphrasing it.
    let host = WASM_ABI_DEFERRALS
        .iter()
        .filter(|d| d.owner.starts_with("HOST"))
        .count();
    assert!(
        host >= 4,
        "the host half of the ownership map must stay explicitly deferred"
    );
    assert!(
        WASM_ABI_DEFERRALS.iter().all(|d| !d.citation.is_empty()),
        "every deferral needs a citation"
    );
}

// ---------------------------------------------------------------------------
// 6. The family is COUNTED by the coverage gate, not merely present
// ---------------------------------------------------------------------------

/// Run `f` on a large stack so `ProofDatabase::new()` does not overflow the
/// default test-thread stack (proof_database.rs #205).
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("wasm-abi-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack gate thread")
        .join()
        .expect("gate thread panicked")
}

/// PINS the family's rows in `GateArch::WasmAbi`: 128 rows, ALL of them in the
/// denominator, 118 covered and 10 RED.
///
/// The breakdown is 22 reconstructed frame obligations + 80 decidable structural
/// checks + 16 refuting anti-tautology guards = 118 covered; 1 declared blind
/// guard + the 9 named deferrals = 10 RED. NOTHING is allowlisted out: five of
/// the nine deferrals are the HOST's under the ownership map, and being someone
/// else's obligation is a reason to name an owner, not a reason to drop the row.
///
/// A module the family cannot decode contributes a REFUSAL row, which is RED and
/// earns no credit — so a fixture drifting out of recognition shows up as debt
/// here rather than as a smaller, cleaner-looking denominator.
#[test]
fn the_family_is_counted_in_the_coverage_gate() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmAbi));
    eprintln!("{}", report.audit_log());

    assert_eq!(
        report.total(),
        128,
        "wasm-abi gate row count changed — 22 frame obligations + 80 structural checks + 17 \
         guards + 9 deferrals.\n{}",
        report.audit_log()
    );
    assert_eq!(
        report.emittable_count(),
        128,
        "every wasm-abi row stays IN the denominator; nothing here may be allowlisted out"
    );
    assert_eq!(
        report.allowlisted_count(),
        0,
        "no wasm-abi row may be excluded from the denominator"
    );
    assert_eq!(
        report.covered_count(),
        118,
        "wasm-abi covered count changed — do NOT inflate by crediting a deferral, a blind guard, \
         or a refusal.\n{}",
        report.audit_log()
    );
    assert_eq!(
        report.failures().len(),
        10,
        "exactly the declared blind guard and the nine named deferrals are RED:\n{}",
        report.failure_summary()
    );
}

/// LOCKS IN that every RED wasm-abi row is a NAMED deferral, never a wiring gap,
/// and that the credited rows and the deferred rows are DISJOINT.
///
/// A `NoProofMapping` row here would be a fixture the family could not model at
/// all, or a function it refused — real debt, but a different class from named
/// deferral, and it must never be silently absorbed into one. A row that was
/// both credited and deferred would be the bookkeeping error the value-domain
/// family's enumeration exists to prevent.
#[test]
fn gate_red_rows_are_named_deferrals_and_disjoint_from_credit() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmAbi));
    for row in report.failures() {
        assert!(
            matches!(
                row.finding,
                Some(CoverageFinding::DeferredUnfaithfulModel { .. })
            ),
            "wasm-abi RED row {} is a WIRING GAP (refusal / unmodeled fixture / undischarged \
             obligation), not an honest deferral:\n{}",
            row.opcode_display,
            report.failure_summary()
        );
    }
    let red: std::collections::HashSet<&str> = report
        .failures()
        .iter()
        .map(|r| r.opcode_display.as_str())
        .collect();
    let credited: std::collections::HashSet<&str> = report
        .rows
        .iter()
        .filter(|r| r.finding.is_none())
        .map(|r| r.opcode_display.as_str())
        .collect();
    assert!(
        red.is_disjoint(&credited),
        "a wasm-abi row is BOTH credited and deferred: {:?}",
        red.intersection(&credited).collect::<Vec<_>>()
    );
    // Every named deferral reaches the gate under its own name.
    for d in WASM_ABI_DEFERRALS {
        assert!(
            red.contains(format!("wasm-abi::{}", d.name).as_str()),
            "deferral `{}` is not a RED row in the gate — a deferral that does not reach the \
             inventory is invisible debt",
            d.name
        );
    }
}

/// LOCKS IN that the family's SMT credit is RECONSTRUCTION credit.
///
/// The frame obligations rebuild their machine side by DECODING the emitted
/// prologue / alloca / epilogue instructions, so `is_reconstructed()` is the
/// discriminator that keeps a `StaticDb` X==X from ever being the reason a row
/// is green. The structural checks are decidable equalities between the decoded
/// module and the trust-ir's independently derived intent, and the guards are
/// refutations of real byte mutations; none of the three is a self-equality.
#[test]
fn gate_credit_never_rests_on_a_self_equality() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmAbi));
    let mut reconstruction_credits = 0usize;
    for row in &report.rows {
        if row.finding.is_some() {
            continue;
        }
        assert!(
            !row.note.contains("DEGENERATE"),
            "covered wasm-abi row {} is credited via a DEGENERATE (X==X) proof: {}",
            row.opcode_display,
            row.note
        );
        if row.note.contains("[reconstruction]") {
            reconstruction_credits += 1;
        }
    }
    assert_eq!(
        reconstruction_credits, 22,
        "the 22 frame obligations are the family's reconstruction-credited rows; if that count \
         moves, the frame family gained or lost an obligation and the pin above moved with it"
    );
}
