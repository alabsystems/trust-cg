// trust-cg-verify/tests/t_silicon_sat_export.rs - t-silicon route-1 upstream export
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// THE LOWERING VCs THAT REACH CNF+DRAT IN-TREE. Drives the full producer chain
// for the ≤8-bit ALU tier — the arithmetic (iadd/isub/neg) AND bitwise
// (band/bor/bxor) i8 lowering rules — proving the lowering catalogue is
// certifiable for a real op FAMILY, not just one hand-picked rule (route (a) of
// trust-ir `designs/2026-07-01-t-silicon-one-tcb-scoping.md`):
//
//   ProofObligation ──sat_blast──> DIMACS miter (UNSAT ⇔ rule correct)
//                    + MiterProvenance (per-clause gate provenance)
//     ──trust-cg-sat-host MicroSAT (+ DRAT recorder)──> proof.drat
//     ──trust-cg-drat-trim──> `s VERIFIED` + TraceCheck trace (-r)
//
// The (cnf, drat, trace, prov) quadruple per rule is pinned as committed
// fixtures under `tests/fixtures/t_silicon/`; downstream (trust-ir) the trace
// is expanded to binary resolution Steps and kernel-re-checked through
// clean-kernel's verified `Clean.Res.checkRefutes3` reflection checker, and the
// prov is re-checked against the payload's clause list and carried into the
// certificate (the t-silicon route-1 milestone).
//
// Regenerate fixtures after an intentional blaster/solver change with:
//   TRUST_CG_BLESS_SAT_FIXTURES=1 cargo test -p trust-cg-verify \
//     --test t_silicon_sat_export
//
// TRUST BOUNDARY: everything in this file is UNTRUSTED producer plumbing.
// Soundness comes from the downstream kernel re-check. Gate-level ENCODING
// FIDELITY (each clause is a NAMED gate's CNF, sides compared bit-for-bit) is
// producer-checked via `MiterCnf::check_provenance`; the residual asserted
// boundary is gate-DAG⇔SmtExpr — see the `sat_blast` module docs.

use std::ffi::CString;
use std::fs;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use trust_cg_sat_host::drat_recorder::{
    disable_drat_output, enable_drat_output, flush_drat_output,
};
use trust_cg_sat_host::sys;
use trust_cg_verify::lowering_proof::{
    ProofObligation, proof_band_i8, proof_bor_i8, proof_bxor_i8, proof_iadd_i8, proof_isub_i8,
    proof_neg_i8,
};
use trust_cg_verify::sat_blast::blast_equivalence_miter;
use trust_cg_verify::smt::SmtExpr;

/// The DRAT recorder and the propagate-mode atomics are process-global;
/// serialize every MicroSAT-driving test in this binary.
static SOLVER_LOCK: Mutex<()> = Mutex::new(());

/// One member of the ≤8-bit ALU tier under test: a fixture key, the rule's
/// obligation, and a WRONG machine side (a different supported op) whose miter
/// must come out SAT — the per-rule non-vacuity control.
struct AluRule {
    key: &'static str,
    obligation: fn() -> ProofObligation,
    wrong_machine_side: fn() -> SmtExpr,
}

/// The certifiable i8 ALU family. Arithmetic (ripple-carry) + bitwise (per-bit).
/// Each wrong-side is a non-capturing `fn` so it coerces to a function pointer.
fn alu_family() -> Vec<AluRule> {
    fn a() -> SmtExpr {
        SmtExpr::var("a", 8)
    }
    fn b() -> SmtExpr {
        SmtExpr::var("b", 8)
    }
    vec![
        AluRule {
            key: "iadd_i8",
            obligation: proof_iadd_i8,
            wrong_machine_side: || a().bvsub(b()),
        },
        AluRule {
            key: "isub_i8",
            obligation: proof_isub_i8,
            wrong_machine_side: || a().bvadd(b()),
        },
        AluRule {
            key: "neg_i8",
            obligation: proof_neg_i8,
            // NEG lowered as identity: -a != a for almost all a ⇒ SAT.
            wrong_machine_side: a,
        },
        AluRule {
            key: "band_i8",
            obligation: proof_band_i8,
            wrong_machine_side: || a().bvor(b()),
        },
        AluRule {
            key: "bor_i8",
            obligation: proof_bor_i8,
            wrong_machine_side: || a().bvand(b()),
        },
        AluRule {
            key: "bxor_i8",
            obligation: proof_bxor_i8,
            wrong_machine_side: || a().bvand(b()),
        },
    ]
}

fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/t_silicon")
}

fn bless_mode() -> bool {
    std::env::var_os("TRUST_CG_BLESS_SAT_FIXTURES").is_some()
}

/// Compare `actual` against the committed fixture (or overwrite it in bless
/// mode). Byte-exact: the blaster and the in-process MicroSAT lane are
/// deterministic, and downstream trust-ir carries copies of these artifacts —
/// silent drift between the repos is exactly what this pin exists to catch.
fn pin_fixture(name: &str, actual: &[u8]) {
    let path = fixtures_dir().join(name);
    if bless_mode() {
        fs::create_dir_all(fixtures_dir()).expect("create fixtures dir");
        fs::write(&path, actual).expect("bless fixture");
        return;
    }
    let expected = fs::read(&path).unwrap_or_else(|e| {
        panic!(
            "missing committed fixture {} ({e}); run with TRUST_CG_BLESS_SAT_FIXTURES=1 to \
             generate",
            path.display()
        )
    });
    assert_eq!(
        expected,
        actual,
        "fixture {} drifted from the live pipeline output; if the change is intentional, \
         re-bless AND refresh the trust-ir copies (crates/trust-ir-build/tests/fixtures/)",
        path.display()
    );
}

/// Run the in-process MicroSAT (trampolined, native mode) over `cnf_path`.
/// Returns the MicroSAT result code (`sys::SAT` / `sys::UNSAT`).
fn run_microsat(cnf_path: &Path) -> i32 {
    let c_path = CString::new(cnf_path.to_string_lossy().into_owned()).expect("cnf path");
    let mut solver: MaybeUninit<sys::solver> = MaybeUninit::uninit();
    // SAFETY: `parse` is the upstream entry point and itself calls `initCDCL`,
    // which initialises every solver field it reads — the same construction
    // MicroSAT's own `main` uses (mirrors trust-cg-sat-host's tests).
    let parse_rc = unsafe {
        sys::parse(
            solver.as_mut_ptr(),
            c_path.as_ptr() as *mut std::os::raw::c_char,
        )
    };
    if parse_rc == sys::UNSAT {
        return sys::UNSAT;
    }
    // SAFETY: `parse` returned without UNSAT, so the solver state is
    // initialised; calling `solve` matches the upstream usage.
    unsafe { sys::solve(solver.as_mut_ptr()) }
}

/// Full positive chain for one rule: blast → provenance self-check →
/// MicroSAT DRAT → drat-trim VERIFIED → trace, pinning the (cnf, prov, drat,
/// trace) quadruple.
fn run_positive_chain(rule: &AluRule) {
    let miter = blast_equivalence_miter(&(rule.obligation)())
        .unwrap_or_else(|e| panic!("blast {} failed: {e}", rule.key));
    // Gate-level encoding-fidelity self-check (redundant with the in-blaster
    // call, asserted here so a regression is attributed to the right rule).
    miter
        .check_provenance()
        .unwrap_or_else(|e| panic!("{} provenance incoherent: {e}", rule.key));

    let dimacs = miter.to_dimacs();
    pin_fixture(&format!("{}_miter.cnf", rule.key), dimacs.as_bytes());
    let prov = miter
        .provenance
        .to_text()
        .unwrap_or_else(|| panic!("{} provenance must serialize", rule.key));
    pin_fixture(&format!("{}_miter.prov", rule.key), prov.as_bytes());

    let dir = tempfile::tempdir().expect("tempdir");
    let cnf_path = dir.path().join("miter.cnf");
    let drat_path = dir.path().join("miter.drat");
    let trace_path = dir.path().join("miter.trace");
    fs::write(&cnf_path, &dimacs).expect("write cnf");

    // Solve with the DRAT recorder attached: the rule's correctness is the
    // UNSAT verdict, and the DRAT file is its replayable evidence.
    enable_drat_output(&drat_path).expect("enable drat");
    let rc = run_microsat(&cnf_path);
    flush_drat_output().expect("flush drat");
    disable_drat_output();
    assert_eq!(
        rc,
        sys::UNSAT,
        "the {} lowering miter must be UNSAT (the lowering rule is correct)",
        rule.key
    );

    let drat = fs::read(&drat_path).expect("read drat");
    assert!(!drat.is_empty(), "DRAT proof must be non-empty");
    pin_fixture(&format!("{}_miter.drat", rule.key), &drat);

    // Independent DRAT check + TraceCheck resolution-graph emission via the
    // vendored drat-trim.
    let out = Command::new(trust_cg_drat_trim::drat_trim_executable_path())
        .arg(&cnf_path)
        .arg(&drat_path)
        .arg("-r")
        .arg(&trace_path)
        .output()
        .expect("invoke drat-trim");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success() && stdout.contains("s VERIFIED"),
        "drat-trim must verify the {} DRAT proof.\nstdout: {stdout}\nstderr: {}",
        rule.key,
        String::from_utf8_lossy(&out.stderr)
    );

    let trace = fs::read(&trace_path).expect("read trace");
    assert!(!trace.is_empty(), "TraceCheck trace must be non-empty");
    pin_fixture(&format!("{}_miter.trace", rule.key), &trace);
}

/// THE FAMILY, positive: every i8 ALU rule's lowering VC reaches a
/// drat-trim-VERIFIED (cnf, prov, drat, trace) quadruple.
#[test]
fn i8_alu_family_lowering_vcs_reach_verified_cnf_drat_trace() {
    let _guard = SOLVER_LOCK.lock().expect("solver lock");
    for rule in alu_family() {
        run_positive_chain(&rule);
    }
}

/// The committed fixture quadruple stays internally coherent for every rule:
/// drat-trim must still verify the COMMITTED drat against the COMMITTED cnf.
/// Guards against a partial re-bless (or a hand-edit) leaving the repo carrying
/// an artifact pair the downstream trust-ir E2E could never have produced.
#[test]
fn committed_fixture_quadruples_are_coherent() {
    if bless_mode() {
        return; // Fresh artifacts are being generated by the positive test.
    }
    for rule in alu_family() {
        let cnf = fixtures_dir().join(format!("{}_miter.cnf", rule.key));
        let drat = fixtures_dir().join(format!("{}_miter.drat", rule.key));
        let prov = fixtures_dir().join(format!("{}_miter.prov", rule.key));
        assert!(
            cnf.exists() && drat.exists() && prov.exists(),
            "{} fixture quadruple missing; run with TRUST_CG_BLESS_SAT_FIXTURES=1",
            rule.key
        );
        let out = Command::new(trust_cg_drat_trim::drat_trim_executable_path())
            .arg(&cnf)
            .arg(&drat)
            .output()
            .expect("invoke drat-trim");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            out.status.success() && stdout.contains("s VERIFIED"),
            "{} committed fixtures failed drat-trim: {stdout}",
            rule.key
        );
    }
}

/// NEGATIVE CONTROL (non-vacuity), per rule: a WRONG machine side (a different
/// supported op) must yield a SATISFIABLE miter. This is what makes each UNSAT
/// verdict above a genuine correctness check rather than a tautology: the same
/// pipeline refutes a real miscompile pattern for every rule in the family.
#[test]
fn wrong_machine_side_miters_are_sat() {
    let _guard = SOLVER_LOCK.lock().expect("solver lock");
    for rule in alu_family() {
        let mut wrong = (rule.obligation)();
        wrong.aarch64_expr = (rule.wrong_machine_side)();
        let miter = blast_equivalence_miter(&wrong)
            .unwrap_or_else(|e| panic!("blast wrong-side {} failed: {e}", rule.key));

        let dir = tempfile::tempdir().expect("tempdir");
        let cnf_path = dir.path().join("wrong.cnf");
        fs::write(&cnf_path, miter.to_dimacs()).expect("write cnf");

        let rc = run_microsat(&cnf_path);
        assert_eq!(
            rc,
            sys::SAT,
            "a wrong-lowered {} miter must be SAT (counterexample exists)",
            rule.key
        );
    }
}
