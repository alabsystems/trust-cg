// trust-cg-verify/tests/fp_bitmodel_bridge.rs — DELIVERABLE of the FP-bit-model
// host-FPU eviction campaign (#89).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE FP BIT-MODEL <-> SILICON DIFFERENTIAL BRIDGE.
// ===========================================================================
//
// THE FINDING this defeats: trust-cg's FP verification path (smt.rs try_eval FP
// cases) computed every F32/F64 op via NATIVE Rust f64 arithmetic, so the host
// CPU's FPU was inside the FP-verification TCB. crates/trust-cg-verify/src/
// fp_bitmodel.rs replaces native float arithmetic with a DETERMINISTIC,
// INTEGER-ONLY, bit-level IEEE-754 model (u32/u64/u128 + shifts/masks; ZERO
// f32/f64 arithmetic — see the grep gate below). This test VALIDATES that
// integer-only model, bit-for-bit, against REAL Apple M4 silicon.
//
// Every fact in tests/fixtures/aarch64_fp_silicon_truth.json is a result
// recorded from a real Apple M4 Pro (an `:= rfl` chip theorem in the sibling
// Clean tree's proofs/aarch64_fp*_chip.lean — the HARDWARE oracle, strictly
// stronger than any second software model). For each fact this test:
//
//   1. takes the op tag + the silicon operand integer(s) (decoded from the
//      Clean List-Bool literals by the fixture generator),
//   2. runs trust-cg's OWN INTEGER-ONLY bit-model function for that op
//      (fp_bitmodel::fadd / fmul / fcvt_* / fcvtzs / scvtf / fcmp_n / …),
//   3. asserts the bit-model result EQUALS the SILICON-recorded result.
//
// A mismatch is a FINDING (a bit-model bug, or a convention divergence between
// the port and the M4). It is NOT papered over by excluding the op or loosening
// the comparison. The bridge is NON-VACUOUS: `bridge_is_non_vacuous_*` below
// prove that DELIBERATELY-WRONG bit-models mismatch silicon facts (so the
// bridge has teeth — it is not a tautology and not a self-comparison).
//
// SCOPE: FADD/FMUL (RNE), FABS/FNEG, FCMP→NZCV (per flag), FMIN/FMAX/FMINNM/
// FMAXNM, classify (isNaN/Inf/Zero/Normal/Subnormal/QNaN/SNaN), FCVT widen/
// narrow, f→int (FCVTZS/ZU/NS/NU at W and X), int→f (SCVTF/UCVTF at W/X to
// .s/.d), AND — newly ported (#94) — FDIV/FSQRT (RNE) at binary32 + binary64
// (integer-only long-division / digit-by-digit sqrt + remainder-sticky), with
// the host FPU now EVICTED for div/sqrt in smt.rs. The fixture's `deferred_ops`
// is now empty for AArch64 scalar binary32/binary64.

use serde_json::Value;

use trust_cg_verify::fp_bitmodel::{
    F16, F32, F64, FpFmt, fabs, fadd, fcmp_c, fcmp_n, fcmp_v, fcmp_z, fcvt_d_to_h, fcvt_h_to_d,
    fcvt_h_to_s, fcvt_narrow, fcvt_s_to_h, fcvt_widen, fcvtns, fcvtnu, fcvtzs, fcvtzu, fdiv, fmax,
    fmaxnm, fmin, fminnm, fmul, fneg, fsqrt, fsub, is_inf, is_nan, is_normal, is_qnan, is_snan,
    is_subnormal, is_zero, scvtf, ucvtf,
};

const FIXTURE: &str = include_str!("fixtures/aarch64_fp_silicon_truth.json");

/// A single FP silicon ground-truth fact (one chip `:= rfl` theorem).
struct Fact {
    op: String,
    lean_def: String,
    kind: String,
    in_widths: Vec<u32>,
    operands: Vec<u64>,
    result: u64,
    result_kind: String, // "bool" | "bits"
    result_width: u32,
}

fn load_facts() -> Vec<Fact> {
    let doc: Value = serde_json::from_str(FIXTURE).expect("FP fixture is valid JSON");
    let arr = doc["facts"]
        .as_array()
        .expect("fixture has a `facts` array");
    arr.iter()
        .map(|f| Fact {
            op: f["op"].as_str().expect("op is a string").to_string(),
            lean_def: f["lean_def"]
                .as_str()
                .expect("lean_def is a string")
                .to_string(),
            kind: f["kind"].as_str().expect("kind is a string").to_string(),
            in_widths: f["in_widths"]
                .as_array()
                .expect("in_widths is an array")
                .iter()
                .map(|v| v.as_u64().expect("in_width is a number") as u32)
                .collect(),
            operands: f["operands"]
                .as_array()
                .expect("operands is an array")
                .iter()
                .map(|v| v.as_u64().expect("operand is a u64 literal"))
                .collect(),
            result: f["result"].as_u64().expect("result is a u64"),
            result_kind: f["result_kind"].as_str().expect("result_kind").to_string(),
            result_width: f["result_width"].as_u64().expect("result_width") as u32,
        })
        .collect()
}

/// FP format for a source bit width (16 -> F16, 32 -> F32, 64 -> F64).
fn fmt_of(width: u32) -> FpFmt {
    match width {
        16 => F16,
        32 => F32,
        64 => F64,
        other => panic!("bridge: unexpected FP width {other}"),
    }
}

/// Run the INTEGER-ONLY bit-model for `fact`, returning the result as a u64
/// (a classify/cmp bool is 0/1). `None` => an op tag the bridge does not model
/// (must never happen — every fixture op has a bit-model; an unknown tag is a
/// fixture/bridge drift bug, caught by the assert in the driver).
fn run_bitmodel(fact: &Fact) -> Option<u64> {
    let op0 = || fact.operands[0];
    let val = match fact.op.as_str() {
        // ---- classify (one f-operand -> bool 0/1).
        "isNaN" => is_nan(fmt_of(fact.in_widths[0]), op0()) as u64,
        "isInf" => is_inf(fmt_of(fact.in_widths[0]), op0()) as u64,
        "isZero" => is_zero(fmt_of(fact.in_widths[0]), op0()) as u64,
        "isNormal" => is_normal(fmt_of(fact.in_widths[0]), op0()) as u64,
        "isSubnormal" => is_subnormal(fmt_of(fact.in_widths[0]), op0()) as u64,
        "isQNaN" => is_qnan(fmt_of(fact.in_widths[0]), op0()) as u64,
        "isSNaN" => is_snan(fmt_of(fact.in_widths[0]), op0()) as u64,
        // ---- FABS / FNEG.
        "fabs" => fabs(fmt_of(fact.in_widths[0]), op0()),
        "fneg" => fneg(fmt_of(fact.in_widths[0]), op0()),
        // ---- FCMP -> NZCV per flag.
        "fcmpN" => fcmp_n(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ) as u64,
        "fcmpZ" => fcmp_z(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ) as u64,
        "fcmpC" => fcmp_c(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ) as u64,
        "fcmpV" => fcmp_v(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ) as u64,
        // ---- FMIN / FMAX / FMINNM / FMAXNM.
        "fmin" => fmin(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ),
        "fmax" => fmax(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ),
        "fminnm" => fminnm(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ),
        "fmaxnm" => fmaxnm(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ),
        // ---- FADD / FMUL (RNE).
        "fadd" => fadd(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ),
        "fmul" => fmul(
            fmt_of(fact.in_widths[0]),
            fact.operands[0],
            fact.operands[1],
        ),
        // ---- FCVT f<->f.
        "fcvt_widen" => fcvt_widen(op0()),
        "fcvt_narrow" => fcvt_narrow(op0()),
        // ---- FCVT f->int. tag = <op>_<s|d>_<w|x>.
        "fcvtzs_s_w" => fcvtzs(F32, 32, op0()),
        "fcvtzs_s_x" => fcvtzs(F32, 64, op0()),
        "fcvtzs_d_w" => fcvtzs(F64, 32, op0()),
        "fcvtzs_d_x" => fcvtzs(F64, 64, op0()),
        "fcvtzu_s_w" => fcvtzu(F32, 32, op0()),
        "fcvtzu_s_x" => fcvtzu(F32, 64, op0()),
        "fcvtzu_d_w" => fcvtzu(F64, 32, op0()),
        "fcvtzu_d_x" => fcvtzu(F64, 64, op0()),
        "fcvtns_s_w" => fcvtns(F32, 32, op0()),
        "fcvtns_s_x" => fcvtns(F32, 64, op0()),
        "fcvtns_d_w" => fcvtns(F64, 32, op0()),
        "fcvtns_d_x" => fcvtns(F64, 64, op0()),
        "fcvtnu_s_w" => fcvtnu(F32, 32, op0()),
        "fcvtnu_s_x" => fcvtnu(F32, 64, op0()),
        "fcvtnu_d_w" => fcvtnu(F64, 32, op0()),
        "fcvtnu_d_x" => fcvtnu(F64, 64, op0()),
        // ---- FCVT int->f. tag = <op>_<w|x>_<s|d>.
        "scvtf_w_s" => scvtf(F32, 32, op0()),
        "scvtf_x_s" => scvtf(F32, 64, op0()),
        "scvtf_w_d" => scvtf(F64, 32, op0()),
        "scvtf_x_d" => scvtf(F64, 64, op0()),
        "ucvtf_w_s" => ucvtf(F32, 32, op0()),
        "ucvtf_x_s" => ucvtf(F32, 64, op0()),
        "ucvtf_w_d" => ucvtf(F64, 32, op0()),
        "ucvtf_x_d" => ucvtf(F64, 64, op0()),
        // ---- FP16 (binary16 / ARMv8.2-FP16). classify at F16 -> bool 0/1.
        "isNaN16" => is_nan(F16, op0()) as u64,
        "isInf16" => is_inf(F16, op0()) as u64,
        "isZero16" => is_zero(F16, op0()) as u64,
        "isNormal16" => is_normal(F16, op0()) as u64,
        "isSubnormal16" => is_subnormal(F16, op0()) as u64,
        "isQNaN16" => is_qnan(F16, op0()) as u64,
        "isSNaN16" => is_snan(F16, op0()) as u64,
        // ---- FP16 FCVT widen (EXACT) / narrow (RNE).
        "fcvt_h_to_s" => fcvt_h_to_s(op0()),
        "fcvt_h_to_d" => fcvt_h_to_d(op0()),
        "fcvt_s_to_h" => fcvt_s_to_h(op0()),
        "fcvt_d_to_h" => fcvt_d_to_h(op0()),
        // ---- scalar FP16 FADD.h / FMUL.h (RNE) — width-generic bit-model at F16.
        "fadd16" => fadd(F16, fact.operands[0], fact.operands[1]),
        "fmul16" => fmul(F16, fact.operands[0], fact.operands[1]),
        // ---- FDIV / FSQRT (RNE) — integer-only long-division / digit-by-digit
        // sqrt + remainder-sticky. The host FPU is EVICTED for div/sqrt.
        "fdiv32" => fdiv(F32, fact.operands[0], fact.operands[1]),
        "fdiv64" => fdiv(F64, fact.operands[0], fact.operands[1]),
        "fsqrt32" => fsqrt(F32, op0()),
        "fsqrt64" => fsqrt(F64, op0()),
        _ => return None,
    };
    Some(val)
}

// ===========================================================================
// THE BRIDGE — the integer-only bit-model must match silicon for EVERY fact.
// ===========================================================================
#[test]
fn fp_bitmodel_matches_silicon_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() >= 3000,
        "FP bridge: too few facts ({}) — the fixture must be the full chip grid",
        facts.len()
    );

    let mut mismatches: Vec<String> = Vec::new();
    let mut per_op_counts: std::collections::BTreeMap<String, usize> = Default::default();
    let mut checked = 0usize;

    for fact in &facts {
        *per_op_counts.entry(fact.op.clone()).or_insert(0) += 1;
        let got = match run_bitmodel(fact) {
            Some(v) => v,
            None => {
                mismatches.push(format!(
                    "UNMODELED OP `{}` (lean_def {}) — fixture/bridge drift",
                    fact.op, fact.lean_def
                ));
                continue;
            }
        };
        checked += 1;
        // kind/result_kind consistency: classify+cmp produce bools, the rest bits.
        let expect_bool = fact.kind == "classify" || fact.kind == "cmp";
        assert_eq!(
            expect_bool,
            fact.result_kind == "bool",
            "FP bridge: kind `{}` and result_kind `{}` disagree for {}",
            fact.kind,
            fact.result_kind,
            fact.lean_def
        );
        // compare on the result width (mask both, defensively).
        let mask = if fact.result_width >= 64 {
            u64::MAX
        } else {
            (1u64 << fact.result_width) - 1
        };
        if (got & mask) != (fact.result & mask) {
            mismatches.push(format!(
                "MISMATCH {} ({}): operands={:x?} bit-model=0x{:x} silicon=0x{:x} (kind={}, rw={})",
                fact.op,
                fact.lean_def,
                fact.operands
                    .iter()
                    .map(|o| format!("{o:x}"))
                    .collect::<Vec<_>>(),
                got & mask,
                fact.result & mask,
                fact.result_kind,
                fact.result_width,
            ));
        }
    }

    if !mismatches.is_empty() {
        let shown: Vec<_> = mismatches.iter().take(40).cloned().collect();
        panic!(
            "FP bit-model <-> silicon bridge found {} mismatch(es) out of {} facts \
             ({} checked).\nThe integer-only bit-model DIVERGES from real M4 silicon — \
             a bit-model bug or a convention divergence (NOT to be papered over).\n\
             First mismatches:\n{}",
            mismatches.len(),
            facts.len(),
            checked,
            shown.join("\n")
        );
    }

    // sanity: a few representative op families are actually exercised — including
    // the FP16 widen/narrow + scalar FADD.h/FMUL.h families (the model that
    // REPLACES trust-cg's bespoke fp16_bits_to_f64/f64_to_fp16_bits).
    for op in [
        "fadd",
        "fmul",
        "fcvt_widen",
        "fcvt_narrow",
        "fcvtzs_s_w",
        "scvtf_w_s",
        "fmin",
        "fcmpN",
        "fcvt_h_to_s",
        "fcvt_h_to_d",
        "fcvt_s_to_h",
        "fcvt_d_to_h",
        "fadd16",
        "fmul16",
        // FDIV/FSQRT — now ported + bridged (host FPU evicted for div/sqrt).
        "fdiv32",
        "fdiv64",
        "fsqrt32",
        "fsqrt64",
    ] {
        assert!(
            per_op_counts.get(op).copied().unwrap_or(0) > 0,
            "FP bridge: op family `{op}` has ZERO facts — coverage hole"
        );
    }
    eprintln!(
        "FP bit-model bridge: {} facts ALL match silicon (per-op: {:?})",
        checked, per_op_counts
    );
}

// ===========================================================================
// NON-VACUITY — deliberately-WRONG bit-models must mismatch a silicon fact.
// If these "passed" (a wrong model agreeing with silicon), the bridge would be
// a tautology / self-comparison and prove nothing. They REFUTE, so it has teeth.
// ===========================================================================

/// A wrong FADD that drops the rounding (truncates the guard/round/sticky to 0
/// by ignoring them) — concretely we model it as "ignore the second operand"
/// which is obviously wrong for the recorded 1.0+1.0=2.0 etc.
fn wrong_fadd(_f: FpFmt, a: u64, _b: u64) -> u64 {
    a // identity in the first operand — wrong for nontrivial adds.
}

/// A wrong FCMP-N that always returns false (drops the LT detection).
fn wrong_fcmp_n(_f: FpFmt, _a: u64, _b: u64) -> bool {
    false
}

/// A wrong FCVTZS that forgets to round toward zero and instead returns 0.
fn wrong_fcvtzs(_f: FpFmt, _int_w: u32, _x: u64) -> u64 {
    0
}

#[test]
fn bridge_is_non_vacuous_fadd() {
    // there MUST exist at least one fadd fact the WRONG model disagrees with.
    let facts = load_facts();
    let mut found_disagreement = false;
    let mut correct_agrees = 0usize;
    let mut fadd_count = 0usize;
    for fact in &facts {
        if fact.op != "fadd" {
            continue;
        }
        fadd_count += 1;
        let f = fmt_of(fact.in_widths[0]);
        // correct model agrees:
        if fadd(f, fact.operands[0], fact.operands[1]) == fact.result {
            correct_agrees += 1;
        }
        // wrong model disagrees somewhere:
        if wrong_fadd(f, fact.operands[0], fact.operands[1]) != fact.result {
            found_disagreement = true;
        }
    }
    assert!(fadd_count > 0, "non-vacuity: no fadd facts");
    assert_eq!(
        correct_agrees, fadd_count,
        "non-vacuity precondition: the CORRECT bit-model must agree with all {fadd_count} fadd facts"
    );
    assert!(
        found_disagreement,
        "NON-VACUITY FAILURE: a deliberately-wrong FADD (identity in op0) agreed with EVERY \
         silicon fact — the bridge would have no teeth"
    );
}

#[test]
fn bridge_is_non_vacuous_fcmp() {
    let facts = load_facts();
    let mut found_disagreement = false;
    let mut cmp_count = 0usize;
    for fact in &facts {
        if fact.op != "fcmpN" {
            continue;
        }
        cmp_count += 1;
        let f = fmt_of(fact.in_widths[0]);
        let wrong = wrong_fcmp_n(f, fact.operands[0], fact.operands[1]) as u64;
        if wrong != fact.result {
            found_disagreement = true;
        }
    }
    assert!(cmp_count > 0, "non-vacuity: no fcmpN facts");
    assert!(
        found_disagreement,
        "NON-VACUITY FAILURE: a deliberately-wrong FCMP-N (always false) agreed with EVERY \
         silicon LT fact — the bridge would have no teeth"
    );
}

#[test]
fn bridge_is_non_vacuous_fcvtzs() {
    let facts = load_facts();
    let mut found_disagreement = false;
    let mut count = 0usize;
    for fact in &facts {
        if fact.op != "fcvtzs_s_w" {
            continue;
        }
        count += 1;
        let wrong = wrong_fcvtzs(F32, 32, fact.operands[0]);
        let mask = (1u64 << fact.result_width) - 1;
        if (wrong & mask) != (fact.result & mask) {
            found_disagreement = true;
        }
    }
    assert!(count > 0, "non-vacuity: no fcvtzs_s_w facts");
    assert!(
        found_disagreement,
        "NON-VACUITY FAILURE: a deliberately-wrong FCVTZS (always 0) agreed with EVERY silicon \
         fact — the bridge would have no teeth"
    );
}

/// A wrong f32->f16 narrow that takes the high 16 bits of the f32 instead of the
/// RNE narrow — obviously wrong for the recorded 3.0 -> 0x4200 etc. This proves
/// the FP16 narrow (the model that REPLACES trust-cg's f64_to_fp16_bits) is
/// non-vacuously validated: a wrong model mismatches a real M4 fp16 fact.
fn wrong_fcvt_s_to_h(x: u64) -> u64 {
    (x >> 16) & 0xFFFF
}

/// A wrong fp16 FADD.h that ignores the second operand — wrong for 1.0+1.0=2.0.
fn wrong_fadd16(_f: FpFmt, a: u64, _b: u64) -> u64 {
    a
}

#[test]
fn bridge_is_non_vacuous_fp16_narrow() {
    let facts = load_facts();
    let mut found_disagreement = false;
    let mut count = 0usize;
    let mut correct_agrees = 0usize;
    for fact in &facts {
        if fact.op != "fcvt_s_to_h" {
            continue;
        }
        count += 1;
        if fcvt_s_to_h(fact.operands[0]) & 0xFFFF == fact.result & 0xFFFF {
            correct_agrees += 1;
        }
        if (wrong_fcvt_s_to_h(fact.operands[0]) & 0xFFFF) != (fact.result & 0xFFFF) {
            found_disagreement = true;
        }
    }
    assert!(count > 0, "non-vacuity: no fcvt_s_to_h fp16 facts");
    assert_eq!(
        correct_agrees, count,
        "non-vacuity precondition: the CORRECT FP16 narrow must agree with all {count} facts"
    );
    assert!(
        found_disagreement,
        "NON-VACUITY FAILURE: a deliberately-wrong f32->f16 narrow (high-16-bits) agreed with EVERY \
         silicon fp16 fact — the FP16 bridge would have no teeth (the bespoke model replacement \
         would be unvalidated)"
    );
}

#[test]
fn bridge_is_non_vacuous_fp16_add() {
    let facts = load_facts();
    let mut found_disagreement = false;
    let mut count = 0usize;
    for fact in &facts {
        if fact.op != "fadd16" {
            continue;
        }
        count += 1;
        let wrong = wrong_fadd16(F16, fact.operands[0], fact.operands[1]);
        if (wrong & 0xFFFF) != (fact.result & 0xFFFF) {
            found_disagreement = true;
        }
    }
    assert!(count > 0, "non-vacuity: no fadd16 fp16 facts");
    assert!(
        found_disagreement,
        "NON-VACUITY FAILURE: a deliberately-wrong FADD.h (identity in op0) agreed with EVERY \
         silicon fp16 fact — the FP16 arith bridge would have no teeth"
    );
}

/// A wrong FDIV that returns the dividend unchanged (drops the division entirely)
/// — wrong for the recorded 1.0/3.0 = 0x3eaaaaab, 6.0/2.0 = 3.0, etc. This proves
/// the integer-only long-division port is non-vacuously validated against silicon.
fn wrong_fdiv(_f: FpFmt, a: u64, _b: u64) -> u64 {
    a
}

/// A wrong FSQRT that returns the operand unchanged (drops the root) — wrong for
/// the recorded sqrt(4.0) = 2.0, sqrt(2.0) = 0x3fb504f3, etc.
fn wrong_fsqrt(_f: FpFmt, a: u64) -> u64 {
    a
}

#[test]
fn bridge_is_non_vacuous_fdiv() {
    let facts = load_facts();
    let mut found_disagreement = false;
    let mut correct_agrees = 0usize;
    let mut count = 0usize;
    for fact in &facts {
        if fact.op != "fdiv32" && fact.op != "fdiv64" {
            continue;
        }
        count += 1;
        let f = fmt_of(fact.in_widths[0]);
        let mask = if fact.result_width >= 64 {
            u64::MAX
        } else {
            (1u64 << fact.result_width) - 1
        };
        // correct model agrees:
        if (fdiv(f, fact.operands[0], fact.operands[1]) & mask) == (fact.result & mask) {
            correct_agrees += 1;
        }
        // wrong model (return dividend) disagrees somewhere:
        if (wrong_fdiv(f, fact.operands[0], fact.operands[1]) & mask) != (fact.result & mask) {
            found_disagreement = true;
        }
    }
    assert!(count > 0, "non-vacuity: no fdiv facts");
    assert_eq!(
        correct_agrees, count,
        "non-vacuity precondition: the CORRECT integer-only FDIV must agree with all {count} \
         silicon fdiv facts"
    );
    assert!(
        found_disagreement,
        "NON-VACUITY FAILURE: a deliberately-wrong FDIV (return dividend) agreed with EVERY \
         silicon fact — the FDIV bridge would have no teeth (the host-FPU-evicting port would \
         be unvalidated)"
    );
}

#[test]
fn bridge_is_non_vacuous_fsqrt() {
    let facts = load_facts();
    let mut found_disagreement = false;
    let mut correct_agrees = 0usize;
    let mut count = 0usize;
    for fact in &facts {
        if fact.op != "fsqrt32" && fact.op != "fsqrt64" {
            continue;
        }
        count += 1;
        let f = fmt_of(fact.in_widths[0]);
        let mask = if fact.result_width >= 64 {
            u64::MAX
        } else {
            (1u64 << fact.result_width) - 1
        };
        if (fsqrt(f, fact.operands[0]) & mask) == (fact.result & mask) {
            correct_agrees += 1;
        }
        if (wrong_fsqrt(f, fact.operands[0]) & mask) != (fact.result & mask) {
            found_disagreement = true;
        }
    }
    assert!(count > 0, "non-vacuity: no fsqrt facts");
    assert_eq!(
        correct_agrees, count,
        "non-vacuity precondition: the CORRECT integer-only FSQRT must agree with all {count} \
         silicon fsqrt facts"
    );
    assert!(
        found_disagreement,
        "NON-VACUITY FAILURE: a deliberately-wrong FSQRT (identity) agreed with EVERY silicon \
         fact — the FSQRT bridge would have no teeth"
    );
}

// ===========================================================================
// INTEGER-ONLY GATE — the bit-model SOURCE must contain NO f32/f64 arithmetic.
// This is the load-bearing property: the whole point is to evict the host FPU.
// A grep over the source asserts there is no float-typed arithmetic operator,
// float method (.sqrt/.round/.abs/...), or f32/f64 `as`-cast in fp_bitmodel.rs.
// ===========================================================================
#[test]
fn bitmodel_source_is_integer_only() {
    let src = include_str!("../src/fp_bitmodel.rs");
    // Strip line comments so doc text mentioning `f64` etc. doesn't trip the gate.
    let code: String = src
        .lines()
        .map(|l| match l.find("//") {
            Some(i) => &l[..i],
            None => l,
        })
        .collect::<Vec<_>>()
        .join("\n");

    // No float TYPE usage in code (no `: f32`, `f64::`, `as f32`, `as f64`,
    // `-> f32`, etc.). The model is entirely u32/u64/u128 + bool.
    for needle in [
        "f32",
        "f64", // any mention of a float type in code
        ".sqrt(",
        ".round(",
        ".round_ties_even(",
        ".floor(",
        ".ceil(",
        ".trunc(",
        ".to_bits(",
        ".from_bits(",
        ".is_nan(",
        ".is_infinite(",
        ".is_normal(",
    ] {
        assert!(
            !code.contains(needle),
            "INTEGER-ONLY GATE FAILED: fp_bitmodel.rs code contains `{needle}` — the bit-model \
             must use ONLY integer/bitwise ops (no host FPU in the FP-verification TCB)"
        );
    }
}

// ===========================================================================
// HOST-FPU DIFFERENTIAL FUZZ (#94 f32 stage). The host FPU is used here ONLY as
// a SECOND, INDEPENDENT oracle (legitimate in a TEST file — the integer-only
// grep gate forbids the host FPU inside the model file fp_bitmodel.rs, not here).
// This is the permanent, in-tree shrink of the 280M-input fuzz that drove the
// f32 host-FPU eviction: the integer-only bit-model arithmetic must be BIT-EXACT
// vs the host FPU at BOTH F32 and F64 for FADD/FSUB/FMUL/FDIV/FNEG/FABS/FSQRT.
// This is what makes the smt.rs f32/f64/fp16 guarded-swap SOUND, and it is the
// regression guard for the FADD/FSUB subtract-sticky BORROW fix (the bug that
// made the OR-after-subtract form 1 ULP too high in the cancellation path).
// ===========================================================================
#[test]
fn bitmodel_arith_is_bit_exact_vs_host_fpu() {
    let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut rng = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    let n = 150_000u64;
    // ---- F32 ----
    for _ in 0..n {
        let a = rng() as u32;
        let b = rng() as u32;
        let (fa, fb) = (f32::from_bits(a), f32::from_bits(b));
        for (name, nat, model) in [
            (
                "F32ADD",
                (fa + fb).to_bits(),
                fadd(F32, a as u64, b as u64) as u32,
            ),
            (
                "F32SUB",
                (fa - fb).to_bits(),
                fsub(F32, a as u64, b as u64) as u32,
            ),
            (
                "F32MUL",
                (fa * fb).to_bits(),
                fmul(F32, a as u64, b as u64) as u32,
            ),
            (
                "F32DIV",
                (fa / fb).to_bits(),
                fdiv(F32, a as u64, b as u64) as u32,
            ),
            ("F32NEG", (-fa).to_bits(), fneg(F32, a as u64) as u32),
            ("F32ABS", fa.abs().to_bits(), fabs(F32, a as u64) as u32),
            ("F32SQRT", fa.sqrt().to_bits(), fsqrt(F32, a as u64) as u32),
        ] {
            let nan_ok = f32::from_bits(nat).is_nan() && f32::from_bits(model).is_nan();
            assert!(
                nat == model || nan_ok,
                "{name} mismatch a={a:#010x} b={b:#010x} host={nat:#010x} model={model:#010x}"
            );
        }
    }
    // ---- F64 ----
    for _ in 0..n {
        let a = rng();
        let b = rng();
        let (fa, fb) = (f64::from_bits(a), f64::from_bits(b));
        for (name, nat, model) in [
            ("F64ADD", (fa + fb).to_bits(), fadd(F64, a, b)),
            ("F64SUB", (fa - fb).to_bits(), fsub(F64, a, b)),
            ("F64MUL", (fa * fb).to_bits(), fmul(F64, a, b)),
            ("F64DIV", (fa / fb).to_bits(), fdiv(F64, a, b)),
            ("F64NEG", (-fa).to_bits(), fneg(F64, a)),
            ("F64ABS", fa.abs().to_bits(), fabs(F64, a)),
            ("F64SQRT", fa.sqrt().to_bits(), fsqrt(F64, a)),
        ] {
            let nan_ok = f64::from_bits(nat).is_nan() && f64::from_bits(model).is_nan();
            assert!(
                nat == model || nan_ok,
                "{name} mismatch a={a:#018x} b={b:#018x} host={nat:#018x} model={model:#018x}"
            );
        }
    }
}

// The f32 host-FPU-eviction carrier round-trip: the smt.rs swap recovers the raw
// f32 bits from the f64 carrier via the INTEGER-ONLY fcvt_narrow (no `as f32`),
// runs the op at F32, and re-widens via fcvt_widen. For EVERY f32 value, the
// carrier (its exact f64 widening) must narrow back to the original f32 bits, so
// the swap path equals the native-f32 result. This pins the carrier invariant the
// f32 eviction relies on.
#[test]
fn f32_carrier_roundtrip_is_lossless() {
    let mut x: u64 = 0x1234_5678_9ABC_DEF0;
    let mut rng = || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for _ in 0..300_000 {
        let s = rng() as u32;
        let v = f32::from_bits(s);
        if v.is_nan() {
            continue; // NaN payload narrowing is op-specific; arithmetic covers it.
        }
        let carrier = (v as f64).to_bits(); // exact widening (what smt.rs stores)
        let recovered = fcvt_narrow(carrier) as u32; // integer-only narrow, no host FPU
        assert_eq!(
            recovered, s,
            "f32 carrier round-trip lost bits: s={s:#010x} recovered={recovered:#010x}"
        );
    }
}
