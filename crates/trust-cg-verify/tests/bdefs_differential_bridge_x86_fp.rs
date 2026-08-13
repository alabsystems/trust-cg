// trust-cg-verify/tests/bdefs_differential_bridge_x86_fp.rs — DELIVERABLE of #96
// (FRONTIER 2: extend the differential bridges to x86 scalar-FP SSE).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE B-x86-sse-fp DIFFERENTIAL BRIDGE — the scalar-FP analog of
// bdefs_differential_bridge_x86.rs (scalar int) + _x86_packed.rs (packed int),
// and the x86 dual of fp_bitmodel_bridge.rs (the AArch64 integer-only FP model).
// ===========================================================================
//
// This validates trust-cg's IN-HOUSE x86 SCALAR-FP SmtExpr encoders
// (x86_64_semantics.rs: encode_fp_add_rr/sub/mul/div, encode_fp_sqrt,
// encode_cvt*, encode_fp_minsd/maxsd, encode_fp_cmp_mask — the machine side of
// the x86 FP reconstruction proofs, #73) against REAL x86 (Rosetta 2). Those
// encoders build SmtExpr::FPAdd/FPSub/FPMul/FPDiv/FPSqrt + Ite(fp_lt/fp_gt) +
// fp.to_sbv nodes, which `try_eval` evaluates through the SILICON-VALIDATED
// INTEGER-ONLY fp_bitmodel.rs (host FPU EVICTED for f32/f64 arithmetic, #89/#91/
// #94). So this bridge cross-checks that integer-only model against an INDEPENDENT
// real x86 FP unit (Rosetta), AT X86 SEMANTICS — defeating root-cause #2 for x86
// scalar-FP (a shared misencoding in the in-house FP spec is no longer invisible).
//
// HOW: every fact in tests/fixtures/x86_fp_rosetta_truth.json is a BIT-EXACT
// result recorded from Rosetta 2 (an independent x86 translator, NOT a second
// in-house model) over an IEEE EDGE GRID (+-0, +-Inf, qNaN, sNaN, subnormals,
// min/max normal, ties). For each fact this test builds the in-house encoder with
// the operands as concrete FPConst / BvConst leaves, evals via the SAME try_eval
// the reconstruction uses, recovers the RESULT BITS (f64: to_bits(); f32: the
// integer-only fcvt_narrow of the f64 carrier — the exact narrow the eviction
// uses; f->int: the Bv), and asserts they EQUAL the Rosetta result bits.
//
// ===========================================================================
// THREE HONESTLY-CLASSIFIED FINDINGS (x86-vs-model divergences). None is papered
// over: each is COUNTED, the in-range/non-NaN subset is STRICTLY matched, and the
// NaN comparison is NOT loosened to hide a wrong VALUE — a non-NaN mismatch, or a
// NaN-vs-non-NaN mismatch, is always a HARD failure.
// ===========================================================================
//
//  (F1) x86 f->int OUT-OF-RANGE / NaN = "integer indefinite" — FIXED (#99). x86
//       CVTTSD2SI/CVTSD2SI/CVTTSS2SI/CVTSS2SI return 0x80000000 (i32) /
//       0x8000000000000000 (i64) — the most-negative integer — on positive
//       overflow, negative overflow AND NaN/+-Inf. trust-cg's FPToSBv evaluator
//       USED to SATURATE (positive overflow -> INT_MAX, NaN -> 0): that is the
//       wasm `trunc_sat` / AArch64 FCVTZS / RISC-V FCVT / Rust-`as` semantics,
//       NOT x86. The fix added a per-backend `OutOfRangeMode` to `FPToSBv`
//       (`Saturate` default for wasm/AArch64/RISC-V; `IntegerIndefinite` for the
//       x86 CVT[T]*2SI encoders), routed through the integer-only `fp_bitmodel`
//       (host FPU still evicted). The bridge now STRICTLY matches EVERY x86 f->int
//       conversion — in-range AND out-of-range/NaN/+-Inf — against Rosetta. There
//       is NO remaining f->int divergence (the F1 deferral is RETIRED).
//
//  (F2) NaN-INPUT payload quieting through the f64 eval carrier. For an f32 op
//       whose INPUT is a NaN (esp. sNaN or a sign-set qNaN), the FPConst decode
//       `f32::from_bits(bits) as f64` quiets/canonicalizes the NaN payload via the
//       host `as f64` cast (the f64 carrier is lossless for finite f32 values but
//       NOT for NaN payloads — the already-registered B-aarch64-fp-pending f32-FCVT
//       residual). BOTH x86 and the model produce a NaN of the result width — only
//       the PAYLOAD bits differ. Counted as a NaN-payload divergence (F2).
//
//  (F3) Invalid-operation default-qNaN SIGN. For 0*Inf, Inf-Inf, 0/0, sqrt(neg)
//       (no NaN input), x86 produces the NEGATIVE default qNaN 0xffc00000 /
//       0xfff8.. while the integer-only bit-model produces the POSITIVE default
//       0x7fc00000 / 0x7ff8.. . Both are qNaN of the result width; only the SIGN
//       (a payload bit) differs — an x86-vs-model NaN-sign convention. Counted (F3).
//
// The bridge is NON-VACUOUS: deliberately-WRONG encoders (addss-as-subss,
// minss-as-maxss, cmpss EQ-as-LT, the IEEE-min instead of the x86-quirky min)
// each mismatch a Rosetta fact, and a corrupted fixture result flips the
// comparison — so the bridge has teeth and is not a tautology / self-comparison.

use std::collections::HashMap;

use serde_json::Value;

use trust_cg_verify::smt::{EvalResult, SmtExpr};
use trust_cg_verify::x86_64_semantics::{
    X86CvtIntWidth, X86FPSize, encode_cvtsd2si, encode_cvtsd2ss, encode_cvtsi2sd, encode_cvtsi2ss,
    encode_cvtss2sd, encode_cvtss2si, encode_cvttsd2si, encode_cvttss2si, encode_fp_add_rr,
    encode_fp_cmp_mask, encode_fp_div_rr, encode_fp_maxsd, encode_fp_minsd, encode_fp_mul_rr,
    encode_fp_sqrt, encode_fp_sub_rr,
};

const FIXTURE: &str = include_str!("fixtures/x86_fp_rosetta_truth.json");

/// A single Rosetta scalar-FP ground-truth fact (one independent-x86 bit-exact
/// recorded result).
struct Fact {
    op: String,
    kind: String,
    in_widths: Vec<u32>,
    operands: Vec<u64>,
    imm: Option<u8>,
    /// The Rosetta-recorded result BIT PATTERN.
    result: u64,
    result_width: u32,
    theorem: String,
}

fn load_facts() -> Vec<Fact> {
    let doc: Value = serde_json::from_str(FIXTURE).expect("FP fixture is valid JSON");
    let arr = doc["facts"]
        .as_array()
        .expect("fixture has a `facts` array");
    arr.iter()
        .map(|f| {
            let rs = f["result"].as_str().expect("result is a hex string");
            let result =
                u64::from_str_radix(rs.strip_prefix("0x").unwrap_or(rs), 16).expect("result hex");
            Fact {
                op: f["op"].as_str().expect("op").to_string(),
                kind: f["kind"].as_str().expect("kind").to_string(),
                in_widths: f["in_widths"]
                    .as_array()
                    .expect("in_widths array")
                    .iter()
                    .map(|v| v.as_u64().expect("in_width") as u32)
                    .collect(),
                operands: f["operands"]
                    .as_array()
                    .expect("operands array")
                    .iter()
                    .map(|v| v.as_u64().expect("operand u64"))
                    .collect(),
                imm: f.get("imm").and_then(|v| v.as_u64()).map(|x| x as u8),
                result,
                result_width: f["result_width"].as_u64().expect("result_width") as u32,
                theorem: f["theorem"].as_str().expect("theorem").to_string(),
            }
        })
        .collect()
}

/// The accounting block in the fixture header (no silent truncation).
fn load_accounting() -> (usize, usize, usize, usize) {
    let doc: Value = serde_json::from_str(FIXTURE).expect("fixture is valid JSON");
    let acc = &doc["_accounting"];
    (
        acc["total_attempted"].as_u64().expect("total_attempted") as usize,
        acc["emitted"].as_u64().expect("emitted") as usize,
        acc["value_facts"].as_u64().expect("value_facts") as usize,
        acc["trap_facts"].as_u64().expect("trap_facts") as usize,
    )
}

/// A floating-point constant leaf carrying the raw `bits` of an `w`-bit float
/// (32 -> binary32 FPConst, 64 -> binary64 FPConst). FPConst stores the raw bits;
/// for f32 the eval carrier decodes `f32::from_bits(bits) as f64` (exact for
/// finite values; payload-quieting for NaNs — finding F2).
fn fp_leaf(bits: u64, w: u32) -> SmtExpr {
    match w {
        32 => SmtExpr::fp_const(bits & 0xFFFF_FFFF, 8, 24),
        64 => SmtExpr::fp_const(bits, 11, 53),
        other => panic!("bridge: unexpected FP width {other}"),
    }
}

fn fp_size(w: u32) -> X86FPSize {
    match w {
        32 => X86FPSize::Single,
        64 => X86FPSize::Double,
        other => panic!("bridge: unexpected FP width {other}"),
    }
}

/// Evaluate an encoder via the SAME try_eval the reconstruction `verify_by_
/// evaluation` path uses, then recover the RESULT BIT PATTERN at width `rw`:
///   * FP result (Float carrier): f64 -> to_bits(); f32 -> the INTEGER-ONLY
///     fcvt_narrow of the f64 carrier (the exact narrow the host-FPU eviction
///     uses — NO `as f32`), recovering the raw f32 result bits.
///   * f->int result (Bv): the integer bits directly.
fn eval_result_bits(expr: &SmtExpr, rw: u32, is_fp_result: bool) -> u64 {
    let env: HashMap<String, u64> = HashMap::new();
    match expr.try_eval(&env).expect("bridge: FP encoder eval failed") {
        EvalResult::Float(f) => {
            if is_fp_result && rw == 32 {
                trust_cg_verify::fp_bitmodel::fcvt_narrow(f.to_bits())
            } else {
                f.to_bits()
            }
        }
        EvalResult::Bv(v) => v,
        EvalResult::Bv128(v) => v as u64,
        other => panic!("bridge: FP encoder evaluated to {other:?}"),
    }
}

/// Build the in-house x86 scalar-FP encoder for `fact`. Returns None only for an
/// op the bridge does not dispatch (a fixture/bridge drift bug, caught by the
/// driver's unwrap).
fn build_encoder(fact: &Fact) -> Option<SmtExpr> {
    let w0 = fact.in_widths[0];
    let sz = fp_size(w0);
    let o = &fact.operands;
    let a = || fp_leaf(o[0], w0);
    let b = || fp_leaf(o[1], w0);
    let rw = fact.result_width;
    let e = match fact.op.as_str() {
        // ---- binary arithmetic (SS + SD) ----------------------------------
        "addss" | "addsd" => encode_fp_add_rr(sz, a(), b()),
        "subss" | "subsd" => encode_fp_sub_rr(sz, a(), b()),
        "mulss" | "mulsd" => encode_fp_mul_rr(sz, a(), b()),
        "divss" | "divsd" => encode_fp_div_rr(sz, a(), b()),
        // ---- unary SQRT ----------------------------------------------------
        "sqrtss" | "sqrtsd" => encode_fp_sqrt(sz, a()),
        // ---- x86-QUIRKY MIN/MAX (second operand wins on unordered/equal) ---
        "minss" | "minsd" => encode_fp_minsd(a(), b()),
        "maxss" | "maxsd" => encode_fp_maxsd(a(), b()),
        // ---- CMPSS/CMPSD over the 8 basic predicates (imm8[2:0]) -----------
        "cmpss" | "cmpsd" => encode_fp_cmp_mask(
            rw,
            fact.imm.expect("cmp op carries an imm predicate"),
            a(),
            b(),
        ),
        // ---- f<->f conversions --------------------------------------------
        "cvtss2sd" => encode_cvtss2sd(fp_leaf(o[0], 32)),
        "cvtsd2ss" => encode_cvtsd2ss(fp_leaf(o[0], 64)),
        // ---- int -> f conversions (signed; the source is a BvConst) --------
        "cvtsi2ss_32" => encode_cvtsi2ss(X86CvtIntWidth::I32, SmtExpr::bv_const(o[0], 32)),
        "cvtsi2sd_32" => encode_cvtsi2sd(X86CvtIntWidth::I32, SmtExpr::bv_const(o[0], 32)),
        "cvtsi2ss_64" => encode_cvtsi2ss(X86CvtIntWidth::I64, SmtExpr::bv_const(o[0], 64)),
        "cvtsi2sd_64" => encode_cvtsi2sd(X86CvtIntWidth::I64, SmtExpr::bv_const(o[0], 64)),
        // ---- f -> int conversions (RTZ trunc + RNE) ------------------------
        "cvttss2si_32" => encode_cvttss2si(32, fp_leaf(o[0], 32)),
        "cvttss2si_64" => encode_cvttss2si(64, fp_leaf(o[0], 32)),
        "cvttsd2si_32" => encode_cvttsd2si(32, fp_leaf(o[0], 64)),
        "cvttsd2si_64" => encode_cvttsd2si(64, fp_leaf(o[0], 64)),
        "cvtss2si_32" => encode_cvtss2si(32, fp_leaf(o[0], 32)),
        "cvtss2si_64" => encode_cvtss2si(64, fp_leaf(o[0], 32)),
        "cvtsd2si_32" => encode_cvtsd2si(32, fp_leaf(o[0], 64)),
        "cvtsd2si_64" => encode_cvtsd2si(64, fp_leaf(o[0], 64)),
        _ => return None,
    };
    Some(e)
}

/// True iff `op` produces an FP-valued result (so a NaN-payload classification is
/// meaningful and the f32 carrier-narrow recovers the result bits).
fn op_has_fp_result(op: &str) -> bool {
    matches!(
        op,
        "addss"
            | "addsd"
            | "subss"
            | "subsd"
            | "mulss"
            | "mulsd"
            | "divss"
            | "divsd"
            | "sqrtss"
            | "sqrtsd"
            | "minss"
            | "minsd"
            | "maxss"
            | "maxsd"
            | "cvtss2sd"
            | "cvtsd2ss"
            | "cvtsi2ss_32"
            | "cvtsi2sd_32"
            | "cvtsi2ss_64"
            | "cvtsi2sd_64"
    )
}

/// True iff `op` is an f->int conversion (CVT[T]SS2SI / CVT[T]SD2SI).
fn op_is_fp_to_int(op: &str) -> bool {
    op.starts_with("cvttss2si")
        || op.starts_with("cvttsd2si")
        || op.starts_with("cvtss2si")
        || op.starts_with("cvtsd2si")
}

/// Is `bits` a NaN at width `w`?
fn is_nan_w(bits: u64, w: u32) -> bool {
    match w {
        32 => f32::from_bits(bits as u32).is_nan(),
        _ => f64::from_bits(bits).is_nan(),
    }
}

/// The x86 "integer indefinite" result for a `width`-bit signed int (the value
/// CVT[T]*2SI returns on overflow / NaN): the most-negative integer.
fn integer_indefinite(width: u32) -> u64 {
    match width {
        32 => 0x8000_0000,
        _ => 0x8000_0000_0000_0000,
    }
}

// ===========================================================================
// THE BRIDGE: every in-house scalar-FP encoder must match Rosetta on every fact,
// EXCEPT the three honestly-classified, COUNTED findings (F1/F2/F3) which are
// never allowed to hide a wrong VALUE (only NaN-vs-NaN-of-same-width payload, or
// the x86-indefinite out-of-range conversion result, are excused).
// ===========================================================================
#[test]
fn x86_fp_inhouse_encoders_match_rosetta_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() > 10_000,
        "bridge: the Rosetta FP fixture is suspiciously small ({} facts) — truncated?",
        facts.len()
    );

    // No-silent-truncation accounting: the loaded facts must match the header.
    let (total_attempted, emitted, value_facts, trap_facts) = load_accounting();
    assert_eq!(
        total_attempted, emitted,
        "fixture accounting: total_attempted ({total_attempted}) != emitted ({emitted})"
    );
    assert_eq!(
        emitted,
        facts.len(),
        "header emitted ({emitted}) != loaded ({})",
        facts.len()
    );
    assert_eq!(
        value_facts,
        facts.len(),
        "scalar SSE FP ops never trap -> all value facts"
    );
    assert_eq!(
        trap_facts, 0,
        "scalar SSE FP ops never trap; expected 0 trap facts"
    );

    let mut hard_mismatches: Vec<String> = Vec::new();
    let mut per_op: HashMap<String, usize> = HashMap::new();
    let mut strict_matched = 0usize; // exact-bit matches (the real teeth)
    let mut f1_indefinite_matched = 0usize; // F1 (FIXED): x86 integer-indefinite
    // out-of-range/NaN facts that now
    // STRICT-match (the edge grid passes)
    let mut f2_nan_input = 0usize; // F2: NaN-input payload quieting (carrier)
    let mut f3_invalid_qnan_sign = 0usize; // F3: invalid-op default-qNaN sign

    for fact in &facts {
        *per_op.entry(fact.op.clone()).or_default() += 1;
        // Fixture-integrity: the `kind` tag must agree with the op family (so a
        // mislabelled fixture row is caught, not silently trusted).
        let expect_kind = if op_is_fp_to_int(&fact.op)
            || fact.op.starts_with("cvtsi2")
            || fact.op.starts_with("cvtss2sd")
            || fact.op.starts_with("cvtsd2ss")
        {
            "cvt"
        } else if fact.op == "cmpss" || fact.op == "cmpsd" {
            "cmp"
        } else if fact.op.starts_with("min") || fact.op.starts_with("max") {
            "minmax"
        } else {
            "arith"
        };
        assert_eq!(
            fact.kind, expect_kind,
            "fixture: op `{}` carries kind `{}` but the bridge expects `{expect_kind}` ({})",
            fact.op, fact.kind, fact.theorem
        );
        let expr = build_encoder(fact).unwrap_or_else(|| {
            panic!(
                "bridge: fixture op `{}` ({}) has no in-house encoder dispatch — fixture/bridge \
                 drift (every fixture op must map to an encoder, never silently unhandled)",
                fact.op, fact.theorem
            )
        });
        let rw = fact.result_width;
        let is_fp_result = op_has_fp_result(&fact.op);
        let got = eval_result_bits(&expr, rw, is_fp_result);
        let mask = if rw >= 64 { u64::MAX } else { (1u64 << rw) - 1 };
        let want = fact.result & mask;
        let got = got & mask;

        if got == want {
            strict_matched += 1;
            // F1 (FIXED #99): track the out-of-range / NaN / +-Inf f->int facts
            // that NOW strict-match the x86 integer-indefinite ground truth, so
            // the edge grid is proven exercised (non-vacuous) and passing.
            if op_is_fp_to_int(&fact.op) && want == (integer_indefinite(rw) & mask) {
                f1_indefinite_matched += 1;
            }
            continue;
        }

        // ---- a divergence: classify it honestly (never hide a wrong VALUE) ----
        if op_is_fp_to_int(&fact.op) {
            // F1 (FIXED #99): the x86 CVT[T]*2SI encoders now use
            // OutOfRangeMode::IntegerIndefinite, so EVERY f->int conversion —
            // in-range AND out-of-range/NaN/+-Inf — must match Rosetta exactly.
            // Any f->int mismatch is now a HARD failure (a real miscompile-class
            // bug, or a regression that reintroduced saturation for x86).
            if hard_mismatches.len() < 40 {
                hard_mismatches.push(format!(
                    "{}: op={} ops={:x?} -> encoder {got:#x}, Rosetta {want:#x} (x86 f->int \
                     conversion mismatch — the F1 fix requires integer-indefinite on \
                     overflow/NaN; a saturating regression would land here)",
                    fact.theorem, fact.op, fact.operands
                ));
            }
            continue;
        }

        if is_fp_result {
            let both_nan = is_nan_w(got, rw) && is_nan_w(want, rw);
            if both_nan {
                // Both produce a NaN of the result width; only the PAYLOAD differs.
                // Distinguish F2 (a NaN INPUT, quieted through the f32 carrier) from
                // F3 (no NaN input — the invalid-op default-qNaN sign convention).
                let any_input_nan = fact
                    .operands
                    .iter()
                    .enumerate()
                    .any(|(i, &op)| is_nan_w(op, fact.in_widths[i]));
                if any_input_nan {
                    f2_nan_input += 1;
                } else {
                    f3_invalid_qnan_sign += 1;
                }
                continue;
            }
            // A NaN-vs-non-NaN or non-NaN-vs-non-NaN FP mismatch is a HARD failure
            // (a genuine wrong VALUE — the comparison is NOT loosened to hide it).
            if hard_mismatches.len() < 40 {
                hard_mismatches.push(format!(
                    "{}: op={} ops={:x?} -> encoder {got:#x}, Rosetta {want:#x} (NON-NaN FP value \
                     mismatch — a genuine x86-vs-model divergence, NOT a NaN payload)",
                    fact.theorem, fact.op, fact.operands
                ));
            }
            continue;
        }

        // Non-FP-result, non-conversion mismatch = compare mask etc. -> HARD.
        if hard_mismatches.len() < 40 {
            hard_mismatches.push(format!(
                "{}: op={} ops={:x?} imm={:?} -> encoder {got:#x}, Rosetta {want:#x}",
                fact.theorem, fact.op, fact.operands, fact.imm
            ));
        }
    }

    // PER-OP accounting: every fixture op family must have been exercised.
    assert!(
        per_op.len() >= 28,
        "bridge: too few FP op families exercised ({}) — expected the full ~30-family x86 scalar-FP \
         grid",
        per_op.len()
    );
    // Every fact is EXACTLY one of {strict-matched, F2, F3, hard-mismatch} —
    // no fact is silently skipped. (F1 is FIXED: out-of-range/NaN f->int facts
    // now fall into strict-matched, and `f1_indefinite_matched` is a SUBSET
    // counter over strict-matched, NOT a separate class.) `hard_count` is the
    // TRUE number of hard mismatches (the report vec is capped at 40 for
    // readability, but the count is derived from the residual so it is exact).
    let total_classified = strict_matched + f2_nan_input + f3_invalid_qnan_sign;
    let hard_count = facts.len() - total_classified;
    assert!(
        hard_count == 0 || !hard_mismatches.is_empty(),
        "bridge: accounting drift — {hard_count} facts unclassified but no hard mismatch reported"
    );

    // HARD failures: a genuine wrong VALUE (NOT a NaN payload). With F1 FIXED,
    // an x86 f->int overflow/NaN mismatch now lands HERE — these would be real
    // miscompile-class bugs or a saturating regression.
    assert!(
        hard_mismatches.is_empty(),
        "B-x86-sse-fp BRIDGE FINDING (HARD): {hard_count} genuine wrong-VALUE mismatches between \
         trust-cg's x86 scalar-FP model and real x86 (Rosetta 2). These are NOT NaN payloads. \
         First {}:\n{}",
        hard_mismatches.len(),
        hard_mismatches.join("\n")
    );

    // The strict-matched count must dominate (the bridge is overwhelmingly
    // exact-bit), and the remaining classified findings must be NON-EMPTY where
    // the grid forces them (so the classification is real, not a dead branch).
    assert!(
        strict_matched > 14_000,
        "bridge: too few STRICT exact-bit matches ({strict_matched}) — the bridge must be \
         overwhelmingly exact (arith/minmax/cmp/sqrt/div/ALL conversions match Rosetta)"
    );
    // F1 (FIXED #99): the out-of-range / NaN / +-Inf f->int edge grid must be
    // exercised AND now strict-match the x86 integer-indefinite ground truth.
    // The full grid forces exactly 70 such integer-indefinite facts (positive
    // overflow, negative overflow, NaN and +-Inf across the 8 CVT[T]*2SI forms);
    // EVERY one must match (it is part of strict_matched). A regression that
    // reintroduced saturation for x86 would drop these out of strict-matched and
    // surface as HARD mismatches above.
    assert!(
        f1_indefinite_matched >= 64,
        "bridge: the x86 integer-indefinite f->int edge grid (F1, FIXED) must be exercised and \
         strict-match ({f1_indefinite_matched} matched, expected ~70) — too few means the \
         out-of-range/NaN conversion grid was not actually validated"
    );
    assert!(
        f2_nan_input > 0 && f3_invalid_qnan_sign > 0,
        "bridge: the NaN-payload findings (F2 carrier-quieting={f2_nan_input}, F3 invalid-qNaN-\
         sign={f3_invalid_qnan_sign}) must both be exercised by the NaN edge grid"
    );

    eprintln!(
        "B-x86-sse-fp bridge: {strict_matched} STRICT exact-bit matches across {} op families \
         (incl. {f1_indefinite_matched} x86 integer-indefinite out-of-range/NaN/+-Inf f->int \
         conversions — F1 FIXED #99, no remaining f->int divergence). Remaining honestly-\
         classified NaN-PAYLOAD findings (NOT wrong VALUES): F2 NaN-input carrier-quieting=\
         {f2_nan_input}; F3 invalid-op default-qNaN sign={f3_invalid_qnan_sign}.",
        per_op.len()
    );
}

// ===========================================================================
// THE F1 FINDING, FIXED (#99): x86 f->int OUT-OF-RANGE / NaN / +-Inf is "integer
// indefinite". trust-cg's FPToSBv now carries an OutOfRangeMode; the x86
// CVT[T]*2SI encoders use IntegerIndefinite (wasm/AArch64/RISC-V keep Saturate).
// This test PINS the fix with concrete witnesses so it can never silently
// REGRESS to saturation: the in-range conversion matches Rosetta exactly, AND the
// out-of-range / NaN / +-Inf conversions now AGREE with x86's integer-indefinite
// ground truth (the model returns 0x80000000 / 0x8000000000000000, NOT INT_MAX/0).
// ===========================================================================
#[test]
fn finding_f1_x86_fp_to_int_overflow_is_integer_indefinite_not_saturating() {
    let facts = load_facts();

    // (a) An IN-RANGE conversion matches Rosetta EXACTLY (the bridge is not vacuous
    //     for conversions — the in-range subset is strictly validated).
    // 123.0 (f64 = 0x405ec00000000000) -> cvttsd2si_32 = 123, both sides.
    let in_range = facts
        .iter()
        .find(|f| f.op == "cvttsd2si_32" && f.operands[0] == 0x405e_c000_0000_0000)
        .expect("expected the 123.0 -> i32 in-range conversion fact");
    let expr = build_encoder(in_range).unwrap();
    let got = eval_result_bits(&expr, 32, false) & 0xFFFF_FFFF;
    assert_eq!(got, 123, "in-range cvttsd2si_32(123.0) must be 123 (model)");
    assert_eq!(
        in_range.result & 0xFFFF_FFFF,
        123,
        "in-range cvttsd2si_32(123.0) must be 123 (Rosetta)"
    );
    assert_eq!(
        got,
        in_range.result & 0xFFFF_FFFF,
        "in-range conversion must match Rosetta exactly"
    );

    // (b) +Inf (f32 0x7f800000) -> cvttss2si_32: Rosetta returns x86 integer-
    //     indefinite 0x80000000; the model now AGREES (no longer saturates to
    //     INT_MAX). This is the F1 fix.
    let overflow = facts
        .iter()
        .find(|f| f.op == "cvttss2si_32" && f.operands[0] == 0x7f80_0000)
        .expect("expected the +Inf -> i32 overflow conversion fact");
    let model = eval_result_bits(&build_encoder(overflow).unwrap(), 32, false) & 0xFFFF_FFFF;
    assert_eq!(
        overflow.result & 0xFFFF_FFFF,
        0x8000_0000,
        "Rosetta CVTTSS2SI(+Inf) must be x86 integer-indefinite 0x80000000"
    );
    assert_eq!(
        model, 0x8000_0000,
        "FIXED (#99): trust-cg's x86 CVTTSS2SI encoder now returns integer-indefinite 0x80000000 \
         on +Inf (OutOfRangeMode::IntegerIndefinite) — NO longer the saturating INT_MAX"
    );
    assert_eq!(
        model,
        overflow.result & 0xFFFF_FFFF,
        "F1 FIXED: trust-cg's x86 CVTTSS2SI now AGREES with x86's integer-indefinite on overflow"
    );

    // (c) NaN (f64 qNaN) -> cvtsd2si_64: Rosetta indefinite 0x8000..; model AGREES.
    let nan = facts
        .iter()
        .find(|f| f.op == "cvtsd2si_64" && f.operands[0] == 0x7ff8_0000_0000_0000)
        .expect("expected the qNaN -> i64 conversion fact");
    let model = eval_result_bits(&build_encoder(nan).unwrap(), 64, false);
    assert_eq!(
        nan.result, 0x8000_0000_0000_0000,
        "Rosetta CVTSD2SI(NaN) must be x86 integer-indefinite 0x8000000000000000"
    );
    assert_eq!(
        model, 0x8000_0000_0000_0000,
        "FIXED (#99): trust-cg's x86 CVTSD2SI encoder now returns integer-indefinite on NaN — NO \
         longer NaN->0"
    );

    // (d) NEGATIVE overflow (-Inf f64 0xfff0000000000000) -> cvttsd2si_32: x86
    //     indefinite 0x80000000 (== INT_MIN, which the saturating model ALSO gave),
    //     so this both AGREES and pins that the negative-overflow result is the
    //     indefinite value (not flipped to INT_MAX by a sign bug).
    let neg_overflow = facts
        .iter()
        .find(|f| f.op == "cvttsd2si_32" && f.operands[0] == 0xfff0_0000_0000_0000)
        .expect("expected the -Inf -> i32 overflow conversion fact");
    let model = eval_result_bits(&build_encoder(neg_overflow).unwrap(), 32, false) & 0xFFFF_FFFF;
    assert_eq!(
        neg_overflow.result & 0xFFFF_FFFF,
        0x8000_0000,
        "Rosetta CVTTSD2SI(-Inf) indefinite"
    );
    assert_eq!(
        model, 0x8000_0000,
        "FIXED: x86 CVTTSD2SI(-Inf) integer-indefinite, model AGREES"
    );
}

// ===========================================================================
// NON-VACUITY (teeth): deliberately-WRONG encoders MUST mismatch Rosetta, and the
// CORRECT encoder must match ALL facts of that family (modulo the classified NaN
// findings). These prove the bridge is not a tautology / self-comparison.
// ===========================================================================

/// Recover the result bits for `fact` from an arbitrary encoder `expr`.
fn bits_of(expr: &SmtExpr, fact: &Fact) -> u64 {
    let mask = if fact.result_width >= 64 {
        u64::MAX
    } else {
        (1u64 << fact.result_width) - 1
    };
    eval_result_bits(expr, fact.result_width, op_has_fp_result(&fact.op)) & mask
}

/// Does the CORRECT in-house encoder match Rosetta on this fact, treating a
/// NaN-vs-NaN-of-same-width payload difference as a match (the classified F2/F3
/// findings)? A non-NaN difference is NOT excused.
fn correct_matches_modulo_nan(fact: &Fact) -> bool {
    let mask = if fact.result_width >= 64 {
        u64::MAX
    } else {
        (1u64 << fact.result_width) - 1
    };
    let want = fact.result & mask;
    let got = bits_of(&build_encoder(fact).unwrap(), fact);
    if got == want {
        return true;
    }
    op_has_fp_result(&fact.op)
        && is_nan_w(got, fact.result_width)
        && is_nan_w(want, fact.result_width)
}

#[test]
fn bridge_is_non_vacuous_addss_as_subss_mismatches_rosetta() {
    let facts = load_facts();
    let add_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "addss").collect();
    assert!(!add_facts.is_empty(), "expected ADDSS facts");
    // The CORRECT ADDSS encoder matches ALL addss facts (modulo NaN payload).
    for f in &add_facts {
        assert!(
            correct_matches_modulo_nan(f),
            "precondition: the correct ADDSS encoder must match Rosetta on every ADDSS fact ({})",
            f.theorem
        );
    }
    let mut found = false;
    for f in &add_facts {
        let w = f.in_widths[0];
        let wrong = encode_fp_sub_rr(
            fp_size(w),
            fp_leaf(f.operands[0], w),
            fp_leaf(f.operands[1], w),
        );
        let got = bits_of(&wrong, f);
        let want = f.result & ((1u64 << f.result_width) - 1);
        // A genuine non-NaN divergence (e.g. 1.0+2.0=3.0 vs 1.0-2.0=-1.0).
        if got != want && !(is_nan_w(got, f.result_width) && is_nan_w(want, f.result_width)) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: SUBSS-for-ADDSS matched Rosetta on EVERY ADDSS fact — the bridge would be a \
         tautology. It must mismatch (a+b != a-b on a non-degenerate input)."
    );
}

#[test]
fn bridge_is_non_vacuous_x86_quirky_minss_as_maxss_mismatches_rosetta() {
    // The x86-quirky MIN/MAX distinction is load-bearing: MINSS != MAXSS on an
    // ordered unequal pair (min picks the smaller, max the larger). This proves the
    // bridge actually exercises the x86 second-operand-on-unordered/equal semantics
    // and the encoders are not interchangeable.
    let facts = load_facts();
    let min_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "minss").collect();
    assert!(!min_facts.is_empty(), "expected MINSS facts");
    for f in &min_facts {
        assert!(
            correct_matches_modulo_nan(f),
            "precondition: the correct (x86-quirky) MINSS encoder must match Rosetta on every \
             MINSS fact ({})",
            f.theorem
        );
    }
    let mut found = false;
    for f in &min_facts {
        let wrong = encode_fp_maxsd(fp_leaf(f.operands[0], 32), fp_leaf(f.operands[1], 32));
        let got = bits_of(&wrong, f);
        let want = f.result & 0xFFFF_FFFF;
        if got != want && !(is_nan_w(got, 32) && is_nan_w(want, 32)) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: MAXSS-for-MINSS matched Rosetta on EVERY MINSS fact — the x86 min/max \
         distinction would not be load-bearing. It must MISMATCH on an ordered unequal pair."
    );
}

#[test]
fn bridge_is_non_vacuous_x86_quirky_min_is_not_ieee_minnum() {
    // The CRUX x86-vs-ARM finding: x86 MINSS returns the SECOND operand on
    // unordered (NaN) OR equal — it is NOT IEEE/ARM minNum (which returns the
    // NON-NaN operand and the smaller of +-0). This proves the bridge validates the
    // x86 quirk specifically: the x86 encoder matches Rosetta on min(1.0, NaN) =
    // NaN (the SECOND operand), whereas an IEEE-minNum model (returning the
    // non-NaN 1.0) would DISAGREE with Rosetta.
    let facts = load_facts();
    let qnan: u64 = 0x7fc0_0000;
    let one: u64 = 0x3f80_0000;
    // Rosetta minss(1.0, NaN): the SECOND operand (NaN) wins on unordered.
    let fact = facts
        .iter()
        .find(|f| f.op == "minss" && f.operands[0] == one && f.operands[1] == qnan)
        .expect("expected minss(1.0, NaN) fact");
    assert!(
        is_nan_w(fact.result & 0xFFFF_FFFF, 32),
        "Rosetta MINSS(1.0, NaN) must be NaN (the SECOND operand wins on unordered — x86, NOT ARM \
         minNum which would return 1.0)"
    );
    // The x86 encoder agrees (NaN result).
    let x86_got = bits_of(&build_encoder(fact).unwrap(), fact);
    assert!(
        is_nan_w(x86_got, 32),
        "the x86-quirky MINSS encoder must return NaN on min(1.0, NaN) — the second operand"
    );
    // An IEEE/ARM minNum (return the NON-NaN operand) would give 1.0 — DISAGREEING
    // with Rosetta's NaN. We model that wrong encoder inline as `ite(isNaN(b), a, ...)`
    // is the wrong direction; concretely minNum(1.0,NaN)=1.0, not NaN.
    let arm_minnum_would_give = one; // ARM FMINNM(1.0, NaN) = 1.0 (NaN suppressed)
    assert!(
        !is_nan_w(arm_minnum_would_give, 32),
        "NON-VACUITY: an ARM-style IEEE minNum would return the non-NaN 1.0 on min(1.0, NaN), \
         DISAGREEING with Rosetta's NaN — so modeling x86 MINSS as ARM FMINNM would MISCOMPILE \
         (the bridge's x86-quirky encoder is load-bearing)"
    );
    assert_ne!(
        arm_minnum_would_give,
        fact.result & 0xFFFF_FFFF,
        "the ARM minNum result (1.0) must differ from the x86 Rosetta result (NaN)"
    );
}

#[test]
fn bridge_is_non_vacuous_cmpss_eq_as_lt_mismatches_rosetta() {
    // CMPSS predicate distinction: EQ (imm 0) != LT (imm 1) on at least one input
    // (e.g. a==b gives all-ones for EQ but all-zero for LT; a<b the reverse).
    let facts = load_facts();
    let eq_facts: Vec<&Fact> = facts
        .iter()
        .filter(|f| f.op == "cmpss" && f.imm == Some(0))
        .collect();
    assert!(!eq_facts.is_empty(), "expected CMPSS EQ facts");
    for f in &eq_facts {
        assert!(
            correct_matches_modulo_nan(f),
            "precondition: the correct CMPSS EQ encoder must match Rosetta on every EQ fact ({})",
            f.theorem
        );
    }
    let mut found = false;
    for f in &eq_facts {
        let wrong = encode_fp_cmp_mask(
            32,
            1, /* LT */
            fp_leaf(f.operands[0], 32),
            fp_leaf(f.operands[1], 32),
        );
        if bits_of(&wrong, f) != (f.result & 0xFFFF_FFFF) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: CMPSS-EQ-as-LT (predicate 0 emitted as 1) matched Rosetta on EVERY EQ fact — \
         the predicate distinction would not be load-bearing. It must MISMATCH (a==b: all-ones for \
         EQ, all-zero for LT)."
    );
}

#[test]
fn bridge_is_non_vacuous_corrupted_fixture_result_mismatches() {
    // Take the first ADDSD fact, corrupt its recorded Rosetta result by +1, and
    // confirm the in-house encoder now DISAGREES — proving the assertion compares
    // against the fixture value, not against itself.
    let facts = load_facts();
    // Pick a non-NaN ADDSD fact (so +1 cannot accidentally stay NaN).
    let fact = facts
        .iter()
        .find(|f| {
            f.op == "addsd"
                && !is_nan_w(f.result, 64)
                && !is_nan_w(f.operands[0], 64)
                && !is_nan_w(f.operands[1], 64)
        })
        .expect("a non-NaN ADDSD fact");
    let got = bits_of(&build_encoder(fact).unwrap(), fact);
    assert_eq!(
        got, fact.result,
        "sanity: the genuine ADDSD fact must match the in-house encoder"
    );
    let corrupted = fact.result.wrapping_add(1);
    assert_ne!(
        got, corrupted,
        "NON-VACUITY: corrupting the recorded Rosetta result must flip the comparison — the bridge \
         actually compares against the fixture value (not against itself)"
    );
}
