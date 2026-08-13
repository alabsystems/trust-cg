// trust-cg-verify/tests/bdefs_differential_bridge.rs — DELIVERABLE of task #81.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE B-aarch64-int DIFFERENTIAL BRIDGE.
// ===========================================================================
//
// This is the machine-side dual of the B-defs Clean model: it defeats
// root-cause #2 of the lowering-equivalence TCB — that BOTH sides of every
// reconstruction check are validated against ONE in-house machine spec
// (trust-cg-verify/src/aarch64_semantics.rs, the SmtExpr encoders), so a SHARED
// misencoding in that spec is INVISIBLE to the equivalence check.
//
// HOW IT DEFEATS THAT: every fact in tests/fixtures/aarch64_silicon_truth.json
// is a result recorded from a REAL Apple M4 Pro (an `:= rfl` chip theorem in
// the sibling Clean tree's proofs/aarch64_isa_chip.lean — the HARDWARE oracle,
// strictly stronger than any second software model). For each fact this test:
//
//   1. takes the op + the silicon operand hex literals,
//   2. constructs trust-cg's OWN in-house AArch64 MACHINE encoder for that op
//      (the SAME encoders the reconstruction machine side uses — see
//      function_verifier.rs: encode_add_rr/.../encode_lsl_rr_masked/...),
//      with the operands as concrete SmtExpr::bv_const leaves,
//   3. evaluates it through the SAME SmtExpr `try_eval` evaluator the
//      reconstruction `verify_by_evaluation` path uses, and
//   4. asserts the EVALUATED result EQUALS the SILICON-recorded result.
//
// A mismatch is a FINDING (a latent miscompile-class bug, or a convention
// divergence). It is NOT papered over by excluding the op or loosening the
// comparison. The bridge is NON-VACUOUS: `bridge_is_non_vacuous_*` below prove
// a deliberately-WRONG encoder mismatches a silicon fact (so the bridge has
// teeth — it is not a tautology and not a self-comparison).
//
// CONVENTIONS (exactly where mismatches surface — all validated here):
//   * SHIFTS use the FAITHFUL amount-MASKED encoders (encode_lsl_rr_masked etc.,
//     amount & (width-1)) — NOT the plain SMT bvshl whose evaluator CLAMPS to 0
//     at amount >= width. The masked encoder matches silicon's &63/&31 (#57).
//   * AArch64 SDIV/UDIV return 0 on divisor==0 (NO trap; DISTINCT from x86 IDIV
//     #DE) and SDIV INT_MIN/-1 = INT_MIN (no trap). The SmtExpr BvSDiv/BvUDiv
//     evaluator yields exactly those, so the raw encoders match silicon.
//   * W-forms: operands are read as their low 32 bits and the result is the
//     low-32 value (upper 32 of Xd zeroed). Encoded by exercising the SAME
//     width-polymorphic encoders at 32-bit width.
//   * MADD/MSUB: Rd = Ra ± Rn*Rm. The Lean chip def is `bvMadd a n m = a+n*m`
//     (a is the addend Ra); the encoder is encode_madd_rr(size, rn, rm, ra), so
//     the fact's [a, n, m] map to ra=a, rn=n, rm=m (matches function_verifier).
//   * UBFM/SBFM (EXTRACT regime, imms>=immr): lsb=immr, width=imms-immr+1.

use std::collections::HashMap;

use serde_json::Value;

use trust_cg_ir::cc::OperandSize;
use trust_cg_verify::aarch64_semantics::{
    encode_add_rr, encode_and_rr, encode_asr_rr_masked, encode_bic_rr, encode_eor_rr,
    encode_lsl_rr_masked, encode_lsr_rr_masked, encode_madd_rr, encode_msub_rr, encode_mul_rr,
    encode_mvn, encode_neg, encode_orn_rr, encode_orr_rr, encode_sbfm_extract, encode_sdiv_rr,
    encode_sub_rr, encode_ubfm_extract, encode_udiv_rr,
};
use trust_cg_verify::smt::{EvalResult, SmtExpr};

const FIXTURE: &str = include_str!("fixtures/aarch64_silicon_truth.json");

/// A single silicon ground-truth fact (one chip `:= rfl` theorem).
struct Fact {
    op: String,
    width: u32,
    operands: Vec<u64>,
    result: u64,
    theorem: String,
}

fn load_facts() -> Vec<Fact> {
    let doc: Value = serde_json::from_str(FIXTURE).expect("fixture is valid JSON");
    let arr = doc["facts"]
        .as_array()
        .expect("fixture has a `facts` array");
    arr.iter()
        .map(|f| Fact {
            op: f["op"].as_str().expect("op is a string").to_string(),
            width: f["width"].as_u64().expect("width is a number") as u32,
            operands: f["operands"]
                .as_array()
                .expect("operands is an array")
                .iter()
                .map(|v| v.as_u64().expect("operand is a u64 (full 64-bit literal)"))
                .collect(),
            result: f["result"].as_u64().expect("result is a u64"),
            theorem: f["theorem"]
                .as_str()
                .expect("theorem is a string")
                .to_string(),
        })
        .collect()
}

/// A `width`-bit constant leaf carrying the low `width` bits of `v`.
///
/// For W-forms (width==32) this is exactly the W-register read semantics: the
/// machine sees only the low 32 bits of the source register. `bv_const` masks
/// the value to `width`, so passing the full 64-bit silicon operand is correct.
fn leaf(v: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(v, width)
}

fn size_of(width: u32) -> OperandSize {
    match width {
        32 => OperandSize::S32,
        64 => OperandSize::S64,
        other => panic!("bridge: unexpected width {other}"),
    }
}

/// Build the trust-cg IN-HOUSE encoder SmtExpr for `fact`. Returns `None` for an
/// op tag the bridge does not encode (should never happen — the fixture only
/// contains in-house-encoded ops; an unknown tag is a fixture/bridge drift bug).
fn build_encoder(fact: &Fact) -> Option<SmtExpr> {
    let w = fact.width;
    let sz = size_of(w);
    let ops = &fact.operands;
    let l = |i: usize| leaf(ops[i], w);
    let e = match fact.op.as_str() {
        // ---- arithmetic / logic (X and W share the width-polymorphic encoder) -
        "add" | "addw" => encode_add_rr(sz, l(0), l(1)),
        "sub" | "subw" => encode_sub_rr(sz, l(0), l(1)),
        "mul" | "mulw" => encode_mul_rr(sz, l(0), l(1)),
        "and" | "andw" => encode_and_rr(sz, l(0), l(1)),
        "orr" | "orrw" => encode_orr_rr(sz, l(0), l(1)),
        "eor" | "eorw" => encode_eor_rr(sz, l(0), l(1)),
        "bic" => encode_bic_rr(sz, l(0), l(1)),
        "orn" => encode_orn_rr(sz, l(0), l(1)),
        "mvn" | "mvnw" => encode_mvn(sz, l(0)),
        "neg" | "negw" => encode_neg(sz, l(0)),
        // ---- shifts: FAITHFUL amount-masked encoders (the #57 fix) -----------
        "lsl" | "lslw" => encode_lsl_rr_masked(sz, l(0), l(1)),
        "lsr" | "lsrw" => encode_lsr_rr_masked(sz, l(0), l(1)),
        "asr" | "asrw" => encode_asr_rr_masked(sz, l(0), l(1)),
        // ---- multiply-accumulate: fact [a, n, m] -> ra=a, rn=n, rm=m ---------
        "madd" | "maddw" => encode_madd_rr(sz, l(1), l(2), l(0)),
        "msub" | "msubw" => encode_msub_rr(sz, l(1), l(2), l(0)),
        // ---- division: no-trap AArch64 semantics (div0=0, INT_MIN/-1=INT_MIN)-
        "sdiv" | "sdivw" => encode_sdiv_rr(sz, l(0), l(1)),
        "udiv" | "udivw" => encode_udiv_rr(sz, l(0), l(1)),
        // ---- bitfield EXTRACT (imms >= immr): lsb=immr, width=imms-immr+1 ----
        "ubfm" | "ubfmw" => {
            let immr = ops[1] as u32;
            let imms = ops[2] as u32;
            encode_ubfm_extract(l(0), immr, imms - immr + 1, w)
        }
        "sbfm" | "sbfmw" => {
            let immr = ops[1] as u32;
            let imms = ops[2] as u32;
            encode_sbfm_extract(l(0), immr, imms - immr + 1, w)
        }
        _ => return None,
    };
    Some(e)
}

/// Evaluate an encoder expression to a concrete value (the SAME `try_eval`
/// evaluator the reconstruction `verify_by_evaluation` path uses).
fn eval(expr: &SmtExpr) -> u64 {
    let env: HashMap<String, u64> = HashMap::new();
    match expr.try_eval(&env) {
        Ok(EvalResult::Bv(v)) => v,
        Ok(EvalResult::Bv128(v)) => v as u64,
        Ok(other) => panic!("bridge: encoder evaluated to non-bitvector {other:?}"),
        Err(e) => panic!("bridge: encoder eval failed: {e:?}"),
    }
}

// ===========================================================================
// THE BRIDGE: every in-house encoder must match silicon on every chip fact.
// ===========================================================================
#[test]
fn aarch64_inhouse_encoders_match_silicon_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() > 30_000,
        "bridge: the silicon fixture is suspiciously small ({} facts) — did the \
         fixture get truncated?",
        facts.len()
    );

    let mut mismatches: Vec<String> = Vec::new();
    let mut checked = 0usize;
    let mut per_op: HashMap<String, usize> = HashMap::new();

    for fact in &facts {
        let expr = build_encoder(fact).unwrap_or_else(|| {
            panic!(
                "bridge: fixture op `{}` ({}) has no in-house encoder dispatch — the \
                 fixture and the bridge have drifted (a fixture op must map to an encoder \
                 or be EXCLUDED in the generator, never silently unhandled)",
                fact.op, fact.theorem
            )
        });
        let got = eval(&expr);
        checked += 1;
        *per_op.entry(fact.op.clone()).or_default() += 1;
        if got != fact.result {
            // Report the FIRST few mismatches in full (a mismatch is a FINDING).
            if mismatches.len() < 40 {
                mismatches.push(format!(
                    "{}: op={} width={} operands={:?} -> in-house encoder gave {:#x} ({}), \
                     silicon recorded {:#x} ({})",
                    fact.theorem,
                    fact.op,
                    fact.width,
                    fact.operands,
                    got,
                    got,
                    fact.result,
                    fact.result
                ));
            }
        }
    }

    // Every op family in the fixture must actually have been exercised.
    assert!(
        per_op.len() >= 30,
        "bridge: too few op families exercised ({})",
        per_op.len()
    );

    assert!(
        mismatches.is_empty(),
        "B-aarch64-int BRIDGE FINDING: {} of {} in-house-encoder vs silicon comparisons \
         MISMATCH. Each is a latent miscompile-class divergence between trust-cg's AArch64 \
         model and the real Apple M4 Pro. First mismatches:\n{}",
        mismatches.len(),
        checked,
        mismatches.join("\n")
    );

    eprintln!(
        "B-aarch64-int bridge: {checked} in-house-encoder vs silicon comparisons PASS \
         across {} op families.",
        per_op.len()
    );
}

// ===========================================================================
// NON-VACUITY (teeth): a deliberately-WRONG encoder MUST mismatch silicon.
// ===========================================================================
//
// These prove the bridge is a genuine encoder<->silicon differential, NOT a
// self-comparison and NOT a tautology. If the comparison were vacuous (always
// equal), these would fail.

/// Helper: does the in-house encoder agree with silicon on this exact fact?
fn encoder_matches_silicon(fact: &Fact) -> bool {
    match build_encoder(fact) {
        Some(expr) => eval(&expr) == fact.result,
        None => false,
    }
}

#[test]
fn bridge_is_non_vacuous_wrong_add_encoder_mismatches_silicon() {
    // Take a real ADD fact and feed it to the SUB encoder: it must NOT match
    // silicon for at least one fact (bvadd != bvsub on a non-degenerate input).
    let facts = load_facts();
    let add_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "add").collect();
    assert!(!add_facts.is_empty(), "expected ADD facts in the fixture");

    let mut found_divergence = false;
    for fact in &add_facts {
        // WRONG encoder: SUB where ADD was recorded.
        let w = fact.width;
        let wrong = encode_sub_rr(
            size_of(w),
            leaf(fact.operands[0], w),
            leaf(fact.operands[1], w),
        );
        if eval(&wrong) != fact.result {
            found_divergence = true;
            break;
        }
    }
    assert!(
        found_divergence,
        "NON-VACUITY: a deliberately-wrong (SUB-for-ADD) encoder matched silicon on EVERY \
         ADD fact — the bridge would be a tautology / self-comparison. It must mismatch."
    );
}

#[test]
fn bridge_is_non_vacuous_corrupted_fixture_result_mismatches() {
    // Take the first ADD fact, corrupt its recorded silicon result by +1, and
    // confirm the in-house encoder now DISAGREES. This proves the assertion
    // actually compares against the fixture value (not against itself).
    let facts = load_facts();
    let fact = facts.iter().find(|f| f.op == "add").expect("an ADD fact");
    let corrupted = Fact {
        op: fact.op.clone(),
        width: fact.width,
        operands: fact.operands.clone(),
        result: fact.result.wrapping_add(1),
        theorem: fact.theorem.clone(),
    };
    assert!(
        encoder_matches_silicon(fact),
        "sanity: the genuine ADD fact must match the in-house encoder"
    );
    assert!(
        !encoder_matches_silicon(&corrupted),
        "NON-VACUITY: corrupting the recorded silicon result did NOT change the comparison \
         outcome — the bridge is not actually comparing against the fixture value"
    );
}

#[test]
fn bridge_is_non_vacuous_clamp_shift_would_mismatch_silicon_at_width() {
    // The CRUX of #57: the PLAIN (clamp-to-0) encoder DISAGREES with silicon at a
    // shift amount >= width, while the FAITHFUL (masked) encoder used by the
    // bridge AGREES. This proves (a) the bridge uses the right encoder, and (b)
    // the silicon fixture genuinely encodes the &63 mask, not the SMT clamp.
    use trust_cg_verify::aarch64_semantics::encode_lsl_rr;
    let facts = load_facts();
    // Find an X-form LSL fact whose amount >= width (e.g. bvShl 1 64 = 1).
    let fact = facts
        .iter()
        .find(|f| f.op == "lsl" && f.width == 64 && f.operands[1] >= 64 && f.operands[0] != 0)
        .expect("expected an X LSL fact with amount >= 64 (e.g. bvShl 1 64)");

    let masked = encode_lsl_rr_masked(
        OperandSize::S64,
        leaf(fact.operands[0], 64),
        leaf(fact.operands[1], 64),
    );
    let plain = encode_lsl_rr(
        OperandSize::S64,
        leaf(fact.operands[0], 64),
        leaf(fact.operands[1], 64),
    );
    assert_eq!(
        eval(&masked),
        fact.result,
        "the FAITHFUL masked encoder must match silicon at amount >= width ({})",
        fact.theorem
    );
    assert_ne!(
        eval(&plain),
        fact.result,
        "NON-VACUITY (#57): the PLAIN clamp-to-0 encoder must DISAGREE with silicon at \
         amount >= width — proving the silicon fixture encodes the hardware &63 mask, not \
         the SMT clamp, and that the bridge's choice of the masked encoder is load-bearing"
    );
}
