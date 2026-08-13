// trust-cg-verify/tests/bdefs_differential_bridge_x86.rs — DELIVERABLE of #92.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE B-x86-rosetta DIFFERENTIAL BRIDGE (the x86 analog of bdefs_differential_bridge.rs).
// ===========================================================================
//
// This is the x86-64 machine-side dual of the in-house SmtExpr model. It defeats
// root-cause #2 of the lowering-equivalence TCB — that BOTH sides of every x86
// reconstruction check are validated against ONE in-house machine spec
// (trust-cg-verify/src/x86_64_semantics.rs, the SmtExpr encoders), so a SHARED
// misencoding in that spec is INVISIBLE to the equivalence check.
//
// HOW IT DEFEATS THAT: every fact in tests/fixtures/x86_64_rosetta_truth.json is a
// result recorded from ROSETTA 2 — Apple's INDEPENDENT x86-64 binary translator,
// NOT a second in-house model. Rosetta is a true independent x86 implementation
// (one notch below bare silicon: it faithfully reproduces x86 integer semantics
// including shift-count masking &0x3f/&0x1f and the IDIV/DIV #DE traps on a zero
// divisor and on signed INT_MIN/-1). For each fact this test:
//
//   1. takes the op + the Rosetta operand literals,
//   2. constructs trust-cg's OWN in-house x86 SmtExpr encoder for that op (the
//      SAME encoders the reconstruction machine side uses — x86_64_semantics.rs),
//      with the operands as concrete SmtExpr::bv_const leaves,
//   3. evaluates it through the SAME SmtExpr `try_eval` evaluator the
//      reconstruction `verify_by_evaluation` path uses, and
//   4. asserts the EVALUATED result EQUALS the ROSETTA-recorded result (VALUE
//      facts) OR yields POISON / is precondition-excluded (TRAP facts).
//
// A mismatch is a FINDING (a latent miscompile-class bug, or a convention
// divergence). It is NOT papered over by excluding the op or loosening the
// comparison. The bridge is NON-VACUOUS: `bridge_is_non_vacuous_*` below prove
// deliberately-WRONG encoders mismatch a Rosetta fact (so the bridge has teeth —
// it is not a tautology and not a self-comparison).
//
// CONVENTIONS (exactly where mismatches surface — all validated here):
//   * SHIFTS use the FAITHFUL amount-MASKED encoders (encode_shl_rr_masked etc.,
//     count & (width-1)) — NOT the plain SMT bvshl whose evaluator CLAMPS to 0 at
//     count >= width. The masked encoder matches Rosetta's &0x3f/&0x1f (#57).
//   * x86 IDIV/DIV #DE-TRAP on a zero divisor and on signed INT_MIN/-1. trust-cg
//     models that as TrapIfZero(divisor) -> EvalResult::Poison (the divisor==0
//     trap; the D-survivor fix, #79) and, for the signed INT_MIN/-1 overflow, a
//     LOAD-BEARING `no overflow` precondition (bvsdiv at INT_MIN/-1 WRAPS to
//     INT_MIN with no Poison, so the precondition — not Poison — carries that
//     trap). The bridge asserts BOTH match Rosetta's #DE: div0 -> the trapping
//     encoder is Poison; INT_MIN/-1 -> the input is precondition-excluded.
//   * W-forms: operands are read as their low 32 bits and the result is the low-32
//     value. Encoded by exercising the SAME width-polymorphic encoders at 32-bit.
//   * IMUL_imm / LEA sample FIXED immediates/scale/disp (the operand grid varies
//     the register operand only — x86 encodes imm/scale/disp as instruction-literal
//     fields). The immediate is operand[1] read as a SIGNED value of the width.
//   * CMOVNE: the condition is `ZF==0` i.e. `a != b`, built from a CMP-derived
//     IntCmpFlags (operands [a, b, old_dst, src]) — mirrors encode_cmovcc(NE,..).

use std::collections::HashMap;

use serde_json::Value;

use trust_cg_ir::X86CondCode;
use trust_cg_verify::smt::{EvalResult, SmtExpr, mask};
use trust_cg_verify::x86_64_semantics::{
    X86OperandSize, encode_add_rr, encode_and_rr, encode_cmovcc, encode_div_quotient,
    encode_div_remainder, encode_idiv_quotient, encode_idiv_remainder, encode_imul_rr,
    encode_imul_rri, encode_int_cmp_flags, encode_lea_base_disp, encode_lea_base_index_scale,
    encode_lea_base_index_scale_disp, encode_mov_rr, encode_movsx, encode_movzx, encode_mul_high,
    encode_mul_low, encode_neg, encode_not, encode_or_rr, encode_sar_rr_masked,
    encode_shl_rr_masked, encode_shr_rr_masked, encode_sub_rr, encode_xor_rr, eval_int_condition,
};

const FIXTURE: &str = include_str!("fixtures/x86_64_rosetta_truth.json");

/// The fixed immediates/scale/disp the generator bakes into the IMUL_imm / LEA
/// instruction encodings (see the fixture inclusion_policy — these are
/// instruction-literal fields, not register-parameterizable).
const LEA_DISP_D4: i64 = 4;
const LEA_SCALE_S4: u32 = 4;
const LEA_SCALE_S8: u32 = 8;

/// A single Rosetta ground-truth fact (one independent-x86 recorded result).
struct Fact {
    op: String,
    width: u32,
    operands: Vec<u64>,
    /// `Some(v)` for a VALUE fact; `None` for a TRAP (#DE) fact.
    result: Option<u64>,
    theorem: String,
}

fn parse_result(v: &Value) -> Option<u64> {
    match v {
        Value::String(s) if s == "trap" => None,
        Value::String(s) => {
            let h = s.strip_prefix("0x").unwrap_or(s);
            Some(u64::from_str_radix(h, 16).expect("result hex parses"))
        }
        other => panic!("bridge: result is neither a hex string nor \"trap\": {other:?}"),
    }
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
                .map(|v| {
                    v.as_u64()
                        .expect("operand is a u64 (full low-width literal)")
                })
                .collect(),
            result: parse_result(&f["result"]),
            theorem: f["theorem"]
                .as_str()
                .expect("theorem is a string")
                .to_string(),
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

/// A `width`-bit constant leaf carrying the low `width` bits of `v`.
fn leaf(v: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(v, width)
}

fn size_of(width: u32) -> X86OperandSize {
    match width {
        32 => X86OperandSize::S32,
        64 => X86OperandSize::S64,
        other => panic!("bridge: unexpected width {other}"),
    }
}

/// Interpret a low-`width` unsigned literal as a signed i64 (sign-extend the
/// top bit of the width). Used for IMUL_imm's immediate operand.
fn signed_of(v: u64, width: u32) -> i64 {
    let v = mask(v, width);
    if width < 64 && (v >> (width - 1)) & 1 == 1 {
        (v | !mask(u64::MAX, width)) as i64
    } else {
        v as i64
    }
}

// ---------------------------------------------------------------------------
// VALUE-encoder dispatch. Every non-trapping op maps to its in-house encoder.
// Division VALUE facts go through `build_div_value_encoder` (the trapping form,
// off the trap point), so they are NOT handled here.
// ---------------------------------------------------------------------------
fn build_value_encoder(fact: &Fact) -> Option<SmtExpr> {
    let w = fact.width;
    let sz = size_of(w);
    let ops = &fact.operands;
    let l = |i: usize| leaf(ops[i], w);
    let e = match fact.op.as_str() {
        // ---- arithmetic / logic (X and W share the width-polymorphic encoder) -
        "add" | "addw" => encode_add_rr(sz, l(0), l(1)),
        "sub" | "subw" => encode_sub_rr(sz, l(0), l(1)),
        "imul" | "imulw" => encode_imul_rr(sz, l(0), l(1)),
        "and" | "andw" => encode_and_rr(sz, l(0), l(1)),
        "or" | "orw" => encode_or_rr(sz, l(0), l(1)),
        "xor" | "xorw" => encode_xor_rr(sz, l(0), l(1)),
        // ---- one-operand unsigned widening MUL: low half (RAX) / high half (RDX)
        "mul_low" | "mul_low_w" => encode_mul_low(l(0), l(1)),
        "mul_high" | "mul_high_w" => encode_mul_high(l(0), l(1)),
        // ---- three-operand IMUL with a fixed sign-extended immediate ----------
        "imul_imm" | "imul_imm_w" => encode_imul_rri(sz, l(0), signed_of(ops[1], w)),
        // ---- unary --------------------------------------------------------------
        "neg" | "negw" => encode_neg(sz, l(0)),
        "not" | "notw" => encode_not(sz, l(0)),
        "mov" | "movw" => encode_mov_rr(sz, l(0)),
        // ---- shifts: FAITHFUL amount-masked encoders (the #57 fix) -------------
        "shl" | "shlw" => encode_shl_rr_masked(sz, l(0), l(1)),
        "shr" | "shrw" => encode_shr_rr_masked(sz, l(0), l(1)),
        "sar" | "sarw" => encode_sar_rr_masked(sz, l(0), l(1)),
        // ---- extension moves (from_width, to_width) ---------------------------
        "movzx_16_64" => encode_movzx(16, 64, l(0)),
        "movsx_16_64" => encode_movsx(16, 64, l(0)),
        "movsxd_32_64" => encode_movsx(32, 64, l(0)),
        "movzx_8_32" => encode_movzx(8, 32, l(0)),
        "movsx_8_32" => encode_movsx(8, 32, l(0)),
        // ---- CMOVNE: condition is ZF==0 (a != b) from a CMP-derived flags -----
        "cmovne" | "cmovne_w" => {
            let flags = encode_int_cmp_flags(w, l(0), l(1));
            let cond = eval_int_condition(X86CondCode::NE, &flags);
            // operands: [a, b, old_dst, src]; CMOV copies src if cond, else old.
            encode_cmovcc(sz, cond, l(2), l(3))
        }
        // ---- LEA: fixed scale/disp (instruction-literal fields) ---------------
        "lea_b_i_s8_d4" => encode_lea_base_index_scale_disp(l(0), l(1), LEA_SCALE_S8, LEA_DISP_D4),
        "lea_b_i_s4" => encode_lea_base_index_scale(l(0), l(1), LEA_SCALE_S4),
        "lea_b_d4" => encode_lea_base_disp(l(0), LEA_DISP_D4, w),
        _ => return None,
    };
    Some(e)
}

/// True iff `op` is an x86 division op family (idiv/div, quotient/remainder, W/X).
fn is_div_op(op: &str) -> bool {
    matches!(
        op,
        "idiv_q" | "idiv_r" | "idiv_q_w" | "idiv_r_w" | "div_q" | "div_r" | "div_q_w" | "div_r_w"
    )
}

/// True iff `op` is a SIGNED division op (IDIV) — relevant for INT_MIN/-1 overflow.
fn is_signed_div(op: &str) -> bool {
    op.starts_with("idiv")
}

/// True iff `op` is a quotient (vs remainder) division op.
fn is_quotient(op: &str) -> bool {
    op == "idiv_q" || op == "idiv_q_w" || op == "div_q" || op == "div_q_w"
}

/// Build the FAITHFUL TRAPPING division encoder for a division fact: the
/// single-width quotient/remainder SmtExpr (the SAME encoder the reconstruction
/// uses — encode_idiv_quotient/.../encode_div_remainder) wrapped in
/// `trap_if_zero(divisor)` so a zero divisor evaluates to Poison (the #DE model,
/// #79). operands = [a (dividend=RAX), b (divisor)].
fn build_div_trapping_encoder(fact: &Fact) -> SmtExpr {
    let w = fact.width;
    let sz = size_of(w);
    let a = leaf(fact.operands[0], w);
    let b = leaf(fact.operands[1], w);
    let value = match fact.op.as_str() {
        "idiv_q" | "idiv_q_w" => encode_idiv_quotient(sz, a, b.clone()),
        "idiv_r" | "idiv_r_w" => encode_idiv_remainder(sz, a, b.clone()),
        "div_q" | "div_q_w" => encode_div_quotient(sz, a, b.clone()),
        "div_r" | "div_r_w" => encode_div_remainder(sz, a, b.clone()),
        other => panic!("bridge: build_div_trapping_encoder on non-div op `{other}`"),
    };
    value.trap_if_zero(b)
}

/// The trust-cg div PRECONDITIONS for this fact: `divisor != 0`, and (signed)
/// `NOT(dividend==INT_MIN AND divisor==-1)`. Mirrors reconstruct_x86_division.
/// Returns whether the precondition HOLDS for this concrete input (i.e. the input
/// is NOT excluded). An EXCLUDED input is the precondition's way of modeling a
/// trap that is NOT a Poison (the signed INT_MIN/-1 overflow, where bvsdiv wraps).
fn div_precondition_holds(fact: &Fact) -> bool {
    let w = fact.width;
    let a = mask(fact.operands[0], w);
    let b = mask(fact.operands[1], w);
    if b == 0 {
        return false; // divisor != 0 precondition excludes this input.
    }
    if is_signed_div(&fact.op) {
        let int_min = 1u64 << (w - 1);
        let neg_one = mask(u64::MAX, w);
        if a == int_min && b == neg_one {
            return false; // no-overflow precondition excludes INT_MIN / -1.
        }
    }
    true
}

/// Evaluate an encoder expression, returning the full EvalResult (so the caller
/// can distinguish Poison from a defined bitvector). The SAME `try_eval`
/// evaluator the reconstruction `verify_by_evaluation` path uses.
fn eval_full(expr: &SmtExpr) -> EvalResult {
    let env: HashMap<String, u64> = HashMap::new();
    expr.try_eval(&env).expect("bridge: encoder eval failed")
}

/// Evaluate to a concrete u64 (panics on Poison / non-bitvector — used for VALUE
/// facts where a defined result is REQUIRED).
fn eval(expr: &SmtExpr) -> u64 {
    match eval_full(expr) {
        EvalResult::Bv(v) => v,
        EvalResult::Bv128(v) => v as u64,
        other => panic!("bridge: encoder evaluated to non-bitvector {other:?}"),
    }
}

// ===========================================================================
// THE BRIDGE: every in-house encoder must match Rosetta on every recorded fact.
// VALUE facts: eval == Rosetta result. TRAP facts: Poison (div0) or precond-
// excluded (signed INT_MIN/-1) — matching Rosetta's #DE.
// ===========================================================================
#[test]
fn x86_inhouse_encoders_match_rosetta_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() > 5_000,
        "bridge: the Rosetta fixture is suspiciously small ({} facts) — truncated?",
        facts.len()
    );

    // No-silent-truncation accounting: the loaded facts must match the header.
    let (total_attempted, emitted, value_facts, trap_facts) = load_accounting();
    assert_eq!(
        total_attempted, emitted,
        "fixture accounting: total_attempted ({total_attempted}) != emitted ({emitted}) — the \
         harness silently truncated"
    );
    assert_eq!(
        emitted,
        facts.len(),
        "fixture accounting: header emitted ({emitted}) != loaded fact count ({})",
        facts.len()
    );
    let loaded_traps = facts.iter().filter(|f| f.result.is_none()).count();
    let loaded_values = facts.len() - loaded_traps;
    assert_eq!(loaded_values, value_facts, "value-fact count drift");
    assert_eq!(loaded_traps, trap_facts, "trap-fact count drift");

    let mut value_mismatches: Vec<String> = Vec::new();
    let mut trap_mismatches: Vec<String> = Vec::new();
    let mut per_op: HashMap<String, usize> = HashMap::new();
    let mut checked_value = 0usize;
    let mut checked_trap = 0usize;

    for fact in &facts {
        *per_op.entry(fact.op.clone()).or_default() += 1;

        if is_div_op(&fact.op) {
            // -- Division: TRAP facts and VALUE facts share the trapping encoder.
            match fact.result {
                None => {
                    // TRAP fact: Rosetta #DE-trapped. trust-cg must AGREE this input
                    // is a trap, via EITHER the trapping encoder -> Poison (div0) OR
                    // the load-bearing precondition EXCLUDING the input (INT_MIN/-1).
                    checked_trap += 1;
                    let precond_excluded = !div_precondition_holds(fact);
                    let trapping = build_div_trapping_encoder(fact);
                    let is_poison = matches!(eval_full(&trapping), EvalResult::Poison);
                    // A genuine x86 #DE is EITHER a zero divisor (Poison) OR a signed
                    // INT_MIN/-1 overflow (precondition-excluded). Both must be a trap
                    // on the trust-cg side; neither may be a defined matching value.
                    if !(is_poison || precond_excluded) && trap_mismatches.len() < 40 {
                        trap_mismatches.push(format!(
                            "{}: op={} width={} operands={:?} -> Rosetta #DE-TRAPPED, but \
                                 trust-cg yielded NEITHER Poison NOR a precondition-exclusion \
                                 (defined value {:#x}) — trust-cg fails to model this x86 trap",
                            fact.theorem,
                            fact.op,
                            fact.width,
                            fact.operands,
                            eval(&trapping)
                        ));
                    }
                }
                Some(want) => {
                    // VALUE fact: off the trap point. The precondition MUST hold (a
                    // value fact is never a trap input) and the trapping encoder must
                    // evaluate (off the trap point) to exactly the Rosetta value.
                    checked_value += 1;
                    assert!(
                        div_precondition_holds(fact),
                        "{}: a division VALUE fact must satisfy the trust-cg precondition \
                         (divisor!=0, no INT_MIN/-1) — operands={:?}",
                        fact.theorem,
                        fact.operands
                    );
                    let trapping = build_div_trapping_encoder(fact);
                    let got = match eval_full(&trapping) {
                        EvalResult::Bv(v) => v,
                        EvalResult::Bv128(v) => v as u64,
                        EvalResult::Poison => {
                            // Off the trap point the trapping encoder must NOT be Poison.
                            if value_mismatches.len() < 40 {
                                value_mismatches.push(format!(
                                    "{}: op={} operands={:?} -> trust-cg trapping encoder gave \
                                     POISON on a NON-trap input; Rosetta value {want:#x}",
                                    fact.theorem, fact.op, fact.operands
                                ));
                            }
                            continue;
                        }
                        other => panic!("bridge: div encoder gave non-bitvector {other:?}"),
                    };
                    if got != want {
                        let _ = is_quotient(&fact.op); // (documents the q/r split)
                        if value_mismatches.len() < 40 {
                            value_mismatches.push(format!(
                                "{}: op={} width={} operands={:?} -> trust-cg encoder gave \
                                 {got:#x}, Rosetta recorded {want:#x}",
                                fact.theorem, fact.op, fact.width, fact.operands
                            ));
                        }
                    }
                }
            }
            continue;
        }

        // -- Non-division: every fact is a VALUE fact with an in-house encoder.
        let want = fact.result.unwrap_or_else(|| {
            panic!(
                "bridge: non-division op `{}` ({}) recorded a TRAP — only IDIV/DIV trap on x86; \
                 a trapping non-div fact is a fixture/bridge drift bug",
                fact.op, fact.theorem
            )
        });
        let expr = build_value_encoder(fact).unwrap_or_else(|| {
            panic!(
                "bridge: fixture op `{}` ({}) has no in-house encoder dispatch — the fixture and \
                 the bridge have drifted (every fixture op must map to an encoder or be EXCLUDED \
                 in the generator, never silently unhandled)",
                fact.op, fact.theorem
            )
        });
        checked_value += 1;
        let got = eval(&expr);
        if got != want && value_mismatches.len() < 40 {
            value_mismatches.push(format!(
                "{}: op={} width={} operands={:?} -> in-house encoder gave {got:#x}, Rosetta \
                     recorded {want:#x}",
                fact.theorem, fact.op, fact.width, fact.operands
            ));
        }
    }

    // PER-OP accounting: every fixture op family must actually have been exercised
    // (no silent skip), and the count must be non-trivial.
    assert!(
        per_op.len() >= 40,
        "bridge: too few op families exercised ({}) — expected the full ~48-family x86 grid",
        per_op.len()
    );
    assert_eq!(
        checked_value + checked_trap,
        facts.len(),
        "bridge: checked {checked_value} value + {checked_trap} trap != {} total facts (silent skip)",
        facts.len()
    );
    assert_eq!(
        checked_trap, trap_facts,
        "bridge: trap-fact check count drift"
    );

    assert!(
        value_mismatches.is_empty(),
        "B-x86-rosetta BRIDGE FINDING (VALUE): {} of {checked_value} in-house-encoder vs Rosetta \
         comparisons MISMATCH. Each is a latent miscompile-class divergence between trust-cg's x86 \
         model and real x86 (Rosetta 2). First mismatches:\n{}",
        value_mismatches.len(),
        value_mismatches.join("\n")
    );
    assert!(
        trap_mismatches.is_empty(),
        "B-x86-rosetta BRIDGE FINDING (TRAP): {} of {checked_trap} #DE traps where trust-cg does \
         NOT agree the input is a trap (neither Poison nor precondition-excluded). First:\n{}",
        trap_mismatches.len(),
        trap_mismatches.join("\n")
    );

    eprintln!(
        "B-x86-rosetta bridge: {checked_value} VALUE + {checked_trap} TRAP in-house-encoder vs \
         Rosetta comparisons PASS across {} op families.",
        per_op.len()
    );
}

// ===========================================================================
// NON-VACUITY (teeth): deliberately-WRONG encoders MUST mismatch Rosetta, and
// the CORRECT encoder must match ALL facts of that family.
// ===========================================================================

/// Helper: does the in-house VALUE encoder agree with Rosetta on this fact?
fn value_encoder_matches(fact: &Fact) -> bool {
    match (build_value_encoder(fact), fact.result) {
        (Some(expr), Some(want)) => eval(&expr) == want,
        _ => false,
    }
}

#[test]
fn bridge_is_non_vacuous_wrong_add_encoder_mismatches_rosetta() {
    // Feed ADD facts to the SUB encoder: it must NOT match Rosetta for at least
    // one fact (bvadd != bvsub on a non-degenerate input).
    let facts = load_facts();
    let add_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "add").collect();
    assert!(!add_facts.is_empty(), "expected ADD facts in the fixture");

    // The CORRECT encoder matches ALL add facts (precondition for the teeth).
    for f in &add_facts {
        assert!(
            value_encoder_matches(f),
            "precondition: the correct ADD encoder must match Rosetta on every ADD fact ({})",
            f.theorem
        );
    }

    let mut found_divergence = false;
    for fact in &add_facts {
        let w = fact.width;
        let wrong = encode_sub_rr(
            size_of(w),
            leaf(fact.operands[0], w),
            leaf(fact.operands[1], w),
        );
        if Some(eval(&wrong)) != fact.result {
            found_divergence = true;
            break;
        }
    }
    assert!(
        found_divergence,
        "NON-VACUITY: a deliberately-wrong (SUB-for-ADD) encoder matched Rosetta on EVERY ADD fact \
         — the bridge would be a tautology / self-comparison. It must mismatch."
    );
}

#[test]
fn bridge_is_non_vacuous_unmasked_shift_mismatches_rosetta_at_count_ge_width() {
    // The CRUX of #57: the PLAIN (clamp-to-0) shift encoder DISAGREES with Rosetta
    // at a shift count >= width, while the FAITHFUL (masked) encoder used by the
    // bridge AGREES. This proves (a) the bridge uses the right encoder, and (b)
    // the Rosetta fixture genuinely encodes the &0x3f mask, not the SMT clamp.
    use trust_cg_verify::x86_64_semantics::encode_shl_rr;
    let facts = load_facts();
    // Find an X-form SHL fact whose count >= width (so masking is observable) and
    // src1 != 0 (so the clamp-to-0 vs masked results actually differ).
    let fact = facts
        .iter()
        .find(|f| f.op == "shl" && f.width == 64 && f.operands[1] >= 64 && f.operands[0] != 0)
        .expect("expected an X SHL fact with count >= 64 and nonzero src");

    let masked = encode_shl_rr_masked(
        X86OperandSize::S64,
        leaf(fact.operands[0], 64),
        leaf(fact.operands[1], 64),
    );
    let plain = encode_shl_rr(
        X86OperandSize::S64,
        leaf(fact.operands[0], 64),
        leaf(fact.operands[1], 64),
    );
    assert_eq!(
        Some(eval(&masked)),
        fact.result,
        "the FAITHFUL masked encoder must match Rosetta at count >= width ({})",
        fact.theorem
    );
    assert_ne!(
        Some(eval(&plain)),
        fact.result,
        "NON-VACUITY (#57): the PLAIN clamp-to-0 encoder must DISAGREE with Rosetta at count >= \
         width — proving the Rosetta fixture encodes the hardware &0x3f mask, not the SMT clamp, \
         and that the bridge's choice of the masked encoder is load-bearing"
    );
}

#[test]
fn bridge_is_non_vacuous_idiv_as_div_mismatches_on_negative_dividend() {
    // An IDIV-emitted-as-DIV (signed-as-unsigned) bug differs ONLY in sdiv-vs-udiv,
    // which DIVERGES on a NEGATIVE dividend (when |a/b| differs under the two
    // interpretations). Over ALL signed-division VALUE facts: (1) the CORRECT
    // signed encoder must match Rosetta on EVERY one (the precondition for the
    // teeth), and (2) the WRONG unsigned encoder must MISMATCH on at least one
    // (the teeth). Note: on some operand pairs sdiv and udiv coincide (e.g.
    // dividend -1 / various b both give 0 or -1), so we scan for a genuine
    // divergence rather than relying on the first negative-dividend fact.
    let facts = load_facts();
    let signed_value_facts: Vec<&Fact> = facts
        .iter()
        .filter(|f| f.op == "idiv_q" && f.width == 64 && f.result.is_some())
        .collect();
    assert!(
        !signed_value_facts.is_empty(),
        "expected signed-IDIV VALUE facts"
    );

    // (1) The CORRECT signed encoder matches Rosetta on EVERY signed VALUE fact.
    for f in &signed_value_facts {
        let correct = build_div_trapping_encoder(f);
        assert_eq!(
            eval(&correct),
            f.result.unwrap(),
            "precondition: the correct SIGNED IDIV encoder must match Rosetta on every signed \
             VALUE fact ({})",
            f.theorem
        );
    }

    // (2) The WRONG unsigned-DIV encoder DIVERGES from the Rosetta signed result
    // on at least one fact (a negative dividend where sdiv != udiv).
    let mut found_divergence = false;
    let mut witness = String::new();
    for f in &signed_value_facts {
        let want = f.result.unwrap();
        let wrong = encode_div_quotient(
            X86OperandSize::S64,
            leaf(f.operands[0], 64),
            leaf(f.operands[1], 64),
        );
        if eval(&wrong) != want {
            found_divergence = true;
            witness = f.theorem.clone();
            break;
        }
    }
    assert!(
        found_divergence,
        "NON-VACUITY: IDIV-as-DIV (unsigned for signed) matched the Rosetta signed result on EVERY \
         signed-division fact — the bridge's sdiv-vs-udiv distinction would not be load-bearing. \
         It must MISMATCH on a negative dividend (witness expected, e.g. -1/2)."
    );
    eprintln!(
        "IDIV-as-DIV teeth: unsigned encoder diverges from Rosetta signed result at {witness}"
    );
}

#[test]
fn bridge_is_non_vacuous_corrupted_fixture_result_mismatches() {
    // Take the first ADD fact, corrupt its recorded Rosetta result by +1, and
    // confirm the in-house encoder now DISAGREES — proving the assertion actually
    // compares against the fixture value (not against itself).
    let facts = load_facts();
    let fact = facts.iter().find(|f| f.op == "add").expect("an ADD fact");
    let want = fact.result.expect("ADD is a value fact");
    let corrupted = Fact {
        op: fact.op.clone(),
        width: fact.width,
        operands: fact.operands.clone(),
        result: Some(want.wrapping_add(1) & mask(u64::MAX, fact.width)),
        theorem: fact.theorem.clone(),
    };
    assert!(
        value_encoder_matches(fact),
        "sanity: the genuine ADD fact must match the in-house encoder"
    );
    assert!(
        !value_encoder_matches(&corrupted),
        "NON-VACUITY: corrupting the recorded Rosetta result did NOT change the comparison outcome \
         — the bridge is not actually comparing against the fixture value"
    );
}

#[test]
fn bridge_is_non_vacuous_div_trap_requires_poison_or_precond() {
    // Prove the TRAP arm has teeth: a div0 TRAP fact yields Poison from the
    // trapping encoder (so a defined value would FAIL the trap arm), and an
    // INT_MIN/-1 signed TRAP fact is precondition-EXCLUDED. If the encoder dropped
    // the TrapIfZero wrapper (the fault-5a mutation), div0 would give a defined
    // value (0) and the trap arm would catch it.
    let facts = load_facts();

    // (a) div0 -> Poison (the TrapIfZero model).
    let div0 = facts
        .iter()
        .find(|f| f.op == "div_q" && f.width == 64 && f.result.is_none() && f.operands[1] == 0)
        .expect("expected a div-by-zero TRAP fact");
    let trapping = build_div_trapping_encoder(div0);
    assert!(
        matches!(eval_full(&trapping), EvalResult::Poison),
        "div-by-zero must yield Poison from the trapping encoder (TrapIfZero models #DE)"
    );
    // And WITHOUT the trap wrapper the result would be a DEFINED value (the bug the
    // wrapper guards against): bvudiv by 0 in SMT-LIB is all-ones, not Poison.
    let unwrapped = encode_div_quotient(
        X86OperandSize::S64,
        leaf(div0.operands[0], 64),
        leaf(div0.operands[1], 64),
    );
    assert!(
        !matches!(eval_full(&unwrapped), EvalResult::Poison),
        "NON-VACUITY: the UNWRAPPED div encoder must give a defined (non-Poison) value at \
         divisor==0 — so the TrapIfZero wrapper (and thus the trap arm's Poison check) is \
         load-bearing"
    );

    // (b) signed INT_MIN / -1 -> precondition-EXCLUDED (not Poison; bvsdiv wraps).
    let overflow = facts
        .iter()
        .find(|f| {
            f.op == "idiv_q"
                && f.width == 64
                && f.result.is_none()
                && f.operands[0] == (1u64 << 63)
                && f.operands[1] == u64::MAX
        })
        .expect("expected a signed INT_MIN / -1 TRAP fact");
    assert!(
        !div_precondition_holds(overflow),
        "signed INT_MIN / -1 must be EXCLUDED by the no-overflow precondition (it is the trap \
         carrier, since bvsdiv at INT_MIN/-1 WRAPS to INT_MIN with no Poison)"
    );
    // Documented contract difference: the raw bvsdiv WRAPS (no Poison) — that is
    // why the precondition, not Poison, carries this trap.
    let raw = encode_idiv_quotient(
        X86OperandSize::S64,
        leaf(overflow.operands[0], 64),
        leaf(overflow.operands[1], 64),
    );
    assert_eq!(
        eval(&raw),
        1u64 << 63,
        "contract: bvsdiv(INT_MIN, -1) WRAPS to INT_MIN (no Poison) — the no-overflow precondition \
         is what makes this input a trap on the trust-cg side, matching Rosetta's #DE"
    );
}
