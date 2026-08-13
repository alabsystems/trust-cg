// trust-cg-verify/tests/bdefs_differential_bridge_x86_packed.rs — DELIVERABLE of #96
// (FRONTIER 2: extend the differential bridges to packed-SIMD, x86 packed-int).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE B-x86-sse-packed DIFFERENTIAL BRIDGE — the PACKED-SSE2 analog of
// bdefs_differential_bridge_x86.rs (the scalar x86 Rosetta bridge).
// ===========================================================================
//
// This MIRRORS the scalar x86 Rosetta bridge exactly, for trust-cg's PACKED-SSE2
// integer machine encoders. It defeats root-cause #2 of the lowering-equivalence
// TCB for x86 PACKED-int ops: BOTH sides of every packed-x86 reconstruction check
// are validated against ONE in-house machine spec (x86_64_semantics.rs, the
// SmtExpr `encode_p*` encoders), so a SHARED misencoding in that spec is INVISIBLE
// to the equivalence check.
//
// HOW IT DEFEATS THAT: every fact in tests/fixtures/x86_packed_rosetta_truth.json
// is a 128-bit result recorded from ROSETTA 2 — Apple's INDEPENDENT x86-64 binary
// translator, NOT a second in-house model. Rosetta is a true independent x86
// implementation (one notch below bare silicon: it faithfully reproduces the
// packed-SSE2/SSE4 integer semantics — lane-wise wrap-around add/sub/mul, all-ones/
// all-zero compare masks, and packed imm-shift SATURATION at count >= lane width).
// For each fact this test:
//
//   1. takes the op + the Rosetta 128-bit operand literals (a_lo/a_hi, b_lo/b_hi,
//      and the imm for shifts),
//   2. constructs trust-cg's OWN in-house packed SmtExpr encoder for that op (the
//      SAME `encode_p*` encoders the reconstruction machine side uses), with the
//      operands as concrete 128-bit `Bv128` constant leaves (built as
//      concat(bv_const(hi,64), bv_const(lo,64)) — the same v128 construction the
//      reconstruction tests use),
//   3. evaluates it through the SAME SmtExpr `try_eval` evaluator the
//      reconstruction `verify_by_evaluation` path uses (yielding an
//      EvalResult::Bv128), and
//   4. asserts the EVALUATED 128-bit result EQUALS the ROSETTA-recorded 128-bit
//      result.
//
// A mismatch is a FINDING (a latent miscompile-class bug, or a convention
// divergence). It is NOT papered over by excluding the op or loosening the
// comparison. The bridge is NON-VACUOUS: the `bridge_is_non_vacuous_*` tests below
// prove deliberately-WRONG encoders mismatch a Rosetta fact (PADDD-as-PSUBD,
// PCMPEQD-as-PCMPGTD, and the wrong lane width PADDB-as-PADDW), so the bridge has
// teeth — it is not a tautology and not a self-comparison.
//
// CONVENTIONS (exactly where mismatches surface — all validated here):
//   * BITWISE ops (PAND/PANDN/POR/PXOR) are whole-128-bit (encoded with lane_bits
//     marker 128 in the fixture); their in-house encoders are plain bvand/bvor/
//     bvxor over the full 128-bit operand (PANDN = (~a)&b, matching SSE andnot).
//   * COMPARE ops produce per-lane ALL-ONES (equal / signed-greater) or ALL-ZERO
//     masks. PCMPGT is SIGNED.
//   * IMMEDIATE dword shifts SATURATE at count >= 32 (PSLLD/PSRLD -> 0, PSRAD ->
//     sign-fill) — NOT a count mask. This is the SMT bvshl/bvlshr/bvashr clamp
//     contract (the OPPOSITE of the scalar SHL/SHR/SAR &0x1f mask), so the bridge
//     validates that the packed encoder uses the clamp, not the mask.

use std::collections::HashMap;

use serde_json::Value;

use trust_cg_verify::smt::{EvalResult, SmtExpr};
use trust_cg_verify::x86_64_semantics::{
    encode_paddb, encode_paddd, encode_paddq, encode_paddw, encode_pand, encode_pandn,
    encode_pcmpeqb, encode_pcmpeqd, encode_pcmpeqq, encode_pcmpeqw, encode_pcmpgtb, encode_pcmpgtd,
    encode_pcmpgtq, encode_pcmpgtw, encode_pmulld, encode_pmullw, encode_por, encode_pslld_imm,
    encode_psrad_imm, encode_psrld_imm, encode_psubb, encode_psubd, encode_psubq, encode_psubw,
    encode_pxor,
};

const FIXTURE: &str = include_str!("fixtures/x86_packed_rosetta_truth.json");

/// A single Rosetta packed ground-truth fact (one independent-x86 recorded 128-bit
/// result).
struct Fact {
    op: String,
    lane_bits: u32,
    /// 128-bit operand A as (lo, hi) qwords.
    a: u128,
    /// 128-bit operand B as (lo, hi) qwords. For imm-shift ops, B is unused.
    b: u128,
    /// `Some(c)` for imm-shift ops; `None` for binary ops.
    imm: Option<u32>,
    /// The Rosetta-recorded 128-bit result.
    result: u128,
    theorem: String,
}

/// Parse a `0x..` hex string (16 or 32 hex digits) into a u128.
fn parse_hex_u128(v: &Value) -> u128 {
    let s = v.as_str().expect("hex field is a string");
    let h = s.strip_prefix("0x").unwrap_or(s);
    u128::from_str_radix(h, 16).expect("hex parses to u128")
}

fn parse_hex_u64(v: &Value) -> u64 {
    let s = v.as_str().expect("hex field is a string");
    let h = s.strip_prefix("0x").unwrap_or(s);
    u64::from_str_radix(h, 16).expect("hex parses to u64")
}

/// Combine lo/hi qwords into a u128 (lo = bits 0..63, hi = bits 64..127).
fn u128_of(lo: u64, hi: u64) -> u128 {
    ((hi as u128) << 64) | (lo as u128)
}

fn load_facts() -> Vec<Fact> {
    let doc: Value = serde_json::from_str(FIXTURE).expect("fixture is valid JSON");
    let arr = doc["facts"]
        .as_array()
        .expect("fixture has a `facts` array");
    arr.iter()
        .map(|f| {
            let a_lo = parse_hex_u64(&f["a_lo"]);
            let a_hi = parse_hex_u64(&f["a_hi"]);
            let a = u128_of(a_lo, a_hi);
            let (b, imm) = if f.get("imm").is_some() {
                (
                    0u128,
                    Some(f["imm"].as_u64().expect("imm is a number") as u32),
                )
            } else {
                let b_lo = parse_hex_u64(&f["b_lo"]);
                let b_hi = parse_hex_u64(&f["b_hi"]);
                (u128_of(b_lo, b_hi), None)
            };
            // Cross-check the 128-bit result string against result_lo/result_hi.
            let result = parse_hex_u128(&f["result"]);
            let r_lo = parse_hex_u64(&f["result_lo"]);
            let r_hi = parse_hex_u64(&f["result_hi"]);
            assert_eq!(
                result,
                u128_of(r_lo, r_hi),
                "fixture: result hex disagrees with result_lo/result_hi for {}",
                f["theorem"].as_str().unwrap_or("?")
            );
            Fact {
                op: f["op"].as_str().expect("op is a string").to_string(),
                lane_bits: f["lane_bits"].as_u64().expect("lane_bits is a number") as u32,
                a,
                b,
                imm,
                result,
                theorem: f["theorem"]
                    .as_str()
                    .expect("theorem is a string")
                    .to_string(),
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

/// A 128-bit constant leaf carrying `v` — built as concat(bv_const(hi,64),
/// bv_const(lo,64)), the SAME v128 construction the reconstruction tests use.
/// `concat` places `hi` in the upper bits, so this evaluates to `v` exactly.
fn leaf128(v: u128) -> SmtExpr {
    let lo = (v & 0xFFFF_FFFF_FFFF_FFFF) as u64;
    let hi = (v >> 64) as u64;
    SmtExpr::bv_const(hi, 64).concat(SmtExpr::bv_const(lo, 64))
}

/// A shift-count leaf (32-bit) carrying the immediate `c`. The packed imm-shift
/// encoders expect a count at most 32 bits wide; 32 bits holds every sampled
/// count (incl. 255).
fn count_leaf(c: u32) -> SmtExpr {
    SmtExpr::bv_const(c as u64, 32)
}

// ---------------------------------------------------------------------------
// VALUE-encoder dispatch. Every packed op maps to its in-house encoder.
// ---------------------------------------------------------------------------
fn build_encoder(fact: &Fact) -> Option<SmtExpr> {
    let a = || leaf128(fact.a);
    let b = || leaf128(fact.b);
    let e = match fact.op.as_str() {
        // ---- packed ADD ----------------------------------------------------
        "paddb" => encode_paddb(a(), b()),
        "paddw" => encode_paddw(a(), b()),
        "paddd" => encode_paddd(a(), b()),
        "paddq" => encode_paddq(a(), b()),
        // ---- packed SUB ----------------------------------------------------
        "psubb" => encode_psubb(a(), b()),
        "psubw" => encode_psubw(a(), b()),
        "psubd" => encode_psubd(a(), b()),
        "psubq" => encode_psubq(a(), b()),
        // ---- packed low-MUL ------------------------------------------------
        "pmulld" => encode_pmulld(a(), b()),
        "pmullw" => encode_pmullw(a(), b()),
        // ---- packed bitwise (whole-128-bit) --------------------------------
        "pand" => encode_pand(a(), b()),
        "pandn" => encode_pandn(a(), b()),
        "por" => encode_por(a(), b()),
        "pxor" => encode_pxor(a(), b()),
        // ---- packed equality compare ---------------------------------------
        "pcmpeqb" => encode_pcmpeqb(a(), b()),
        "pcmpeqw" => encode_pcmpeqw(a(), b()),
        "pcmpeqd" => encode_pcmpeqd(a(), b()),
        "pcmpeqq" => encode_pcmpeqq(a(), b()),
        // ---- packed signed greater-than compare ----------------------------
        "pcmpgtb" => encode_pcmpgtb(a(), b()),
        "pcmpgtw" => encode_pcmpgtw(a(), b()),
        "pcmpgtd" => encode_pcmpgtd(a(), b()),
        "pcmpgtq" => encode_pcmpgtq(a(), b()),
        // ---- immediate dword shifts (SATURATE at count >= 32) --------------
        "pslld" => encode_pslld_imm(a(), count_leaf(fact.imm.expect("pslld is an imm shift"))),
        "psrld" => encode_psrld_imm(a(), count_leaf(fact.imm.expect("psrld is an imm shift"))),
        "psrad" => encode_psrad_imm(a(), count_leaf(fact.imm.expect("psrad is an imm shift"))),
        _ => return None,
    };
    Some(e)
}

/// Evaluate an encoder expression to a concrete u128 (the SAME `try_eval`
/// evaluator the reconstruction `verify_by_evaluation` path uses). A packed result
/// is 128 bits, so it evaluates to EvalResult::Bv128.
fn eval_u128(expr: &SmtExpr) -> u128 {
    let env: HashMap<String, u64> = HashMap::new();
    match expr
        .try_eval(&env)
        .expect("bridge: packed encoder eval failed")
    {
        EvalResult::Bv128(v) => v,
        EvalResult::Bv(v) => v as u128, // a 128-bit op never narrows, but accept it
        other => panic!("bridge: packed encoder evaluated to non-bitvector {other:?}"),
    }
}

// ===========================================================================
// THE BRIDGE: every in-house packed encoder must match Rosetta on every fact.
// ===========================================================================
#[test]
fn x86_packed_inhouse_encoders_match_rosetta_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() > 10_000,
        "bridge: the Rosetta packed fixture is suspiciously small ({} facts) — truncated?",
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
    assert_eq!(value_facts, facts.len(), "value-fact count drift");
    assert_eq!(
        trap_facts, 0,
        "packed-SSE2 integer ops do not trap; expected 0 trap facts"
    );

    let mut mismatches: Vec<String> = Vec::new();
    let mut per_op: HashMap<String, usize> = HashMap::new();
    let mut per_op_mismatch: HashMap<String, usize> = HashMap::new();
    let mut checked = 0usize;

    for fact in &facts {
        *per_op.entry(fact.op.clone()).or_default() += 1;
        let expr = build_encoder(fact).unwrap_or_else(|| {
            panic!(
                "bridge: fixture op `{}` ({}) has no in-house encoder dispatch — the fixture and \
                 the bridge have drifted (every fixture op must map to an encoder, never silently \
                 unhandled)",
                fact.op, fact.theorem
            )
        });
        checked += 1;
        let got = eval_u128(&expr);
        if got != fact.result {
            *per_op_mismatch.entry(fact.op.clone()).or_default() += 1;
            if mismatches.len() < 40 {
                mismatches.push(format!(
                    "{}: op={} lane_bits={} a={:#034x} b={:#034x} imm={:?} -> in-house encoder gave \
                     {got:#034x}, Rosetta recorded {:#034x}",
                    fact.theorem, fact.op, fact.lane_bits, fact.a, fact.b, fact.imm, fact.result
                ));
            }
        }
    }

    // PER-OP accounting: every fixture op family must actually have been exercised
    // (no silent skip), and the count must be the full ~25-family packed grid.
    assert!(
        per_op.len() >= 25,
        "bridge: too few packed op families exercised ({}) — expected the full ~25-family x86 \
         packed-SSE2 grid",
        per_op.len()
    );
    assert_eq!(
        checked,
        facts.len(),
        "bridge: checked {checked} != {} total facts (silent skip)",
        facts.len()
    );

    // PER-OP mismatch accounting (no silent truncation of the finding report).
    if !per_op_mismatch.is_empty() {
        let mut summary: Vec<String> = per_op_mismatch
            .iter()
            .map(|(op, n)| format!("{op}={n}"))
            .collect();
        summary.sort();
        mismatches.push(format!("PER-OP mismatch counts: {}", summary.join(" ")));
    }

    assert!(
        mismatches.is_empty(),
        "B-x86-sse-packed BRIDGE FINDING: {} of {checked} in-house-packed-encoder vs Rosetta \
         comparisons MISMATCH. Each is a latent miscompile-class divergence between trust-cg's x86 \
         packed-SSE2 model and real x86 (Rosetta 2). First mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );

    eprintln!(
        "B-x86-sse-packed bridge: {checked} in-house-packed-encoder vs Rosetta comparisons PASS \
         across {} op families.",
        per_op.len()
    );
}

// ===========================================================================
// NON-VACUITY (teeth): deliberately-WRONG encoders MUST mismatch Rosetta, and
// the CORRECT encoder must match ALL facts of that family.
// ===========================================================================

/// Helper: does the in-house encoder agree with Rosetta on this fact?
fn encoder_matches(fact: &Fact) -> bool {
    match build_encoder(fact) {
        Some(expr) => eval_u128(&expr) == fact.result,
        None => false,
    }
}

#[test]
fn bridge_is_non_vacuous_paddd_as_psubd_mismatches_rosetta() {
    // Feed PADDD facts to the PSUBD encoder: it must NOT match Rosetta for at least
    // one fact (lane bvadd != lane bvsub on a non-degenerate input).
    let facts = load_facts();
    let add_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "paddd").collect();
    assert!(!add_facts.is_empty(), "expected PADDD facts in the fixture");

    // The CORRECT encoder matches ALL paddd facts (precondition for the teeth).
    for f in &add_facts {
        assert!(
            encoder_matches(f),
            "precondition: the correct PADDD encoder must match Rosetta on every PADDD fact ({})",
            f.theorem
        );
    }

    let mut found_divergence = false;
    for fact in &add_facts {
        let wrong = encode_psubd(leaf128(fact.a), leaf128(fact.b));
        if eval_u128(&wrong) != fact.result {
            found_divergence = true;
            break;
        }
    }
    assert!(
        found_divergence,
        "NON-VACUITY: a deliberately-wrong (PSUBD-for-PADDD) encoder matched Rosetta on EVERY \
         PADDD fact — the bridge would be a tautology / self-comparison. It must mismatch."
    );
}

#[test]
fn bridge_is_non_vacuous_pcmpeqd_as_pcmpgtd_mismatches_rosetta() {
    // Feed PCMPEQD facts to the PCMPGTD encoder: the equal-mask differs from the
    // signed-greater mask on at least one input (e.g. a == b yields all-ones for
    // EQ but all-zero for GT).
    let facts = load_facts();
    let eq_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "pcmpeqd").collect();
    assert!(
        !eq_facts.is_empty(),
        "expected PCMPEQD facts in the fixture"
    );

    for f in &eq_facts {
        assert!(
            encoder_matches(f),
            "precondition: the correct PCMPEQD encoder must match Rosetta on every PCMPEQD fact \
             ({})",
            f.theorem
        );
    }

    let mut found_divergence = false;
    for fact in &eq_facts {
        let wrong = encode_pcmpgtd(leaf128(fact.a), leaf128(fact.b));
        if eval_u128(&wrong) != fact.result {
            found_divergence = true;
            break;
        }
    }
    assert!(
        found_divergence,
        "NON-VACUITY: PCMPEQD-as-PCMPGTD (equal-mask for greater-mask) matched Rosetta on EVERY \
         PCMPEQD fact — the predicate distinction would not be load-bearing. It must MISMATCH \
         (a==b gives an all-ones EQ mask but an all-zero GT mask)."
    );
}

#[test]
fn bridge_is_non_vacuous_wrong_lane_width_paddb_as_paddw_mismatches_rosetta() {
    // A wrong-lane-WIDTH bug: PADDB (16x8-bit) emitted as PADDW (8x16-bit). The
    // carry crosses the 8-bit lane boundary in PADDW where PADDB has none, so they
    // DIVERGE whenever a byte-lane add carries into the next byte.
    let facts = load_facts();
    let paddb_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "paddb").collect();
    assert!(
        !paddb_facts.is_empty(),
        "expected PADDB facts in the fixture"
    );

    for f in &paddb_facts {
        assert!(
            encoder_matches(f),
            "precondition: the correct PADDB encoder must match Rosetta on every PADDB fact ({})",
            f.theorem
        );
    }

    let mut found_divergence = false;
    let mut witness = String::new();
    for fact in &paddb_facts {
        // Wrong lane width: treat the operands as 8x16-bit words instead of 16x8-bit
        // bytes. Where a byte-lane add would carry past bit 7, PADDW lets the carry
        // propagate into the next byte (no byte boundary), diverging from PADDB.
        let wrong = encode_paddw(leaf128(fact.a), leaf128(fact.b));
        if eval_u128(&wrong) != fact.result {
            found_divergence = true;
            witness = fact.theorem.clone();
            break;
        }
    }
    assert!(
        found_divergence,
        "NON-VACUITY: wrong-lane-width PADDB-as-PADDW matched Rosetta on EVERY PADDB fact — the \
         lane-width distinction would not be load-bearing. It must MISMATCH (a byte-lane carry \
         crosses the wrong boundary under i16 lanes)."
    );
    eprintln!("PADDB-as-PADDW teeth: wrong-lane-width diverges from Rosetta at {witness}");
}

#[test]
fn bridge_is_non_vacuous_unsaturated_shift_would_mismatch_at_count_ge_width() {
    // The packed imm-shift SATURATION contract (the OPPOSITE of the scalar SHL
    // &0x1f mask): at count >= 32 every dword lane saturates to 0 (PSLLD) / sign
    // (PSRAD). The FAITHFUL clamp encoder (encode_pslld_imm — bvshl, clamp-to-0)
    // AGREES; a hypothetical MASKED encoder (count & 0x1f, the scalar contract)
    // would DISAGREE. This proves (a) the bridge uses the right (clamp) encoder,
    // and (b) the Rosetta fixture genuinely encodes packed saturation, not a mask.
    let facts = load_facts();
    // Find a PSLLD fact whose count >= 32 and operand non-zero (so saturation to 0
    // differs from the masked result count&0x1f).
    let fact = facts
        .iter()
        .find(|f| f.op == "pslld" && f.imm == Some(32) && f.a != 0)
        .expect("expected a PSLLD fact with count==32 and nonzero operand");

    // The FAITHFUL clamp encoder matches Rosetta (saturation to 0 at count==32).
    let clamp = encode_pslld_imm(leaf128(fact.a), count_leaf(32));
    assert_eq!(
        eval_u128(&clamp),
        fact.result,
        "the FAITHFUL clamp (saturating) PSLLD encoder must match Rosetta at count>=32 ({})",
        fact.theorem
    );
    assert_eq!(
        fact.result, 0,
        "Rosetta PSLLD saturates each dword lane to 0 at count==32 (the saturation contract, NOT \
         a &0x1f mask which would shift by 0 = identity)"
    );
    // A MASKED encoder (count & 0x1f == 0 -> identity) would give back the nonzero
    // operand, DISAGREEING with Rosetta's 0 — proving the saturation/clamp choice
    // is load-bearing and the fixture is not a self-comparison.
    let masked_count = 32u32 & 0x1f; // == 0
    let masked = encode_pslld_imm(leaf128(fact.a), count_leaf(masked_count));
    assert_ne!(
        eval_u128(&masked),
        fact.result,
        "NON-VACUITY: a MASKED (count&0x1f) PSLLD encoder must DISAGREE with Rosetta at count==32 \
         — proving the Rosetta fixture encodes packed saturation (not the scalar &0x1f mask), and \
         that the bridge's choice of the clamp/saturating encoder is load-bearing"
    );
}

#[test]
fn bridge_is_non_vacuous_corrupted_fixture_result_mismatches() {
    // Take the first PADDQ fact, corrupt its recorded Rosetta result by +1, and
    // confirm the in-house encoder now DISAGREES — proving the assertion actually
    // compares against the fixture value (not against itself).
    let facts = load_facts();
    let fact = facts
        .iter()
        .find(|f| f.op == "paddq")
        .expect("a PADDQ fact");
    let corrupted = Fact {
        op: fact.op.clone(),
        lane_bits: fact.lane_bits,
        a: fact.a,
        b: fact.b,
        imm: fact.imm,
        result: fact.result.wrapping_add(1),
        theorem: fact.theorem.clone(),
    };
    assert!(
        encoder_matches(fact),
        "sanity: the genuine PADDQ fact must match the in-house encoder"
    );
    assert!(
        !encoder_matches(&corrupted),
        "NON-VACUITY: corrupting the recorded Rosetta result did NOT change the comparison outcome \
         — the bridge is not actually comparing against the fixture value"
    );
}
