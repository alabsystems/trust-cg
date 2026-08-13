// trust-cg-verify/tests/bdefs_differential_bridge_neon.rs — DELIVERABLE of the
// AArch64 NEON integer differential bridge (FRONTIER 2: extend the differential
// bridges to AArch64 NEON SIMD).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE B-aarch64-neon DIFFERENTIAL BRIDGE — the NEON analog of
// bdefs_differential_bridge.rs (the AArch64 integer silicon bridge).
// ===========================================================================
//
// This MIRRORS the AArch64 integer silicon bridge exactly, for trust-cg's NEON
// integer machine encoders. It defeats root-cause #2 of the lowering-equivalence
// TCB for the AArch64 NEON integer ops: BOTH sides of every NEON reconstruction
// check are validated against ONE in-house machine spec (neon_semantics.rs, the
// SmtExpr `encode_neon_*` encoders), so a SHARED misencoding in that spec is
// INVISIBLE to the equivalence check.
//
// HOW IT DEFEATS THAT: every fact in tests/fixtures/aarch64_neon_silicon_truth.json
// is a 128-bit result recorded from BARE SILICON — the host IS an Apple M4 (native
// AArch64), so the NEON oracle harness ran the ACTUAL instruction via
// `std::arch::asm!` over q-registers and read back the 128-bit result DIRECTLY
// (gen_aarch64_neon_silicon_truth.rs). This is the SAME oracle tier as the AArch64
// integer bridge (real M4 chip results) — STRICTLY ABOVE the Rosetta/qemu tier the
// x86/RISC-V bridges use. For each fact this test:
//
//   1. takes the op + arrangement + the silicon 128-bit operand literals (and the
//      imm/scalar/lane for the shift/dup/ins/movi families),
//   2. constructs trust-cg's OWN in-house NEON SmtExpr encoder for that op (the
//      SAME `encode_neon_*` encoders the reconstruction machine side uses), with
//      the operands as concrete 128-bit `Bv128` constant leaves (built as
//      concat(bv_const(hi,64), bv_const(lo,64)) — the same v128 construction the
//      reconstruction tests use),
//   3. evaluates it through the SAME SmtExpr `try_eval` evaluator the
//      reconstruction `verify_by_evaluation` path uses (yielding an
//      EvalResult::Bv128 for a 128-bit op, or Bv for a 64-bit-arrangement op), and
//   4. asserts the EVALUATED 128-bit result EQUALS the SILICON-recorded result.
//
// A mismatch is a FINDING (a latent miscompile-class bug, or a convention
// divergence). It is NOT papered over by excluding the op or loosening the
// comparison. The bridge is NON-VACUOUS: the `bridge_is_non_vacuous_*` tests below
// prove deliberately-WRONG encoders mismatch a silicon fact (ADD-as-SUB, the wrong
// ARRANGEMENT ADD.16B-as-ADD.8H so a byte-lane carry crosses the wrong boundary,
// and CMGT-as-CMGE on an equal lane), so the bridge has teeth — it is not a
// tautology and not a self-comparison.
//
// CONVENTIONS (exactly where mismatches surface — all validated here):
//   * 64-bit (D-register) arrangements (.8B/.4H/.2S) produce a 64-bit result; the
//     hardware ZEROES the upper 64 bits of the q-register, so the silicon 128-bit
//     readback has zero in bits [127:64]. The in-house 64-bit encoder builds a
//     64-bit SmtExpr (lane_concat of 64 bits total) that evaluates to that low-64
//     value; the bridge compares it against the silicon low 64 bits AND asserts the
//     silicon upper 64 bits are zero (the D-register zeroing contract).
//   * COMPARE ops (CMEQ/CMGT/CMGE) produce per-lane ALL-ONES / ALL-ZERO masks.
//     CMGT/CMGE are SIGNED; CMEQ is bit-equality.
//   * SHL is encoded with bvshl (no count mask); USHR=bvlshr, SSHR=bvashr. The
//     try_eval lane evaluator CLAMPS a shift >= lane width to 0 (USHR/SHL) or to
//     the sign fill (SSHR) — which is EXACTLY what NEON does at amount == lane
//     width (the only >= case the encoding allows), so the bridge validates the
//     clamp against silicon at amount == lane width.
//   * DUP/INS/MOVI/UMAXV take an imm / lane index / scalar / are a cross-lane
//     reduction (NOT a second vector). They are BRIDGED here (NOT deferred) by
//     feeding the matching encoder the SAME imm/lane/scalar the silicon harness
//     used (the x86 imul_imm/LEA fixed-imm pattern): DUP broadcasts the recorded
//     scalar, INS inserts the recorded scalar at the recorded lane, MOVI uses the
//     recorded 8-bit imm, UMAXV reduces .4S to the recorded 32-bit scalar.

use std::collections::HashMap;

use serde_json::Value;

use trust_cg_verify::neon_semantics::{
    encode_neon_add, encode_neon_and, encode_neon_bic, encode_neon_cmeq, encode_neon_cmge,
    encode_neon_cmgt, encode_neon_dup, encode_neon_eor, encode_neon_ins, encode_neon_mla,
    encode_neon_movi, encode_neon_mul, encode_neon_neg, encode_neon_not, encode_neon_orr,
    encode_neon_shl, encode_neon_smax, encode_neon_smin, encode_neon_sshr, encode_neon_sub,
    encode_neon_umax, encode_neon_umaxv_4s, encode_neon_umin, encode_neon_ushr,
};
use trust_cg_verify::smt::{EvalResult, SmtExpr, VectorArrangement};

const FIXTURE: &str = include_str!("fixtures/aarch64_neon_silicon_truth.json");

/// A single NEON bare-silicon ground-truth fact (one M4 NEON readback).
struct Fact {
    op: String,
    arrangement: String,
    kind: String,
    lane_bits: u32,
    total_bits: u32,
    a: u128,
    b: u128,
    c: u128,
    imm: i64,
    scalar: u128,
    result: u128,
    theorem: String,
}

fn parse_hex_u128(v: &Value) -> u128 {
    let s = v.as_str().expect("hex field is a string");
    let h = s.strip_prefix("0x").unwrap_or(s);
    u128::from_str_radix(h, 16).expect("hex parses to u128")
}

fn load_facts() -> Vec<Fact> {
    let doc: Value = serde_json::from_str(FIXTURE).expect("fixture is valid JSON");
    let arr = doc["facts"]
        .as_array()
        .expect("fixture has a `facts` array");
    arr.iter()
        .map(|f| Fact {
            op: f["op"].as_str().expect("op is a string").to_string(),
            arrangement: f["arrangement"]
                .as_str()
                .expect("arrangement is a string")
                .to_string(),
            kind: f["kind"].as_str().expect("kind is a string").to_string(),
            lane_bits: f["lane_bits"].as_u64().expect("lane_bits") as u32,
            total_bits: f["total_bits"].as_u64().expect("total_bits") as u32,
            a: parse_hex_u128(&f["a"]),
            b: parse_hex_u128(&f["b"]),
            c: parse_hex_u128(&f["c"]),
            imm: f["imm"].as_i64().expect("imm is a number"),
            scalar: parse_hex_u128(&f["scalar"]),
            result: parse_hex_u128(&f["result"]),
            theorem: f["theorem"]
                .as_str()
                .expect("theorem is a string")
                .to_string(),
        })
        .collect()
}

/// The accounting block (no silent truncation).
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

fn arrangement_of(name: &str) -> VectorArrangement {
    match name {
        "8b" => VectorArrangement::B8,
        "16b" => VectorArrangement::B16,
        "4h" => VectorArrangement::H4,
        "8h" => VectorArrangement::H8,
        "2s" => VectorArrangement::S2,
        "4s" => VectorArrangement::S4,
        "2d" => VectorArrangement::D2,
        other => panic!("bridge: unknown arrangement `{other}`"),
    }
}

/// A `width`-bit constant leaf carrying the low `width` bits of `v`. For a 128-bit
/// vector this is concat(bv_const(hi,64), bv_const(lo,64)); for a 64-bit vector it
/// is a single 64-bit `bv_const` (the same v128/v64 construction the encoders'
/// own tests use).
fn leaf(v: u128, width: u32) -> SmtExpr {
    if width <= 64 {
        SmtExpr::bv_const(v as u64, width)
    } else {
        let lo = (v & 0xFFFF_FFFF_FFFF_FFFF) as u64;
        let hi = (v >> 64) as u64;
        // hi width is total-64; for the 128-bit NEON case that is 64.
        SmtExpr::bv_const(hi, width - 64).concat(SmtExpr::bv_const(lo, 64))
    }
}

/// Build the trust-cg IN-HOUSE NEON encoder SmtExpr for `fact`. Returns `None` for
/// an op tag the bridge does not encode (should never happen — the fixture only
/// contains in-house-encoded ops; an unknown tag is a fixture/bridge drift bug).
fn build_encoder(fact: &Fact) -> Option<SmtExpr> {
    let arr = arrangement_of(&fact.arrangement);
    let w = fact.total_bits;
    let a = leaf(fact.a, w);
    let b = leaf(fact.b, w);
    let e = match (fact.op.as_str(), fact.kind.as_str()) {
        // ---- arithmetic ----
        ("add", _) => encode_neon_add(arr, &a, &b),
        ("sub", _) => encode_neon_sub(arr, &a, &b),
        ("mul", _) => encode_neon_mul(arr, &a, &b),
        ("neg", _) => encode_neon_neg(arr, &a),
        // ---- bitwise (width-agnostic) ----
        ("and", _) => encode_neon_and(&a, &b),
        ("orr", _) => encode_neon_orr(&a, &b),
        ("eor", _) => encode_neon_eor(&a, &b),
        ("bic", _) => encode_neon_bic(&a, &b),
        ("not", _) => encode_neon_not(&a),
        // ---- compare ----
        ("cmeq", _) => encode_neon_cmeq(arr, &a, &b),
        ("cmgt", _) => encode_neon_cmgt(arr, &a, &b),
        ("cmge", _) => encode_neon_cmge(arr, &a, &b),
        // ---- min / max ----
        ("smin", _) => encode_neon_smin(arr, &a, &b),
        ("umin", _) => encode_neon_umin(arr, &a, &b),
        ("smax", _) => encode_neon_smax(arr, &a, &b),
        ("umax", _) => encode_neon_umax(arr, &a, &b),
        // ---- multiply-accumulate: silicon va=c, vn=a, vm=b ----
        ("mla", _) => {
            let va = leaf(fact.c, w);
            encode_neon_mla(arr, &va, &a, &b)
        }
        // ---- shifts: imm amount from the fixture ----
        ("shl", _) => encode_neon_shl(arr, &a, fact.imm as u32),
        ("ushr", _) => encode_neon_ushr(arr, &a, fact.imm as u32),
        ("sshr", _) => encode_neon_sshr(arr, &a, fact.imm as u32),
        // ---- dup: broadcast the recorded scalar (32-bit for non-2D, 64-bit 2D) -
        ("dup", _) => {
            let sw = fact.lane_bits.clamp(32, 64); // dup-from-greg reads a W or X
            let scalar = if fact.lane_bits >= 64 {
                SmtExpr::bv_const(fact.scalar as u64, 64)
            } else {
                SmtExpr::bv_const(fact.scalar as u64, sw)
            };
            encode_neon_dup(arr, &scalar)
        }
        // ---- ins: insert the recorded scalar at the recorded lane ----
        ("ins", _) => {
            let lane = fact.imm as u32;
            let new_lane = SmtExpr::bv_const(fact.scalar as u64, fact.lane_bits);
            encode_neon_ins(&a, arr, lane, new_lane)
        }
        // ---- movi: 8-bit imm broadcast over total_bits ----
        ("movi", _) => encode_neon_movi(fact.total_bits, fact.imm as u8),
        // ---- umaxv: .4S cross-lane reduction to a 32-bit scalar ----
        ("umaxv", _) => encode_neon_umaxv_4s(&a),
        _ => return None,
    };
    Some(e)
}

/// Evaluate an encoder expression to a concrete u128 (the SAME `try_eval`
/// evaluator the reconstruction `verify_by_evaluation` path uses). A 128-bit op
/// evaluates to Bv128; a 64-bit-arrangement op (or a scalar reduction) evaluates
/// to Bv.
fn eval_u128(expr: &SmtExpr) -> u128 {
    let env: HashMap<String, u64> = HashMap::new();
    match expr
        .try_eval(&env)
        .expect("bridge: NEON encoder eval failed")
    {
        EvalResult::Bv128(v) => v,
        EvalResult::Bv(v) => v as u128,
        other => panic!("bridge: NEON encoder evaluated to non-bitvector {other:?}"),
    }
}

/// Does the in-house encoder agree with silicon on this fact? For a 64-bit
/// arrangement the encoder yields the low 64 bits and silicon zeroes the upper 64;
/// agreement requires (a) low-64 match AND (b) silicon upper-64 == 0.
fn encoder_matches(fact: &Fact) -> bool {
    let expr = match build_encoder(fact) {
        Some(e) => e,
        None => return false,
    };
    let got = eval_u128(&expr);
    expected_eq(fact, got)
}

/// Compare an evaluated encoder result `got` against the silicon `fact.result`,
/// honoring the 64-bit-arrangement D-register upper-half zeroing contract.
fn expected_eq(fact: &Fact, got: u128) -> bool {
    if fact.total_bits >= 128 {
        got == fact.result
    } else {
        // 64-bit arrangement: encoder gives low 64 bits; silicon upper 64 == 0.
        let lo_mask: u128 = 0xFFFF_FFFF_FFFF_FFFF;
        (fact.result >> 64) == 0 && (got & lo_mask) == (fact.result & lo_mask)
    }
}

// ===========================================================================
// THE BRIDGE: every in-house NEON encoder must match silicon on every fact.
// ===========================================================================
#[test]
fn aarch64_neon_inhouse_encoders_match_silicon_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() > 10_000,
        "bridge: the NEON silicon fixture is suspiciously small ({} facts) — truncated?",
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
        "integer NEON ops do not trap; expected 0 trap facts"
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
        if !expected_eq(fact, got) {
            *per_op_mismatch.entry(fact.op.clone()).or_default() += 1;
            if mismatches.len() < 40 {
                mismatches.push(format!(
                    "{}: op={}.{} kind={} a={:#034x} b={:#034x} c={:#034x} imm={} scalar={:#034x} \
                     -> in-house encoder gave {got:#034x}, silicon recorded {:#034x}",
                    fact.theorem,
                    fact.op,
                    fact.arrangement,
                    fact.kind,
                    fact.a,
                    fact.b,
                    fact.c,
                    fact.imm,
                    fact.scalar,
                    fact.result
                ));
            }
        }
    }

    // PER-OP accounting: every one of the 24 in-house NEON integer families must
    // actually have been exercised (no silent skip).
    assert_eq!(
        per_op.len(),
        24,
        "bridge: expected exactly the 24 in-house NEON integer families to be exercised, saw {} \
         ({:?})",
        per_op.len(),
        {
            let mut v: Vec<&String> = per_op.keys().collect();
            v.sort();
            v
        }
    );
    // The 24 families, named explicitly so a dropped family is a hard failure.
    for fam in [
        "add", "sub", "mul", "neg", "and", "orr", "eor", "bic", "not", "cmeq", "cmgt", "cmge",
        "smin", "umin", "smax", "umax", "mla", "dup", "ins", "movi", "shl", "ushr", "sshr",
        "umaxv",
    ] {
        assert!(
            per_op.contains_key(fam),
            "bridge: NEON family `{fam}` is MISSING from the fixture — it must be exercised, not \
             silently dropped"
        );
    }
    assert_eq!(
        checked,
        facts.len(),
        "bridge: checked {checked} != {} total facts (silent skip)",
        facts.len()
    );

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
        "B-aarch64-neon BRIDGE FINDING: {} of {checked} in-house-NEON-encoder vs M4-silicon \
         comparisons MISMATCH. Each is a latent miscompile-class divergence between trust-cg's \
         AArch64 NEON model and the real Apple M4. First mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );

    eprintln!(
        "B-aarch64-neon bridge: {checked} in-house-NEON-encoder vs M4-silicon comparisons PASS \
         across {} integer NEON families.",
        per_op.len()
    );
}

// ===========================================================================
// NON-VACUITY (teeth): deliberately-WRONG encoders MUST mismatch silicon, and
// the CORRECT encoder must match ALL facts of that family.
// ===========================================================================

#[test]
fn bridge_is_non_vacuous_add_as_sub_mismatches_silicon() {
    // Feed ADD facts to the SUB encoder: it must NOT match silicon for at least one
    // fact (lane bvadd != lane bvsub on a non-degenerate input).
    let facts = load_facts();
    let add_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "add").collect();
    assert!(!add_facts.is_empty(), "expected ADD facts in the fixture");

    // PRECONDITION: the correct ADD encoder matches ALL add facts.
    for f in &add_facts {
        assert!(
            encoder_matches(f),
            "precondition: the correct ADD encoder must match silicon on every ADD fact ({})",
            f.theorem
        );
    }

    let mut found = false;
    for fact in &add_facts {
        let arr = arrangement_of(&fact.arrangement);
        let w = fact.total_bits;
        let wrong = encode_neon_sub(arr, &leaf(fact.a, w), &leaf(fact.b, w));
        if !expected_eq(fact, eval_u128(&wrong)) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: a deliberately-wrong (SUB-for-ADD) encoder matched silicon on EVERY ADD fact \
         — the bridge would be a tautology / self-comparison. It must mismatch."
    );
}

#[test]
fn bridge_is_non_vacuous_wrong_arrangement_add16b_as_add8h_mismatches_silicon() {
    // A wrong-ARRANGEMENT bug: ADD.16B (16x8-bit) emitted as ADD.8H (8x16-bit). The
    // carry crosses the 8-bit lane boundary in .8H where .16B has none, so they
    // DIVERGE whenever a byte-lane add carries into the next byte.
    let facts = load_facts();
    let add16b: Vec<&Fact> = facts
        .iter()
        .filter(|f| f.op == "add" && f.arrangement == "16b")
        .collect();
    assert!(!add16b.is_empty(), "expected ADD.16B facts in the fixture");

    for f in &add16b {
        assert!(
            encoder_matches(f),
            "precondition: the correct ADD.16B encoder must match silicon on every ADD.16B fact \
             ({})",
            f.theorem
        );
    }

    let mut found = false;
    let mut witness = String::new();
    for fact in &add16b {
        // Wrong arrangement: treat the 128-bit operands as 8x16-bit instead of
        // 16x8-bit. Where a byte-lane add would carry past bit 7, .8H lets the carry
        // propagate into the next byte (no byte boundary), diverging from .16B.
        let wrong = encode_neon_add(
            VectorArrangement::H8,
            &leaf(fact.a, 128),
            &leaf(fact.b, 128),
        );
        if !expected_eq(fact, eval_u128(&wrong)) {
            found = true;
            witness = fact.theorem.clone();
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: wrong-arrangement ADD.16B-as-ADD.8H matched silicon on EVERY ADD.16B fact — \
         the lane-width distinction would not be load-bearing. It must MISMATCH (a byte-lane carry \
         crosses the wrong boundary under .8H lanes)."
    );
    eprintln!("ADD.16B-as-ADD.8H teeth: wrong arrangement diverges from silicon at {witness}");
}

#[test]
fn bridge_is_non_vacuous_cmgt_as_cmge_mismatches_silicon_on_equal_lane() {
    // Feed CMGT facts to the CMGE encoder: on an EQUAL lane CMGT gives all-zero but
    // CMGE gives all-ones, so they DIVERGE. (The fixture grid includes uniform
    // vectors where every lane of a == b — guaranteeing an equal lane exists.)
    let facts = load_facts();
    let cmgt: Vec<&Fact> = facts.iter().filter(|f| f.op == "cmgt").collect();
    assert!(!cmgt.is_empty(), "expected CMGT facts in the fixture");

    for f in &cmgt {
        assert!(
            encoder_matches(f),
            "precondition: the correct CMGT encoder must match silicon on every CMGT fact ({})",
            f.theorem
        );
    }

    let mut found = false;
    let mut witness = String::new();
    for fact in &cmgt {
        let arr = arrangement_of(&fact.arrangement);
        let w = fact.total_bits;
        let wrong = encode_neon_cmge(arr, &leaf(fact.a, w), &leaf(fact.b, w));
        if !expected_eq(fact, eval_u128(&wrong)) {
            found = true;
            witness = fact.theorem.clone();
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: CMGT-as-CMGE matched silicon on EVERY CMGT fact — the strict-vs-nonstrict \
         predicate distinction would not be load-bearing. It must MISMATCH on an equal lane (CMGT \
         gives 0, CMGE gives all-ones)."
    );
    eprintln!("CMGT-as-CMGE teeth: predicate distinction diverges from silicon at {witness}");
}

#[test]
fn bridge_is_non_vacuous_corrupted_fixture_result_mismatches() {
    // Take the first MUL fact with a nonzero result, corrupt its recorded silicon
    // result by +1, and confirm the in-house encoder now DISAGREES — proving the
    // assertion actually compares against the fixture value (not against itself).
    let facts = load_facts();
    let fact = facts
        .iter()
        .find(|f| f.op == "mul" && f.result != 0)
        .expect("a MUL fact with a nonzero result");
    let corrupted = Fact {
        op: fact.op.clone(),
        arrangement: fact.arrangement.clone(),
        kind: fact.kind.clone(),
        lane_bits: fact.lane_bits,
        total_bits: fact.total_bits,
        a: fact.a,
        b: fact.b,
        c: fact.c,
        imm: fact.imm,
        scalar: fact.scalar,
        result: fact.result.wrapping_add(1),
        theorem: fact.theorem.clone(),
    };
    assert!(
        encoder_matches(fact),
        "sanity: the genuine MUL fact must match the in-house encoder"
    );
    assert!(
        !encoder_matches(&corrupted),
        "NON-VACUITY: corrupting the recorded silicon result did NOT change the comparison outcome \
         — the bridge is not actually comparing against the fixture value"
    );
}

#[test]
fn bridge_is_non_vacuous_dup_ins_movi_umaxv_are_bridged_not_deferred() {
    // The imm/lane/scalar/reduction families (dup/ins/movi/umaxv) are BRIDGED, not
    // honest-deferred. Confirm each has facts AND its correct encoder matches ALL
    // of them (so the bridge genuinely exercises them, the x86 imul_imm pattern).
    let facts = load_facts();
    for fam in ["dup", "ins", "movi", "umaxv"] {
        let fam_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == fam).collect();
        assert!(
            !fam_facts.is_empty(),
            "the imm/lane/scalar family `{fam}` must be present in the fixture (bridged, not dropped)"
        );
        for f in &fam_facts {
            assert!(
                encoder_matches(f),
                "the correct `{fam}` encoder must match silicon on every `{fam}` fact ({})",
                f.theorem
            );
        }
    }

    // And prove the umaxv reduction is load-bearing: a fact whose lanes are NOT all
    // equal must reduce to the (unique) max lane, NOT lane 0. Find one and confirm
    // the encoder produces the silicon max (which differs from a "just take lane 0"
    // wrong reduction).
    let umaxv: Vec<&Fact> = facts.iter().filter(|f| f.op == "umaxv").collect();
    let mut found_nontrivial = false;
    for f in &umaxv {
        let lane0 = f.a & 0xFFFF_FFFF;
        if f.result != lane0 {
            // silicon picked a non-lane-0 max; the encoder must agree (and a
            // lane-0-only wrong reduction would disagree).
            assert!(
                encoder_matches(f),
                "umaxv encoder must match the silicon cross-lane max ({})",
                f.theorem
            );
            assert_ne!(
                f.result, lane0,
                "this fact is the non-trivial witness; result != lane0 by construction"
            );
            found_nontrivial = true;
            break;
        }
    }
    assert!(
        found_nontrivial,
        "NON-VACUITY: every UMAXV fact had its max in lane 0 — the cross-lane reduction would not \
         be load-bearing. The grid must include a vector whose max is NOT lane 0."
    );
}

#[test]
fn bridge_is_non_vacuous_d_register_zeroes_upper_half() {
    // The 64-bit-arrangement D-register zeroing contract is load-bearing: every
    // .8B/.4H/.2S (total_bits==64) silicon fact must have ZERO in bits [127:64].
    // (If the harness had read back garbage in the upper half, expected_eq would be
    // hiding a bug; this asserts the contract directly.)
    let facts = load_facts();
    let mut count64 = 0usize;
    for f in &facts {
        if f.total_bits == 64 {
            count64 += 1;
            assert_eq!(
                f.result >> 64,
                0,
                "64-bit arrangement {}.{} ({}) must zero the upper 64 bits of the q-register, but \
                 silicon recorded {:#034x}",
                f.op,
                f.arrangement,
                f.theorem,
                f.result
            );
        }
    }
    assert!(
        count64 > 100,
        "expected many 64-bit-arrangement facts (.8B/.4H/.2S); saw {count64}"
    );
}
