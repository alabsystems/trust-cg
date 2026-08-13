// trust-cg-verify/tests/bdefs_differential_bridge_riscv_fp.rs — DELIVERABLE of
// #96 (FRONTIER 2: extend the differential bridges to RISC-V F/D scalar FP).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE B-riscv-fp DIFFERENTIAL BRIDGE — the RISC-V scalar-FP analog of
// bdefs_differential_bridge_riscv.rs (RV64 integer ALU vs qemu) and the RISC-V
// dual of bdefs_differential_bridge_x86_fp.rs (x86 scalar-FP vs Rosetta) +
// fp_bitmodel_bridge.rs (the AArch64 integer-only FP model vs silicon).
// ===========================================================================
//
// This validates trust-cg's IN-HOUSE RISC-V F/D scalar-FP SmtExpr encoders
// (riscv_semantics.rs: encode_fadd/fsub/fmul/fdiv/fsqrt (.d/.s), encode_feq/flt/
// fle, encode_fmin/fmax (the RISC-V IEEE-2019 minimumNumber/maximumNumber),
// encode_fsgnj*/encode_fcvt_to_int_*/encode_fcvt_from_int_*/encode_fcvt_fp_to_fp)
// against an INDEPENDENT RISC-V executor — qemu-system-riscv64, a SOFTWARE GOLDEN
// MODEL of the RV64 ISA, NOT a second in-house model.
//
// Those encoders build SmtExpr::FPAdd/FPSub/FPMul/FPDiv/FPSqrt + the fp.to_sbv/
// to_fp converts + ite(fp_lt/fp_eq/fp_is_nan) trees, which `try_eval` evaluates
// through the SILICON-VALIDATED INTEGER-ONLY fp_bitmodel.rs (host FPU EVICTED for
// f32/f64 arithmetic — #89/#91/#94). So this bridge cross-checks that integer-only
// model against an INDEPENDENT real RISC-V executor, AT RISC-V SEMANTICS,
// defeating root-cause #2 for the RV64 scalar-FP ops.
//
// HOW: every fact in tests/fixtures/riscv_fp_qemu_truth.json is a RAW-BIT result
// recorded from qemu decoding+executing a real RV64 F/D instruction word over an
// IEEE EDGE GRID (+-0, +-Inf, qNaN, sNaN, subnormals, min/max normal, ties; an
// integer edge grid for the converts). For each fact this test builds the in-house
// encoder with the operands as concrete FPConst / BvConst leaves, evals via the
// SAME try_eval the reconstruction uses, recovers the RESULT BITS (f64: to_bits();
// f32: the integer-only fcvt_narrow of the f64 carrier — the exact narrow the
// eviction uses; f->int / FEQ/FLT/FLE: the Bv), and asserts they EQUAL the qemu
// result bits.
//
// ===========================================================================
// RISC-V-SPECIFIC SEMANTICS — modeled AS RISC-V (NOT x86 MINSD, NOT ARM FMINNM):
// ===========================================================================
//   * FMIN/FMAX = IEEE-754-2019 minimumNumber/maximumNumber: a lone NaN (incl
//     sNaN) returns the NUMBER; both NaN -> the CANONICAL qNaN (0x7fc0../0x7ff8..);
//     -0 < +0. Validated bit-exact against qemu. (x86 MINSD returns the SECOND
//     operand on unordered; ARM FMINNM forces NaN on an sNaN input — both WRONG
//     for RISC-V, and the non-vacuity teeth prove modeling them that way mismatches.)
//   * FCVT-to-int SATURATES with NaN -> max: signed NaN -> INT_MAX (2^(w-1)-1),
//     unsigned NaN -> UINT_MAX; +-overflow -> INT_MAX/INT_MIN (signed) or
//     UINT_MAX/0 (unsigned). The encoder wraps the shared (NaN->0) FPToSBv/FPToUBv
//     evaluator in a RISC-V NaN-fixup ite, so the RISC-V NaN convention is modeled
//     EXACTLY (not deferred). Validated bit-exact against qemu.
//   * All NaN-producing ops emit the canonical NaN (0x7fc0../0x7ff8..) — RISC-V
//     does NOT propagate input NaN payloads (Section 11.3).
//
// ===========================================================================
// HONESTLY-CLASSIFIED RESIDUALS (NONE papered over; the NaN comparison is NEVER
// loosened to hide a wrong non-NaN VALUE — a non-NaN mismatch, or a NaN-vs-non-NaN
// mismatch, is ALWAYS a HARD failure):
// ===========================================================================
//   (R1) f32 FCVT residual (the already-registered B-aarch64-fp-pending residual).
//        int->f32 (BvToFP), f32->f-format (FPToFP), and f32-source f->int
//        (FPToSBv/FPToUBv) still use the NATIVE `as f32`/`as i32` casts in the
//        evaluator (the integer-only f32 FCVT carrier is honest-deferred). For the
//        RISC-V f32 converts these casts are Rust's saturating semantics, which can
//        DIVERGE from RISC-V on the NaN/overflow edges. COUNTED, never hidden: a
//        deferred f32-FCVT divergence is recorded only when the model produced a
//        DIFFERENT-but-explainable value (NaN-fixup or saturation edge) for an f32
//        FCVT op; every f32-FCVT IN-RANGE conversion is STRICTLY matched.
//   (R2) NaN-payload-through-carrier for f32 (the F2 of the x86 bridge): an f32 op
//        whose RESULT is a NaN may have its payload quieted by the f64 eval carrier.
//        RISC-V always emits the CANONICAL qNaN, and the model's f32 NaN results are
//        canonical too, so this is essentially never hit for RISC-V (the canonical
//        NaN survives the carrier) — but a NaN-vs-NaN-of-same-width payload
//        difference is classified here rather than treated as a hard failure.

use std::collections::HashMap;

use serde_json::Value;

use trust_cg_verify::fp_bitmodel;
use trust_cg_verify::riscv_semantics::{
    RiscVFpFormat, encode_fadd, encode_fcvt_fp_to_fp, encode_fcvt_from_int_signed,
    encode_fcvt_to_int_signed, encode_fcvt_to_int_unsigned, encode_fdiv, encode_feq, encode_fle,
    encode_flt, encode_fmax, encode_fmin, encode_fmul, encode_fsgnj_bits, encode_fsgnjn_bits,
    encode_fsgnjx_bits, encode_fsqrt, encode_fsub,
};
use trust_cg_verify::smt::{EvalResult, SmtExpr};

const FIXTURE: &str = include_str!("fixtures/riscv_fp_qemu_truth.json");

/// A single qemu FP ground-truth fact (one independent-RV64 recorded result).
struct Fact {
    op: String,
    fmt: String, // "s" or "d"
    in_bits: Vec<u64>,
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
        .map(|f| Fact {
            op: f["op"].as_str().expect("op").to_string(),
            fmt: f["fmt"].as_str().expect("fmt").to_string(),
            in_bits: f["in_bits"]
                .as_array()
                .expect("in_bits array")
                .iter()
                .map(parse_hex)
                .collect(),
            result: parse_hex(&f["result"]),
            result_width: f["result_width"].as_u64().expect("result_width") as u32,
            theorem: f["theorem"].as_str().expect("theorem").to_string(),
        })
        .collect()
}

fn parse_hex(v: &Value) -> u64 {
    let s = v.as_str().expect("hex string");
    let h = s.strip_prefix("0x").unwrap_or(s);
    u64::from_str_radix(h, 16).expect("hex parses")
}

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

fn fmt_of(s: &str) -> RiscVFpFormat {
    match s {
        "s" => RiscVFpFormat::S,
        "d" => RiscVFpFormat::D,
        other => panic!("bridge: unexpected fmt `{other}`"),
    }
}

/// An FP constant leaf carrying the raw `bits` of an `s`/`d` value.
fn fp_leaf(bits: u64, fmt: RiscVFpFormat) -> SmtExpr {
    match fmt {
        RiscVFpFormat::S => SmtExpr::fp_const(bits & 0xFFFF_FFFF, 8, 24),
        RiscVFpFormat::D => SmtExpr::fp_const(bits, 11, 53),
    }
}

/// The width of the source FP format for a `fcvt.*.<src>` int<-fp or fp-fp op,
/// derived from the fmt tag (which records the SOURCE format here).
fn src_int_width_for_fcvt_from_int(op: &str) -> u32 {
    // fcvt.<d|s>.<w|wu|l|lu> — the source integer width is the trailing token.
    if op.ends_with(".w") || op.ends_with(".wu") {
        32
    } else {
        64
    }
}

/// Build the in-house RISC-V FP encoder for `fact`. Returns None only for an op
/// the bridge does not dispatch (a fixture/bridge drift, caught by the unwrap).
fn build_encoder(fact: &Fact) -> Option<SmtExpr> {
    let fmt = fmt_of(&fact.fmt);
    let o = &fact.in_bits;
    let a = || fp_leaf(o[0], fmt);
    let b = || fp_leaf(o[1], fmt);
    let w = fmt.bits();
    let e = match fact.op.as_str() {
        // ---- binary arithmetic ----
        "fadd.d" | "fadd.s" => encode_fadd(fmt, a(), b()),
        "fsub.d" | "fsub.s" => encode_fsub(fmt, a(), b()),
        "fmul.d" | "fmul.s" => encode_fmul(fmt, a(), b()),
        "fdiv.d" | "fdiv.s" => encode_fdiv(fmt, a(), b()),
        // ---- unary sqrt ----
        "fsqrt.d" | "fsqrt.s" => encode_fsqrt(fmt, a()),
        // ---- RISC-V IEEE-2019 minimumNumber/maximumNumber ----
        "fmin.d" | "fmin.s" => encode_fmin(fmt, a(), b()),
        "fmax.d" | "fmax.s" => encode_fmax(fmt, a(), b()),
        // ---- sign injection (raw bitvector operands) ----
        "fsgnj.d" | "fsgnj.s" => {
            encode_fsgnj_bits(fmt, SmtExpr::bv_const(o[0], w), SmtExpr::bv_const(o[1], w))
        }
        "fsgnjn.d" | "fsgnjn.s" => {
            encode_fsgnjn_bits(fmt, SmtExpr::bv_const(o[0], w), SmtExpr::bv_const(o[1], w))
        }
        "fsgnjx.d" | "fsgnjx.s" => {
            encode_fsgnjx_bits(fmt, SmtExpr::bv_const(o[0], w), SmtExpr::bv_const(o[1], w))
        }
        // ---- comparisons (1-bit GPR result) ----
        "feq.d" | "feq.s" => encode_feq(fmt, a(), b()),
        "flt.d" | "flt.s" => encode_flt(fmt, a(), b()),
        "fle.d" | "fle.s" => encode_fle(fmt, a(), b()),
        // ---- FCVT f -> signed int (RISC-V saturating, NaN -> INT_MAX) ----
        "fcvt.w.d" | "fcvt.w.s" => encode_fcvt_to_int_signed(32, a()),
        "fcvt.l.d" | "fcvt.l.s" => encode_fcvt_to_int_signed(64, a()),
        // ---- FCVT f -> unsigned int (RISC-V saturating, NaN -> UINT_MAX) ----
        "fcvt.wu.d" | "fcvt.wu.s" => encode_fcvt_to_int_unsigned(32, a()),
        "fcvt.lu.d" | "fcvt.lu.s" => encode_fcvt_to_int_unsigned(64, a()),
        // ---- FCVT signed int -> f ----
        // fcvt.<dst>.<w|l>: dst from the prefix, src int width from the suffix.
        "fcvt.d.w" | "fcvt.d.l" => encode_fcvt_from_int_signed(
            RiscVFpFormat::D,
            SmtExpr::bv_const(o[0], src_int_width_for_fcvt_from_int(&fact.op)),
        ),
        "fcvt.s.w" | "fcvt.s.l" => encode_fcvt_from_int_signed(
            RiscVFpFormat::S,
            SmtExpr::bv_const(o[0], src_int_width_for_fcvt_from_int(&fact.op)),
        ),
        // ---- FCVT unsigned int -> f (zero-extend by one bit-width so the
        //      signed BvToFP interpretation yields the non-negative magnitude,
        //      matching x86 CVTSI2SD/AArch64 UCVTF idiom) ----
        "fcvt.d.wu" => encode_fcvt_from_int_signed(RiscVFpFormat::D, zext_unsigned(o[0], 32)),
        "fcvt.d.lu" => encode_fcvt_from_int_signed(RiscVFpFormat::D, zext_unsigned(o[0], 64)),
        "fcvt.s.wu" => encode_fcvt_from_int_signed(RiscVFpFormat::S, zext_unsigned(o[0], 32)),
        "fcvt.s.lu" => encode_fcvt_from_int_signed(RiscVFpFormat::S, zext_unsigned(o[0], 64)),
        // ---- FCVT fp <-> fp ----
        "fcvt.s.d" => encode_fcvt_fp_to_fp(RiscVFpFormat::S, fp_leaf(o[0], RiscVFpFormat::D)),
        "fcvt.d.s" => encode_fcvt_fp_to_fp(RiscVFpFormat::D, fp_leaf(o[0], RiscVFpFormat::S)),
        _ => return None,
    };
    Some(e)
}

/// Zero-extend a `src_width`-bit unsigned value to `src_width+1` bits (sign-bit
/// clear), so a SIGNED BvToFP interpretation produces the non-negative magnitude.
fn zext_unsigned(v: u64, src_width: u32) -> SmtExpr {
    let mask = if src_width >= 64 {
        u64::MAX
    } else {
        (1u64 << src_width) - 1
    };
    SmtExpr::bv_const(v & mask, src_width + 1)
}

/// Op families whose result is an FP value (so the f32-carrier narrow recovers
/// the bits and a NaN-class classification is meaningful).
fn op_has_fp_result(op: &str) -> bool {
    op.starts_with("fadd")
        || op.starts_with("fsub")
        || op.starts_with("fmul")
        || op.starts_with("fdiv")
        || op.starts_with("fsqrt")
        || op.starts_with("fmin")
        || op.starts_with("fmax")
        || op.starts_with("fsgnj")
        || op.starts_with("fcvt.d.")
        || op.starts_with("fcvt.s.")
}

/// True iff `op` is an f->int conversion.
fn op_is_fp_to_int(op: &str) -> bool {
    matches!(
        op,
        "fcvt.w.d"
            | "fcvt.w.s"
            | "fcvt.wu.d"
            | "fcvt.wu.s"
            | "fcvt.l.d"
            | "fcvt.l.s"
            | "fcvt.lu.d"
            | "fcvt.lu.s"
    )
}

/// True iff `op` touches the f32 FCVT NATIVE-cast residual path (R1): an int->f32
/// convert, an f32->f convert, or an f32-source f->int convert. (The f32
/// ARITHMETIC ops are bit-model-backed; only FCVT remains native for f32.)
fn op_is_f32_fcvt_residual(op: &str) -> bool {
    // int -> f32
    matches!(op, "fcvt.s.w" | "fcvt.s.wu" | "fcvt.s.l" | "fcvt.s.lu")
        // f32 -> f
        || op == "fcvt.d.s"
        || op == "fcvt.s.d"
        // f32 source -> int
        || matches!(op, "fcvt.w.s" | "fcvt.wu.s" | "fcvt.l.s" | "fcvt.lu.s")
}

fn is_nan_w(bits: u64, w: u32) -> bool {
    match w {
        32 => fp_bitmodel::is_nan(fp_bitmodel::F32, bits & 0xFFFF_FFFF),
        _ => fp_bitmodel::is_nan(fp_bitmodel::F64, bits),
    }
}

/// Recover the result bits of an encoder at width `rw`. FP results: f64 ->
/// to_bits(); f32 -> the INTEGER-ONLY fcvt_narrow of the f64 carrier. Bv results
/// (compares, f->int): the integer bits.
fn eval_result_bits(expr: &SmtExpr, rw: u32, is_fp_result: bool) -> u64 {
    let env: HashMap<String, u64> = HashMap::new();
    match expr
        .try_eval(&env)
        .expect("bridge: RISC-V FP encoder eval failed")
    {
        EvalResult::Float(f) => {
            if is_fp_result && rw == 32 {
                fp_bitmodel::fcvt_narrow(f.to_bits())
            } else {
                f.to_bits()
            }
        }
        EvalResult::Bv(v) => v,
        EvalResult::Bv128(v) => v as u64,
        other => panic!("bridge: RISC-V FP encoder evaluated to {other:?}"),
    }
}

fn mask_w(v: u64, w: u32) -> u64 {
    if w >= 64 { v } else { v & ((1u64 << w) - 1) }
}

// ===========================================================================
// THE BRIDGE: every in-house RISC-V FP encoder must match qemu on every fact,
// with the RISC-V-specific FMIN/FMAX/FCVT modeled AS RISC-V (so those are STRICT
// matches, not deferred). The ONLY excused divergences are the honestly-counted
// f32-FCVT NATIVE-cast residual (R1) and a NaN-vs-NaN-of-same-width payload (R2);
// a non-NaN mismatch or a NaN-vs-non-NaN mismatch is ALWAYS a HARD failure.
// ===========================================================================
#[test]
fn riscv_fp_inhouse_encoders_match_qemu_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() > 7_000,
        "bridge: the qemu FP fixture is suspiciously small ({} facts) — truncated?",
        facts.len()
    );

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
        "RV64 scalar FP -> all value facts"
    );
    assert_eq!(
        trap_facts, 0,
        "RV64 scalar FP produces no traps under FS!=0 default handling"
    );

    let mut hard_mismatches: Vec<String> = Vec::new();
    let mut per_op: HashMap<String, usize> = HashMap::new();
    let mut strict_matched = 0usize;
    let mut r1_f32_fcvt = 0usize; // R1: f32-FCVT native-cast residual
    let mut r2_nan_payload = 0usize; // R2: NaN-vs-NaN payload (f32 carrier)

    for fact in &facts {
        *per_op.entry(fact.op.clone()).or_default() += 1;
        let expr = build_encoder(fact).unwrap_or_else(|| {
            panic!(
                "bridge: fixture op `{}` ({}) has no in-house encoder dispatch — fixture/bridge \
                 drift (every fixture op must map to an encoder, never silently unhandled)",
                fact.op, fact.theorem
            )
        });
        let rw = fact.result_width;
        let is_fp_result = op_has_fp_result(&fact.op);
        let got = mask_w(eval_result_bits(&expr, rw, is_fp_result), rw);
        let want = mask_w(fact.result, rw);

        if got == want {
            strict_matched += 1;
            continue;
        }

        // ---- a divergence: classify it honestly (never hide a wrong VALUE) ----

        // (R1) the f32-FCVT NATIVE-cast residual (already-registered
        // B-aarch64-fp-pending). EXCUSED only for an f32-FCVT op AND only when the
        // model's value is a NaN-class or saturation-edge difference (the native
        // `as` cast's saturating/NaN semantics vs RISC-V). Any other f32-FCVT
        // mismatch is HARD.
        if op_is_f32_fcvt_residual(&fact.op) {
            let both_nan = is_fp_result && is_nan_w(got, rw) && is_nan_w(want, rw);
            // For f32-source f->int: RISC-V NaN->max / saturation; the native cast
            // may differ on those edges only.
            let int_edge = op_is_fp_to_int(&fact.op);
            if both_nan || int_edge {
                r1_f32_fcvt += 1;
                continue;
            }
            // Otherwise it must be an int->f32 / f32->f rounding divergence: only
            // excuse it if neither side is a "plain finite small" value (i.e. the
            // input magnitude is large / a NaN). Conservatively, classify any
            // remaining f32-FCVT divergence as R1 (the native carrier residual),
            // since the whole f32 FCVT path is honest-deferred — but RECORD it so
            // the count is exact and visible.
            r1_f32_fcvt += 1;
            continue;
        }

        if is_fp_result {
            let both_nan = is_nan_w(got, rw) && is_nan_w(want, rw);
            if both_nan {
                // RISC-V emits canonical NaN; the model emits canonical too, so this
                // is rare — but a NaN-vs-NaN-of-same-width payload difference is
                // classified (R2), not a hard failure.
                r2_nan_payload += 1;
                continue;
            }
            // A NaN-vs-non-NaN or non-NaN-vs-non-NaN FP mismatch is a HARD failure
            // (a genuine wrong VALUE — NOT loosened).
            if hard_mismatches.len() < 40 {
                hard_mismatches.push(format!(
                    "{}: op={} fmt={} in={:x?} -> encoder {got:#x}, qemu {want:#x} (non-NaN FP \
                     value mismatch — a genuine RISC-V-vs-model divergence, NOT a NaN payload)",
                    fact.theorem, fact.op, fact.fmt, fact.in_bits
                ));
            }
            continue;
        }

        // Non-FP-result mismatch (compare / f->int at .d source) = HARD. These are
        // the RISC-V-SPECIFIC paths modeled AS RISC-V (fmin/fmax via fp results
        // above; fcvt .d-source NaN->max here), so a mismatch is a real finding.
        if hard_mismatches.len() < 40 {
            hard_mismatches.push(format!(
                "{}: op={} fmt={} in={:x?} -> encoder {got:#x}, qemu {want:#x}",
                fact.theorem, fact.op, fact.fmt, fact.in_bits
            ));
        }
    }

    // PER-OP accounting: all 41 fixture op families must have been exercised.
    assert!(
        per_op.len() >= 40,
        "bridge: too few FP op families exercised ({}) — expected the full ~41-family RISC-V F/D \
         grid",
        per_op.len()
    );
    for required in [
        "fadd.d",
        "fsub.d",
        "fmul.d",
        "fdiv.d",
        "fsqrt.d",
        "fmin.d",
        "fmax.d",
        "feq.d",
        "flt.d",
        "fle.d",
        "fsgnj.d",
        "fsgnjn.d",
        "fsgnjx.d",
        "fcvt.w.d",
        "fcvt.wu.d",
        "fcvt.l.d",
        "fcvt.lu.d",
        "fcvt.d.w",
        "fcvt.d.l",
        "fcvt.s.d",
        "fcvt.d.s",
        "fadd.s",
        "fmin.s",
        "fmax.s",
        "feq.s",
    ] {
        assert!(
            per_op.contains_key(required),
            "bridge: required encoder family `{required}` was not exercised by any fact"
        );
    }

    // Every fact is EXACTLY one of {strict, R1, R2, hard} — no silent skip.
    let total_classified = strict_matched + r1_f32_fcvt + r2_nan_payload;
    let hard_count = facts.len() - total_classified;
    assert!(
        hard_count == 0 || !hard_mismatches.is_empty(),
        "bridge: accounting drift — {hard_count} facts unclassified but no hard mismatch reported"
    );

    // HARD failures: a genuine wrong VALUE (NOT a NaN payload, NOT the f32-FCVT
    // residual). These would be real miscompile-class bugs / wrong RISC-V modeling.
    assert!(
        hard_mismatches.is_empty(),
        "B-riscv-fp BRIDGE FINDING (HARD): {hard_count} genuine wrong-VALUE mismatches between \
         trust-cg's RISC-V F/D model and qemu-system-riscv64. These are NOT NaN payloads and NOT \
         the honestly-deferred f32-FCVT native-cast residual — they are real divergences. First \
         {}:\n{}",
        hard_mismatches.len(),
        hard_mismatches.join("\n")
    );

    // The bridge is FULLY STRICT: every one of the 8104 facts is an EXACT-bit
    // match (the RISC-V-specific FMIN/FMAX = IEEE-2019 minimumNumber/maximumNumber,
    // FCVT-to-int saturate-with-NaN->max, and the canonical-NaN rule for every
    // NaN-producing op are ALL modeled AS RISC-V and STRICT-matched). The R1/R2
    // classification machinery is retained so a FUTURE regression that pushed a
    // bit-model-backed op onto the lossy native carrier — or that dropped the
    // canonical-NaN rule — would surface as a COUNTED residual (not a silent skip)
    // here, while the strict-count assertion below would also drop.
    assert!(
        strict_matched == facts.len(),
        "bridge: expected ALL {} facts to be STRICT exact-bit matches (the RISC-V FP model is \
         host-FPU-free + canonical-NaN-correct); got {strict_matched} strict, R1={r1_f32_fcvt}, \
         R2={r2_nan_payload} — a residual appeared, which is a regression (the original raw \
         bit-model NaN convention is ARM-payload, NOT RISC-V canonical; the encoders' \
         canonicalize_nan + RISC-V FCVT NaN-fixup close that finding to ZERO residual)",
        facts.len()
    );
    assert!(
        strict_matched > 7_000,
        "bridge: too few STRICT exact-bit matches ({strict_matched})"
    );
    // Defensive bound: the residual classes must stay empty (the finding is CLOSED,
    // not deferred). If a regression reintroduces them they are still COUNTED above.
    assert_eq!(
        r1_f32_fcvt, 0,
        "bridge: the f32-FCVT residual is expected to be ZERO (the canonical NaN survives the \
         carrier; in-range f32 converts are exact) — a nonzero count is a regression"
    );
    assert_eq!(
        r2_nan_payload, 0,
        "bridge: the NaN-payload residual is expected to be ZERO (RISC-V + the encoders both emit \
         the canonical NaN) — a nonzero count is a regression"
    );

    eprintln!(
        "B-riscv-fp bridge: {strict_matched}/{} STRICT exact-bit matches across {} op families — \
         FULLY STRICT, ZERO residual. The RISC-V-specific semantics are modeled AS RISC-V and \
         all STRICT-matched: FMIN/FMAX = IEEE-2019 minimumNumber/maximumNumber (lone NaN incl sNaN \
         -> the number; both NaN -> canonical qNaN; -0 < +0); FCVT-to-int saturate with NaN -> max \
         (signed INT_MAX, unsigned UINT_MAX); and the canonical-NaN rule (every NaN-producing op \
         emits 0x7fc0../0x7ff8.., closing the FINDING that the raw bit-model NaN is an ARM-payload \
         0x7ff8..01 / negative 0xfff8..). R1 f32-FCVT residual={r1_f32_fcvt}, R2 NaN-payload \
         residual={r2_nan_payload}. No genuine wrong-VALUE mismatch.",
        facts.len(),
        per_op.len()
    );
}

// ===========================================================================
// THE RISC-V-SPECIFIC SEMANTICS, PINNED with concrete witnesses so they can
// never be silently regressed or "fixed away" to x86/ARM semantics.
// ===========================================================================

/// Find the unique fact with the given op + operand bit patterns.
fn find2<'a>(facts: &'a [Fact], op: &str, a: u64, b: u64) -> &'a Fact {
    facts
        .iter()
        .find(|f| f.op == op && f.in_bits.len() == 2 && f.in_bits[0] == a && f.in_bits[1] == b)
        .unwrap_or_else(|| panic!("expected fact {op}({a:#x},{b:#x})"))
}
fn find1<'a>(facts: &'a [Fact], op: &str, a: u64) -> &'a Fact {
    facts
        .iter()
        .find(|f| f.op == op && f.in_bits.len() == 1 && f.in_bits[0] == a)
        .unwrap_or_else(|| panic!("expected fact {op}({a:#x})"))
}

fn model_bits(fact: &Fact) -> u64 {
    let rw = fact.result_width;
    mask_w(
        eval_result_bits(
            &build_encoder(fact).unwrap(),
            rw,
            op_has_fp_result(&fact.op),
        ),
        rw,
    )
}

#[test]
fn riscv_fmin_fmax_is_ieee2019_minnum_not_x86_not_arm() {
    let facts = load_facts();
    let qnan_d: u64 = 0x7ff8_0000_0000_0000;
    let snan_d: u64 = 0x7ff0_0000_0000_0001;
    let one_d: u64 = 0x3ff0_0000_0000_0000;

    // (a) FMIN.d(1.0, qNaN): RISC-V minimumNumber returns the NUMBER 1.0.
    //     (x86 MINSD would return the SECOND operand = NaN; the bridge proves
    //     qemu returns 1.0, and the in-house encoder agrees.)
    let f = find2(&facts, "fmin.d", one_d, qnan_d);
    assert_eq!(
        f.result, one_d,
        "qemu FMIN.d(1.0, NaN) must be 1.0 (RISC-V minimumNumber)"
    );
    assert_eq!(
        model_bits(f),
        one_d,
        "in-house FMIN.d(1.0, NaN) must be 1.0 (NOT NaN like x86)"
    );

    // (b) FMIN.d(sNaN, 1.0): RISC-V IEEE-2019 STILL returns the number 1.0 (sNaN
    //     only raises invalid). ARM FMINNM (IEEE-2008 minNum) would force a NaN
    //     result here — so this proves the bridge models RISC-V, NOT ARM.
    let f = find2(&facts, "fmin.d", snan_d, one_d);
    assert_eq!(
        f.result, one_d,
        "qemu FMIN.d(sNaN, 1.0) must be 1.0 (RISC-V 2019 minimumNumber; NOT ARM FMINNM's NaN)"
    );
    assert_eq!(
        model_bits(f),
        one_d,
        "in-house FMIN.d(sNaN, 1.0) must be 1.0 (NOT ARM's NaN)"
    );

    // (c) FMIN.d(qNaN, qNaN): both NaN -> the CANONICAL qNaN (RISC-V never
    //     propagates a payload).
    let f = find2(&facts, "fmin.d", qnan_d, qnan_d);
    assert_eq!(
        f.result, qnan_d,
        "qemu FMIN.d(NaN, NaN) must be the canonical qNaN"
    );
    assert_eq!(
        model_bits(f),
        qnan_d,
        "in-house FMIN.d(NaN, NaN) must be the canonical qNaN"
    );

    // (d) signed-zero ordering: FMIN.d(-0, +0) = -0, FMAX.d(-0, +0) = +0.
    let neg0: u64 = 0x8000_0000_0000_0000;
    let pos0: u64 = 0x0;
    let fmin = find2(&facts, "fmin.d", neg0, pos0);
    assert_eq!(
        fmin.result, neg0,
        "qemu FMIN.d(-0, +0) must be -0 (RISC-V: -0 < +0)"
    );
    assert_eq!(model_bits(fmin), neg0, "in-house FMIN.d(-0, +0) must be -0");
    let fmax = find2(&facts, "fmax.d", neg0, pos0);
    assert_eq!(fmax.result, pos0, "qemu FMAX.d(-0, +0) must be +0");
    assert_eq!(model_bits(fmax), pos0, "in-house FMAX.d(-0, +0) must be +0");
}

#[test]
fn riscv_fcvt_to_int_saturates_with_nan_to_max() {
    let facts = load_facts();
    let qnan_d: u64 = 0x7ff8_0000_0000_0000;
    let pinf_d: u64 = 0x7ff0_0000_0000_0000;
    let ninf_d: u64 = 0xfff0_0000_0000_0000;
    let r123_d: u64 = 0x405e_c000_0000_0000;

    // (a) in-range: FCVT.W.D(123.0) = 123 (both sides).
    let f = find1(&facts, "fcvt.w.d", r123_d);
    assert_eq!(f.result & 0xFFFF_FFFF, 123, "qemu FCVT.W.D(123.0) = 123");
    assert_eq!(
        model_bits(f) & 0xFFFF_FFFF,
        123,
        "in-house FCVT.W.D(123.0) = 123"
    );

    // (b) NaN -> INT_MAX (2^31-1) signed — the RISC-V-SPECIFIC rule (NOT 0 like
    //     the shared wasm/ARM/Rust FPToSBv; the encoder's NaN-fixup models RISC-V).
    let f = find1(&facts, "fcvt.w.d", qnan_d);
    assert_eq!(
        f.result & 0xFFFF_FFFF,
        0x7fff_ffff,
        "qemu FCVT.W.D(NaN) must be INT_MAX 0x7fffffff (RISC-V; NOT 0)"
    );
    assert_eq!(
        model_bits(f) & 0xFFFF_FFFF,
        0x7fff_ffff,
        "in-house FCVT.W.D(NaN) must be INT_MAX (the RISC-V NaN-fixup is modeled, NOT deferred)"
    );

    // (c) NaN -> UINT_MAX unsigned.
    let f = find1(&facts, "fcvt.wu.d", qnan_d);
    assert_eq!(
        f.result & 0xFFFF_FFFF,
        0xFFFF_FFFF,
        "qemu FCVT.WU.D(NaN) = UINT_MAX"
    );
    assert_eq!(
        model_bits(f) & 0xFFFF_FFFF,
        0xFFFF_FFFF,
        "in-house FCVT.WU.D(NaN) = UINT_MAX"
    );

    // (d) +Inf -> INT_MAX, -Inf -> INT_MIN (saturate).
    let f = find1(&facts, "fcvt.w.d", pinf_d);
    assert_eq!(
        f.result & 0xFFFF_FFFF,
        0x7fff_ffff,
        "qemu FCVT.W.D(+Inf) = INT_MAX"
    );
    assert_eq!(
        model_bits(f) & 0xFFFF_FFFF,
        0x7fff_ffff,
        "in-house FCVT.W.D(+Inf) = INT_MAX"
    );
    let f = find1(&facts, "fcvt.w.d", ninf_d);
    assert_eq!(
        f.result & 0xFFFF_FFFF,
        0x8000_0000,
        "qemu FCVT.W.D(-Inf) = INT_MIN"
    );
    assert_eq!(
        model_bits(f) & 0xFFFF_FFFF,
        0x8000_0000,
        "in-house FCVT.W.D(-Inf) = INT_MIN"
    );

    // (e) +Inf -> UINT_MAX (unsigned), -1.0 -> 0 (negative -> 0 unsigned).
    let f = find1(&facts, "fcvt.lu.d", pinf_d);
    assert_eq!(f.result, u64::MAX, "qemu FCVT.LU.D(+Inf) = UINT64_MAX");
    assert_eq!(
        model_bits(f),
        u64::MAX,
        "in-house FCVT.LU.D(+Inf) = UINT64_MAX"
    );
}

// ===========================================================================
// NON-VACUITY (teeth): deliberately-WRONG encoders MUST mismatch qemu, and the
// CORRECT encoder must match ALL facts of that family. These prove the bridge is
// not a tautology / self-comparison.
// ===========================================================================

/// Does the CORRECT encoder match qemu on this fact (treating a NaN-of-same-width
/// payload difference as a match — the R2 class)?
fn correct_matches_modulo_nan(fact: &Fact) -> bool {
    let rw = fact.result_width;
    let want = mask_w(fact.result, rw);
    let got = model_bits(fact);
    if got == want {
        return true;
    }
    op_has_fp_result(&fact.op) && is_nan_w(got, rw) && is_nan_w(want, rw)
}

#[test]
fn bridge_is_non_vacuous_fadd_as_fsub_mismatches_qemu() {
    let facts = load_facts();
    let add_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "fadd.d").collect();
    assert!(!add_facts.is_empty(), "expected FADD.d facts");
    for f in &add_facts {
        assert!(
            correct_matches_modulo_nan(f),
            "precondition: the correct FADD.d encoder must match qemu on every FADD.d fact ({})",
            f.theorem
        );
    }
    let mut found = false;
    for f in &add_facts {
        let wrong = encode_fsub(
            RiscVFpFormat::D,
            fp_leaf(f.in_bits[0], RiscVFpFormat::D),
            fp_leaf(f.in_bits[1], RiscVFpFormat::D),
        );
        let got = mask_w(eval_result_bits(&wrong, 64, true), 64);
        let want = mask_w(f.result, 64);
        if got != want && !(is_nan_w(got, 64) && is_nan_w(want, 64)) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: FSUB-for-FADD matched qemu on EVERY FADD.d fact — the bridge would be a \
         tautology. It must mismatch (a+b != a-b on a non-degenerate input)."
    );
}

#[test]
fn bridge_is_non_vacuous_fmin_as_fmax_mismatches_qemu() {
    let facts = load_facts();
    let min_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "fmin.d").collect();
    assert!(!min_facts.is_empty(), "expected FMIN.d facts");
    for f in &min_facts {
        assert!(
            correct_matches_modulo_nan(f),
            "precondition: the correct FMIN.d encoder must match qemu on every FMIN.d fact ({})",
            f.theorem
        );
    }
    let mut found = false;
    for f in &min_facts {
        let wrong = encode_fmax(
            RiscVFpFormat::D,
            fp_leaf(f.in_bits[0], RiscVFpFormat::D),
            fp_leaf(f.in_bits[1], RiscVFpFormat::D),
        );
        let got = mask_w(eval_result_bits(&wrong, 64, true), 64);
        let want = mask_w(f.result, 64);
        if got != want && !(is_nan_w(got, 64) && is_nan_w(want, 64)) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: FMAX-for-FMIN matched qemu on EVERY FMIN.d fact — the min/max distinction \
         would not be load-bearing. It must MISMATCH on an ordered unequal pair."
    );
}

#[test]
fn bridge_is_non_vacuous_feq_as_flt_mismatches_qemu() {
    let facts = load_facts();
    let eq_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "feq.d").collect();
    assert!(!eq_facts.is_empty(), "expected FEQ.d facts");
    for f in &eq_facts {
        assert!(
            correct_matches_modulo_nan(f),
            "precondition: the correct FEQ.d encoder must match qemu on every FEQ.d fact ({})",
            f.theorem
        );
    }
    let mut found = false;
    for f in &eq_facts {
        let wrong = encode_flt(
            RiscVFpFormat::D,
            fp_leaf(f.in_bits[0], RiscVFpFormat::D),
            fp_leaf(f.in_bits[1], RiscVFpFormat::D),
        );
        let got = mask_w(eval_result_bits(&wrong, 1, false), 1);
        if got != mask_w(f.result, 1) {
            found = true;
            break;
        }
    }
    assert!(
        found,
        "NON-VACUITY: FEQ-as-FLT (== emitted as <) matched qemu on EVERY FEQ.d fact — the predicate \
         distinction would not be load-bearing. It must MISMATCH (a==a: 1 for FEQ, 0 for FLT)."
    );
}

#[test]
fn bridge_is_non_vacuous_riscv_fcvt_nan_is_not_zero() {
    // The RISC-V-vs-shared-evaluator finding, PINNED as teeth: the SHARED FPToSBv
    // (NaN -> 0, the wasm/ARM/Rust convention) DISAGREES with qemu on a NaN input,
    // while the RISC-V encoder's NaN-fixup (NaN -> INT_MAX) AGREES. This proves the
    // RISC-V-specific NaN modeling is load-bearing (not a no-op wrap).
    let facts = load_facts();
    let qnan_d: u64 = 0x7ff8_0000_0000_0000;
    let f = find1(&facts, "fcvt.w.d", qnan_d);
    // qemu (RISC-V): NaN -> INT_MAX.
    assert_eq!(f.result & 0xFFFF_FFFF, 0x7fff_ffff);
    // The RAW shared evaluator (no RISC-V fixup): NaN -> 0.
    let shared = SmtExpr::fp_to_sbv(
        trust_cg_verify::smt::RoundingMode::RTZ,
        fp_leaf(qnan_d, RiscVFpFormat::D),
        32,
    );
    let shared_bits = mask_w(eval_result_bits(&shared, 32, false), 32);
    assert_eq!(
        shared_bits, 0,
        "the SHARED FPToSBv maps NaN -> 0 (wasm/ARM/Rust) — distinct from RISC-V"
    );
    assert_ne!(
        shared_bits,
        f.result & 0xFFFF_FFFF,
        "NON-VACUITY: the shared NaN->0 converter DISAGREES with qemu's RISC-V NaN->INT_MAX, so the \
         RISC-V encoder's NaN-fixup is load-bearing (modeling FCVT-NaN as the shared 0 would \
         MISCOMPILE on RISC-V)"
    );
    // The RISC-V encoder agrees with qemu.
    assert_eq!(model_bits(f) & 0xFFFF_FFFF, f.result & 0xFFFF_FFFF);
}

#[test]
fn bridge_is_non_vacuous_riscv_nan_is_canonical_not_arm_payload() {
    // The RISC-V canonical-NaN finding, PINNED as teeth: the RAW bit-model FP
    // arithmetic (the ARM-payload convention, silicon-validated against the M4)
    // produces a NaN with a NON-canonical payload — and for FSUB even a NEGATIVE
    // NaN — on a NaN-producing input, which DISAGREES with qemu's RISC-V canonical
    // NaN. The RISC-V encoder's canonicalize_nan wrap AGREES with qemu. This proves
    // the canonical-NaN rule is load-bearing (NOT a no-op wrap): modeling RISC-V FP
    // arithmetic as the raw bit-model (ARM NaN convention) would MISCOMPILE on RISC-V.
    use trust_cg_verify::smt::RoundingMode;
    let facts = load_facts();
    let canon_d: u64 = 0x7ff8_0000_0000_0000;
    // sNaN + 1.0: the NaN propagates. RISC-V QUIETS it to the SINGLE canonical NaN
    // (0x7ff8..00), discarding the payload; the raw bit-model (ARM FPProcessNaNs)
    // quiets it KEEPING the payload -> 0x7ff8..01 (non-canonical).
    let snan_d: u64 = 0x7ff0_0000_0000_0001;
    let one_d: u64 = 0x3ff0_0000_0000_0000;
    let f = find2(&facts, "fadd.d", snan_d, one_d);
    assert_eq!(
        f.result, canon_d,
        "qemu FADD.d(sNaN, 1.0) must be the RISC-V canonical NaN 0x7ff8..00 (payload discarded)"
    );
    // The RAW (un-canonicalized) bit-model arithmetic: a NaN, but with the ARM
    // payload convention -> NOT the bit-identical canonical NaN.
    let raw = SmtExpr::fp_add(
        RoundingMode::RNE,
        fp_leaf(snan_d, RiscVFpFormat::D),
        fp_leaf(one_d, RiscVFpFormat::D),
    );
    let raw_bits = eval_result_bits(&raw, 64, true);
    assert!(
        is_nan_w(raw_bits, 64),
        "the raw bit-model result must still be a NaN"
    );
    assert_ne!(
        raw_bits, canon_d,
        "NON-VACUITY: the RAW bit-model NaN (ARM-payload convention, keeps the sNaN payload) must \
         DIFFER bit-for-bit from qemu's RISC-V canonical NaN — so modeling RISC-V FP as the raw \
         bit-model would diverge; the encoder's canonicalize_nan is load-bearing"
    );
    // The RISC-V encoder (with canonicalize_nan) agrees with qemu.
    assert_eq!(
        model_bits(f),
        canon_d,
        "in-house FADD.d(sNaN, 1.0) must be the RISC-V canonical NaN (canonicalize_nan applied)"
    );

    // FSUB(1.0, sNaN): the raw bit-model quiets the sNaN operand and keeps its
    // ORIGINAL (positive) sign + payload (owner #8 fix — ARM FSUB propagates the NaN
    // over the original operands, it does NOT sub-negate the NaN), giving a POSITIVE
    // non-canonical NaN 0x7ff8..01, where RISC-V emits the POSITIVE canonical NaN
    // 0x7ff8..00. Still non-vacuous: canonicalize_nan is load-bearing for the PAYLOAD.
    let f = find2(&facts, "fsub.d", one_d, snan_d);
    assert_eq!(
        f.result, canon_d,
        "qemu FSUB.d(1.0, sNaN) must be the POSITIVE canonical NaN"
    );
    let raw = SmtExpr::fp_sub(
        RoundingMode::RNE,
        fp_leaf(one_d, RiscVFpFormat::D),
        fp_leaf(snan_d, RiscVFpFormat::D),
    );
    let raw_bits = eval_result_bits(&raw, 64, true);
    assert!(is_nan_w(raw_bits, 64));
    assert!(
        (raw_bits >> 63) & 1 == 0,
        "the raw bit-model FSUB(1.0, sNaN) is a POSITIVE NaN (owner #8 fix: the sNaN's original sign is kept, not sub-negated)"
    );
    assert_ne!(
        raw_bits, canon_d,
        "NON-VACUITY: the raw bit-model non-canonical NaN (keeps the sNaN payload) differs from \
         RISC-V's canonical NaN — canonicalize_nan is load-bearing for the PAYLOAD"
    );
    assert_eq!(
        model_bits(f),
        canon_d,
        "in-house FSUB.d(1.0, sNaN) must be the canonical NaN"
    );
}

#[test]
fn bridge_is_non_vacuous_corrupted_fixture_result_mismatches() {
    // Corrupt a non-NaN FADD.d fact's recorded qemu result and confirm the
    // encoder now DISAGREES — proving the bridge compares against the fixture
    // value, not against itself.
    let facts = load_facts();
    let fact = facts
        .iter()
        .find(|f| {
            f.op == "fadd.d"
                && !is_nan_w(f.result, 64)
                && !is_nan_w(f.in_bits[0], 64)
                && !is_nan_w(f.in_bits[1], 64)
                && f.result != 0
        })
        .expect("a non-NaN nonzero FADD.d fact");
    assert_eq!(
        model_bits(fact),
        fact.result,
        "sanity: the genuine FADD.d fact must match"
    );
    let corrupted = fact.result.wrapping_add(1);
    assert_ne!(
        model_bits(fact),
        corrupted,
        "NON-VACUITY: corrupting the recorded qemu result must flip the comparison — the bridge \
         actually compares against the fixture value (not against itself)"
    );
}

#[test]
fn oracle_provenance_is_independent_qemu_fp() {
    let doc: Value = serde_json::from_str(FIXTURE).expect("fixture is valid JSON");
    let oracle = doc["_header"]["oracle"].as_str().expect("header.oracle");
    assert_eq!(
        oracle, "qemu-system-riscv64",
        "the oracle must be the INDEPENDENT qemu RISC-V executor (got `{oracle}`)"
    );
    let qver = doc["_header"]["qemu_version"]
        .as_str()
        .expect("header.qemu_version");
    assert!(
        qver.contains("QEMU") && !qver.contains("@"),
        "qemu_version must be a spliced real version string (got `{qver}`)"
    );
    // The header must declare the RISC-V-specific FMIN/FMAX/FCVT semantics it
    // records (so a regression that swapped in x86/ARM facts is caught).
    let spec = doc["_header"]["riscv_specific"]
        .as_str()
        .expect("header.riscv_specific");
    assert!(
        spec.contains("minimumNumber") && spec.contains("canonical") && spec.contains("SATURATES"),
        "the header must declare the RISC-V-specific FMIN/FMAX (IEEE-2019 minimumNumber) + \
         canonical-NaN + saturating-FCVT semantics"
    );
}
