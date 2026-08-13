// trust-cg-verify/tests/bdefs_differential_bridge_riscv.rs — DELIVERABLE of #93.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE B-riscv-qemu DIFFERENTIAL BRIDGE (the RISC-V analog of
// bdefs_differential_bridge.rs [AArch64 silicon] and _x86.rs [Rosetta]).
// ===========================================================================
//
// This is the RISC-V machine-side dual of the in-house SmtExpr model. It defeats
// root-cause #2 of the lowering-equivalence TCB — that BOTH sides of every RISC-V
// reconstruction check are validated against ONE in-house machine spec
// (trust-cg-verify/src/riscv_semantics.rs, the SmtExpr encoders), so a SHARED
// mis-encoding in that spec is INVISIBLE to the equivalence check.
//
// HOW IT DEFEATS THAT: every fact in tests/fixtures/riscv_qemu_truth.json is a
// result recorded from `qemu-system-riscv64` — QEMU's INDEPENDENT RISC-V machine
// emulator (a SOFTWARE GOLDEN MODEL of the RV64 ISA), NOT a second in-house
// model. qemu is a genuinely independent executor of the real RV64 instruction
// ENCODINGS (the oracle harness emits each op as an explicit RV64 instruction via
// inline asm over volatile runtime operands — qemu decodes+executes the actual
// instruction word; the result is not a Rust-level computation). It is one notch
// below bare silicon (it does not run on a physical RISC-V part), so this is a
// SOFTWARE-GOLDEN-MODEL tier — strictly weaker than the AArch64 silicon oracle
// but strictly stronger than the two-in-house-authorings FALLBACK, because the
// executor is independent of trust-cg.
//
// For each fact this test:
//   1. takes the op + the qemu operand literals,
//   2. constructs trust-cg's OWN in-house RISC-V SmtExpr encoder for that op (the
//      SAME encoders the reconstruction machine side uses — riscv_semantics.rs),
//      with the operands as concrete SmtExpr::bv_const leaves,
//   3. evaluates it through the SAME SmtExpr `try_eval` evaluator the
//      reconstruction `verify_by_evaluation` path uses, and
//   4. asserts the EVALUATED result EQUALS the qemu-recorded result.
//
// A mismatch is a FINDING (a latent miscompile-class bug, or a convention
// divergence) — NOT papered over by excluding the op or loosening the comparison.
// The bridge is NON-VACUOUS: `bridge_is_non_vacuous_*` below prove deliberately-
// WRONG encoders mismatch a qemu fact (so the bridge has teeth — not a tautology,
// not a self-comparison).
//
// CONVENTIONS (exactly where mismatches surface — all validated here):
//   * SHIFTS use the FAITHFUL amount-MASKED register-shift encoders
//     (encode_sll_masked etc., count & (width-1)) — NOT the plain SMT bvshl whose
//     evaluator CLAMPS to 0 at count >= width. The masked encoder matches RV64's
//     &0x3F (X) / &0x1F (W) amount mask (#57). The W-form mask falls out of the
//     32-bit operand sort the encoder reads (riscv_shift_amount_mask(32)=31).
//   * RV64 integer ALU does NOT trap (DIV/REM by zero is defined and out of the
//     reconstructable ALU set), so there are no trap facts — every fact is a VALUE.
//   * SLT/SLTU/SLTIU return the 1-bit boolean result (0/1), per encode_slt et al.
//   * W-forms: the architectural W result is the 32-bit op sign-extended to 64;
//     the width-32 encoder produces the LOW-32 result, and the oracle records the
//     LOW 32 bits — these are equal, so the bridge compares low-32 to low-32.
//     W-form AND/OR/XOR/SLT/SLTU have no dedicated RV64 instruction; they are the
//     X-form op on the low 32 bits, encoded at width 32 (matching the oracle).
//   * I-type immediates (ADDI/XORI/SLTIU): the immediate is an instruction-literal
//     12-bit field, recorded SIGN-EXTENDED to 64 bits in operands[1]; the bridge
//     rebuilds it as a 64-bit bv_const (the encoders take imm as an SmtExpr).
//   * SLLI/SRLI: the shift amount is the instruction-literal shamt in operands[1],
//     passed to the constant-shift encoders as a u32.

use std::collections::HashMap;

use serde_json::Value;

use trust_cg_verify::riscv_semantics::{
    RiscVOperandSize, encode_add, encode_addi, encode_and, encode_mul, encode_or,
    encode_sll_masked, encode_slli, encode_slt, encode_sltiu, encode_sltu, encode_sra_masked,
    encode_srl_masked, encode_srli, encode_sub, encode_xor, encode_xori,
};
use trust_cg_verify::smt::{EvalResult, SmtExpr, mask};

const FIXTURE: &str = include_str!("fixtures/riscv_qemu_truth.json");

/// A single qemu ground-truth fact (one independent-RV64 recorded result).
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
                .map(|v| v.as_u64().expect("operand is a u64 (low-width literal)"))
                .collect(),
            result: parse_hex(&f["result"]),
            theorem: f["theorem"]
                .as_str()
                .expect("theorem is a string")
                .to_string(),
        })
        .collect()
}

fn parse_hex(v: &Value) -> u64 {
    let s = v.as_str().expect("result is a hex string");
    let h = s.strip_prefix("0x").unwrap_or(s);
    u64::from_str_radix(h, 16).expect("result hex parses")
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
///
/// For W-forms (width==32) this is exactly the W-register read semantics: the
/// machine sees only the low 32 bits. `bv_const` masks to `width`, so passing the
/// full 64-bit literal is correct.
fn leaf(v: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(v, width)
}

fn size_of(width: u32) -> RiscVOperandSize {
    match width {
        32 => RiscVOperandSize::S32,
        64 => RiscVOperandSize::S64,
        other => panic!("bridge: unexpected width {other}"),
    }
}

/// Build the trust-cg IN-HOUSE RISC-V encoder SmtExpr for `fact`. Returns `None`
/// for an op tag the bridge does not encode (should never happen — the fixture
/// only contains in-house-encoded ops; an unknown tag is a fixture/bridge drift).
fn build_encoder(fact: &Fact) -> Option<SmtExpr> {
    let w = fact.width;
    let sz = size_of(w);
    let ops = &fact.operands;
    let l = |i: usize| leaf(ops[i], w);
    let e = match fact.op.as_str() {
        // ---- arithmetic / logic (X) ----
        "add" => encode_add(sz, l(0), l(1)),
        "sub" => encode_sub(sz, l(0), l(1)),
        "mul" => encode_mul(sz, l(0), l(1)),
        "and" => encode_and(sz, l(0), l(1)),
        "or" => encode_or(sz, l(0), l(1)),
        "xor" => encode_xor(sz, l(0), l(1)),
        // ---- arithmetic / logic (W, low-32 width-polymorphic encoder) ----
        // ADDW/SUBW/MULW are real W instructions; AND/OR/XOR have no W form (the
        // width-32 X-form op IS the W result on the low 32 bits). The encoder is
        // identical at width 32; the oracle records the low-32 of each.
        "addw" => encode_add(sz, l(0), l(1)),
        "subw" => encode_sub(sz, l(0), l(1)),
        "mulw" => encode_mul(sz, l(0), l(1)),
        "andw" => encode_and(sz, l(0), l(1)),
        "orw" => encode_or(sz, l(0), l(1)),
        "xorw" => encode_xor(sz, l(0), l(1)),
        // ---- compare (X) — 1-bit boolean result ----
        "slt" => encode_slt(sz, l(0), l(1)),
        "sltu" => encode_sltu(sz, l(0), l(1)),
        // ---- compare (W) — signed/unsigned 32-bit lt, 1-bit result ----
        "sltw" => encode_slt(sz, l(0), l(1)),
        "sltuw" => encode_sltu(sz, l(0), l(1)),
        // ---- register shifts (X) — FAITHFUL amount-masked encoders (#57) ----
        "sll" => encode_sll_masked(sz, l(0), l(1)),
        "srl" => encode_srl_masked(sz, l(0), l(1)),
        "sra" => encode_sra_masked(sz, l(0), l(1)),
        // ---- register shifts (W) — width-32 leaves => mask &0x1F ----
        "sllw" => encode_sll_masked(sz, l(0), l(1)),
        "srlw" => encode_srl_masked(sz, l(0), l(1)),
        "sraw" => encode_sra_masked(sz, l(0), l(1)),
        // ---- I-type immediates (X): imm is the sign-extended 64-bit operands[1] -
        "addi" => encode_addi(sz, l(0), leaf(ops[1], 64)),
        "xori" => encode_xori(sz, l(0), leaf(ops[1], 64)),
        "sltiu" => encode_sltiu(sz, l(0), leaf(ops[1], 64)),
        // ---- immediate-shift forms: shamt is operands[1] (constant amount) ----
        "slli" => encode_slli(sz, l(0), ops[1] as u32),
        "srli" => encode_srli(sz, l(0), ops[1] as u32),
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
// THE BRIDGE: every in-house encoder must match qemu on every recorded fact.
// ===========================================================================
#[test]
fn riscv_inhouse_encoders_match_qemu_ground_truth() {
    let facts = load_facts();
    assert!(
        facts.len() > 3_000,
        "bridge: the qemu fixture is suspiciously small ({} facts) — truncated?",
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
    assert_eq!(trap_facts, 0, "RV64 integer ALU produces no traps");

    let mut mismatches: Vec<String> = Vec::new();
    let mut checked = 0usize;
    let mut per_op: HashMap<String, usize> = HashMap::new();

    for fact in &facts {
        let expr = build_encoder(fact).unwrap_or_else(|| {
            panic!(
                "bridge: fixture op `{}` ({}) has no in-house encoder dispatch — the fixture and \
                 the bridge have drifted (every fixture op must map to an encoder or be EXCLUDED \
                 in the generator, never silently unhandled)",
                fact.op, fact.theorem
            )
        });
        let got = eval(&expr);
        checked += 1;
        *per_op.entry(fact.op.clone()).or_default() += 1;
        if got != fact.result && mismatches.len() < 40 {
            mismatches.push(format!(
                "{}: op={} width={} operands={:?} -> in-house encoder gave {:#x} ({}), qemu \
                 recorded {:#x} ({})",
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

    // Every op family in the fixture must actually have been exercised, and the
    // 14 reconstructable ALU encoders must all be present.
    assert!(
        per_op.len() >= 20,
        "bridge: too few op families exercised ({})",
        per_op.len()
    );
    for required in [
        "add", "sub", "mul", "and", "or", "xor", "sll", "srl", "sra", "slt", "sltu", "addi",
        "xori", "sltiu", "slli", "srli",
    ] {
        assert!(
            per_op.contains_key(required),
            "bridge: required encoder family `{required}` was not exercised by any fact"
        );
    }
    assert_eq!(
        checked,
        facts.len(),
        "bridge: checked {checked} != {} total facts (silent skip)",
        facts.len()
    );

    assert!(
        mismatches.is_empty(),
        "B-riscv-qemu BRIDGE FINDING: {} of {checked} in-house-encoder vs qemu comparisons \
         MISMATCH. Each is a latent miscompile-class divergence between trust-cg's RISC-V model \
         and an independent RV64 executor (qemu-system-riscv64). First mismatches:\n{}",
        mismatches.len(),
        mismatches.join("\n")
    );

    eprintln!(
        "B-riscv-qemu bridge: {checked} in-house-encoder vs qemu comparisons PASS across {} op \
         families.",
        per_op.len()
    );
}

// ===========================================================================
// NON-VACUITY (teeth): deliberately-WRONG encoders MUST mismatch qemu, and the
// CORRECT encoder must match ALL facts of that family.
// ===========================================================================

/// Helper: does the in-house encoder agree with qemu on this exact fact?
fn encoder_matches(fact: &Fact) -> bool {
    match build_encoder(fact) {
        Some(expr) => eval(&expr) == fact.result,
        None => false,
    }
}

#[test]
fn bridge_is_non_vacuous_add_as_sub_mismatches_qemu() {
    // Feed ADD facts to the SUB encoder: it must NOT match qemu for at least one
    // fact (bvadd != bvsub on a non-degenerate input).
    let facts = load_facts();
    let add_facts: Vec<&Fact> = facts.iter().filter(|f| f.op == "add").collect();
    assert!(!add_facts.is_empty(), "expected ADD facts in the fixture");

    // The CORRECT encoder matches ALL add facts (precondition for the teeth).
    for f in &add_facts {
        assert!(
            encoder_matches(f),
            "precondition: the correct ADD encoder must match qemu on every ADD fact ({})",
            f.theorem
        );
    }

    let mut found_divergence = false;
    for fact in &add_facts {
        let w = fact.width;
        let wrong = encode_sub(
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
        "NON-VACUITY: a deliberately-wrong (SUB-for-ADD) encoder matched qemu on EVERY ADD fact \
         — the bridge would be a tautology / self-comparison. It must mismatch."
    );
}

#[test]
fn bridge_is_non_vacuous_unmasked_shift_mismatches_qemu_at_count_ge_width() {
    // The CRUX of #57: the PLAIN (clamp-to-0) shift encoder DISAGREES with qemu at
    // a shift count >= width, while the FAITHFUL (masked) encoder used by the
    // bridge AGREES. This proves (a) the bridge uses the right encoder, and (b)
    // the qemu fixture genuinely encodes the &0x3F mask, not the SMT clamp.
    use trust_cg_verify::riscv_semantics::encode_sll;
    let facts = load_facts();
    // Find an X-form SLL fact whose count >= width (so masking is observable) and
    // src != 0 (so clamp-to-0 vs masked actually differ).
    let fact = facts
        .iter()
        .find(|f| f.op == "sll" && f.width == 64 && f.operands[1] >= 64 && f.operands[0] != 0)
        .expect("expected an X SLL fact with count >= 64 and nonzero src");

    let masked = encode_sll_masked(
        RiscVOperandSize::S64,
        leaf(fact.operands[0], 64),
        leaf(fact.operands[1], 64),
    );
    let plain = encode_sll(
        RiscVOperandSize::S64,
        leaf(fact.operands[0], 64),
        leaf(fact.operands[1], 64),
    );
    assert_eq!(
        eval(&masked),
        fact.result,
        "the FAITHFUL masked encoder must match qemu at count >= width ({})",
        fact.theorem
    );
    assert_ne!(
        eval(&plain),
        fact.result,
        "NON-VACUITY (#57): the PLAIN clamp-to-0 encoder must DISAGREE with qemu at count >= \
         width — proving the qemu fixture encodes the hardware &0x3F mask, not the SMT clamp, and \
         that the bridge's choice of the masked encoder is load-bearing"
    );
}

#[test]
fn bridge_is_non_vacuous_unmasked_w_shift_mismatches_qemu_at_count_ge_32() {
    // The W-form analog of #57: a W-form shift masks the count with &0x1F (5 bits),
    // so at count >= 32 the masked-at-width-32 encoder agrees with qemu while the
    // plain bvshl clamps to 0. This proves the W-form mask is load-bearing AND that
    // the bridge's choice to encode W-forms at operand-width 32 is what produces
    // the &0x1F mask (riscv_shift_amount_mask(32) = 31), distinct from &0x3F.
    use trust_cg_verify::riscv_semantics::encode_sll;
    let facts = load_facts();
    let fact = facts
        .iter()
        .find(|f| {
            f.op == "sllw"
                && f.width == 32
                && f.operands[1] >= 32
                && (f.operands[0] & 0xFFFF_FFFF) != 0
        })
        .expect("expected a W SLLW fact with count >= 32 and nonzero src");

    // Masked at width 32 -> &0x1F -> matches qemu's W-form mask.
    let masked = encode_sll_masked(
        RiscVOperandSize::S32,
        leaf(fact.operands[0], 32),
        leaf(fact.operands[1], 32),
    );
    // Plain bvshl at width 32 clamps to 0 for count >= 32.
    let plain = encode_sll(
        RiscVOperandSize::S32,
        leaf(fact.operands[0], 32),
        leaf(fact.operands[1], 32),
    );
    assert_eq!(
        eval(&masked) & 0xFFFF_FFFF,
        fact.result,
        "the FAITHFUL width-32 masked encoder (&0x1F) must match qemu's W-form shift at count >= \
         32 ({})",
        fact.theorem
    );
    assert_ne!(
        eval(&plain) & 0xFFFF_FFFF,
        fact.result,
        "NON-VACUITY (#57, W-form): the PLAIN clamp-to-0 encoder must DISAGREE with qemu at count \
         >= 32 — proving the qemu W fixture encodes the hardware &0x1F mask"
    );
}

#[test]
fn bridge_is_non_vacuous_slt_as_sltu_mismatches_qemu_on_negative() {
    // A signed-SLT-emitted-as-unsigned-SLTU bug differs ONLY in signed-vs-unsigned
    // comparison, which DIVERGES when an operand has its sign bit set. Over all SLT
    // VALUE facts: (1) the CORRECT signed encoder must match qemu on EVERY one (the
    // teeth precondition), and (2) the WRONG unsigned encoder must MISMATCH on at
    // least one (e.g. -1 <s 0 is 1 but -1 <u 0 is 0).
    let facts = load_facts();
    let slt_facts: Vec<&Fact> = facts
        .iter()
        .filter(|f| f.op == "slt" && f.width == 64)
        .collect();
    assert!(!slt_facts.is_empty(), "expected signed-SLT facts");

    // (1) The CORRECT signed encoder matches qemu on EVERY SLT fact.
    for f in &slt_facts {
        assert!(
            encoder_matches(f),
            "precondition: the correct signed SLT encoder must match qemu on every SLT fact ({})",
            f.theorem
        );
    }

    // (2) The WRONG unsigned-SLTU encoder DIVERGES on at least one negative operand.
    let mut found_divergence = false;
    let mut witness = String::new();
    for f in &slt_facts {
        let wrong = encode_sltu(
            RiscVOperandSize::S64,
            leaf(f.operands[0], 64),
            leaf(f.operands[1], 64),
        );
        if eval(&wrong) != f.result {
            found_divergence = true;
            witness = f.theorem.clone();
            break;
        }
    }
    assert!(
        found_divergence,
        "NON-VACUITY: SLT-as-SLTU (signed for unsigned) matched the qemu signed result on EVERY \
         SLT fact — the bridge's signed-vs-unsigned distinction would not be load-bearing. It must \
         MISMATCH on a negative operand (e.g. -1 <s 0 = 1 but -1 <u 0 = 0)."
    );
    eprintln!("SLT-as-SLTU teeth: unsigned encoder diverges from qemu signed result at {witness}");
}

#[test]
fn bridge_is_non_vacuous_corrupted_fixture_result_mismatches() {
    // Take the first ADD fact, corrupt its recorded qemu result by +1, and confirm
    // the in-house encoder now DISAGREES — proving the assertion actually compares
    // against the fixture value (not against itself).
    let facts = load_facts();
    let fact = facts.iter().find(|f| f.op == "add").expect("an ADD fact");
    let corrupted = Fact {
        op: fact.op.clone(),
        width: fact.width,
        operands: fact.operands.clone(),
        result: mask(fact.result.wrapping_add(1), fact.width),
        theorem: fact.theorem.clone(),
    };
    assert!(
        encoder_matches(fact),
        "sanity: the genuine ADD fact must match the in-house encoder"
    );
    assert!(
        !encoder_matches(&corrupted),
        "NON-VACUITY: corrupting the recorded qemu result did NOT change the comparison outcome — \
         the bridge is not actually comparing against the fixture value"
    );
}

#[test]
fn oracle_provenance_is_independent_qemu() {
    // The fixture MUST declare an INDEPENDENT executor (qemu), not an in-house
    // model — this is the property that lets the bridge defeat root-cause #2. A
    // FALLBACK (Clean B-def) fixture would NOT carry this oracle tag; a regression
    // that swapped the oracle for a second in-house model would be caught here.
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
}
