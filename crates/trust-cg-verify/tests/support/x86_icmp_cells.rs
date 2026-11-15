// trust-cg-verify/tests/support/x86_icmp_cells.rs - the x86-64 vector-compare
// cell table: which ground each cell rests on, and the certified query pins.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// One table, two readers: `tests/x86_icmp_manifest_cells.rs` pins it against
// the code (query bytes, degeneracy, evaluation, the spec side, the instruction
// models), and `examples/x86_icmp_certificate_queries.rs` dumps each cell's
// query with its pin, its ground and the certificate rule for
// `scripts/check_x86_icmp_certificates.py`, which re-runs the certificate (AY
// `--strict-proofs` + Clean `cert verify-external`, both named by
// `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`) on exactly those bytes.

#![allow(dead_code)]

use sha2::{Digest, Sha256};
use trust_cg_verify::ay_bridge::{AYConfig, DEFAULT_AY_TIMEOUT_MS, generate_smt2_query};
use trust_cg_verify::lowering_proof::ProofObligation;
use trust_ir::{ChcX86IcmpGround, ICmpOp};

pub const OPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

/// `(lane bits, lanes, obligation shape name)` of each `chc_x86` descriptor.
pub const SHAPES: [(u32, u32, &str); 4] = [
    (32, 4, "V4I32"),
    (64, 2, "V2I64"),
    (8, 16, "V16I8"),
    (16, 8, "V8I16"),
];

/// sha256 of `generate_smt2_query(obligation, timeout DEFAULT_AY_TIMEOUT_MS)`
/// for every CERTIFICATE-ground cell: `(shape, cond, digest)`. Each query is
/// one the AY of `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE` answers `unsat`
/// under `--strict-proofs` with `unproved_steps=0` and a proof the rule's
/// Clean `cert verify-external` accepts in full (exit 0, no `hole`, no
/// `lia_generic`). `scripts/check_x86_icmp_certificates.py` (a
/// `scripts/soundness_check.sh` leg) re-runs exactly that on these bytes; the
/// certifying run of this table is in
/// reports/2026-10-09-x86-icmp-certificate-rule-as-code.md.
///
/// The sixteen unsigned rows are the queries of the PER-LANE sign-bit bias
/// spelling, the one the lowering materializes. From 2026-09-27 (`65c99316a`)
/// until the pin move that adopted the rule, they were the queries of a
/// two-64-bit-halves spelling that worked around a tree-sized node cap in AY
/// `f28345ff`'s proof-producing bit-blast checker; AY fixed that at the root,
/// and the per-lane bytes are those certified before the workaround (the twelve
/// `v4_i32`/`v2_i64`/`v8_i16` rows equal `65c99316a^`'s pins). The sixteen
/// `ne`/`slt`/`sle`/`sge` rows did not move.
pub const CERTIFIED_QUERY_SHA256: &[(&str, &str, &str)] = &[
    (
        "V8I16",
        "Ult",
        "ba48e3297873370e352497e82d5942bbcf64884132217ea7510f282301531bad",
    ),
    (
        "V8I16",
        "Ule",
        "0968262798801fd40cb4535f4d6cb0f40c729074286a763ceeae0cb611e8c2b1",
    ),
    (
        "V8I16",
        "Ugt",
        "71569ebf30ab3806f0b3324514d3894ea99a58a99250dce6b6d48e290af00486",
    ),
    (
        "V8I16",
        "Uge",
        "34f6656eb341fd37769fe0f402a0afe8d2b42bc52a04f3280dea5ae5ebccc287",
    ),
    (
        "V4I32",
        "Ult",
        "6ed4ba480e877e8002c4ede06ccdef221326e6f6bb8a988fee94e82381092410",
    ),
    (
        "V4I32",
        "Ule",
        "338b629ca65d23424586112edf550909858a03413b445d9d38cec4ad2452edf0",
    ),
    (
        "V4I32",
        "Ugt",
        "29226ed1bb1d5b29450bc97baf4bf8255e3d0d9bb741e89725bafd916b04480a",
    ),
    (
        "V4I32",
        "Uge",
        "0a53bc0fc6e92ad5f48181dd3a98644035ec59486004eeb58caeff6a03a303eb",
    ),
    (
        "V2I64",
        "Ult",
        "5850d6e35d82d9d8c60812e99783a94aca3e2b145545c5043f7cf50955fb5075",
    ),
    (
        "V2I64",
        "Ule",
        "b996168cc001643e06b291781b30f5afcd860221e6ead4236219ae2f570cb9d8",
    ),
    (
        "V2I64",
        "Ugt",
        "fb754cb5b2cde9017dd11013a68104678f6e21d81d06820af591769837b88a09",
    ),
    (
        "V2I64",
        "Uge",
        "05a536433f334548274ab512303db707603d34e1b856b0eff551af707961b6f0",
    ),
    // Signed composites (ne / slt / sle / sge), recomputed at this landing.
    (
        "V4I32",
        "Ne",
        "58995b86d20d406d260b247d3a6ee951177c96a59b35ff9d790933cc1ab9168a",
    ),
    (
        "V4I32",
        "Slt",
        "22d25a6804d90b5d5814bda0c044aa8de87d246194ce83ad6c0896f46538e7b0",
    ),
    (
        "V4I32",
        "Sle",
        "19528d91ecf9bd8a3fe227f7bedaea81c31ac8d6f4da77587d47f67e53f8b533",
    ),
    (
        "V4I32",
        "Sge",
        "82081290576432736ef0e2812fac6f33a321dabd2c5a9f23c94786384a32d8f7",
    ),
    (
        "V2I64",
        "Ne",
        "86b5ae2691f6836c7cccf69ebb74318945f05c64c0ed8038c496653a8db71053",
    ),
    (
        "V2I64",
        "Slt",
        "3d5099e7b62343163913f76180d7ef6e7975b1fdd0a041471f078ea4125aa823",
    ),
    (
        "V2I64",
        "Sle",
        "e9c817517bcc39358fdf23d9e2789ecdb5845fed0a52d28daa1e34fb5dcaf602",
    ),
    (
        "V2I64",
        "Sge",
        "36e890b945a1d8361c5867907de23da04effa9fd2a38eb6b63e4d1c3e727bd3e",
    ),
    (
        "V16I8",
        "Ne",
        "7f7b56c45947daaa985126bd5dcd469469027fa499e868b836a634c6a4c011f6",
    ),
    (
        "V16I8",
        "Slt",
        "43da672021146d13982406715583b33ef3aaed9d99af353905d82a4fe71330c0",
    ),
    (
        "V16I8",
        "Sle",
        "9fac34d42a1880f9c565d7b234795a599ef397e4454d62ea6cc33eb255f6b216",
    ),
    (
        "V16I8",
        "Sge",
        "3861d90ab0bb1aef8a9a6e10a6964a6eedd9bf2616996c1b5a3fc565ebfca6eb",
    ),
    (
        "V8I16",
        "Ne",
        "2f4a09334793316b53d602c0c48f145cab5a668838f332bc5000bbcad12c0f2d",
    ),
    (
        "V8I16",
        "Slt",
        "9e169f2bc4cf233a614a3293d81c3c645175cc68d2aed0fe8bfa16764d0f1230",
    ),
    (
        "V8I16",
        "Sle",
        "ab634a9c760bce5ef4966ccc3b1bc22e0790659d11039f57f4cc854f94f550f1",
    ),
    (
        "V8I16",
        "Sge",
        "4b459296025dfa174cc030e2e4bdcf4b452c2d4a73a9e280048687749c0ca980",
    ),
    // Available since trust-ir 72dee4b6 (pin 8e81e98a); per-lane bytes since
    // the certificate rule became code.
    (
        "V16I8",
        "Ult",
        "dbbbd2c15e1096f35ced8cb2f3f659357a86d174d9e2076a5b667f6950ede8c5",
    ),
    (
        "V16I8",
        "Ule",
        "d400c9b75d5a55b72f1270b3a2792391350f634a22428bfbdde9db6875f8a9c6",
    ),
    (
        "V16I8",
        "Ugt",
        "5d413777b073d98047be08473938f13b2939340e53d10efd81309117abd02c79",
    ),
    (
        "V16I8",
        "Uge",
        "25077d0fb9ac9be017105aef87f59cbcc5bf0584cec1c389cb98f81ede4a3b34",
    ),
];

/// REVIEWED FAIL-CLOSED: `(shape, cond)` of every covered cell the pinned
/// trust-ir manifest answers fail-closed, exactly. A cell trust-ir defers
/// fails `fail_closed_icmp_cells_carry_no_certificate_pin` until it is
/// reviewed and listed here, and a listed cell the manifest makes available
/// fails until its row is deleted (`deferred_cell_findings`). This is the
/// one place a deferred cell is reviewed; `x86_vector_icmp_admission.rs`
/// (trust-cg-lower) holds admission equal to the manifest for whatever set
/// the reader answers. Empty at this pin: no covered cell is fail-closed, and
/// `fail_closed_icmp_cells_carry_no_certificate_pin` fails at any pin whose
/// reader answers one while this table is empty.
pub const REVIEWED_FAIL_CLOSED_CELLS: &[(&str, &str)] = &[];

/// MEASURED, NOT ADMITTED: `(shape, cond, digest)` of a cell the pinned
/// trust-ir manifest still calls fail-closed (so a row of
/// [`REVIEWED_FAIL_CLOSED_CELLS`]), whose exact query has been certified under
/// the same bar as [`CERTIFIED_QUERY_SHA256`] (AY `unsat` under
/// `--strict-proofs`, `unproved_steps=0`; Clean fully verified). A row here
/// grants nothing: the x86-64 module entry keeps refusing the cell until
/// trust-ir publishes it available and this backend's trust-ir pin moves
/// there. That move must carry each row into [`CERTIFIED_QUERY_SHA256`] — a
/// row naming an available cell fails
/// `fail_closed_icmp_cells_carry_no_certificate_pin`, and an available cell
/// with no certified pin fails `available_icmp_cells_rest_on_their_named_ground`.
/// The certificate gate re-runs only [`CERTIFIED_QUERY_SHA256`] rows.
///
/// Empty at this pin. Its last rows, the four unsigned `V16I8` compares, moved
/// into [`CERTIFIED_QUERY_SHA256`] with the pin move to trust-ir `8e81e98a`,
/// whose manifest (trust-ir `72dee4b6`) publishes them available.
pub const MEASURED_NOT_ADMITTED_QUERY_SHA256: &[(&str, &str, &str)] = &[];

/// The ground trust-ir's per-cell rule assigns a cell (`docs/dialects.md`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ground {
    /// (a) one instruction whose model IS the predicate: a degenerate
    /// obligation, no certificate claimed.
    InstructionModel,
    /// (b) a non-degenerate composition obligation whose exact query carries
    /// a checked certificate under `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`.
    Certificate,
    /// Not available: refused at x86-64 module entry, no ground.
    FailClosed,
}

impl Ground {
    pub fn name(self) -> &'static str {
        match self {
            Ground::InstructionModel => "instruction-model",
            Ground::Certificate => "certificate",
            Ground::FailClosed => "fail-closed",
        }
    }
}

/// The rule's ground for the `icmp.<op>` cell of `<lanes x i<lane_bits>>`, as
/// trust-ir answers it (`trust_ir::chc_x86_vector_icmp_cell_ground`, the
/// projection of the cell reader): never re-derived here. A cell trust-ir
/// answers no ground for (fail-closed, or no descriptor) has none. A
/// certificate ground must name THE rule constant this crate compiled against.
pub fn rule_ground(lane_bits: u32, lanes: u32, op: ICmpOp) -> Ground {
    match trust_ir::chc_x86_vector_icmp_cell_ground(lane_bits, lanes, op) {
        None => Ground::FailClosed,
        Some(ChcX86IcmpGround::InstructionModel) => Ground::InstructionModel,
        Some(ChcX86IcmpGround::Certificate(rule)) => {
            assert_eq!(
                *rule,
                trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE,
                "a certificate ground names a rule other than CHC_X86_ICMP_CERTIFICATE_RULE"
            );
            Ground::Certificate
        }
    }
}

pub fn shape_name(lane_bits: u32, lanes: u32) -> Option<&'static str> {
    SHAPES
        .iter()
        .find(|(bits, count, _)| *bits == lane_bits && *count == lanes)
        .map(|(_, _, name)| *name)
}

pub fn cond_name(op: ICmpOp) -> &'static str {
    match op {
        ICmpOp::Eq => "Eq",
        ICmpOp::Ne => "Ne",
        ICmpOp::Ult => "Ult",
        ICmpOp::Ule => "Ule",
        ICmpOp::Ugt => "Ugt",
        ICmpOp::Uge => "Uge",
        ICmpOp::Slt => "Slt",
        ICmpOp::Sle => "Sle",
        ICmpOp::Sgt => "Sgt",
        ICmpOp::Sge => "Sge",
    }
}

pub fn manifest_operation(op: ICmpOp) -> String {
    format!("icmp.{}", cond_name(op).to_ascii_lowercase())
}

/// The exact SMT-LIB bytes the certificate is about.
pub fn query_text(obligation: &ProofObligation) -> String {
    let config = AYConfig {
        timeout_ms: DEFAULT_AY_TIMEOUT_MS,
        ..AYConfig::default()
    };
    generate_smt2_query(obligation, &config)
}

pub fn query_sha256(obligation: &ProofObligation) -> String {
    let digest = Sha256::digest(query_text(obligation).as_bytes());
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Every obligation registered for `(shape, cond)`.
pub fn obligations<'a>(
    proofs: &'a [ProofObligation],
    shape: &str,
    cond: &str,
) -> Vec<&'a ProofObligation> {
    let prefix = format!("x86_64: {shape}Icmp_{cond} -> ");
    proofs
        .iter()
        .filter(|ob| ob.name.starts_with(&prefix))
        .collect()
}

/// The one registered obligation for `(shape, cond)`.
pub fn obligation<'a>(
    proofs: &'a [ProofObligation],
    shape: &str,
    cond: &str,
) -> Result<&'a ProofObligation, String> {
    match obligations(proofs, shape, cond).as_slice() {
        [one] => Ok(one),
        other => Err(format!(
            "{shape} {cond}: {} obligations registered, expected exactly one",
            other.len()
        )),
    }
}

/// The certified digest pinned for `(shape, cond)`, if any.
pub fn certified_pin(shape: &str, cond: &str) -> Option<&'static str> {
    CERTIFIED_QUERY_SHA256
        .iter()
        .find(|(s, c, _)| *s == shape && *c == cond)
        .map(|(_, _, digest)| *digest)
}
