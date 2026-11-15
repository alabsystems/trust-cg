// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The CLI compiles the canonical bare `TRUST_IR` binary container under the
//! default `--format=binary` and under `--format=auto` (roadmap WS7.4,
//! finding F-115, ratchet row `LEAN.consumer.binary_container`).
//!
//! The container is the only variable: for every vendored fixture the object
//! compiled from the binary is byte-identical to the one compiled from the
//! same module's JSON twin, and a fixture the backend refuses is refused the
//! same way from both spellings. Fixtures: `tests/fixtures/
//! trust_ir_binary_container/` (provenance and sha256 in its `SOURCE.txt`).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use trust_ir::BUILD_IDENTITY;

/// The named refusal for bytes that are neither binary container.
const NOT_A_BINARY_MODULE: &str = "neither a TRUST_IR module nor a tMBC envelope";

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/trust_ir_binary_container")
}

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

/// A new scratch directory, removed when the returned guard is dropped.
fn scratch_dir(name: &str) -> scratch::ScratchDir {
    scratch::create(&format!("trust_cg_cli_binary_container_{name}_"))
}

/// Every vendored bare-binary fixture paired with its JSON twin.
fn binary_fixtures() -> Vec<(String, PathBuf, PathBuf)> {
    let mut fixtures = Vec::new();
    for directory in ["conformance", "clean", "pinned_writer"] {
        let entries = std::fs::read_dir(fixture_root().join(directory))
            .unwrap_or_else(|error| panic!("read fixture directory {directory}: {error}"));
        for entry in entries {
            let path = entry.expect("fixture directory entry").path();
            let Some(stem) = path.file_stem().and_then(|stem| stem.to_str()) else {
                continue;
            };
            if path.extension().and_then(|ext| ext.to_str()) != Some("tmbc")
                || stem.starts_with("compat_")
            {
                continue;
            }
            fixtures.push((
                format!("{directory}/{stem}"),
                path.clone(),
                path.with_extension("json"),
            ));
        }
    }
    fixtures.sort();
    fixtures
}

/// An explicit target, so the compiling set does not depend on the host.
const TARGET: &str = "aarch64-apple-darwin";

/// Compile `input` for [`TARGET`]. The corpus is the legacy conformance
/// corpus: most fixtures predate the v41 codegen license and decode to
/// `body_gate: None`, which the CLI refuses by default (roadmap WS7.5,
/// DG-73). This test is about the CONTAINER, so it compiles the corpus
/// under the explicit, disclosed `--permit-unlicensed`
/// (`default_license_refuses_the_claim_less_corpus` pins the default).
fn compile(format: Option<&str>, input: &Path, object: &Path) -> Output {
    let mut command = Command::new(trust_cg_bin());
    command
        .arg("--target")
        .arg(TARGET)
        .arg("--permit-unlicensed");
    if let Some(format) = format {
        command.arg(format!("--format={format}"));
    }
    command
        .arg("-c")
        .arg("-o")
        .arg(object)
        .arg(input)
        .output()
        .unwrap_or_else(|error| panic!("run trust-cg on {}: {error}", input.display()))
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Stderr with the input and object paths erased, so two refusals of the
/// same module from different spellings compare equal.
fn normalized_stderr(output: &Output, input: &Path, object: &Path) -> String {
    stderr(output)
        .replace(&input.display().to_string(), "<input>")
        .replace(&object.display().to_string(), "<object>")
}

/// The fixtures that compile to an object for [`TARGET`] FROM JSON. Since
/// WS7.3 the backend refuses every module trust-ir's codegen admission
/// refuses, so a fixture trust-ir refuses (several conformance fixtures are
/// format round-trip shapes, not valid modules) is refused by that finding;
/// those are pinned in [`NAMED_REFUSALS`]. Pinned as
/// a ratchet so a backend change that alters what this corpus reaches shows
/// up here by name. The others are refused by the backend (unsupported
/// instruction or type, the codegen license, the dataflow witness gate, the
/// adapter's trust-ir surface floor), the same way from binary and from JSON;
/// none is refused at load except the [`PRODUCER_OMITTED_GATE_FIXTURES`],
/// whose BINARY form the reader refuses before the backend sees it.
const COMPILING_FIXTURES: &[&str] = &[
    "clean/lean_library",
    "conformance/abi_enum_tag_repr",
    "conformance/b1_scalars",
    "conformance/bytes_constants",
    "conformance/certificate_binding",
    "conformance/chc_batch",
    "conformance/closure_frame_origin",
    "conformance/debug_metadata_v33",
    "conformance/frontend_emission_subset",
    "conformance/frontend_panic_obligations",
    "conformance/import_scheme",
    "conformance/inst_arithmetic",
    "conformance/inst_vector",
    "conformance/inst_vector_crosslane",
    "conformance/mixed_producer_module",
    "conformance/producer_provenance",
    "conformance/proof_diagnostics",
    "conformance/single_inhabited_enums",
    "conformance/spec_carrier",
    "conformance/storage_only",
    "conformance/text_directives",
    "conformance/ty_container_vtable",
    "conformance/ty_primitives",
    "conformance/u128_constants",
];

/// Fixtures whose BINARY form the reader refuses by trust-ir's PRODUCER rule
/// (KIND 4, 2026-09-24): the header declares the contract surface (v41+) and
/// a bodied function carries no codegen license, so the blob is a producer
/// omission, not pre-v41 content, and `pipeline::decode_binary` refuses it as
/// `PipelineError::ProducerOmittedBodyGate` — exactly what trust-ir's own
/// `trust-ir validate` reports for these files (measured 2026-09-25 on every
/// fixture here: `ProducerOmittedBodyGate`). The JSON twin carries no header
/// and so cannot be held to a declared version; it is judged by the backend
/// alone, which is the one asymmetry the agreement test below admits, by
/// name. Exact in both directions: a binary refusal by this rule on an
/// unlisted fixture, or a listed fixture the reader no longer refuses, fails.
const PRODUCER_OMITTED_GATE_FIXTURES: &[&str] = &[
    "conformance/abi_calling_conv",
    "conformance/abi_enum_tag_repr",
    "conformance/abi_function_symbol",
    "conformance/body_gate",
    "conformance/composition",
    "conformance/import_scheme",
    "conformance/spec_carrier",
    "conformance/storage_only",
    "conformance/text_directives",
];

const PRODUCER_OMITTED_GATE_TEXT: &str = "has a body but no codegen license";

/// Fixtures the backend refuses by a NAMED rule, pinned with that rule's exact
/// diagnostic so a refusal cannot drift into a different one unnoticed.
///
/// `func_param_abi` declares `TargetInfo.struct_passing = AlwaysMemory`
/// (`structpass=always_memory` in its text form). Since trust-cg `4427c5432`
/// (WS7.17) the adapter's target floor refuses that policy by name
/// (`AdapterError::TargetStructPassingUnsupported`) before any function is
/// lowered, so the module never reaches its byval parameter; the
/// `[TCG-BYVAL-ABI]` refusal itself stays pinned by `tests/abi_refusals.rs`.
/// `abi_function_symbol` states a v45 `protected` visibility on a function
/// declaration, which the v45 function-surface floor (trust-cg `c1b5db26b`)
/// refuses because no emitter honours it. `pinned_writer/crystal_lane_v49`
/// (the v47-v49 drop, weak compare-exchange and unwritten lane, at wire v49)
/// wears an explicit `ungated` license, the only stamp a v41+ blob can carry
/// here without evidence, so the license refuses it before the adapter floor
/// that refuses each construct (`tests/pin_move_floor.rs` in trust-cg-lower).
/// The goldens `assert_kind` (v52) and `proof_surface` (WS4.4), vendored at
/// trust-ir 8cf20223, wear the same explicit `ungated` license and are refused
/// the same way. `inst_control` compiled until the v52 panic cohort (trust-cg
/// `acb3403fe`): its `dispatch` asserts without a panic kind, which trust-ir's
/// codegen admission now refuses (`require_assert_panic_kinds`, fail-closed
/// Assert semantics) because no Rust panic states what a failed check lowers
/// to. Since WS7.3 the ingestion validator refuses it first, by trust-ir's
/// own finding (`TargetInfoRequired`, pinned below: its cross-convention
/// indirect edge is an FFI boundary with no pinned target); the panic-kind
/// rule stays pinned by the CLI must-refuse row `assert_panic_kind_unspecified`
/// (`tests/must_refuse_corpus.rs`). The v53 golden `call_unwind_boundary` (trust-ir 8a0d54c0) wears the
/// same explicit `ungated` license and is refused the same way, before the
/// adapter floor that refuses its `call_cannot_unwind` /
/// `call_indirect_cannot_unwind` by name (`tests/pin_move_floor.rs` and the
/// construct inventory in trust-cg-lower). The v54 panic-site goldens
/// `assert_panic_site` and `assert_invoke` (trust-ir 6f2dfce6) wear it too and
/// are refused the same way, before the adapter floor's assert clause that
/// refuses a sited `Inst::Assert` and `Inst::AssertInvoke` by name (the same
/// trust-cg-lower tests, and the conformance manifest).
/// `text_directives`, refused before for its `crc` target feature,
/// compiles since the AArch64 23-feature vocabulary with CRC32 (trust-cg
/// `b76494e32`, L03-P9).
/// `lean_library_envelope` compiled until the trust-ir v61 pin (cb639776):
/// its `addmul` wears the evidence-bound `clean-kernel-tv` license with a
/// kernel certificate but no `GateEvidence` (it predates v61), the shape of
/// trust-ir's must-refuse row `body_gate_kernel_tv_evidence_unrecorded`, so
/// the admission's license-evidence layer refuses it by name
/// (`AdapterError::UnevidencedGate`, decision record
/// OD-V61-GATE-EVIDENCE-20261014). The v61 golden `certificate_binding`, whose
/// two `clean-kernel-tv` licenses carry evidence that holds, compiles: its
/// certificates are bound to the pinned Clean environment, so a Clean pin that
/// moves that environment needs the golden re-vendored (trust-ir 8d304e36
/// regenerated it for Clean 80f09a7e9; `SOURCE.txt`). The v62 golden
/// `param_pointee_place` (trust-ir 8d304e36) wears the explicit `ungated`
/// license on `bump` and is refused by it, like `proof_surface`.
/// The three dialect rows are refused by the codegen's default dialect
/// legalization registry (`L05-P11`): `inst_dialect`'s opaque payload fails the
/// `verif` v1 grammar, `inst_vector_dialect` reads two parameter masks the
/// backend has no lane image for, and `ty_dialect_v39`'s namespace has no
/// registration (`tests/dialect_legalization_corpus.rs` in trust-cg-codegen
/// executes all three under the registrations that admit them).
const NAMED_REFUSALS: &[(&str, &str)] = &[
    (
        "conformance/tensor_map_reduce_view",
        "is affirmatively ungated",
    ),
    (
        "conformance/tensor_contract",
        "function `matmul` is affirmatively ungated",
    ),
    (
        "conformance/make_closure",
        "function `add_lo_hi` is licensed by gate authority \"conformance-fixture\" (trust-ir v41), which this backend does not recognize",
    ),
    (
        "pinned_writer/runtime_closure_v63",
        "adapter error: function `host` is affirmatively ungated (`body_gate: ungated`, trust-ir \
         v41): the producer states that no verification gate was applied to this body, so codegen \
         refuses it",
    ),
    (
        "conformance/assert_kind",
        "adapter error: function `bounds` is affirmatively ungated (`body_gate: ungated`, trust-ir \
         v41): the producer states that no verification gate was applied to this body, so codegen \
         refuses it",
    ),
    (
        "conformance/call_unwind_boundary",
        "adapter error: function `identity` is affirmatively ungated (`body_gate: ungated`, \
         trust-ir v41): the producer states that no verification gate was applied to this body, \
         so codegen refuses it",
    ),
    (
        "conformance/assert_invoke",
        "adapter error: function `guarded` is affirmatively ungated (`body_gate: ungated`, \
         trust-ir v41): the producer states that no verification gate was applied to this body, \
         so codegen refuses it",
    ),
    (
        "conformance/assert_panic_site",
        "adapter error: function `bounds` is affirmatively ungated (`body_gate: ungated`, \
         trust-ir v41): the producer states that no verification gate was applied to this body, \
         so codegen refuses it",
    ),
    (
        "conformance/proof_surface",
        "adapter error: function `bump` is affirmatively ungated (`body_gate: ungated`, trust-ir \
         v41): the producer states that no verification gate was applied to this body, so codegen \
         refuses it",
    ),
    (
        "conformance/param_pointee_place",
        "adapter error: function `bump` is affirmatively ungated (`body_gate: ungated`, trust-ir \
         v41): the producer states that no verification gate was applied to this body, so codegen \
         refuses it",
    ),
    (
        "conformance/lean_library_envelope",
        "adapter error: function `addmul` is licensed by the evidence-bound gate authority \
         \"clean-kernel-tv\" with no GateEvidence (trust-ir v61): the license names neither the \
         obligation it rests on nor the body it was granted to, so codegen refuses it",
    ),
    (
        "conformance/inst_dialect",
        "[TCG-DIALECT-GRAMMAR] `verif.bfs_step` (in function `dialect_roundtrip`) violates the \
         `verif` v1 registration's grammar",
    ),
    (
        "conformance/inst_vector_dialect",
        "[TCG-DIALECT-UNBOUND] `vector.mask_to_bits` (in function `portable_vector_dialect`) is \
         registered by the `vector` v1 registration but has no lowering in this registry",
    ),
    (
        "conformance/ty_dialect_v39",
        "[TCG-DIALECT-UNREGISTERED] dialect `example` (used by nominal type `example.value@1`) \
         has no legalization registered in this backend",
    ),
    (
        "conformance/abi_function_symbol",
        "adapter error: function `imported_protected` states trust-ir v45 `visibility` = \
         protected, which this backend has no emitter for; refusing rather than emit an object \
         that does not implement the IR it claims",
    ),
    (
        "pinned_writer/crystal_lane_v49",
        "adapter error: function `crystal_lane` is affirmatively ungated (`body_gate: ungated`, \
         trust-ir v41): the producer states that no verification gate was applied to this body, \
         so codegen refuses it",
    ),
    (
        "conformance/func_param_abi",
        "adapter error: module `func_param_abi` declares aggregate passing policy AlwaysMemory \
         (`TargetInfo.struct_passing`), but this backend passes aggregates by the native C ABI; \
         refusing rather than change every aggregate call's ABI",
    ),
    // WS7.3 ingestion admission: trust-ir's own findings, by name.
    // `composition` cites a proof-bearing import this lone module cannot
    // authenticate (the authority tier's import rule).
    ("conformance/composition", "UnauthenticatedImport"),
    // A cross-convention indirect edge is an FFI boundary; no target is pinned.
    ("conformance/inst_control", "TargetInfoRequired"),
    // A proof-annotation round-trip corpus: conflicting memory roles first.
    (
        "conformance/proof_annotations",
        "ConflictingFunctionMemoryRoles",
    ),
];

/// Positive (ratchet LEAN.consumer.binary_container CONSUMER-GAP -> PASS):
/// the binary and auto spellings agree with the JSON spelling for every
/// fixture, byte for byte when the backend compiles it.
#[test]
fn bare_trust_ir_binary_compiles_like_its_json_twin() {
    let dir = scratch_dir("agree");
    let mut compiled = Vec::new();
    for (name, binary, json) in binary_fixtures() {
        let tag = name.replace('/', "__");
        let json_object = dir.join(format!("{tag}.json.o"));
        let from_json = compile(Some("json"), &json, &json_object);
        let producer_omitted_gate = PRODUCER_OMITTED_GATE_FIXTURES.contains(&name.as_str());
        for format in [None, Some("auto")] {
            let object = dir.join(format!("{tag}.{}.o", format.unwrap_or("default")));
            let from_binary = compile(format, &binary, &object);
            let text = stderr(&from_binary);
            assert!(
                !text.contains("tMBC magic") && !text.contains(NOT_A_BINARY_MODULE),
                "{name} ({format:?}): the container was refused: {text}"
            );
            // The reader's producer rule: fires exactly on the listed
            // fixtures, refuses without an object, and is the one outcome the
            // header-less JSON twin cannot share.
            assert_eq!(
                text.contains(PRODUCER_OMITTED_GATE_TEXT),
                producer_omitted_gate,
                "{name} ({format:?}): PRODUCER_OMITTED_GATE_FIXTURES lists it = \
                 {producer_omitted_gate}, the reader's producer rule fired = {}: {text}",
                text.contains(PRODUCER_OMITTED_GATE_TEXT)
            );
            if producer_omitted_gate {
                assert!(
                    !from_binary.status.success(),
                    "{name} ({format:?}): compiled"
                );
                assert!(
                    !object.exists(),
                    "{name} ({format:?}): object after refusal"
                );
                continue;
            }
            assert_eq!(
                from_binary.status.success(),
                from_json.status.success(),
                "{name} ({format:?}): binary and JSON outcomes differ.\nbinary: {text}\njson: {}",
                stderr(&from_json)
            );
            if from_json.status.success() {
                let binary_bytes = std::fs::read(&object).expect("binary object");
                let json_bytes = std::fs::read(&json_object).expect("JSON object");
                assert!(
                    binary_bytes == json_bytes,
                    "{name} ({format:?}): objects differ ({} vs {} bytes)",
                    binary_bytes.len(),
                    json_bytes.len()
                );
            } else {
                assert!(
                    !object.exists(),
                    "{name} ({format:?}): object after refusal"
                );
                assert_eq!(
                    normalized_stderr(&from_binary, &binary, &object),
                    normalized_stderr(&from_json, &json, &json_object),
                    "{name} ({format:?}): refusals differ"
                );
            }
        }
        if let Some((_, rule)) = NAMED_REFUSALS.iter().find(|(fixture, _)| *fixture == name) {
            assert!(
                !from_json.status.success() && stderr(&from_json).contains(rule),
                "{name}: expected the named refusal {rule}: {}",
                stderr(&from_json)
            );
        }
        if from_json.status.success() {
            compiled.push(name);
        }
    }
    assert_eq!(compiled, COMPILING_FIXTURES);
    let _ = std::fs::remove_dir_all(&dir);
}

/// Negative twin: the Clean artifact with `TRUST_IR` mutated to `TRUST_IS`
/// is refused under both formats, by name, with no object written. The
/// unmutated artifact compiling in the test above is the mutation control.
#[test]
fn near_miss_magic_is_refused_by_name() {
    let dir = scratch_dir("near_miss");
    let mut bytes = std::fs::read(fixture_root().join("clean/lean_library.tmbc")).expect("read");
    assert_eq!(&bytes[..8], b"TRUST_IR");
    bytes[7] = b'S';
    let input = dir.join("lean_library.tmbc");
    std::fs::write(&input, &bytes).expect("write");
    for format in [None, Some("auto")] {
        let object = dir.join(format!("{}.o", format.unwrap_or("default")));
        let output = compile(format, &input, &object);
        let text = stderr(&output);
        assert!(!output.status.success(), "{format:?}: accepted TRUST_IS");
        assert!(text.contains(NOT_A_BINARY_MODULE), "{format:?}: {text}");
        assert!(
            text.contains("54 52 55 53 54 5f 49 53"),
            "{format:?}: {text}"
        );
        assert!(!object.exists(), "{format:?}: object after refusal");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Adversarial: a bare blob in the ambiguous-lineage range, or newer than the
/// pinned reader, is refused with trust-ir's version error, not "tMBC magic".
/// Both versions come from the linked reader's own `BUILD_IDENTITY`, so a pin
/// move cannot leave this probing a version the new reader accepts.
#[test]
fn bare_blob_outside_the_reader_window_is_refused_by_trust_ir() {
    let dir = scratch_dir("version_window");
    let good = std::fs::read(fixture_root().join("clean/lean_library.tmbc")).expect("read");
    let ambiguous = BUILD_IDENTITY.refused_read_versions.0;
    let too_new = BUILD_IDENTITY.wire_version + 1;
    for version in [ambiguous, too_new] {
        assert!(!BUILD_IDENTITY.reads(version), "v{version}");
        let mut bytes = good.clone();
        bytes[8..12].copy_from_slice(&version.to_le_bytes());
        let input = dir.join(format!("v{version}.tmbc"));
        std::fs::write(&input, &bytes).expect("write");
        for format in [None, Some("auto")] {
            let object = dir.join(format!("v{version}.{}.o", format.unwrap_or("default")));
            let output = compile(format, &input, &object);
            let text = stderr(&output);
            assert!(!output.status.success(), "v{version} {format:?}: accepted");
            assert!(
                text.contains("failed to deserialize TRUST_IR module: unsupported version"),
                "v{version} {format:?}: {text}"
            );
            assert!(!text.contains("tMBC"), "v{version} {format:?}: {text}");
            assert!(
                !object.exists(),
                "v{version} {format:?}: object after refusal"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Review adversary: inputs that are not a binary container at all (empty,
/// `.trust_ir` text, JSON, a tMBC envelope around a tMBC envelope) are refused
/// under the default binary format with no object written. Widening the
/// binary path to a second magic must not widen it to anything else.
#[test]
fn review_non_binary_inputs_are_refused_under_the_default_format() {
    let dir = scratch_dir("non_binary");
    let json = std::fs::read(fixture_root().join("conformance/b1_scalars.json")).expect("read");
    let bare = std::fs::read(fixture_root().join("conformance/b1_scalars.tmbc")).expect("read");
    let mut once = b"tMBC".to_vec();
    once.extend_from_slice(&1u32.to_le_bytes());
    once.extend_from_slice(&bare);
    let mut twice = b"tMBC".to_vec();
    twice.extend_from_slice(&1u32.to_le_bytes());
    twice.extend_from_slice(&once);
    let cases: [(&str, &[u8], &str); 4] = [
        ("empty", b"", NOT_A_BINARY_MODULE),
        (
            "text",
            b"; TrustIr text format v1\nmodule \"m\"\n",
            NOT_A_BINARY_MODULE,
        ),
        ("json", &json, NOT_A_BINARY_MODULE),
        (
            "double_envelope",
            &twice,
            "failed to deserialize tMBC payload",
        ),
    ];
    for (name, bytes, reason) in cases {
        let input = dir.join(format!("{name}.tmbc"));
        std::fs::write(&input, bytes).expect("write");
        let object = dir.join(format!("{name}.o"));
        let output = compile(None, &input, &object);
        let text = stderr(&output);
        assert!(!output.status.success(), "{name}: accepted");
        assert!(text.contains(reason), "{name}: {text}");
        assert!(!object.exists(), "{name}: object after refusal");
    }
    // Positive control: the single envelope around the same payload compiles.
    let input = dir.join("once.tmbc");
    std::fs::write(&input, &once).expect("write");
    let object = dir.join("once.o");
    let output = compile(None, &input, &object);
    assert!(
        output.status.success(),
        "single envelope: {}",
        stderr(&output)
    );
    assert!(object.exists());
    let _ = std::fs::remove_dir_all(&dir);
}

/// WS4.9 companion (F-115): the container is trust-ir's `codec::sniff_format`
/// answer, and the default-format refusal says what the sniff read the bytes
/// as, in trust-ir's own words (`SniffedFormat::describe`), so the user sees
/// which `--format` the file wanted. The same bytes under the format the claim
/// names compile: the positive control that the claim is the right one.
#[test]
fn default_format_refusal_names_what_trust_ir_sniffs() {
    use trust_ir::codec::{SniffedFormat, sniff_format};

    let dir = scratch_dir("sniff_claim");
    let json = std::fs::read(fixture_root().join("conformance/b1_scalars.json")).expect("read");
    assert_eq!(sniff_format(&json), Some(SniffedFormat::Json));
    let input = dir.join("b1_scalars.tmbc");
    std::fs::write(&input, &json).expect("write");

    let object = dir.join("refused.o");
    let output = compile(None, &input, &object);
    let text = stderr(&output);
    assert!(!output.status.success(), "accepted JSON as binary");
    assert!(text.contains(NOT_A_BINARY_MODULE), "{text}");
    assert!(text.contains(SniffedFormat::Json.describe()), "{text}");
    assert!(!text.contains(SniffedFormat::Text.describe()), "{text}");
    assert!(!object.exists(), "object after refusal");

    let object = dir.join("json.o");
    let output = compile(Some("json"), &input, &object);
    assert!(
        output.status.success(),
        "positive control, --format=json: {}",
        stderr(&output)
    );
    assert!(object.exists());

    // Review twin (WS4.9): the same module as `.trust_ir` text names the TEXT
    // claim and not the JSON one, so the claim follows the bytes rather than
    // being a fixed hint; `--format=text` then compiles it.
    let module: trust_ir::Module =
        serde_json::from_slice(&json).expect("the JSON twin is a module");
    let text = format!("{module}");
    assert_eq!(
        sniff_format(text.as_bytes()),
        Some(SniffedFormat::Text),
        "{text}"
    );
    let input = dir.join("b1_scalars_text.tmbc");
    std::fs::write(&input, &text).expect("write");
    let object = dir.join("text_refused.o");
    let output = compile(None, &input, &object);
    let refusal = stderr(&output);
    assert!(!output.status.success(), "accepted text as binary");
    assert!(refusal.contains(NOT_A_BINARY_MODULE), "{refusal}");
    assert!(
        refusal.contains(SniffedFormat::Text.describe()),
        "{refusal}"
    );
    assert!(
        !refusal.contains(SniffedFormat::Json.describe()),
        "{refusal}"
    );
    assert!(!object.exists(), "object after refusal");

    let object = dir.join("text.o");
    let output = compile(Some("text"), &input, &object);
    assert!(
        output.status.success(),
        "positive control, --format=text: {}",
        stderr(&output)
    );
    assert!(object.exists());
    let _ = std::fs::remove_dir_all(&dir);
}

#[path = "common/scratch.rs"]
mod scratch;

/// The default license (roadmap WS7.5, DG-73): without `--permit-unlicensed`
/// a claim-less corpus fixture is REFUSED by name from both spellings, and so
/// is a license whose evidence the admission does not find, while a fixture
/// whose licenses carry evidence that holds compiles with no flag at all: the
/// v61 golden `certificate_binding`, both of whose `Gated{"clean-kernel-tv"}`
/// licenses are bound by `GateEvidence` to kernel-rechecked TranslationValidation
/// certificates. The Lean envelope was that positive control until the trust-ir
/// v61 pin (cb639776): its pre-v61 `clean-kernel-tv` license records no
/// evidence, and the admission refuses it by name (`UnevidencedGate`,
/// OD-V61-GATE-EVIDENCE-20261014; decision record LD-82).
#[test]
fn default_license_refuses_the_claim_less_corpus() {
    let dir = scratch_dir("default_license");
    let root = fixture_root();
    // (fixture, the named refusal it must meet, or None: it compiles)
    for (name, refusal) in [
        (
            "conformance/inst_arithmetic",
            Some("carries no codegen license"),
        ),
        (
            "conformance/lean_library_envelope",
            Some(
                "is licensed by the evidence-bound gate authority \"clean-kernel-tv\" with no \
                 GateEvidence (trust-ir v61)",
            ),
        ),
        ("conformance/certificate_binding", None),
    ] {
        let expect_ok = refusal.is_none();
        for (format, extension) in [(None, "tmbc"), (Some("json"), "json")] {
            let input = root.join(format!("{name}.{extension}"));
            let object = dir.join(format!("{}.{extension}.o", name.replace('/', "__")));
            let mut command = Command::new(trust_cg_bin());
            command.arg("--target").arg(TARGET);
            if let Some(format) = format {
                command.arg(format!("--format={format}"));
            }
            let output = command
                .arg("-c")
                .arg("-o")
                .arg(&object)
                .arg(&input)
                .output()
                .expect("run trust-cg");
            let text = stderr(&output);
            assert_eq!(
                output.status.success(),
                expect_ok,
                "{name} ({format:?}): {text}"
            );
            assert!(
                !text.contains("--permit-unlicensed: '"),
                "{name}: nothing disclosed: {text}"
            );
            if let Some(refusal) = refusal {
                assert!(text.contains(refusal), "{name}: {text}");
                assert!(!object.exists(), "{name}: object after refusal");
            } else {
                assert!(object.exists(), "{name}: no object after success");
            }
        }
    }
}
