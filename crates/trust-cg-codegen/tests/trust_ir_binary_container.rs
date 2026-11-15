// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The binary loader accepts the canonical bare `TRUST_IR` container as well
//! as trust-cg's `tMBC` envelope (roadmap WS7.4, finding F-115).
//!
//! Before WS7.4 the `Tmbc` path refused anything without `tMBC`, so trust-ir's
//! own conformance `.tmbc` fixtures and Clean's `--emit trustir-bin` output
//! were refused with "invalid tMBC magic". The container is now chosen by
//! magic. Everything else still fails closed: a near-miss magic is refused by
//! name, and a bare blob outside the pinned reader's version window is refused
//! by trust-ir's own decoder, never decoded partially.
//!
//! Which container a buffer is, is trust-ir's answer, not trust-cg's: every
//! entry point asks `trust_ir::codec::sniff_format` (the WS4.9 companion of
//! F-115), so the `TRUST_IR` magic is spelled once, in trust-ir's codec. The
//! sniff-agreement tests below pin that over a corpus reaching every answer
//! the sniff gives.
//!
//! Fixtures: `tests/fixtures/trust_ir_binary_container/` (provenance and
//! sha256 in its `SOURCE.txt`).

// Test fixture: the big `Err` is the compiler's own public error type, not this file's to shrink.
#![allow(clippy::result_large_err)]

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use trust_cg_codegen::pipeline::{
    FormatMode, InputFormat, NOT_A_BINARY_MODULE, PipelineError, TEMPLATE_IS_NOT_A_MODULE,
    TMBC_MAGIC, TMBC_VERSION, TRUST_IR_BINARY_MAGIC, TRUST_IS_TEMPLATE_MAGIC, decode_binary,
    decode_tmbc, detect_input_format, encode_tmbc, load_module_as, load_module_from_bytes,
};
use trust_ir::codec::{self, SniffedFormat};
use trust_ir::{
    BUILD_IDENTITY, CertificateBinding, CleanCicKernelRecheck, Module, ProofCertificate,
    ProofDigest, ProofEvidence, ProofId, Ty,
};
use trust_ir_build::ModuleBuilder;

/// The number of top-level conformance `.tmbc` fixtures vendored from the
/// trust-ir pin. Pinned so a lost or added fixture is a visible change; it
/// equals the pinned corpus's top-level golden count
/// (`the_vendored_conformance_fixtures_are_the_pinned_corpus_bytes`).
const CONFORMANCE_FIXTURE_COUNT: usize = 64;

/// The version-read gate of the pinned trust-ir reader, as its error prints.
const TRUST_IR_VERSION_REFUSAL: &str = "failed to deserialize TRUST_IR module: unsupported version";

/// The newest version a trust-ir MODULE is written at. trust-ir v57
/// (amendment S) is a template blob's version floor, which no module writes;
/// v58 (nominal type origins and declared closure layouts), v59 (typed effect
/// summaries), v60 (typed callable ABI facts), v61 (certificate binding and
/// codegen-license evidence) and v62 (the entry-state pointee clause place,
/// `ParamPointeeEntry`) and v63 (runtime closure construction) are module
/// versions; v64 adds addressable Storage geometry, and v65 adds explicit
/// single-inhabited enum selectors, v66 adds nominal closure origins, v67
/// adds tensor types and contractions, v68 tensor maps, reductions and views,
/// v69 tensor gathers and scatters, and v70 content-addressed weight blobs.
/// V70 is the reader's `wire_version`
/// (trust-ir `binary::VERSION`). Checked against the pin by
/// `the_newest_module_version_is_the_readers_and_above_the_template_floor`,
/// so a pin that moves any of these numbers fails there first.
const NEWEST_MODULE_VERSION: u32 = trust_ir::binary::TENSOR_BLOB_FORMAT_VERSION;

#[test]
fn the_newest_module_version_is_the_readers_and_above_the_template_floor() {
    use trust_ir::binary::{
        CERTIFICATE_BINDING_FORMAT_VERSION, EFFECT_SUMMARY_FORMAT_VERSION,
        NOMINAL_IDENTITY_FORMAT_VERSION, PARAM_POINTEE_PLACE_FORMAT_VERSION,
        SIGNATURE_ABI_FORMAT_VERSION, TEMPLATE_FORMAT_VERSION,
    };
    assert_eq!(BUILD_IDENTITY.wire_version, NEWEST_MODULE_VERSION);
    // Every version above the template floor is a module version, in order.
    assert_eq!(
        [
            TEMPLATE_FORMAT_VERSION + 1,
            TEMPLATE_FORMAT_VERSION + 2,
            TEMPLATE_FORMAT_VERSION + 3,
            TEMPLATE_FORMAT_VERSION + 4,
            TEMPLATE_FORMAT_VERSION + 5,
            TEMPLATE_FORMAT_VERSION + 6,
            TEMPLATE_FORMAT_VERSION + 7,
            TEMPLATE_FORMAT_VERSION + 8,
            TEMPLATE_FORMAT_VERSION + 9,
            TEMPLATE_FORMAT_VERSION + 10,
            TEMPLATE_FORMAT_VERSION + 11,
            TEMPLATE_FORMAT_VERSION + 12,
            TEMPLATE_FORMAT_VERSION + 13,
        ],
        [
            NOMINAL_IDENTITY_FORMAT_VERSION,
            EFFECT_SUMMARY_FORMAT_VERSION,
            SIGNATURE_ABI_FORMAT_VERSION,
            CERTIFICATE_BINDING_FORMAT_VERSION,
            PARAM_POINTEE_PLACE_FORMAT_VERSION,
            trust_ir::binary::MAKE_CLOSURE_FORMAT_VERSION,
            trust_ir::binary::STORAGE_LAYOUT_FORMAT_VERSION,
            trust_ir::binary::SINGLE_INHABITED_ENUM_FORMAT_VERSION,
            trust_ir::binary::CLOSURE_ORIGIN_FORMAT_VERSION,
            trust_ir::binary::TENSOR_FORMAT_VERSION,
            trust_ir::binary::TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION,
            trust_ir::binary::TENSOR_GATHER_SCATTER_FORMAT_VERSION,
            NEWEST_MODULE_VERSION,
        ]
    );
}

/// Vendored goldens whose header declares the contract surface (v41+) while a
/// bodied function carries no codegen license. Since KIND 4 (2026-09-24) the
/// reader holds a producer to the version it declared
/// (`PipelineError::ProducerOmittedBodyGate`, trust-ir's
/// `decoded_provenance_errors`), so every binary entry refuses these eight —
/// exactly what trust-ir's own `trust-ir validate` reports for each of them
/// (`ProducerOmittedBodyGate`, measured 2026-09-25) — while the header-less
/// JSON twin still decodes. The same list is pinned by trust-cg-cli
/// `tests/trust_ir_binary_container.rs`. Exact in both directions.
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

fn producer_omitted_gate(name: &str) -> bool {
    PRODUCER_OMITTED_GATE_FIXTURES.contains(&name)
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/trust_ir_binary_container")
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
            let json = path.with_extension("json");
            assert!(json.is_file(), "{} has no JSON twin", path.display());
            fixtures.push((format!("{directory}/{stem}"), path, json));
        }
    }
    fixtures.sort();
    fixtures
}

fn read(path: &Path) -> Vec<u8> {
    std::fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}

fn json_module(path: &Path) -> Module {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    serde_json::from_str(&text)
        .unwrap_or_else(|error| panic!("parse JSON twin {}: {error}", path.display()))
}

fn b1_scalars_bytes() -> Vec<u8> {
    read(&fixture_root().join("conformance/b1_scalars.tmbc"))
}

fn header_version(bytes: &[u8]) -> u32 {
    u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]])
}

fn with_header_version(bytes: &[u8], version: u32) -> Vec<u8> {
    let mut out = bytes.to_vec();
    out[8..12].copy_from_slice(&version.to_le_bytes());
    out
}

fn tmbc_envelope(payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + payload.len());
    out.extend_from_slice(TMBC_MAGIC);
    out.extend_from_slice(&TMBC_VERSION.to_le_bytes());
    out.extend_from_slice(payload);
    out
}

fn scratch_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_binary_container_{name}_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn err_text(result: Result<Module, PipelineError>) -> String {
    match result {
        Ok(module) => panic!("expected a refusal, decoded module `{}`", module.name),
        Err(error) => error.to_string(),
    }
}

fn magic_probe_module() -> Module {
    let mut builder = ModuleBuilder::new("magic_probe");
    let signature = builder.add_func_type(vec![], vec![Ty::I64]);
    let mut function = builder.function("magic_probe_fn", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let value = function.iconst(Ty::I64, 7);
    function.ret(vec![value]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn trust_ir_binary_magic_matches_serializer() {
    let bytes = trust_ir::binary::serialize_module(&magic_probe_module())
        .expect("serialize_module: test fixture");
    assert_eq!(&bytes[..TRUST_IR_BINARY_MAGIC.len()], TRUST_IR_BINARY_MAGIC);
    assert_ne!(&bytes[..TMBC_MAGIC.len()], TMBC_MAGIC);
    // Spelled once (WS4.9 companion): trust-cg's constant IS trust-ir's.
    assert_eq!(TRUST_IR_BINARY_MAGIC, &codec::TRUST_IR_BINARY_MAGIC);
    assert_eq!(TMBC_MAGIC, &codec::TRUST_CG_CONTAINER_MAGIC);
}

// ---------------------------------------------------------------------------
// WS4.9 companion (F-115): the container is chosen by trust-ir's shared
// `codec::sniff_format`, not by a local spelling of either magic.
// ---------------------------------------------------------------------------

/// A labelled input for the sniff-agreement table.
struct SniffCase {
    label: String,
    bytes: Vec<u8>,
}

/// Every class `sniff_format` distinguishes, plus the near misses around the
/// two magics: each vendored fixture bare and enveloped, what trust-cg's own
/// writer and trust-ir's own serializer emit, the JSON twin, text, and bytes
/// no rule claims.
fn sniff_corpus() -> Vec<SniffCase> {
    let mut cases = Vec::new();
    let mut push = |label: &str, bytes: Vec<u8>| {
        cases.push(SniffCase {
            label: label.to_string(),
            bytes,
        })
    };
    for (name, binary, json) in binary_fixtures() {
        let bytes = read(&binary);
        push(&format!("{name} (json twin)"), read(&json));
        push(&format!("{name} (tMBC envelope)"), tmbc_envelope(&bytes));
        push(&format!("{name} (bare)"), bytes);
    }
    let probe = magic_probe_module();
    push(
        "encode_tmbc output",
        encode_tmbc(&probe).expect("the probe has a wire image"),
    );
    push(
        "serialize_module output",
        trust_ir::binary::serialize_module(&probe).expect("serialize_module: test fixture"),
    );
    let good = b1_scalars_bytes();
    let mut near_miss = good.clone();
    near_miss[7] = b'S';
    push("TRUST_IS near miss", near_miss);
    for (label, lead) in [
        ("space before TRUST_IR", &b" "[..]),
        ("newline before TRUST_IR", b"\n"),
        ("tab before TRUST_IR", b"\t"),
    ] {
        let mut led = lead.to_vec();
        led.extend_from_slice(&good);
        push(label, led);
    }
    let mut lower = good.clone();
    lower[..8].copy_from_slice(b"trust_ir");
    push("lower-case trust_ir magic", lower);
    let envelope = tmbc_envelope(&good);
    for (label, magic) in [
        ("TMBC upper-case envelope", b"TMBC"),
        ("tmbc lower-case envelope", b"tmbc"),
        ("tMBc near-miss envelope", b"tMBc"),
    ] {
        let mut bad = envelope.clone();
        bad[..4].copy_from_slice(magic);
        push(label, bad);
    }
    push(
        "text banner",
        b"; TrustIr text format v1\nmodule \"m\"\n".to_vec(),
    );
    push("text module line", b"module \"m\"\n".to_vec());
    push("whitespace-led JSON", b"  \n{\"name\":\"m\"}".to_vec());
    push("messagepack array marker", vec![0xdc, 0x00, 0x13]);
    push("empty", Vec::new());
    push("whitespace only", b" \n\t".to_vec());
    for short in [&b"T"[..], b"TRUST_I", b"tMB", b"tM"] {
        push(
            &format!("short prefix {:?}", String::from_utf8_lossy(short)),
            short.to_vec(),
        );
    }
    // Review adversaries (WS4.9): a magic and nothing a decoder can use after
    // it is still CLAIMED binary, so it must reach that container's decoder
    // and be refused by the decoder's own reason, never re-routed or guessed.
    push("TRUST_IR magic only", TRUST_IR_BINARY_MAGIC.to_vec());
    push("TRUST_IR magic and version only", good[..12].to_vec());
    push(
        "TRUST_IR magic then JSON",
        [&TRUST_IR_BINARY_MAGIC[..], b"{\"name\":\"m\"}"].concat(),
    );
    push("tMBC magic only", TMBC_MAGIC.to_vec());
    push("tMBC header, empty payload", tmbc_envelope(&[]));
    let mut wrong_version = envelope.clone();
    wrong_version[4..8].copy_from_slice(&(TMBC_VERSION + 1).to_le_bytes());
    push("tMBC envelope, unsupported version", wrong_version);
    // ...and bytes a lenient sniff might skip to reach a magic or a brace
    // (a UTF-8 byte-order mark, NUL, CR, form feed) claim nothing binary.
    for (label, lead) in [
        ("BOM before TRUST_IR", &b"\xef\xbb\xbf"[..]),
        ("NUL before TRUST_IR", b"\0"),
        ("CR before TRUST_IR", b"\r"),
        ("form feed before TRUST_IR", b"\x0c"),
        ("BOM before tMBC", b"\xef\xbb\xbf"),
    ] {
        let body = if label.ends_with("tMBC") {
            &envelope
        } else {
            &good
        };
        push(label, [lead, &body[..]].concat());
    }
    push("BOM-led JSON", b"\xef\xbb\xbf{\"name\":\"m\"}".to_vec());
    // trust-cg's text rule still takes an unquoted `module ` prefix, which the
    // sniff does not claim: a text-side divergence only, never a binary one.
    push("unquoted module line", b"module m\n".to_vec());
    // The sniff's `TemplateBinary` answer (trust-ir amendment S): the pinned
    // corpus's real level-S template blob, the bare magic, and the magic in
    // front of a module payload. None is a module, so every entry routes it to
    // the binary reader, which refuses it by name and decodes nothing.
    push(
        "pinned template blob (compat/template_ident_param.tmbs)",
        read(&template_blob_path()),
    );
    push("TRUST_IS magic only", TRUST_IS_TEMPLATE_MAGIC.to_vec());
    push(
        "TRUST_IS magic then a module payload",
        [&TRUST_IS_TEMPLATE_MAGIC[..], &good[8..]].concat(),
    );
    // ...and the template magic after a byte a lenient sniff might skip is no
    // claim at all, so it never reaches the template refusal either.
    push(
        "space before TRUST_IS",
        [&b" "[..], &TRUST_IS_TEMPLATE_MAGIC[..]].concat(),
    );
    cases
}

/// The pinned trust-ir corpus's level-S template blob (amendment S): a real
/// `TRUST_IS` artifact, not a mutation of a module.
fn template_blob_path() -> PathBuf {
    trust_ir_conformance::refuse::fixtures_dir()
        .parent()
        .expect("refuse/ sits inside the corpus fixtures directory")
        .join("compat/template_ident_param.tmbs")
}

fn is_binary_claim(claim: Option<SniffedFormat>) -> bool {
    matches!(
        claim,
        Some(SniffedFormat::Binary | SniffedFormat::TrustCgContainer)
    )
}

/// The claims the auto-detecting entries hand to `decode_binary`: both binary
/// containers, and a template blob, which `decode_binary` refuses by name.
fn routes_to_binary_reader(claim: Option<SniffedFormat>) -> bool {
    is_binary_claim(claim) || claim == Some(SniffedFormat::TemplateBinary)
}

/// `PipelineError::ModuleIo`'s display prefix, which the auto-detecting file
/// loader replaces with the path.
const MODULE_IO_PREFIX: &str = "trust-ir module I/O failed: ";

/// Phrases only a binary decoder (the dispatch, trust-ir's reader, the tMBC
/// envelope decoder, the reader's producer rule) puts in a refusal.
const BINARY_DECODER_REASONS: [&str; 5] = [
    NOT_A_BINARY_MODULE,
    "failed to deserialize TRUST_IR module",
    "tMBC",
    PRODUCER_OMITTED_GATE_TEXT,
    "decoded-provenance refusal",
];

/// What the JSON reader, else the text reader, makes of `bytes`.
fn text_or_json(bytes: &[u8]) -> Option<Module> {
    let text = std::str::from_utf8(bytes).ok()?;
    serde_json::from_str(text)
        .ok()
        .or_else(|| trust_ir::parser::parse_module(text).ok())
}

/// Positive: trust-cg's binary decision IS `sniff_format`'s, on every entry
/// point (`detect_input_format`, `decode_binary`, `load_module_as` forced and
/// auto, `load_module_from_bytes`), over a corpus that reaches every answer
/// the sniff can give. A buffer the sniff calls binary is never refused as
/// "not a binary module" (it decodes, or trust-ir's reader / the tMBC decoder
/// refuses it by its own reason), and the auto-detecting entries take exactly
/// `decode_binary`'s path for it; a buffer it does not call binary is refused
/// by name by the binary entries and never reaches a binary decoder through
/// the auto-detecting ones.
#[test]
fn container_dispatch_is_trust_ir_sniff_format() {
    let corpus = sniff_corpus();
    let mut seen = std::collections::BTreeSet::new();
    let dir = scratch_dir("sniff_agreement");
    for (index, case) in corpus.iter().enumerate() {
        let label = &case.label;
        let claim = codec::sniff_format(&case.bytes);
        seen.insert(format!("{claim:?}"));
        let routed = routes_to_binary_reader(claim);

        let file = dir.join(format!("case{index}"));
        std::fs::write(&file, &case.bytes).expect("write extensionless case");
        assert_eq!(
            detect_input_format(&file) == InputFormat::Tmbc,
            routed,
            "{label}: detect_input_format disagrees with sniff_format ({claim:?})"
        );

        let decoded = decode_binary(&case.bytes).map_err(|error| error.to_string());
        let forced = load_module_as(&file, FormatMode::Tmbc).map_err(|error| error.to_string());
        for (entry, outcome) in [
            ("decode_binary", &decoded),
            ("load_module_as(Tmbc)", &forced),
        ] {
            match claim {
                // A `TRUST_IR` claim goes whole to trust-ir's reader: its
                // result, or the reader's producer rule on what it decoded.
                Some(SniffedFormat::Binary) => {
                    match (trust_ir::binary::deserialize_module(&case.bytes), outcome) {
                        (Ok(expected), Ok(module)) => {
                            assert_eq!(module, &expected, "{label}: {entry}")
                        }
                        (Ok(_), Err(error)) => assert!(
                            error.contains(PRODUCER_OMITTED_GATE_TEXT),
                            "{label}: {entry}: trust-ir reads it, so only the producer rule \
                             may refuse it: {error}"
                        ),
                        (Err(reader), Err(error)) => assert!(
                            error.contains(&format!(
                                "failed to deserialize TRUST_IR module: {reader}"
                            )) && !error.contains(NOT_A_BINARY_MODULE),
                            "{label}: {entry}: expected trust-ir's own refusal `{reader}`: {error}"
                        ),
                        (Err(reader), Ok(module)) => panic!(
                            "{label}: {entry}: decoded `{}` although trust-ir refuses it: {reader}",
                            module.name
                        ),
                    }
                }
                // A `tMBC` claim goes to the envelope decoder, unchanged.
                Some(SniffedFormat::TrustCgContainer) => {
                    match (decode_tmbc(&case.bytes), outcome) {
                        (Ok(expected), Ok(module)) => {
                            assert_eq!(module, &expected, "{label}: {entry}")
                        }
                        (Err(envelope), Err(error)) => {
                            let envelope = envelope.to_string();
                            let inner = envelope
                                .strip_prefix("trust-ir module I/O failed: ")
                                .unwrap_or(&envelope);
                            assert!(
                                error.contains(inner) && !error.contains(NOT_A_BINARY_MODULE),
                                "{label}: {entry}: expected decode_tmbc's `{inner}`: {error}"
                            );
                        }
                        (expected, outcome) => panic!(
                            "{label}: {entry}: decode_tmbc gives {:?}, the loader {:?}",
                            expected.map(|module| module.name),
                            outcome.as_ref().map(|module| &module.name)
                        ),
                    }
                }
                // A template claim is refused by the template's own name
                // (WS4.9 review, amendment S), never decoded.
                Some(SniffedFormat::TemplateBinary) => match outcome {
                    Ok(module) => panic!(
                        "{label}: {entry}: decoded `{}` from a template blob",
                        module.name
                    ),
                    Err(error) => assert!(
                        error.contains(NOT_A_BINARY_MODULE)
                            && error.contains(TEMPLATE_IS_NOT_A_MODULE),
                        "{label}: {entry}: a template must be refused by name: {error}"
                    ),
                },
                _ => match outcome {
                    Ok(module) => panic!(
                        "{label}: {entry}: decoded `{}` from a non-binary claim {claim:?}",
                        module.name
                    ),
                    Err(error) => assert!(
                        error.contains(NOT_A_BINARY_MODULE)
                            && !error.contains(TEMPLATE_IS_NOT_A_MODULE),
                        "{label}: {entry}: {claim:?} must be refused by name, and never \
                         named a template: {error}"
                    ),
                },
            }
        }

        // The two auto-detecting entries are entry points too (WS4.9
        // review). A binary claim takes EXACTLY `decode_binary`'s path; a
        // non-binary claim never reaches a binary decoder, and anything it
        // decodes is what the text or JSON reader makes of the same bytes.
        let from_bytes = load_module_from_bytes(&case.bytes).map_err(|error| error.to_string());
        let auto = load_module_as(&file, FormatMode::Auto).map_err(|error| error.to_string());
        if routed {
            assert_eq!(
                from_bytes, decoded,
                "{label}: load_module_from_bytes must be decode_binary on a binary claim"
            );
            match (&decoded, &auto) {
                (Ok(expected), Ok(module)) => assert_eq!(module, expected, "{label}: Auto"),
                (Err(expected), Err(error)) => {
                    let inner = expected.strip_prefix(MODULE_IO_PREFIX).unwrap_or(expected);
                    assert!(
                        error.contains(inner),
                        "{label}: Auto: expected decode_binary's `{inner}`: {error}"
                    );
                }
                (expected, outcome) => panic!(
                    "{label}: decode_binary gives {:?}, Auto {:?}",
                    expected.as_ref().map(|module| &module.name),
                    outcome.as_ref().map(|module| &module.name)
                ),
            }
        } else {
            for (entry, outcome) in [
                ("load_module_from_bytes", &from_bytes),
                ("load_module_as(Auto)", &auto),
            ] {
                match outcome {
                    Ok(module) => assert_eq!(
                        Some(module),
                        text_or_json(&case.bytes).as_ref(),
                        "{label}: {entry}: decoded what neither the text nor the JSON reader \
                         makes of these bytes ({claim:?})"
                    ),
                    Err(error) => {
                        for binary_reason in BINARY_DECODER_REASONS {
                            assert!(
                                !error.contains(binary_reason),
                                "{label}: {entry}: {claim:?} reached a binary decoder: {error}"
                            );
                        }
                    }
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    let expected: std::collections::BTreeSet<String> = [
        Some(SniffedFormat::Binary),
        Some(SniffedFormat::TrustCgContainer),
        Some(SniffedFormat::Json),
        Some(SniffedFormat::Text),
        Some(SniffedFormat::TemplateBinary),
        None,
    ]
    .iter()
    .map(|claim| format!("{claim:?}"))
    .collect();
    assert_eq!(
        seen, expected,
        "the corpus must reach every sniff answer, so no class is tested vacuously"
    );
}

/// Negative twin: the canonical magic after one leading whitespace byte is
/// not a binary container. `sniff_format` matches magics as exact prefixes, so
/// every binary entry (`decode_binary`, the forced format, a `.tmbc` file
/// under auto) refuses it by name, and the auto-detecting entries (the byte
/// loader, an extensionless file under auto) never hand it to a binary decoder
/// and fail in the JSON reader instead. The unprefixed bytes decoding on every
/// one of those entries is the mutation control that makes the one byte the
/// only cause.
#[test]
fn whitespace_before_the_trust_ir_magic_is_refused_by_name() {
    let good = b1_scalars_bytes();
    let dir = scratch_dir("whitespace_led_magic");
    let expected = decode_binary(&good).expect("positive control: the unprefixed blob decodes");
    assert_eq!(
        load_module_from_bytes(&good).expect("positive control: byte loader"),
        expected
    );
    let unled = dir.join("unled");
    std::fs::write(&unled, &good).expect("write");
    assert_eq!(
        load_module_as(&unled, FormatMode::Auto).expect("positive control: extensionless auto"),
        expected
    );
    for lead in *b" \n\t\r\x0c" {
        let mut led = vec![lead];
        led.extend_from_slice(&good);
        assert_eq!(codec::sniff_format(&led), None, "lead {lead:#04x}");
        let error = err_text(decode_binary(&led));
        assert!(
            error.contains(NOT_A_BINARY_MODULE),
            "lead {lead:#04x}: {error}"
        );
        let path = dir.join(format!("led_{lead}.tmbc"));
        std::fs::write(&path, &led).expect("write");
        for mode in [FormatMode::Tmbc, FormatMode::Auto] {
            let error = err_text(load_module_as(&path, mode));
            assert!(
                error.contains(NOT_A_BINARY_MODULE),
                "lead {lead:#04x} {mode:?}: {error}"
            );
        }
        let bare_path = dir.join(format!("led_{lead}"));
        std::fs::write(&bare_path, &led).expect("write");
        assert_eq!(
            detect_input_format(&bare_path),
            InputFormat::Json,
            "lead {lead:#04x}"
        );
        for (entry, error) in [
            (
                "load_module_from_bytes",
                err_text(load_module_from_bytes(&led)),
            ),
            (
                "extensionless load_module_as(Auto)",
                err_text(load_module_as(&bare_path, FormatMode::Auto)),
            ),
        ] {
            for binary_reason in BINARY_DECODER_REASONS {
                assert!(
                    !error.contains(binary_reason),
                    "lead {lead:#04x} {entry}: reached a binary decoder: {error}"
                );
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Named reason: under the forced binary format (the CLI default), a JSON or
/// text module is refused as "not a binary module" AND the refusal says what
/// trust-ir's sniff read it as, in trust-ir's own words
/// (`SniffedFormat::describe`). Bytes the sniff does not recognise carry no
/// claim, so the message never invents one, and it never names either binary
/// container, which the bytes are not. Under auto a `.tmbc` extension takes
/// the same refusal.
#[test]
fn binary_refusal_names_what_trust_ir_sniffs() {
    let dir = scratch_dir("refusal_claim");
    let json = read(&fixture_root().join("conformance/b1_scalars.json"));
    let mut led_magic = b" ".to_vec();
    led_magic.extend_from_slice(&b1_scalars_bytes());
    let cases: [(&str, Vec<u8>, Option<SniffedFormat>); 11] = [
        ("json", json, Some(SniffedFormat::Json)),
        (
            "template_blob",
            read(&template_blob_path()),
            Some(SniffedFormat::TemplateBinary),
        ),
        (
            "template_magic_only",
            TRUST_IS_TEMPLATE_MAGIC.to_vec(),
            Some(SniffedFormat::TemplateBinary),
        ),
        (
            "whitespace_led_json",
            b"\n\t {\"name\":\"m\"}".to_vec(),
            Some(SniffedFormat::Json),
        ),
        (
            "text",
            b"; TrustIr text format v1\nmodule \"m\"\n".to_vec(),
            Some(SniffedFormat::Text),
        ),
        (
            "text_module_line",
            b"module \"m\"\n".to_vec(),
            Some(SniffedFormat::Text),
        ),
        (
            "bom_led_json",
            b"\xef\xbb\xbf{\"name\":\"m\"}".to_vec(),
            None,
        ),
        ("unquoted_module", b"module m\n".to_vec(), None),
        ("whitespace_led_magic", led_magic, None),
        ("messagepack", vec![0xdc, 0x00, 0x13], None),
        ("empty", Vec::new(), None),
    ];
    let claims = [
        SniffedFormat::Json,
        SniffedFormat::Text,
        SniffedFormat::Binary,
        SniffedFormat::TrustCgContainer,
    ];
    for (name, bytes, expected) in cases {
        assert_eq!(codec::sniff_format(&bytes), expected, "{name}");
        let path = dir.join(format!("{name}.tmbc"));
        std::fs::write(&path, &bytes).expect("write");
        for (entry, error) in [
            ("decode_binary", err_text(decode_binary(&bytes))),
            (
                "load_module_as(Tmbc)",
                err_text(load_module_as(&path, FormatMode::Tmbc)),
            ),
            (
                "load_module_as(Auto) on .tmbc",
                err_text(load_module_as(&path, FormatMode::Auto)),
            ),
        ] {
            assert!(
                error.contains(NOT_A_BINARY_MODULE),
                "{name} {entry}: {error}"
            );
            for claim in claims {
                assert_eq!(
                    error.contains(claim.describe()),
                    expected == Some(claim),
                    "{name} {entry}: claim {claim:?}: {error}"
                );
            }
            // A template claim is named as a template, and nothing else is.
            assert_eq!(
                error.contains(TEMPLATE_IS_NOT_A_MODULE),
                expected == Some(SniffedFormat::TemplateBinary),
                "{name} {entry}: template naming: {error}"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Mutation control: trust-cg's own writer and trust-ir's sniff agree on the
/// envelope, and the dispatch is exactly as strict as the sniff. One flipped
/// case bit in the tMBC magic turns a decodable envelope into a refusal by
/// name, so no looser local check sits beside `sniff_format`.
#[test]
fn tmbc_writer_and_trust_ir_sniff_agree() {
    let probe = magic_probe_module();
    let written = encode_tmbc(&probe).expect("the probe has a wire image");
    assert_eq!(
        codec::sniff_format(&written),
        Some(SniffedFormat::TrustCgContainer)
    );
    assert_eq!(decode_binary(&written).expect("positive control"), probe);
    for index in 0..TMBC_MAGIC.len() {
        let mut mutant = written.clone();
        mutant[index] ^= 0x20;
        assert_eq!(codec::sniff_format(&mutant), None, "byte {index}");
        let error = err_text(decode_binary(&mutant));
        assert!(error.contains(NOT_A_BINARY_MODULE), "byte {index}: {error}");
    }

    let bare = trust_ir::binary::serialize_module(&probe).expect("serialize_module: test fixture");
    assert_eq!(codec::sniff_format(&bare), Some(SniffedFormat::Binary));
    assert_eq!(decode_binary(&bare).expect("positive control"), probe);
    for index in 0..TRUST_IR_BINARY_MAGIC.len() {
        let mut mutant = bare.clone();
        mutant[index] ^= 0x20;
        assert_eq!(codec::sniff_format(&mutant), None, "byte {index}");
        let error = err_text(decode_binary(&mutant));
        assert!(error.contains(NOT_A_BINARY_MODULE), "byte {index}: {error}");
    }
}

/// Synthetic transport data only: neither this certificate nor its optional
/// binding was produced by a proof checker. These tests grant no authority.
fn synthetic_recheck_module(binding: Option<Box<CertificateBinding>>) -> Module {
    let mut builder = ModuleBuilder::new("synthetic_recheck_transport");
    let signature = builder.add_func_type(vec![], vec![Ty::I64]);
    let mut function = builder.function("return_seven", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let value = function.iconst(Ty::I64, 7);
    function.ret(vec![value]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(73),
        prover: "synthetic transport fixture; not certified".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![1, 2],
            context: vec![3],
            lineage: ProofDigest::trust_ir_stable("synthetic.transport", b"lineage"),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "TransportFixture".into(),
                theorems: vec![],
                anchor: "transport-fixture".into(),
                allowed_axioms: vec![],
                binding,
            }),
        },
        assurance: None,
    });
    module
}

#[test]
fn unbound_synthetic_kernel_recheck_roundtrips_through_tmbc() {
    let module = synthetic_recheck_module(None);
    let before = module.clone();
    let bytes = encode_tmbc(&module).expect("an unbound directive has a wire carrier");
    assert_eq!(
        decode_tmbc(&bytes).expect("decode unbound transport fixture"),
        before,
        "the complete certificate, including its unbound directive, is retained"
    );
    assert_eq!(module, before, "encoding does not alter the source module");
}

/// Since trust-ir binary v61 (`certificate-binding`) a bound directive has a
/// wire carrier, so the envelope carries it whole: the binding is neither
/// refused nor narrowed to `None`, and the payload is written at v61 (an
/// all-unbound module keeps its older bytes; see the unbound twin above).
/// A v61 payload declares the contract surface (v41+), so the reader holds
/// its bodied function to the producer rule: claim-less, it is refused as a
/// producer omission; licensed (here the honest `Ungated`: nothing gated
/// this synthetic body), it round-trips.
#[test]
fn bound_synthetic_kernel_recheck_roundtrips_through_tmbc_at_v61() {
    let mut module = synthetic_recheck_module(Some(Box::new(CertificateBinding::new(
        ProofDigest::trust_ir_stable("synthetic.transport", b"environment"),
        ProofDigest::trust_ir_stable("synthetic.transport", b"statement"),
    ))));
    let claim_less = encode_tmbc(&module).expect("a certificate binding has a binary carrier");
    assert!(
        matches!(
            decode_tmbc(&claim_less),
            Err(PipelineError::ProducerOmittedBodyGate { wire_version, .. })
                if wire_version == trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION
        ),
        "a claim-less body in a v61 payload is a producer omission"
    );
    module.functions[0].body_gate = Some(trust_ir::BodyGate::Ungated);
    let before = module.clone();
    let bytes = std::panic::catch_unwind(|| encode_tmbc(&module))
        .expect("encode_tmbc never panics on a bound directive")
        .expect("a certificate binding has a binary carrier since v61");
    let decoded = decode_tmbc(&bytes).expect("decode bound transport fixture");
    assert_eq!(
        decoded, before,
        "the complete certificate, including its binding, is retained"
    );
    let payload = trust_ir::binary::serialize_module(&module).expect("the bound module encodes");
    assert_eq!(
        header_version(&payload),
        trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION,
        "a bound module is written at the binding's version"
    );
    assert_eq!(module, before, "encoding does not alter the source module");
}

/// The v49 blob the then-pinned writer produced (`pinned_writer/`, see
/// `SOURCE.txt`): trust-ir's reader and validator accept its drop, weak
/// compare-exchange and unwritten lane (since v55 its validator names the
/// `drop i64` non-canonical: a trivially droppable type's drop is spelled by
/// absence), so the decoded module reaches this backend whole — bare and
/// inside the tMBC envelope — where trust-ir's own codegen verdict refuses the
/// drop first, and the adapter's shared floor refuses it by the construct's
/// own name, the first it meets.
/// The blob keeps its own v49 header. Geometry-only `conformance/storage_only`
/// retains v64; `conformance/single_inhabited_enums` carries the newest module
/// version v65 (v57 is the template floor, see [`NEWEST_MODULE_VERSION`]).
/// The generated `pinned_writer/runtime_closure_v63` retains its v63 header. Previously v62 was carried by
/// `conformance/param_pointee_place` (trust-ir 8d304e36, the
/// `ParamPointeeEntry` clause place; v61 is `certificate_binding`'s, from the
/// WS6.7 wire line, trust-ir 7c4cab5d..827056dd; v60 is `typed_signature_abi`'s, from 1ede2d9e; v59 is
/// `effect_summaries`'s, from 1d31d4c0; v58 `closure_layout`'s and
/// `nominal_type_origin`'s, from 695fcf51; v56 was `unwind_twins`'s, v55 `drop_glue`'s and v54
/// `assert_panic_site`'s, from 0be81d5c and 6f2dfce6; v53
/// `call_unwind_boundary`'s, from 8a0d54c0; v52 `assert_kind`'s, from 8cf20223; v51
/// `inst_wire_batch`'s, from 9674bea5; v50 `array_splat`'s,
/// from 066e1765). The v49 fixture stays frozen (`SOURCE.txt`), and this
/// test pins that some vendored fixture is at the writer's version.
#[test]
fn v49_crystal_lane_blob_decodes_and_the_adapter_floor_refuses_it_by_name() {
    let bytes = read(&fixture_root().join("pinned_writer/crystal_lane_v49.tmbc"));
    assert_eq!(header_version(&bytes), 49);
    assert_eq!(
        header_version(&read(
            &fixture_root().join("pinned_writer/runtime_closure_v63.tmbc")
        )),
        trust_ir::binary::MAKE_CLOSURE_FORMAT_VERSION,
        "the existing runtime-closure fixture retains its original v63 header"
    );
    assert_eq!(
        header_version(&read(&fixture_root().join("conformance/storage_only.tmbc"))),
        trust_ir::binary::STORAGE_LAYOUT_FORMAT_VERSION,
        "the geometry-only Storage fixture retains its normative v64 header"
    );
    assert_eq!(
        header_version(&read(
            &fixture_root().join("conformance/single_inhabited_enums.tmbc")
        )),
        trust_ir::binary::SINGLE_INHABITED_ENUM_FORMAT_VERSION,
        "the explicit single-inhabited fixture carries its normative v65 header"
    );
    let expected = json_module(&fixture_root().join("pinned_writer/crystal_lane_v49.json"));
    for (entry, decoded) in [
        ("decode_binary", decode_binary(&bytes)),
        ("decode_tmbc envelope", decode_tmbc(&tmbc_envelope(&bytes))),
    ] {
        let module = decoded.unwrap_or_else(|error| panic!("{entry}: {error}"));
        assert_eq!(module, expected, "{entry}");
        // Since trust-ir v55 (amendment D, §20 rule 5a) the validator's ONE
        // finding is the blob's `drop i64`: a drop of a trivially droppable
        // type is not the one spelling of a drop (it is spelled by absence).
        // The reader still decodes the blob whole, and the weak
        // compare-exchange and the unwritten lane stay structurally valid.
        let findings = trust_ir_build::validate_module(&module);
        assert!(
            matches!(
                findings.as_slice(),
                [trust_ir_build::ValidationError::NonCanonicalDrop { function, .. }]
                    if function == "crystal_lane"
            ),
            "{entry}: trust-ir's only finding is the non-canonical drop, got {findings:?}"
        );
        // Every entry now meets trust-ir's own codegen verdict on that drop
        // first (`validate_codegen_prerequisites`)...
        match trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::default(),
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        ) {
            Err(trust_cg_lower::adapter::AdapterError::TrustIrAdmissionRefused { error }) => {
                assert!(
                    error.contains("crystal_lane")
                        && error.contains("not the one spelling of a drop"),
                    "{entry}: {error}"
                );
            }
            other => panic!("{entry}: expected trust-ir's drop verdict, got {other:?}"),
        }
        // ...and the adapter's shared floor still refuses the blob by the
        // first construct it meets, by name.
        match trust_cg_lower::adapter::reject_unconsumed_v41_target_neutral_surface(&module) {
            Err(trust_cg_lower::adapter::AdapterError::UnmodeledTrustIrConstruct {
                location,
                construct,
                ..
            }) => {
                assert_eq!(construct, "Constant::Uninit", "{entry}");
                assert_eq!(location, "function `crystal_lane` bb0", "{entry}");
            }
            other => panic!("{entry}: expected the floor's by-name refusal, got {other:?}"),
        }
    }
}

/// Positive: every conformance fixture and the Clean artifact decode through
/// every loader entry point, and equal the module their JSON twin spells.
#[test]
fn every_bare_trust_ir_fixture_decodes_and_equals_its_json_twin() {
    let fixtures = binary_fixtures();
    let conformance = fixtures
        .iter()
        .filter(|(name, _, _)| name.starts_with("conformance/"))
        .count();
    assert_eq!(conformance, CONFORMANCE_FIXTURE_COUNT);
    assert!(
        fixtures
            .iter()
            .any(|(name, _, _)| name == "clean/lean_library"),
        "the Clean-produced artifact is part of the positive set"
    );

    let dir = scratch_dir("every_fixture");
    for (name, binary, json) in &fixtures {
        let bytes = read(binary);
        assert!(
            bytes.starts_with(TRUST_IR_BINARY_MAGIC),
            "{name}: fixture must be the bare container"
        );
        let expected = json_module(json);

        if producer_omitted_gate(name) {
            // The reader's producer rule, on every binary entry, bare or
            // enveloped, by path or by bytes; the JSON twin decodes.
            for (entry, error) in [
                ("decode_binary", err_text(decode_binary(&bytes))),
                (
                    "load_module_from_bytes",
                    err_text(load_module_from_bytes(&bytes)),
                ),
                (
                    "load_module_as(Tmbc)",
                    err_text(load_module_as(binary, FormatMode::Tmbc)),
                ),
                (
                    "load_module_as(Auto)",
                    err_text(load_module_as(binary, FormatMode::Auto)),
                ),
                (
                    "tMBC envelope",
                    err_text(decode_binary(&tmbc_envelope(&bytes))),
                ),
            ] {
                assert!(
                    error.contains(PRODUCER_OMITTED_GATE_TEXT),
                    "{name}: {entry}: expected the producer-omitted-gate refusal, got {error}"
                );
            }
            continue;
        }
        let decoded = decode_binary(&bytes).unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(decoded, expected, "{name}: decode_binary vs JSON twin");
        assert_eq!(
            load_module_from_bytes(&bytes).unwrap_or_else(|error| panic!("{name}: {error}")),
            expected,
            "{name}: load_module_from_bytes"
        );
        for mode in [FormatMode::Tmbc, FormatMode::Auto] {
            let loaded =
                load_module_as(binary, mode).unwrap_or_else(|error| panic!("{name}: {error}"));
            assert_eq!(loaded, expected, "{name}: load_module_as({mode:?})");
        }

        // Auto with no telling extension: the sniff alone must pick binary.
        let bare = dir.join(name.replace('/', "__"));
        std::fs::write(&bare, &bytes).expect("write extensionless copy");
        assert_eq!(detect_input_format(&bare), InputFormat::Tmbc, "{name}");
        assert_eq!(
            load_module_as(&bare, FormatMode::Auto)
                .unwrap_or_else(|error| panic!("{name}: {error}")),
            expected,
            "{name}: extensionless auto"
        );

        // The tMBC envelope around the same payload stays readable.
        assert_eq!(
            decode_binary(&tmbc_envelope(&bytes)).unwrap_or_else(|error| panic!("{name}: {error}")),
            expected,
            "{name}: tMBC envelope"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// TrustCG's own v22 refusal control in `conformance/`, outside the
/// pinned-corpus comparison (`SOURCE.txt`).
const OWN_REFUSAL_CONTROL: &str = "compat_v22_composition.tmbc";

/// The vendored `conformance/` directory is the pinned trust-ir's goldens, byte
/// for byte: every top-level `.tmbc` of the pinned corpus
/// (`crates/trust-ir-conformance/tests/fixtures/`) with its `.json` twin, and
/// nothing else but [`OWN_REFUSAL_CONTROL`]. Decoding alone cannot see a stale
/// copy: a golden the pin regenerated can still decode, equal its stale twin
/// and compile, and the serializer has re-emitted every JSON twin several times
/// with fields the reader defaults. (trust-ir `11a23715` regenerated
/// `certificate_binding` for a Clean prelude change; the stale copy was caught
/// only because its certificates no longer replayed, LD-81.) A pin move that
/// adds, removes or regenerates a golden fails here by file name until
/// `conformance/` is re-vendored from the pin and `SOURCE.txt` records it;
/// `scripts/bump_trust_ir_pin.py` runs this target as a guard of the move
/// (LD-84). Test-rung evidence about file identity only.
#[test]
fn the_vendored_conformance_fixtures_are_the_pinned_corpus_bytes() {
    let corpus = trust_ir_conformance::refuse::fixtures_dir()
        .parent()
        .expect("refuse/ sits inside the corpus fixtures directory")
        .to_path_buf();
    let vendored = fixture_root().join("conformance");
    let files = |directory: &Path| -> BTreeSet<String> {
        std::fs::read_dir(directory)
            .unwrap_or_else(|error| panic!("read {}: {error}", directory.display()))
            .map(|entry| entry.expect("fixture directory entry").path())
            .filter(|path| path.is_file())
            .map(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .expect("UTF-8 fixture file name")
                    .to_owned()
            })
            .collect()
    };
    let goldens: BTreeSet<String> = files(&corpus)
        .into_iter()
        .filter_map(|name| name.strip_suffix(".tmbc").map(str::to_owned))
        .collect();
    assert_eq!(
        goldens.len(),
        CONFORMANCE_FIXTURE_COUNT,
        "the pinned corpus's top-level golden count"
    );
    let expected: BTreeSet<String> = goldens
        .iter()
        .flat_map(|stem| [format!("{stem}.tmbc"), format!("{stem}.json")])
        .collect();
    let mut present = files(&vendored);
    assert!(
        present.remove(OWN_REFUSAL_CONTROL),
        "conformance/{OWN_REFUSAL_CONTROL} is missing"
    );
    let unvendored: Vec<&String> = expected.difference(&present).collect();
    let not_in_corpus: Vec<&String> = present.difference(&expected).collect();
    let differing: Vec<&String> = expected
        .intersection(&present)
        .filter(|name| {
            let pinned = std::fs::read(corpus.join(name.as_str())).ok();
            pinned != Some(read(&vendored.join(name.as_str())))
        })
        .collect();
    assert!(
        unvendored.is_empty() && not_in_corpus.is_empty() && differing.is_empty(),
        "tests/fixtures/trust_ir_binary_container/conformance is not the pinned corpus ({}): \
         not vendored {unvendored:?}; not a pinned golden {not_in_corpus:?}; bytes differ \
         {differing:?}. Re-vendor it from the pin's crates/trust-ir-conformance/tests/fixtures \
         and record the re-vendor in SOURCE.txt.",
        corpus.display()
    );
}

/// Negative twin: one byte turns `TRUST_IR` into `TRUST_IS`, and every entry
/// point refuses it with the named reason instead of guessing.
#[test]
fn near_miss_magic_is_refused_by_name() {
    let good = b1_scalars_bytes();
    // Mutation control: the unmutated bytes decode, so the refusal below is
    // caused by the one-byte change and nothing else.
    decode_binary(&good).expect("positive control");
    let mut bad = good.clone();
    bad[7] = b'S';
    assert_eq!(&bad[..8], b"TRUST_IS");

    let error = err_text(decode_binary(&bad));
    assert!(error.contains(NOT_A_BINARY_MODULE), "{error}");
    assert!(error.contains("54 52 55 53 54 5f 49 53"), "{error}");
    assert!(!error.contains("tMBC magic"), "{error}");

    let dir = scratch_dir("near_miss");
    let path = dir.join("near_miss.tmbc");
    std::fs::write(&path, &bad).expect("write near miss");
    for mode in [FormatMode::Tmbc, FormatMode::Auto] {
        let error = err_text(load_module_as(&path, mode));
        assert!(error.contains(NOT_A_BINARY_MODULE), "{mode:?}: {error}");
    }
    let error = err_text(load_module_as(&path, FormatMode::Tmbc));
    assert!(error.contains("--format=json"), "{error}");
    let _ = std::fs::remove_dir_all(&dir);

    for short in [&b""[..], b"TRU", b"TRUST_I", b"tMB"] {
        let error = err_text(decode_binary(short));
        assert!(error.contains(NOT_A_BINARY_MODULE), "{short:?}: {error}");
    }
}

/// Adversarial: the envelope still carries the newest payload the pin reads.
/// "Newest" is the newest version a module is written at
/// ([`NEWEST_MODULE_VERSION`], the reader's `wire_version`), and at least one
/// vendored fixture must be written at it,
/// so a pin move without a re-vendor fails here instead of silently testing an
/// older payload.
#[test]
fn tmbc_envelope_around_the_newest_payload_still_decodes() {
    let newest: Vec<_> = binary_fixtures()
        .into_iter()
        .filter(|(_, binary, _)| header_version(&read(binary)) == NEWEST_MODULE_VERSION)
        .collect();
    assert!(
        !newest.is_empty(),
        "no vendored fixture is written at the newest module version v{NEWEST_MODULE_VERSION}"
    );
    for (name, binary, json) in &newest {
        let expected = json_module(json);
        let envelope = tmbc_envelope(&read(binary));
        if producer_omitted_gate(name) {
            // The newest payload is held to the producer rule inside the
            // envelope exactly as bare; the envelope's own version gate below
            // is still exercised on it.
            for (entry, error) in [
                ("decode_tmbc", err_text(decode_tmbc(&envelope))),
                ("decode_binary", err_text(decode_binary(&envelope))),
                (
                    "load_module_from_bytes",
                    err_text(load_module_from_bytes(&envelope)),
                ),
            ] {
                assert!(
                    error.contains(PRODUCER_OMITTED_GATE_TEXT),
                    "{name}: {entry}: expected the producer-omitted-gate refusal, got {error}"
                );
            }
        } else {
            assert_eq!(
                decode_tmbc(&envelope).unwrap_or_else(|error| panic!("{name}: {error}")),
                expected,
                "{name}: decode_tmbc"
            );
            assert_eq!(
                decode_binary(&envelope).unwrap_or_else(|error| panic!("{name}: {error}")),
                expected,
                "{name}: decode_binary"
            );
            assert_eq!(
                load_module_from_bytes(&envelope).unwrap_or_else(|error| panic!("{name}: {error}")),
                expected,
                "{name}: load_module_from_bytes"
            );
        }

        // The envelope's own version gate is unchanged.
        let mut wrong = envelope.clone();
        wrong[4..8].copy_from_slice(&2u32.to_le_bytes());
        let error = err_text(decode_binary(&wrong));
        assert!(
            error.contains("unsupported tMBC version: 2"),
            "{name}: {error}"
        );
    }
}

/// Adversarial: a bare blob in the ambiguous-lineage range (v26..=v28 at the
/// pin, read from the reader's `BUILD_IDENTITY.refused_read_versions`) is
/// refused by trust-ir's own reader, not by the old "tMBC magic" check.
#[test]
fn bare_ambiguous_lineage_blob_is_refused_by_trust_ir() {
    let good = b1_scalars_bytes();
    assert_eq!(header_version(&good), 38);
    decode_binary(&good).expect("positive control: the v38 original decodes");
    let (first, last) = BUILD_IDENTITY.refused_read_versions;
    for version in first..=last {
        assert!(!BUILD_IDENTITY.reads(version), "v{version}");
        let error = err_text(decode_binary(&with_header_version(&good, version)));
        assert!(
            error.contains(TRUST_IR_VERSION_REFUSAL),
            "v{version}: {error}"
        );
        assert!(!error.contains("tMBC"), "v{version}: {error}");
        assert!(!error.contains(NOT_A_BINARY_MODULE), "v{version}: {error}");
    }
}

/// Versions outside the pinned reader's window as its `BUILD_IDENTITY`
/// reports it (above `wire_version`, below `min_read_version`), never a
/// hard-coded number: a pin move must not leave these tests probing a version
/// the new reader accepts.
fn versions_outside_the_reader_window() -> [u32; 5] {
    let newest = BUILD_IDENTITY.wire_version;
    let floor = BUILD_IDENTITY.min_read_version;
    [newest + 1, newest + 2, u32::MAX, floor - 1, 0]
}

/// Adversarial (REVIEW): a bare blob newer than the pinned reader, or older
/// than its floor, is refused whole by trust-ir's version gate.
#[test]
fn bare_blob_outside_the_pinned_version_window_is_refused() {
    let good = b1_scalars_bytes();
    for version in versions_outside_the_reader_window() {
        assert!(!BUILD_IDENTITY.reads(version), "v{version}");
        let blob = with_header_version(&good, version);
        let error = err_text(decode_binary(&blob));
        assert!(
            error.contains(TRUST_IR_VERSION_REFUSAL),
            "v{version}: {error}"
        );
        let error = err_text(load_module_from_bytes(&blob));
        assert!(
            error.contains(TRUST_IR_VERSION_REFUSAL),
            "v{version}: {error}"
        );
        let error = err_text(decode_binary(&tmbc_envelope(&blob)));
        assert!(
            error.contains("unsupported version"),
            "tMBC v{version}: {error}"
        );
    }

    // Window-edge control: the lowest and highest versions the reader accepts
    // pass its version gate, so the refusals above come from the window and
    // not from a stricter gate on trust-cg's side. A relabelled v38 body may
    // still fail later in the decoder, but never as an unsupported version.
    for version in [BUILD_IDENTITY.min_read_version, BUILD_IDENTITY.wire_version] {
        assert!(BUILD_IDENTITY.reads(version), "v{version}");
        if let Err(error) = decode_binary(&with_header_version(&good, version)) {
            let error = error.to_string();
            assert!(
                !error.contains(TRUST_IR_VERSION_REFUSAL),
                "v{version} is inside the window: {error}"
            );
        }
    }

    // A real v22 blob from trust-ir's compat corpus, below the v23 floor.
    let v22 = read(&fixture_root().join("conformance/compat_v22_composition.tmbc"));
    assert!(v22.starts_with(TRUST_IR_BINARY_MAGIC));
    assert_eq!(header_version(&v22), 22);
    assert!(
        !BUILD_IDENTITY.reads(22),
        "v22 must be below the reader floor"
    );
    let error = err_text(decode_binary(&v22));
    assert!(error.contains(TRUST_IR_VERSION_REFUSAL), "{error}");
}

/// Extension dispatch is unchanged for JSON and text: a `.json` file holding
/// binary bytes is still parsed as JSON under `Auto` and refused as such.
#[test]
fn json_extension_still_dispatches_to_json() {
    let dir = scratch_dir("json_extension");
    let path = dir.join("binary_in_disguise.json");
    std::fs::write(&path, b1_scalars_bytes()).expect("write");
    assert_eq!(detect_input_format(&path), InputFormat::Json);
    assert!(load_module_as(&path, FormatMode::Auto).is_err());
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Review adversaries (WS7.4 review)
// ---------------------------------------------------------------------------

/// Adversarial: bytes after the last section of a bare container are refused
/// by trust-ir's trailing-byte check, both bare and inside a tMBC envelope.
/// A decoder that stopped at the module end and ignored the rest would let a
/// second, unvalidated payload ride along behind a valid one.
#[test]
fn review_trailing_bytes_after_a_bare_module_are_refused() {
    for (name, binary, _) in binary_fixtures() {
        let good = read(&binary);
        // Positive control: the unmutated bytes decode, or are refused ONLY
        // by the reader's producer rule (a rule about the decoded module, so
        // the container was read whole); a trailing-byte refusal below is
        // therefore the deserializer's, not that rule's.
        match decode_binary(&good) {
            Ok(_) => assert!(
                !producer_omitted_gate(&name),
                "{name}: listed as producer-omitted"
            ),
            Err(error) => assert!(
                producer_omitted_gate(&name)
                    && error.to_string().contains(PRODUCER_OMITTED_GATE_TEXT),
                "{name}: positive control: {error}"
            ),
        }
        for tail in [&b"\0"[..], b"TRUST_IR", &good[..]] {
            let mut bad = good.clone();
            bad.extend_from_slice(tail);
            let error = err_text(decode_binary(&bad));
            assert!(
                error.contains("failed to deserialize TRUST_IR module"),
                "{name} + {} trailing bytes: {error}",
                tail.len()
            );
            let error = err_text(load_module_from_bytes(&bad));
            assert!(error.contains("TRUST_IR"), "{name}: {error}");
            assert!(
                decode_binary(&tmbc_envelope(&bad)).is_err(),
                "{name}: tMBC envelope with trailing bytes decoded"
            );
        }
    }
}

/// Adversarial: the envelope is exactly one layer. A tMBC envelope around a
/// tMBC envelope, and a `TRUST_IR` header followed by a tMBC envelope, are
/// both refused; nothing peels containers recursively.
#[test]
fn review_nested_containers_are_refused() {
    let good = b1_scalars_bytes();
    let once = tmbc_envelope(&good);
    decode_binary(&once).expect("positive control: one envelope decodes");
    let twice = tmbc_envelope(&once);
    let error = err_text(decode_binary(&twice));
    assert!(
        error.contains("failed to deserialize tMBC payload"),
        "{error}"
    );
    assert!(load_module_from_bytes(&twice).is_err());

    let mut prefixed = TRUST_IR_BINARY_MAGIC.to_vec();
    prefixed.extend_from_slice(&good[8..12]);
    prefixed.extend_from_slice(&once);
    assert!(decode_binary(&prefixed).is_err(), "TRUST_IR header + tMBC");
}

/// Adversarial: every strict prefix of every bare fixture is refused without
/// a panic. A truncated container must never decode to a (smaller) module.
#[test]
fn review_every_truncation_of_a_bare_module_is_refused_without_panic() {
    for (name, binary, _) in binary_fixtures() {
        let good = read(&binary);
        for len in 0..good.len() {
            let prefix = &good[..len];
            let outcome = std::panic::catch_unwind(|| decode_binary(prefix));
            match outcome {
                Err(_) => panic!("{name}: decode_binary panicked on a {len}-byte prefix"),
                Ok(Ok(module)) => panic!(
                    "{name}: a {len}-of-{}-byte prefix decoded to module `{}`",
                    good.len(),
                    module.name
                ),
                Ok(Err(_)) => {}
            }
        }
    }
}

/// Adversarial: a single flipped bit anywhere in a bare container never
/// panics the loader. A flip may land in an unchecked byte and still decode
/// (the container carries no checksum), but it must not crash the consumer.
#[test]
fn review_single_bit_flips_never_panic_the_loader() {
    for (name, binary, _) in binary_fixtures() {
        let good = read(&binary);
        for index in 0..good.len() {
            for bit in [0u8, 7] {
                let mut bad = good.clone();
                bad[index] ^= 1 << bit;
                let outcome = std::panic::catch_unwind(|| decode_binary(&bad));
                assert!(
                    outcome.is_ok(),
                    "{name}: decode_binary panicked with byte {index} bit {bit} flipped"
                );
            }
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
