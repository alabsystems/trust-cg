// trust-cg-codegen/tests/trust_ir_corpus_roundtrip.rs — the pinned trust-ir
// conformance corpus through trust-cg's own reader and writer paths (L05-P7).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The pinned trust-ir ships its serialization conformance corpus as wire
//! files (`crates/trust-ir-conformance/tests/fixtures/`, located here through
//! `trust_ir_conformance::refuse::fixtures_dir()`, so it is always the corpus
//! of the pinned revision): every live golden in four formats (`.tmbc`,
//! `.json`, `.msgpack`, canonical `.trust_ir` text), the pinned
//! `compat/` blobs of the v24 read-floor move, the frozen
//! `v41-reader-compat/` serde roster, and the must-refuse corpus
//! (`refuse/`, whose `MANIFEST.tsv` states each row's verdict). It also holds
//! hand-written text-only binding-frame modules in `frame-cfg/`. trust-ir's
//! own `conformance` test proves those files against trust-ir's codecs; this
//! target proves them against TRUST-CG's. The level-S generic templates of
//! amendment S (wire v57: `templates/` and the pin
//! `compat/template_ident_param.{tmbs,json}`) are NOT modules: a template is
//! its own artifact (`TRUST_IS` magic), instantiated into a module by a
//! template consumer, and trust-cg consumes none, so its module readers must
//! refuse every template file, the binary entries by name
//! ([`pipeline::TEMPLATE_IS_NOT_A_MODULE`]); see [`NonModule::Template`].
//! The module formats:
//!
//! | format   | trust-cg entry points driven (every one must agree)                                        |
//! |----------|---------------------------------------------------------------------------------------------|
//! | `.tmbc`  | `load_module_as(Tmbc)` (the CLI default), `load_module_as(Auto)`, `load_module_from_bytes`, `decode_tmbc` over the golden wrapped in trust-cg's `tMBC` envelope |
//! | `.json`  | `load_module_as(Json)` (`--format=json`), `load_module_as(Auto)`, `load_module_from_bytes`  |
//! | `.trust_ir` | `load_module_as(Text)` (`--format=text`), `load_module_as(Auto)`, `load_module_from_bytes` |
//! | `.msgpack` | the same binary/auto/byte entries: trust-cg admits NO MessagePack, so each must REFUSE    |
//!
//! and requires, for every module, either an EXACT round trip or a refusal
//! BY NAME that the corpus predicts:
//!
//! * **Exact.** trust-cg's read equals trust-ir's read of the same file (the
//!   oracle, below) and the family's reference module (the independent
//!   MessagePack codec's result where a twin exists);
//!   `encode_tmbc` (the writer behind the CLI's canonical tMBC and the
//!   compile service's artifact identity) reproduces the golden `.tmbc`
//!   payload byte for byte and re-reads to the same module; the CLI's
//!   `--emit-json` spelling reproduces the golden `.json` byte for byte and
//!   re-reads; `trust_ir::format::canonical` of the read reproduces the golden
//!   `.trust_ir`, and trust-cg's own text writer (`--emit-trust_ir`) re-parses
//!   to the identical module and is a fixed point.
//! * **Refused by name.** A `.tmbc` whose v41+ header declares the contract
//!   surface while a bodied function carries no codegen license is refused as
//!   a producer omission (trust-ir's decoded-provenance rule, the corpus's
//!   `refuse/body_gate_omitted_at_contract_surface` verdict); a blob below the
//!   read floor or a poisoned `bytes` row is refused with trust-ir's
//!   `BinaryError` (the manifest's `deserialize_module` verdict); a text dump
//!   of a construct the grammar cannot spell is refused by its `#lossy`
//!   marker, with exactly the loss kinds trust-ir's `text_losses` reports
//!   (for `refuse/` rows, exactly the manifest's `text_losses` column).
//!
//! # The independent oracle (so a trust-cg mis-read cannot round-trip silently)
//!
//! A mis-read that is self-consistent — the reader drops or alters a field
//! and the writer faithfully re-encodes the altered module — passes every
//! round-trip check. So each read is compared with (1) trust-ir's own reader
//! of the SAME bytes (`binary::deserialize_module`, `parser::parse_module`,
//! serde), which catches every trust-cg-side layer (format detection,
//! envelopes, bounded file reads, provenance checks), and (2) the module the
//! corpus's `.msgpack` twin decodes to through `rmp-serde`, a codec trust-cg
//! never uses, which catches a defect common to trust-cg and the trust-ir
//! codec it wraps. `the_oracle_catches_a_self_consistent_misread` shows the
//! first check is not vacuous.
//!
//! The five text-only `frame-cfg/` inputs have no independent MessagePack
//! twin or canonical writer golden. They start from trust-ir's text parser
//! with their source IDs intact, drive all three trust-cg text readers, and
//! undergo the same binary, JSON and raw-text writer/read checks. This adds
//! transport coverage, not an independent source-parser oracle.
//!
//! # Mutation controls (recorded; run once at landing, 2026-09-29)
//!
//! * `decode_trust_ir_payload` with its decoded-provenance refusal disabled:
//!   the gate failed with 20 findings — each of the nine producer-omission
//!   `.tmbc` files "ADMITTED, but the corpus predicts a refusal", and eleven
//!   writer lanes "re-read a v4x image with an unstamped body".
//! * `parse_trust_ir_text` clearing `Module.files` (a self-consistent
//!   mis-read every text entry shares): 33 findings, among them
//!   "MIS-READ — trust-cg's reader disagrees with trust-ir's" on every text
//!   golden with a file table and "text write/read changes the module" on the
//!   writer lanes.
//!
//! # Evidence strength
//!
//! Test-rung evidence over the pinned corpus files, run on this host; never a
//! proof. It says nothing about modules the corpus does not contain — the
//! construct property generator in `tmbc_roundtrip_prop.rs` extends the same
//! checks to generated modules — and nothing about lowering.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use trust_cg_codegen::pipeline::{
    self, FormatMode, NOT_A_BINARY_MODULE, TEMPLATE_IS_NOT_A_MODULE, TMBC_MAGIC, TMBC_VERSION,
};
use trust_ir::template::Template;
use trust_ir::text_loss::{TextLoss, TextLossKind, text_losses};
use trust_ir::{Module, NativeVerificationBundle, ProofLineageManifest};
use trust_ir_conformance::refuse::{self, Carrier, Row, STRUCTURAL_LICENSE_AUTHORITY, Verdict};

// ---------------------------------------------------------------------------
// The corpus layout at the pinned revision
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Dir {
    Live,
    Compat,
    V41ReaderCompat,
    Refuse,
    /// Hand-written binding-frame control-flow modules. These are module
    /// inputs, not canonical writer goldens or a directory to omit.
    FrameCfg,
    /// The level-S template goldens (amendment S): every file is a
    /// [`NonModule::Template`] by the directory's own contract (trust-ir's
    /// `template_goldens.rs` keeps it exact: one stem in `.tmbs`,
    /// `.trust_irs`, `.json` and `.msgpack`).
    Templates,
}

impl Dir {
    const ALL: [Dir; 6] = [
        Dir::Live,
        Dir::Compat,
        Dir::V41ReaderCompat,
        Dir::Refuse,
        Dir::FrameCfg,
        Dir::Templates,
    ];

    fn rel(self) -> &'static str {
        match self {
            Dir::Live => "",
            Dir::Compat => "compat",
            Dir::V41ReaderCompat => "v41-reader-compat",
            Dir::Refuse => "refuse",
            Dir::FrameCfg => "frame-cfg",
            Dir::Templates => "templates",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Dir::Live => "fixtures/",
            Dir::Compat => "fixtures/compat/",
            Dir::V41ReaderCompat => "fixtures/v41-reader-compat/",
            Dir::Refuse => "fixtures/refuse/",
            Dir::FrameCfg => "fixtures/frame-cfg/",
            Dir::Templates => "fixtures/templates/",
        }
    }
}

/// Subdirectories of the corpus root this target does not walk, with why.
/// Exact together with [`Dir::ALL`]: a subdirectory in neither fails by name.
const UNWALKED_DIRECTORIES: &[(&str, &str)] = &[
    (
        "refuse_templates",
        "amendment S's level-S must-refuse corpus: every row is a refusal of a TEMPLATE consumer \
     (`deserialize_template`, `validate_template`, `instantiate`, with scripted hosts) and \
     trust-cg consumes no template; the rows a MODULE consumer meets (a template blob, and the \
     template `Ext` tags under the module magic) are `refuse/` rows, driven here",
    ),
    (
        "semr_compiled",
        "the stage-2 compiler's own trust-ir artifacts (`.bin`, `-Ztrust-dump=ir:`) that trust-ir's \
         `lean_exec_differential.rs` holds SemR's decoder and runs to; raw crate dumps with no \
         format twins, which VF5 proves rows over, not a golden family a backend round-trips",
    ),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Format {
    Tmbc,
    Json,
    Text,
    Msgpack,
}

impl Format {
    fn from_ext(ext: &str) -> Option<Self> {
        Some(match ext {
            "tmbc" => Format::Tmbc,
            "json" => Format::Json,
            "trust_ir" => Format::Text,
            "msgpack" => Format::Msgpack,
            _ => return None,
        })
    }

    fn ext(self) -> &'static str {
        match self {
            Format::Tmbc => "tmbc",
            Format::Json => "json",
            Format::Text => "trust_ir",
            Format::Msgpack => "msgpack",
        }
    }
}

/// What a non-module corpus file is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NonModule {
    /// A proof-lineage sidecar (`ProofLineageManifest`). trust-cg has no
    /// sidecar reader; its module reader must refuse the file.
    LineageSidecar,
    /// A native verification bundle; it CARRIES a module, which is driven
    /// through trust-cg's writers and readers like any other.
    NativeBundle,
    /// A level-S generic template (amendment S, wire v57) in one of its four
    /// formats: the `TRUST_IS` blob (`.tmbs`), the template text
    /// (`.trust_irs`) or its serde JSON / MessagePack form. Not a module and
    /// does not carry one: a template is instantiated into a module by a
    /// template consumer, and a module consumer refuses it (trust-ir's
    /// `refuse/template_blob_is_not_a_module`: by magic, never instantiated
    /// or partially read). trust-cg consumes no template, so every one of its
    /// module entries for the format must refuse the file, the binary
    /// entries by name; trust-ir's template codec must read it, to the
    /// template its stem's `.tmbs` blob decodes to, and the blob must
    /// re-encode byte for byte (so the file is what it is classified as).
    Template,
    /// Oracle data, a manifest, or snapshot provenance.
    Data,
}

/// Every file in the corpus that is not a module, with what it is. Exact in
/// both directions: an unlisted non-module file and a listed file that is
/// gone both fail by name. (Every file of `templates/` is a
/// [`NonModule::Template`] by its directory; see [`non_module_kind`].)
const NON_MODULE_FILES: &[(Dir, &str, NonModule)] = &[
    (
        Dir::Live,
        "proof_lineage_single_stage.trust_irpl",
        NonModule::LineageSidecar,
    ),
    (
        Dir::Live,
        "proof_lineage_single_stage.json",
        NonModule::LineageSidecar,
    ),
    (
        Dir::Live,
        "proof_lineage_single_stage.msgpack",
        NonModule::LineageSidecar,
    ),
    (
        Dir::Live,
        "proof_lineage_multi_stage.trust_irpl",
        NonModule::LineageSidecar,
    ),
    (
        Dir::Live,
        "proof_lineage_multi_stage.json",
        NonModule::LineageSidecar,
    ),
    (
        Dir::Live,
        "proof_lineage_multi_stage.msgpack",
        NonModule::LineageSidecar,
    ),
    (
        Dir::Live,
        "native_request_trust_bundle.json",
        NonModule::NativeBundle,
    ),
    (
        Dir::Live,
        "native_request_trust_bundle.msgpack",
        NonModule::NativeBundle,
    ),
    (Dir::Live, "vector_mask_oracles.json", NonModule::Data),
    (
        Dir::V41ReaderCompat,
        "native_request_trust_bundle.json",
        NonModule::NativeBundle,
    ),
    (
        Dir::V41ReaderCompat,
        "native_request_trust_bundle.msgpack",
        NonModule::NativeBundle,
    ),
    // Amendment S's never-regenerated template pin (trust-ir
    // `back_compat.rs`, `the_pinned_template_blob_keeps_its_bytes_and_identity`):
    // the `ident_param` template as first written, and its serde JSON twin
    // (`{"header": .., "module": ..}`, a `Template`, not a `Module`).
    (
        Dir::Compat,
        "template_ident_param.tmbs",
        NonModule::Template,
    ),
    (
        Dir::Compat,
        "template_ident_param.json",
        NonModule::Template,
    ),
    (Dir::V41ReaderCompat, "ORIGIN.json", NonModule::Data),
    (Dir::V41ReaderCompat, "module-names.txt", NonModule::Data),
    (Dir::Refuse, "MANIFEST.tsv", NonModule::Data),
    (Dir::Refuse, "UNCOVERED.tsv", NonModule::Data),
];

/// What the non-module file `name` of `dir` is: every file of `templates/` is
/// a template; elsewhere, its [`NON_MODULE_FILES`] row.
fn non_module_kind(dir: Dir, name: &str) -> Option<NonModule> {
    if dir == Dir::Templates {
        return Some(NonModule::Template);
    }
    NON_MODULE_FILES
        .iter()
        .find(|(d, file, _)| *d == dir && *file == name)
        .map(|(_, _, kind)| *kind)
}

/// The template files the corpus holds at the pinned revision (the
/// `compat/` pin's two formats and `templates/`' nine goldens in four), each
/// read by trust-ir's template codec and refused by trust-cg's module
/// readers. A pin move that adds or drops one fails the census by name.
const TEMPLATE_FILES: usize = 38;

/// The frozen v41 roster keeps its historical spelling; a live fixture renamed
/// since is mapped here (trust-ir `conformance.rs` `LEGACY_ROSTER_RENAMES`).
const LEGACY_ROSTER_RENAMES: &[(&str, &str)] = &[("body_gate_v41", "body_gate")];

const PRODUCER_OMISSION: &str = "producer omission";

/// The corpus `.tmbc` files outside `refuse/` that trust-cg's binary reader
/// refuses, with the text its refusal must carry and why. Exact in both
/// directions (a `refuse/` row's reader verdict comes from `MANIFEST.tsv`).
///
/// The nine live goldens are wire-format pins written at a v41+ header (a
/// v41+ feature is present) with at least one bodied function carrying no
/// codegen license; trust-ir's decoded-provenance rule
/// (`trust_ir_build::decoded_provenance_errors`, the corpus verdict of
/// `refuse/body_gate_omitted_at_contract_surface`) holds the producer to
/// stamping every body, so the reader refuses them — while their JSON and
/// text forms, which carry no wire version, decode (see
/// `JSON_TEXT_ADMIT_WHAT_THE_BINARY_READER_REFUSES`).
const TMBC_READER_REFUSALS: &[(Dir, &str, &str, &str)] = &[
    (
        Dir::Live,
        "abi_calling_conv",
        PRODUCER_OMISSION,
        "v45 golden; `caller` is bodied and unstamped",
    ),
    (
        Dir::Live,
        "abi_enum_tag_repr",
        PRODUCER_OMISSION,
        "v45 golden; `wide_tags` is bodied and unstamped",
    ),
    (
        Dir::Live,
        "abi_function_symbol",
        PRODUCER_OMISSION,
        "v45 golden; `hidden_helper` is bodied and unstamped",
    ),
    (
        Dir::Live,
        "body_gate",
        PRODUCER_OMISSION,
        "v41 golden pinning all three license states, including a bodied `None`",
    ),
    (
        Dir::Live,
        "composition",
        PRODUCER_OMISSION,
        "v41 golden; `passthrough` is bodied and unstamped",
    ),
    (
        Dir::Live,
        "import_scheme",
        PRODUCER_OMISSION,
        "v44 golden; `identity` is bodied and unstamped",
    ),
    (
        Dir::Live,
        "spec_carrier",
        PRODUCER_OMISSION,
        "v46 golden; `identity` is bodied and unstamped",
    ),
    (
        Dir::Live,
        "storage_only",
        PRODUCER_OMISSION,
        "v64 geometry golden; root is bodied and unstamped, not a source license",
    ),
    (
        Dir::Live,
        "text_directives",
        PRODUCER_OMISSION,
        "v41 golden; `sink` is bodied and unstamped",
    ),
    (
        Dir::Compat,
        "v22_composition",
        "unsupported version",
        "a v22 blob, below MIN_READ_VERSION 23 (the v24 read-floor move)",
    ),
    (
        Dir::Compat,
        "v22_frontend_emission_subset",
        "unsupported version",
        "a v22 blob, below MIN_READ_VERSION 23 (the v24 read-floor move)",
    ),
];

/// Modules whose tMBC form trust-cg's reader refuses as a producer omission
/// while their JSON / text forms decode. trust-ir states why on `BodyGate`:
/// a module parsed from text / JSON / MessagePack carries no wire version, so
/// the producer rule cannot apply to it. What stands between such a module
/// and code is then the codegen license policy, whose DEFAULT refuses a
/// claim-less body (`UnlicensedBodyPolicy::Refuse`, roadmap WS7.5 / DG-73);
/// only an explicit, named `Permit` (a grandfathering consumer) admits it.
/// `json_twin_of_the_producer_omission_row_is_refused_unless_explicitly_permitted`
/// measures that on the must-refuse row. Exact: a module that joins or
/// leaves this list fails by name.
const JSON_TEXT_ADMIT_WHAT_THE_BINARY_READER_REFUSES: &[(Dir, &str)] = &[
    (Dir::Live, "abi_calling_conv"),
    (Dir::Live, "abi_enum_tag_repr"),
    (Dir::Live, "abi_function_symbol"),
    (Dir::Live, "body_gate"),
    (Dir::Live, "composition"),
    (Dir::Live, "import_scheme"),
    (Dir::Live, "spec_carrier"),
    (Dir::Live, "storage_only"),
    (Dir::Live, "text_directives"),
    (Dir::Refuse, "body_gate_omitted_at_contract_surface"),
];

/// The modules outside `refuse/` whose TEXT form does not round-trip: the
/// kinds trust-ir's `text_losses` reports for the module as trust-cg's text
/// writer (`--emit-trust_ir`) prints it. Every dump carries the `#lossy`
/// marker and trust-cg's text reader refuses it by that marker; a `.trust_ir`
/// golden of such a module is refused the same way. Exact in both directions
/// (for `refuse/` rows the manifest's `text_losses` column is the table).
/// Empty since trust-ir 8cf20223: WS4.4 (51e81d0c, "text carries the proof
/// surface") prints function summaries, spec carriers, clause bindings, kernel
/// rechecks and obligation kinds, the five kinds this table pinned for
/// `composition`, `spec_carrier` and `lean_library_envelope` (live, compat and
/// v41-reader-compat) at 9674bea5, so every module outside `refuse/` now
/// round-trips through text.
const TEXT_LOSSES: &[(Dir, &str, &[TextLossKind])] = &[];

/// The census at the pinned revision: `(dir, format, files, round-tripped,
/// [(refusal, count)])`. A pin move that changes the corpus fails here with
/// the measured census printed, so the report stays reproducible.
type CensusRow = (Dir, Format, usize, usize, &'static [(&'static str, usize)]);

/// (trust-ir `9674bea5`: the live corpus gained the four-format
/// `inst_wire_batch` golden, the only one at header 51, and trust-cg
/// round-trips it in tMBC, JSON and text.)
/// (trust-ir `8cf20223`: the live corpus gained the v52 `assert_kind` golden
/// and WS4.4's `proof_surface`, both four-format and round-tripped in tMBC,
/// JSON and text; every live module now has a text golden, and none is
/// `#lossy` (see `TEXT_LOSSES`). `refuse/` gained two tMBC rows and two
/// JSON / MessagePack rows.)
/// (trust-ir `8a0d54c0`: the live corpus gained the v53 `call_unwind_boundary`
/// golden, four-format and round-tripped in tMBC, JSON and text; `refuse/`
/// gained the two poisoned tMBC rows that spell its tags under a v52 header.)
/// (trust-ir `6f2dfce6`: the live corpus gained the v54 panic-site goldens
/// `assert_panic_site` and `assert_invoke`, four-format and round-tripped in
/// tMBC, JSON and text; `compat/` gained the pre-v54 JSON twin
/// `pre_panic_site_assert_kind` (read and round-tripped) and two MessagePack
/// twins; `refuse/` gained six tMBC rows (one poisoned: an unknown panic
/// location tag) and five JSON / MessagePack rows, the v54 site refusals.)
/// (trust-ir `0be81d5c`: the live corpus gained the v55 `drop_glue` and v56
/// `unwind_twins` goldens, four-format and round-tripped in tMBC, JSON and
/// text; `compat/` gained the v55 blob `drop_glue_table` (read and
/// round-tripped at its own header) and the pre-v55 JSON / MessagePack twins
/// `pre_drop_glue_assert_invoke`; `refuse/` gained six tMBC rows (one
/// poisoned: `blob_drop_glue_not_canonical`) and five JSON / MessagePack rows,
/// the amendment-D refusals.)
/// (trust-ir `0f243925`, amendment S, wire v57 level-S generic templates: no
/// module golden changed; `refuse/` gained the three poisoned tMBC rows a
/// MODULE consumer meets — `template_blob_is_not_a_module` (a `TRUST_IS`
/// blob, `InvalidMagic`, refused by trust-cg's container check by name) and
/// `ty_ext_tag_under_module_magic` / `constant_ext_tag_under_module_magic`
/// (a template `Ext` tag under the module magic, `InvalidTag`); the template
/// files — `compat/template_ident_param.{tmbs,json}` and `templates/` — are
/// not modules ([`NonModule::Template`], counted by [`TEMPLATE_FILES`]); and
/// `refuse_templates/`, the template-consumer corpus, is
/// [`UNWALKED_DIRECTORIES`].)
/// (trust-ir `695fcf51`, wire v58 nominal identity: the live corpus gained the
/// v58 goldens `closure_layout` and `nominal_type_origin`, four-format and
/// round-tripped in tMBC, JSON and text; `refuse/` gained the tMBC, JSON and
/// MessagePack row `type_origin_claimed_twice`, round-tripped by the reader
/// and refused by the backend's nominal-origin floor.)
/// (Re-measured at the D1b pin move, whose trust-ir carries main through
/// `5c4f9e1d`. This table had not followed the pin: at `8dfdd235` the test
/// was already red on trust-cg main, whose corpus there holds 54 live and 81
/// `refuse/` tMBC files against the table's 52 and 74. At the new pin: 54
/// live files per format (46 tMBC round-tripped, 8 still a producer
/// omission); `refuse/` 86 tMBC (66 round-tripped, 19 poisoned bytes rows, 1
/// producer omission) and 67 JSON / MessagePack, the five rows after
/// `8dfdd235` included (`const_usize_beyond_target_width`,
/// `rust_reference_as_permission_borrow`, and three switch-case rows).)
/// (trust-ir `cb639776`, wire v61 `certificate-binding`: the live corpus
/// gained the v61 golden `certificate_binding`, four-format and round-tripped
/// in tMBC, JSON and text (55 live files per format, 47 tMBC round-tripped);
/// `refuse/` gained the tMBC, JSON and MessagePack rows
/// `body_gate_evidence_stale_body_digest` and
/// `body_gate_kernel_tv_evidence_unrecorded`, round-tripped by the reader and
/// refused by the admission's license-evidence layer (88 tMBC, 68
/// round-tripped; 69 JSON / MessagePack).)
/// (trust-ir `8d304e36`, wire v62 `ParamPointeeEntry`: the live corpus gained
/// the v62 golden `param_pointee_place`, four-format and round-tripped in
/// tMBC, JSON and text (56 live files per format, 48 tMBC round-tripped; the
/// eight producer omissions are `TMBC_READER_REFUSALS`' unchanged eight);
/// `refuse/` gained the poisoned tMBC row
/// `blob_param_pointee_place_below_its_version` (`InvalidTag`, 20 poisoned
/// rows) and the tMBC, JSON and MessagePack rows
/// `summary_clause_param_pointee_of_by_value_param` (`InvalidFunctionSummary`)
/// and `function_symbol_synthetic_shadowed` (`SyntheticSymbolName`),
/// round-tripped by the reader and refused by the admission (LD-PIN62-3);
/// 91 tMBC, 70 round-tripped; 71 JSON / MessagePack. `dc2b8073` moves no
/// corpus file. Decision record LD-77.)
/// (trust-ir `1e05bd01`, the lattice train to Clean `55410ba0b`: `refuse/`
/// gained the binding-frame rows `binding_frame_closed_edge` and
/// `binding_frame_analysis_incomplete` (tMBC, JSON and MessagePack), read and
/// round-tripped by the reader and refused by the admission (93 tMBC, 72
/// round-tripped; 73 JSON / MessagePack; the second row's text form loses its
/// entry block, which its manifest row's `text_losses` names); the corpus root
/// gained `frame-cfg/` and `semr_compiled/`. `semr_compiled/` is not a golden
/// family ([`UNWALKED_DIRECTORIES`]); the five text-only `frame-cfg/` modules
/// are walked as [`Dir::FrameCfg`] (LD-STRICT-FRAME-1E05). No live, compat or
/// template file moved.)
/// (trust-ir `424049d8`, scoped proof components on Clean `4b85a3bd`: `refuse/` gained the
/// `make_closure_capture_count` tMBC/JSON/MessagePack row. Its one supplied
/// capture mismatches the declared two-capture environment; the reader still
/// round-trips it and module validation must refuse `InvalidMakeClosure`.
/// Measured 94 tMBC (73 round-tripped), 74 JSON and 74 MessagePack files;
/// no live, compat, reader-compat, frame, template or exception row moved.)
/// (trust-ir `96f7ff19`, wire v68–v70 tensor regions, gather/scatter and the
/// weight-blob table: the live corpus gained `tensor_map_reduce_view`,
/// `tensor_gather_scatter` and `tensor_weight_blob` (tMBC, JSON, text and
/// MessagePack each), all three round-tripped. `refuse/` gained eleven module
/// rows (`tensor_blob_{codegen,digest_mismatch,extents_do_not_fit_its_bytes,missing}`,
/// `tensor_gather_{coordinate_count_is_not_the_data_rank,scatter_codegen}`,
/// `tensor_map_{lane_out_of_scope,reduce_view_codegen}`,
/// `tensor_reduce_axes_not_ascending`, `tensor_scatter_init_is_not_the_result_type`,
/// `tensor_view_shape_reads_a_coordinate`) in tMBC, JSON and MessagePack, and
/// four poisoned bytes rows (`blob_tensor_*_below_its_version`,
/// `blob_tensor_blob_table_not_canonical`). Measured 64 live tMBC (55
/// round-tripped), 114 refuse tMBC (88 round-tripped, 25 poisoned), 89 refuse
/// JSON and 89 refuse MessagePack files; no compat, reader-compat, frame,
/// template or exception row moved.)
const CENSUS: &[CensusRow] = &[
    (
        Dir::Live,
        Format::Tmbc,
        64,
        55,
        &[("reader: producer omission (v41+ header, unstamped body)", 9)],
    ),
    (Dir::Live, Format::Json, 64, 64, &[]),
    (Dir::Live, Format::Text, 64, 64, &[]),
    (
        Dir::Live,
        Format::Msgpack,
        64,
        0,
        &[("not a trust-cg input format (MessagePack)", 64)],
    ),
    (
        Dir::Compat,
        Format::Tmbc,
        5,
        3,
        &[("reader: below the read floor (UnsupportedVersion)", 2)],
    ),
    (Dir::Compat, Format::Json, 2, 2, &[]),
    (
        Dir::Compat,
        Format::Msgpack,
        7,
        0,
        &[("not a trust-cg input format (MessagePack)", 7)],
    ),
    (Dir::V41ReaderCompat, Format::Json, 30, 30, &[]),
    (
        Dir::V41ReaderCompat,
        Format::Msgpack,
        30,
        0,
        &[("not a trust-cg input format (MessagePack)", 30)],
    ),
    (
        Dir::Refuse,
        Format::Tmbc,
        114,
        88,
        &[
            ("reader: manifest Binary verdict (poisoned bytes row)", 25),
            ("reader: producer omission (v41+ header, unstamped body)", 1),
        ],
    ),
    (Dir::Refuse, Format::Json, 89, 89, &[]),
    (
        Dir::Refuse,
        Format::Msgpack,
        89,
        0,
        &[("not a trust-cg input format (MessagePack)", 89)],
    ),
    (Dir::FrameCfg, Format::Text, 5, 5, &[]),
];

// ---------------------------------------------------------------------------
// Readers
// ---------------------------------------------------------------------------

fn corpus_root() -> PathBuf {
    refuse::fixtures_dir()
        .parent()
        .expect("refuse/ sits inside the corpus fixtures directory")
        .to_path_buf()
}

type Read = Result<Module, String>;

/// A golden bare `TRUST_IR` payload inside trust-cg's `tMBC` envelope.
fn envelope(bare: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + bare.len());
    out.extend_from_slice(TMBC_MAGIC);
    out.extend_from_slice(&TMBC_VERSION.to_le_bytes());
    out.extend_from_slice(bare);
    out
}

/// Every trust-cg entry point that admits `format` (MessagePack: the entries
/// a `.msgpack` file would meet), over the file at `path`.
fn trust_cg_reads(format: Format, path: &Path, bytes: &[u8]) -> Vec<(&'static str, Read)> {
    let e = |e: pipeline::PipelineError| e.to_string();
    let file = |mode| pipeline::load_module_as(path, mode).map_err(e);
    let from_bytes = pipeline::load_module_from_bytes(bytes).map_err(e);
    match format {
        Format::Tmbc => vec![
            ("load_module_as(Tmbc)", file(FormatMode::Tmbc)),
            ("load_module_as(Auto)", file(FormatMode::Auto)),
            ("load_module_from_bytes", from_bytes),
            (
                "decode_tmbc(tMBC envelope)",
                pipeline::decode_tmbc(&envelope(bytes)).map_err(e),
            ),
        ],
        Format::Json => vec![
            ("load_module_as(Json)", file(FormatMode::Json)),
            ("load_module_as(Auto)", file(FormatMode::Auto)),
            ("load_module_from_bytes", from_bytes),
        ],
        Format::Text => vec![
            ("load_module_as(Text)", file(FormatMode::Text)),
            ("load_module_as(Auto)", file(FormatMode::Auto)),
            ("load_module_from_bytes", from_bytes),
        ],
        Format::Msgpack => vec![
            ("load_module_as(Tmbc)", file(FormatMode::Tmbc)),
            ("load_module_as(Auto)", file(FormatMode::Auto)),
            ("load_module_from_bytes", from_bytes),
        ],
    }
}

/// trust-ir's own reader of the same bytes: no trust-cg code on this path.
fn oracle_read(format: Format, bytes: &[u8]) -> Read {
    match format {
        Format::Tmbc => {
            trust_ir::binary::deserialize_module(bytes).map_err(|e| format!("{e:?} ({e})"))
        }
        Format::Json => serde_json::from_slice::<Module>(bytes).map_err(|e| e.to_string()),
        Format::Msgpack => rmp_serde::from_slice::<Module>(bytes).map_err(|e| e.to_string()),
        Format::Text => std::str::from_utf8(bytes)
            .map_err(|e| e.to_string())
            .and_then(|t| trust_ir::parser::parse_module(t).map_err(|e| e.to_string())),
    }
}

fn loss_kinds(losses: &[TextLoss]) -> BTreeSet<TextLossKind> {
    losses.iter().map(TextLoss::kind).collect()
}

fn license_for_the_run() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_recognized_authority(STRUCTURAL_LICENSE_AUTHORITY)
}

// ---------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------

#[derive(Debug, Default, Clone, PartialEq, Eq)]
struct Family {
    files: usize,
    round_tripped: usize,
    refused: BTreeMap<String, usize>,
}

#[derive(Default)]
struct Census {
    families: BTreeMap<(Dir, Format), Family>,
    /// `(dir, stem)` -> the kinds trust-cg's text writer cannot carry.
    text_losses: BTreeMap<(Dir, String), BTreeSet<TextLossKind>>,
    /// `(dir, stem)` whose tMBC trust-cg refuses as a producer omission while
    /// the JSON / text form decodes.
    json_text_admit: BTreeSet<(Dir, String)>,
    /// `(stem, golden header, re-encoded header)` for the compat blobs trust-cg
    /// decodes: the writer re-encodes at the minimum lossless version.
    reencoded: Vec<(String, u32, u32)>,
    non_module_files: usize,
    bundle_modules: usize,
    lineage_sidecars: usize,
    /// Template files read by trust-ir's template codec and refused by every
    /// trust-cg module entry.
    template_files: usize,
    findings: Vec<String>,
}

impl Census {
    fn family(&mut self, dir: Dir, format: Format) -> &mut Family {
        self.families.entry((dir, format)).or_default()
    }

    fn finding(&mut self, message: String) {
        self.findings.push(message);
    }
}

/// One module of the corpus: its stem and the formats present.
struct Case {
    dir: Dir,
    stem: String,
    files: BTreeMap<Format, PathBuf>,
}

impl Case {
    fn label(&self) -> String {
        format!("{}{}", self.dir.label(), self.stem)
    }

    fn bytes(&self, format: Format) -> Option<Vec<u8>> {
        self.files
            .get(&format)
            .map(|path| fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display())))
    }
}

/// The reader verdict `MANIFEST.tsv` states for a `refuse/` row, or `None`
/// when trust-cg's reader must admit the row.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ReaderVerdict {
    /// `deserialize_module=Binary:<variant>`: trust-ir's reader refuses the
    /// bytes, and trust-cg's must refuse them with the same message — or,
    /// for `InvalidMagic`, with its own container check
    /// ([`NOT_A_BINARY_MODULE`]), which runs first.
    Binary(String),
    /// `validate_module_as_decoded=Validation:ProducerOmittedBodyGate`.
    ProducerOmission,
}

fn manifest_reader_verdict(row: &Row) -> Option<ReaderVerdict> {
    row.manifest.expectations.iter().find_map(|expectation| {
        match (expectation.entry_point.as_str(), &expectation.verdict) {
            ("deserialize_module", Verdict::Binary(variant)) => {
                Some(ReaderVerdict::Binary(variant.clone()))
            }
            ("validate_module_as_decoded", Verdict::Validation(variant))
                if variant == "ProducerOmittedBodyGate" =>
            {
                Some(ReaderVerdict::ProducerOmission)
            }
            _ => None,
        }
    })
}

/// The needles a refusal of a `refuse/` row's bytes must carry, checked
/// against trust-ir's own reader (whose error must be the manifest's variant).
fn manifest_reader_refusal(row: &Row, bytes: &[u8]) -> Option<(Vec<String>, &'static str)> {
    match manifest_reader_verdict(row)? {
        ReaderVerdict::ProducerOmission => Some((
            vec![PRODUCER_OMISSION.to_string()],
            "reader: producer omission (v41+ header, unstamped body)",
        )),
        ReaderVerdict::Binary(variant) => {
            let needles = match trust_ir::binary::deserialize_module(bytes) {
                Err(error) if format!("{error:?}").starts_with(variant.as_str()) => {
                    if variant == "InvalidMagic" {
                        vec![NOT_A_BINARY_MODULE.to_string()]
                    } else {
                        vec![error.to_string()]
                    }
                }
                // trust-ir's reader disagrees with its own manifest: no
                // needle can match, so the row fails by name below.
                other => vec![format!(
                    "<trust-ir's reader returns {other:?}, not Binary:{variant}>"
                )],
            };
            Some((
                needles,
                "reader: manifest Binary verdict (poisoned bytes row)",
            ))
        }
    }
}

fn enumerate(dir: Dir) -> (Vec<Case>, Vec<PathBuf>) {
    let root = corpus_root().join(dir.rel());
    let mut stems: BTreeMap<String, BTreeMap<Format, PathBuf>> = BTreeMap::new();
    let mut non_modules = Vec::new();
    let mut entries: Vec<PathBuf> = fs::read_dir(&root)
        .unwrap_or_else(|e| panic!("{}: {e}", root.display()))
        .map(|entry| entry.expect("corpus entry").path())
        .collect();
    entries.sort();
    // Exact in both directions: a listed unwalked directory that is gone
    // fails by name, as an unlisted one does below.
    if dir == Dir::Live {
        for (unwalked, _) in UNWALKED_DIRECTORIES {
            assert!(
                root.join(unwalked).is_dir(),
                "{}{unwalked}/: listed in UNWALKED_DIRECTORIES but no longer in the corpus",
                dir.label()
            );
        }
    }
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if path.is_dir() {
            // Every subdirectory is a walked `Dir` or a named unwalked one.
            let known = dir == Dir::Live
                && (Dir::ALL.iter().any(|d| *d != Dir::Live && d.rel() == name)
                    || UNWALKED_DIRECTORIES.iter().any(|(n, _)| *n == name));
            assert!(
                known,
                "{}{name}/: a corpus directory neither walked (Dir::ALL) nor in \
                 UNWALKED_DIRECTORIES — a new corpus family? classify it",
                dir.label()
            );
            continue;
        }
        if non_module_kind(dir, &name).is_some() {
            non_modules.push(path);
            continue;
        }
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        let ext = path
            .extension()
            .map(|e| e.to_string_lossy().into_owned())
            .unwrap_or_default();
        let format = Format::from_ext(&ext).unwrap_or_else(|| {
            panic!(
                "{}{name}: not a module format and not in NON_MODULE_FILES — a new corpus \
                 family? classify it",
                dir.label()
            )
        });
        stems.entry(stem).or_default().insert(format, path);
    }
    let cases = stems
        .into_iter()
        .map(|(stem, files)| Case { dir, stem, files })
        .collect();
    (cases, non_modules)
}

/// The module every format of `case` must denote: the independent
/// MessagePack reading when there is one, else trust-ir's binary reading,
/// else its JSON reading. A frozen v41 serde input denotes the LIVE module
/// of its (renamed) stem. The text-only frame-CFG family starts from
/// trust-ir's parser; its writer checks compare the resulting module through
/// the binary, JSON and text transports rather than a second source format.
fn reference(case: &Case) -> Option<Module> {
    if case.dir == Dir::V41ReaderCompat {
        let live = LEGACY_ROSTER_RENAMES
            .iter()
            .find(|(legacy, _)| *legacy == case.stem)
            .map_or(case.stem.as_str(), |(_, renamed)| *renamed);
        let path = corpus_root().join(format!("{live}.msgpack"));
        let bytes = fs::read(&path).ok()?;
        return oracle_read(Format::Msgpack, &bytes).ok();
    }
    if case.dir == Dir::FrameCfg {
        return case
            .bytes(Format::Text)
            .and_then(|bytes| oracle_read(Format::Text, &bytes).ok());
    }
    for format in [Format::Msgpack, Format::Tmbc, Format::Json] {
        if let Some(bytes) = case.bytes(format)
            && let Ok(module) = oracle_read(format, &bytes)
        {
            return Some(module);
        }
    }
    None
}

/// The golden bytes the writers must reproduce for `case`: its own files,
/// except a frozen v41 serde input, whose writers must reproduce the LIVE
/// goldens (the legacy spelling is read, the current one is written).
fn goldens(case: &Case) -> (Option<Vec<u8>>, Option<String>, Option<String>) {
    let root = corpus_root();
    if case.stem.contains('#') {
        // A module carried inside a bundle file has no goldens of its own.
        return (None, None, None);
    }
    match case.dir {
        // `templates/` holds no module case (every file is a template).
        // The hand-written frame-CFG inputs pin modules, not the spelling
        // of canonical writer output.
        Dir::Compat | Dir::Templates | Dir::FrameCfg => (None, None, None),
        Dir::V41ReaderCompat => {
            let live = LEGACY_ROSTER_RENAMES
                .iter()
                .find(|(legacy, _)| *legacy == case.stem)
                .map_or(case.stem.as_str(), |(_, renamed)| *renamed);
            (
                fs::read(root.join(format!("{live}.tmbc"))).ok(),
                fs::read_to_string(root.join(format!("{live}.json"))).ok(),
                fs::read_to_string(root.join(format!("{live}.trust_ir"))).ok(),
            )
        }
        Dir::Live | Dir::Refuse => (
            case.bytes(Format::Tmbc),
            case.bytes(Format::Json)
                .map(|b| String::from_utf8(b).expect("JSON golden is UTF-8")),
            case.bytes(Format::Text)
                .map(|b| String::from_utf8(b).expect("text golden is UTF-8")),
        ),
    }
}

/// True when trust-ir's decoded-provenance rule refuses `module` written at
/// `header`: a v41+ header (the contract surface) with a bodied function
/// that carries no codegen license. Computed from the module itself, so the
/// writer lane predicts the reader's refusal independently of the reader.
fn producer_omission_at(module: &Module, header: u32) -> bool {
    header >= 41
        && module
            .functions
            .iter()
            .any(|f| !f.is_declaration() && f.body_gate.is_none())
}

/// The writer lanes over the reference module: `encode_tmbc`, the
/// `--emit-json` spelling, trust-cg's `--emit-trust_ir` text writer and the
/// canonical printer — each against its golden where one exists, and each
/// re-read through trust-cg.
fn check_writers(census: &mut Census, case: &Case, module: &Module) {
    let label = case.label();
    let (golden_tmbc, golden_json, golden_text) = goldens(case);

    // tMBC (the CLI's canonical bytes and the compile service's identity).
    match pipeline::encode_tmbc(module) {
        Err(e) => census.finding(format!("{label}: encode_tmbc refused a corpus module: {e}")),
        Ok(env) => {
            if env[..4] != TMBC_MAGIC[..] || env[4..8] != TMBC_VERSION.to_le_bytes() {
                census.finding(format!("{label}: encode_tmbc wrote a bad envelope header"));
            }
            let payload = &env[8..];
            let header = u32::from_le_bytes(payload[8..12].try_into().unwrap());
            if let Some(golden) = &golden_tmbc {
                if payload != golden.as_slice() {
                    census.finding(format!(
                        "{label}: encode_tmbc does not reproduce the golden .tmbc payload \
                         ({} bytes vs {})",
                        payload.len(),
                        golden.len()
                    ));
                }
            } else if let Some(original) = case.bytes(Format::Tmbc) {
                let was = u32::from_le_bytes(original[8..12].try_into().unwrap());
                census.reencoded.push((label.clone(), was, header));
            }
            let predicted = producer_omission_at(module, header);
            match (pipeline::decode_tmbc(&env), predicted) {
                (Ok(back), false) => {
                    if &back != module {
                        census.finding(format!("{label}: tMBC write/read changes the module"));
                    }
                    if pipeline::encode_tmbc(&back).ok().as_deref() != Some(env.as_slice()) {
                        census.finding(format!("{label}: tMBC bytes are not a fixed point"));
                    }
                }
                (Err(e), true) if e.to_string().contains(PRODUCER_OMISSION) => {
                    // trust-ir's plain reader (no producer rule) still
                    // reproduces the module, so the writer is exact.
                    match trust_ir::binary::deserialize_module(payload) {
                        Ok(back) if &back == module => {}
                        other => census.finding(format!(
                            "{label}: trust-ir's reader does not reproduce the written module: \
                             {:?}",
                            other.map(|_| ())
                        )),
                    }
                }
                (Ok(_), true) => census.finding(format!(
                    "{label}: trust-cg re-read a v{header} image with an unstamped body (the \
                     producer rule was not applied)"
                )),
                (Err(e), _) => census.finding(format!(
                    "{label}: trust-cg refuses its own re-encoding: {e}"
                )),
            }
        }
    }

    // JSON (`--emit-json`).
    match serde_json::to_string_pretty(module) {
        Err(e) => census.finding(format!("{label}: JSON writer failed: {e}")),
        Ok(json) => {
            if let Some(golden) = &golden_json
                && json != *golden
            {
                census.finding(format!(
                    "{label}: the --emit-json spelling does not reproduce the golden .json"
                ));
            }
            match pipeline::load_module_from_bytes(json.as_bytes()) {
                Ok(back) if &back == module => {}
                Ok(_) => census.finding(format!("{label}: JSON write/read changes the module")),
                Err(e) => census.finding(format!("{label}: JSON re-read refused: {e}")),
            }
        }
    }

    // Text: trust-cg's `--emit-trust_ir` writer (the Display form) and the
    // canonical printer the goldens are pinned in.
    let text = pipeline::encode_trust_ir_text(module);
    let losses = loss_kinds(&text_losses(module));
    match pipeline::parse_trust_ir_text(&text) {
        Ok(back) if losses.is_empty() => {
            if &back != module {
                census.finding(format!("{label}: text write/read changes the module"));
            }
            if pipeline::encode_trust_ir_text(&back) != text {
                census.finding(format!(
                    "{label}: --emit-trust_ir text is not a fixed point"
                ));
            }
        }
        Ok(_) => census.finding(format!(
            "{label}: trust-cg's text reader ACCEPTED a #lossy dump ({losses:?})"
        )),
        Err(e) if !losses.is_empty() => {
            if !e.to_string().contains("printed LOSSILY") {
                census.finding(format!(
                    "{label}: a lossy dump was refused, but not by its #lossy marker: {e}"
                ));
            }
            census
                .text_losses
                .insert((case.dir, case.stem.clone()), losses);
        }
        Err(e) => census.finding(format!(
            "{label}: trust-cg's text reader refused a loss-free dump: {e}"
        )),
    }
    if let Some(golden) = &golden_text
        && trust_ir::format::canonical(module) != *golden
    {
        census.finding(format!(
            "{label}: the canonical printer over trust-cg's read does not reproduce the golden \
             .trust_ir"
        ));
    }
}

fn run_case(census: &mut Census, case: &Case, rows: &BTreeMap<String, &Row>) {
    let label = case.label();
    let row = (case.dir == Dir::Refuse)
        .then(|| rows.get(&case.stem).copied())
        .flatten();
    if case.dir == Dir::Refuse && row.is_none() {
        census.finding(format!("{label}: a refuse/ file no MANIFEST.tsv row names"));
    }
    // A poisoned `bytes` row denotes no module; every other case must.
    let bytes_row = row.is_some_and(|row| row.manifest.carrier == Carrier::Bytes);
    let reference = reference(case);
    if reference.is_none() && !bytes_row {
        census.finding(format!(
            "{label}: no format of this module decodes anywhere"
        ));
        return;
    }
    let mut producer_omission_tmbc = false;

    for (&format, path) in &case.files {
        let bytes = case.bytes(format).expect("listed");
        let reads = trust_cg_reads(format, path, &bytes);
        let oracle = oracle_read(format, &bytes);
        // Every trust-cg entry point for the format agrees.
        let agree = reads.windows(2).all(|w| match (&w[0].1, &w[1].1) {
            (Ok(a), Ok(b)) => a == b,
            (Err(_), Err(_)) => true,
            _ => false,
        });
        if !agree {
            let outcomes: Vec<String> = reads
                .iter()
                .map(|(entry, r)| format!("{entry}={}", if r.is_ok() { "ok" } else { "refused" }))
                .collect();
            census.finding(format!(
                "{label}.{}: trust-cg's entry points disagree: {}",
                format.ext(),
                outcomes.join(", ")
            ));
            continue;
        }
        census.family(case.dir, format).files += 1;

        if format == Format::Msgpack {
            // Not a trust-cg input: refused on every entry, never mis-read.
            if reads.iter().any(|(_, r)| r.is_ok()) {
                census.finding(format!(
                    "{label}.msgpack: trust-cg ADMITTED MessagePack bytes"
                ));
            }
            match &oracle {
                Ok(m) if Some(m) == reference.as_ref() => {}
                Ok(_) => census.finding(format!(
                    "{label}.msgpack: the MessagePack twin denotes another module"
                )),
                Err(e) => census.finding(format!(
                    "{label}.msgpack: the independent MessagePack codec refuses the twin: {e}"
                )),
            }
            *census
                .family(case.dir, format)
                .refused
                .entry("not a trust-cg input format (MessagePack)".into())
                .or_default() += 1;
            continue;
        }

        // What the corpus predicts trust-cg's reader does with this file.
        let expected_refusal: Option<(Vec<String>, String)> = match (format, case.dir) {
            (Format::Tmbc, Dir::Refuse) => row
                .and_then(|row| manifest_reader_refusal(row, &bytes))
                .map(|(needles, why)| (needles, why.to_string())),
            (Format::Tmbc, dir) => TMBC_READER_REFUSALS
                .iter()
                .find(|(d, stem, _, _)| *d == dir && *stem == case.stem)
                .map(|(_, _, needle, _)| {
                    let why = if *needle == PRODUCER_OMISSION {
                        "reader: producer omission (v41+ header, unstamped body)"
                    } else {
                        "reader: below the read floor (UnsupportedVersion)"
                    };
                    (vec![(*needle).to_string()], why.to_string())
                }),
            (Format::Text, _) => {
                // The golden of a lossy module carries the #lossy marker.
                reference
                    .as_ref()
                    .map(trust_ir::format::canonicalize)
                    .filter(|canon| !text_losses(canon).is_empty())
                    .map(|_| {
                        (
                            vec!["printed LOSSILY".to_string()],
                            "reader: #lossy marker (text_losses)".to_string(),
                        )
                    })
            }
            _ => None,
        };

        let (_, first) = &reads[0];
        match (first, &oracle, expected_refusal) {
            (Ok(read), Ok(ir), None) => {
                // THE ORACLE: trust-cg's read is trust-ir's read of the same
                // bytes, and the family's reference module. The hand-written
                // frame-CFG inputs preserve source IDs; other text families
                // are canonical goldens of an independently decoded module.
                if read != ir {
                    census.finding(format!(
                        "{label}.{}: MIS-READ — trust-cg's reader disagrees with trust-ir's",
                        format.ext()
                    ));
                    continue;
                }
                let denotes = match (&reference, format) {
                    (Some(reference), Format::Text) if case.dir != Dir::FrameCfg => {
                        *read == trust_ir::format::canonicalize(reference)
                    }
                    (Some(reference), _) => read == reference,
                    (None, _) => false,
                };
                if !denotes {
                    census.finding(format!(
                        "{label}.{}: the read disagrees with the family's reference module",
                        format.ext()
                    ));
                    continue;
                }
                census.family(case.dir, format).round_tripped += 1;
            }
            (Err(message), _, Some((needles, why))) => {
                // The CLI's own entry names the refusal; the agreement check
                // above already holds every other entry to refusing it.
                if !needles
                    .iter()
                    .any(|needle| message.contains(needle.as_str()))
                {
                    census.finding(format!(
                        "{label}.{}: refused, but not by the predicted name {needles:?}: \
                         {message}",
                        format.ext()
                    ));
                }
                if format == Format::Tmbc && why.contains(PRODUCER_OMISSION) {
                    producer_omission_tmbc = true;
                }
                *census
                    .family(case.dir, format)
                    .refused
                    .entry(why)
                    .or_default() += 1;
            }
            (Ok(_), Err(ir), _) => census.finding(format!(
                "{label}.{}: trust-cg ADMITS bytes trust-ir's reader refuses ({ir})",
                format.ext()
            )),
            (Ok(_), Ok(_), Some((needles, _))) => census.finding(format!(
                "{label}.{}: ADMITTED, but the corpus predicts a refusal naming {needles:?}",
                format.ext()
            )),
            (Err(message), _, None) => census.finding(format!(
                "{label}.{}: trust-cg REFUSED a module the corpus predicts it reads: {message}",
                format.ext()
            )),
        }
    }

    // The writers, over the module every format denotes.
    let Some(reference) = reference else {
        return;
    };
    check_writers(census, case, &reference);

    // A tMBC refused as a producer omission while a version-less form of the
    // same module decodes.
    if producer_omission_tmbc
        && case
            .files
            .iter()
            .filter(|(f, _)| matches!(f, Format::Json | Format::Text))
            .any(|(_, path)| pipeline::load_module_as(path, FormatMode::Auto).is_ok())
    {
        census.json_text_admit.insert((case.dir, case.stem.clone()));
    }

    // The manifest's `text_losses` column is the exact expectation for a
    // refuse/ row's text writer.
    if let Some(row) = row {
        let measured: BTreeSet<String> = loss_kinds(&text_losses(&reference))
            .iter()
            .map(|kind| format!("{kind:?}"))
            .collect();
        let recorded: BTreeSet<String> = row.manifest.text_losses.iter().cloned().collect();
        if measured != recorded {
            census.finding(format!(
                "{label}: trust-cg's text writer loses {measured:?}; MANIFEST.tsv records \
                 {recorded:?}"
            ));
        }
    }
}

fn run_non_module(census: &mut Census, dir: Dir, path: &Path) {
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let label = format!("{}{name}", dir.label());
    let kind = non_module_kind(dir, &name).expect("classified");
    census.non_module_files += 1;
    let bytes = fs::read(path).expect("non-module corpus file");
    // Never mis-read as a module, whatever the entry point.
    for (entry, read) in [
        (
            "load_module_from_bytes",
            pipeline::load_module_from_bytes(&bytes),
        ),
        (
            "load_module_as(Auto)",
            pipeline::load_module_as(path, FormatMode::Auto),
        ),
    ] {
        if read.is_ok() {
            census.finding(format!(
                "{label}: trust-cg's module reader ({entry}) ADMITTED it"
            ));
        }
    }
    let ext = path.extension().map(|e| e.to_string_lossy().into_owned());
    match (kind, ext.as_deref()) {
        (NonModule::LineageSidecar, Some("trust_irpl")) => {
            census.lineage_sidecars += 1;
            // trust-cg has no sidecar reader: trust-ir's codec only.
            match trust_ir::binary::deserialize_proof_lineage_manifest(&bytes) {
                Ok(manifest) => {
                    if trust_ir::binary::serialize_proof_lineage_manifest(&manifest) != bytes {
                        census.finding(format!("{label}: sidecar re-encoding is not exact"));
                    }
                    let stem = path.with_extension("");
                    let json = fs::read(stem.with_extension("json")).expect("sidecar JSON");
                    let msgpack =
                        fs::read(stem.with_extension("msgpack")).expect("sidecar msgpack");
                    let from_json = serde_json::from_slice::<ProofLineageManifest>(&json);
                    let from_msgpack = rmp_serde::from_slice::<ProofLineageManifest>(&msgpack);
                    if from_json.ok().as_ref() != Some(&manifest)
                        || from_msgpack.ok().as_ref() != Some(&manifest)
                    {
                        census.finding(format!("{label}: the sidecar's three formats disagree"));
                    }
                }
                Err(e) => census.finding(format!("{label}: sidecar refused: {e:?}")),
            }
        }
        (NonModule::NativeBundle, Some(ext)) => {
            let bundle = if ext == "json" {
                serde_json::from_slice::<NativeVerificationBundle>(&bytes)
                    .map_err(|e| e.to_string())
            } else {
                rmp_serde::from_slice::<NativeVerificationBundle>(&bytes).map_err(|e| e.to_string())
            };
            match bundle {
                Ok(bundle) => {
                    census.bundle_modules += 1;
                    // The module a bundle carries takes the writer lanes.
                    let case = Case {
                        dir,
                        stem: format!("{name}#module"),
                        files: BTreeMap::new(),
                    };
                    check_writers(census, &case, &bundle.module);
                }
                Err(e) => census.finding(format!("{label}: bundle refused: {e}")),
            }
        }
        (NonModule::Template, Some(ext)) => {
            census.template_files += 1;
            check_template(census, &label, path, ext, &bytes);
        }
        // Every template file is checked by its format; one without an
        // extension names no format and is not silently passed over.
        (NonModule::Template, None) => {
            census.finding(format!(
                "{label}: a template-directory file without an extension"
            ));
        }
        _ => {}
    }
}

/// trust-ir's template codec for one template format.
fn read_template(ext: &str, bytes: &[u8]) -> Result<Template, String> {
    match ext {
        "tmbs" => trust_ir::binary::deserialize_template(bytes).map_err(|e| e.to_string()),
        "trust_irs" => std::str::from_utf8(bytes)
            .map_err(|e| e.to_string())
            .and_then(|t| trust_ir::parser::parse_template(t).map_err(|e| e.to_string())),
        "json" => serde_json::from_slice::<Template>(bytes).map_err(|e| e.to_string()),
        "msgpack" => rmp_serde::from_slice::<Template>(bytes).map_err(|e| e.to_string()),
        other => Err(format!("`.{other}` is not a template format")),
    }
}

/// A [`NonModule::Template`] file: what it is (trust-ir's template codec
/// reads it, to the template its stem's `.tmbs` blob denotes, and the blob is
/// canonical) and what trust-cg does with it (every module entry for the
/// format refuses it; the binary entries name it, as trust-ir's module reader
/// refuses the blob by magic).
fn check_template(census: &mut Census, label: &str, path: &Path, ext: &str, bytes: &[u8]) {
    match read_template(ext, bytes) {
        Err(e) => census.finding(format!(
            "{label}: classified a template, but trust-ir's template codec refuses it: {e}"
        )),
        Ok(template) => {
            let blob = fs::read(path.with_extension("tmbs"));
            match blob.as_deref().map(|b| read_template("tmbs", b)) {
                Ok(Ok(reference)) if reference == template => {}
                Ok(Ok(_)) => census.finding(format!(
                    "{label}: denotes another template than its stem's .tmbs blob"
                )),
                Ok(Err(e)) => census.finding(format!("{label}: its .tmbs twin is refused: {e}")),
                Err(e) => census.finding(format!("{label}: no .tmbs twin: {e}")),
            }
            if ext == "tmbs" {
                match trust_ir::binary::serialize_template(&template) {
                    Ok(again) if again == bytes => {}
                    Ok(_) => census.finding(format!(
                        "{label}: the template blob does not re-encode to its own bytes"
                    )),
                    Err(e) => census.finding(format!("{label}: the template re-encode fails: {e}")),
                }
                // The oracle: trust-ir's MODULE reader refuses it by magic.
                if trust_ir::binary::deserialize_module(bytes)
                    != Err(trust_ir::binary::BinaryError::InvalidMagic)
                {
                    census.finding(format!(
                        "{label}: trust-ir's module reader does not refuse the template blob \
                         as InvalidMagic"
                    ));
                }
            }
        }
    }
    // trust-cg: the entry that format would meet on the CLI (`--format`),
    // beside the auto-detecting file and byte entries `run_non_module`
    // already holds to a refusal.
    let explicit = match ext {
        "json" => FormatMode::Json,
        "trust_irs" => FormatMode::Text,
        _ => FormatMode::Tmbc,
    };
    let reads = [
        (
            "load_module_from_bytes",
            pipeline::load_module_from_bytes(bytes),
        ),
        (
            "load_module_as(Auto)",
            pipeline::load_module_as(path, FormatMode::Auto),
        ),
        (
            "load_module_as(<format>)",
            pipeline::load_module_as(path, explicit),
        ),
    ];
    for (entry, read) in reads {
        match read {
            Ok(_) => census.finding(format!(
                "{label}: trust-cg's module reader ({entry}) ADMITTED a template"
            )),
            Err(e) if ext == "tmbs" && !e.to_string().contains(TEMPLATE_IS_NOT_A_MODULE) => {
                census.finding(format!(
                    "{label}: {entry} refused the template blob, but not by name \
                     ({TEMPLATE_IS_NOT_A_MODULE:?}): {e}"
                ));
            }
            Err(_) => {}
        }
    }
}

fn run() -> Census {
    let mut census = Census::default();
    let rows = refuse::corpus()
        .expect("the pinned must-refuse corpus loads (a vacuous one is a typed error)");
    let by_id: BTreeMap<String, &Row> = rows.iter().map(|row| (row.id().to_owned(), row)).collect();
    let mut on_disk: BTreeSet<(Dir, String)> = BTreeSet::new();
    let mut refuse_stems: BTreeSet<String> = BTreeSet::new();
    for dir in Dir::ALL {
        let (cases, non_modules) = enumerate(dir);
        for path in &non_modules {
            on_disk.insert((
                dir,
                path.file_name().unwrap().to_string_lossy().into_owned(),
            ));
            run_non_module(&mut census, dir, path);
        }
        for case in &cases {
            if dir == Dir::Refuse {
                refuse_stems.insert(case.stem.clone());
            }
            run_case(&mut census, case, &by_id);
        }
    }
    for (dir, file, _) in NON_MODULE_FILES {
        if !on_disk.contains(&(*dir, (*file).to_owned())) {
            census.finding(format!(
                "NON_MODULE_FILES lists {}{file}, which the pinned corpus no longer has",
                dir.label()
            ));
        }
    }
    // Every artifact row of the manifest was driven.
    for row in &rows {
        if !refuse_stems.contains(row.id()) {
            census.finding(format!(
                "refuse/{}: a manifest artifact row with no file",
                row.id()
            ));
        }
        if row.manifest.carrier == Carrier::None {
            census.finding(format!(
                "refuse/{}: a `none` row returned as an artifact",
                row.id()
            ));
        }
    }
    census
}

fn census_table(census: &Census) -> String {
    let mut out = String::new();
    for ((dir, format), family) in &census.families {
        let _ = write!(
            out,
            "\n  {:<28} {:<9} files {:>3}  round-tripped {:>3}",
            dir.label(),
            format.ext(),
            family.files,
            family.round_tripped
        );
        for (why, count) in &family.refused {
            let _ = write!(out, "  | refused {count} ({why})");
        }
    }
    let _ = write!(
        out,
        "\n  non-module files {} (lineage sidecars {}, bundle modules driven through the \
         writers {}, level-S template files {})",
        census.non_module_files,
        census.lineage_sidecars,
        census.bundle_modules,
        census.template_files
    );
    let _ = write!(out, "\n  text writer losses (refused by #lossy):");
    for ((dir, stem), kinds) in &census.text_losses {
        let _ = write!(out, "\n    {}{stem}: {kinds:?}", dir.label());
    }
    let _ = write!(
        out,
        "\n  compat blobs re-encoded at the minimum lossless header:"
    );
    for (label, was, now) in &census.reencoded {
        let _ = write!(out, "\n    {label}: v{was} -> v{now}");
    }
    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// THE GATE: every module of the pinned corpus round-trips exactly through
/// trust-cg's readers and writers, agrees with trust-ir's reader and the
/// independent codec, or is refused by the name the corpus predicts.
#[test]
fn every_corpus_module_round_trips_through_trust_cg_or_is_refused_by_name() {
    let census = run();
    eprintln!(
        "trust-ir conformance corpus through trust-cg's readers:{}",
        census_table(&census)
    );
    assert!(
        census.findings.is_empty(),
        "{} finding(s):\n  {}",
        census.findings.len(),
        census.findings.join("\n  ")
    );
}

/// The census at the pinned revision is exact, and so are the three
/// named-exception tables (text losses, the JSON/text-versus-tMBC reader
/// asymmetry, and the tMBC reader refusals).
#[test]
fn corpus_census_and_exception_tables_are_exact() {
    let census = run();
    let mut drift = Vec::new();
    let pinned: BTreeMap<(Dir, Format), Family> = CENSUS
        .iter()
        .map(|(dir, format, files, round_tripped, refused)| {
            (
                (*dir, *format),
                Family {
                    files: *files,
                    round_tripped: *round_tripped,
                    refused: refused
                        .iter()
                        .map(|(why, count)| ((*why).to_owned(), *count))
                        .collect(),
                },
            )
        })
        .collect();
    if pinned != census.families || census.template_files != TEMPLATE_FILES {
        drift.push(format!(
            "CENSUS or TEMPLATE_FILES ({TEMPLATE_FILES}) drifted (a pin move changed the \
             corpus?); measured:{}",
            census_table(&census)
        ));
    }
    let expected_losses: BTreeMap<(Dir, String), BTreeSet<TextLossKind>> = TEXT_LOSSES
        .iter()
        .map(|(dir, stem, kinds)| ((*dir, (*stem).to_owned()), kinds.iter().copied().collect()))
        .collect();
    let measured_losses: BTreeMap<(Dir, String), BTreeSet<TextLossKind>> = census
        .text_losses
        .iter()
        .filter(|((dir, _), _)| *dir != Dir::Refuse)
        .map(|(key, kinds)| (key.clone(), kinds.clone()))
        .collect();
    if expected_losses != measured_losses {
        drift.push(format!(
            "TEXT_LOSSES drifted: pinned {expected_losses:?}, measured {measured_losses:?}"
        ));
    }
    let expected_admit: BTreeSet<(Dir, String)> = JSON_TEXT_ADMIT_WHAT_THE_BINARY_READER_REFUSES
        .iter()
        .map(|(dir, stem)| (*dir, (*stem).to_owned()))
        .collect();
    if expected_admit != census.json_text_admit {
        drift.push(format!(
            "JSON_TEXT_ADMIT_WHAT_THE_BINARY_READER_REFUSES drifted: pinned {expected_admit:?}, \
             measured {:?}",
            census.json_text_admit
        ));
    }
    // TMBC_READER_REFUSALS rows name corpus files whose refusal the gate saw.
    for (dir, stem, _, _) in TMBC_READER_REFUSALS {
        if !corpus_root()
            .join(dir.rel())
            .join(format!("{stem}.tmbc"))
            .is_file()
        {
            drift.push(format!(
                "TMBC_READER_REFUSALS names {}{stem}.tmbc, which the corpus no longer has",
                dir.label()
            ));
        }
    }
    assert!(drift.is_empty(), "{}", drift.join("\n"));
}

/// The oracle is not vacuous. For every corpus module trust-cg reads from
/// `.tmbc`, a simulated SELF-CONSISTENT mis-read — the module with one field
/// altered, which trust-cg's writer then re-encodes and re-reads perfectly —
/// passes the write/read round trip, and is caught only by comparing with
/// trust-ir's reader of the golden bytes.
#[test]
fn the_oracle_catches_a_self_consistent_misread() {
    let (cases, _) = enumerate(Dir::Live);
    let mut exercised = 0;
    for case in &cases {
        let Some(bytes) = case.bytes(Format::Tmbc) else {
            continue;
        };
        let Ok(read) = pipeline::load_module_from_bytes(&bytes) else {
            continue;
        };
        let mut misread = read.clone();
        misread.name.push_str("~misread");
        // The round trip alone is blind to it.
        let env = pipeline::encode_tmbc(&misread).expect("re-encode");
        assert_eq!(
            pipeline::decode_tmbc(&env).expect("re-read"),
            misread,
            "{}: the mis-read round-trips",
            case.label()
        );
        // The oracle is not.
        let oracle = oracle_read(Format::Tmbc, &bytes).expect("trust-ir reads the golden");
        assert_ne!(oracle, misread, "{}: the oracle must see it", case.label());
        assert_eq!(
            oracle,
            read,
            "{}: and agree with the true read",
            case.label()
        );
        exercised += 1;
    }
    assert!(exercised >= 30, "exercised on {exercised} live modules");
}

/// The residual `JSON_TEXT_ADMIT_WHAT_THE_BINARY_READER_REFUSES` states, on
/// the must-refuse row: the JSON twin of
/// `refuse/body_gate_omitted_at_contract_surface` decodes (no wire version,
/// so no producer rule), is the same module the tMBC would have been, and is
/// then refused by the codegen admission under trust-cg's DEFAULT policy
/// (which refuses claim-less bodies, roadmap WS7.5 / DG-73, as the manifest's
/// `validate_module_for_codegen=Validation:UnlicensedBodyForCodegen` does) and
/// under an explicit `Refuse`; only an explicit, grandfathering `Permit`
/// makes the strict adapter admit it.
#[test]
fn json_twin_of_the_producer_omission_row_is_refused_unless_explicitly_permitted() {
    use trust_cg_codegen::strict_adapter::translate_core_module_for_target_with_validation_and_license;
    use trust_cg_codegen::target::TargetSpec;

    let dir = refuse::fixtures_dir();
    let row = "body_gate_omitted_at_contract_surface";
    let tmbc = fs::read(dir.join(format!("{row}.tmbc"))).expect("row bytes");
    let refusal = pipeline::load_module_from_bytes(&tmbc).expect_err("tMBC refused");
    assert!(refusal.to_string().contains(PRODUCER_OMISSION), "{refusal}");
    let json = pipeline::load_module_as(&dir.join(format!("{row}.json")), FormatMode::Json)
        .expect("the JSON twin decodes");
    assert_eq!(
        json,
        trust_ir::binary::deserialize_module(&tmbc).expect("trust-ir's plain reader"),
        "the JSON twin is the tMBC's module"
    );
    let triple = json
        .target_info
        .as_ref()
        .map_or("aarch64-apple-darwin", |t| t.triple.as_str());
    let spec = TargetSpec::parse(triple).expect("target");
    let permit = translate_core_module_for_target_with_validation_and_license(
        &json,
        spec,
        &license_for_the_run().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    );
    assert!(
        permit.is_ok(),
        "under an explicit Permit the strict adapter admits the JSON twin: {:?}",
        permit.err().map(|e| e.to_string())
    );
    for (what, license) in [
        ("the default policy", license_for_the_run()),
        (
            "an explicit Refuse",
            license_for_the_run().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Refuse),
        ),
    ] {
        let refuse =
            translate_core_module_for_target_with_validation_and_license(&json, spec, &license)
                .expect_err("a refusing policy refuses the claim-less body");
        assert!(
            refuse.to_string().to_lowercase().contains("licens"),
            "{what}: refused by the license layer, by name: {refuse}"
        );
    }
}
