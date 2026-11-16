// trust-cg-codegen/tests/must_refuse_corpus.rs — trust-ir's must-refuse corpus,
// run through THIS backend's real admission paths (KIND 4 part 2, 2026-09-24).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir ships, at the pinned revision, a corpus of WIRE ARTIFACTS a
//! conforming consumer must REFUSE (`trust_ir_conformance::refuse`,
//! `crates/trust-ir-conformance/tests/fixtures/refuse/MANIFEST.tsv`): modules
//! a named trust-ir entry point refuses, modules that are well-formed by every
//! trust-ir rule and that a native backend must STILL refuse (the obligations
//! the format states in prose — `Unclassified` struct passing beside a
//! by-value aggregate call, `RegionHavocStore`, an unrecorded narrow argument
//! extension on Darwin, ...), and poisoned byte strings the binary reader must
//! refuse — plus ONE `control` row, the envelope every module row shares with
//! no subject, which a conforming consumer must ACCEPT.
//!
//! This target drives EVERY artifact row through trust-cg's own entry points.
//! It never calls trust-ir's validator as the admission, which would say
//! nothing about trust-cg:
//!
//! | lane              | trust-cg entry point                                                         |
//! |-------------------|------------------------------------------------------------------------------|
//! | `decode`          | `pipeline::load_module_from_bytes` — the reader behind `load_module_as`, the CLI's file entry, and every in-process byte entry |
//! | `strict-adapter`  | `strict_adapter::translate_core_module_for_target_with_validation_and_license` |
//! | `aot-compiler`    | `Compiler::new_for_target_spec(..).with_codegen_license(..).compile(..)` — the CLI's `compile_one`, in process |
//! | `compile-service` | `CompileService::compile_plan` with an `Object` artifact                     |
//! | `wasm-module`     | `wasm::compile_module_with_license` — the closed wasm32 module               |
//! | `wasm-object`     | `wasm::compile_object_with_license` — the relocatable wasm32 object (the bridge's entry) |
//! | `host-jit`        | `Compiler::new_for_target_spec(CompilerConfig::for_host_jit(), host).with_codegen_license(..).compile_module_to_jit(..)` (AArch64 macOS hosts only) |
//!
//! Every lane FIRST decodes the row's bytes through trust-cg's reader — a
//! `bytes` row is refused there and never reaches a compiler, exactly as a
//! poisoned `.tmbc` never reaches one from the CLI — then admits the decoded
//! module for the target the module declares (`TargetInfo.triple`; the
//! corpus's canonical `aarch64-apple-darwin` when it declares none). A target
//! this backend cannot name (`i686-unknown-linux-gnu`) is a refusal at
//! `TargetSpec::parse`, the same refusal the CLI's `--target` gives.
//!
//! The two wasm lanes admit every row RETARGETED to wasm32
//! ([`retarget_to_wasm32`]): a row that declares no target or the canonical
//! one takes the wasm32 machine shape and keeps its `struct_passing` claim
//! (a producer fact several rows are about); a row pinned to another target
//! stays pinned and is refused as such. The control row, retargeted the same
//! way, must compile on both, so a wasm refusal is the row's subject and not
//! the retargeting. Both wasm entries compile at the lane's default level, O2,
//! so the trust-ir mid-end runs on every row the admission accepts (and its
//! output passes the same admission again before it is lowered): no mid-end
//! rewrite can make a refused row compile, since a refused row never reaches
//! the mid-end.
//!
//! The `host-jit` lane is the other exception, because a JIT cannot cross compile:
//! it compiles for the HOST, as every JIT consumer does, and takes no target
//! from the module (it is compiled only on the corpus's canonical host,
//! `aarch64-apple-darwin`). Every bodyless `External` declaration is bound to
//! a host address the compiled code never calls, so an unresolved symbol is
//! never what refuses a row. This is the lane a consumer's in-process JIT
//! reaches (ty's typed-host lane is exactly this call).
//!
//! # The runner is reason-blind; the control row and one negative check bound it
//!
//! `Report::run` sees `Ok`/`Err` only. Every non-license module row wears
//! `Gated { authority: STRUCTURAL_LICENSE_AUTHORITY }`, an authority in no
//! consumer's default recognized set, so a lane run under the production
//! policy would refuse most rows as an unrecognized gate authority before
//! their subject is reached — and a refuse-everything lane would "pass". Each
//! lane therefore recognizes that authority FOR THIS RUN (a test-time
//! decision that licenses nothing in production), the `control` row must be
//! ACCEPTED by every lane (this target's own per-lane assertions fail by
//! name otherwise), and NO refusal message may name that authority. What this does
//! not close: a row can still be refused for a reason other than its subject
//! (a lane that lowers no `Vector` type would refuse
//! `struct_passing_unclassified_vector_by_value` for the wrong reason); the
//! [`EXPECTED_REASON`] table pins the reason text for
//! every row whose refusal this crate owns, so that a refusal drifting to
//! another arm fails here by name.
//!
//! # Known-accepted rows are named, reasoned, and EXACT
//!
//! A lane's [`Lane::known_accepted`] entries name the rows that lane accepts today
//! with the reason. The list is exact in both directions: a must-refuse row
//! accepted and NOT listed fails (the finding the corpus exists to surface),
//! and a listed row that is now refused fails too — delete the line; the list
//! only shrinks. A row the corpus adds at a later pin fails by name through
//! `uncovered`, so a pin bump cannot pass over a new obligation unseen. This
//! is test-rung evidence about trust-cg's refusals, never proof.
//!
//! # Mutation control (recorded; run once at landing)
//!
//! With the `GlobalAsmUnsupported` arm of
//! `reject_unconsumed_v41_target_neutral_surface_with_weak_references`
//! (trust-cg-lower `adapter.rs`) deleted, this target failed on the
//! `strict-adapter`, `aot-compiler` and `compile-service` lanes, each naming
//! `global_asm_block` as ACCEPTED; restoring the arm made it green again. The
//! same run with `Report::run(&rows, |_| Err("refused"))` in place of a lane
//! fails naming `control_licensed_identity` as a REFUSED control.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{self, OptLevel};
use trust_cg_codegen::strict_adapter::translate_core_module_for_target_with_validation_and_license;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    ArtifactKind, CompileGeneration, CompilePlan, CompileRequest, CompileService,
    CompileServiceConfig, CompileStatus, InstallIntent,
};
use trust_cg_lower::CodegenLicensePolicy;
use trust_ir::Module;
use trust_ir_conformance::refuse::{Report, Row, STRUCTURAL_LICENSE_AUTHORITY, corpus};

/// The target every corpus row that declares none is admitted for: the
/// canonical target the corpus is measured on (`refuse_target()` in trust-ir's
/// `tests/generate/refuse.rs`).
const CANONICAL_TARGET: &str = "aarch64-apple-darwin";

/// One lane: a named trust-cg entry point, driven over every row.
struct Lane {
    name: &'static str,
    admit: fn(&Row) -> Result<(), String>,
    /// Must-refuse rows this lane ACCEPTS today, each with the reason. Exact:
    /// see the module docs.
    known_accepted: &'static [(&'static str, &'static str)],
}

/// Rows whose refusal this crate owns, with the text the refusing arm spells:
/// `(row, lane, substring)`, where `lane` is a lane name, `"*"` (every
/// compiler lane), `"native"` (the three native compiler lanes), `"wasm"`
/// (both wasm lanes) or `"ingest"` (every lane behind the WS7.3 ingestion
/// admission, `trust_cg_lower::admit_module`: every compiler lane but the
/// strict adapter, a raw Core-lane diagnostic entry that `ingest_admission.rs`
/// lists as such). A refusal that stops containing the text
/// has drifted to another arm (or to the license layer) and fails here by
/// name. Not every row is listed — a row a lower layer refuses for its own
/// named reason (an unsupported type, a missing func type, ...) is pinned
/// only by the exactness of [`Lane::known_accepted`].
const EXPECTED_REASON: &[(&str, &str, &str)] = &[
    (
        "binding_frame_closed_edge",
        "strict-adapter",
        "binding frame %1 is used after close_frame on the same path",
    ),
    // The reader (every lane decodes through it first).
    (
        "body_gate_omitted_at_contract_surface",
        "decode",
        "producer omission",
    ),
    (
        "body_gate_omitted_at_contract_surface",
        "*",
        "producer omission",
    ),
    // A level-S template blob (amendment S) is refused by its magic, by name,
    // never by falling through to another format's parser.
    (
        "template_blob_is_not_a_module",
        "decode",
        pipeline::TEMPLATE_IS_NOT_A_MODULE,
    ),
    (
        "template_blob_is_not_a_module",
        "*",
        pipeline::TEMPLATE_IS_NOT_A_MODULE,
    ),
    // trust-cg-lower's own license layer.
    ("body_gate_ungated", "*", "affirmatively ungated"),
    // trust-ir's codegen admission, run by `validate_codegen_prerequisites`
    // as a NAMED ratchet (these variants are consumed by name; the residual
    // is stated there).
    (
        "body_gate_kernel_tv_without_certificate",
        "*",
        "without the evidence it names",
    ),
    // trust-ir v61 license evidence, refused on every lane in the same
    // admission layer: a PRESENT `GateEvidence` naming another body's digest
    // is trust-ir's `GatedEvidenceMismatch`, consumed by name; an
    // evidence-bound license with NONE is this backend's `UnevidencedGate`
    // (`refuse_unevidenced_gates`, decision record OD-V61-GATE-EVIDENCE-20261014).
    (
        "body_gate_evidence_stale_body_digest",
        "*",
        "GateEvidence does not hold",
    ),
    (
        "body_gate_kernel_tv_evidence_unrecorded",
        "*",
        "evidence-bound gate authority \"clean-kernel-tv\" with no GateEvidence",
    ),
    (
        "body_gate_refuted_by_failed_tv",
        "strict-adapter",
        "revokes the license",
    ),
    (
        "body_gate_refuted_by_failed_tv",
        "aot-compiler",
        "revokes the license",
    ),
    // The service's verifier preflight (`first_verifier_rejection`) runs
    // before lowering and refuses the same `Failed` row first.
    (
        "body_gate_refuted_by_failed_tv",
        "compile-service",
        "provenance assumptions",
    ),
    // The wasm lanes run the same admission (`validate_codegen_prerequisites`)
    // and have no verifier preflight in front of it.
    (
        "body_gate_refuted_by_failed_tv",
        "wasm",
        "revokes the license",
    ),
    ("tainted_value_reaches_sink", "*", "trusted sink"),
    // v59 effect-frame coverage is consumed from the shared validator, not
    // erased or refused for an unrelated ABI/license reason.
    (
        "effect_summary_uncovered_write",
        "*",
        "declares an effect summary that does not cover its body",
    ),
    // Two rows the trust-ir 5c4f9e1d pin brought (236214d69), each refused by
    // its named arm of `validate_codegen_prerequisites`: a Rust-stamped
    // borrow permission instruction on every lane, and a pointer-width
    // constant outside the target's width on the wasm lanes (the row is a
    // wasm32 module, so the native lanes refuse its target first, as they
    // refuse `enum_tag_lane_off_scalar_table`'s below).
    (
        "rust_reference_as_permission_borrow",
        "*",
        "never as a permission instruction",
    ),
    (
        "const_usize_beyond_target_width",
        "wasm",
        "const type mismatch: expected usize",
    ),
    (
        "const_usize_beyond_target_width",
        "native",
        "this backend has no such target",
    ),
    (
        "custom_obligation_unpinned_namespace",
        "*",
        "ObligationKind::Custom",
    ),
    (
        "certified_with_empty_kernel_term",
        "*",
        "no CleanCic certificate",
    ),
    (
        "source_provenance_stale_body_digest",
        "*",
        "invalid source provenance",
    ),
    ("duplicate_enum_id", "*", "duplicate enum id"),
    // trust-ir v55 (amendment D): a registered drop glue reached by a direct
    // call, refused by trust-ir's own verdict (`validate_codegen_prerequisites`).
    (
        "drop_glue_called_directly",
        "*",
        "not the one spelling of a drop",
    ),
    (
        "formula_smtlib_rendering_disagrees",
        "*",
        "formula states two SMT-LIB texts",
    ),
    (
        "summary_clause_smtlib_rendering_disagrees",
        "*",
        "formula states two SMT-LIB texts",
    ),
    (
        "spec_carrier_smtlib_rendering_disagrees",
        "*",
        "formula states two SMT-LIB texts",
    ),
    // trust-cg-lower's v41/v45 surface floors.
    ("global_asm_block", "*", "global_asm!"),
    (
        "assert_panic_kind_unspecified",
        "*",
        "unspecified panic kind",
    ),
    ("target_feature_unknown", "*", "target feature"),
    (
        "struct_passing_unclassified_by_value_aggregate",
        "*",
        "unclassified",
    ),
    // trust-ir SPEC_RATIFICATIONS §17: the Unclassified gate reads trust-ir's
    // ONE by-value-aggregate-slot predicate (`is_by_value_aggregate_slot`),
    // so a refined aggregate, a vector and a closure are aggregate slots too.
    (
        "struct_passing_unclassified_refined_aggregate",
        "*",
        "unclassified",
    ),
    (
        "struct_passing_unclassified_vector_by_value",
        "*",
        "unclassified",
    ),
    (
        "struct_passing_unclassified_closure_by_value",
        "*",
        "unclassified",
    ),
    // §17 AlwaysMemory: trust-ir's validator refuses the by-value slot; this
    // backend refuses every AlwaysMemory module first (a capability choice:
    // it consumes no pre-lowered `byval` spelling).
    (
        "struct_passing_always_memory_by_value_aggregate",
        "*",
        "AlwaysMemory",
    ),
    // §17 NativeC: a recorded placement fact is a second statement this
    // backend cannot establish agreement with, so it refuses every one.
    (
        "struct_passing_native_c_pass_mode_contradicts_target",
        "*",
        "ParamAttrs.pass",
    ),
    (
        "pred_citation_rendering_disagrees",
        "*",
        "formula states two SMT-LIB texts",
    ),
    (
        "narrow_arg_ext_unrecorded_darwin",
        "*",
        "no recorded argument extension",
    ),
    // The instruction translator.
    ("region_havoc_store", "*", "RegionHavocStore"),
    // The borrow / binding-frame / Undef legalization stage
    // (`trust_cg_lower::borrow_frame_undef`), which refuses a marked undef by
    // construction before its narrowing `Assume` or its return is reached.
    (
        "undef_fresh_havoc_feeds_assume",
        "*",
        "FreshSymbolicHavoc-marked undef",
    ),
    // G18-1 (re-decided 2026-09-27): every `Dealloc` is refused for codegen
    // in every body, by trust-ir's own verdict (`validate_codegen_prerequisites`
    // consumes `UnlowerableForCodegen { inst: "Dealloc" }` by name) and by the
    // instruction arm behind it; no provenance analysis remains to lower one.
    ("dealloc_instruction", "*", "[TCG-DEALLOC]"),
    ("dealloc_instruction", "*", "UnlowerableForCodegen"),
    // IR 8e81e98a retired vector_unsigned_cmp_bytes_x86 after publishing all
    // four byte-vector unsigned cells available; no known-accepted exception.
    // trust-cg-lower `sequence_layout`: a sequence PARAMETER lowers as the
    // image pointer, so the row is refused at its subject, the element op,
    // by trust-ir's own verdict (never by the parameter's type).
    ("sequence_element_op", "native", "UnlowerableForCodegen"),
    // The wasm lanes refuse the subject itself, the element op, by the same
    // trust-ir verdict, at the WS7.3 ingestion admission
    // (`codegen_lowerability_errors`), before the lane's own capability
    // refusal of the `Sequence` type ("no wasm32 carrier") is reached.
    (
        "sequence_element_op",
        "wasm",
        "UnlowerableForCodegen: function 0 ('first') bb0: `ExtractElement`",
    ),
    // The instruction translator's operand-type admission, which the wasm
    // lane's body scan (`reject_unmodeled_body_constructs`) mirrors.
    ("array_splat_non_array_type", "*", "InvalidArraySplat"),
    // SPEC_RATIFICATIONS §3.3: source cases use the selector's type,
    // never a signedness-agnostic residue at its carrier width.
    (
        "switch_case_negative_at_unsigned",
        "*",
        "const type mismatch",
    ),
    ("switch_case_above_signed_max", "*", "const type mismatch"),
    // A `PtrData` over a non-pointer: trust-ir's own structural finding,
    // `PointerOpInvalid` (whose docs name this row), on every lane behind the
    // WS7.3 ingestion admission; the strict adapter, which runs none, reaches
    // the instruction translator's operand admission.
    (
        "ptr_data_of_non_pointer",
        "ingest",
        "PointerOpInvalid: bb0: ptr_data cannot use pointer type i32: type is not pointer-like",
    ),
    (
        "ptr_data_of_non_pointer",
        "strict-adapter",
        "requires a pointer-like type",
    ),
    // A proved summary `backed_by` an import row this entry cannot
    // authenticate: refused at its subject, trust-ir's authority-tier
    // `UnauthenticatedImport`, on every lane behind the ingestion admission
    // (which validates under the authority tier's import policy). The strict
    // adapter accepts the row (`STRICT_ADAPTER_ACCEPTS`).
    (
        "import_backed_summary_unauthenticated",
        "ingest",
        "UnauthenticatedImport: import #0 (backed_by)",
    ),
    ("unop_not_scalar_bool", "wasm", "UnOpNotOnScalarBool"),
    // A row pinned to a target the lane does not lower stays pinned.
    (
        "enum_tag_lane_off_scalar_table",
        "native",
        "this backend has no such target",
    ),
    (
        "enum_tag_lane_off_scalar_table",
        "wasm",
        "is not a wasm32 triple",
    ),
    // The object lane binds the declaration as an undefined symbol and then
    // reaches the definition's convention; the closed module refuses the
    // declaration first (unbound under the closed policy). The lane judges a
    // definition's own signature before its body (`function_memory_use`), so
    // the convention is refused before the definition's `Invoke` reaches the
    // unwired-EH scan.
    ("calling_conv_c_unwind_definition", "wasm-object", "CUnwind"),
    // trust-ir v74 `Inst::BoxDeref` (the pinned Box validity
    // lane, not a landed pin). Every row is refused on every lane by the
    // instruction's own verdict: a fact rule trust-ir names, the tier floor
    // (the default license admits no premise tier; the policy-free funnels
    // hold the assumed roots to `named_premise` before it), or the reader.
    (
        "box_deref_premise_tier",
        "*",
        "backed at tier named_premise",
    ),
    (
        "box_deref_assumed_root_tier",
        "*",
        "backed at tier assumed_root_premise",
    ),
    ("box_deref_operand_not_ptr", "*", "BoxDerefTypeMismatch"),
    (
        "box_deref_pointee_zero_sized",
        "*",
        "BoxDerefPointeeOutOfScope",
    ),
    (
        "box_deref_pointee_uninhabited",
        "*",
        "BoxDerefPointeeOutOfScope",
    ),
    ("box_deref_conjunct_missing", "*", "BoxDerefConjunctCover"),
    (
        "box_deref_conjunct_duplicated",
        "*",
        "BoxDerefConjunctCover",
    ),
    (
        "box_deref_conjunct_misordered",
        "*",
        "BoxDerefConjunctCover",
    ),
    (
        "box_deref_metadata_valid_on_sized",
        "*",
        "BoxDerefConjunctCover",
    ),
    (
        "box_deref_premise_standing_dropped",
        "*",
        "BoxDerefPremiseNotPinned",
    ),
    ("box_deref_session_fallback", "*", "BoxDerefSessionRefused"),
    ("box_deref_session_not_proof", "*", "BoxDerefSessionRefused"),
    (
        "box_deref_check_pinned_shape",
        "*",
        "BoxDerefDominatingCheckInvalid",
    ),
    (
        "box_deref_check_address_round_trip",
        "*",
        "BoxDerefDominatingCheckInvalid",
    ),
    (
        "box_deref_check_for_dereferenceable",
        "*",
        "BoxDerefDominatingCheckInvalid",
    ),
    (
        "box_deref_check_wrong_alignment",
        "*",
        "BoxDerefDominatingCheckInvalid",
    ),
    (
        "box_deref_check_absent",
        "*",
        "BoxDerefDominatingCheckInvalid",
    ),
    (
        "box_deref_check_not_dominating",
        "*",
        "BoxDerefDominatingCheckInvalid",
    ),
    (
        "box_deref_check_on_operand",
        "*",
        "BoxDerefDominatingCheckInvalid",
    ),
    (
        "box_deref_obligation_missing",
        "*",
        "BoxDerefObligationUnbound",
    ),
    (
        "box_deref_obligation_wrong_kind",
        "*",
        "BoxDerefObligationUnbound",
    ),
    (
        "box_deref_obligation_wrong_function",
        "*",
        "BoxDerefObligationUnbound",
    ),
    (
        "box_deref_obligation_wrong_site",
        "*",
        "BoxDerefObligationUnbound",
    ),
    (
        "box_deref_obligation_not_replayed",
        "*",
        "BoxDerefObligationUnbound",
    ),
    (
        "box_deref_non_claim_dropped",
        "*",
        "BoxDerefNonClaimsNotPinned",
    ),
    (
        "box_deref_premise_null_operand",
        "*",
        "BoxDerefPremiseContradicted",
    ),
    (
        "box_deref_premise_inttoptr_operand",
        "*",
        "BoxDerefPremiseContradicted",
    ),
    (
        "box_deref_premise_param_root_without_parameter",
        "*",
        "BoxDerefPremiseContradicted",
    ),
    (
        "box_deref_premise_alloc_root_without_allocation",
        "*",
        "BoxDerefPremiseContradicted",
    ),
    (
        "box_deref_premise_freed_operand",
        "*",
        "BoxDerefPremiseContradicted",
    ),
    (
        "box_deref_premise_mixed_roots",
        "*",
        "BoxDerefPremiseContradicted",
    ),
    ("blob_box_deref_below_its_version", "*", "invalid tag: 77"),
    ("blob_box_deref_premise_root_unknown", "*", "invalid tag: 9"),
];

/// Whether an [`EXPECTED_REASON`] lane spec covers `lane`.
fn reason_applies(spec: &str, lane: &str) -> bool {
    match spec {
        "*" => lane != "decode",
        "native" => matches!(lane, "strict-adapter" | "aot-compiler" | "compile-service"),
        "wasm" => matches!(lane, "wasm-module" | "wasm-object"),
        "ingest" => matches!(
            lane,
            "aot-compiler" | "compile-service" | "wasm-module" | "wasm-object" | "host-jit"
        ),
        exact => exact == lane,
    }
}

/// Must-refuse rows every compiler lane ACCEPTS today, with the reason. Each
/// is a construct this backend observes and deliberately admits; none is
/// unobservable. Exact per lane (see the module docs).
const COMPILER_LANES_ACCEPT: &[(&str, &str)] = &[
    (
        "completeness_unclaimed",
        "this backend needs no completeness claim: it lowers exactly the definitions present and \
         a bodyless declaration is an undefined symbol the LINK resolves or refuses. `None` is \
         no claim (never read as Complete); every `Some` is refused by name \
         (`ModuleCompletenessUnsupported`), so a claim is never erased. The row's obligation \
         binds a consumer that needs a complete module, which this is not.",
    ),
    (
        "trusted_status_row",
        "this backend takes no codegen decision from an obligation's status: \
         `obligation_surface_floor` consumes `status` only to refuse an unrecognized KIND that \
         claims completion, guards bind to an obligation only through an explicit `ProofRef` \
         (`node_obligation_id`) and the kernel keeps a guard whose obligation is unbound, so a \
         `Trusted` row is never read as kernel-checked here. Refusing every module carrying one \
         would refuse real producer output the zero-Trusted census governs on the trust-ir side \
         (`trust-ir validate --forbid-trusted`), not a codegen fact.",
    ),
];

/// [`COMPILER_LANES_ACCEPT`] plus the rows only the strict adapter accepts.
const STRICT_ADAPTER_ACCEPTS: &[(&str, &str)] = &[
    (
        "import_backed_summary_unauthenticated",
        "a `FunctionSummary.backed_by` is contract data this backend takes no codegen decision \
         from (`function_surface_floor` classifies `summary` as consumed-inert; no emitted byte \
         depends on it), and the row's refusal lives at trust-ir's AUTHORITY-tier entry \
         (`validate_module_with_authority`), for a consumer that would draw authority from the \
         import. The strict adapter is a raw Core-lane diagnostic entry that runs no ingestion \
         admission (`ingest_admission.rs`); every lane behind the WS7.3 ingestion admission \
         validates under the authority tier's import policy and refuses the row at its subject, \
         `UnauthenticatedImport` (pinned in EXPECTED_REASON).",
    ),
    ("completeness_unclaimed", "see COMPILER_LANES_ACCEPT"),
    ("trusted_status_row", "see COMPILER_LANES_ACCEPT"),
];

/// Module rows the reader itself refuses, so they are not "accepted at
/// decode" like every other module row (see `DECODE_ACCEPTS_EVERY_MODULE_ROW`).
const DECODE_REFUSES: &[(&str, &str)] = &[(
    "body_gate_omitted_at_contract_surface",
    "the reader holds the producer to the header version it declared: a v41+ blob with a \
     bodied, claim-less function is a producer omission, refused as \
     `PipelineError::ProducerOmittedBodyGate` before any policy can grandfather it",
)];

fn license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_recognized_authority(STRUCTURAL_LICENSE_AUTHORITY)
}

/// The target the row declares, or the canonical one. A triple this backend
/// cannot spell is a refusal, the same one `trust-cg --target` gives.
fn target_spec_for(module: &Module) -> Result<TargetSpec, String> {
    let triple = module
        .target_info
        .as_ref()
        .map_or(CANONICAL_TARGET, |t| t.triple.as_str());
    TargetSpec::parse(triple)
        .map_err(|error| format!("target `{triple}`: this backend has no such target: {error:?}"))
}

/// trust-cg's own reader over the bytes a `.tmbc` file holds.
fn decode(row: &Row) -> Result<Module, String> {
    pipeline::load_module_from_bytes(row.wire_bytes()).map_err(|e| format!("decode: {e}"))
}

fn lane_decode(row: &Row) -> Result<(), String> {
    decode(row).map(|_| ())
}

fn lane_strict_adapter(row: &Row) -> Result<(), String> {
    let module = decode(row)?;
    let spec = target_spec_for(&module)?;
    translate_core_module_for_target_with_validation_and_license(&module, spec, &license())
        .map(|_| ())
        .map_err(|e| format!("strict adapter: {e}"))
}

fn lane_aot_compiler(row: &Row) -> Result<(), String> {
    let module = decode(row)?;
    let spec = target_spec_for(&module)?;
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(license())
    .compile(&module)
    .map(|_| ())
    .map_err(|e| format!("aot compiler: {e}"))
}

fn lane_compile_service(row: &Row) -> Result<(), String> {
    let module = decode(row)?;
    let spec = target_spec_for(&module)?;
    let service = CompileService::new(CompileServiceConfig {
        codegen_license: license(),
        ..CompileServiceConfig::default()
    });
    let mut request = CompileRequest::new(row.id(), CompileGeneration::new(1));
    request.artifact_kind = ArtifactKind::Object;
    request.install_intent = InstallIntent::CompileOnly;
    let response = service.compile_plan(CompilePlan::new(request, spec), &module);
    if response.status == CompileStatus::Compiled {
        return Ok(());
    }
    let mut message = format!("compile service: {:?}", response.status);
    for diagnostic in &response.diagnostics {
        let _ = write!(message, "; [{}] {}", diagnostic.code, diagnostic.message);
    }
    Err(message)
}

/// The row's module, read by trust-cg's reader, retargeted to wasm32 the way
/// the corpus allows. A row that declares no target, or the corpus's
/// canonical one, is target-neutral by construction (the shared envelope is
/// pinned to the canonical target): it takes the wasm32 machine shape and
/// KEEPS its `struct_passing` claim, which is a producer fact several rows
/// are about. A row pinned to another target is about that target and is
/// left pinned, so the wasm lanes refuse it as such, as the native lanes
/// refuse a triple they cannot name.
fn wasm_retargeted(row: &Row) -> Result<Module, String> {
    let module = decode(row)?;
    Ok(retarget_to_wasm32(module))
}

fn retarget_to_wasm32(mut module: Module) -> Module {
    let wasm32 = trust_cg_codegen::wasm::wasm32_target_info();
    module.target_info = match module.target_info.take() {
        None => Some(wasm32),
        Some(info) if info.triple == CANONICAL_TARGET => Some(trust_ir::TargetInfo {
            struct_passing: info.struct_passing,
            ..wasm32
        }),
        pinned => pinned,
    };
    module
}

fn lane_wasm_module(row: &Row) -> Result<(), String> {
    let module = wasm_retargeted(row)?;
    trust_cg_codegen::wasm::compile_module_with_license(&module, &license())
        .map(drop)
        .map_err(|e| format!("wasm module: {e}"))
}

fn lane_wasm_object(row: &Row) -> Result<(), String> {
    let module = wasm_retargeted(row)?;
    trust_cg_codegen::wasm::compile_object_with_license(&module, &license())
        .map(drop)
        .map_err(|e| format!("wasm object: {e}"))
}

/// The host JIT (`compile_module_to_jit`), on the corpus's canonical host
/// only: a JIT compiles for the process it runs in.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn lane_host_jit(row: &Row) -> Result<(), String> {
    extern "C" fn never_called() {}
    let module = decode(row)?;
    let host = trust_cg_codegen::CoreHostJitTarget::detect()
        .expect("the canonical host is a JIT host")
        .target_spec();
    // Every bodyless `External` declaration resolves (the envelope a JIT
    // consumer supplies: ty binds exactly these), so an unresolved symbol is
    // never what refuses a row.
    let declarations: std::collections::HashMap<String, *const u8> = module
        .functions
        .iter()
        .filter(|function| {
            function.is_declaration() && matches!(function.linkage, trust_ir::Linkage::External)
        })
        .map(|function| (function.name.clone(), never_called as *const u8))
        .collect();
    Compiler::new_for_target_spec(CompilerConfig::for_host_jit(), host)
        .with_codegen_license(license())
        .compile_module_to_jit(&module, &declarations)
        .map(|_| ())
        .map_err(|e| format!("host jit: {e}"))
}

const LANES: &[Lane] = &[
    Lane {
        name: "decode",
        admit: lane_decode,
        // The reader decodes every `module` row by construction (the corpus
        // pins that trust-ir's reader does); what it must refuse is the
        // `bytes` rows. A module row is therefore ACCEPTED here and refused
        // downstream, which the three compiler lanes below pin; the reason is
        // the same for every module row and is stated once.
        known_accepted: DECODE_ACCEPTS_EVERY_MODULE_ROW,
    },
    Lane {
        name: "strict-adapter",
        admit: lane_strict_adapter,
        known_accepted: STRICT_ADAPTER_ACCEPTS,
    },
    Lane {
        name: "aot-compiler",
        admit: lane_aot_compiler,
        known_accepted: COMPILER_LANES_ACCEPT,
    },
    Lane {
        name: "compile-service",
        admit: lane_compile_service,
        known_accepted: COMPILER_LANES_ACCEPT,
    },
    Lane {
        name: "wasm-module",
        admit: lane_wasm_module,
        known_accepted: COMPILER_LANES_ACCEPT,
    },
    Lane {
        name: "wasm-object",
        admit: lane_wasm_object,
        known_accepted: COMPILER_LANES_ACCEPT,
    },
    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    Lane {
        name: "host-jit",
        admit: lane_host_jit,
        known_accepted: COMPILER_LANES_ACCEPT,
    },
];

/// Every `module` row: the decode lane accepts them all (see `LANES`).
const DECODE_ACCEPTS_EVERY_MODULE_ROW: &[(&str, &str)] = &[(
    "*module*",
    "a `module` row decodes by construction; the reader's obligation is the `bytes` rows",
)];

fn known_accepted_ids<'a>(lane: &Lane, rows: &'a [Row]) -> BTreeSet<&'a str> {
    let mut out = BTreeSet::new();
    for (id, _reason) in lane.known_accepted {
        if *id == "*module*" {
            out.extend(
                rows.iter()
                    .filter(|row| row.module().is_some() && !row.is_control())
                    .filter(|row| {
                        !DECODE_REFUSES
                            .iter()
                            .any(|(refused, _)| *refused == row.id())
                    })
                    .map(Row::id),
            );
        } else {
            let row = rows.iter().find(|row| row.id() == *id).unwrap_or_else(|| {
                panic!(
                    "{}: KNOWN_ACCEPTED names `{id}`, which is not a corpus row (a row \
                         retired at the pin? delete the line)",
                    lane.name
                )
            });
            assert!(
                row.manifest.must_refuse(),
                "{}: KNOWN_ACCEPTED names `{id}`, which is not a must-refuse row",
                lane.name
            );
            out.insert(row.id());
        }
    }
    out
}

#[test]
fn every_must_refuse_row_is_refused_by_every_trust_cg_admission_lane() {
    let rows =
        corpus().expect("the pinned must-refuse corpus loads (a vacuous one is a typed error)");
    assert!(!rows.is_empty(), "the corpus is not empty");
    let handled: Vec<&str> = rows.iter().map(Row::id).collect();
    assert!(
        rows.uncovered(&handled).is_empty(),
        "rows not dispatched: {:?}",
        rows.uncovered(&handled)
    );

    let mut failures: Vec<String> = Vec::new();
    // Every reason pin names a row of the PINNED corpus. A row retired at a
    // pin move leaves its pins behind, and each would otherwise read below as
    // "accepted"; name it as what it is, once, instead.
    let retired: BTreeSet<&str> = EXPECTED_REASON
        .iter()
        .map(|(id, _, _)| *id)
        .filter(|id| !rows.iter().any(|row| row.id() == *id))
        .collect();
    for id in &retired {
        failures.push(format!(
            "EXPECTED_REASON names `{id}`, which is not a corpus row at the pinned trust-ir \
             (retired at the pin? delete its lines)"
        ));
    }
    for lane in LANES {
        let report = Report::run(&rows, lane.admit);
        for (id, outcome) in report.outcomes() {
            eprintln!("{}: {id}: {outcome:?}", lane.name);
        }
        // The control row (the shared envelope) is accepted, or nothing in
        // this lane's report is attributable to any row's subject.
        for id in report.controls_refused(&rows) {
            failures.push(format!(
                "{}: control row `{id}` REFUSED: {}",
                lane.name,
                report.message(id).unwrap_or("")
            ));
        }
        for id in report.uncovered(&rows) {
            failures.push(format!("{}: row `{id}` not dispatched", lane.name));
        }
        // No refusal is the license layer's: the run recognized the
        // structural authority, so a message naming it means the lane did not.
        for id in report.refused() {
            let message = report.message(id).unwrap_or("");
            if message.contains(STRUCTURAL_LICENSE_AUTHORITY) {
                failures.push(format!(
                    "{}: `{id}` refused by the license layer, not its subject: {message}",
                    lane.name
                ));
            }
        }
        // Exact known-accepted set.
        let accepted: BTreeSet<&str> = report.must_refuse_accepted(&rows).into_iter().collect();
        let known = known_accepted_ids(lane, &rows);
        for id in accepted.difference(&known) {
            let why = rows
                .iter()
                .find(|row| row.id() == *id)
                .map(|row| row.manifest.why.as_str())
                .unwrap_or("");
            failures.push(format!(
                "{}: must-refuse row `{id}` ACCEPTED (trust-ir: {why}). Refuse it by a typed \
                 error, or list it in this lane's KNOWN_ACCEPTED with the reason.",
                lane.name
            ));
        }
        for id in known.difference(&accepted) {
            failures.push(format!(
                "{}: `{id}` is listed KNOWN_ACCEPTED but is now refused ({}): delete its line — \
                 the list only shrinks",
                lane.name,
                report.message(id).unwrap_or("")
            ));
        }
        // Reason pins for the refusals this crate owns (lane specs: see
        // `reason_applies`); the reader is named explicitly.
        for (id, lane_name, needle) in EXPECTED_REASON {
            if !reason_applies(lane_name, lane.name) || retired.contains(id) {
                continue;
            }
            match report.message(id) {
                Some(message) if message.contains(needle) => {}
                Some(message) => failures.push(format!(
                    "{}: `{id}` refused, but not by the arm that spells `{needle}`: {message}",
                    lane.name
                )),
                None => failures.push(format!(
                    "{}: `{id}` expected refused with `{needle}` but was accepted",
                    lane.name
                )),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "must-refuse corpus ({} rows, {} lanes): {} finding(s)\n  {}",
        rows.len(),
        LANES.len(),
        failures.len(),
        failures.join("\n  ")
    );
}

/// The reason-blind trap, demonstrated on the real corpus: a lane that
/// refuses everything is named by the control row, and a lane that accepts
/// everything is named by every must-refuse row.
#[test]
fn the_control_row_bounds_a_refuse_everything_lane() {
    let rows = corpus().expect("the pinned must-refuse corpus loads");
    let report = Report::run(&rows, |_| Err::<(), _>("unsupported"));
    assert_eq!(
        report.controls_refused(&rows),
        ["control_licensed_identity"]
    );
    let report = Report::run(&rows, |_| Ok::<(), String>(()));
    assert_eq!(
        report.must_refuse_accepted(&rows).len(),
        rows.iter().filter(|r| r.manifest.must_refuse()).count()
    );
    assert!(report.controls_refused(&rows).is_empty());
}

/// The wasm entries apply the CALLER's codegen-license policy, and every
/// entry that takes none applies the production default — as strict as it
/// was. The control row (the shared envelope, gated by the structural
/// authority no default recognizes) is refused as an unrecognized authority
/// by every default-policy wasm entry, the public single-function one
/// included, and admitted by every `*_license` entry under a policy that
/// recognizes it; a claim-less body is admitted there under
/// `UnlicensedBodyPolicy::Permit` and refused under the default `Refuse`
/// (roadmap WS7.5, DG-73), spelled or not.
#[test]
fn wasm_entries_take_the_callers_license_and_default_to_the_production_policy() {
    use trust_cg_codegen::wasm::{self, WasmModulePolicy};
    use trust_cg_lower::UnlicensedBodyPolicy;

    let rows = corpus().expect("the pinned must-refuse corpus loads");
    let control = rows
        .iter()
        .find(|row| row.is_control())
        .expect("the corpus carries its control row");
    let module = retarget_to_wasm32(decode(control).expect("the control decodes"));
    let closed = WasmModulePolicy::closed();

    let defaults = [
        ("compile_module", wasm::compile_module(&module).map(drop)),
        ("compile_object", wasm::compile_object(&module).map(drop)),
        (
            "compile_module_with_evidence",
            wasm::compile_module_with_evidence(&module).map(drop),
        ),
        (
            "compile_object_with_evidence",
            wasm::compile_object_with_evidence(&module).map(drop),
        ),
        (
            "compile_module_with_policy",
            wasm::compile_module_with_policy(&module, &closed).map(drop),
        ),
        (
            "lower_function",
            wasm::lower_function(
                &mut wasm::WasmModule::new(),
                &module.functions[0],
                &module,
                wasm::WasmFunctionEnv::empty(),
            )
            .map(drop),
        ),
    ];
    for (entry, result) in defaults {
        let error = result
            .map(|()| format!("{entry}: the control ACCEPTED under the default policy"))
            .expect_err("the default policy recognizes no test authority")
            .to_string();
        assert!(
            error.contains("does not recognize") && error.contains(STRUCTURAL_LICENSE_AUTHORITY),
            "{entry}: refused, but not as an unrecognized authority: {error}"
        );
    }

    let admitted = |license: &CodegenLicensePolicy, module: &Module| {
        [
            (
                "compile_module_with_license",
                wasm::compile_module_with_license(module, license).map(drop),
            ),
            (
                "compile_module_with_policy_and_license",
                wasm::compile_module_with_policy_and_license(module, &closed, license).map(drop),
            ),
            (
                "compile_module_with_evidence_policy_and_license",
                wasm::compile_module_with_evidence_policy_and_license(module, &closed, license)
                    .map(drop),
            ),
            (
                "compile_object_with_license",
                wasm::compile_object_with_license(module, license).map(drop),
            ),
            (
                "compile_object_with_evidence_and_license",
                wasm::compile_object_with_evidence_and_license(module, license).map(drop),
            ),
        ]
    };
    for (entry, result) in admitted(&license(), &module) {
        if let Err(error) = result {
            panic!(
                "{entry}: the control REFUSED under a policy recognizing its authority: {error}"
            );
        }
    }

    let mut claim_less = module.clone();
    for function in &mut claim_less.functions {
        function.body_gate = None;
    }
    let permitting = license().with_unlicensed(UnlicensedBodyPolicy::Permit);
    for (entry, result) in admitted(&permitting, &claim_less) {
        if let Err(error) = result {
            panic!("{entry}: a claim-less body REFUSED under `Permit`: {error}");
        }
    }
    for (entry, result) in [
        license(),
        license().with_unlicensed(UnlicensedBodyPolicy::Refuse),
    ]
    .iter()
    .flat_map(|refusing| admitted(refusing, &claim_less))
    {
        let error = result
            .map(|()| format!("{entry}: a claim-less body ACCEPTED under `Refuse`"))
            .expect_err("`Refuse` refuses a claim-less body")
            .to_string();
        assert!(
            error.contains("codegen license refused") && error.contains("no codegen license"),
            "{entry}: refused, but not by the license policy: {error}"
        );
    }
}

/// The production reach of the wasm body and ABI refusals: each row's subject,
/// CLAIM-LESS (every `body_gate` removed), is refused by the wasm entries —
/// the closed module and the object — by the same arm the corpus lanes pin,
/// under a policy that PERMITS claim-less bodies. Before these arms, a
/// claim-less body carrying any of them compiled on both entries; the corpus
/// lanes alone (which recognize the structural authority) would not show that
/// a permitted claim-less body is refused too. The default policy refuses a
/// claim-less body at the license (roadmap WS7.5, DG-73), which would hide
/// the arm, so the entries take `Permit` explicitly.
///
/// Each row names two arms. The module entries run the WS7.3 ingestion
/// admission first, so a subject trust-ir's validator refuses by a typed
/// finding is refused there, in its name (`ptr_data_of_non_pointer`:
/// `PointerOpInvalid`). The public per-function entry
/// (`lower_function_with_license`) runs no ingestion admission and reaches
/// the lane's own floor, which therefore stays pinned here: the first
/// refusal over the row's bodied functions, in module order, names it.
#[test]
fn default_wasm_entries_refuse_the_claim_less_body_and_abi_subjects() {
    use trust_cg_codegen::wasm::{
        WasmFunctionEnv, WasmModule, compile_module_with_license, compile_object_with_license,
        lower_function_with_license,
    };
    let permitting = license().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit);
    let rows = corpus().expect("the pinned must-refuse corpus loads");
    // `(row, module/object entry needle, per-function lane-floor needle)`.
    for (id, needle, floor) in [
        ("region_havoc_store", "RegionHavocStore", "RegionHavocStore"),
        (
            "undef_fresh_havoc_feeds_assume",
            "FreshSymbolicHavoc-marked undef",
            "FreshSymbolicHavoc-marked undef",
        ),
        (
            "array_splat_non_array_type",
            "InvalidArraySplat",
            "InvalidArraySplat",
        ),
        (
            "switch_case_negative_at_unsigned",
            "const type mismatch",
            "const type mismatch",
        ),
        (
            "switch_case_above_signed_max",
            "const type mismatch",
            "const type mismatch",
        ),
        (
            "ptr_data_of_non_pointer",
            "PointerOpInvalid: bb0: ptr_data cannot use pointer type i32: type is not pointer-like",
            "requires a pointer-like type",
        ),
        (
            "struct_passing_always_memory_by_value_aggregate",
            "AlwaysMemory",
            "AlwaysMemory",
        ),
        (
            "struct_passing_unclassified_by_value_aggregate",
            "unclassified",
            "unclassified",
        ),
        (
            "narrow_arg_ext_unrecorded_darwin",
            "no recorded argument extension",
            "no recorded argument extension",
        ),
    ] {
        let row = rows
            .iter()
            .find(|row| row.id() == id)
            .unwrap_or_else(|| panic!("`{id}` is a row of the pinned corpus"));
        let mut module = retarget_to_wasm32(decode(row).expect("the row decodes"));
        for function in &mut module.functions {
            function.body_gate = None;
        }
        let per_function = module
            .functions
            .iter()
            .filter(|function| !function.is_declaration())
            .find_map(|function| {
                lower_function_with_license(
                    &mut WasmModule::new(),
                    function,
                    &module,
                    WasmFunctionEnv::empty(),
                    &permitting,
                )
                .err()
            })
            .map_or(Ok(()), Err);
        for (lane, result, needle) in [
            (
                "compile_module_with_license",
                compile_module_with_license(&module, &permitting).map(drop),
                needle,
            ),
            (
                "compile_object_with_license",
                compile_object_with_license(&module, &permitting).map(drop),
                needle,
            ),
            ("lower_function_with_license", per_function, floor),
        ] {
            let error = result
                .map(|()| format!("{lane}: claim-less `{id}` ACCEPTED"))
                .expect_err("the entries refuse the subject under Permit")
                .to_string();
            assert!(
                error.contains(needle),
                "{lane}: claim-less `{id}` refused, but not by `{needle}`: {error}"
            );
        }
    }
}

/// The wasm lanes' body-construct floor applies the rest of the native
/// adapter's operand admission: a `PtrMetadata` / `PtrFromParts` whose
/// declared metadata type is not the pointer's metadata at 32-bit pointers
/// (trust-ir `PointerMetadataTypeMismatch`; the lane would fabricate or drop a
/// metadata word), and an `Undef` outside the native scalar carrier set
/// (aggregate poison is unmodelled). These are not corpus rows; each refusal
/// is checked beside a well-typed twin that both module entries still
/// compile. The probes are claim-less, which the default policy refuses at
/// the license (roadmap WS7.5, DG-73), so the entries take `Permit`
/// explicitly.
///
/// Since WS7.3 the module entries run trust-ir's validator first, so the
/// metadata mismatch is refused there, as trust-ir's own typed finding
/// (`PointerMetadataTypeMismatch`), before the lane's floor; trust-ir admits
/// an aggregate `Undef`, so the floor still refuses that one on every entry.
/// The public per-function entry (`lower_function_with_license`) runs no
/// ingestion admission, so it reaches the lane's floor for every subject,
/// which stays pinned there. It does not lower the twins: a bare per-function
/// environment provisions no stack-pointer global for the slice twin's frame.
#[test]
fn default_wasm_entries_refuse_the_native_operand_admission_subjects() {
    use trust_cg_codegen::wasm::{
        WasmFunctionEnv, WasmModule, compile_module_with_license, compile_object_with_license,
        lower_function_with_license,
    };
    let permitting = license().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit);
    const HEADER: &str =
        "; TrustIr text format v1\nmodule \"m\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n";
    // `(case, body, None for a twin | Some((module/object entry needle,
    // per-function lane-floor needle)))`.
    type Case = (
        &'static str,
        &'static str,
        Option<(&'static str, &'static str)>,
    );
    let cases: [Case; 6] = [
        (
            "ptr_metadata of a thin pointer declared i32",
            "functy.0 = (ptr) -> (i32)\n\nfn @f(functy.0) {\nbb0(%0: ptr):\n    %1 = ptr_metadata ptr %0 to i32\n    ret %1\n}\n",
            Some((
                "PointerMetadataTypeMismatch: bb0: ptr_metadata for ptr metadata must be (), got i32",
                "PtrMetadata in `f` block BlockId(0) metadata type mismatch for Ptr: declared I32, expected Unit",
            )),
        ),
        (
            "ptr_from_parts of a thin pointer with i32 metadata",
            "functy.0 = (ptr, i32) -> (ptr)\n\nfn @f(functy.0) {\nbb0(%0: ptr, %1: i32):\n    %2 = ptr_from_parts ptr ptr %0, i32 %1\n    ret %2\n}\n",
            Some((
                "PointerMetadataTypeMismatch: bb0: ptr_from_parts for ptr metadata must be (), got i32",
                "PtrFromParts in `f` block BlockId(0) metadata type mismatch for Ptr: declared I32, expected Unit",
            )),
        ),
        (
            "slice metadata declared at the 64-bit width",
            "type ty.0 = i32\n\nfuncty.0 = (ptr, u64) -> (u64)\n\nfn @f(functy.0) {\nbb0(%0: ptr, %1: u64):\n    %2 = ptr_from_parts fatptr<slice ty.0> ptr %0, u64 %1\n    %3 = ptr_metadata fatptr<slice ty.0> %2 to u64\n    ret %3\n}\n",
            Some((
                "PointerMetadataTypeMismatch: bb0: ptr_from_parts for fatptr<slice ty.0> metadata must be u32, got u64",
                "PtrFromParts in `f` block BlockId(0) metadata type mismatch for FatPtr",
            )),
        ),
        (
            "slice metadata at the wasm32 width (twin)",
            "type ty.0 = i32\n\nfuncty.0 = (ptr, u32) -> (u32)\n\nfn @f(functy.0) {\nbb0(%0: ptr, %1: u32):\n    %2 = ptr_from_parts fatptr<slice ty.0> ptr %0, u32 %1\n    %3 = ptr_metadata fatptr<slice ty.0> %2 to u32\n    ret %3\n}\n",
            None,
        ),
        (
            "undef of an array type",
            "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\nfn @f(functy.0) {\nbb0(%0: i32):\n    %1 = undef [ty.0 x 4]\n    %2 = extractelement i32 %1, %0\n    ret %2\n}\n",
            Some((
                "aggregate/vector poison is unmodelled",
                "aggregate/vector poison is unmodelled",
            )),
        ),
        (
            "undef of a scalar type (twin)",
            "functy.0 = (i32) -> (i32)\n\nfn @f(functy.0) {\nbb0(%0: i32):\n    %1 = undef i32\n    %2 = add i32 %1, %0\n    ret %2\n}\n",
            None,
        ),
    ];
    for (case, body, needles) in cases {
        let module = trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
            .unwrap_or_else(|e| panic!("{case}: the probe parses: {e}"));
        let entries = [
            (
                "compile_module_with_license",
                compile_module_with_license(&module, &permitting).map(drop),
            ),
            (
                "compile_object_with_license",
                compile_object_with_license(&module, &permitting).map(drop),
            ),
        ];
        let Some((needle, floor)) = needles else {
            for (lane, result) in entries {
                if let Err(error) = result {
                    panic!("{lane}: twin `{case}` refused: {error}");
                }
            }
            continue;
        };
        let per_function = lower_function_with_license(
            &mut WasmModule::new(),
            &module.functions[0],
            &module,
            WasmFunctionEnv::empty(),
            &permitting,
        )
        .map(drop);
        for (lane, result, needle) in entries
            .into_iter()
            .map(|(lane, result)| (lane, result, needle))
            .chain([("lower_function_with_license", per_function, floor)])
        {
            let error = result
                .map(|()| format!("{lane}: `{case}` ACCEPTED"))
                .expect_err("the entry refuses the subject")
                .to_string();
            assert!(
                error.contains(needle),
                "{lane}: `{case}` refused, but not by `{needle}`: {error}"
            );
        }
    }
}
