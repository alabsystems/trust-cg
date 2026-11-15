// trust-cg-lower - trust_ir to LIR lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

// Trust Codegen is embedded into tRust's compiler build, so rustc's internal lint set
// is applied here. These rustc query lints are not part of Trust Codegen's standalone
// API contract; deterministic lowering evidence is checked at Trust Codegen boundaries.
#![allow(rustc::default_hash_types)]
#![allow(rustc::potential_query_instability)]

//! trust_ir to Low-level IR (LIR) lowering for Trust Codegen.
//!
//! This crate handles the first stage of compilation: lowering trust_ir
//! (the universal IR from tRust/tSwift/tC) to a low-level IR suitable
//! for optimization and machine code generation.

pub mod abi;
pub mod adapter;
pub mod bitfield_dialect;
pub mod codegen_license;
mod codegen_metadata;
pub mod compute_graph;
pub mod declared_layout;
pub mod dispatch;
pub mod function;
pub mod guard_evidence;
pub mod handle_transport;
pub mod instructions;
pub mod isel;
pub mod lattice_guard;
pub mod layout_refusal;
pub mod magic_udiv;
pub(crate) mod niche_codec;
pub mod overflow_idiom;
pub mod perf_stats;
mod retained_identity;
pub mod smulh_idiom;
pub mod static_call_devirtualization;
pub mod switch;
pub mod target_analysis;
pub mod trust_ir_compat;
mod tuple_pointer_transport;
pub mod types;
pub mod va_list;
pub mod x86_64_isel;

/// Whether this build carries the test-only mutation knobs.
///
/// `false` in every default build: a knob that re-introduces a known
/// miscompile must never ship. Even with the feature compiled in (an
/// `--all-features` check), every knob starts OFF and is reachable only through
/// the `mutation_knobs` module's setters, which no shipped binary calls.
pub const MUTATION_KNOBS: bool = cfg!(feature = "mutation-knobs");

/// Test-only mutation knobs that re-introduce historical miscompiles, so a
/// differential gate can prove it detects them. Compiled only with the
/// non-default `mutation-knobs` feature (a Cargo feature rather than
/// `cfg(test)`, so integration tests of dependent crates can reach it).
#[cfg(feature = "mutation-knobs")]
pub mod mutation_knobs {
    use std::sync::atomic::{AtomicBool, Ordering};

    static ENUM_PAYLOAD_OFF_BY_ONE: AtomicBool = AtomicBool::new(false);
    static PERTURB_ENUM_CANONICAL_LAYOUT: AtomicBool = AtomicBool::new(false);

    /// WS7.6: emit every direct-tag enum PAYLOAD projection one byte past the
    /// offset the layout names, after the canonical-layout check has passed.
    /// A wrong-code mutation a native-vs-interpreter differential must catch.
    /// Process-global; callers serialize its use.
    pub fn set_enum_payload_off_by_one(enabled: bool) {
        ENUM_PAYLOAD_OFF_BY_ONE.store(enabled, Ordering::SeqCst);
    }

    /// Whether [`set_enum_payload_off_by_one`] is currently on.
    pub fn enum_payload_off_by_one() -> bool {
        ENUM_PAYLOAD_OFF_BY_ONE.load(Ordering::SeqCst)
    }

    /// WS7.6: move trust-cg's own `Type::Enum` payload offset one byte, so
    /// trust-cg's canonical layout disagrees with trust-ir's
    /// `Module::enum_layout_shape`; the canonical-agreement precondition must
    /// then refuse every projection (`EnumCanonicalLayoutDisagrees`).
    /// Process-global; callers serialize its use.
    pub fn set_perturb_enum_canonical_layout(enabled: bool) {
        PERTURB_ENUM_CANONICAL_LAYOUT.store(enabled, Ordering::SeqCst);
    }

    /// Whether [`set_perturb_enum_canonical_layout`] is currently on.
    pub fn perturb_enum_canonical_layout() -> bool {
        PERTURB_ENUM_CANONICAL_LAYOUT.load(Ordering::SeqCst)
    }
}

pub use abi::{
    AArch64AbiVariant, AppleAArch64ABI, ArgLocation, ClassifyResult, CompactUnwindEntry,
    DwarfCfiOp, HfaBaseType, PReg, SavedRegister, UnwindInfo, generate_compact_unwind,
    generate_dwarf_cfi, gpr,
};
pub use adapter::{
    AdapterError, AdapterNamedCallSemantics, ExtractedProofMetadata, GuardCarrierArch,
    LLVM_LIBM_PURE_FUNCTION_ATTR_TAG, LLVM_STACK_PROTECTOR_FUNCTION_ATTR_TAG,
    LLVM_STACK_PROTECTOR_REQUIRED_FUNCTION_ATTR_TAG, ObjectAccessModel, PreLirTransform,
    PreparedModuleForLir, Proof, ProofContext, ProofDivergence, ProofDropCode, ProofDropDiagnostic,
    ProofFact, RelocationModel, SourceDebugInfo, SourceSpanEntry, SwiftReturnBudget, TlsDialect,
    WeakUndefinedReferencePolicy, classify_adapter_named_call, extract_proof_diagnostics,
    extract_proof_facts, extract_proof_metadata, extract_proofs, extract_source_debug_info,
    inline_handle_identity, known_target_features, prepare_module_for_lir,
    reject_unconsumed_v41_surface, reject_unconsumed_v41_surface_with_weak_references,
    reject_unconsumed_v41_target_neutral_surface,
    reject_unconsumed_v41_target_neutral_surface_with_weak_references,
    reject_unwitnessed_swift_conv_for_x86_abi, swift_return_budget_for_arch, translate_function,
    translate_function_with_license, translate_function_with_names, translate_module,
    translate_module_for_arch, translate_module_for_arch_with_access_model_and_stats_with_license,
    translate_module_for_arch_with_tls, translate_module_for_arch_with_tls_and_stats,
    translate_module_for_arch_with_tls_and_stats_and_validation,
    translate_module_for_arch_with_tls_and_stats_and_validation_with_license,
    translate_module_for_arch_with_tls_and_stats_with_license,
    translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references,
    translate_module_for_arch_with_tls_and_validation,
    translate_module_for_arch_with_tls_and_validation_with_license,
    translate_module_for_arch_with_tls_with_license,
    translate_module_strict_for_arch_with_tls_and_validation,
    translate_module_strict_for_arch_with_tls_and_validation_with_license, translate_type,
    translate_type_with_structs, translate_type_with_tables,
    translate_validated_module_strict_for_arch_with_tls_and_validation,
    translate_validated_module_strict_for_arch_with_tls_and_validation_with_license,
    x86_swift_budget_is_witnessed_for_abi,
};
pub use codegen_license::{CLEAN_KERNEL_TV_AUTHORITY, CodegenLicensePolicy, UnlicensedBodyPolicy};
pub use codegen_metadata::{
    reject_byval_params, reject_variadic_definition, validate_codegen_metadata,
    validate_function_codegen_metadata,
};
pub use compute_graph::TargetRecommendation;
pub use dispatch::{
    DispatchError, DispatchOp, DispatchPlan, ProfitabilityMismatch, VerificationReport,
    generate_dispatch_plan, generate_profitability_aware_dispatch_plan, validate_dispatch_plan,
    validate_profitability_compliance, verify_dispatch_plan_properties,
};
pub use function::{Function, ParamPointeeType, StackSlotInfo};
pub use handle_transport::{
    admit_handle_surface, handle_validation_refusal, module_spells_a_handle, refuse_handle_surface,
};
pub use isel::{
    ISelBlock, ISelError, ISelFunction, ISelInst, ISelOperand, InstructionSelector,
    convert_isel_operand_to_ir,
};
pub use layout_refusal::{
    AuthorityLayout, FieldOffsetMismatch, NotComparableKind, StructLayoutCensus,
    StructLayoutDisposition, StructLayoutRow, StructSizeMismatch, census_module_struct_layouts,
    classify_struct_layout,
};
pub use retained_identity::{RetainedIdentityError, retained_lir_proof_context_digest};
pub use static_call_devirtualization::{
    ModuleLocalFunctionIdentityCensus, ModuleTranslationValidationReport,
    StaticCallDevirtualizationStats, module_local_function_identity_census,
};
pub use switch::{
    SwitchStrategy, choose_strategy, emit_binary_search, emit_jump_table, emit_linear_scan,
};
pub use target_analysis::{ComputeTarget, ProofAnalyzer, SubgraphProof, TargetLegality};
pub use trust_ir::SourceSpan;
pub use types::Type;
pub use va_list::{VaArgAccess, VaArgLowering, VaListIntrinsic, lower_va_arg, va_start_offset};
pub use x86_64_isel::{
    X86CallResultReg, X86FloatCmpStrategy, X86ISelBlock, X86ISelError, X86ISelFunction,
    X86ISelInst, X86ISelOperand, X86InstructionSelector, x86_float_cmp_strategy,
    x86cc_from_floatcc, x86cc_from_intcc,
};
