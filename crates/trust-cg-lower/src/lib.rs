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
pub mod compute_graph;
pub mod declared_layout;
pub mod dispatch;
pub mod function;
pub mod guard_evidence;
pub mod instructions;
pub mod isel;
pub mod lattice_guard;
pub mod layout_refusal;
pub mod magic_udiv;
pub mod overflow_idiom;
pub mod perf_stats;
pub mod smulh_idiom;
pub mod switch;
pub mod target_analysis;
pub mod trust_ir_compat;
pub mod types;
pub mod va_list;
pub mod x86_64_isel;

pub use abi::{
    AArch64AbiVariant, AppleAArch64ABI, ArgLocation, ClassifyResult, CompactUnwindEntry,
    DwarfCfiOp, HfaBaseType, PReg, SavedRegister, UnwindInfo, generate_compact_unwind,
    generate_dwarf_cfi, gpr,
};
pub use adapter::{
    AdapterError, ExtractedProofMetadata, GuardCarrierArch, LLVM_LIBM_PURE_FUNCTION_ATTR_TAG,
    LLVM_STACK_PROTECTOR_FUNCTION_ATTR_TAG, LLVM_STACK_PROTECTOR_REQUIRED_FUNCTION_ATTR_TAG, Proof,
    ProofContext, ProofDivergence, ProofDropCode, ProofDropDiagnostic, ProofFact, SourceDebugInfo,
    SourceSpanEntry, TlsDialect, extract_proof_diagnostics, extract_proof_facts,
    extract_proof_metadata, extract_proofs, extract_source_debug_info, translate_function,
    translate_module, translate_module_for_arch, translate_module_for_arch_with_tls,
    translate_type, translate_type_with_structs, translate_type_with_tables,
};
pub use compute_graph::TargetRecommendation;
pub use dispatch::{
    DispatchError, DispatchOp, DispatchPlan, ProfitabilityMismatch, VerificationReport,
    generate_dispatch_plan, generate_profitability_aware_dispatch_plan, validate_dispatch_plan,
    validate_profitability_compliance, verify_dispatch_plan_properties,
};
pub use function::{Function, ParamPointeeType, StackSlotInfo};
pub use isel::{
    ISelBlock, ISelError, ISelFunction, ISelInst, ISelOperand, InstructionSelector,
    convert_isel_operand_to_ir,
};
pub use layout_refusal::{
    AuthorityLayout, FieldOffsetMismatch, NotComparableKind, StructLayoutCensus,
    StructLayoutDisposition, StructLayoutRow, StructSizeMismatch, census_module_struct_layouts,
    classify_struct_layout,
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
