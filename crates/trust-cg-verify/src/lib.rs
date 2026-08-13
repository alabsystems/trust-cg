// trust-cg-verify - Verification backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

// Trust Codegen is embedded into tRust's compiler build, so rustc's internal lint set
// is applied here. These rustc query lints are not part of Trust Codegen's standalone
// API contract; deterministic verification evidence is checked at Trust Codegen
// boundaries.
#![allow(rustc::default_hash_types)]
#![allow(rustc::potential_query_instability)]

//! Verification backend for Trust Codegen.
//!
//! This crate builds and checks verification obligations for selected trust_ir
//! lowering, optimization, encoding, and whole-function paths. Coverage and
//! evidence strength vary by obligation: small domains can be exhaustive,
//! wider evaluator runs are statistical, and supported obligations can be sent
//! to an external ay/Z3-compatible SMT solver.
//!
//! # Architecture
//!
//! ```text
//! trust_ir_semantics    -- trust_ir instruction semantics as SmtExpr; currently a
//!                      local encoder pending the #255 trust_ir semantics bridge
//! aarch64_semantics -- AArch64 instruction semantics as SmtExpr
//! lowering_proof    -- Proof obligations pairing both sides
//! smt               -- Self-contained bitvector expression AST + evaluator
//! verify            -- High-level verification interface
//! ```
//!
//! # Verification strength levels
//!
//! Each proof obligation is verified at one of three strength levels
//! (see [`verify::VerificationStrength`] for full details):
//!
//! | Level | Bit-width | Strategy | Guarantee |
//! |-------|-----------|----------|-----------|
//! | **Exhaustive** | <= 8 (with <= 2 inputs) | All 2^(w*n) input combinations | Complete for that width |
//! | **Statistical** | > 8 (32-bit, 64-bit) | Edge cases + 100K random samples | Probabilistic, not formal |
//! | **Formal** | Supported represented obligation | AY SMT solver | Mathematical proof when the solver returns `Verified` |
//!
//! ## Current status
//!
//! The evaluator remains the baseline library path via
//! [`lowering_proof::verify_by_evaluation`]:
//! - 8-bit proofs run **exhaustive** verification (all 65,536 input pairs tested)
//! - 32/64-bit proofs run **statistical** verification (36 edge-case combos +
//!   100,000 random samples per proof)
//!
//! The 32/64-bit statistical verification provides high confidence but is
//! **not a formal proof**. Structured or adversarial bugs could theoretically
//! hide in the untested ~2^64 input space.
//!
//! The default Cargo feature set runs the evaluator lane. v0.1.0 does not
//! expose a native-AY Cargo feature.
//!
//! ## Formal verification (ay)
//!
//! Two verification backends are available in v0.1.0:
//!
//! 1. **Evaluation testing** (always available): fast, catches
//!    regressions, exhaustive for 8-bit, statistical for 32/64-bit. This is
//!    the baseline API path and requires no external solver.
//! 2. **AY CLI** via [`ay_bridge`]: serialize proof obligations to
//!    SMT-LIB2 format with [`lowering_proof::ProofObligation::to_smt2`],
//!    pipe them to the external AY solver for formal discharge. A supported
//!    obligation is formally proved only when the solver returns `Verified`;
//!    timeouts, `unknown`, and unsupported translations are not proofs. The
//!    subprocess lane is available without a Cargo feature when a compatible
//!    solver binary is on `PATH`.
//!
//! The native-AY experiment was retired: solver-backed verification has one
//! maintained path through the canonical external AY binary.
//!
//! ## Configuring sample count
//!
//! The number of random samples for statistical verification is configurable
//! via [`lowering_proof::VerificationConfig`]:
//!
//! ```rust
//! use trust_cg_verify::lowering_proof::{
//!     proof_iadd_i32, verify_by_evaluation_with_config, VerificationConfig,
//! };
//! use trust_cg_verify::verify::VerificationResult;
//!
//! let config = VerificationConfig::with_sample_count(500_000);
//! let obligation = proof_iadd_i32();
//! let result = verify_by_evaluation_with_config(&obligation, &config);
//! assert!(matches!(result, VerificationResult::Valid));
//! ```
//!
//! # Example
//!
//! ```rust
//! use trust_cg_verify::lowering_proof::{proof_iadd_i32, verify_by_evaluation};
//! use trust_cg_verify::verify::VerificationResult;
//!
//! let obligation = proof_iadd_i32();
//! let result = verify_by_evaluation(&obligation);
//! assert!(matches!(result, VerificationResult::Valid));
//! ```

// `rayon` is a declared dependency reserved for the parallel verification runner
// (currently single-threaded); keep it linked without tripping the Trust compiler
// build's deny(unused_extern_crates). See verification_runner.rs (the parallel
// `use rayon::prelude::*` is staged but not yet enabled).
use rayon as _;

pub mod aarch64_backend_proof_report;
pub mod aarch64_eh_coverage_proofs;
pub mod aarch64_eh_lsda_proofs;
pub mod aarch64_elf_tls_reloc_proofs;
pub mod aarch64_jumptable_proofs;
pub mod aarch64_macho_call_reloc_proofs;
pub mod aarch64_macho_data_reloc_proofs;
pub mod aarch64_macho_tlvp_reloc_proofs;
pub mod aarch64_semantics;
pub mod aarch64_tlv_thunk_proofs;
pub mod action_equiv;
pub mod addr_mode_proofs;
pub mod ane_semantics;
pub mod atomic_proofs;
pub mod ay_bridge;
pub mod bridge_coverage;
pub mod call_lowering_proofs;
pub mod canary_cert;
pub mod carrier_hygiene;
pub mod cegis;
pub mod cegis_cache_io;
pub mod cegis_pass;
pub mod cegis_pass_x86;
pub mod certified_pass_chain;
pub mod certified_pass_checker;
pub mod cfg_proofs;
pub mod checked_overflow_proofs;
pub mod cmp_combine_proofs;
pub mod const_fold_proofs;
pub mod const_materialize_proofs;
pub mod coroutine_frame_proofs;
pub mod coverage_gate;
pub mod cse_licm_proofs;
pub mod dataflow_integrity;
pub mod definite_init;
pub mod diag;
pub use trust_cg_process_env as env_lock;
pub mod elf_call_reloc_proofs;
pub mod elf_data_reloc_proofs;
pub mod ext_trunc_proofs;
pub mod failed_proof_reducer;
pub mod field_copy_faithfulness;
pub mod fp_bitmodel;
pub mod fp_convert_proofs;
pub mod frame_proofs;
pub mod fsym_arith;
pub mod fsym_bounds;
pub mod fsym_null;
pub mod fsym_summary;
pub mod fsym_trust_ir;
pub mod fsym_uaf;
pub mod function_verifier;
pub mod gpu_semantics;
pub mod gvn_proofs;
pub mod if_convert_proofs;
pub mod loop_backedge_symexec;
pub mod loop_opt_proofs;
pub mod lowering_proof;
pub mod lrat_cert;
pub mod macho_call_reloc_proofs;
pub mod macho_data_reloc_proofs;
pub mod macho_proofs;
pub mod memory_model;
pub mod memory_proofs;
pub mod mir_semantics;
pub mod neon_encoding_proofs;
pub mod neon_lowering_proofs;
pub mod neon_semantics;
pub mod nzcv;
pub mod object_inventory;
pub mod obligation_cert_store;
pub mod opt_proofs;
pub mod pass_validators;
pub mod peephole_proofs;
pub mod post_ra_captured_spec;
pub mod post_ra_dataflow;
pub mod post_ra_reaching_def;
pub mod post_ra_spill_slots;
pub mod post_regalloc_recheck;
pub mod proof_certificate;
pub mod proof_database;
pub mod proof_gate;
pub mod provenance_xcheck;
pub mod reduction_split_proofs;
pub mod regalloc_proofs;
pub mod rewrite_admission;
pub mod rewrite_candidate_extractor;
pub mod riscv_function_verifier;
pub mod riscv_lowering_proofs;
pub mod riscv_semantics;
pub mod rule_discovery;
pub mod sat_blast;
pub mod scheduler_proofs;
pub mod smt;
pub mod smt_bv_batch;
pub mod ssa_loop_complete;
pub mod strength_reduce_proofs;
pub mod switch_proofs;
pub mod synthesis;
#[cfg(feature = "trust-types-bridge")]
pub mod transval_compat;
pub mod trust_ir_semantics;
pub mod unified_synthesis;
pub mod vectorization_proofs;
pub mod verdict_db;
pub mod verification_runner;
pub mod verify;
#[cfg(test)]
mod wasm_formal;
pub mod wasm_function_verifier;
pub mod wasm_lowering_proofs;
pub mod wasm_memory_proofs;
pub mod wasm_semantics;
pub mod x86_64_eflags;
pub mod x86_64_eflags_proofs;
pub mod x86_64_function_verifier;
pub mod x86_64_lowering_proofs;
pub mod x86_64_semantics;

pub use ay_bridge::{
    AYCategoryBreakdown, AYConfig, AYResult, BOUNDED_QUANTIFIER_EXPANSION_LIMIT,
    ProofDatabaseAYReport, encode_obligation_as_chc, expand_bounded_quantifiers,
    expand_bounded_quantifiers_with_limit, generate_smt2_query, has_quantifiers, parse_ay_output,
    prepare_formula_for_smt, serialize_to_smt2, solver_info, verify_proof_database_with_ay,
    verify_with_ay, verify_with_ay_cli, verify_with_cli, z3_available,
};
pub use cegis::{CegisLoop, CegisResult, ConcreteInput};
pub use cegis_cache_io::{
    CEGIS_CACHE_DIR_NAME, CEGIS_CACHE_ENV, STALE_LOCK_AGE, SharedCegisCache, WRITE_LOCK_POLL,
    WRITE_LOCK_WAIT, default_cache_root as cegis_shared_cache_root,
};
pub use cegis_pass::{
    CegisCacheEntry, CegisPassStats, CegisSuperoptConfig, CegisSuperoptPass, ProvenRewrite,
    RewriteLayer,
};
pub use cegis_pass_x86::{X86CegisPassStats, X86CegisSuperoptConfig, X86CegisSuperoptPass};
pub use certified_pass_chain::{
    CertifiedPassChain, CertifiedPassChainEntry, CertifiedPassChainError,
};
pub use failed_proof_reducer::{
    FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA, FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION,
    FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA, FAILED_PROOF_REDUCER_ARTIFACT_SCHEMA_VERSION,
    FAILED_PROOF_REDUCER_PARENT_ISSUE, FailedProofCounterexampleCorpus,
    FailedProofCounterexampleSeed, FailedProofCounterexampleSeedFilter, FailedProofEvidenceSummary,
    FailedProofFollowUpTemplate, FailedProofReducerArtifact, ProductGateName,
    classify_failed_admission_record, missing_product_gates,
};
pub use function_verifier::{
    FunctionVerificationReport, FunctionVerifier, InstructionOpcode, InstructionReport,
    InstructionVerificationResult, reconstruct_alu_obligation, verify_function,
};
pub use lowering_proof::{
    DEFAULT_SAMPLE_COUNT, EXHAUSTIVE_WIDTH_THRESHOLD, MachineSideProvenance, ProofObligation,
    TransvalCheckKind, VerificationConfig, verify_by_evaluation, verify_by_evaluation_with_config,
    verify_fp_by_evaluation,
};
pub use object_inventory::{
    ObjectContainer, ObjectProofBinding, ObjectRelocationInventoryReport, ObjectRelocationKind,
    ObjectRelocationProofRegistry, RelocationInventoryEntry, RelocationInventoryStatus,
};
pub use proof_certificate::{
    CertificateChain, CertificateError, CertificateResult, ChainSummary, ChainVerificationResult,
    ProofCertificate, SolverUsed, generate_certificate, generate_certificate_chain,
};
pub use proof_database::{CategorizedProof, ProofCategory, ProofDatabase, ProofSummary};
pub use rewrite_admission::{
    AY_LRA_BASIS_UPDATE_KERNEL_FAMILY, AY_LRA_PROOF_CONSUMPTION_MANIFEST_ISSUE,
    AY_LRA_SPARSE_SUBSTITUTE_KERNEL_FAMILY, AYLraRewriteKernelFamily, AdmissionState,
    CertificateIdentity, CostContext, CounterexampleRecord, CounterexampleValue, KernelAllowlist,
    PROOF_GUIDED_ADMISSION_VERDICT_ISSUE, PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA,
    PROOF_GUIDED_ADMISSION_VERDICT_SCHEMA_VERSION, ProductGateEvidence, ProofAssumption,
    ProofAssumptionKind, ProofFailureKind, ProofGuidedAdmissionDisposition,
    ProofGuidedAdmissionRejection, ProofGuidedAdmissionVerdict, REWRITE_ADMISSION_SCHEMA,
    REWRITE_ADMISSION_SCHEMA_VERSION, ReducerMetadata, RewriteAdmissionRecord, SolverEvidence,
    SourceRegionIdentity, TargetAbiLayoutIdentity, TransformIdentity,
};
pub use rewrite_candidate_extractor::{
    CandidateKernelFamily, CandidateRegionExtractionInput, CandidateRegionExtractionMetadata,
    ExtractedRewriteAdmissionCandidate, REWRITE_CANDIDATE_EXTRACTOR_SCHEMA,
    REWRITE_CANDIDATE_EXTRACTOR_SCHEMA_VERSION, REWRITE_CANDIDATE_SOURCE_HASH_ALGORITHM,
    RewriteAdmissionRecordInputs, TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
    TY_NATIVE_FUSED_PARENT_LOOP_DEFAULT_KERNEL_NAME, TY_NATIVE_FUSED_PARENT_LOOP_KERNEL_FAMILY,
    TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA, TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT,
    extract_rewrite_admission_candidate,
};
pub use riscv_function_verifier::{
    RiscVFunctionVerifier, RiscVISelFunction, RiscVISelInst, RiscVISelOperand,
    reconstruct_alu_obligation as reconstruct_riscv_alu_obligation,
    representative_reconstructable_inst as representative_riscv_reconstructable_inst,
    verify_riscv_function,
};
pub use rule_discovery::{DiscoveryStats, RuleDatabase, RuleDiscovery, RuleProposal, RuleResult};
pub use smt::{RoundingMode, SmtError, SmtExpr, SmtSort};
pub use smt_bv_batch::{
    SMT_BV_BATCH_PROMOTION_BLOCKERS, SMT_BV_BATCH_PROOF_POLICY_VERSION,
    SMT_BV_BATCH_TEMPLATE_SCHEMA, SMT_BV_BATCH_TEMPLATE_VERSION, SmtBvBatchLane,
    SmtBvBatchLaneResult, SmtBvBatchStatus, SmtBvBatchTemplateError, SmtBvBatchTemplateManifest,
    SmtBvInputSymbol, SmtBvLaneTimeoutBudget, SmtBvObligationBatchLayout, SmtBvOutcome,
    SmtBvPromotionPolicy, SmtBvReplayInputs, SmtBvReplayLane, SmtBvScalarBatchEquivalence,
    SmtBvScalarEquivalenceLane, SmtBvScalarEquivalenceLayout, SmtBvScalarResult, SmtBvSolverRoute,
    SmtBvTemplateHash, SmtBvTimeoutBudget, build_smt_bv_batch_template_from_ay_inventory,
    build_smt_bv_batch_template_manifest, compare_scalar_and_batch_outcome, is_smt_bv_obligation,
};
pub use verification_runner::{
    AYVerificationMode, CategoryBreakdown, FailedProofDetail, VerificationRunReport,
    VerificationRunResult, VerificationRunner, select_auto_mode,
};
pub use verify::{
    ProofResult, VerificationReport, VerificationResult, VerificationStrength, Verifier,
    WholeFunctionVerificationReport,
};
pub use wasm_function_verifier::{
    WasmISelFunction, WasmISelInst, reconstruct_alu_obligation as reconstruct_wasm_alu_obligation,
    representative_reconstructable_inst as representative_wasm_reconstructable_inst,
};
pub use x86_64_function_verifier::{
    X86FunctionVerifier, reconstruct_alu_obligation as reconstruct_x86_alu_obligation,
    representative_reconstructable_inst as representative_x86_reconstructable_inst,
    verify_x86_64_function,
};
