// trust-cg-verify/proof_database.rs - Unified proof obligation database
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Consolidates all proof obligation registries across trust-cg-verify into a
// single queryable database. Previously, proofs were scattered across 8+
// modules with separate registry functions (all_arithmetic_proofs(),
// all_division_proofs(), all_fp_lowering_proofs(), etc.). This module
// provides a unified ProofDatabase for inventory, reporting, and
// verification orchestration.
//
// Reference: designs/2026-04-13-verification-architecture.md

//! Unified proof obligation database.
//!
//! [`ProofDatabase`] collects all [`ProofObligation`]s from every proof
//! module in `trust-cg-verify` and exposes them through a queryable API:
//!
//! - [`ProofDatabase::all()`] -- every proof obligation in the system.
//! - [`ProofDatabase::by_category()`] -- filter by [`ProofCategory`].
//! - [`ProofDatabase::summary()`] -- counts per category, width, and strength.
//!
//! # Example
//!
//! ```rust
//! use trust_cg_verify::proof_database::{ProofDatabase, ProofCategory};
//!
//! let db = ProofDatabase::new();
//! let total = db.all().len();
//! let arith = db.by_category(ProofCategory::Arithmetic).len();
//! let summary = db.summary();
//! assert!(total > 0);
//! assert!(arith > 0);
//! assert_eq!(summary.total, total);
//! ```

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};

// ---------------------------------------------------------------------------
// Prepared x86-64 bitfield proof query hooks
// ---------------------------------------------------------------------------

/// Representative L68 x86-64 bitfield window used for verifier/database/smoke
/// hooks.
pub const X86_BITFIELD_REPRESENTATIVE_TYPE_BITS: u32 = 32;
pub const X86_BITFIELD_REPRESENTATIVE_LSB: u8 = 7;
pub const X86_BITFIELD_REPRESENTATIVE_WIDTH: u8 = 13;

/// Query substring for the representative x86 unsigned bitfield extract proof.
pub const X86_EXTRACT_BITS_I32_PROOF_QUERY: &str = "ExtractBits{lsb=7,width=13}_I32";

/// Query substring for the representative x86 signed bitfield extract proof.
pub const X86_SEXTRACT_BITS_I32_PROOF_QUERY: &str = "SextractBits{lsb=7,width=13}_I32";

/// Query substring for the representative x86 bitfield insert proof.
pub const X86_INSERT_BITS_I32_PROOF_QUERY: &str = "InsertBits{lsb=7,width=13}_I32";

/// Query substring for the representative x86 aliased bitfield insert proof.
pub const X86_INSERT_BITS_ALIAS_I32_PROOF_QUERY: &str = "InsertBits{lsb=7,width=13}_I32(dst,dst)";

/// Representative x86-64 bitfield proof query names. These are intentionally
/// substring queries so they match the full x86 obligation names
/// (`x86_64: ... -> ...`) without coupling smoke tests to the suffix.
pub const X86_BITFIELD_REPRESENTATIVE_PROOF_QUERIES: &[(&str, &str)] = &[
    ("x86_extract_bits_i32", X86_EXTRACT_BITS_I32_PROOF_QUERY),
    ("x86_sextract_bits_i32", X86_SEXTRACT_BITS_I32_PROOF_QUERY),
    ("x86_insert_bits_i32", X86_INSERT_BITS_I32_PROOF_QUERY),
    (
        "x86_insert_bits_alias_i32",
        X86_INSERT_BITS_ALIAS_I32_PROOF_QUERY,
    ),
];

// ---------------------------------------------------------------------------
// ProofCategory enum
// ---------------------------------------------------------------------------

/// Categories of proof obligations in the verification system.
///
/// Each proof obligation belongs to exactly one category, determined by
/// the module and registry function that produces it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProofCategory {
    /// Integer arithmetic lowering: add, sub, mul, neg (I8-I64).
    /// Source: `lowering_proof::all_arithmetic_proofs()` (excludes division subset).
    Arithmetic,

    /// Integer division lowering: sdiv, udiv (I32, I64).
    /// Source: `lowering_proof::all_division_proofs()`.
    Division,

    /// Floating-point lowering: fadd, fsub, fmul, fneg (F32, F64).
    /// Source: `lowering_proof::all_fp_lowering_proofs()`.
    FloatingPoint,

    /// Comparison lowering: icmp -> CMP + CSET (10 conditions x I32/I64).
    /// Source: `lowering_proof::all_comparison_proofs_i32()` + `_i64()`.
    Comparison,

    /// Branch lowering: condbr -> CMP + B.cond (10 conditions x I32/I64).
    /// Source: `lowering_proof::all_branch_proofs()`.
    Branch,

    /// Peephole optimization identity rules.
    /// Source: `peephole_proofs::all_peephole_proofs_all_widths()`.
    Peephole,

    /// General optimization pass proofs (const fold, AND/OR absorb, DCE, copy prop).
    /// Source: `opt_proofs::all_opt_proofs()`.
    Optimization,

    /// Constant folding proofs (comprehensive: binary ops, unary ops, identities).
    /// Source: `const_fold_proofs::all_const_fold_proofs_with_variants()`.
    ConstantFolding,

    /// CSE and LICM proofs.
    /// Source: `cse_licm_proofs::all_cse_licm_proofs()`.
    CseLicm,

    /// CFG simplification proofs (branch folding, empty block elimination).
    /// Source: `cfg_proofs::all_cfg_proofs_with_variants()`.
    CfgSimplification,

    /// Memory load/store and load-pair proofs (SMT array theory).
    /// Source: `memory_proofs::all_memory_proofs()`.
    Memory,

    /// Load/Store lowering proofs: trust_ir Load/Store -> AArch64 LDR/LDRB/LDRH/STR/STRB/STRH
    /// (I8/I16/I32/I64 equivalence) plus store-load roundtrip (I32, I64). 10 obligations.
    /// Source: `lowering_proof::all_load_store_proofs()`.
    LoadStoreLowering,

    /// NEON SIMD lowering proofs (trust_ir vector ops -> NEON instructions).
    /// Source: `neon_lowering_proofs::all_neon_lowering_proofs()`.
    NeonLowering,

    /// NEON encoding correctness proofs (Wave 22 opcodes).
    /// Source: `neon_encoding_proofs::all_neon_encoding_proofs()`.
    NeonEncoding,

    /// Vectorization proofs (scalar-to-NEON mapping correctness).
    /// Source: `vectorization_proofs::all_vectorization_proofs()`.
    Vectorization,

    /// Register allocation correctness proofs (non-interference, completeness,
    /// spill correctness, copy insertion, phi elimination, calling convention,
    /// live-through, spill slot non-aliasing).
    /// Source: `regalloc_proofs::all_regalloc_proofs()`.
    RegAlloc,

    /// Bitwise and shift lowering proofs: AND, OR, XOR, NOT, SHL, LSR, ASR,
    /// BIC/ORN, and bitfield extracts/inserts.
    /// Source: `lowering_proof::all_bitwise_shift_proofs()`.
    BitwiseShift,

    /// Constant materialization proofs (MOVZ, MOVZ+MOVK, ORR logical imm, MOVN).
    /// Source: `const_materialize_proofs::all_const_materialize_proofs_with_variants()`.
    ConstantMaterialization,

    /// Address mode formation proofs (base+imm, base+reg, scaled offsets, writeback).
    /// Source: `addr_mode_proofs::all_addr_mode_proofs()`.
    AddressMode,

    /// Frame index elimination correctness proofs (offset computation, range checks,
    /// alignment, callee-save non-overlap, slot distinctness).
    /// Source: `frame_proofs::all_frame_proofs()`.
    FrameLayout,

    /// Instruction scheduling correctness proofs (RAW/WAW/WAR dependency
    /// preservation, register pressure bounds, latency ordering, memory
    /// ordering, control flow, topological validity, reordering freedom,
    /// critical path optimality).
    /// Source: `scheduler_proofs::all_scheduler_proofs()`.
    InstructionScheduling,

    /// Mach-O emission correctness proofs (relocation encoding, symbol binding,
    /// structural invariants).
    /// Source: `macho_proofs::all_macho_proofs()`.
    MachOEmission,

    /// Loop optimization correctness proofs (loop unrolling semantics preservation,
    /// strength reduction multiply-to-add equivalence, combined transformation
    /// composition, dead IV elimination).
    /// Source: `loop_opt_proofs::all_loop_opt_proofs()`.
    LoopOptimization,

    /// Strength reduction pass correctness proofs.
    StrengthReduction,

    /// Compare-and-branch fusion and compare-select combine proofs.
    CmpCombine,

    /// Global Value Numbering correctness proofs.
    Gvn,

    /// If-conversion correctness proofs (diamond/triangle CFG to CSEL/CSINC/CSNEG).
    /// Source: `if_convert_proofs::all_if_convert_proofs_with_variants()`.
    IfConversion,

    /// FP conversion lowering proofs (FCVTZS, FCVTZU, SCVTF, UCVTF, FCVT,
    /// roundtrip, NaN handling).
    /// Source: `fp_convert_proofs::all_fp_convert_proofs()`.
    FpConversion,

    /// Extension and truncation lowering proofs (SXTB, SXTH, SXTW, UXTB,
    /// UXTH, UXTW, AND masking, roundtrip, idempotence).
    /// Source: `ext_trunc_proofs::all_ext_trunc_proofs()`.
    ExtensionTruncation,

    /// Atomic memory operation proofs (LDAR/STLR load-acquire/store-release,
    /// LSE read-modify-write including min/max, CAS compare-and-swap,
    /// DMB fence ordering, SUB via NEG+LDADD, AND via MVN+LDCLR equivalences).
    /// Source: `atomic_proofs::all_atomic_proofs()`.
    AtomicOperations,

    /// Call lowering correctness proofs (argument placement X0-X7/V0-V7,
    /// return values X0/V0, callee-saved preservation X19-X28/V8-V15,
    /// stack alignment, BL/BLR link register, indirect call via X16 scratch,
    /// GPR/FPR independent allocation, stack overflow arguments).
    /// Source: `call_lowering_proofs::all_call_lowering_proofs()`.
    CallLowering,

    /// x86-64 lowering proofs (arithmetic, division, bitwise, shifts,
    /// comparisons, floating-point, extensions, LEA, three-operand IMUL).
    /// Source: `x86_64_lowering_proofs::all_x86_64_proofs()`.
    /// Wired in #434; remains opt-in (not default-on) until AArch64 is
    /// default-on first per #407/#340.
    X8664Lowering,

    /// Switch lowering correctness proofs: trust_ir `Switch(scrutinee, cases,
    /// default)` lowered as jump table (dense) or balanced BST (sparse)
    /// selects the same successor block as a linear-scan reference.
    /// Source: `switch_proofs::all_switch_proofs()`.
    /// Wired in #444 (deferred proof obligation from #323).
    ///
    /// Separate from `Branch` (which is single-target CMP+B.cond) and from
    /// `CfgSimplification` (which eliminates branches rather than selecting
    /// among multiple targets).
    SwitchLowering,

    /// RISC-V (RV64) lowering proofs: clean 1:1 dataflow ALU (ADD/SUB/MUL/
    /// AND/OR/XOR/SLL/SRL/SRA), shift-by-immediate (SLLI/SRLI), the ADDI value
    /// role, the direct comparison value ops (SLT/SLTU), and the comparison
    /// idioms (Icmp Eq/Ne/Sge/Sgt/Sle/Uge/Ugt/Ule modeled as the full emitted
    /// SUB+SLTIU / SUB+SLTU / SLT+XORI / swapped-SLT sequences).
    /// Source: `riscv_lowering_proofs::all_riscv_proofs()`.
    RiscVLowering,

    /// WebAssembly lowering proofs: the GENUINELY non-degenerate scalar
    /// refinement obligations (shifts under the `b < width` mask divergence,
    /// integer comparisons, NaN-precise float comparisons, integer negate, and
    /// integer-width casts). The plain int-ALU / div-rem / bitwise / FP-arith
    /// lowerings are NOT registered here — they were degenerate X==X
    /// self-equalities and are SUPERSEDED by operand reconstruction
    /// (`wasm_function_verifier`), the SAME genuine credit path the gate uses.
    /// Source: `wasm_lowering_proofs::all_wasm_lowering_proofs()`.
    WasmLowering,
}

impl ProofCategory {
    /// Return all category variants in declaration order.
    pub fn all_categories() -> &'static [ProofCategory] {
        &[
            ProofCategory::Arithmetic,
            ProofCategory::Division,
            ProofCategory::FloatingPoint,
            ProofCategory::Comparison,
            ProofCategory::Branch,
            ProofCategory::Peephole,
            ProofCategory::Optimization,
            ProofCategory::ConstantFolding,
            ProofCategory::CseLicm,
            ProofCategory::CfgSimplification,
            ProofCategory::Memory,
            ProofCategory::LoadStoreLowering,
            ProofCategory::NeonLowering,
            ProofCategory::NeonEncoding,
            ProofCategory::Vectorization,
            ProofCategory::RegAlloc,
            ProofCategory::BitwiseShift,
            ProofCategory::ConstantMaterialization,
            ProofCategory::AddressMode,
            ProofCategory::FrameLayout,
            ProofCategory::InstructionScheduling,
            ProofCategory::MachOEmission,
            ProofCategory::LoopOptimization,
            ProofCategory::StrengthReduction,
            ProofCategory::CmpCombine,
            ProofCategory::Gvn,
            ProofCategory::IfConversion,
            ProofCategory::FpConversion,
            ProofCategory::ExtensionTruncation,
            ProofCategory::AtomicOperations,
            ProofCategory::CallLowering,
            ProofCategory::X8664Lowering,
            ProofCategory::SwitchLowering,
            ProofCategory::RiscVLowering,
            ProofCategory::WasmLowering,
        ]
    }

    /// Human-readable name for this category.
    pub fn name(&self) -> &'static str {
        match self {
            ProofCategory::Arithmetic => "Arithmetic",
            ProofCategory::Division => "Division",
            ProofCategory::FloatingPoint => "Floating-Point",
            ProofCategory::Comparison => "Comparison",
            ProofCategory::Branch => "Branch",
            ProofCategory::Peephole => "Peephole",
            ProofCategory::Optimization => "Optimization",
            ProofCategory::ConstantFolding => "Constant Folding",
            ProofCategory::CseLicm => "CSE/LICM",
            ProofCategory::CfgSimplification => "CFG Simplification",
            ProofCategory::Memory => "Memory",
            ProofCategory::LoadStoreLowering => "Load/Store Lowering",
            ProofCategory::NeonLowering => "NEON Lowering",
            ProofCategory::NeonEncoding => "NEON Encoding",
            ProofCategory::Vectorization => "Vectorization",
            ProofCategory::RegAlloc => "Register Allocation",
            ProofCategory::BitwiseShift => "Bitwise/Shift",
            ProofCategory::ConstantMaterialization => "Constant Materialization",
            ProofCategory::AddressMode => "Address Mode",
            ProofCategory::FrameLayout => "Frame Layout",
            ProofCategory::InstructionScheduling => "Instruction Scheduling",
            ProofCategory::MachOEmission => "Mach-O Emission",
            ProofCategory::LoopOptimization => "Loop Optimization",
            ProofCategory::StrengthReduction => "Strength Reduction",
            ProofCategory::CmpCombine => "Cmp Combine",
            ProofCategory::Gvn => "GVN",
            ProofCategory::IfConversion => "If-Conversion",
            ProofCategory::FpConversion => "FP Conversion",
            ProofCategory::ExtensionTruncation => "Extension/Truncation",
            ProofCategory::AtomicOperations => "Atomic Operations",
            ProofCategory::CallLowering => "Call Lowering",
            ProofCategory::X8664Lowering => "x86-64 Lowering",
            ProofCategory::SwitchLowering => "Switch Lowering",
            ProofCategory::RiscVLowering => "RISC-V Lowering",
            ProofCategory::WasmLowering => "WebAssembly Lowering",
        }
    }

    /// Coarse translation-validation check kind for this proof family.
    ///
    /// The direct trust-transval kinds are used only when the obligation has
    /// the same meaning as that VC class. Backend-specific families map to
    /// Trust Codegen's extension kinds.
    pub fn transval_check_kind(&self) -> TransvalCheckKind {
        match self {
            ProofCategory::Optimization
            | ProofCategory::ConstantFolding
            | ProofCategory::CseLicm
            | ProofCategory::LoopOptimization
            | ProofCategory::StrengthReduction
            | ProofCategory::Gvn => TransvalCheckKind::DataFlow,

            ProofCategory::CfgSimplification
            | ProofCategory::IfConversion
            | ProofCategory::SwitchLowering => TransvalCheckKind::ControlFlow,

            ProofCategory::Peephole | ProofCategory::CmpCombine => {
                TransvalCheckKind::PeepholeOptimization
            }

            ProofCategory::Memory
            | ProofCategory::LoadStoreLowering
            | ProofCategory::AtomicOperations => TransvalCheckKind::MemoryModel,

            ProofCategory::FrameLayout | ProofCategory::RegAlloc => {
                TransvalCheckKind::RegisterAllocation
            }

            ProofCategory::NeonLowering
            | ProofCategory::NeonEncoding
            | ProofCategory::Vectorization => TransvalCheckKind::Vectorization,

            ProofCategory::Arithmetic
            | ProofCategory::Division
            | ProofCategory::FloatingPoint
            | ProofCategory::Comparison
            | ProofCategory::Branch
            | ProofCategory::BitwiseShift
            | ProofCategory::ConstantMaterialization
            | ProofCategory::AddressMode
            | ProofCategory::InstructionScheduling
            | ProofCategory::MachOEmission
            | ProofCategory::FpConversion
            | ProofCategory::ExtensionTruncation
            | ProofCategory::CallLowering
            | ProofCategory::X8664Lowering
            | ProofCategory::RiscVLowering
            | ProofCategory::WasmLowering => TransvalCheckKind::InstructionLowering,
        }
    }
}

impl std::fmt::Display for ProofCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ---------------------------------------------------------------------------
// CategorizedProof: a proof obligation paired with its category
// ---------------------------------------------------------------------------

/// A proof obligation paired with its category.
#[derive(Debug, Clone)]
pub struct CategorizedProof {
    /// The proof obligation.
    pub obligation: ProofObligation,
    /// The category this proof belongs to.
    pub category: ProofCategory,
}

// ---------------------------------------------------------------------------
// ProofSummary: aggregated statistics
// ---------------------------------------------------------------------------

/// Aggregated statistics about the proof database.
#[derive(Debug, Clone)]
pub struct ProofSummary {
    /// Total number of proof obligations.
    pub total: usize,
    /// Count of proofs per category.
    pub by_category: Vec<(ProofCategory, usize)>,
    /// Count of proofs per translation-validation check kind.
    pub by_check_kind: Vec<(TransvalCheckKind, usize)>,
    /// Count of proofs with no typed translation-validation check kind.
    pub uncategorized_check_kind_count: usize,
    /// Count of proofs using one of trust-transval's four native check kinds.
    pub transval_compatible_count: usize,
    /// Count of proofs using Trust Codegen-specific TransvalCheckKind extensions.
    pub trust_cg_extension_count: usize,
    /// Count of proofs per maximum input bit-width.
    /// Key is the width (8, 16, 32, 64, 128, or 0 for FP-only).
    pub by_width: Vec<(u32, usize)>,
    /// Count of proofs that use floating-point inputs.
    pub fp_proof_count: usize,
    /// Count of proofs with preconditions.
    pub preconditioned_count: usize,
}

impl std::fmt::Display for ProofSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "ProofDatabase Summary")?;
        writeln!(f, "=====================")?;
        writeln!(f, "Total proofs: {}", self.total)?;
        writeln!(f)?;
        writeln!(f, "By category:")?;
        for (cat, count) in &self.by_category {
            if *count > 0 {
                writeln!(f, "  {:25} {:>4}", cat.name(), count)?;
            }
        }
        writeln!(f)?;
        writeln!(f, "By transval check kind:")?;
        for (kind, count) in &self.by_check_kind {
            if *count > 0 {
                writeln!(f, "  {:25} {:>4}", kind, count)?;
            }
        }
        if self.uncategorized_check_kind_count > 0 {
            writeln!(
                f,
                "  {:25} {:>4}",
                "uncategorized", self.uncategorized_check_kind_count
            )?;
        }
        writeln!(f)?;
        writeln!(f, "By max input width:")?;
        for (width, count) in &self.by_width {
            if *count > 0 {
                let label = if *width == 0 {
                    "FP-only".to_string()
                } else {
                    format!("{}-bit", width)
                };
                writeln!(f, "  {:25} {:>4}", label, count)?;
            }
        }
        writeln!(f)?;
        writeln!(
            f,
            "Transval-compatible:  {}",
            self.transval_compatible_count
        )?;
        writeln!(
            f,
            "Trust Codegen extensions:     {}",
            self.trust_cg_extension_count
        )?;
        writeln!(f, "FP proofs:            {}", self.fp_proof_count)?;
        writeln!(f, "With preconditions:   {}", self.preconditioned_count)?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// ProofDatabase
// ---------------------------------------------------------------------------

/// Unified database of all proof obligations in trust-cg-verify.
///
/// Collects proofs from every registry function across all proof modules
/// and provides query and reporting capabilities.
///
/// # Construction
///
/// ```rust
/// use trust_cg_verify::proof_database::ProofDatabase;
/// let db = ProofDatabase::new();
/// ```
///
/// The database is constructed eagerly -- all proofs are materialized
/// on `new()`. For lazy iteration, use the individual module registries.
pub struct ProofDatabase {
    proofs: Vec<CategorizedProof>,
}

// ---------------------------------------------------------------------------
// Proof registration helpers — #[inline(never)] to limit stack frame size
//
// Each function registers one category of proofs. By splitting the
// registration across separate functions, we prevent the compiler from
// merging all temporaries into a single stack frame in debug builds,
// which was causing stack overflows. See issue #205.
// ---------------------------------------------------------------------------

#[inline(never)]
fn register_arithmetic_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::lowering_proof::all_division_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Division,
        });
    }
    let all_arith = crate::lowering_proof::all_arithmetic_proofs();
    let div_count = crate::lowering_proof::all_division_proofs().len();
    let arith_take = all_arith.len().saturating_sub(div_count);
    for p in all_arith.into_iter().take(arith_take) {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Arithmetic,
        });
    }
    // Remainder lowering proofs (issue #435). Categorized as Division since
    // Urem/Srem compose UDIV/SDIV + MSUB and share the div-by-zero
    // precondition.
    for p in crate::lowering_proof::all_remainder_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Division,
        });
    }
    // Bitcast lowering proofs (issue #435). Categorized as Arithmetic since
    // `Bitcast` is a scalar opcode with no dedicated category and lowers to
    // MOV/FMOV -- a pure arithmetic identity at the bitvector level.
    for p in crate::lowering_proof::all_bitcast_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Arithmetic,
        });
    }
    for p in crate::lowering_proof::all_bitwise_shift_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::BitwiseShift,
        });
    }
    // Bitfield lowering proofs (issue #452/#435). ExtractBits / SextractBits /
    // InsertBits compose shifts, masks, and sign-extends; categorized as
    // BitwiseShift since they share the underlying shift+mask structure.
    for p in crate::lowering_proof::all_bitfield_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::BitwiseShift,
        });
    }
}

#[inline(never)]
fn register_fp_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::lowering_proof::all_fp_lowering_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::FloatingPoint,
        });
    }
    // FCSEL (scalar FP conditional select): the faithful bit-preserving-mux
    // obligations (S+D, a spread of condition codes). Registered under
    // FloatingPoint so the coverage gate credits `FcselRR` through the
    // `fcsel_f32` / `fcsel_f64` names. These are pure QF_BV `ite` obligations
    // (bitvector `inputs`, no `fp_inputs`), so the generic evaluator discharges
    // them — they never route to the FP-specific NaN-aware evaluator.
    for p in crate::lowering_proof::all_fcsel_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::FloatingPoint,
        });
    }
}

#[inline(never)]
fn register_comparison_branch_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::lowering_proof::all_comparison_proofs_i32() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Comparison,
        });
    }
    for p in crate::lowering_proof::all_comparison_proofs_i64() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Comparison,
        });
    }
    for p in crate::lowering_proof::all_branch_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Branch,
        });
    }
}

#[inline(never)]
fn register_peephole_opt_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::peephole_proofs::all_peephole_proofs_all_widths() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Peephole,
        });
    }
    for p in crate::opt_proofs::all_opt_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Optimization,
        });
    }
    for p in crate::const_fold_proofs::all_const_fold_proofs_with_variants() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::ConstantFolding,
        });
    }
}

#[inline(never)]
fn register_analysis_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::cse_licm_proofs::all_cse_licm_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::CseLicm,
        });
    }
    for p in crate::cfg_proofs::all_cfg_proofs_with_variants() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::CfgSimplification,
        });
    }
    for p in crate::memory_proofs::all_memory_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Memory,
        });
    }
    // Coroutine-suspend frame save/restore — store next_state at frame[state_slot]
    // (offset slot*8) and preserve the independently-yielded return value. Both
    // discharge through the same symbolic byte-array memory model.
    for p in crate::coroutine_frame_proofs::all_coroutine_frame_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Memory,
        });
    }
    for p in crate::lowering_proof::all_load_store_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::LoadStoreLowering,
        });
    }
}

#[inline(never)]
fn register_backend_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::const_materialize_proofs::all_const_materialize_proofs_with_variants() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::ConstantMaterialization,
        });
    }
    for p in crate::addr_mode_proofs::all_addr_mode_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::AddressMode,
        });
    }
    // Dense-`match` / fieldless-enum JUMP-TABLE scaled table-entry load: the
    // LDRSW [Xn,Xm,LSL#2] effective-address scaling (`base + (index<<2) ==
    // base + 4*index`). FAITHFUL address-mode credit only — the loaded value
    // (dereference + i32->i64 sext) stays the shared unfaithful-load debt of the
    // Ldr* family. (The ADR jump-table BASE proof is registered under
    // MachOEmission in `register_emission_proofs`.)
    for p in crate::aarch64_jumptable_proofs::aarch64_jumptable_addr_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::AddressMode,
        });
    }
    for p in crate::frame_proofs::all_frame_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::FrameLayout,
        });
    }
    for p in crate::scheduler_proofs::all_scheduler_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::InstructionScheduling,
        });
    }
    for p in crate::regalloc_proofs::all_regalloc_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::RegAlloc,
        });
    }
}

#[inline(never)]
fn register_target_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::neon_lowering_proofs::all_neon_lowering_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::NeonLowering,
        });
    }
    for p in crate::neon_encoding_proofs::all_neon_encoding_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::NeonEncoding,
        });
    }
    for p in crate::vectorization_proofs::all_vectorization_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Vectorization,
        });
    }
}

#[inline(never)]
fn register_emission_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::macho_proofs::all_macho_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // The relocation obligations below are strict solver-backed formal
    // evidence. ProofDatabase membership is coverage accounting, not production
    // Certified object authority; the object registries remain empty until an
    // independently checked gate report is bound to the exact emitted object.
    for p in crate::aarch64_macho_data_reloc_proofs::aarch64_macho_data_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    for p in crate::aarch64_macho_call_reloc_proofs::aarch64_macho_call_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // x86-64 Mach-O relocation lanes (data rows + the direct-call BRANCH row):
    // the x86 mirror of the two AArch64 registrations above. Same standing —
    // coverage accounting for strict solver-backed evidence; production
    // Certified authority additionally requires the per-object ENC-9 reparse
    // binding (see object_inventory.rs).
    for p in crate::macho_data_reloc_proofs::x86_64_macho_data_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    for p in crate::macho_call_reloc_proofs::x86_64_macho_call_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // x86-64 ELF relocation lanes (data rows + the direct-call PLT32 row):
    // the ELF mirror of the two x86-64 Mach-O registrations above, modeling
    // the psABI Rela semantics (explicit addend, field-START `P`, the baked
    // `-4` RIP bridge). Registered in the shared object code-emission /
    // relocation family for strict solver-backed evidence and coverage
    // accounting. Production Certified authority additionally requires the
    // per-object ELF reparse binding (see object_inventory.rs).
    for p in crate::elf_data_reloc_proofs::x86_64_elf_data_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    for p in crate::elf_call_reloc_proofs::x86_64_elf_call_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // Dense-`match` / fieldless-enum JUMP-TABLE dispatch base: the ADR
    // PC-relative jump-table base (`ADR Xd == table_base`, the ring identity
    // `P + (T - P) == T`). Sibling of the BRANCH26 / PAGE21 PC-relative proofs.
    // (The LDRSW scaled table-entry effective-address proof is registered under
    // AddressMode in `register_backend_proofs`.)
    for p in crate::aarch64_jumptable_proofs::aarch64_jumptable_pcrel_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    for p in crate::aarch64_macho_tlvp_reloc_proofs::aarch64_macho_tlvp_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // AArch64 ELF TLS local-exec (TLSLE) relocation selection/encoding: the
    // `R_AARCH64_TLSLE_ADD_TPREL_HI12` (first ADD, LSL#12) + `_LO12_NC` (second
    // ADD) reconstruction of the thread-local address `TP + TPREL(S+A)`. Registered
    // in the shared object code-emission / relocation family for strict
    // solver-backed formal evidence and coverage accounting. This does NOT add
    // production Certified object-inventory authority: that registry remains
    // empty until Trusted-vs-Certified strength and solver-report binding exist.
    for p in crate::aarch64_elf_tls_reloc_proofs::aarch64_elf_tls_relocation_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // Darwin aarch64 TLV thunk-call (indirect descriptor resolver) — the
    // load-then-indirect-call SEMANTICS that turn the materialized descriptor
    // address into the thread-local variable address. Sibling of the TLVP reloc
    // address-arithmetic proofs.
    for p in crate::aarch64_tlv_thunk_proofs::aarch64_tlv_thunk_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // aarch64 LSDA EH call-site/dispatch encoding (catch(...) range membership +
    // positive-type-filter dispatch vs. cleanup). The __gcc_except_tab emission.
    for p in crate::aarch64_eh_lsda_proofs::aarch64_eh_lsda_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    // aarch64 LSDA EH call-site TABLE COVERAGE / PARTITION — the invariant the
    // dispatch proof above ASSUMES and that `resolve_eh_offsets` filler synthesis
    // (pipeline.rs:6720-6802) establishes: the resolved table covers [0,code_len)
    // exactly once (no gap => no terminate; no overlap => single record), and an
    // Invoke PC maps to its own landing pad (not a filler's 0).
    for p in crate::aarch64_eh_coverage_proofs::aarch64_eh_coverage_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::MachOEmission,
        });
    }
    for p in crate::loop_opt_proofs::all_loop_opt_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::LoopOptimization,
        });
    }
    // Reduction-splitting (accumulator-widening): N-lane regrouping of an
    // associative-integer reduction equals the sequential fold.
    for p in crate::reduction_split_proofs::all_reduction_split_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::LoopOptimization,
        });
    }
    // Closed-form (Faulhaber) reduction: a pure-polynomial add reduction's
    // straight-line closed form (S1/S2 modular identities) equals the loop's
    // running mod-2^64 accumulation.
    for p in crate::reduction_split_proofs::all_closed_form_reduction_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::LoopOptimization,
        });
    }
}

#[inline(never)]
fn register_strength_reduce_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::strength_reduce_proofs::all_strength_reduce_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::StrengthReduction,
        });
    }
}

#[inline(never)]
fn register_cmp_combine_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::cmp_combine_proofs::all_cmp_combine_proofs_with_variants() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::CmpCombine,
        });
    }
}

#[inline(never)]
fn register_gvn_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::gvn_proofs::all_gvn_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Gvn,
        });
    }
}

#[inline(never)]
fn register_if_convert_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::if_convert_proofs::all_if_convert_proofs_with_variants() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::IfConversion,
        });
    }
}

#[inline(never)]
fn register_fp_convert_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::fp_convert_proofs::all_fp_convert_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::FpConversion,
        });
    }
}

#[inline(never)]
fn register_ext_trunc_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::ext_trunc_proofs::all_ext_trunc_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::ExtensionTruncation,
        });
    }
}

#[inline(never)]
fn register_atomic_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::atomic_proofs::all_atomic_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::AtomicOperations,
        });
    }
}

#[inline(never)]
fn register_call_lowering_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::call_lowering_proofs::all_call_lowering_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::CallLowering,
        });
    }
}

#[inline(never)]
fn register_x86_64_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::x86_64_lowering_proofs::all_x86_64_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::X8664Lowering,
        });
    }
}

#[inline(never)]
fn register_riscv_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::riscv_lowering_proofs::all_riscv_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::RiscVLowering,
        });
    }
}

#[inline(never)]
fn register_wasm_proofs(proofs: &mut Vec<CategorizedProof>) {
    // The GENUINE non-degenerate wasm scalar refinement proofs (shifts /
    // comparisons / float comparisons / negate / casts). The plain int-ALU /
    // div-rem / bitwise / FP-arith lowerings are NOT registered — they were
    // degenerate X==X and are SUPERSEDED by operand reconstruction (the gate's
    // `audit_wasm` credits those opcodes via `wasm_reconstruction_discharges_valid`,
    // the SAME genuine path). Each registered proof's `category` is set to
    // `Some(InstructionLowering)` to satisfy the registered-check-kind invariant.
    for mut p in crate::wasm_lowering_proofs::all_wasm_lowering_proofs() {
        p.category = Some(ProofCategory::WasmLowering.transval_check_kind());
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::WasmLowering,
        });
    }
}

#[inline(never)]
fn register_switch_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in crate::switch_proofs::all_switch_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::SwitchLowering,
        });
    }
}

/// FAITHFUL whole-chain i128 add/sub composition proofs (ADDS;ADC / SUBS;SBC
/// reconstruct the native 128-bit value). Registered AFTER
/// `register_arithmetic_proofs` so a generic "add"/"sub" first-contains query
/// still resolves to the plain proofs; the unique "whole-chain" token avoids
/// collision with the degenerate `Iadd_I128 lo`/`hi` names. ProofCategory reused.
#[inline(never)]
fn register_i128_carry_chain_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in [
        crate::lowering_proof::proof_iadd_i128_whole_chain(),
        crate::lowering_proof::proof_isub_i128_whole_chain(),
    ] {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Arithmetic,
        });
    }
}

/// The FAITHFUL 32->64 UNSIGNED widening multiply obligation (UMULL Xd, Wn, Wm
/// — the UMADDL-with-XZR alias, `lowering_proof::proof_umull_rr`): SOURCE =
/// the Concat-zext ring form `concat(0,a) * concat(0,b)`, MACHINE = the
/// encoder-faithful `0 + ZeroExtend(a)*ZeroExtend(b)` — structurally distinct
/// (NOT X==X), provably equal over BV64; the SMULL sext confusion and the
/// truncating-MUL confusion REFUTE (`umull_wrong_controls`). Registered in a
/// dedicated registrar (NOT appended to `all_arithmetic_proofs`, whose
/// registration slices by division-proof count) AFTER the plain mul proofs, so
/// the `"-> umull xd"` query is a unique last-registered match and the generic
/// "mul" query still first-contains-resolves to the plain Imul proofs. UMULL
/// has exactly ONE legal form, so this single obligation is the complete
/// per-opcode statement. SMULL deliberately has NO registered proof — the
/// signed sibling stays a deferred RED row and must not inherit this credit.
#[inline(never)]
fn register_widening_multiply_proofs(proofs: &mut Vec<CategorizedProof>) {
    proofs.push(CategorizedProof {
        obligation: crate::lowering_proof::proof_umull_rr(),
        category: ProofCategory::Arithmetic,
    });
}

/// FAITHFUL per-compile AArch64 bitfield-EXTRACT ENCODING proofs (UBFM/SBFM at
/// register widths 32 and 64). These verify that the isel encoding
/// `immr = lsb, imms = lsb + width - 1` decodes (under the ARM hardware UBFM/SBFM
/// semantics) to the intended trust_ir `ExtractBits`/`SextractBits`: the machine
/// side is the hardware DECODE of the ENCODING (mask width `imms - immr + 1`),
/// STRUCTURALLY DISTINCT from the source side (mask width `width`), so a wrong
/// `immr`/`imms` formula REFUTES (NOT a degenerate X==X; crucially NOT the
/// structurally-identical `encode_ubfm_extract` reconstruction). Registered AFTER
/// `register_arithmetic_proofs` under `ExtensionTruncation` with unique
/// width-tagged name tokens ("ubfm extract w32" …) so the per-opcode and
/// width-polymorphic gate queries resolve unambiguously.
#[inline(never)]
fn register_bitfield_extract_proofs(proofs: &mut Vec<CategorizedProof>) {
    for p in [
        crate::lowering_proof::proof_ubfm_extract_w32(),
        crate::lowering_proof::proof_ubfm_extract_w64(),
        crate::lowering_proof::proof_sbfm_extract_w32(),
        crate::lowering_proof::proof_sbfm_extract_w64(),
    ] {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::ExtensionTruncation,
        });
    }
}

#[inline(never)]
fn register_checked_overflow_proofs(proofs: &mut Vec<CategorizedProof>) {
    // #67: kept-carrier checked-overflow DETECTION idioms (AArch64).
    //   sadd/ssub -> ADDS/SUBS + CSET VS       (V-flag sign-mismatch rule)
    //   uadd/usub -> ADDS/SUBS + CSET HS/LO    (carry/borrow rule)
    //   smul      -> MUL + SMULH + ASR + CMP + CSET NE  (high-half != sign-ext)
    //   umul      -> MUL + UMULH + CMP #0 + CSET NE     (high-half != 0)
    //
    // Each obligation packs `overflow_b1 :: value_iN` so the single-expression
    // ProofObligation machinery proves the wrapping result AND the overflow flag
    // together — a FAITHFUL (non-degenerate) witness, not the f81e45b identity
    // class. Registered under `Arithmetic` because the obligations carry
    // `Some(TransvalCheckKind::InstructionLowering)` (which Arithmetic's
    // `transval_check_kind()` returns), avoiding a new ProofCategory (and the
    // pinned 38). The `Checked*_I64` names are unique substrings within the
    // category, so the opcode_to_proof_query bindings select them unambiguously
    // and do not collide with the plain add/sub/mul Arithmetic proofs (those are
    // registered first, so a generic "add"/"sub"/"mul" query still resolves to
    // the plain proof by first-contains).
    for p in crate::checked_overflow_proofs::all_checked_overflow_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Arithmetic,
        });
    }

    // #67 mul disposition: the 64-bit Smulh/Umulh FORMAL discharge is SMT-hard
    // (128-bit `bvmul` times out), so those opcodes stay fail-closed-allowlisted
    // in classify_aarch64 rather than claim a 64-bit formal proof. The HONEST
    // mul evidence the allowlist reason cites — a genuine overflow-equivalence
    // theorem, EXHAUSTIVELY verified at width-8 (all 2^16 cases) and ay-formal at
    // width-8 — is registered here as first-class, gate-discharged proofs so the
    // "exhaustively/formally verified at width-8" claim is checkable, not prose.
    // These I8 names are distinct from the I64 names, so they never collide with
    // the Smulh/Umulh opcode bindings (which, being allowlisted, bind nothing).
    for p in crate::checked_overflow_proofs::all_checked_overflow_mul_exhaustive_i8_proofs() {
        proofs.push(CategorizedProof {
            obligation: p,
            category: ProofCategory::Arithmetic,
        });
    }
}

/// Every registrar, paired with the categories it can emit.
///
/// The pairing is what makes [`ProofDatabase::for_categories`] safe: a
/// consumer that only ever asks for one category need not pay to CONSTRUCT the
/// obligations of any other. It is verified against reality by
/// `registrar_category_table_matches_reality`, which builds the full database
/// and asserts that each registrar produced exactly the categories claimed
/// here — so adding a proof in a new category to an existing registrar fails
/// the test rather than silently shrinking somebody's database.
type ProofRegistrar = fn(&mut Vec<CategorizedProof>);

const REGISTRARS: &[(ProofRegistrar, &[ProofCategory])] = &[
    (
        register_arithmetic_proofs,
        &[
            ProofCategory::Arithmetic,
            ProofCategory::BitwiseShift,
            ProofCategory::Division,
        ],
    ),
    (register_fp_proofs, &[ProofCategory::FloatingPoint]),
    (
        register_comparison_branch_proofs,
        &[ProofCategory::Branch, ProofCategory::Comparison],
    ),
    (
        register_peephole_opt_proofs,
        &[
            ProofCategory::ConstantFolding,
            ProofCategory::Optimization,
            ProofCategory::Peephole,
        ],
    ),
    (
        register_analysis_proofs,
        &[
            ProofCategory::CfgSimplification,
            ProofCategory::CseLicm,
            ProofCategory::LoadStoreLowering,
            ProofCategory::Memory,
        ],
    ),
    (
        register_backend_proofs,
        &[
            ProofCategory::AddressMode,
            ProofCategory::ConstantMaterialization,
            ProofCategory::FrameLayout,
            ProofCategory::InstructionScheduling,
            ProofCategory::RegAlloc,
        ],
    ),
    (
        register_target_proofs,
        &[
            ProofCategory::NeonEncoding,
            ProofCategory::NeonLowering,
            ProofCategory::Vectorization,
        ],
    ),
    (
        register_emission_proofs,
        &[
            ProofCategory::LoopOptimization,
            ProofCategory::MachOEmission,
        ],
    ),
    (
        register_strength_reduce_proofs,
        &[ProofCategory::StrengthReduction],
    ),
    (register_cmp_combine_proofs, &[ProofCategory::CmpCombine]),
    (register_gvn_proofs, &[ProofCategory::Gvn]),
    (register_if_convert_proofs, &[ProofCategory::IfConversion]),
    (register_fp_convert_proofs, &[ProofCategory::FpConversion]),
    (
        register_ext_trunc_proofs,
        &[ProofCategory::ExtensionTruncation],
    ),
    (register_atomic_proofs, &[ProofCategory::AtomicOperations]),
    (
        register_call_lowering_proofs,
        &[ProofCategory::CallLowering],
    ),
    (register_x86_64_proofs, &[ProofCategory::X8664Lowering]),
    (register_riscv_proofs, &[ProofCategory::RiscVLowering]),
    (register_wasm_proofs, &[ProofCategory::WasmLowering]),
    (register_switch_proofs, &[ProofCategory::SwitchLowering]),
    (
        register_checked_overflow_proofs,
        &[ProofCategory::Arithmetic],
    ),
    (
        register_i128_carry_chain_proofs,
        &[ProofCategory::Arithmetic],
    ),
    (
        register_widening_multiply_proofs,
        &[ProofCategory::Arithmetic],
    ),
    (
        register_bitfield_extract_proofs,
        &[ProofCategory::ExtensionTruncation],
    ),
];

impl ProofDatabase {
    /// Construct a database holding ONLY the proofs a consumer can actually
    /// consult, by running only the registrars that emit `wanted`.
    ///
    /// MEASURED (2026-08-06): `ProofDatabase::new()` builds 1841 obligations,
    /// each an `SmtExpr` TREE, and that construction is the bulk of the
    /// bridge's compile-memory gap (153 MB vs LLVM's 70 MB; proofs off is
    /// 71 MB, i.e. parity). An x86-64 compile consults exactly ONE category —
    /// `X8664Lowering`, 531 obligations — so ~71% of that memory was built and
    /// never read.
    ///
    /// This changes NO verdict. The obligations for a wanted category are the
    /// same objects, produced by the same registrars, in the same relative
    /// order (registrars run in `REGISTRARS` order, and skipping a registrar
    /// cannot reorder the ones kept). Order matters because `resolve_db_proof`
    /// takes the FIRST name match, so preserving it is load-bearing, and
    /// `for_categories_matches_full_database` asserts it per category.
    ///
    /// Asking for a category no registrar emits yields an empty database for
    /// it, which resolves as `Unverified` — the fail-closed direction.
    pub fn for_categories(wanted: &[ProofCategory]) -> Self {
        let mut proofs = Vec::new();
        for (registrar, emits) in REGISTRARS {
            if emits.iter().any(|c| wanted.contains(c)) {
                registrar(&mut proofs);
            }
        }
        // A registrar that emits several categories still contributes only the
        // ones asked for; the rest would be dead weight of exactly the kind
        // this constructor exists to avoid.
        proofs.retain(|p| wanted.contains(&p.category));
        ProofDatabase { proofs }
    }

    /// Construct the database by collecting all proofs from all registries.
    ///
    /// Proof registration is split across multiple `#[inline(never)]` helper
    /// functions to prevent the compiler from accumulating all temporaries
    /// (SmtExpr trees, Vec buffers, etc.) into a single enormous stack frame
    /// in debug builds. This was causing stack overflows on the default 8 MB
    /// test-thread stack. See issue #205.
    pub fn new() -> Self {
        let mut proofs = Vec::new();
        register_arithmetic_proofs(&mut proofs);
        register_fp_proofs(&mut proofs);
        register_comparison_branch_proofs(&mut proofs);
        register_peephole_opt_proofs(&mut proofs);
        register_analysis_proofs(&mut proofs);
        register_backend_proofs(&mut proofs);
        register_target_proofs(&mut proofs);
        register_emission_proofs(&mut proofs);
        register_strength_reduce_proofs(&mut proofs);
        register_cmp_combine_proofs(&mut proofs);
        register_gvn_proofs(&mut proofs);
        register_if_convert_proofs(&mut proofs);
        register_fp_convert_proofs(&mut proofs);
        register_ext_trunc_proofs(&mut proofs);
        register_atomic_proofs(&mut proofs);
        register_call_lowering_proofs(&mut proofs);
        register_x86_64_proofs(&mut proofs);
        register_riscv_proofs(&mut proofs);
        register_wasm_proofs(&mut proofs);
        register_switch_proofs(&mut proofs);
        register_checked_overflow_proofs(&mut proofs);
        register_i128_carry_chain_proofs(&mut proofs);
        register_widening_multiply_proofs(&mut proofs);
        register_bitfield_extract_proofs(&mut proofs);
        ProofDatabase { proofs }
    }

    /// Return all proof obligations in the database.
    pub fn all(&self) -> &[CategorizedProof] {
        &self.proofs
    }

    /// Return all proof obligations matching the given category.
    pub fn by_category(&self, cat: ProofCategory) -> Vec<&CategorizedProof> {
        self.proofs.iter().filter(|p| p.category == cat).collect()
    }

    /// Return the count of proofs in the given category.
    pub fn count_by_category(&self, cat: ProofCategory) -> usize {
        self.proofs.iter().filter(|p| p.category == cat).count()
    }

    /// Return all proof obligations matching the given TransvalCheckKind.
    pub fn by_check_kind(&self, kind: TransvalCheckKind) -> Vec<&CategorizedProof> {
        self.proofs
            .iter()
            .filter(|p| p.obligation.category == Some(kind))
            .collect()
    }

    /// Return the count of proofs in the given TransvalCheckKind.
    pub fn count_by_check_kind(&self, kind: TransvalCheckKind) -> usize {
        self.proofs
            .iter()
            .filter(|p| p.obligation.category == Some(kind))
            .count()
    }

    /// Return registered proofs that have no typed TransvalCheckKind.
    pub fn uncategorized_check_kind(&self) -> Vec<&CategorizedProof> {
        self.proofs
            .iter()
            .filter(|p| p.obligation.category.is_none())
            .collect()
    }

    /// Search proofs by name substring (case-insensitive).
    pub fn search(&self, query: &str) -> Vec<&CategorizedProof> {
        let query_lower = query.to_lowercase();
        self.proofs
            .iter()
            .filter(|p| p.obligation.name.to_lowercase().contains(&query_lower))
            .collect()
    }

    /// Return a summary of the proof database.
    pub fn summary(&self) -> ProofSummary {
        let total = self.proofs.len();

        // Count by category
        let by_category: Vec<(ProofCategory, usize)> = ProofCategory::all_categories()
            .iter()
            .map(|cat| (*cat, self.count_by_category(*cat)))
            .collect();

        // Count by coarse translation-validation check kind.
        let by_check_kind: Vec<(TransvalCheckKind, usize)> = TransvalCheckKind::all_kinds()
            .iter()
            .map(|kind| (*kind, self.count_by_check_kind(*kind)))
            .collect();

        let uncategorized_check_kind_count = self.uncategorized_check_kind().len();
        let transval_compatible_count = self
            .proofs
            .iter()
            .filter(
                |p| matches!(p.obligation.category, Some(kind) if kind.is_transval_compatible()),
            )
            .count();
        let trust_cg_extension_count = self
            .proofs
            .iter()
            .filter(
                |p| matches!(p.obligation.category, Some(kind) if !kind.is_transval_compatible()),
            )
            .count();

        // Count by max input width
        let mut width_counts = std::collections::HashMap::new();
        for p in &self.proofs {
            let max_width = max_input_width(&p.obligation);
            *width_counts.entry(max_width).or_insert(0usize) += 1;
        }
        let mut by_width: Vec<(u32, usize)> = width_counts.into_iter().collect();
        by_width.sort_by_key(|(w, _)| *w);

        // Count FP proofs
        let fp_proof_count = self
            .proofs
            .iter()
            .filter(|p| !p.obligation.fp_inputs.is_empty())
            .count();

        // Count preconditioned proofs
        let preconditioned_count = self
            .proofs
            .iter()
            .filter(|p| !p.obligation.preconditions.is_empty())
            .count();

        ProofSummary {
            total,
            by_category,
            by_check_kind,
            uncategorized_check_kind_count,
            transval_compatible_count,
            trust_cg_extension_count,
            by_width,
            fp_proof_count,
            preconditioned_count,
        }
    }

    /// Return all distinct proof names (sorted).
    pub fn names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self
            .proofs
            .iter()
            .map(|p| p.obligation.name.as_str())
            .collect();
        names.sort();
        names
    }

    /// Total number of proofs.
    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    /// Whether the database is empty.
    pub fn is_empty(&self) -> bool {
        self.proofs.is_empty()
    }

    /// Construct a database from a pre-built list of categorized proofs.
    ///
    /// Useful for testing with a subset of proofs without constructing the
    /// full database.
    pub fn from_proofs(proofs: Vec<CategorizedProof>) -> Self {
        Self { proofs }
    }
}

impl Default for ProofDatabase {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Universal non-degeneracy gate (Strategy C, task #53)
// ---------------------------------------------------------------------------
//
// A lowering proof whose `trust_ir_expr` is STRUCTURALLY IDENTICAL to its
// machine (`aarch64_expr`) side — `SmtExpr` derives `PartialEq` (smt.rs:181) —
// proves nothing UNLESS the lowering genuinely IS a 1:1 identity. The honest
// (non-degenerate) case is one where the two sides are built by INDEPENDENT
// encoders: `encode_trust_ir_*(Opcode)` on the trust_ir side and a DISTINCT
// machine encoder on the other, such that a WRONG opcode/instruction choice
// would make the two sides differ and refute (e.g. `Iadd -> ADD`: both
// independently denote `bvadd`, but `Iadd -> SUB` would yield `bvadd == bvsub`
// and refute). For those, the identity is the faithful proof and it pins the
// emitted opcode.
//
// [`GENUINE_IDENTITY_ALLOWLIST`] enumerates exactly those audited genuine
// identities. The universal gate (see `proof_gate_strict` /
// `coverage_gate_tests`) iterates EVERY proof in [`ProofDatabase::new`] and
// requires it to be EITHER non-degenerate (`trust_ir_expr != aarch64_expr`) OR
// present on this allowlist. A degenerate proof NOT on the allowlist FAILS the
// gate (fail-closed), so a future degenerate proof can never silently register.
//
// This is the C-class generalization of the per-family `assert_ne` guards
// already enforced on the #67 checked-overflow family (proof_gate_strict.rs)
// and the RISC-V comparison idioms (coverage_gate_tests.rs).
//
// AUDIT PROVENANCE — each allowlisted name belongs to one of the audited
// genuine-identity families (independent-encoder 1:1 lowerings):
//
//   * Integer ALU single-instruction (Iadd/Isub/Imul/Neg -> ADD/SUB/MUL/NEG),
//     AArch64 + x86-64 + RISC-V, I8..I128.
//   * Division/remainder (Sdiv/Udiv -> SDIV/UDIV; Srem/Urem -> SDIV/UDIV+MSUB).
//   * Bitwise (Band/Bor/Bxor/Bnot/BandNot/BorNot -> AND/OR/XOR/NOT/BIC/ORN).
//   * Shift (Ishl/Ushr/Sshr -> SHL|LSL / LSR / ASR) — genuine 1:1 over the
//     in-range [0,width) region; see `shift_in_range_precondition` (#57).
//   * Floating-point (Fadd/Fsub/Fmul/Fneg/Fdiv/Fabs/Fsqrt -> F*) and Fcmp
//     (-> FCMP+CSET) and Fdemote/Fpromote (-> FCVT).
//   * FP conversion (FpToFp/BvToFp/FpToSBv/FpToUBv) + Extend/Truncate
//     (SignExtend/ZeroExtend/Trunc; Sextend/Uextend).
//   * NEON / vectorization lane-wise lowerings + NEON encoding.
//   * Bitcast same-width + Copy/MOV bit-preserving lowerings.
//   * Atomic memory-model identities (AtomicLoad -> LDAR*; RMW returns old
//     value; CAS success/failure paths) — genuine byte-addressable memory
//     expressions reconstructed by the memory-model encoder.
//   * AArch64 bitfield (ExtractBits/SextractBits/InsertBits -> UBFM/SBFM/BFM).
//   * x86-64 ALU/shift/FP/bitwise/bitcast/copy/conv/popcnt/bitfield/load/store
//     lowerings (EXCLUDES x86 control-flow target==target, MOV r,imm
//     materialize, Fence const==const, and LEA address-mode — those are
//     SUSPICIOUS, not genuine, and are deliberately absent here).
//
// Anything NOT on this list and degenerate is a SUSPICIOUS f81e45b X==X (the
// CSE/GVN/copy-prop/DCE/CFG/loop/TCO/call-arg-placement/if-conversion/
// cmp-combine/strength-reduce-no-change/scheduling/frame/regalloc/addr-mode/
// MachO/Fence/ANE-FP16 self-equalities). Those must be FIXED with a faithful
// independent-encoder obligation, NOT added here.
/// Audited "genuine 1:1 identity" proof names — a DOCUMENTED MODEL-CONSISTENCY /
/// classification list for the universal non-degeneracy gate.
///
/// STRICT proven-honesty (task #61, STRICT decision): this list NO LONGER grants
/// proven/covered/verified status to ANY proof. Under STRICT, a structurally
/// `X == X` obligation NEVER counts as proven — even these audited identities are
/// model-consistency checks, not lowering-correctness proofs, and credit ZERO in
/// every proven/covered/verified tally (`is_genuinely_proven` is the SOLE
/// criterion). The entries are KEPT here only so the `non_degeneracy_violations`
/// gate can recognize which degenerate proofs are EXPECTED/disclosed (vs. an
/// unclassified new one that would fail-close) — i.e. this is a classification /
/// documentation list, not an evidence allowlist.
///
/// INVARIANT (for classification only): a name belongs here ONLY if it is an
/// audited 1:1 identity whose two sides denote the same operation by intent.
/// Adding a name here grants NOTHING toward coverage/proven — to make a proof
/// count, give it a faithful independent machine-side obligation so that
/// `trust_ir_expr != aarch64_expr` (then it no longer belongs on this list).
pub const GENUINE_IDENTITY_ALLOWLIST: &[&str] = &[
    "AArch64 MADD_RR generic",
    "AArch64 MSUB_RR generic",
    "AtomicLoad_I16 -> LDARH",
    "AtomicLoad_I32 -> LDAR_W",
    "AtomicLoad_I64 -> LDAR_X",
    "AtomicLoad_I8 -> LDARB",
    "BandNot_I16 -> BIC (16-bit)",
    "BandNot_I32 -> BIC (32-bit)",
    "BandNot_I64 -> BIC (64-bit)",
    "BandNot_I8 -> BIC (8-bit)",
    "Band_I16 -> AND (16-bit)",
    "Band_I32 -> AND (32-bit)",
    "Band_I64 -> AND (64-bit)",
    "Band_I8 -> AND (8-bit)",
    "Bitcast_I16_I16 -> MOV (16-bit)",
    "Bitcast_I32_I32 -> MOV (32-bit)",
    "Bitcast_I64_I64 -> MOV (64-bit)",
    "Bitcast_I8_I8 -> MOV (8-bit)",
    "Bnot_I16 -> NOT (16-bit)",
    "Bnot_I8 -> NOT (8-bit)",
    "BorNot_I16 -> ORN (16-bit)",
    "BorNot_I32 -> ORN (32-bit)",
    "BorNot_I64 -> ORN (64-bit)",
    "BorNot_I8 -> ORN (8-bit)",
    "Bor_I16 -> OR (16-bit)",
    "Bor_I32 -> OR (32-bit)",
    "Bor_I64 -> OR (64-bit)",
    "Bor_I8 -> OR (8-bit)",
    "Bxor_I16 -> XOR (16-bit)",
    "Bxor_I32 -> XOR (32-bit)",
    "Bxor_I64 -> XOR (64-bit)",
    "Bxor_I8 -> XOR (8-bit)",
    "CAS_I32: failure path — memory unchanged",
    "CAS_I32: success path — mem[addr] = desired",
    "CAS_I64: success path — mem[addr] = desired",
    // (The two Faulhaber closed-form m=1 base cases that formerly lived here were
    // REMOVED when their obligations became genuinely non-degenerate: `proof_sum_i`
    // / `proof_sum_i2` now encode the closed form `m(m-1)/2` / `m(m-1)(2m-1)/6` as
    // an EXPRESSION TREE (`s1_expr`/`s2_expr`) rather than a pre-folded constant, so
    // even at m=1 the closed-form side `x + (1·0 >> 1)` is structurally distinct
    // from the loop fold `x + 0` and the obligation refutes a wrong closed form. A
    // faithful independent obligation belongs OFF this list — see the invariant
    // above.)
    "ExtractBits{lsb=11,width=23}_I64 -> UBFM (64-bit)",
    "ExtractBits{lsb=2,width=4}_I8 -> UBFM (8-bit)",
    "ExtractBits{lsb=3,width=7}_I16 -> UBFM (16-bit)",
    "ExtractBits{lsb=7,width=13}_I32 -> UBFM (32-bit)",
    "Fabs_F32 -> FABS Sd",
    "Fabs_F64 -> FABS Dd",
    "Fadd_F32 -> FADD Sd",
    "Fadd_F64 -> FADD Dd",
    // FCMP→NZCV+CSET model (encode_fcmp via the nzcv flag table). The cond
    // codes whose CSET flag-reading is STRUCTURALLY DISTINCT from the trust_ir
    // source predicate (GE/GT/LE/Ord and ALL the Unordered-* forms) are now
    // GENUINELY PROVEN (not X==X) — they were removed from this allowlist when
    // encode_fcmp moved from the degenerate FloatCC-mirroring model to the
    // faithful from_floatcc + NZCV model. The 8 that survive here read a single
    // flag equal to the source predicate (Eq→Z, NE→¬Z, LT→N, Uno→V), so they
    // remain structurally identical 1:1 identities.
    "Fcmp_Eq_F32 -> FCMP+CSET",
    "Fcmp_Eq_F64 -> FCMP+CSET",
    "Fcmp_LT_F32 -> FCMP+CSET",
    "Fcmp_LT_F64 -> FCMP+CSET",
    "Fcmp_NE_F32 -> FCMP+CSET",
    "Fcmp_NE_F64 -> FCMP+CSET",
    "Fcmp_Uno_F32 -> FCMP+CSET",
    "Fcmp_Uno_F32 -> x86_64 UCOMISS+SETcc",
    "Fcmp_Uno_F64 -> FCMP+CSET",
    "Fcmp_Uno_F64 -> x86_64 UCOMISD+SETcc",
    "FcvtFromInt_F32_I32 -> SCVTF Sd,Wn",
    "FcvtFromInt_F64_I64 -> SCVTF Dd,Xn",
    "FcvtFromUint_F32_I32 -> UCVTF Sd,Wn",
    "FcvtFromUint_F64_I64 -> UCVTF Dd,Xn",
    "FcvtToInt_I32_F32 -> FCVTZS Wd,Sn",
    "FcvtToInt_I64_F64 -> FCVTZS Xd,Dn",
    "FcvtToUint_I32_F32 -> FCVTZU Wd,Sn",
    "FcvtToUint_I64_F64 -> FCVTZU Xd,Dn",
    "Fdemote_F16_F32 -> FCVT Hd,Sn",
    "Fdemote_F32_F64 -> FCVT Ss,Dn",
    "Fdiv_F32 -> FDIV Sd",
    "Fdiv_F64 -> FDIV Dd",
    "Fmul_F32 -> FMUL Sd",
    "Fmul_F64 -> FMUL Dd",
    "Fneg_F32 -> FNEG Sd",
    "Fneg_F64 -> FNEG Dd",
    "Fpromote_F64_F32 -> FCVT Dd,Sn",
    "Fsqrt_F32 -> FSQRT Sd",
    "Fsqrt_F64 -> FSQRT Dd",
    "Fsub_F32 -> FSUB Sd",
    "Fsub_F64 -> FSUB Dd",
    // FP round-to-integral (AArch64 FRINT family). Single-instruction 1:1
    // identities in the SAME category as Fneg/Fabs/Fsqrt above: the machine side
    // is independently encoded FROM THE EMITTED OPCODE (aarch64_semantics.rs
    // encode_frintm->RTN, encode_frintp->RTP, encode_frintz->RTZ), so a wrong
    // opcode/rounding-mode refutes — they denote the same round-to-integral op by
    // intent. Classification only (zero coverage credit under STRICT, task #61).
    "Fceil_F32 -> FRINTP Sd",
    "Fceil_F64 -> FRINTP Dd",
    "Ffloor_F32 -> FRINTM Sd",
    "Ffloor_F64 -> FRINTM Dd",
    "Ftrunc_F32 -> FRINTZ Sd",
    "Ftrunc_F64 -> FRINTZ Dd",
    "Iadd_I128 hi -> ADC Xhi,Xa_hi,Xb_hi",
    "Iadd_I128 lo -> ADDS Xlo,Xa_lo,Xb_lo",
    "Iadd_I16 -> ADD (16-bit)",
    "Iadd_I32 -> ADDWrr",
    "Iadd_I64 -> ADDXrr",
    "Iadd_I8 -> ADD (8-bit)",
    "Imul_I128 lo -> MUL Xlo,Xa_lo,Xb_lo",
    "Imul_I16 -> MUL (16-bit)",
    "Imul_I32 -> MULWrrr",
    "Imul_I64 -> MULXrrr",
    "Imul_I8 -> MUL (8-bit)",
    "InsertBits{lsb=11,width=23}_I64 -> BFM (64-bit)",
    "InsertBits{lsb=2,width=4}_I8 -> BFM (8-bit)",
    "InsertBits{lsb=3,width=7}_I16 -> BFM (16-bit)",
    "InsertBits{lsb=7,width=13}_I32 -> BFM (32-bit)",
    "Isub_I128 hi -> SBC Xhi,Xa_hi,Xb_hi",
    "Isub_I128 lo -> SUBS Xlo,Xa_lo,Xb_lo",
    "Isub_I16 -> SUB (16-bit)",
    "Isub_I32 -> SUBWrr",
    "Isub_I64 -> SUBXrr",
    "Isub_I8 -> SUB (8-bit)",
    "Neg_I16 -> NEG (16-bit)",
    "Neg_I32 -> NEG Wd",
    "Neg_I64 -> NEG Xd",
    "Neg_I8 -> NEG (8-bit)",
    "NeonEncoding: ADD lane decomposition 4S",
    "NeonEncoding: ADD lane decomposition 8H",
    "NeonEncoding: AND bitwise 16B",
    "NeonEncoding: AND bitwise 8B",
    "NeonEncoding: CMEQ comparison 16B",
    "NeonEncoding: CMEQ comparison 4S",
    "NeonEncoding: DUP broadcast 4S",
    "NeonEncoding: DUP broadcast 8H",
    "NeonEncoding: EOR bitwise 16B",
    "NeonEncoding: EOR bitwise 8B",
    "NeonEncoding: INS lane insert 4S idx=0",
    "NeonEncoding: INS lane insert 4S idx=2",
    "NeonEncoding: MOVI immediate 16B",
    "NeonEncoding: MOVI immediate 8B",
    "NeonEncoding: MUL lane decomposition 4S",
    "NeonEncoding: MUL lane decomposition 8H",
    "NeonEncoding: NOT bitwise 16B",
    "NeonEncoding: NOT bitwise 8B",
    "NeonEncoding: ORR bitwise 16B",
    "NeonEncoding: ORR bitwise 8B",
    "NeonEncoding: SUB lane decomposition 16B",
    "NeonEncoding: SUB lane decomposition 4S",
    // Sdiv_I32/I64 -> SDIVWrr/Xrr removed 2026-07-12: their lowering proofs are
    // no longer degenerate (a genuine machine model, not an X==X identity), so
    // the identity exemption was DEAD and masking a possible regression
    // (genuine_allowlist_is_tight_and_live). Coverage still holds via the
    // genuine proof. (Udiv siblings removed below.)
    "Sextend_I16_to_I32 -> SXTH",
    "Sextend_I16_to_I64 -> SXTH",
    "Sextend_I32_to_I64 -> SXTW",
    "Sextend_I8_to_I32 -> SXTB",
    "Sextend_I8_to_I64 -> SXTB",
    "SextractBits{lsb=11,width=23}_I64 -> SBFM (64-bit)",
    "SextractBits{lsb=2,width=4}_I8 -> SBFM (8-bit)",
    "SextractBits{lsb=3,width=7}_I16 -> SBFM (16-bit)",
    "SextractBits{lsb=7,width=13}_I32 -> SBFM (32-bit)",
    "Srem_I16 -> SDIV+MSUB (16-bit)",
    "Srem_I32 -> SDIV+MSUB (32-bit)",
    "Srem_I64 -> SDIV+MSUB (64-bit)",
    "Srem_I8 -> SDIV+MSUB (8-bit)",
    // Udiv_I32/I64 -> UDIVWrr/Xrr removed 2026-07-12 (dead identity exemption;
    // see the Sdiv note above).
    "Urem_I16 -> UDIV+MSUB (16-bit)",
    "Urem_I32 -> UDIV+MSUB (32-bit)",
    "Urem_I64 -> UDIV+MSUB (64-bit)",
    "Urem_I8 -> UDIV+MSUB (8-bit)",
    "VectorAdd -> NEON ADD.2S",
    "VectorAdd -> NEON ADD.4S",
    "VectorAnd -> NEON AND.16B",
    "VectorAnd -> NEON AND.8B",
    "VectorBic -> NEON BIC.16B",
    "VectorBic -> NEON BIC.8B",
    "VectorCmge -> NEON CMGE.4H",
    "VectorCmge -> NEON CMGE.8H",
    "VectorCmgt -> NEON CMGT.2S",
    "VectorCmgt -> NEON CMGT.4S",
    "VectorMla -> NEON MLA.4S",
    "VectorMla -> NEON MLA.8B",
    "VectorMul -> NEON MUL.16B",
    "VectorMul -> NEON MUL.8B",
    "VectorNeg -> NEON NEG.2D",
    "VectorNeg -> NEON NEG.2S",
    "VectorOr -> NEON ORR.16B",
    "VectorOr -> NEON ORR.8B",
    "VectorShl -> NEON SHL.4H #imm=4",
    "VectorShl -> NEON SHL.4S #imm=8",
    "VectorSmax -> NEON SMAX.16B",
    "VectorSmax -> NEON SMAX.2S",
    "VectorSmin -> NEON SMIN.4H",
    "VectorSmin -> NEON SMIN.4S",
    "VectorSshr -> NEON SSHR.2S #imm=1",
    "VectorSshr -> NEON SSHR.4S #imm=4",
    "VectorSshr -> NEON SSHR.8H #imm=4",
    "VectorSub -> NEON SUB.4H",
    "VectorSub -> NEON SUB.8H",
    "VectorUmax -> NEON UMAX.4H",
    "VectorUmax -> NEON UMAX.4S",
    "VectorUmin -> NEON UMIN.8B",
    "VectorUmin -> NEON UMIN.8H",
    "VectorUshr -> NEON USHR.2D #imm=16",
    "VectorUshr -> NEON USHR.4S #imm=2",
    "VectorUshr -> NEON USHR.8B #imm=2",
    "VectorXor -> NEON EOR.16B",
    "VectorXor -> NEON EOR.8B",
    "Vectorize: ScalarAdd -> NEON ADD.2D",
    "Vectorize: ScalarAdd -> NEON ADD.4S",
    "Vectorize: ScalarAdd -> NEON ADD.8H",
    "Vectorize: ScalarAnd -> NEON AND.16B",
    "Vectorize: ScalarAnd -> NEON AND.8B",
    "Vectorize: ScalarBic -> NEON BIC.16B",
    "Vectorize: ScalarBic -> NEON BIC.8B",
    "Vectorize: ScalarCmge -> NEON CMGE.4S",
    "Vectorize: ScalarCmge -> NEON CMGE.8H",
    "Vectorize: ScalarCmgt -> NEON CMGT.2D",
    "Vectorize: ScalarCmgt -> NEON CMGT.4S",
    "Vectorize: ScalarEor -> NEON EOR.16B",
    "Vectorize: ScalarEor -> NEON EOR.8B",
    "Vectorize: ScalarMla -> NEON MLA.4S",
    "Vectorize: ScalarMla -> NEON MLA.8H",
    "Vectorize: ScalarMul -> NEON MUL.16B",
    "Vectorize: ScalarMul -> NEON MUL.4S",
    "Vectorize: ScalarMul -> NEON MUL.8H",
    "Vectorize: ScalarNeg -> NEON NEG.2D",
    "Vectorize: ScalarNeg -> NEON NEG.4S",
    "Vectorize: ScalarOrr -> NEON ORR.16B",
    "Vectorize: ScalarOrr -> NEON ORR.8B",
    "Vectorize: ScalarShl -> NEON SHL.4S #imm=8",
    "Vectorize: ScalarShl -> NEON SHL.8H #imm=4",
    "Vectorize: ScalarSmax -> NEON SMAX.4S",
    "Vectorize: ScalarSmax -> NEON SMAX.8H",
    "Vectorize: ScalarSmin -> NEON SMIN.4S",
    "Vectorize: ScalarSmin -> NEON SMIN.8H",
    "Vectorize: ScalarSshr -> NEON SSHR.4S #imm=1",
    "Vectorize: ScalarSshr -> NEON SSHR.8H #imm=4",
    "Vectorize: ScalarSub -> NEON SUB.2D",
    "Vectorize: ScalarSub -> NEON SUB.4S",
    "Vectorize: ScalarSub -> NEON SUB.8H",
    "Vectorize: ScalarUmax -> NEON UMAX.16B",
    "Vectorize: ScalarUmax -> NEON UMAX.4S",
    "Vectorize: ScalarUmin -> NEON UMIN.16B",
    "Vectorize: ScalarUmin -> NEON UMIN.4S",
    "Vectorize: ScalarUshr -> NEON USHR.2D #imm=16",
    "Vectorize: ScalarUshr -> NEON USHR.4S #imm=4",
    "x86_64: AtomicLoad_I16 -> MOV r,[mem]",
    "x86_64: AtomicLoad_I32 -> MOV r,[mem]",
    "x86_64: AtomicLoad_I64 -> MOV r,[mem]",
    "x86_64: AtomicLoad_I8 -> MOV r,[mem]",
    "x86_64: AtomicStore_I16 -> MOV [mem],r",
    "x86_64: AtomicStore_I32 -> MOV [mem],r",
    "x86_64: AtomicStore_I64 -> MOV [mem],r",
    "x86_64: AtomicStore_I8 -> MOV [mem],r",
    "x86_64: BandNot_B1 -> NOT+AND (1-bit)",
    "x86_64: BandNot_I16 -> NOT+AND (16-bit)",
    "x86_64: BandNot_I32 -> NOT+AND r32,r32",
    "x86_64: BandNot_I64 -> NOT+AND r64,r64",
    "x86_64: BandNot_I8 -> NOT+AND (8-bit)",
    "x86_64: Band_I16 -> AND (16-bit)",
    "x86_64: Band_I32 -> AND r32,r32",
    "x86_64: Band_I64 -> AND r64,r64",
    "x86_64: Band_I8 -> AND (8-bit)",
    "x86_64: Bnot_I32 -> NOT r32",
    "x86_64: Bnot_I64 -> NOT r64",
    "x86_64: BorNot_B1 -> NOT+OR (1-bit)",
    "x86_64: BorNot_I16 -> NOT+OR (16-bit)",
    "x86_64: BorNot_I32 -> NOT+OR r32,r32",
    "x86_64: BorNot_I64 -> NOT+OR r64,r64",
    "x86_64: BorNot_I8 -> NOT+OR (8-bit)",
    "x86_64: Bor_I16 -> OR (16-bit)",
    "x86_64: Bor_I32 -> OR r32,r32",
    "x86_64: Bor_I64 -> OR r64,r64",
    "x86_64: Bor_I8 -> OR (8-bit)",
    "x86_64: Bxor_I16 -> XOR (16-bit)",
    "x86_64: Bxor_I32 -> XOR r32,r32",
    "x86_64: Bxor_I64 -> XOR r64,r64",
    "x86_64: Bxor_I8 -> XOR (8-bit)",
    "x86_64: CMOVcc bitwise select",
    "x86_64: CMOVcc32 bitwise select",
    "x86_64: CMP+SETcc_NP_I32",
    "x86_64: CMP+SETcc_NP_I8",
    "x86_64: CMP+SETcc_P_I32",
    "x86_64: CMP+SETcc_P_I8",
    "x86_64: CMP_CF_writes_I32",
    "x86_64: CMP_OF_writes_I32",
    "x86_64: CMP_PF_flag_I32",
    "x86_64: CMP_PF_flag_I8",
    "x86_64: CMP_SF_writes_I32",
    "x86_64: CMP_ZF_writes_I32",
    "x86_64: CVTSD2SI_RNE_I64 -> fp_to_sbv(RNE) r64,xmm",
    "x86_64: CVTSS2SI_RNE_I64 -> fp_to_sbv(RNE) r64,xmm",
    "x86_64: Copy_F32 -> MOVSS xmm,xmm preserves scalar bits",
    "x86_64: Copy_F64 -> MOVSD xmm,xmm preserves scalar bits",
    "x86_64: Copy_I32 -> MOV r32,r32 preserves bits",
    "x86_64: Copy_I64 -> MOV r64,r64 preserves bits",
    "x86_64: Ctlz_I32 -> LZCNT r,r",
    "x86_64: Ctlz_I64 -> LZCNT r,r",
    "x86_64: Ctlz_I8 -> LZCNT r,r",
    "x86_64: Ctpop_I16 -> POPCNT r,r",
    "x86_64: Ctpop_I32 -> POPCNT r,r",
    "x86_64: Ctpop_I64 -> POPCNT r,r",
    "x86_64: Ctpop_I8 -> POPCNT r,r",
    "x86_64: Cttz_I32 (nonzero) -> BSF r,r",
    "x86_64: Cttz_I32 -> TZCNT r,r",
    "x86_64: Cttz_I64 (nonzero) -> BSF r,r",
    "x86_64: Cttz_I64 -> TZCNT r,r",
    "x86_64: Cttz_I8 (nonzero) -> BSF r,r",
    "x86_64: Cttz_I8 -> TZCNT r,r",
    "x86_64: ExtractBits{lsb=11,width=23}_I64 -> SHR+AND",
    "x86_64: ExtractBits{lsb=7,width=13}_I32 -> SHR+AND",
    "x86_64: FCeil_F32 -> ROUNDSS xmm,xmm,ceil",
    "x86_64: FCeil_F64 -> ROUNDSD xmm,xmm,ceil",
    "x86_64: FFloor_F32 -> ROUNDSS xmm,xmm,floor",
    "x86_64: FFloor_F64 -> ROUNDSD xmm,xmm,floor",
    "x86_64: FPExt_F64_F32 -> CVTSS2SD xmm,xmm",
    "x86_64: FPTrunc_F32_F64 -> CVTSD2SS xmm,xmm",
    "x86_64: FTrunc_F32 -> ROUNDSS xmm,xmm,trunc",
    "x86_64: FTrunc_F64 -> ROUNDSD xmm,xmm,trunc",
    "x86_64: Fabs_F32 -> ANDPS (abs)",
    "x86_64: Fabs_F64 -> ANDPD (abs)",
    "x86_64: Fadd_F32 -> ADDSS xmm,xmm",
    "x86_64: Fadd_F64 -> ADDSD xmm,xmm",
    "x86_64: FcvtFromInt_F32_I32 -> CVTSI2SS xmm,r32",
    "x86_64: FcvtFromInt_F32_I64 -> CVTSI2SS xmm,r64",
    "x86_64: FcvtFromInt_F64_I32 -> CVTSI2SD xmm,r32",
    "x86_64: FcvtFromInt_F64_I64 -> CVTSI2SD xmm,r64",
    "x86_64: FcvtToInt_I32_F32 -> CVTTSS2SI r32,xmm",
    "x86_64: FcvtToInt_I32_F64 -> CVTTSD2SI r32,xmm",
    "x86_64: FcvtToInt_I64_F32 -> CVTTSS2SI r64,xmm",
    "x86_64: FcvtToInt_I64_F64 -> CVTTSD2SI r64,xmm",
    "x86_64: Fdiv_F32 -> DIVSS xmm,xmm",
    "x86_64: Fdiv_F64 -> DIVSD xmm,xmm",
    "x86_64: Fmul_F32 -> MULSS xmm,xmm",
    "x86_64: Fmul_F64 -> MULSD xmm,xmm",
    "x86_64: Fneg_F32 -> XORPS (negate)",
    "x86_64: Fneg_F64 -> XORPD (negate)",
    "x86_64: Fsqrt_F32 -> SQRTSS xmm,xmm",
    "x86_64: Fsqrt_F64 -> SQRTSD xmm,xmm",
    "x86_64: Fsub_F32 -> SUBSS xmm,xmm",
    "x86_64: Fsub_F64 -> SUBSD xmm,xmm",
    "x86_64: Iadd_I16 -> ADD (16-bit)",
    "x86_64: Iadd_I32 -> ADD r32,r32",
    "x86_64: Iadd_I64 -> ADD r64,r64",
    "x86_64: Iadd_I8 -> ADD (8-bit)",
    "x86_64: Icmp_ULT_I32 -> CMP+SETB",
    "x86_64: Icmp_ULT_I64 -> CMP+SETB",
    "x86_64: Imul_I16 -> IMUL (16-bit)",
    "x86_64: Imul_I32 -> IMUL r32,r32",
    "x86_64: Imul_I32_Imm -> IMUL r32,r/m32,42",
    "x86_64: Imul_I64 -> IMUL r64,r64",
    "x86_64: Imul_I64_Imm -> IMUL r64,r/m64,42",
    "x86_64: Imul_I8 -> IMUL (8-bit)",
    "x86_64: InsertBits{lsb=11,width=23}_I64 -> AND+AND+SHL+OR",
    "x86_64: InsertBits{lsb=11,width=23}_I64(dst,dst) -> AND+AND+SHL+OR",
    "x86_64: InsertBits{lsb=7,width=13}_I32 -> AND+AND+SHL+OR",
    "x86_64: InsertBits{lsb=7,width=13}_I32(dst,dst) -> AND+AND+SHL+OR",
    "x86_64: Ishl_I16 -> SHL (16-bit)",
    "x86_64: Ishl_I32 -> SHL r32,CL",
    "x86_64: Ishl_I64 -> SHL r64,CL",
    "x86_64: Ishl_I8 -> SHL (8-bit)",
    "x86_64: Isub_I16 -> SUB (16-bit)",
    "x86_64: Isub_I32 -> SUB r32,r32",
    "x86_64: Isub_I64 -> SUB r64,r64",
    "x86_64: Isub_I8 -> SUB (8-bit)",
    "x86_64: Load_F32 -> MOVSS xmm,[r64+disp32]",
    "x86_64: Load_F64 -> MOVSD xmm,[r64+disp32]",
    "x86_64: Load_I16 -> MOV r16,[r64+disp32]",
    "x86_64: Load_I32 -> MOV r32,[r64+disp32]",
    "x86_64: Load_I64 -> MOV r64,[r64+disp32]",
    "x86_64: Load_I8 -> MOV r8,[r64+disp32]",
    "x86_64: Neg_I32 -> NEG r32",
    "x86_64: Neg_I64 -> NEG r64",
    "x86_64: Sdiv_I32 -> IDIV r32 (quotient)",
    "x86_64: Sdiv_I64 -> IDIV r64 (quotient)",
    // SLICE 3 (fences). MFENCE's SINGLE-THREAD data-flow semantics IS the
    // identity on the (register, memory) state — it writes no GPR/XMM/flag and no
    // memory byte (Intel SDM 8.2.5: MFENCE is purely an ordering barrier). So the
    // faithful single-thread obligation (state-after == state-before) is
    // necessarily structurally degenerate, EXACTLY like the audited
    // `AtomicLoad_* -> MOV r,[mem]` / reg-reg copy identities above: there is no
    // second independent encoder to make the two sides differ. It is NOT the
    // retracted #62 `bv_const(0x0FAEF0)==bv_const(...)` encoding tautology — that
    // compared the instruction's ENCODING BYTES to themselves and had no state to
    // clobber, so nothing could ever refute it. THIS obligation models MFENCE's
    // register/memory TRANSITION FUNCTION over symbolic state; its non-vacuity is
    // witnessed by the refuting negative controls
    // (`proof_x86_mfence_clobbers_register_refutes` / `_memory_refutes`): a
    // "fence" that zeroed a register or overwrote the fenced byte is structurally
    // distinct and REFUTES. The cross-thread ORDERING guarantee MFENCE also
    // provides is a separate architectural axiom, deliberately NOT modeled here.
    "x86_64: SeqCst fence -> MFENCE single-thread identity",
    "x86_64: Sextend_I16_to_I32 -> MOVSX r32,r/m16",
    "x86_64: Sextend_I16_to_I64 -> MOVSX r64,r/m16",
    "x86_64: Sextend_I32_to_I64 -> MOVSXD r64,r/m32",
    "x86_64: Sextend_I8_to_I32 -> MOVSX r32,r/m8",
    "x86_64: Sextend_I8_to_I64 -> MOVSX r64,r/m8",
    "x86_64: Srem_I32 -> IDIV r32 (remainder)",
    "x86_64: Srem_I64 -> IDIV r64 (remainder)",
    "x86_64: Sshr_I16 -> SAR (16-bit)",
    "x86_64: Sshr_I32 -> SAR r32,CL",
    "x86_64: Sshr_I64 -> SAR r64,CL",
    "x86_64: Sshr_I8 -> SAR (8-bit)",
    "x86_64: Store_F32 -> MOVSS [r64+disp32],xmm",
    "x86_64: Store_F64 -> MOVSD [r64+disp32],xmm",
    "x86_64: Store_I16 -> MOV [r64+disp32],r16",
    "x86_64: Store_I32 -> MOV [r64+disp32],r32",
    "x86_64: Store_I64 -> MOV [r64+disp32],r64",
    "x86_64: Store_I8 -> MOV [r64+disp32],r8",
    "x86_64: Udiv_I32 -> DIV r32 (quotient)",
    "x86_64: Udiv_I64 -> DIV r64 (quotient)",
    "x86_64: Uextend_I16_to_I32 -> MOVZX r32,r/m16",
    "x86_64: Uextend_I16_to_I64 -> MOVZX r64,r/m16",
    "x86_64: Uextend_I8_to_I32 -> MOVZX r32,r/m8",
    "x86_64: Uextend_I8_to_I64 -> MOVZX r64,r/m8",
    "x86_64: Urem_I32 -> DIV r32 (remainder)",
    "x86_64: Urem_I64 -> DIV r64 (remainder)",
    "x86_64: Ushr_I16 -> SHR (16-bit)",
    "x86_64: Ushr_I32 -> SHR r32,CL",
    "x86_64: Ushr_I64 -> SHR r64,CL",
    "x86_64: Ushr_I8 -> SHR (8-bit)",
    "x86_64: V128 Band -> ANDPD xmm,xmm",
    "x86_64: V128 Band -> ANDPS xmm,xmm",
    "x86_64: V128 Band -> PAND xmm,xmm",
    "x86_64: V128 Bor -> POR xmm,xmm",
    "x86_64: V128 Bxor -> PXOR xmm,xmm",
    "x86_64: V16I8Add -> PADDB xmm,xmm",
    "x86_64: V16I8Icmp_Eq -> PCMPEQB",
    "x86_64: V16I8Icmp_Sgt -> PCMPGTB",
    "x86_64: V16I8Sub -> PSUBB xmm,xmm",
    "x86_64: V2F64Fadd -> ADDPD xmm,xmm (per-lane)",
    "x86_64: V2F64Fdiv -> DIVPD xmm,xmm (per-lane)",
    "x86_64: V2F64Fmul -> MULPD xmm,xmm (per-lane)",
    "x86_64: V2F64Fsub -> SUBPD xmm,xmm (per-lane)",
    "x86_64: V2I64Add -> PADDQ xmm,xmm",
    "x86_64: V2I64ExtractLane{lane=0} -> MOVQ",
    "x86_64: V2I64Icmp_Eq -> PCMPEQQ",
    "x86_64: V2I64Icmp_Sgt -> PCMPGTQ",
    "x86_64: V2I64Mul -> scalar lane IMUL + qword repack",
    "x86_64: V2I64Sub -> PSUBQ xmm,xmm",
    "x86_64: V4F32Fadd -> ADDPS xmm,xmm (per-lane)",
    "x86_64: V4F32Fdiv -> DIVPS xmm,xmm (per-lane)",
    "x86_64: V4F32Fmul -> MULPS xmm,xmm (per-lane)",
    "x86_64: V4F32Fsub -> SUBPS xmm,xmm (per-lane)",
    "x86_64: V4I32 Ishl -> scalarized SHL lanes + reassembly",
    "x86_64: V4I32 Sshr -> scalarized SAR lanes + reassembly",
    "x86_64: V4I32 Ushr -> scalarized SHR lanes + reassembly",
    "x86_64: V4I32Add -> PADDD xmm,xmm",
    "x86_64: V4I32ExtractLane{lane=0} -> MOVD",
    "x86_64: V4I32Icmp_Eq -> PCMPEQD",
    "x86_64: V4I32Icmp_Sgt -> PCMPGTD",
    "x86_64: V4I32Mul -> PMULLD xmm,xmm",
    "x86_64: V4I32Sub -> PSUBD xmm,xmm",
    "x86_64: V8I16Add -> PADDW xmm,xmm",
    "x86_64: V8I16Icmp_Eq -> PCMPEQW",
    "x86_64: V8I16Icmp_Sgt -> PCMPGTW",
    "x86_64: V8I16Sub -> PSUBW xmm,xmm",
];

/// Returns true if `name` is on the audited genuine-identity classification list.
///
/// STRICT (task #61): this is used ONLY by the `non_degeneracy_violations`
/// classification gate to recognize disclosed/expected degenerate identities. It
/// grants NO proven/covered/verified status — counting is purely structural via
/// [`ProofObligation::is_genuinely_proven`].
pub fn is_genuine_identity(name: &str) -> bool {
    GENUINE_IDENTITY_ALLOWLIST.contains(&name)
}

// ---------------------------------------------------------------------------
// Known-degenerate DEBT LEDGER (task #53 follow-up) — NOT a genuineness claim
// ---------------------------------------------------------------------------
//
// These proofs are currently DEGENERATE (`trust_ir_expr == aarch64_expr`) and
// are NOT genuine 1:1 identities — they are the audited SUSPICIOUS f81e45b
// X==X class (CSE/GVN/copy-prop/DCE/CFG/loop/TCO/call-arg-placement/
// if-conversion/cmp-combine/strength-reduce-no-change/scheduling/frame/regalloc/
// addr-mode/load-store/MachO/Fence/ANE-FP16 self-equalities, plus the x86/riscv
// control-flow target==target and constant-materialize tautologies). They prove
// NOTHING about a lowering: both sides are the same constructed expression with
// no independent machine encoder, so no wrong opcode/instruction/placement could
// ever refute.
//
// This ledger exists SOLELY so the universal non-degeneracy gate can ship as a
// fail-closed RATCHET without a flag day over the whole legacy registry:
//
//   * The gate FAILS if any degenerate proof appears that is on NEITHER
//     GENUINE_IDENTITY_ALLOWLIST NOR this ledger — so a FUTURE degenerate proof
//     can never silently register (fail-closed for new code).
//   * The gate FAILS if this ledger ever GROWS past its pinned length — debt may
//     only SHRINK, never expand.
//   * No name may appear on BOTH lists (a debt entry must never be silently
//     reclassified as "genuine").
//
// CRITICAL: presence here is an explicit admission that the proof is BROKEN and
// must be FIXED with a faithful independent-encoder obligation (model the
// destination register for call/TCO placement; encode the real ANE error bound
// in SMT; encode the actual fence/MachO bytes via the emitter; model the
// value-numbering/liveness/dominance side-analysis for the optimizer passes).
// As each is fixed (made non-degenerate) it MUST be deleted from this ledger and
// the pinned length lowered. This is NOT an exemption that makes the proof count
// as evidence — it is a tracked, shrinking debt list with a fail-closed ratchet.
/// Audited SUSPICIOUS degenerate proofs awaiting a faithful (independent-encoder)
/// re-derivation. See the module-level note above: this is a SHRINKING debt
/// ledger, NOT a genuineness allowlist. Fixing a proof removes it from here.
pub const KNOWN_DEGENERATE_PENDING_FIX: &[&str] = &[
    // #62 capstone: EMPTY. Every entry that was here was a degenerate X==X
    // self-equality (the f81e45b class) that proved nothing about a lowering.
    // They have all been RETRACTED — the non-lowering vacuous families (CSE/LICM/
    // GVN/DCE/CFG/Loop/TCO/IfConversion-self-eq/CopyProp/CallLowering/TCO/Frame/
    // RegAlloc/Scheduling/AddrMode/MachO/Fence/ANE-FP16/PureDeterminism/ConstFold-
    // tautology/ConstMaterialize/NZCV/Memory-self-equality/CmpCombine/x86-control-
    // flow+LEA+Fence) were DELETED from the proof builders, and the
    // reconstruction-superseded static lowerings (riscv ALU, AArch64 scalar shift,
    // AArch64 UGE/HS cmp+branch) were removed because operand reconstruction is now
    // the genuine coverage. The ledger is empty: the database no longer contains a
    // single degenerate-debt proof. The universal non-degeneracy gate now passes
    // with EVERY degenerate proof being an audited GENUINE_IDENTITY_ALLOWLIST 1:1
    // identity; nothing remains "pending fix".
];

/// Returns true if `name` is on the known-degenerate debt ledger.
pub fn is_known_degenerate_debt(name: &str) -> bool {
    KNOWN_DEGENERATE_PENDING_FIX.contains(&name)
}

/// A degenerate-but-unallowlisted proof found by the universal gate: its
/// `trust_ir_expr` is structurally identical to its `aarch64_expr` and its name
/// is NOT on [`GENUINE_IDENTITY_ALLOWLIST`]. Such a proof FAILS the gate.
#[derive(Debug, Clone)]
pub struct DegeneracyViolation {
    /// The offending proof's name.
    pub name: String,
}

impl ProofDatabase {
    /// Universal non-degeneracy gate (Strategy C, task #53).
    ///
    /// Returns every registered proof that is degenerate
    /// (`trust_ir_expr == aarch64_expr`) AND absent from BOTH
    /// [`GENUINE_IDENTITY_ALLOWLIST`] (audited genuine 1:1 identities) and
    /// [`KNOWN_DEGENERATE_PENDING_FIX`] (the tracked, shrinking debt ledger of
    /// suspicious self-equalities awaiting a faithful re-derivation).
    ///
    /// An empty result means the gate passes: every degenerate proof is either
    /// an audited genuine identity or a pinned, disclosed debt entry. A NON-empty
    /// result is a fail-closed violation — a NEW degenerate proof proving nothing
    /// has silently registered without being classified, which the gate test
    /// rejects. (The debt ledger is additionally pinned by length so it can only
    /// shrink; fixing a suspicious proof removes it from the ledger.)
    pub fn non_degeneracy_violations(&self) -> Vec<DegeneracyViolation> {
        self.proofs
            .iter()
            .filter(|p| p.obligation.trust_ir_expr == p.obligation.aarch64_expr)
            .filter(|p| {
                !is_genuine_identity(&p.obligation.name)
                    && !is_known_degenerate_debt(&p.obligation.name)
            })
            .map(|p| DegeneracyViolation {
                name: p.obligation.name.clone(),
            })
            .collect()
    }

    /// Returns the names of every degenerate proof (structurally equal sides),
    /// regardless of allowlist membership. Used by the gate test to assert the
    /// allowlist is TIGHT (no allowlisted name is actually non-degenerate, i.e.
    /// no dead entries) and that the genuine identities really are degenerate.
    pub fn degenerate_proof_names(&self) -> Vec<String> {
        self.proofs
            .iter()
            .filter(|p| p.obligation.trust_ir_expr == p.obligation.aarch64_expr)
            .map(|p| p.obligation.name.clone())
            .collect()
    }
}

/// Determine the maximum input bit-width for a proof obligation.
///
/// Returns 0 for FP-only proofs (no bitvector inputs).
fn max_input_width(obligation: &ProofObligation) -> u32 {
    obligation.inputs.iter().map(|(_, w)| *w).max().unwrap_or(0)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn with_large_stack(f: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name("proof-db-audit".to_string())
            .stack_size(32 * 1024 * 1024)
            .spawn(f)
            .expect("failed to spawn large-stack proof database test")
            .join()
            .expect("large-stack proof database test panicked");
    }

    #[test]
    fn test_x86_64_bitfield_query_hooks_are_ready() {
        with_large_stack(|| {
            let db = ProofDatabase::new();
            let candidates = db.by_category(ProofCategory::X8664Lowering);
            let matched = X86_BITFIELD_REPRESENTATIVE_PROOF_QUERIES
                .iter()
                .filter(|(_, query)| {
                    candidates
                        .iter()
                        .any(|p| p.obligation.name.contains(*query))
                })
                .count();

            assert_eq!(
                matched,
                X86_BITFIELD_REPRESENTATIVE_PROOF_QUERIES.len(),
                "missing x86-64 bitfield proof registration: matched {matched}/{} representative queries",
                X86_BITFIELD_REPRESENTATIVE_PROOF_QUERIES.len()
            );
        });
    }

    // =======================================================================
    // Construction and basic queries
    // =======================================================================

    #[test]
    fn test_database_is_non_empty() {
        let db = ProofDatabase::new();
        assert!(!db.is_empty(), "database should contain proofs");
        assert!(db.len() > 100, "expected 100+ proofs, got {}", db.len());
    }

    #[test]
    fn test_all_returns_same_count_as_len() {
        let db = ProofDatabase::new();
        assert_eq!(db.all().len(), db.len());
    }

    /// The `REGISTRARS` category table must match what the registrars actually
    /// emit. If it drifts, `for_categories` silently omits obligations a
    /// consumer expected, which turns a verified instruction into `Unverified`
    /// — fail-closed, but a real loss of coverage. This makes the table
    /// self-checking instead of a comment.
    #[test]
    fn registrar_category_table_matches_reality() {
        for (registrar, declared) in REGISTRARS {
            let mut produced = Vec::new();
            registrar(&mut produced);
            let mut actual: Vec<ProofCategory> = produced.iter().map(|p| p.category).collect();
            actual.sort_by_key(|c| c.name());
            actual.dedup();
            for cat in &actual {
                assert!(
                    declared.contains(cat),
                    "a registrar emits {} but the REGISTRARS table does not declare it — \
                     `for_categories` would omit those obligations",
                    cat.name()
                );
            }
        }
    }

    /// For EVERY category, the filtered database must be indistinguishable from
    /// the full one: same obligations, same order. Order is load-bearing —
    /// `resolve_db_proof` takes the FIRST name match.
    #[test]
    fn for_categories_matches_full_database() {
        let full = ProofDatabase::new();
        let mut categories: Vec<ProofCategory> = full.all().iter().map(|p| p.category).collect();
        categories.sort_by_key(|c| c.name());
        categories.dedup();
        assert!(
            !categories.is_empty(),
            "the full database must not be empty"
        );

        for cat in categories {
            let filtered = ProofDatabase::for_categories(&[cat]);
            let want: Vec<&str> = full
                .by_category(cat)
                .iter()
                .map(|p| p.obligation.name.as_str())
                .collect();
            let got: Vec<&str> = filtered
                .by_category(cat)
                .iter()
                .map(|p| p.obligation.name.as_str())
                .collect();
            assert_eq!(
                got,
                want,
                "for_categories({}) must yield the same obligations in the same order as new()",
                cat.name()
            );
            // And nothing else may leak in: a filtered database holds only what
            // was asked for, which is the entire point.
            assert_eq!(
                filtered.all().len(),
                got.len(),
                "for_categories({}) must hold ONLY that category",
                cat.name()
            );
        }
    }

    /// The x86-64 lane's actual request. Guards the specific saving this was
    /// built for, and fails loudly if the x86 database ever needs more.
    #[test]
    fn x86_only_database_is_a_strict_subset_of_the_full_one() {
        let full = ProofDatabase::new();
        let x86 = ProofDatabase::for_categories(&[ProofCategory::X8664Lowering]);
        assert_eq!(
            x86.all().len(),
            full.by_category(ProofCategory::X8664Lowering).len()
        );
        assert!(
            x86.all().len() * 2 < full.all().len(),
            "x86 database ({}) should be far smaller than the full one ({})",
            x86.all().len(),
            full.all().len()
        );
    }

    #[test]
    fn test_default_same_as_new() {
        let db1 = ProofDatabase::new();
        let db2 = ProofDatabase::default();
        assert_eq!(db1.len(), db2.len());
    }

    // =======================================================================
    // Category-specific counts
    // =======================================================================

    #[test]
    fn test_arithmetic_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::Arithmetic);
        // 4 ops x 4 widths = 16 (excluding division)
        assert!(
            count >= 16,
            "expected >= 16 arithmetic proofs, got {}",
            count
        );
    }

    #[test]
    fn test_division_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::Division);
        // Coverage floor: sdiv/udiv x I32/I64 = 4, plus urem/srem at
        // I8/I16/I32/I64 = 8.
        // This category can grow as new remainder/division widths land, so guard
        // against regressions without freezing the exact total.
        assert!(count >= 12, "expected >= 12 division proofs, got {}", count);
    }

    #[test]
    fn test_fp_lowering_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::FloatingPoint);
        // Coverage floor: historic baseline 38
        // (fadd/fsub/fmul/fdiv/fneg x F32/F64 = 10, plus 14 fcmp conditions x 2
        // sizes = 28; total 38). Grows monotonically as new FP lowerings land
        // (#418). Regression is still caught: any decrease fails.
        assert!(count >= 38, "expected >= 38 FP proofs, got {}", count);
    }

    #[test]
    fn test_comparison_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::Comparison);
        // 9 genuine conditions x 2 widths = 18 (the degenerate UGE/HS pair was
        // retracted in #62; CSet is reconstruction-credited).
        assert_eq!(count, 18, "expected 18 comparison proofs, got {}", count);
    }

    #[test]
    fn test_branch_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::Branch);
        // 9 genuine conditions x 2 widths = 18 (the degenerate UGE/B.HS pair was
        // retracted in #62; Bcc is reconstruction-credited).
        assert_eq!(count, 18, "expected 18 branch proofs, got {}", count);
    }

    #[test]
    fn test_peephole_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::Peephole);
        // Was 99; the degenerate "CSEL Xd,Xn,Xn,cond ≡ MOV" X==X was retracted in
        // #62, leaving 98.
        assert_eq!(count, 98, "expected 98 peephole proofs, got {}", count);
    }

    #[test]
    fn test_neon_lowering_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::NeonLowering);
        // 36 base + USHR.4S + SSHR.4S (the <4 x i32> lane-wise right shifts) = 38,
        // + 5 FAITHFUL per-lane-intent == whole-register bitwise proofs
        // (AndV/OrrV/EorV/BicV/NotV — the gate-credited NEON bitwise obligations) = 43,
        // + 16 FAITHFUL per-lane D-register-pair COMPUTE proofs (Add/Sub/Mul,
        // Cmeq {.4S + .16B}/Cmge/Cmgt/Cmhi/Cmhs, Smax/Smin/Umax/Umin,
        // Shl/Ushr/Sshr — the `.16B` byte-lane CMEQ is the count-if kernel's mask) = 59,
        // + 3 FAITHFUL popcount-fold proofs (CntV.16B + UaddlpV .16B->.8H + .8H->.4S) = 62,
        // + 1 FAITHFUL signed-abs proof (AbsV.4S) = 63,
        // + 1 FAITHFUL unsigned dot-product-accumulate proof (UdotV.4S) = 64,
        // + 3 FAITHFUL byte-window extract proofs (ExtV.16B #4/#8/#12) = 67,
        // + 10 FAITHFUL `.2D` (2 x i64) lane-wise compute proofs (Add/Sub,
        //   Cmeq/Cmge/Cmgt/Cmhi/Cmhs, Shl/Ushr/Sshr — the ops the i64 vectorizer
        //   paths emit at `.2D`) = 77,
        // + 2 FAITHFUL signed add-long-pairwise proofs (SaddlpV .16B->.8H and
        //   .8H->.4S — the sext(i8/i16) widening-reduction op) = 79,
        // + 1 FAITHFUL bitwise insert-if-true proof (BitV.16B — the i64 min/max
        //   reduction's tied-destination select) = 80,
        // + 30 FAITHFUL per-lane FP LANE-PLUMBING proofs (FaddV/FsubV/FmulV/
        //   FdivV/FcmgtV x {.4S lanes 0..4, .2D lanes 0..2} — the elementwise-FP
        //   vectorizer's ops; see all_neon_fp_lanewise_proofs' honesty note) = 110,
        // + 26 FAITHFUL `neon_fpred` per-lane obligations (FMLA/FMLS fused fp.fma,
        //   UCVTF/SCVTF int->FP, DupScalarD 64-bit lane copy, plus the added
        //   FP-reduction lane ops; DupScalarD x .2D 2 lanes, FMLA/FMLS and
        //   UCVTF/SCVTF x BOTH .2D 2 lanes and .4S 4 lanes) = 136,
        // + 20 FAITHFUL FMLA-by-lane obligations (FmlaLaneV .4S {4 sel x 4 dest = 16}
        //   + .2D {2 sel x 2 dest = 4} — fused fp broadcast-lane fma) = 156,
        // + 30 FAITHFUL per-(size,lane) NeonUmovGen extract obligations (UMOV
        //   lane->GPR: .16B 16 lanes + .8H 8 + .4S 4 + .2D 2, zero-extended; the
        //   op every NEON lane->scalar extract lowers through — reduction drains
        //   at .S/.D + V{16I8,8I16,4I32,2I64}ExtractLane isel at .B/.H/.S/.D) = 186,
        // + 4 FAITHFUL FCVTL/FCVTL2 f32->f64 widening obligations ({FCVTL low half,
        //   FCVTL2 high half} x .2D 2 lanes — the vector fpext the FP
        //   array-reduction vectorizer neon_farray emits for the widening dot) = 190,
        // + 4 FAITHFUL SMLAL/SMLAL2/UMLAL/UMLAL2 widening multiply-accumulate-long
        //   obligations (i32->i64 MAC, .4S -> .2D; one whole-register obligation per
        //   opcode with both .2D lanes concatenated — the widening dot the neon_array
        //   vectorizer emits for `s(i64) += ext(a_i32[i])*ext(b_i32[i])`) = 194,
        // + 2 FAITHFUL UADDW/UADDW2 widening add-wide obligations (u32->u64
        //   unsigned three-operand wide add, .4S -> .2D; one whole-register
        //   obligation per opcode with both .2D lanes concatenated — the widening
        //   abs-sum accumulate the neon_array TRACK D vectorizer emits for
        //   `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`) = 196,
        // + 2 FAITHFUL SADDW/SADDW2 SIGNED widening add-wide obligations
        //   (i32->i64 signed three-operand wide add, .4S -> .2D; one
        //   whole-register obligation per opcode with both .2D lanes
        //   concatenated — the widening condsum accumulate the neon_predsum
        //   vectorizer emits for `s(i64) += (a_i32[iv] as i64) [if pred]`,
        //   replacing the SMLAL-by-ones MAC) = 198,
        // + 1 Rev64V.4S pair-swap (the neon_butterfly AoS complex vectorizer's
        //   within-doubleword {rp,ip} element swap) = 199.
        // + 1 FAITHFUL MLA.4S vector multiply-accumulate obligation
        //   (tied-accumulator i32 MAC mod 2^32, all four .4S lanes concatenated
        //   — the MLA-by-mask condsum accumulate the neon_predsum vectorizer
        //   emits for the Gpr32 masked-add `s(i32) += a_i32[iv] [if pred]`,
        //   replacing the AND + ADD.4S pair; the accumulators hold the NEGATED
        //   sum, folded by one wrapping SubRR) = 200,
        // + 1 FAITHFUL UADALP.2D pairwise widening accumulate obligation
        //   (tied-accumulator u32-pair -> i64, .4S -> .2D, both .2D lanes
        //   concatenated — the abs-sum accumulate the neon_array TRACK D
        //   vectorizer emits, replacing the UADDW/UADDW2 pair; adjacent-pair
        //   grouping is a pure mod-2^64 reassociation under the both-lanes
        //   drain) = 202,
        // + 1 FAITHFUL RBIT.16B per-byte 8-bit reverse obligation (within-byte
        //   bit reversal — the neon-bitrev vectorizer's `a[i].reverse_bits()`
        //   over `[u8; N]`; per-bit D-half mirror SOURCE vs the SWAR machine;
        //   identity / byte-swap [REV16.8B] / 16-bit-lane-reverse refute
        //   controls) = 203,
        // + 2 FAITHFUL single-byte shifted-NEIGHBOR ExtV.16B obligations
        //   (#1 = `a[iv+1]` forward window / #15 = `a[iv-1]` backward window —
        //   the neon-bytesum stencil count-if's shifted-neighbor stream over a
        //   `[u8; N]`; same per-byte D-pair SOURCE vs the whole-register
        //   shift/OR machine; opposite-direction #1<->#15 / swapped-operand /
        //   identity refute controls) = 206,
        // + 2 FAITHFUL `.16B` byte-lane compute obligations (UshrVImm.16B #4 =
        //   the hex-nibble kernel's high-nibble isolate `b >> 4`, and CmhsV.16B =
        //   its hex-letter `nibble >= 10` mask; USHR-as-SSHR / CMHS-as-CMGE refute
        //   controls, both diverging on bytes `>= 0x80`) = 208,
        // + 2 FAITHFUL per-WORD byte-reverse obligations (Rev32V .16B + .8B — the
        //   i32 reverse_bits lowering's byte-order half, un-deferring NeonRev32V) = 210,
        // + 1 FAITHFUL cross-lane horizontal-reduce obligation (Umaxv.4S — the
        //   compare-mask any-lane collapse, un-deferring NeonUmaxv) = 211,
        // + 6 FAITHFUL selected-lane broadcast obligations (DupElem, every lane of
        //   both emitted arrangements, un-deferring NeonDupElem) = 217,
        // + 30 FAITHFUL GPR-broadcast round-trip obligations (DupGen, every lane of
        //   every emitted element size, un-deferring NeonDupGen and replacing its
        //   degenerate all-lanes==src identity) = 247,
        // + 30 FAITHFUL tied-destination lane-insert obligations (InsGen, every lane
        //   of every emitted element size, un-deferring NeonInsGen) = 277,
        // + 4 FAITHFUL byte-replicated-immediate obligations (Movi, un-deferring
        //   NeonMovi and replacing its degenerate replicated-byte identity) = 281,
        // + 4 PARTIAL post-index base-register writeback obligations (the four NEON
        //   post-index memory opcodes; these prove the base advance ONLY and those
        //   rows STAY explicitly deferred RED on the transfer itself) = 285.
        assert_eq!(
            count, 285,
            "expected 285 NEON lowering proofs, got {}",
            count
        );
    }

    #[test]
    fn test_vectorization_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::Vectorization);
        // 11 arithmetic + 14 bitwise + 6 shifts = 31 (may grow with new proofs)
        assert!(
            count >= 31,
            "expected >= 31 vectorization proofs, got {}",
            count
        );
    }

    #[test]
    fn test_memory_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::Memory);
        // Was 68; #62 retracted the 12 degenerate Load_I*/Store_I* [Xn,#imm] X==X,
        // WriteCombine_I32, and Aligned_ScaledOffset_I32 (14 total), leaving 54
        // genuine (roundtrip/non-interference/endianness/forwarding/subword/array).
        assert!(count >= 54, "expected >= 54 memory proofs, got {}", count);
    }

    #[test]
    fn test_memory_ldp_qf_abv_proofs_registered() {
        let db = ProofDatabase::new();
        let memory = db.by_category(ProofCategory::Memory);
        for expected in [
            (
                "LDP_QF_ABV_I32_offset0: two adjacent Load_I32 == LDP [Xn, #0]",
                32,
            ),
            (
                "LDP_QF_ABV_I64_offset0: two adjacent Load_I64 == LDP [Xn, #0]",
                64,
            ),
            (
                "LDP_QF_ABV_I64_scaled_offset2: two adjacent Load_I64 == LDP [Xn, #2]",
                64,
            ),
        ] {
            let proof = memory
                .iter()
                .find(|p| p.obligation.name == expected.0)
                .unwrap_or_else(|| panic!("Memory proof category missing {:?}", expected.0));
            assert!(
                proof
                    .obligation
                    .inputs
                    .contains(&("lane0_value".to_string(), expected.1)),
                "Memory proof {:?} missing symbolic lane0 input",
                expected.0
            );
            assert!(
                proof
                    .obligation
                    .inputs
                    .contains(&("lane1_value".to_string(), expected.1)),
                "Memory proof {:?} missing symbolic lane1 input",
                expected.0
            );
        }
    }

    // =======================================================================
    // Summary
    // =======================================================================

    #[test]
    fn test_summary_total_matches_len() {
        let db = ProofDatabase::new();
        let summary = db.summary();
        assert_eq!(summary.total, db.len());
    }

    #[test]
    fn test_summary_category_counts_sum_to_total() {
        let db = ProofDatabase::new();
        let summary = db.summary();
        let category_sum: usize = summary.by_category.iter().map(|(_, c)| c).sum();
        assert_eq!(
            category_sum, summary.total,
            "sum of category counts ({}) != total ({})",
            category_sum, summary.total
        );
    }

    #[test]
    fn test_summary_check_kind_counts_cover_all_proofs() {
        with_large_stack(|| {
            let db = ProofDatabase::new();
            let summary = db.summary();
            let check_kind_sum: usize = summary.by_check_kind.iter().map(|(_, c)| c).sum();
            assert_eq!(
                check_kind_sum + summary.uncategorized_check_kind_count,
                summary.total,
                "sum of check-kind counts ({}) + uncategorized ({}) != total ({})",
                check_kind_sum,
                summary.uncategorized_check_kind_count,
                summary.total
            );
            assert_eq!(
                summary.transval_compatible_count + summary.trust_cg_extension_count,
                check_kind_sum,
                "compatible + Trust Codegen extension check-kind counts should cover categorized proofs"
            );
        });
    }

    #[test]
    fn test_all_registered_proofs_have_transval_check_kind() {
        with_large_stack(|| {
            let db = ProofDatabase::new();
            let missing = db.uncategorized_check_kind();
            assert!(
                missing.is_empty(),
                "registered proofs missing TransvalCheckKind: {:?}",
                missing
                    .iter()
                    .take(10)
                    .map(|p| (p.category, p.obligation.name.as_str()))
                    .collect::<Vec<_>>()
            );
        });
    }

    #[test]
    fn test_registered_check_kind_matches_proof_family() {
        with_large_stack(|| {
            let db = ProofDatabase::new();
            let mismatches: Vec<_> = db
                .all()
                .iter()
                .filter(|p| p.obligation.category != Some(p.category.transval_check_kind()))
                .take(10)
                .map(|p| {
                    (
                        p.category,
                        p.category.transval_check_kind(),
                        p.obligation.category,
                        p.obligation.name.as_str(),
                    )
                })
                .collect();
            assert!(
                mismatches.is_empty(),
                "registered proofs with unexpected TransvalCheckKind: {:?}",
                mismatches
            );
        });
    }

    #[test]
    fn test_summary_width_counts_sum_to_total() {
        let db = ProofDatabase::new();
        let summary = db.summary();
        let width_sum: usize = summary.by_width.iter().map(|(_, c)| c).sum();
        assert_eq!(
            width_sum, summary.total,
            "sum of width counts ({}) != total ({})",
            width_sum, summary.total
        );
    }

    #[test]
    fn test_summary_fp_proofs_exist() {
        let db = ProofDatabase::new();
        let summary = db.summary();
        assert!(summary.fp_proof_count > 0, "expected at least one FP proof");
    }

    #[test]
    fn test_summary_preconditioned_proofs_exist() {
        let db = ProofDatabase::new();
        let summary = db.summary();
        // Division proofs have non-zero divisor preconditions
        assert!(
            summary.preconditioned_count > 0,
            "expected at least one preconditioned proof"
        );
    }

    // =======================================================================
    // Search
    // =======================================================================

    #[test]
    fn test_search_add() {
        let db = ProofDatabase::new();
        let results = db.search("add");
        assert!(!results.is_empty(), "search for 'add' should find proofs");
    }

    #[test]
    fn test_search_case_insensitive() {
        let db = ProofDatabase::new();
        let upper = db.search("NEON");
        let lower = db.search("neon");
        assert_eq!(
            upper.len(),
            lower.len(),
            "search should be case-insensitive"
        );
    }

    #[test]
    fn test_search_no_match() {
        let db = ProofDatabase::new();
        let results = db.search("zzz_nonexistent_xyz");
        assert!(results.is_empty(), "bogus query should return no results");
    }

    // =======================================================================
    // Names
    // =======================================================================

    #[test]
    fn test_names_sorted() {
        let db = ProofDatabase::new();
        let names = db.names();
        let mut sorted = names.clone();
        sorted.sort();
        assert_eq!(names, sorted, "names() should return sorted list");
    }

    #[test]
    fn test_names_count_matches_len() {
        let db = ProofDatabase::new();
        assert_eq!(db.names().len(), db.len());
    }

    // =======================================================================
    // Every category has at least one proof
    // =======================================================================

    #[test]
    fn test_every_category_has_proofs() {
        let db = ProofDatabase::new();
        for cat in ProofCategory::all_categories() {
            let count = db.count_by_category(*cat);
            assert!(
                count > 0,
                "category {:?} has 0 proofs -- every category should have at least one",
                cat
            );
        }
    }

    // =======================================================================
    // ProofCategory::all_categories covers all variants
    // =======================================================================

    #[test]
    fn test_all_categories_is_exhaustive() {
        let categories = ProofCategory::all_categories();
        assert_eq!(
            categories.len(),
            35,
            "expected 35 categories: #71 added WebAssembly Lowering (54 genuine non-degenerate \
             wasm scalar refinement proofs). (5 fully-vacuous categories — NzcvFlags, \
             CopyPropagation, DeadCodeElimination, AnePrecision, TailCallOptimization — were \
             removed in #62 when their every X==X proof was retracted.) got {}",
            categories.len()
        );
    }

    #[test]
    fn test_bitwise_shift_proofs_count() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::BitwiseShift);
        // I8/I16: 7 ops x 2 widths (14) + BIC/ORN (4, #425/#407) = 18
        // I32/I64: 6 ops (no BNOT yet) x 2 widths (12) + BIC/ORN (4, #449) = 16
        // I8/I16/I32/I64 bitfield
        // (ExtractBits/SextractBits/InsertBits, #452/#435) = 12
        // Total was 46; the 12 scalar shift (Ishl/Ushr/Sshr I8..I64) proofs were
        // degenerate X==X and were RETRACTED in #62 (reconstruction-credited), so
        // the BitwiseShift category was 34 (22 bitwise/BIC/ORN + 12 bitfield).
        // +10 for the EOR-ROR shifted-register obligations (5 amounts x {W,X},
        // all_eor_ror_shift_proofs — the rotate-fusion peephole's EorRRShift) = 44.
        // +20 for the ADD/SUB-LSL shifted-register obligations (10 ADD + 10 SUB,
        // all_add_sub_lsl_shift_proofs — the shift-add/sub fusion peephole's
        // AddRRShift/SubRRShift) = 64.
        // +10 for the ADD-LSR shifted-register obligations (5 amounts x {W,X},
        // all_add_lsr_shift_proofs — the shift-ALU fusion peephole's
        // AddRRShiftLsr, the srem/sdiv magic sign-bit correction) = 74.
        assert_eq!(count, 74, "expected 74 bitwise/shift proofs, got {}", count);
    }

    // =======================================================================
    // Load/Store lowering proofs — wired via #422
    // =======================================================================

    /// Regression test for #422: the `lowering_proof::all_load_store_proofs`
    /// registry was an orphan for months. It still flows through
    /// `ProofDatabase::new()`, but #62 RETRACTED the 8 degenerate per-width
    /// "Load_I*/Store_I* -> LDR/STR*ui [Xn,#0]" X==X self-equalities (the machine
    /// side mirrored the spec with no independent address-mode encoder). The 2
    /// GENUINE store-then-load Roundtrip proofs remain and carry the real coverage.
    #[test]
    fn test_load_store_proofs_registered() {
        let db = ProofDatabase::new();
        let count = db.count_by_category(ProofCategory::LoadStoreLowering);
        assert_eq!(
            count, 2,
            "expected 2 genuine LoadStoreLowering Roundtrip proofs (8 degenerate \
             Load_I*/Store_I* X==X retracted in #62), got {}",
            count
        );
    }

    // =======================================================================
    // x86-64 lowering proofs — wired via #434 (analog of #422 for LoadStore)
    // =======================================================================

    /// Regression test for #434: the `x86_64_lowering_proofs::all_x86_64_proofs`
    /// registry was an orphan and not exercised by the default
    /// `cargo test -p trust-cg-verify` suite. Ensure it flows through
    /// `ProofDatabase::new()` and every obligation from the registry is
    /// represented under `ProofCategory::X8664Lowering`.
    ///
    /// Note: x86-64 remains opt-in (not default-on for full SMT proof) until
    /// AArch64 is default-on first — see #407, #340.
    #[test]
    fn test_x86_64_proofs_registered() {
        std::thread::Builder::new()
            .name("test_x86_64_proofs_registered".to_string())
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let db = ProofDatabase::new();
                let db_count = db.count_by_category(ProofCategory::X8664Lowering);
                let registry_count = crate::x86_64_lowering_proofs::all_x86_64_proofs().len();
                assert_eq!(
                    db_count, registry_count,
                    "ProofDatabase x86-64 count ({}) != all_x86_64_proofs() length ({}) -- #434 wiring regressed?",
                    db_count, registry_count
                );
                // Current registry size floor; grows as new x86-64 lowerings land.
                // L69 adds x86 AtomicRmwCasLoop old/update/adjacent obligations.
                // L68 adds 16 x86 scalar bitfield extract/sextract/insert/alias obligations.
                assert!(
                    db_count >= 212,
                    "expected >= 212 x86-64 lowering proofs (as of L68 scalar bitfield wiring), got {}",
                    db_count
                );
                let candidates = db.by_category(ProofCategory::X8664Lowering);
                for query in [
                    "AtomicRmwCasLoop_Add_I32 returns old value",
                    "AtomicRmwCasLoop_Xor_I64 updates memory",
                    "AtomicRmwCasLoop8_Xchg_I8 preserves adjacent memory",
                    "AtomicRmwCasLoop16_Sub_I16 updates memory",
                ] {
                    assert!(
                        candidates.iter().any(|p| p.obligation.name.contains(query)),
                        "missing registered x86-64 AtomicRmwCasLoop proof matching {query:?}"
                    );
                }
                for &(_, query) in X86_BITFIELD_REPRESENTATIVE_PROOF_QUERIES {
                    assert!(
                        candidates.iter().any(|p| p.obligation.name.contains(query)),
                        "missing registered x86-64 scalar bitfield proof matching {query:?}"
                    );
                }
            })
            .expect("spawn big-stack x86 proof registry thread")
            .join()
            .expect("join big-stack x86 proof registry thread");
    }

    // =======================================================================
    // Switch lowering proofs — wired via #444
    // =======================================================================

    /// Regression test for #444: the `switch_proofs::all_switch_proofs`
    /// registry must flow through `ProofDatabase::new()` so jump-table and
    /// balanced-BST obligations from the deferred #323 work are exercised by
    /// the default suite. The obligation count must match the registry length
    /// and meet a documented floor (dense i8/i16, sparse i8/i16, nonzero base,
    /// holes, 7-case sparse).
    #[test]
    fn test_switch_proofs_registered() {
        let db = ProofDatabase::new();
        let db_count = db.count_by_category(ProofCategory::SwitchLowering);
        let registry_count = crate::switch_proofs::all_switch_proofs().len();
        assert_eq!(
            db_count, registry_count,
            "ProofDatabase SwitchLowering count ({}) != all_switch_proofs() length ({}) -- #444 wiring regressed?",
            db_count, registry_count
        );
        // Current registry size floor; grows as new switch lowerings land.
        assert!(
            db_count >= 7,
            "expected >= 7 switch lowering proofs (as of #444 wiring), got {}",
            db_count
        );
    }

    // =======================================================================
    // Summary Display
    // =======================================================================

    #[test]
    fn test_summary_display() {
        let db = ProofDatabase::new();
        let summary = db.summary();
        let text = format!("{}", summary);
        assert!(text.contains("Total proofs:"), "display should show total");
        assert!(
            text.contains("By category:"),
            "display should show categories"
        );
    }

    // =======================================================================
    // ProofCategory Display
    // =======================================================================

    #[test]
    fn test_category_display() {
        assert_eq!(format!("{}", ProofCategory::Arithmetic), "Arithmetic");
        assert_eq!(format!("{}", ProofCategory::NeonLowering), "NEON Lowering");
        assert_eq!(format!("{}", ProofCategory::Comparison), "Comparison");
    }
}
