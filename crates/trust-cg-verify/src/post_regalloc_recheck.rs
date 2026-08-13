// trust-cg-verify/post_regalloc_recheck.rs - TV-4 post-regalloc re-verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-4: post-regalloc re-verification — no stage after ISel is validator-only.
//!
//! Per-instruction certs (`compiler.rs::generate_x86_64_proof_certificates`),
//! the TV-2 provenance cross-check ([`crate::provenance_xcheck`]) and the TV-3
//! dataflow-integrity gate ([`crate::dataflow_integrity`]) all run **before**
//! register allocation, on the RAW / post-opt-pass ISel stream. Everything the
//! x86 pipeline does AFTER that point — register-allocation rewrite, spill
//! store/reload materialization, the formal-argument parallel-copy fixup
//! (#497/#499), the two-address fixup, prologue/epilogue insertion and branch
//! resolution — was covered only by the regalloc translation validator
//! ([`trust_cg_regalloc::regalloc_validator`], whose value-flow walk documents a
//! reload-register blind spot) plus opcode COUNTERS
//! (`x86_64::X86MachineCodeEvidence`). This module adds a **fail-closed
//! re-verification of the FINAL post-fixup instruction stream, immediately
//! before encoding**, so those stages are no longer validator-only.
//!
//! # Two tiers
//!
//! The rustc bridge builds `trust-cg-codegen` with `default-features = false`,
//! so the heavy SMT/ay per-instruction verifier is NOT on the default AOT/JIT
//! path (`generate_x86_64_proof_certificates` is `#[cfg(feature = "verify")]`).
//! To keep the object path honest on the default build — exactly like the
//! unconditional [`crate::dataflow_integrity`] and [`crate::carrier_hygiene`]
//! gates — TV-4 splits into:
//!
//! * **Tier 1 (this module, default-ON, pure-lattice, no solver).** A
//!   `structural block-integrity` re-derivation over the FINAL post-regalloc
//!   machine function: within every machine block, no real (non-pseudo)
//!   instruction may follow an unconditional terminator (`JMP`/`RET`/`UD2` on
//!   x86). A register-allocation rewrite, a fixup or a branch-layout pass that
//!   appended dead/fused code after a block's terminator — or the classic
//!   "instruction added after a terminator by a bad pass" corruption — fails
//!   the compile CLOSED. The caller pairs this with an opcode-legality
//!   re-derivation (`reject_unsupported_x86_isel` re-run on the post-RA stream)
//!   so a fixup/prologue that introduced an unsupported form is also caught.
//!
//! * **Tier 2 (the caller, `#[cfg(feature = "verify")]` proof mode).** A full
//!   per-instruction cert re-derivation on the post-RA stream with a
//!   report-monotonicity check against the pre-RA report
//!   ([`nonpromotable_regression`]): the set of NON-PROMOTABLE emitted opcodes
//!   must not grow across regalloc+fixups. A correct spill store/reload / fixup
//!   copy / prologue push verifies (or is covered-elsewhere) and stays out of
//!   that set; a malformed insert that fails or falls unverified-uncovered
//!   fails closed.
//!
//! # Arch-parametricity
//!
//! The structural check runs over the shared [`crate::dataflow_integrity`]
//! [`DataflowFunctionView`] trait (already implemented for the x86
//! `X86ISelFunction` and the aarch64 `MachFunction`), so the same gate
//! instantiates on both arches. Both defaults are ENFORCE; final-stream
//! structural correctness cannot be downgraded by process environment.
//! `TCG_TRACE_POST_RA=1` remains a diagnostics-only trace control.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::dataflow_integrity::DataflowFunctionView;

// ---------------------------------------------------------------------------
// Violations
// ---------------------------------------------------------------------------

/// Which post-regalloc re-verification property broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostRegallocViolationKind {
    /// A real (non-pseudo) instruction follows an unconditional block
    /// terminator within the same machine block, on the FINAL post-regalloc
    /// stream. Catches a regalloc/fixup/branch-layout rewrite (or a bad pass)
    /// that appended dead or fused code after a block's terminator — including
    /// the "instruction added after a terminator" corruption class.
    InstructionAfterTerminator,
    /// A previously-promotable emitted opcode became NON-promotable across
    /// register allocation + fixups (Tier 2 cert monotonicity): the post-RA
    /// stream introduced a `Failed`/unverified-uncovered instruction the pre-RA
    /// stream did not have — a corrupted spill/reload/fixup/prologue insert.
    NonPromotableRegression,
}

impl PostRegallocViolationKind {
    /// Greppable tag for the diagnostic line.
    pub fn tag(self) -> &'static str {
        match self {
            Self::InstructionAfterTerminator => "code-after-terminator",
            Self::NonPromotableRegression => "nonpromotable-regression",
        }
    }
}

/// A single post-regalloc re-verification violation. In ENFORCE mode any one of
/// these fails the function's compile closed.
#[derive(Debug, Clone)]
pub struct PostRegallocViolation {
    /// Which property broke.
    pub kind: PostRegallocViolationKind,
    /// Human-readable diagnostic.
    pub detail: String,
}

// ---------------------------------------------------------------------------
// Tier 1: structural block-integrity re-derivation (pure-lattice, no solver)
// ---------------------------------------------------------------------------

/// Re-derive block-level structural integrity over the FINAL post-regalloc
/// machine function: within every machine block, no real (non-pseudo)
/// instruction may follow an unconditional terminator.
///
/// Pure and side-effect-free; the caller ([`evaluate`]) decides how to
/// report/enforce. Deliberately does NOT re-run TV-3's provenance-source
/// coherence (properties 2/3): register allocation legitimately reorders blocks
/// and inserts `Unattributed` spill/fixup/prologue instructions, so those
/// LIR-relative properties belong to the RAW pre-pass gate, not here. The
/// structural terminator property, by contrast, is arch-fixed and must hold on
/// the encoded stream regardless of allocation.
pub fn check_structure<F: DataflowFunctionView>(func: &F) -> Vec<PostRegallocViolation> {
    let mut violations = Vec::new();
    for b in 0..func.block_count() {
        let bid = func.block_id(b);
        let n = func.inst_count(b);
        let mut seen_uncond_terminator = false;
        for i in 0..n {
            let facts = func.inst_facts(b, i);
            if seen_uncond_terminator && !facts.is_pseudo {
                violations.push(PostRegallocViolation {
                    kind: PostRegallocViolationKind::InstructionAfterTerminator,
                    detail: format!(
                        "fn `{}` machine block {bid}: post-regalloc instruction #{i} ({}) follows \
                         an unconditional terminator within the same block (dead/fused code \
                         introduced after ISel — regalloc/fixup/branch-layout corruption)",
                        func.function_name(),
                        func.inst_opcode_debug(b, i),
                    ),
                });
            }
            if facts.is_unconditional_terminator {
                seen_uncond_terminator = true;
            }
        }
    }
    violations
}

// ---------------------------------------------------------------------------
// Tier 2: per-instruction cert-report monotonicity (proof mode)
// ---------------------------------------------------------------------------

/// Tier 2 (proof mode): given the PRE-regalloc and POST-regalloc emitted-opcode
/// inventories (each a list of `(opcode_display, is_promotable)` rows from a
/// [`crate::function_verifier::FunctionVerificationReport::emitted_opcode_inventory`]),
/// return a violation iff the post-RA stream introduced a NON-promotable opcode
/// that the pre-RA stream did not carry.
///
/// This is the report-monotonicity core: `nonpromotable(post) ⊆
/// nonpromotable(pre)`. A correct register-allocation rewrite only changes
/// operands (which the per-instruction reconstruction obligation is invariant
/// under: a self-consistent `add r,r` verifies identically whichever physical
/// registers it names) and inserts spill/reload/fixup/prologue copies that
/// verify or are covered-elsewhere — so the non-promotable multiset cannot
/// grow. A corrupted insert (an unverifiable form, a `Failed` reconstruction)
/// pushes a new non-promotable opcode into the post set and is caught here,
/// WITHOUT re-rejecting an opcode that was already a pre-existing coverage gap
/// (no new fail-closed).
///
/// `pre` / `post` are `(opcode_display, is_promotable)`; only the
/// NON-promotable rows matter, compared as an opcode-keyed multiset.
pub fn nonpromotable_regression(
    function_name: &str,
    pre: &[(String, bool)],
    post: &[(String, bool)],
) -> Option<PostRegallocViolation> {
    let mut pre_counts: HashMap<&str, i64> = HashMap::new();
    for (opcode, promotable) in pre {
        if !promotable {
            *pre_counts.entry(opcode.as_str()).or_insert(0) += 1;
        }
    }
    let mut post_counts: HashMap<&str, i64> = HashMap::new();
    for (opcode, promotable) in post {
        if !promotable {
            *post_counts.entry(opcode.as_str()).or_insert(0) += 1;
        }
    }
    // Deterministic order for the first-offender diagnostic.
    let mut offenders: Vec<(&str, i64, i64)> = post_counts
        .iter()
        .filter_map(|(opcode, &post_n)| {
            let pre_n = pre_counts.get(opcode).copied().unwrap_or(0);
            (post_n > pre_n).then_some((*opcode, pre_n, post_n))
        })
        .collect();
    offenders.sort_unstable_by(|a, b| a.0.cmp(b.0));
    let (opcode, pre_n, post_n) = offenders.into_iter().next()?;
    Some(PostRegallocViolation {
        kind: PostRegallocViolationKind::NonPromotableRegression,
        detail: format!(
            "fn `{function_name}`: emitted opcode `{opcode}` is non-promotable on {post_n} \
             post-regalloc instruction(s) but only {pre_n} pre-regalloc — register allocation / a \
             fixup / prologue introduced an unproven instruction (post-ISel corruption)"
        ),
    })
}

// ---------------------------------------------------------------------------
// Mode + telemetry (mirrors crate::dataflow_integrity)
// ---------------------------------------------------------------------------

/// Enforcement mode for the TV-4 post-regalloc re-verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostRegallocRecheckMode {
    /// Do not run the re-verification at all.
    Off,
    /// Run it; count + report violations, never fail the compile.
    Warn,
    /// Run it; any violation fails the function's compile closed.
    Enforce,
}

/// Default mode for the x86-64 path: ENFORCE.
///
/// Flipped default-ON per the §2.4 gate rollout after a warn-only telemetry pass
/// over the full differential corpus reported 0 hits. Any NEW violation a future
/// program surfaces fails closed loudly (never a miscompile) and is triaged.
pub const X86_POST_RA_RECHECK_DEFAULT: PostRegallocRecheckMode = PostRegallocRecheckMode::Enforce;

/// Default mode for the aarch64 path: ENFORCE.
pub const AARCH64_POST_RA_RECHECK_DEFAULT: PostRegallocRecheckMode =
    PostRegallocRecheckMode::Enforce;

/// Resolve the active mode. The caller supplies its architecture's enforce
/// default; environment variables cannot weaken a production correctness gate.
pub fn post_regalloc_recheck_mode(
    arch_default: PostRegallocRecheckMode,
) -> PostRegallocRecheckMode {
    arch_default
}

/// True when `TCG_TRACE_POST_RA=1` requests per-function trace output.
pub fn post_regalloc_trace_enabled() -> bool {
    matches!(
        std::env::var("TCG_TRACE_POST_RA").as_deref(),
        Ok("1") | Ok("true") | Ok("on")
    )
}

/// Process-wide count of post-regalloc re-verification violations observed
/// (warn or enforce) — telemetry for the warn-only rollout and for tests.
static VIOLATION_HITS: AtomicU64 = AtomicU64::new(0);

/// Total post-regalloc re-verification violations observed by this process.
pub fn post_regalloc_hit_count() -> u64 {
    VIOLATION_HITS.load(Ordering::Relaxed)
}

/// Record one violation: bump the process-wide counter and print a greppable
/// one-line report (`[TCG-POST-RA-RECHECK-*]`).
pub fn record_post_regalloc_violation(
    arch: &str,
    function_name: &str,
    kind_tag: &str,
    detail: &str,
    mode: PostRegallocRecheckMode,
) {
    VIOLATION_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = match mode {
        PostRegallocRecheckMode::Enforce => "[TCG-POST-RA-RECHECK-FAIL]",
        _ => "[TCG-POST-RA-RECHECK-WARN]",
    };
    eprintln!("{tag} arch={arch} fn={function_name} kind={kind_tag}: {detail}");
}

/// Print the per-function trace summary when `TCG_TRACE_POST_RA=1`.
pub fn trace_function_summary(arch: &str, function_name: &str, violations: usize) {
    if post_regalloc_trace_enabled() {
        eprintln!("[TCG-TRACE-POST-RA] arch={arch} fn={function_name} violations={violations}");
    }
}

// ---------------------------------------------------------------------------
// Driver (Tier 1 structural)
// ---------------------------------------------------------------------------

/// Tier-1 driver: re-derive structural block integrity over one FINAL
/// post-regalloc machine function, applying the resolved
/// [`PostRegallocRecheckMode`].
///
/// * `Off` → returns `None` immediately.
/// * All violations are recorded (telemetry) regardless of mode.
/// * In `Enforce` mode the FIRST violation is returned so the caller can fail
///   the compile closed; in `Warn`/`Off` mode `None` is returned (no verdict
///   change).
pub fn evaluate<F: DataflowFunctionView>(
    func: &F,
    arch: &str,
    mode: PostRegallocRecheckMode,
) -> Option<PostRegallocViolation> {
    if mode == PostRegallocRecheckMode::Off {
        return None;
    }
    let violations = check_structure(func);
    trace_function_summary(arch, func.function_name(), violations.len());
    for v in &violations {
        record_post_regalloc_violation(arch, func.function_name(), v.kind.tag(), &v.detail, mode);
    }
    if mode == PostRegallocRecheckMode::Enforce {
        violations.into_iter().next()
    } else {
        None
    }
}

/// Report a Tier-1 opcode-legality re-derivation failure (the caller re-runs the
/// arch pipeline's `reject_unsupported_*` on the post-RA stream and routes the
/// error through here so it obeys the same mode/telemetry). Returns `true` when
/// the caller must fail the compile closed (ENFORCE), `false` for WARN/OFF.
pub fn report_opcode_legality_failure(
    arch: &str,
    function_name: &str,
    detail: &str,
    mode: PostRegallocRecheckMode,
) -> bool {
    if mode == PostRegallocRecheckMode::Off {
        return false;
    }
    record_post_regalloc_violation(
        arch,
        function_name,
        "unsupported-post-ra-opcode",
        detail,
        mode,
    );
    mode == PostRegallocRecheckMode::Enforce
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dataflow_integrity::InstFacts;
    use trust_cg_ir::provenance::LoweringProvenance;

    /// A hand-built machine-function view for exercising the structural check
    /// independent of a real ISel function.
    struct MockView {
        blocks: Vec<Vec<InstFacts>>,
        opcodes: Vec<Vec<&'static str>>,
    }

    impl DataflowFunctionView for MockView {
        fn function_name(&self) -> &str {
            "mock"
        }
        fn block_count(&self) -> usize {
            self.blocks.len()
        }
        fn block_id(&self, block: usize) -> u32 {
            block as u32
        }
        fn inst_count(&self, block: usize) -> usize {
            self.blocks[block].len()
        }
        fn inst_facts(&self, block: usize, inst: usize) -> InstFacts {
            self.blocks[block][inst]
        }
        fn inst_opcode_debug(&self, block: usize, inst: usize) -> String {
            self.opcodes[block][inst].to_string()
        }
    }

    fn real(uncond_term: bool) -> InstFacts {
        InstFacts {
            is_unconditional_terminator: uncond_term,
            is_pseudo: false,
            provenance: LoweringProvenance::UNATTRIBUTED,
        }
    }

    fn pseudo() -> InstFacts {
        InstFacts {
            is_unconditional_terminator: false,
            is_pseudo: true,
            provenance: LoweringProvenance::UNATTRIBUTED,
        }
    }

    #[test]
    fn clean_post_ra_block_passes() {
        // block: add; add; ret  — nothing after the terminator.
        let view = MockView {
            blocks: vec![vec![real(false), real(false), real(true)]],
            opcodes: vec![vec!["Add", "Add", "Ret"]],
        };
        assert!(check_structure(&view).is_empty());
        assert!(evaluate(&view, "x86_64", PostRegallocRecheckMode::Enforce).is_none());
    }

    #[test]
    fn pseudo_after_terminator_is_allowed() {
        // A pseudo (Nop/label) after the terminator is legitimate (no encoding).
        let view = MockView {
            blocks: vec![vec![real(true), pseudo()]],
            opcodes: vec![vec!["Ret", "Nop"]],
        };
        assert!(check_structure(&view).is_empty());
    }

    #[test]
    fn real_inst_after_terminator_refutes() {
        // REFUTATION: a real instruction inserted after the block terminator by
        // a hypothetical bad post-RA pass must fail closed.
        let view = MockView {
            blocks: vec![vec![real(false), real(true), real(false)]],
            opcodes: vec![vec!["Add", "Jmp", "Mov"]],
        };
        let vs = check_structure(&view);
        assert_eq!(vs.len(), 1);
        assert_eq!(
            vs[0].kind,
            PostRegallocViolationKind::InstructionAfterTerminator
        );
        // ENFORCE returns the violation (fail closed); WARN does not.
        assert!(evaluate(&view, "x86_64", PostRegallocRecheckMode::Enforce).is_some());
        assert!(evaluate(&view, "x86_64", PostRegallocRecheckMode::Warn).is_none());
        assert!(evaluate(&view, "x86_64", PostRegallocRecheckMode::Off).is_none());
    }

    #[test]
    fn nonpromotable_monotonic_clean() {
        // Pre-RA already had one uncovered `Foo`; post-RA still has exactly one
        // (kept) plus newly-inserted, verifying `Mov`s — no regression.
        let pre = vec![
            ("Add".to_string(), true),
            ("Foo".to_string(), false),
            ("Ret".to_string(), true),
        ];
        let post = vec![
            ("Mov".to_string(), true),
            ("Add".to_string(), true),
            ("Foo".to_string(), false),
            ("Mov".to_string(), true),
            ("Push".to_string(), true),
            ("Ret".to_string(), true),
        ];
        assert!(nonpromotable_regression("f", &pre, &post).is_none());
    }

    #[test]
    fn nonpromotable_regression_refutes() {
        // REFUTATION: post-RA introduced a NEW uncovered opcode `Bad` (a
        // corrupted spill/fixup insert) that pre-RA did not carry.
        let pre = vec![("Add".to_string(), true), ("Ret".to_string(), true)];
        let post = vec![
            ("Add".to_string(), true),
            ("Bad".to_string(), false),
            ("Ret".to_string(), true),
        ];
        let v = nonpromotable_regression("f", &pre, &post).expect("must refute");
        assert_eq!(v.kind, PostRegallocViolationKind::NonPromotableRegression);
        assert!(v.detail.contains("Bad"));
    }

    #[test]
    fn nonpromotable_regression_counts_duplicates() {
        // Pre-RA had ONE uncovered `Foo`; post-RA has TWO (one kept + one
        // newly-corrupted). The multiset comparison catches the extra.
        let pre = vec![("Foo".to_string(), false)];
        let post = vec![("Foo".to_string(), false), ("Foo".to_string(), false)];
        assert!(nonpromotable_regression("f", &pre, &post).is_some());
    }

    // ===================================================================
    // PINNED refutation over a REAL X86ISelFunction (exercises the x86
    // DataflowFunctionView impl end-to-end, not just the mock).
    // ===================================================================

    use trust_cg_ir::x86_64_ops::X86Opcode;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;
    use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst};

    fn x86_inst(opcode: X86Opcode) -> X86ISelInst {
        X86ISelInst::new(opcode, vec![])
    }

    fn x86_func(name: &str, insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            name.to_string(),
            Signature {
                params: vec![Type::I64],
                returns: vec![],
            },
        );
        let block = Block(0);
        func.ensure_block(block);
        func.blocks.get_mut(&block).unwrap().insts.extend(insts);
        func
    }

    /// PINNED POSITIVE: a well-formed post-RA block (add; add; ret) passes the
    /// real x86 structural recheck under the ENFORCE default.
    #[test]
    fn x86_clean_post_ra_passes_enforce() {
        let func = x86_func(
            "f",
            vec![
                x86_inst(X86Opcode::AddRR),
                x86_inst(X86Opcode::AddRR),
                x86_inst(X86Opcode::Ret),
            ],
        );
        assert!(evaluate(&func, "x86_64", PostRegallocRecheckMode::Enforce).is_none());
    }

    /// PINNED REFUTATION (TV-4 done-criterion): a real instruction placed AFTER
    /// the block's terminator on the post-regalloc stream — the exact shape a
    /// bad post-RA pass ("instruction added after a terminator") would produce —
    /// fails the compile CLOSED under ENFORCE, and is telemetry-only under WARN.
    #[test]
    fn x86_inst_after_terminator_refutes_enforce() {
        let func = x86_func(
            "bad",
            vec![
                x86_inst(X86Opcode::AddRR),
                x86_inst(X86Opcode::Ret),   // unconditional terminator
                x86_inst(X86Opcode::MovRR), // corruption: real inst AFTER ret
            ],
        );
        let violation = evaluate(&func, "x86_64", PostRegallocRecheckMode::Enforce)
            .expect("post-RA recheck must fail closed on an inst after the terminator");
        assert_eq!(
            violation.kind,
            PostRegallocViolationKind::InstructionAfterTerminator
        );
        // WARN mode records telemetry but does NOT fail (returns None).
        assert!(evaluate(&func, "x86_64", PostRegallocRecheckMode::Warn).is_none());
    }

    #[test]
    fn opcode_legality_failure_gating() {
        // ENFORCE => caller must fail closed (returns true); WARN/OFF => not.
        assert!(report_opcode_legality_failure(
            "x86_64",
            "f",
            "unsupported opcode Foo",
            PostRegallocRecheckMode::Enforce
        ));
        assert!(!report_opcode_legality_failure(
            "x86_64",
            "f",
            "unsupported opcode Foo",
            PostRegallocRecheckMode::Warn
        ));
        assert!(!report_opcode_legality_failure(
            "x86_64",
            "f",
            "unsupported opcode Foo",
            PostRegallocRecheckMode::Off
        ));
    }

    #[test]
    fn production_defaults_enforce_both_architectures() {
        assert_eq!(
            X86_POST_RA_RECHECK_DEFAULT,
            PostRegallocRecheckMode::Enforce
        );
        assert_eq!(
            AARCH64_POST_RA_RECHECK_DEFAULT,
            PostRegallocRecheckMode::Enforce
        );
    }
}
