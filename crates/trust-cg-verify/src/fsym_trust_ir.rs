// Symbolic execution: bounded trust_ir preflight scanner
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Bounded trust_ir-to-fsym preflight scanner.
//!
//! This module is intentionally narrow: it walks small acyclic functions with
//! direct branches and only evaluates concrete/value-known SSA expressions. It
//! only unrolls small loops when the CFG shape and trip count are statically
//! bounded. It does not invoke an SMT solver, summarize calls, or claim
//! corpus-level coverage.

use crate::fsym_arith::{ArithOp, ArithUbKind, check_arith_ub};
use crate::fsym_bounds::{BoundsOp, check_oob_ub};
use crate::fsym_null::{FsymVerdict, MemOp, PathContext, check_null_deref};
use crate::fsym_uaf::{UafEvent, UafEventKind, check_uaf_ub};
use crate::smt::{EvalResult, SmtExpr};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::path::Path;
use trust_cg_lower::adapter::translate_type_with_tables;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, Function, ICmpOp, Inst, InstrNode, Module, OverflowOp,
    ProofAnnotation, SourceSpan, SwitchCase, Ty, UnOp, ValueId,
};

/// Maximum instruction count scanned in one bounded trust_ir preflight function.
///
/// Larger bodies are skipped so `--fsym` remains a bounded preflight rather than
/// an unbounded analysis pass.
pub const FSYM_TRUST_IR_MAX_STRAIGHT_LINE_INSTRUCTIONS: usize = 256;

/// Maximum basic block count scanned in one acyclic trust_ir preflight function.
pub const FSYM_TRUST_IR_MAX_BLOCKS: usize = 16;

/// Maximum explicit switch cases explored by the bounded trust_ir preflight.
pub const FSYM_TRUST_IR_MAX_SWITCH_CASES: usize = 8;

/// Maximum backedge traversals scanned for one statically bounded trust_ir loop.
pub const FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS: usize = 16;

const FSYM_TRUST_IR_MAX_LOOP_VALIDATION_STATES: usize =
    FSYM_TRUST_IR_MAX_BLOCKS * (FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS + 2) * 4;

/// Severity used when rendering fsym diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymTrustIrSeverity {
    Warning,
    Error,
}

impl FsymTrustIrSeverity {
    fn as_str(self) -> &'static str {
        match self {
            FsymTrustIrSeverity::Warning => "warning",
            FsymTrustIrSeverity::Error => "error",
        }
    }
}

/// Concrete UB class reported by the trust_ir fsym preflight.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymTrustIrDiagnosticKind {
    NullDeref,
    Arithmetic,
    OutOfBounds,
    UseAfterFree,
}

impl FsymTrustIrDiagnosticKind {
    fn as_str(self) -> &'static str {
        match self {
            FsymTrustIrDiagnosticKind::NullDeref => "null-deref",
            FsymTrustIrDiagnosticKind::Arithmetic => "arithmetic",
            FsymTrustIrDiagnosticKind::OutOfBounds => "bounds",
            FsymTrustIrDiagnosticKind::UseAfterFree => "use-after-free",
        }
    }
}

/// One concrete UB diagnostic emitted by the bounded preflight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrDiagnostic {
    pub kind: FsymTrustIrDiagnosticKind,
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    pub span: Option<SourceSpan>,
    pub message: String,
    pub witness: Vec<(String, u64)>,
}

impl FsymTrustIrDiagnostic {
    /// Render this diagnostic in the CLI's `warning[fsym]` / `error[fsym]`
    /// style. The optional input path is display-only provenance.
    pub fn render(&self, severity: FsymTrustIrSeverity, input: Option<&Path>) -> String {
        let mut out = format!("{}[fsym]: ", severity.as_str());
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "{} in module `{}` function `{}` bb{} inst{}: {}",
            self.kind.as_str(),
            self.module,
            self.function,
            self.block,
            self.inst_index,
            self.message
        ));

        if let Some(span) = self.span {
            out.push_str(&format!(
                " (source file {} line {} col {})",
                span.file, span.line, span.col
            ));
        }

        if !self.witness.is_empty() {
            let witness = self
                .witness
                .iter()
                .map(|(name, value)| format!("{name}={value}"))
                .collect::<Vec<_>>()
                .join(", ");
            out.push_str(&format!("; witness: {witness}"));
        }

        out
    }
}

/// Reason a function was not scanned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymTrustIrSkipReason {
    Loop,
    Switch,
    TooLarge,
    MalformedCfg,
    UnsupportedTerminator,
    UnsupportedInstruction,
}

impl FsymTrustIrSkipReason {
    fn as_str(self) -> &'static str {
        match self {
            FsymTrustIrSkipReason::Loop => "loop",
            FsymTrustIrSkipReason::Switch => "switch",
            FsymTrustIrSkipReason::TooLarge => "too-large",
            FsymTrustIrSkipReason::MalformedCfg => "malformed-cfg",
            FsymTrustIrSkipReason::UnsupportedTerminator => "unsupported-terminator",
            FsymTrustIrSkipReason::UnsupportedInstruction => "unsupported-instruction",
        }
    }
}

/// One bounded-preflight skip emitted for a function outside fsym scope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrSkip {
    pub function: String,
    pub reason: FsymTrustIrSkipReason,
    pub detail: String,
}

impl FsymTrustIrSkip {
    /// Render this skip as a stable warning diagnostic.
    pub fn render(&self, input: Option<&Path>) -> String {
        let mut out = "warning[fsym]: ".to_string();
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "skipped function `{}` reason={} detail={}",
            self.function,
            self.reason.as_str(),
            self.detail
        ));
        out
    }
}

/// One non-concrete fsym obligation that would need a stronger backend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrUnknown {
    pub kind: FsymTrustIrDiagnosticKind,
    pub label: String,
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    pub reason: String,
    pub path_guards: Vec<String>,
    pub candidate_expression: Option<String>,
    pub solver_candidate: Option<FsymTrustIrSolverCandidate>,
}

impl FsymTrustIrUnknown {
    /// Render this unknown obligation as a stable warning diagnostic.
    pub fn render(&self, input: Option<&Path>) -> String {
        let mut out = "warning[fsym]: ".to_string();
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "unknown obligation {} label `{}` in module `{}` function `{}` bb{} inst{}: {}",
            self.kind.as_str(),
            self.label,
            self.module,
            self.function,
            self.block,
            self.inst_index,
            self.reason
        ));
        if let Some(candidate_expression) = &self.candidate_expression {
            out.push_str(&format!("; candidate: {candidate_expression}"));
        }
        if !self.path_guards.is_empty() {
            out.push_str(&format!("; guards: {}", self.path_guards.join(" && ")));
        }
        out
    }
}

/// Structured solver handoff for a bounded fsym unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymTrustIrSolverCandidate {
    pub path_guards: Vec<SmtExpr>,
    pub obligation: FsymTrustIrSolverObligation,
}

/// Conservative obligation shapes accepted by the bounded fsym escalation path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FsymTrustIrSolverObligation {
    NullDeref {
        ptr: SmtExpr,
        ptr_width: u32,
    },
    Arithmetic {
        kind: ArithUbKind,
        lhs: SmtExpr,
        rhs: Option<SmtExpr>,
        width: u32,
    },
    OutOfBounds {
        byte_offset: SmtExpr,
        object_size_bytes: SmtExpr,
        access_size_bytes: u64,
        width: u32,
    },
}

/// A reachable pointer dereference the scanner failed to account for.
///
/// This is the fail-closed backstop for the deref-coverage invariant: every
/// reachable memory access (`Load`/`Store`/`Atomic*`/`AtomicRMW`/`CmpXchg`)
/// walked by the scanner MUST be discharged by exactly one verdict — `Safe`
/// (with a recorded justification), a concrete-UB `Diagnostic`, or an
/// `Unknown` solver candidate. If a site is walked but no verdict is recorded
/// for it, the obligation was silently dropped — i.e. the scanner would be
/// *failing open*, asserting a safety it never proved. Rather than let that
/// pass silently, the scanner records this error and callers treat it as
/// fatal (mirroring the opcode `coverage_gate`: an unaccounted obligation is
/// never an implicit pass).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymCoverageError {
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    /// The memory-access opcode whose obligation was dropped (e.g. "Load").
    pub opcode: &'static str,
    pub detail: String,
}

impl FsymCoverageError {
    /// Render this coverage gap as a stable error diagnostic.
    pub fn render(&self, input: Option<&Path>) -> String {
        let mut out = "error[fsym]: ".to_string();
        if let Some(input) = input {
            out.push_str(&format!("{}: ", input.display()));
        }
        out.push_str(&format!(
            "deref-coverage invariant violated: reachable {} in module `{}` function `{}` bb{} inst{} recorded no verdict (fail-closed): {}",
            self.opcode, self.module, self.function, self.block, self.inst_index, self.detail
        ));
        out
    }
}

/// Scanner output: concrete UB diagnostics plus bounded-scope accounting.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FsymTrustIrReport {
    pub diagnostics: Vec<FsymTrustIrDiagnostic>,
    pub scanned_functions: usize,
    pub scanned_function_names: Vec<String>,
    pub skipped_functions: Vec<FsymTrustIrSkip>,
    pub unknown_obligations: Vec<FsymTrustIrUnknown>,
    /// Fail-closed deref-coverage violations: reachable memory accesses that
    /// were walked but produced no verdict. A non-empty list means the
    /// scanner dropped an obligation and MUST be treated as fatal.
    pub coverage_errors: Vec<FsymCoverageError>,
}

impl FsymTrustIrReport {
    pub fn has_concrete_ub(&self) -> bool {
        !self.diagnostics.is_empty()
    }

    /// True if the deref-coverage invariant was violated for any function.
    ///
    /// A coverage gap is a dropped obligation (the scanner failed open). It is
    /// fatal: callers must reject the module rather than emit code on the
    /// strength of an unproven safety assertion.
    pub fn has_coverage_error(&self) -> bool {
        !self.coverage_errors.is_empty()
    }
}

#[derive(Debug, Clone)]
struct PointerFacts {
    null_expr: SmtExpr,
    object: Option<SmtExpr>,
    byte_offset: Option<SmtExpr>,
    object_size_bytes: Option<SmtExpr>,
    in_bounds_proven: bool,
    not_null_proven: bool,
}

#[derive(Debug, Clone)]
struct ValueFacts {
    ty: Ty,
    expr: Option<SmtExpr>,
    pointer: Option<PointerFacts>,
}

type VerdictEvidence = (Option<String>, Option<FsymTrustIrSolverObligation>);

#[derive(Debug, Clone)]
struct FunctionScan<'a> {
    module: &'a Module,
    function: &'a Function,
    block: &'a Block,
    values: HashMap<ValueId, ValueFacts>,
    ctx: PathContext,
    uaf_events: Vec<UafEvent>,
    uaf_reported: bool,
    diagnostics: Vec<FsymTrustIrDiagnostic>,
    unknown_obligations: Vec<FsymTrustIrUnknown>,
    /// Deref-coverage accounting for the block currently being walked: the set
    /// of `inst_index`es at which `record_verdict` produced a verdict. After a
    /// block is walked, every reachable memory-access site MUST appear here, or
    /// the obligation was dropped (fail-closed — see `FsymCoverageError`).
    covered: HashSet<usize>,
    coverage_errors: Vec<FsymCoverageError>,
    /// Test-only fault injection: when true, `check_null` reproduces the
    /// historical fail-open behaviour (silent early return, no verdict
    /// recorded) so the deref-coverage invariant can be exercised against a
    /// deliberately dropped obligation. Never set outside tests.
    #[cfg(test)]
    force_drop_deref: bool,
}

/// Scan a trust_ir module for concrete UB in bounded straight-line functions.
pub fn scan_module(module: &Module) -> FsymTrustIrReport {
    let mut report = FsymTrustIrReport::default();

    for function in &module.functions {
        if let Err(skip) = validate_function_scope(module, function) {
            report.skipped_functions.push(FsymTrustIrSkip {
                function: function.name.clone(),
                reason: skip.reason,
                detail: skip.detail,
            });
            continue;
        }

        report.scanned_functions += 1;
        report.scanned_function_names.push(function.name.clone());
        let scan = scan_function(module, function);
        report.diagnostics.extend(scan.diagnostics);
        report.unknown_obligations.extend(scan.unknown_obligations);
        report.coverage_errors.extend(scan.coverage_errors);
    }

    report
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionSkip {
    reason: FsymTrustIrSkipReason,
    detail: String,
}

impl FunctionSkip {
    fn new(reason: FsymTrustIrSkipReason, detail: impl Into<String>) -> Self {
        Self {
            reason,
            detail: detail.into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CfgEdge {
    source: BlockId,
    target: BlockId,
}

fn validate_function_scope(module: &Module, function: &Function) -> Result<(), FunctionSkip> {
    if function.blocks.is_empty() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            "function has no blocks",
        ));
    }

    if function.blocks.len() > FSYM_TRUST_IR_MAX_BLOCKS {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::TooLarge,
            format!(
                "function has {} block(s), over fsym bound {}",
                function.blocks.len(),
                FSYM_TRUST_IR_MAX_BLOCKS
            ),
        ));
    }

    if function_block(function, function.entry).is_none() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            "entry block is missing",
        ));
    }

    let body_len: usize = function.blocks.iter().map(|block| block.body.len()).sum();
    if body_len > FSYM_TRUST_IR_MAX_STRAIGHT_LINE_INSTRUCTIONS {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::TooLarge,
            format!(
                "function body has {body_len} instruction(s), over fsym bound {FSYM_TRUST_IR_MAX_STRAIGHT_LINE_INSTRUCTIONS}"
            ),
        ));
    }

    for block in &function.blocks {
        let Some((last, prefix)) = block.body.split_last() else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!("bb{} has no terminator", block.id.index()),
            ));
        };
        if prefix.iter().any(InstrNode::is_terminator) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!(
                    "bb{} has a terminator before the end of the block",
                    block.id.index()
                ),
            ));
        }
        for (inst_index, node) in prefix.iter().enumerate() {
            validate_supported_nonterminator(block.id, inst_index, node)?;
        }
        match &last.inst {
            Inst::Br { target, args } => {
                validate_edge_args(function, block.id, *target, args)?;
            }
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                validate_edge_args(function, block.id, *then_target, then_args)?;
                validate_edge_args(function, block.id, *else_target, else_args)?;
            }
            Inst::Return { .. } | Inst::Unreachable => {}
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                ..
            } => {
                validate_switch_terminator(
                    module,
                    function,
                    block.id,
                    *value,
                    *default,
                    default_args,
                    cases,
                )?;
            }
            _ => {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::UnsupportedTerminator,
                    format!("bb{} does not end in a terminator", block.id.index()),
                ));
            }
        }
    }

    let backedges = cfg_backedges(function);
    match backedges.as_slice() {
        [] => {}
        [backedge] => validate_bounded_loop_scope(module, function, *backedge)?,
        _ => {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "control-flow graph contains {} backedge(s); bounded fsym only supports one static backedge",
                    backedges.len()
                ),
            ));
        }
    }

    Ok(())
}

fn validate_supported_nonterminator(
    block: BlockId,
    inst_index: usize,
    node: &InstrNode,
) -> Result<(), FunctionSkip> {
    let Some(detail) = unsupported_nonterminator_detail(&node.inst) else {
        return Ok(());
    };

    Err(FunctionSkip::new(
        FsymTrustIrSkipReason::UnsupportedInstruction,
        format!(
            "bb{} inst{} unsupported: {detail}",
            block.index(),
            inst_index
        ),
    ))
}

fn unsupported_nonterminator_detail(inst: &Inst) -> Option<String> {
    match inst {
        Inst::Undef { ty } => Some(format!(
            "Undef({ty:?}) requires poison/undef and NoUndef proof semantics"
        )),
        Inst::CallIndirect { .. } => {
            Some("CallIndirect requires callee/call-effect summaries".to_string())
        }
        Inst::Retain { .. } | Inst::Release { .. } | Inst::IsUnique { .. } => Some(
            "ARC retain/release/is_unique semantics are outside bounded fsym support".to_string(),
        ),
        Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. } => Some(
            "binding-frame ops require quantified frame semantics outside bounded fsym support"
                .to_string(),
        ),
        Inst::DialectOp(op) => Some(format!(
            "DialectOp `{}` requires dialect-specific semantics before fsym",
            op.qualified_name()
        )),
        _ => None,
    }
}

fn validate_switch_terminator(
    module: &Module,
    function: &Function,
    source: BlockId,
    value: ValueId,
    default: BlockId,
    default_args: &[ValueId],
    cases: &[SwitchCase],
) -> Result<(), FunctionSkip> {
    if cases.len() > FSYM_TRUST_IR_MAX_SWITCH_CASES {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Switch,
            format!(
                "bb{} switch has {} case(s), over fsym bound {}",
                source.index(),
                cases.len(),
                FSYM_TRUST_IR_MAX_SWITCH_CASES
            ),
        ));
    }

    let Some(selector_ty) = function
        .typed_value(module, value)
        .map(|metadata| metadata.ty)
    else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Switch,
            format!(
                "bb{} switch selector value {} has no typed metadata",
                source.index(),
                value.index()
            ),
        ));
    };

    if switch_selector_width(&selector_ty).is_none() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Switch,
            format!(
                "bb{} switch selector type {:?} is outside bounded fsym support",
                source.index(),
                selector_ty
            ),
        ));
    }

    validate_edge_args(function, source, default, default_args)?;
    for case in cases {
        if !matches!(case.value, Constant::Int(_)) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Switch,
                format!(
                    "bb{} switch case constant {:?} is outside bounded fsym support",
                    source.index(),
                    case.value
                ),
            ));
        }
        validate_edge_args(function, source, case.target, &case.args)?;
    }

    Ok(())
}

fn validate_edge_args(
    function: &Function,
    source: BlockId,
    target: BlockId,
    args: &[ValueId],
) -> Result<(), FunctionSkip> {
    let Some(target_block) = function_block(function, target) else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!("bb{} targets missing bb{}", source.index(), target.index()),
        ));
    };
    if target_block.params.len() != args.len() {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!(
                "bb{} passes {} arg(s) to bb{} with {} param(s)",
                source.index(),
                args.len(),
                target.index(),
                target_block.params.len()
            ),
        ));
    }
    Ok(())
}

fn function_block(function: &Function, block: BlockId) -> Option<&Block> {
    function
        .blocks
        .iter()
        .find(|candidate| candidate.id == block)
}

fn block_successors(block: &Block) -> Vec<BlockId> {
    let Some(last) = block.body.last() else {
        return Vec::new();
    };
    match &last.inst {
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut successors = Vec::with_capacity(cases.len() + 1);
            successors.push(*default);
            successors.extend(cases.iter().map(|case| case.target));
            successors
        }
        _ => Vec::new(),
    }
}

fn cfg_backedges(function: &Function) -> Vec<CfgEdge> {
    fn visit(
        function: &Function,
        block: BlockId,
        visiting: &mut HashSet<BlockId>,
        visited: &mut HashSet<BlockId>,
        backedges: &mut HashSet<CfgEdge>,
    ) {
        if visiting.contains(&block) {
            return;
        }
        if visited.contains(&block) {
            return;
        }

        visiting.insert(block);
        if let Some(block_ref) = function_block(function, block) {
            for successor in block_successors(block_ref) {
                if visiting.contains(&successor) {
                    backedges.insert(CfgEdge {
                        source: block,
                        target: successor,
                    });
                } else {
                    visit(function, successor, visiting, visited, backedges);
                }
            }
        }
        visiting.remove(&block);
        visited.insert(block);
    }

    let mut backedges = HashSet::new();
    visit(
        function,
        function.entry,
        &mut HashSet::new(),
        &mut HashSet::new(),
        &mut backedges,
    );
    let mut backedges = backedges.into_iter().collect::<Vec<_>>();
    backedges.sort_by_key(|edge| (edge.source.index(), edge.target.index()));
    backedges
}

fn validate_bounded_loop_scope(
    module: &Module,
    function: &Function,
    backedge: CfgEdge,
) -> Result<(), FunctionSkip> {
    let loop_blocks = natural_loop_blocks(function, backedge)?;
    validate_loop_header(function, backedge, &loop_blocks)?;
    validate_loop_edges(function, backedge, &loop_blocks)?;
    validate_static_loop_unroll(module, function, backedge, &loop_blocks)?;
    Ok(())
}

fn natural_loop_blocks(
    function: &Function,
    backedge: CfgEdge,
) -> Result<HashSet<BlockId>, FunctionSkip> {
    let predecessors = block_predecessors(function);
    let mut loop_blocks = HashSet::from([backedge.target]);
    let mut stack = vec![backedge.source];

    while let Some(block) = stack.pop() {
        if !loop_blocks.insert(block) {
            continue;
        }
        if let Some(preds) = predecessors.get(&block) {
            stack.extend(preds.iter().copied());
        }
    }

    for block in &loop_blocks {
        if *block == backedge.target {
            continue;
        }
        for predecessor in predecessors.get(block).into_iter().flatten() {
            if !loop_blocks.contains(predecessor) {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::Loop,
                    format!(
                        "complex loop has entry from bb{} to bb{} instead of header bb{}",
                        predecessor.index(),
                        block.index(),
                        backedge.target.index()
                    ),
                ));
            }
        }
    }

    Ok(loop_blocks)
}

fn block_predecessors(function: &Function) -> HashMap<BlockId, Vec<BlockId>> {
    let mut predecessors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for block in &function.blocks {
        for successor in block_successors(block) {
            predecessors.entry(successor).or_default().push(block.id);
        }
    }
    predecessors
}

fn validate_loop_header(
    function: &Function,
    backedge: CfgEdge,
    loop_blocks: &HashSet<BlockId>,
) -> Result<(), FunctionSkip> {
    let Some(header) = function_block(function, backedge.target) else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!("loop header bb{} is missing", backedge.target.index()),
        ));
    };

    for (_, ty) in &header.params {
        if !loop_carried_ty_supported(ty) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop header bb{} carries unsupported state type {:?}",
                    header.id.index(),
                    ty
                ),
            ));
        }
    }

    let Some(terminator) = header.body.last() else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::MalformedCfg,
            format!("loop header bb{} has no terminator", header.id.index()),
        ));
    };
    let Inst::CondBr {
        then_target,
        else_target,
        ..
    } = &terminator.inst
    else {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Loop,
            format!(
                "loop header bb{} is not a conditional static-bound check",
                header.id.index()
            ),
        ));
    };

    let then_continues = loop_blocks.contains(then_target);
    let else_continues = loop_blocks.contains(else_target);
    if then_continues == else_continues {
        return Err(FunctionSkip::new(
            FsymTrustIrSkipReason::Loop,
            format!(
                "loop header bb{} must have exactly one loop continuation and one exit",
                header.id.index()
            ),
        ));
    }

    Ok(())
}

fn validate_loop_edges(
    function: &Function,
    backedge: CfgEdge,
    loop_blocks: &HashSet<BlockId>,
) -> Result<(), FunctionSkip> {
    for block_id in loop_blocks {
        let Some(block) = function_block(function, *block_id) else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!("loop block bb{} is missing", block_id.index()),
            ));
        };

        if matches!(
            block.body.last().map(|node| &node.inst),
            Some(Inst::Switch { .. })
        ) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "switch-controlled loop at bb{} is outside bounded fsym support",
                    block.id.index()
                ),
            ));
        }

        for successor in block_successors(block) {
            let edge = CfgEdge {
                source: *block_id,
                target: successor,
            };
            if successor == backedge.target && edge != backedge {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::Loop,
                    format!(
                        "loop has multiple edges to header bb{}",
                        backedge.target.index()
                    ),
                ));
            }
            if !loop_blocks.contains(&successor) && *block_id != backedge.target {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::Loop,
                    format!(
                        "loop exits from bb{}; bounded fsym only supports header exits",
                        block_id.index()
                    ),
                ));
            }
        }
    }

    if backedge.source != backedge.target {
        let Some(latch) = function_block(function, backedge.source) else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::MalformedCfg,
                format!("loop latch bb{} is missing", backedge.source.index()),
            ));
        };
        if !matches!(
            latch.body.last().map(|node| &node.inst),
            Some(Inst::Br { target, .. }) if *target == backedge.target
        ) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop latch bb{} must branch directly to header bb{}",
                    backedge.source.index(),
                    backedge.target.index()
                ),
            ));
        }
    }

    Ok(())
}

fn validate_static_loop_unroll(
    module: &Module,
    function: &Function,
    backedge: CfgEdge,
    loop_blocks: &HashSet<BlockId>,
) -> Result<(), FunctionSkip> {
    let Some(entry) = function_block(function, function.entry) else {
        return Ok(());
    };
    let mut worklist = VecDeque::from([FunctionScan::new(module, function, entry)]);
    let mut states = 0;
    let mut backedge_count = 0;

    while let Some(mut scan) = worklist.pop_front() {
        states += 1;
        if states > FSYM_TRUST_IR_MAX_LOOP_VALIDATION_STATES {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop validation exceeded {} state(s); CFG is outside bounded fsym loop support",
                    FSYM_TRUST_IR_MAX_LOOP_VALIDATION_STATES
                ),
            ));
        }

        scan.run_block();
        let source = scan.block.id;
        let Some(successors) = successor_scans(scan) else {
            if loop_blocks.contains(&source) {
                return Err(FunctionSkip::new(
                    FsymTrustIrSkipReason::Loop,
                    format!(
                        "loop control in bb{} is outside bounded fsym support",
                        source.index()
                    ),
                ));
            }
            continue;
        };

        for successor in successors {
            if successor.target == backedge.target {
                validate_static_loop_args(function, backedge.target, &successor)?;
            }
            if successor.source == backedge.source && successor.target == backedge.target {
                backedge_count += 1;
                if backedge_count > FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS {
                    return Err(FunctionSkip::new(
                        FsymTrustIrSkipReason::Loop,
                        format!(
                            "loop backedge bb{} -> bb{} exceeds fsym unroll bound {}; trip count is not statically bounded",
                            backedge.source.index(),
                            backedge.target.index(),
                            FSYM_TRUST_IR_MAX_LOOP_UNROLL_ITERATIONS
                        ),
                    ));
                }
            }

            let target = successor.target;
            let args = successor.args;
            enqueue_edge(successor.scan, target, &args, &mut worklist);
        }
    }

    Ok(())
}

fn validate_static_loop_args(
    function: &Function,
    header: BlockId,
    successor: &SuccessorScan<'_>,
) -> Result<(), FunctionSkip> {
    let Some(header_block) = function_block(function, header) else {
        return Ok(());
    };

    for ((param, ty), arg) in header_block.params.iter().zip(&successor.args) {
        if !loop_carried_ty_supported(ty) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop header bb{} param {} has unsupported state type {:?}",
                    header.index(),
                    param.index(),
                    ty
                ),
            ));
        }

        let Some(facts) = successor.scan.values.get(arg) else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} passes unknown value {} to header param {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index(),
                    param.index()
                ),
            ));
        };
        if facts.pointer.is_some() || !loop_carried_ty_supported(&facts.ty) {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} carries unsupported state value {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index()
                ),
            ));
        }
        let Some(expr) = facts.expr.as_ref() else {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} carries non-symbolic state value {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index()
                ),
            ));
        };
        if eval_concrete_u64(expr).is_none() {
            return Err(FunctionSkip::new(
                FsymTrustIrSkipReason::Loop,
                format!(
                    "loop edge bb{} -> bb{} carries non-static state value {}",
                    successor.source.index(),
                    successor.target.index(),
                    arg.index()
                ),
            ));
        }
    }

    Ok(())
}

fn loop_carried_ty_supported(ty: &Ty) -> bool {
    (ty.is_integer() || matches!(ty, Ty::Bool))
        && ty
            .bit_width()
            .is_some_and(|width| (1..=64).contains(&width))
}

#[derive(Debug, Clone, Default)]
struct FunctionScanReport {
    diagnostics: Vec<FsymTrustIrDiagnostic>,
    unknown_obligations: Vec<FsymTrustIrUnknown>,
    coverage_errors: Vec<FsymCoverageError>,
}

fn scan_function(module: &Module, function: &Function) -> FunctionScanReport {
    let mut report = FunctionScanReport::default();
    let mut worklist = VecDeque::new();
    let Some(entry) = function_block(function, function.entry) else {
        return report;
    };

    worklist.push_back(FunctionScan::new(module, function, entry));

    while let Some(mut scan) = worklist.pop_front() {
        scan.run_block();
        report.diagnostics.append(&mut scan.diagnostics);
        report
            .unknown_obligations
            .append(&mut scan.unknown_obligations);
        report.coverage_errors.append(&mut scan.coverage_errors);
        enqueue_successors(scan, &mut worklist);
    }

    report
}

#[derive(Debug, Clone)]
struct SuccessorScan<'a> {
    source: BlockId,
    target: BlockId,
    args: Vec<ValueId>,
    scan: FunctionScan<'a>,
}

fn enqueue_successors<'a>(scan: FunctionScan<'a>, worklist: &mut VecDeque<FunctionScan<'a>>) {
    let Some(successors) = successor_scans(scan) else {
        return;
    };
    for successor in successors {
        let target = successor.target;
        let args = successor.args;
        enqueue_edge(successor.scan, target, &args, worklist);
    }
}

fn successor_scans<'a>(scan: FunctionScan<'a>) -> Option<Vec<SuccessorScan<'a>>> {
    let source = scan.block.id;
    let terminator = scan.block.body.last().map(|node| node.inst.clone())?;

    match terminator {
        Inst::Br { target, args } => Some(vec![SuccessorScan {
            source,
            target,
            args,
            scan,
        }]),
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            let branch_expr = scan
                .values
                .get(&cond)
                .and_then(|facts| facts.expr.clone())?;
            let original_guard_len = scan.ctx.guards.len();
            let fork = scan.ctx.fork_branch(branch_expr);

            let mut successors = Vec::with_capacity(2);
            let mut then_scan = scan.clone();
            then_scan.ctx = fork.then_ctx;
            if !context_has_new_concrete_false_guard(&then_scan.ctx, original_guard_len) {
                successors.push(SuccessorScan {
                    source,
                    target: then_target,
                    args: then_args,
                    scan: then_scan,
                });
            }

            let mut else_scan = scan;
            else_scan.ctx = fork.else_ctx;
            if !context_has_new_concrete_false_guard(&else_scan.ctx, original_guard_len) {
                successors.push(SuccessorScan {
                    source,
                    target: else_target,
                    args: else_args,
                    scan: else_scan,
                });
            }
            Some(successors)
        }
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => switch_successor_scans(scan, source, value, default, default_args, &cases),
        Inst::Return { .. } | Inst::Unreachable => Some(Vec::new()),
        _ => Some(Vec::new()),
    }
}

fn switch_successor_scans<'a>(
    scan: FunctionScan<'a>,
    source: BlockId,
    value: ValueId,
    default: BlockId,
    default_args: Vec<ValueId>,
    cases: &[SwitchCase],
) -> Option<Vec<SuccessorScan<'a>>> {
    let selector = scan
        .values
        .get(&value)
        .and_then(|facts| facts.expr.clone())?;
    let width = selector
        .try_bv_width()
        .ok()
        .filter(|width| (1..=64).contains(width))?;
    let mut successors = Vec::with_capacity(cases.len() + 1);

    for case in cases {
        let guard = switch_case_guard(&selector, width, &case.value)?;
        if let Some(successor) =
            guarded_successor_scan(scan.clone(), source, guard, case.target, case.args.clone())
        {
            successors.push(successor);
        }
    }

    let default_guard = switch_default_guard(&selector, width, cases)?;
    if let Some(successor) =
        guarded_successor_scan(scan, source, default_guard, default, default_args)
    {
        successors.push(successor);
    }

    Some(successors)
}

fn guarded_successor_scan<'a>(
    mut scan: FunctionScan<'a>,
    source: BlockId,
    guard: SmtExpr,
    target: BlockId,
    args: Vec<ValueId>,
) -> Option<SuccessorScan<'a>> {
    if guard_is_concrete_false(&guard) {
        return None;
    }
    scan.ctx.guards.push(guard);
    Some(SuccessorScan {
        source,
        target,
        args,
        scan,
    })
}

fn context_has_new_concrete_false_guard(ctx: &PathContext, original_guard_len: usize) -> bool {
    ctx.guards[original_guard_len..]
        .iter()
        .any(guard_is_concrete_false)
}

fn enqueue_edge<'a>(
    mut scan: FunctionScan<'a>,
    target: BlockId,
    args: &[ValueId],
    worklist: &mut VecDeque<FunctionScan<'a>>,
) {
    let Some(target_block) = function_block(scan.function, target) else {
        return;
    };
    bind_block_params(&mut scan, target_block, args);
    scan.block = target_block;
    scan.diagnostics.clear();
    scan.unknown_obligations.clear();
    worklist.push_back(scan);
}

fn bind_block_params(scan: &mut FunctionScan<'_>, target: &Block, args: &[ValueId]) {
    let arg_facts = args
        .iter()
        .map(|arg| scan.values.get(arg).cloned())
        .collect::<Vec<_>>();
    for ((param, ty), facts) in target.params.iter().zip(arg_facts) {
        let facts = facts.unwrap_or(ValueFacts {
            ty: ty.clone(),
            expr: None,
            pointer: None,
        });
        scan.values.insert(*param, facts);
    }
}

impl<'a> FunctionScan<'a> {
    fn new(module: &'a Module, function: &'a Function, block: &'a Block) -> Self {
        let mut values = HashMap::new();
        for (value, ty) in &block.params {
            values.insert(*value, parameter_facts(function, *value, ty));
        }

        Self {
            module,
            function,
            block,
            values,
            ctx: PathContext {
                guards: Vec::new(),
                witness_candidates: Vec::new(),
            },
            uaf_events: Vec::new(),
            uaf_reported: false,
            diagnostics: Vec::new(),
            unknown_obligations: Vec::new(),
            covered: HashSet::new(),
            coverage_errors: Vec::new(),
            #[cfg(test)]
            force_drop_deref: false,
        }
    }

    fn run_block(&mut self) {
        // Fail-closed deref-coverage invariant. Structurally enumerate every
        // reachable memory-access site in this block BEFORE walking it, then
        // after the walk assert each enumerated site recorded a verdict. A
        // reachable deref that produces no verdict is a dropped obligation:
        // the scanner would be asserting a safety it never proved (fail-open).
        // We record an `FsymCoverageError` instead so callers fail closed —
        // the same discipline as the opcode coverage_gate.
        self.covered.clear();
        let expected = reachable_memory_access_sites(self.block);

        for (inst_index, node) in self.block.body.iter().enumerate() {
            if node.is_terminator() {
                break;
            }
            self.visit_node(node, inst_index);
        }

        for (inst_index, opcode) in expected {
            if !self.covered.contains(&inst_index) {
                self.coverage_errors.push(FsymCoverageError {
                    module: self.module.name.clone(),
                    function: self.function.name.clone(),
                    block: self.block.id.index(),
                    inst_index,
                    opcode,
                    detail: format!(
                        "reachable {opcode} dereference recorded no Safe/Diagnostic/Unknown verdict"
                    ),
                });
            }
        }
    }

    fn visit_node(&mut self, node: &InstrNode, inst_index: usize) {
        match &node.inst {
            Inst::Const { ty, value } => {
                // A constant pointer holds a fixed address. A NONZERO constant
                // address is provably non-null, so model it with PointerFacts
                // (`null_expr` = the address) exactly as `NullPtr`/`Alloca` do,
                // rather than leaving a constant-address dereference as an
                // unaccounted "pointer facts unavailable" Unknown. The address
                // is built at the fixed 64-bit pointer width here because
                // `constant_expr` declines `Ty::Ptr` (its bit width is
                // target-dependent / `None`). Bounds stay abstained:
                // `object_size_bytes` is unknown for a raw address, so
                // `check_bounds` still declines to prove in-bounds (no new
                // safety claim); a literal null (`value == 0`) keeps the
                // existing fail-closed path. [TCG-FSYM-CONSTPTR]
                match (ty, value) {
                    (Ty::Ptr, Constant::Int(addr_value)) if *addr_value != 0 => {
                        let null_expr = SmtExpr::bv_const(*addr_value as u64, 64);
                        let pointer = PointerFacts {
                            null_expr: null_expr.clone(),
                            object: None,
                            byte_offset: Some(SmtExpr::bv_const(0, 64)),
                            object_size_bytes: None,
                            in_bounds_proven: has_proof(node, ProofAnnotation::InBounds),
                            not_null_proven: has_proof(node, ProofAnnotation::NotNull),
                        };
                        self.define_value(node, Ty::Ptr, Some(null_expr), Some(pointer));
                    }
                    _ => {
                        let expr = constant_expr(ty, value);
                        self.define_value(node, ty.clone(), expr, None);
                    }
                }
            }
            Inst::NullPtr => {
                let pointer = PointerFacts {
                    null_expr: SmtExpr::bv_const(0, 64),
                    object: None,
                    byte_offset: None,
                    object_size_bytes: None,
                    in_bounds_proven: has_proof(node, ProofAnnotation::InBounds),
                    not_null_proven: has_proof(node, ProofAnnotation::NotNull),
                };
                self.define_value(
                    node,
                    Ty::Ptr,
                    Some(pointer.null_expr.clone()),
                    Some(pointer),
                );
            }
            Inst::Alloca { ty, count, .. } => {
                let pointer = self.alloca_pointer(node, ty, *count, inst_index);
                self.define_value(
                    node,
                    Ty::Ptr,
                    Some(pointer.null_expr.clone()),
                    Some(pointer),
                );
            }
            Inst::Copy { ty, operand } => {
                let facts = self.values.get(operand).cloned();
                self.define_value(
                    node,
                    ty.clone(),
                    facts.as_ref().and_then(|facts| facts.expr.clone()),
                    facts.and_then(|facts| facts.pointer),
                );
            }
            Inst::Cast {
                op,
                dst_ty,
                operand,
                ..
            } => {
                let source = self.values.get(operand).cloned();
                let expr = source
                    .as_ref()
                    .and_then(|source| cast_expr(*op, &source.ty, dst_ty, source.expr.clone()?));
                let pointer = cast_pointer(*op, dst_ty, source.as_ref(), expr.clone());
                self.define_value(node, dst_ty.clone(), expr, pointer);
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                self.check_arithmetic(node, inst_index, *op, ty, *lhs, *rhs);
                let expr = self.binop_expr(*op, *lhs, *rhs);
                self.define_value(node, ty.clone(), expr, None);
            }
            Inst::UnOp { op, ty, operand } => {
                self.check_unary(node, inst_index, *op, ty, *operand);
                let expr = self.unop_expr(*op, *operand);
                self.define_value(node, ty.clone(), expr, None);
            }
            Inst::ICmp { op, lhs, rhs, .. } => {
                let expr = self.icmp_expr(*op, *lhs, *rhs);
                self.define_value(node, Ty::Bool, expr, None);
            }
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                let expr = self.select_expr(*cond, *then_val, *else_val);
                self.define_value(node, ty.clone(), expr, None);
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                // SOUNDNESS: deliberately ignore the producer's `inbounds`
                // claim. This is a memory-safety checker; trusting an
                // unverified no-wrap/in-bounds hint could suppress a genuine
                // out-of-bounds finding. The symbolic address is computed
                // conservatively from base + index*size and bounds are checked
                // independently regardless of this flag.
                inbounds: _,
            } => {
                let pointer = self.gep_pointer(node, pointee_ty, *base, indices);
                self.define_value(
                    node,
                    Ty::Ptr,
                    pointer.as_ref().map(|pointer| pointer.null_expr.clone()),
                    pointer,
                );
            }
            Inst::Load { ty, ptr, .. } | Inst::AtomicLoad { ty, ptr, .. } => {
                self.check_memory_read(node, inst_index, ty, *ptr);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::Store { ty, ptr, .. } | Inst::AtomicStore { ty, ptr, .. } => {
                self.check_memory_write(node, inst_index, ty, *ptr);
            }
            Inst::AtomicRMW { ty, ptr, .. } | Inst::CmpXchg { ty, ptr, .. } => {
                self.check_memory_write(node, inst_index, ty, *ptr);
                self.define_value(node, ty.clone(), None, None);
            }
            Inst::Dealloc { ptr } => {
                self.check_uaf_event(node, inst_index, *ptr, UafEventKind::Free);
            }
            Inst::Assume { cond } => {
                if let Some(expr) = self.values.get(cond).and_then(|facts| facts.expr.clone()) {
                    self.ctx.guards.push(expr);
                }
            }
            Inst::Overflow { op, ty, lhs, rhs } => {
                self.define_overflow(node, *op, ty, *lhs, *rhs);
            }
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } | Inst::IsUnique { ptr } => {
                let source = self.values.get(ptr).cloned();
                self.define_value(
                    node,
                    Ty::Ptr,
                    source.as_ref().and_then(|facts| facts.expr.clone()),
                    source.and_then(|facts| facts.pointer),
                );
            }
            Inst::Retain { ptr } | Inst::Release { ptr } | Inst::EndBorrow { borrow_ptr: ptr } => {
                self.check_uaf_event(node, inst_index, *ptr, UafEventKind::Use);
            }
            _ => {}
        }
    }

    fn alloca_pointer(
        &self,
        node: &InstrNode,
        ty: &Ty,
        count: Option<ValueId>,
        inst_index: usize,
    ) -> PointerFacts {
        let object_id = ((self.function.id.index() as u64 + 1) << 32)
            | ((self.block.id.index() as u64 + 1) << 16)
            | (inst_index as u64 + 1);
        let element_size = self.type_size_bytes(ty);
        let count = count
            .and_then(|count| self.values.get(&count))
            .and_then(|facts| facts.expr.as_ref())
            .and_then(eval_concrete_u64)
            .unwrap_or(1);
        let object_size_bytes = element_size.and_then(|size| size.checked_mul(count));

        PointerFacts {
            null_expr: SmtExpr::bv_const(object_id, 64),
            object: Some(SmtExpr::bv_const(object_id, 64)),
            byte_offset: Some(SmtExpr::bv_const(0, 64)),
            object_size_bytes: object_size_bytes.map(|size| SmtExpr::bv_const(size, 64)),
            in_bounds_proven: has_proof(node, ProofAnnotation::InBounds),
            not_null_proven: true,
        }
    }

    fn gep_pointer(
        &self,
        node: &InstrNode,
        pointee_ty: &Ty,
        base: ValueId,
        indices: &[ValueId],
    ) -> Option<PointerFacts> {
        let mut pointer = self.values.get(&base)?.pointer.clone()?;
        pointer.in_bounds_proven |= has_proof(node, ProofAnnotation::InBounds);
        pointer.not_null_proven |= has_proof(node, ProofAnnotation::NotNull);

        match indices {
            [] => Some(pointer),
            [index] => {
                let index_facts = self.values.get(index)?;
                let index_expr = widen_index_to_i64(index_facts.expr.clone()?, &index_facts.ty)?;
                let elem_size = self.type_size_bytes(pointee_ty)?;
                let scaled = if elem_size == 1 {
                    index_expr
                } else {
                    index_expr.bvmul(SmtExpr::bv_const(elem_size, 64))
                };
                let base_offset = pointer.byte_offset.clone()?;
                pointer.byte_offset = Some(base_offset.bvadd(scaled));
                Some(pointer)
            }
            _ => None,
        }
    }

    fn check_memory_read(&mut self, node: &InstrNode, inst_index: usize, ty: &Ty, ptr: ValueId) {
        self.check_null(node, inst_index, ptr);
        self.check_bounds(node, inst_index, ty, ptr);
        self.check_uaf_event(node, inst_index, ptr, UafEventKind::Load);
    }

    fn check_memory_write(&mut self, node: &InstrNode, inst_index: usize, ty: &Ty, ptr: ValueId) {
        self.check_null(node, inst_index, ptr);
        self.check_bounds(node, inst_index, ty, ptr);
        self.check_uaf_event(node, inst_index, ptr, UafEventKind::Store);
    }

    fn check_null(&mut self, node: &InstrNode, inst_index: usize, ptr: ValueId) {
        // Test-only fault injection: silently drop the obligation (the exact
        // shape of the regression this invariant guards against) so the
        // deref-coverage check can be tested for firing. No effect in release.
        #[cfg(test)]
        if self.force_drop_deref {
            return;
        }
        let Some(pointer) = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone())
        else {
            // Fail closed: a reachable deref whose pointer has no modeled
            // facts is NOT safe. Record an Unknown (a solver candidate the
            // caller can escalate) instead of silently returning — a missing
            // model must never be an implicit not-null proof. This also keeps
            // the deref-coverage invariant honest: the site is accounted for.
            self.record_unaccounted_deref(
                node,
                inst_index,
                FsymTrustIrDiagnosticKind::NullDeref,
                "null pointer dereference",
                "pointer facts unavailable; cannot prove not-null",
            );
            return;
        };
        let candidate_expression = pointer.null_expr.to_string();
        let solver_obligation = FsymTrustIrSolverObligation::NullDeref {
            ptr: pointer.null_expr.clone(),
            ptr_width: 64,
        };
        let verdict = check_null_deref(
            &MemOp {
                label: self.label(inst_index, "memory"),
                ptr: pointer.null_expr,
                ptr_width: 64,
                has_not_null_annotation: pointer.not_null_proven
                    || has_proof(node, ProofAnnotation::NotNull),
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::NullDeref,
            "null pointer dereference",
            verdict,
            (Some(candidate_expression), Some(solver_obligation)),
        );
    }

    fn check_bounds(&mut self, node: &InstrNode, inst_index: usize, ty: &Ty, ptr: ValueId) {
        let Some(pointer) = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.clone())
        else {
            return;
        };
        let Some(byte_offset) = pointer.byte_offset else {
            return;
        };
        let Some(object_size_bytes) = pointer.object_size_bytes else {
            return;
        };
        let Some(access_size_bytes) = self.type_size_bytes(ty) else {
            return;
        };

        let candidate_expression = format!(
            "bounds side condition: offset={}, object_size={}, access_size={}",
            byte_offset, object_size_bytes, access_size_bytes
        );
        let solver_obligation =
            bounds_solver_obligation(&byte_offset, &object_size_bytes, access_size_bytes);
        let verdict = check_oob_ub(
            &BoundsOp {
                label: self.label(inst_index, "memory"),
                byte_offset: byte_offset.clone(),
                object_size_bytes: object_size_bytes.clone(),
                access_size_bytes,
                has_in_bounds_annotation: pointer.in_bounds_proven
                    || has_proof(node, ProofAnnotation::InBounds),
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::OutOfBounds,
            "out-of-bounds memory access",
            verdict,
            (Some(candidate_expression), solver_obligation),
        );
    }

    fn check_uaf_event(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        ptr: ValueId,
        kind: UafEventKind,
    ) {
        if self.uaf_reported {
            return;
        }
        let Some(object) = self
            .values
            .get(&ptr)
            .and_then(|facts| facts.pointer.as_ref())
            .and_then(|pointer| pointer.object.clone())
        else {
            return;
        };

        let candidate_expression = object.to_string();
        self.uaf_events.push(UafEvent {
            label: self.label(inst_index, "lifetime"),
            kind,
            object,
        });

        let verdict = check_uaf_ub(&self.uaf_events, &self.ctx);
        if matches!(verdict, FsymVerdict::Ub { .. }) {
            self.uaf_reported = true;
        }
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::UseAfterFree,
            "use after free or double free",
            verdict,
            (Some(candidate_expression), None),
        );
    }

    fn check_arithmetic(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        op: BinOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) {
        let Some(kind) = arith_ub_kind(op, ty) else {
            return;
        };
        let Some(width) = ty.bit_width().filter(|width| *width <= 64) else {
            return;
        };
        let Some(lhs) = self.values.get(&lhs).and_then(|facts| facts.expr.clone()) else {
            return;
        };
        let Some(rhs) = self.values.get(&rhs).and_then(|facts| facts.expr.clone()) else {
            return;
        };

        let candidate_expression = format!("{op} side condition: {lhs}, {rhs}");
        let solver_obligation = FsymTrustIrSolverObligation::Arithmetic {
            kind,
            lhs: lhs.clone(),
            rhs: Some(rhs.clone()),
            width,
        };
        let verdict = check_arith_ub(
            &ArithOp {
                label: self.label(inst_index, op),
                kind,
                lhs,
                rhs,
                width,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Arithmetic,
            format!("arithmetic UB in `{op}`"),
            verdict,
            (Some(candidate_expression), Some(solver_obligation)),
        );
    }

    fn check_unary(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        op: UnOp,
        ty: &Ty,
        operand: ValueId,
    ) {
        if !matches!(op, UnOp::Neg) || !ty.is_signed() {
            return;
        }
        let Some(width) = ty.bit_width().filter(|width| *width <= 64) else {
            return;
        };
        let Some(lhs) = self
            .values
            .get(&operand)
            .and_then(|facts| facts.expr.clone())
        else {
            return;
        };

        let candidate_expression = format!("neg side condition: {lhs}");
        let solver_obligation = FsymTrustIrSolverObligation::Arithmetic {
            kind: ArithUbKind::Sneg,
            lhs: lhs.clone(),
            rhs: None,
            width,
        };
        let verdict = check_arith_ub(
            &ArithOp {
                label: self.label(inst_index, op),
                kind: ArithUbKind::Sneg,
                lhs,
                rhs: SmtExpr::bv_const(0, width),
                width,
            },
            &self.ctx,
        );
        self.record_verdict(
            node,
            inst_index,
            FsymTrustIrDiagnosticKind::Arithmetic,
            "arithmetic UB in `neg`",
            verdict,
            (Some(candidate_expression), Some(solver_obligation)),
        );
    }

    fn record_verdict(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        kind: FsymTrustIrDiagnosticKind,
        message: impl Into<String>,
        verdict: FsymVerdict,
        evidence: VerdictEvidence,
    ) {
        let (candidate_expression, solver_obligation) = evidence;
        let message = message.into();
        // Deref-coverage accounting: this (block, inst_index) site is now
        // discharged by a verdict. `Safe` is a justified pass (a dominating
        // not-null/in-bounds proof, an annotation, or a concrete-nonzero
        // address), `Ub` is a concrete diagnostic, `Unknown` is a recorded
        // solver candidate. All three count as accounted; the only thing the
        // invariant forbids is a reachable deref that records NONE of them.
        self.covered.insert(inst_index);
        match verdict {
            FsymVerdict::Safe => {}
            FsymVerdict::Ub { witness } => {
                let mut witness: Vec<(String, u64)> = witness.into_iter().collect();
                witness.sort_by(|a, b| a.0.cmp(&b.0));
                self.diagnostics.push(FsymTrustIrDiagnostic {
                    kind,
                    module: self.module.name.clone(),
                    function: self.function.name.clone(),
                    block: self.block.id.index(),
                    inst_index,
                    span: node.span,
                    message,
                    witness,
                });
            }
            FsymVerdict::Unknown { reason } => {
                let path_guards = self.ctx.guards.iter().map(ToString::to_string).collect();
                let solver_candidate =
                    solver_obligation.map(|obligation| FsymTrustIrSolverCandidate {
                        path_guards: self.ctx.guards.clone(),
                        obligation,
                    });
                self.unknown_obligations.push(FsymTrustIrUnknown {
                    kind,
                    label: self.label(inst_index, &message),
                    module: self.module.name.clone(),
                    function: self.function.name.clone(),
                    block: self.block.id.index(),
                    inst_index,
                    reason,
                    path_guards,
                    candidate_expression,
                    solver_candidate,
                });
            }
        }
    }

    /// Record a reachable deref that the scanner cannot model (no pointer
    /// facts / size / offset) as a fail-closed `Unknown` obligation.
    ///
    /// This is the structural complement of the deref-coverage invariant: the
    /// absence of a model must route through `record_verdict` (as Unknown, a
    /// recorded solver candidate) rather than bypass it via an early return.
    /// That guarantees no reachable deref is ever an implicit pass, and that
    /// the site is marked covered so the invariant is satisfied honestly
    /// rather than by suppression.
    fn record_unaccounted_deref(
        &mut self,
        node: &InstrNode,
        inst_index: usize,
        kind: FsymTrustIrDiagnosticKind,
        message: impl Into<String>,
        reason: impl Into<String>,
    ) {
        self.record_verdict(
            node,
            inst_index,
            kind,
            message,
            FsymVerdict::Unknown {
                reason: reason.into(),
            },
            (None, None),
        );
    }

    fn define_value(
        &mut self,
        node: &InstrNode,
        ty: Ty,
        expr: Option<SmtExpr>,
        pointer: Option<PointerFacts>,
    ) {
        if let Some(result) = node.results.first().copied() {
            self.values.insert(result, ValueFacts { ty, expr, pointer });
        }
    }

    fn define_overflow(
        &mut self,
        node: &InstrNode,
        op: OverflowOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) {
        let result_expr = match op {
            OverflowOp::AddOverflow => self.binop_expr(BinOp::Add, lhs, rhs),
            OverflowOp::SubOverflow => self.binop_expr(BinOp::Sub, lhs, rhs),
            OverflowOp::MulOverflow => self.binop_expr(BinOp::Mul, lhs, rhs),
        };

        if let Some(result) = node.results.first().copied() {
            self.values.insert(
                result,
                ValueFacts {
                    ty: ty.clone(),
                    expr: result_expr,
                    pointer: None,
                },
            );
        }
        if let Some(flag) = node.results.get(1).copied() {
            self.values.insert(
                flag,
                ValueFacts {
                    ty: Ty::Bool,
                    expr: None,
                    pointer: None,
                },
            );
        }
    }

    fn binop_expr(&self, op: BinOp, lhs: ValueId, rhs: ValueId) -> Option<SmtExpr> {
        let lhs = self.values.get(&lhs)?.expr.clone()?;
        let rhs = self.values.get(&rhs)?.expr.clone()?;
        same_bv_width(&lhs, &rhs)?;
        Some(match op {
            BinOp::Add => lhs.bvadd(rhs),
            BinOp::Sub => lhs.bvsub(rhs),
            BinOp::Mul => lhs.bvmul(rhs),
            BinOp::UDiv => lhs.bvudiv(rhs),
            BinOp::SDiv => lhs.bvsdiv(rhs),
            BinOp::URem => lhs.bvurem(rhs),
            BinOp::And => lhs.bvand(rhs),
            BinOp::Or => lhs.bvor(rhs),
            BinOp::Xor => lhs.bvxor(rhs),
            BinOp::Shl => lhs.bvshl(rhs),
            BinOp::LShr => lhs.bvlshr(rhs),
            BinOp::AShr => lhs.bvashr(rhs),
            BinOp::SRem
            | BinOp::FAdd
            | BinOp::FSub
            | BinOp::FMul
            | BinOp::FDiv
            | BinOp::FRem
            | BinOp::FMin
            | BinOp::FMax => {
                return None;
            }
        })
    }

    fn unop_expr(&self, op: UnOp, operand: ValueId) -> Option<SmtExpr> {
        let operand = self.values.get(&operand)?.expr.clone()?;
        Some(match op {
            UnOp::Neg => operand.bvneg(),
            UnOp::Not | UnOp::FNeg => return None,
            _ => return None,
        })
    }

    fn icmp_expr(&self, op: ICmpOp, lhs: ValueId, rhs: ValueId) -> Option<SmtExpr> {
        let lhs = self.values.get(&lhs)?.expr.clone()?;
        let rhs = self.values.get(&rhs)?.expr.clone()?;
        same_bv_width(&lhs, &rhs)?;
        Some(match op {
            ICmpOp::Eq => lhs.eq_expr(rhs),
            ICmpOp::Ne => lhs.eq_expr(rhs).not_expr(),
            ICmpOp::Ult => lhs.bvult(rhs),
            ICmpOp::Ule => lhs.bvule(rhs),
            ICmpOp::Ugt => lhs.bvugt(rhs),
            ICmpOp::Uge => lhs.bvuge(rhs),
            ICmpOp::Slt => lhs.bvslt(rhs),
            ICmpOp::Sle => lhs.bvsle(rhs),
            ICmpOp::Sgt => lhs.bvsgt(rhs),
            ICmpOp::Sge => lhs.bvsge(rhs),
        })
    }

    fn select_expr(&self, cond: ValueId, then_val: ValueId, else_val: ValueId) -> Option<SmtExpr> {
        let cond = self.values.get(&cond)?.expr.clone()?;
        let then_expr = self.values.get(&then_val)?.expr.clone()?;
        let else_expr = self.values.get(&else_val)?.expr.clone()?;
        Some(SmtExpr::ite(cond, then_expr, else_expr))
    }

    fn type_size_bytes(&self, ty: &Ty) -> Option<u64> {
        translate_type_with_tables(ty, &self.module.structs, &self.module.types)
            .ok()
            .map(|ty| u64::from(ty.bytes()))
    }

    fn label(&self, inst_index: usize, subject: impl fmt::Display) -> String {
        format!(
            "{} bb{} inst{} {}",
            self.function.name,
            self.block.id.index(),
            inst_index,
            subject
        )
    }
}

fn parameter_facts(function: &Function, value: ValueId, ty: &Ty) -> ValueFacts {
    let expr = parameter_expr(function, value, ty);
    let pointer = if is_pointer_like_ty(ty) {
        expr.clone().map(|expr| PointerFacts {
            null_expr: expr,
            object: None,
            byte_offset: None,
            object_size_bytes: None,
            in_bounds_proven: false,
            not_null_proven: false,
        })
    } else {
        None
    };

    ValueFacts {
        ty: ty.clone(),
        expr,
        pointer,
    }
}

/// Thin-pointer width (bits) the scanner models pointers with.
///
/// The scanner hardcodes 64-bit pointer obligations everywhere (see
/// `check_null` `ptr_width: 64`). `Ty::bit_width()` deliberately returns
/// `None` for pointer-like types because their width is target-dependent
/// (`bit_width_with(pointer_bits)`); resolving them here at the same 64 the
/// rest of the scanner assumes keeps pointer params modeled rather than
/// silently dropped. Trust: this MUST match the `ptr_width` constants below.
const FSYM_TRUST_IR_POINTER_BITS: u32 = 64;

/// True for every pointer-like Trust IR type the scanner treats as a
/// dereferenceable pointer (bare `Ptr`, raw `*const`/`*mut`, Rust
/// `&`/`&mut`, `Rc`, and the data lane of a fat pointer `FatPtr`). A
/// null/bounds/UAF obligation rooted at a parameter of any of these types must
/// not be silently dropped.
///
/// `FatPtr` is included for type-set CONSISTENCY with `Ty::bit_width_with`,
/// which sizes a fat pointer at `2 * pointer_bits` (128 on a 64-bit target):
/// without this entry a `FatPtr` param got neither a symbolic expr (the 128-bit
/// width tripped the `width > 64` guard in `parameter_expr`) NOR `PointerFacts`,
/// so its derefs routed to unaccounted/unknown rather than analyzed. We model
/// the dereferenceable DATA-pointer lane of the fat pointer at the same 64-bit
/// `FSYM_TRUST_IR_POINTER_BITS` the rest of the scanner assumes (see
/// `parameter_expr`'s FatPtr arm); the 128-bit semantic width is unchanged
/// everywhere else. Keep this predicate and `parameter_expr` in lockstep so the
/// two can never drift again.
fn is_pointer_like_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
            | Ty::FatPtr(_)
    )
}

fn parameter_expr(function: &Function, value: ValueId, ty: &Ty) -> Option<SmtExpr> {
    // A fat pointer is two pointer-sized lanes (`bit_width_with` sizes it at
    // `2 * pointer_bits` = 128 on a 64-bit target). The dereferenceable lane is
    // the DATA pointer; model it at the scanner's thin-pointer width (64) so a
    // FatPtr param gets a symbolic address (and thus PointerFacts) at the same
    // `ptr_width: 64` the deref obligations assume — rather than vanishing under
    // the `width > 64` guard. We do NOT relax that guard globally; this is a
    // FatPtr-specific special case to the 64-bit data lane.
    if matches!(ty, Ty::FatPtr(_)) {
        return Some(SmtExpr::var(
            format!("{}_arg{}", function.name, value.index()),
            FSYM_TRUST_IR_POINTER_BITS,
        ));
    }
    // Pointer-like types have a target-dependent width that `bit_width()`
    // leaves as `None`; resolve them at the scanner's modeled pointer width so
    // a pointer parameter gets a symbolic address (and thus PointerFacts)
    // instead of vanishing. Non-pointer types are unaffected.
    let width = ty.bit_width_with(FSYM_TRUST_IR_POINTER_BITS)?;
    if width == 0 || width > 64 {
        return None;
    }
    Some(SmtExpr::var(
        format!("{}_arg{}", function.name, value.index()),
        width,
    ))
}

/// Structurally enumerate the reachable pointer-dereference sites in `block`.
///
/// Returns `(inst_index, opcode)` for every memory-access instruction the
/// scanner is responsible for accounting with a null/bounds verdict. This is
/// the *expected* set for the fail-closed deref-coverage invariant in
/// `run_block`: the opcodes listed here are exactly the ones `visit_node`
/// routes to `check_memory_read`/`check_memory_write` (Load/AtomicLoad,
/// Store/AtomicStore, AtomicRMW/CmpXchg). Keep this in lockstep with that
/// dispatch — a deref opcode handled there but missing here would let its
/// obligation be dropped without tripping the invariant.
///
/// Instructions past the terminator are unreachable within the block and are
/// not enumerated (the walk stops at the terminator too).
fn reachable_memory_access_sites(block: &Block) -> Vec<(usize, &'static str)> {
    let mut sites = Vec::new();
    for (inst_index, node) in block.body.iter().enumerate() {
        if node.is_terminator() {
            break;
        }
        let opcode = match &node.inst {
            Inst::Load { .. } => Some("Load"),
            Inst::AtomicLoad { .. } => Some("AtomicLoad"),
            Inst::Store { .. } => Some("Store"),
            Inst::AtomicStore { .. } => Some("AtomicStore"),
            Inst::AtomicRMW { .. } => Some("AtomicRMW"),
            Inst::CmpXchg { .. } => Some("CmpXchg"),
            _ => None,
        };
        if let Some(opcode) = opcode {
            sites.push((inst_index, opcode));
        }
    }
    sites
}

fn has_proof(node: &InstrNode, proof: ProofAnnotation) -> bool {
    node.proofs.contains(&proof)
}

fn arith_ub_kind(op: BinOp, ty: &Ty) -> Option<ArithUbKind> {
    match op {
        BinOp::UDiv => Some(ArithUbKind::Udiv),
        BinOp::SDiv => Some(ArithUbKind::Sdiv),
        BinOp::URem => Some(ArithUbKind::Urem),
        BinOp::SRem => Some(ArithUbKind::Srem),
        BinOp::Add if ty.is_signed() => Some(ArithUbKind::Sadd),
        BinOp::Sub if ty.is_signed() => Some(ArithUbKind::Ssub),
        BinOp::Mul if ty.is_signed() => Some(ArithUbKind::Smul),
        _ => None,
    }
}

fn same_bv_width(lhs: &SmtExpr, rhs: &SmtExpr) -> Option<u32> {
    let lhs_width = lhs.try_bv_width().ok()?;
    (lhs_width == rhs.try_bv_width().ok()?).then_some(lhs_width)
}

fn bounds_solver_obligation(
    byte_offset: &SmtExpr,
    object_size_bytes: &SmtExpr,
    access_size_bytes: u64,
) -> Option<FsymTrustIrSolverObligation> {
    let width = same_bv_width(byte_offset, object_size_bytes)?;
    (1..=64)
        .contains(&width)
        .then(|| FsymTrustIrSolverObligation::OutOfBounds {
            byte_offset: byte_offset.clone(),
            object_size_bytes: object_size_bytes.clone(),
            access_size_bytes,
            width,
        })
}

fn switch_selector_width(ty: &Ty) -> Option<u32> {
    if !ty.is_integer() {
        return None;
    }
    let width = ty.bit_width()?;
    (1..=64).contains(&width).then_some(width)
}

fn switch_case_guard(selector: &SmtExpr, width: u32, value: &Constant) -> Option<SmtExpr> {
    let Constant::Int(value) = value else {
        return None;
    };
    Some(
        selector
            .clone()
            .eq_expr(SmtExpr::bv_const(*value as u64, width)),
    )
}

fn switch_default_guard(selector: &SmtExpr, width: u32, cases: &[SwitchCase]) -> Option<SmtExpr> {
    let mut guard = SmtExpr::bool_const(true);
    for case in cases {
        guard = guard.and_expr(switch_case_guard(selector, width, &case.value)?.not_expr());
    }
    Some(guard)
}

fn guard_is_concrete_false(guard: &SmtExpr) -> bool {
    let empty_env = HashMap::new();
    match guard.try_eval(&empty_env).ok() {
        Some(EvalResult::Bool(false)) => true,
        Some(EvalResult::Bv(0) | EvalResult::Bv128(0)) if guard.try_bv_width().ok() == Some(1) => {
            true
        }
        _ => false,
    }
}

fn constant_expr(ty: &Ty, value: &Constant) -> Option<SmtExpr> {
    match value {
        Constant::Int(value) => {
            let width = ty.bit_width()?;
            if width == 0 || width > 64 {
                return None;
            }
            Some(SmtExpr::bv_const(*value as u64, width))
        }
        Constant::Bool(value) => Some(SmtExpr::bool_const(*value)),
        Constant::Float(value) => match ty {
            Ty::F32 => Some(SmtExpr::fp32_const(*value as f32)),
            Ty::F64 => Some(SmtExpr::fp64_const(*value)),
            _ => None,
        },
        // trust-ir v24 U128: the scanner's SMT lane is <= 64-bit (same gate
        // as the Int arm's `width > 64` bail) and a canonical U128 exceeds
        // i128::MAX by definition — no bit-vector to model; fail closed.
        Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Aggregate(_)
        | Constant::Array(_)
        | Constant::Vector(_)
        | Constant::Sequence(_)
        | Constant::Set(_)
        | Constant::Record(_)
        | Constant::Closure { .. }
        | Constant::FnDef(_)
        // A symbol address has no concrete value until link time, so there is
        // no SMT bit-vector to model it as.
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => None,
    }
}

fn cast_expr(op: CastOp, src_ty: &Ty, dst_ty: &Ty, expr: SmtExpr) -> Option<SmtExpr> {
    // Resolve pointer-like widths at the fixed 64-bit pointer width (as the rest
    // of the scanner does, e.g. `parameter_expr`). `Ty::bit_width()` returns
    // `None` for pointers (target-dependent), which would otherwise make the
    // `IntToPtr`/`PtrToInt`/`Bitcast` arm below dead — leaving an int↔ptr cast
    // result with no SMT expr, hence a deref through it as an unaccounted
    // "pointer facts unavailable" Unknown instead of a candidate the solver can
    // discharge.
    let src_width = src_ty.bit_width_with(FSYM_TRUST_IR_POINTER_BITS)?;
    let dst_width = dst_ty.bit_width_with(FSYM_TRUST_IR_POINTER_BITS)?;
    if src_width == 0 || dst_width == 0 || src_width > 64 || dst_width > 64 {
        return None;
    }

    match op {
        CastOp::Trunc if dst_width <= src_width => Some(expr.extract(dst_width - 1, 0)),
        CastOp::ZExt if dst_width >= src_width => Some(expr.zero_ext(dst_width - src_width)),
        CastOp::SExt if dst_width >= src_width => Some(expr.sign_ext(dst_width - src_width)),
        CastOp::PtrToInt | CastOp::IntToPtr | CastOp::Bitcast if src_width == dst_width => {
            Some(expr)
        }
        _ => None,
    }
}

fn cast_pointer(
    op: CastOp,
    dst_ty: &Ty,
    source: Option<&ValueFacts>,
    expr: Option<SmtExpr>,
) -> Option<PointerFacts> {
    if !matches!(
        dst_ty,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_)
    ) {
        return None;
    }

    if matches!(op, CastOp::Bitcast)
        && let Some(pointer) = source.and_then(|facts| facts.pointer.clone())
    {
        return Some(pointer);
    }

    expr.map(|expr| PointerFacts {
        null_expr: expr,
        object: None,
        byte_offset: None,
        object_size_bytes: None,
        in_bounds_proven: false,
        not_null_proven: false,
    })
}

fn widen_index_to_i64(expr: SmtExpr, ty: &Ty) -> Option<SmtExpr> {
    let width = expr.try_bv_width().ok()?;
    match width {
        64 => Some(expr),
        1..=63 if ty.is_signed() => Some(expr.sign_ext(64 - width)),
        1..=63 => Some(expr.zero_ext(64 - width)),
        _ => None,
    }
}

fn eval_concrete_u64(expr: &SmtExpr) -> Option<u64> {
    let empty_env = HashMap::new();
    match expr.try_eval(&empty_env).ok()? {
        EvalResult::Bv(value) => Some(value),
        EvalResult::Bv128(value) => u64::try_from(value).ok(),
        // Poison (a trapping-op result) has no defined concrete value; fail closed.
        EvalResult::Bool(_)
        | EvalResult::Float(_)
        | EvalResult::Array { .. }
        | EvalResult::Poison => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        FSYM_TRUST_IR_MAX_SWITCH_CASES, FSYM_TRUST_IR_POINTER_BITS, FsymTrustIrDiagnosticKind,
        FsymTrustIrSkipReason, FsymTrustIrSolverObligation, FunctionScan, is_pointer_like_ty,
        parameter_facts, scan_module,
    };
    use crate::fsym_arith::ArithUbKind;
    use trust_ir::inst::{BindingFrameDef, BindingSlot};
    use trust_ir::ty::FatPtrKind;
    use trust_ir::value::BindingFrameId;
    use trust_ir::{
        BinOp, Block, BlockId, Constant, DialectInst, FuncId, FuncTy, FuncTyId, Function, ICmpOp,
        Inst, InstrNode, Module, SwitchCase, Ty, ValueId,
    };

    /// A `FatPtr` parameter must be type-set CONSISTENT: `is_pointer_like_ty`
    /// reports it as a pointer AND `parameter_facts` attaches `PointerFacts`
    /// whose `null_expr` is the 64-bit DATA-pointer lane — NOT a silent `None`
    /// that would route its derefs to unaccounted/unknown. (Regression guard for
    /// the type-set split between `is_pointer_like_ty` and `bit_width_with`.)
    #[test]
    fn fat_pointer_param_is_pointer_like_and_gets_data_lane_facts() {
        // Sanity: a fat pointer is two pointer-sized lanes (128 on a 64-bit
        // target), which is exactly why the naive width path dropped it.
        assert_eq!(
            Ty::FatPtr(FatPtrKind::Str).bit_width_with(FSYM_TRUST_IR_POINTER_BITS),
            Some(2 * FSYM_TRUST_IR_POINTER_BITS)
        );

        let func = Function::new(
            FuncId::new(0),
            "fatptr_fn",
            FuncTyId::new(0),
            BlockId::new(0),
        );

        for fat in [
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::Slice(trust_ir::value::TyId::new(0))),
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 0 }),
        ] {
            assert!(
                is_pointer_like_ty(&fat),
                "FatPtr must be pointer-like for fact attachment: {fat:?}"
            );
            let facts = parameter_facts(&func, v(0), &fat);
            let pointer = facts
                .pointer
                .unwrap_or_else(|| panic!("FatPtr param must get PointerFacts, not None: {fat:?}"));
            // The modeled lane is the 64-bit thin data pointer, matching the
            // scanner's `ptr_width: 64` deref obligations.
            assert_eq!(
                pointer.null_expr.try_bv_width().unwrap(),
                FSYM_TRUST_IR_POINTER_BITS,
                "FatPtr null_expr must be the 64-bit data lane: {fat:?}"
            );
            assert!(
                facts.expr.is_some(),
                "FatPtr param must get a symbolic expr: {fat:?}"
            );
        }
    }

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    fn test_module(name: &str, body: Vec<InstrNode>) -> Module {
        test_module_blocks(
            name,
            vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body,
            }],
        )
    }

    fn test_module_blocks(name: &str, blocks: Vec<Block>) -> Module {
        let mut module = Module::new(name);
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "test", FuncTyId::new(0), BlockId::new(0));
        function.blocks = blocks;
        module.functions.push(function);
        module
    }

    fn const_i64(result: u32, value: i64) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value.into()),
        })
        .with_result(v(result))
    }

    fn const_bool(result: u32, value: bool) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(value),
        })
        .with_result(v(result))
    }

    fn bin_i64(result: u32, op: BinOp, lhs: u32, rhs: u32) -> InstrNode {
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs: v(lhs),
            rhs: v(rhs),
        })
        .with_result(v(result))
    }

    fn icmp_i64(result: u32, op: ICmpOp, lhs: u32, rhs: u32) -> InstrNode {
        InstrNode::new(Inst::ICmp {
            op,
            ty: Ty::I64,
            lhs: v(lhs),
            rhs: v(rhs),
        })
        .with_result(v(result))
    }

    fn br(target: u32, args: &[u32]) -> InstrNode {
        InstrNode::new(Inst::Br {
            target: BlockId::new(target),
            args: args.iter().copied().map(v).collect(),
        })
    }

    fn condbr(
        cond: u32,
        then_target: u32,
        then_args: &[u32],
        else_target: u32,
        else_args: &[u32],
    ) -> InstrNode {
        InstrNode::new(Inst::CondBr {
            cond: v(cond),
            then_target: BlockId::new(then_target),
            then_args: then_args.iter().copied().map(v).collect(),
            else_target: BlockId::new(else_target),
            else_args: else_args.iter().copied().map(v).collect(),
        })
    }

    fn ret_i64(value: u32) -> InstrNode {
        InstrNode::new(Inst::Return {
            values: vec![v(value)],
        })
    }

    fn assert_skips_unsupported_instruction(module_name: &str, mut body: Vec<InstrNode>) {
        body.push(const_i64(90, 0));
        body.push(ret_i64(90));
        let report = scan_module(&test_module(module_name, body));

        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::UnsupportedInstruction
        );
        assert!(report.skipped_functions[0].detail.contains("unsupported"));
    }

    fn guarded_null_loop_module(name: &str, trip_count: i64, bad_index: i64) -> Module {
        test_module_blocks(
            name,
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![const_i64(0, 0), br(1, &[0])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::I64)],
                    body: vec![
                        const_i64(11, trip_count),
                        icmp_i64(12, ICmpOp::Slt, 10, 11),
                        condbr(12, 2, &[], 4, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        const_i64(20, bad_index),
                        icmp_i64(21, ICmpOp::Eq, 10, 20),
                        condbr(21, 3, &[], 5, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(30)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(30),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(31)),
                        br(5, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(4),
                    params: vec![],
                    body: vec![const_i64(40, 0), ret_i64(40)],
                },
                Block {
                    id: BlockId::new(5),
                    params: vec![],
                    body: vec![
                        const_i64(50, 1),
                        bin_i64(51, BinOp::Add, 10, 50),
                        br(1, &[51]),
                    ],
                },
            ],
        )
    }

    #[test]
    fn reports_concrete_null_load() {
        let module = test_module(
            "fsym_null",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
    }

    #[test]
    fn reports_concrete_division_by_zero() {
        let module = test_module(
            "fsym_divzero",
            vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(42),
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::Arithmetic
        );
    }

    #[test]
    fn records_symbolic_arithmetic_unknown_solver_candidate() {
        let module = test_module_blocks(
            "fsym_symbolic_sadd",
            vec![Block {
                id: BlockId::new(0),
                params: vec![(v(0), Ty::I8), (v(1), Ty::I8)],
                body: vec![
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Ne,
                        ty: Ty::I8,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Assume { cond: v(2) }),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I8,
                        lhs: v(0),
                        rhs: v(1),
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            }],
        );

        let report = scan_module(&module);

        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unknown_obligations.len(), 1);
        assert_eq!(
            report.unknown_obligations[0].kind,
            FsymTrustIrDiagnosticKind::Arithmetic
        );
        let solver_candidate = report.unknown_obligations[0]
            .solver_candidate
            .as_ref()
            .expect("arithmetic unknown should carry a typed solver candidate");
        assert_eq!(solver_candidate.path_guards.len(), 1);
        match &solver_candidate.obligation {
            FsymTrustIrSolverObligation::Arithmetic { kind, width, .. } => {
                assert_eq!(*kind, ArithUbKind::Sadd);
                assert_eq!(*width, 8);
            }
            other => panic!("expected arithmetic solver candidate, got {other:?}"),
        }
    }

    #[test]
    fn reports_concrete_out_of_bounds_load() {
        let module = test_module(
            "fsym_oob",
            vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(1)),
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I64,
                    base: v(0),
                    indices: vec![v(1)],
                    inbounds: false,
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(2),
                    volatile: false,
                    align: None,
                })
                .with_result(v(3)),
                InstrNode::new(Inst::Return { values: vec![v(3)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::OutOfBounds
        );
    }

    #[test]
    fn records_symbolic_oob_unknown_solver_candidate() {
        let module = test_module_blocks(
            "fsym_symbolic_oob",
            vec![Block {
                id: BlockId::new(0),
                params: vec![(v(0), Ty::I64)],
                body: vec![
                    InstrNode::new(Inst::Alloca {
                        ty: Ty::I64,
                        count: None,
                        align: None,
                    })
                    .with_result(v(1)),
                    InstrNode::new(Inst::GEP {
                        pointee_ty: Ty::I64,
                        base: v(1),
                        indices: vec![v(0)],
                        inbounds: false,
                    })
                    .with_result(v(2)),
                    InstrNode::new(Inst::Load {
                        ty: Ty::I64,
                        ptr: v(2),
                        volatile: false,
                        align: None,
                    })
                    .with_result(v(3)),
                    InstrNode::new(Inst::Return { values: vec![v(3)] }),
                ],
            }],
        );

        let report = scan_module(&module);

        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unknown_obligations.len(), 1);
        let unknown = &report.unknown_obligations[0];
        assert_eq!(unknown.kind, FsymTrustIrDiagnosticKind::OutOfBounds);
        assert!(
            unknown
                .candidate_expression
                .as_deref()
                .is_some_and(|candidate| candidate.contains("bounds side condition"))
        );
        let solver_candidate = unknown
            .solver_candidate
            .as_ref()
            .expect("symbolic OOB unknown should carry a typed solver candidate");
        assert!(solver_candidate.path_guards.is_empty());
        match &solver_candidate.obligation {
            FsymTrustIrSolverObligation::OutOfBounds {
                access_size_bytes,
                width,
                ..
            } => {
                assert_eq!(*access_size_bytes, 8);
                assert_eq!(*width, 64);
            }
            other => panic!("expected OOB solver candidate, got {other:?}"),
        }
    }

    #[test]
    fn reports_concrete_use_after_free() {
        let module = test_module(
            "fsym_uaf",
            vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: None,
                    align: None,
                })
                .with_result(v(0)),
                InstrNode::new(Inst::Dealloc { ptr: v(0) }),
                InstrNode::new(Inst::Load {
                    ty: Ty::I64,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::UseAfterFree
        );
    }

    #[test]
    fn skips_undef_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_undef_skip",
            vec![InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(0))],
        );
    }

    #[test]
    fn skips_call_indirect_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_call_indirect_skip",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::CallIndirect {
                    callee: v(0),
                    sig: FuncTyId::new(0),
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                })
                .with_result(v(1)),
            ],
        );
    }

    #[test]
    fn skips_dialect_op_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_dialect_skip",
            vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    DialectInst::new("verif", "opaque").with_result_ty(Ty::I64),
                )))
                .with_result(v(0)),
            ],
        );
    }

    #[test]
    fn skips_binding_frame_ops_instead_of_silently_scanning() {
        let def = BindingFrameDef::new(
            BindingFrameId::new(0),
            "q",
            vec![BindingSlot::new("i", Ty::I64)],
        );

        assert_skips_unsupported_instruction(
            "fsym_binding_frame_skip",
            vec![
                InstrNode::new(Inst::OpenFrame { def }).with_result(v(0)),
                const_i64(1, 7),
                InstrNode::new(Inst::BindSlot {
                    frame: v(0),
                    slot: 0,
                    value: v(1),
                })
                .with_result(v(2)),
            ],
        );
    }

    #[test]
    fn skips_arc_ops_instead_of_silently_scanning() {
        assert_skips_unsupported_instruction(
            "fsym_arc_skip",
            vec![
                InstrNode::new(Inst::NullPtr).with_result(v(0)),
                InstrNode::new(Inst::IsUnique { ptr: v(0) }).with_result(v(1)),
            ],
        );
    }

    #[test]
    fn follows_condbr_taken_path_with_block_arg() {
        let module = test_module_blocks(
            "fsym_condbr_taken",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(true),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::NullPtr).with_result(v(1)),
                        InstrNode::new(Inst::CondBr {
                            cond: v(0),
                            then_target: BlockId::new(1),
                            then_args: vec![v(1)],
                            else_target: BlockId::new(2),
                            else_args: vec![],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::Ptr)],
                    body: vec![
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(10),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(11)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(11)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(20)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(20)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.diagnostics[0].block, 1);
    }

    #[test]
    fn suppresses_ub_on_infeasible_condbr_arm() {
        let module = test_module_blocks(
            "fsym_condbr_infeasible",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(7),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(7),
                        })
                        .with_result(v(1)),
                        InstrNode::new(Inst::ICmp {
                            op: ICmpOp::Eq,
                            ty: Ty::I64,
                            lhs: v(0),
                            rhs: v(1),
                        })
                        .with_result(v(2)),
                        InstrNode::new(Inst::CondBr {
                            cond: v(2),
                            then_target: BlockId::new(1),
                            then_args: vec![],
                            else_target: BlockId::new(2),
                            else_args: vec![],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(10)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(10)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(20)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(20),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(21)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(21)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn scans_concrete_ub_in_static_bounded_loop() {
        let module = guarded_null_loop_module("fsym_loop_concrete_ub", 4, 2);

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.diagnostics[0].block, 3);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn suppresses_ub_on_infeasible_loop_iteration() {
        let module = guarded_null_loop_module("fsym_loop_infeasible_iteration", 2, 3);

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty());
    }

    /// Fixture: a 2-iteration symbolic loop whose block 2 dereferences an
    /// unconstrained pointer FUNCTION PARAM `v(0): Ptr` with no not-null
    /// annotation on any path. That `Load` is a genuine potential null deref;
    /// each loop iteration is a distinct reachable deref site. Kept as the
    /// regression fixture for the trust-ir `bit_width()`-on-pointers fail-open.
    fn symbolic_loop_ptr_module(ptr_ty: Ty) -> Module {
        test_module_blocks(
            "fsym_loop_symbolic_ptr",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), ptr_ty)],
                    body: vec![const_i64(1, 0), br(1, &[1])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::I64)],
                    body: vec![
                        const_i64(11, 2),
                        icmp_i64(12, ICmpOp::Slt, 10, 11),
                        condbr(12, 2, &[], 4, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(0),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(20)),
                        br(3, &[]),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![
                        const_i64(30, 1),
                        bin_i64(31, BinOp::Add, 10, 30),
                        br(1, &[31]),
                    ],
                },
                Block {
                    id: BlockId::new(4),
                    params: vec![],
                    body: vec![const_i64(40, 0), ret_i64(40)],
                },
            ],
        )
    }

    /// Principled property (replaces the old `assert_eq!(len, 2)` magic
    /// number): the unconstrained-pointer deref MUST be ACCOUNTED FOR as an
    /// unknown null-deref carrying a typed solver candidate — never silently
    /// dropped — and the fail-closed deref-coverage invariant must report no
    /// gap. We do not hinge on the exact obligation count; we assert the
    /// obligations are the right KIND, are tied to the reachable deref site,
    /// and that every reachable deref is covered.
    #[test]
    fn symbolic_loop_ptr_deref_is_accounted_as_unknown_null() {
        let module = symbolic_loop_ptr_module(Ty::Ptr);

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        // The deref is a candidate, not a proven UB or a proven-safe pass.
        assert!(report.diagnostics.is_empty());
        // FAIL-CLOSED invariant: no reachable deref was dropped.
        assert!(
            report.coverage_errors.is_empty(),
            "deref-coverage gap on a fixture that should be fully accounted: {:?}",
            report.coverage_errors
        );

        // The unconstrained-ptr deref IS accounted for as an unknown
        // null-deref with a typed solver candidate. The Load at bb2 is the
        // only deref site, so every unknown obligation must be a NullDeref
        // rooted there.
        assert!(
            !report.unknown_obligations.is_empty(),
            "the unconstrained-pointer deref must be recorded, not dropped"
        );
        assert!(
            report.unknown_obligations.iter().all(|unknown| unknown.kind
                == FsymTrustIrDiagnosticKind::NullDeref
                && unknown.block == 2),
            "every recorded obligation must be the bb2 null-deref: {:?}",
            report.unknown_obligations
        );

        // The deepest-path obligation carries the loop guards and a typed
        // NullDeref solver candidate the caller can escalate.
        let unknown = report
            .unknown_obligations
            .iter()
            .max_by_key(|unknown| unknown.path_guards.len())
            .expect("bounded loop should produce a symbolic null obligation");
        assert!(unknown.path_guards.len() >= 2);
        let solver_candidate = unknown
            .solver_candidate
            .as_ref()
            .expect("loop null unknown should carry a typed solver candidate");
        assert_eq!(
            solver_candidate.path_guards.len(),
            unknown.path_guards.len()
        );
        assert!(matches!(
            solver_candidate.obligation,
            FsymTrustIrSolverObligation::NullDeref { .. }
        ));
    }

    /// Regression case for the original fail-open: the bumped trust-ir made
    /// `Ty::bit_width()` return `None` for pointer types, so a `Ptr` param lost
    /// its facts and its deref produced ZERO obligations (a silent pass). The
    /// scanner must now record one obligation per reachable loop iteration —
    /// and the non-bare pointer variants must NOT be silently dropped either.
    #[test]
    fn symbolic_loop_ptr_deref_records_per_iteration_obligations() {
        for ptr_ty in [
            Ty::Ptr,
            Ty::PtrConst(Box::new(Ty::I64)),
            Ty::PtrMut(Box::new(Ty::I64)),
            Ty::Ref(Box::new(Ty::I64)),
            Ty::RefMut(Box::new(Ty::I64)),
        ] {
            let module = symbolic_loop_ptr_module(ptr_ty.clone());
            let report = scan_module(&module);
            assert!(
                report.coverage_errors.is_empty(),
                "{ptr_ty:?}: unexpected coverage gap"
            );
            // Two reachable iterations of the bb2 Load => two null obligations,
            // proving the regression (0 obligations) is fixed for every
            // pointer-like parameter type.
            assert_eq!(
                report.unknown_obligations.len(),
                2,
                "{ptr_ty:?}: expected one null obligation per loop iteration"
            );
            assert!(report.diagnostics.is_empty(), "{ptr_ty:?}");
        }
    }

    /// The fail-closed deref-coverage invariant must FIRE when a reachable
    /// deref's verdict is artificially dropped. This tests the GUARD itself:
    /// we inject the historical fail-open behaviour (silent early return in
    /// `check_null`) and assert `run_block` raises an `FsymCoverageError`
    /// rather than letting the obligation vanish. Without the invariant this
    /// is exactly the regression that slipped through.
    #[test]
    fn deref_coverage_invariant_fails_closed_on_dropped_verdict() {
        let module = symbolic_loop_ptr_module(Ty::Ptr);
        let function = &module.functions[0];
        // Block 2 holds the reachable Load deref site.
        let block = function
            .blocks
            .iter()
            .find(|block| block.id == BlockId::new(2))
            .expect("fixture has block 2");

        // Sanity: with the verdict recorded normally, the site is covered and
        // no coverage error is raised.
        let mut ok_scan = FunctionScan::new(&module, function, block);
        ok_scan.run_block();
        assert!(
            ok_scan.coverage_errors.is_empty(),
            "a recorded deref must not trip the coverage invariant"
        );

        // Inject the dropped-verdict fault: `check_null` returns without
        // recording, so the reachable Load records NO verdict.
        let mut dropped_scan = FunctionScan::new(&module, function, block);
        dropped_scan.force_drop_deref = true;
        dropped_scan.run_block();

        assert_eq!(
            dropped_scan.coverage_errors.len(),
            1,
            "a dropped reachable deref must raise exactly one coverage error"
        );
        let error = &dropped_scan.coverage_errors[0];
        assert_eq!(error.block, 2);
        assert_eq!(error.inst_index, 0);
        assert_eq!(error.opcode, "Load");
        assert!(error.function.contains("test"));
    }

    #[test]
    fn skips_loop_without_static_trip_count() {
        let module = test_module_blocks(
            "fsym_loop_symbolic_trip_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::I64)],
                    body: vec![const_i64(1, 0), br(1, &[1])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::I64)],
                    body: vec![icmp_i64(11, ICmpOp::Slt, 10, 0), condbr(11, 2, &[], 3, &[])],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        const_i64(20, 1),
                        bin_i64(21, BinOp::Add, 10, 20),
                        br(1, &[21]),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![const_i64(30, 0), ret_i64(30)],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("trip count is not statically bounded")
        );
    }

    #[test]
    fn skips_unsupported_loop_carried_pointer_state() {
        let module = test_module_blocks(
            "fsym_loop_pointer_state_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::NullPtr).with_result(v(0)), br(1, &[0])],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![(v(10), Ty::Ptr)],
                    body: vec![const_bool(11, true), condbr(11, 1, &[10], 2, &[])],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![const_i64(20, 0), ret_i64(20)],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("unsupported state type")
        );
    }

    #[test]
    fn skips_cyclic_cfgs_instead_of_unrolling_loops() {
        let module = test_module_blocks(
            "fsym_loop_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Br {
                        target: BlockId::new(1),
                        args: vec![],
                    })],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Br {
                        target: BlockId::new(1),
                        args: vec![],
                    })],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("conditional static-bound check")
        );
    }

    #[test]
    fn skips_switch_cycles_instead_of_unrolling() {
        let module = test_module_blocks(
            "fsym_switch_cycle_skip",
            vec![Block {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(v(0)),
                    InstrNode::new(Inst::Switch {
                        value: v(0),
                        default: BlockId::new(0),
                        default_args: vec![],
                        cases: vec![SwitchCase {
                            value: Constant::Int(1),
                            target: BlockId::new(0),
                            args: vec![],
                        }],
                        exhaustive_enum_unreachable: false,
                    }),
                ],
            }],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Loop
        );
    }

    #[test]
    fn scans_concrete_switch_to_selected_ub_arm() {
        let module = test_module_blocks(
            "fsym_switch_concrete_ub",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(1),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(3),
                            default_args: vec![],
                            cases: vec![
                                SwitchCase {
                                    value: Constant::Int(0),
                                    target: BlockId::new(1),
                                    args: vec![],
                                },
                                SwitchCase {
                                    value: Constant::Int(1),
                                    target: BlockId::new(2),
                                    args: vec![],
                                },
                            ],
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(10)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(10)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(20)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(20),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(21)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(21)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(3),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(9),
                        })
                        .with_result(v(30)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(30)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.diagnostics[0].block, 2);
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn suppresses_ub_on_infeasible_switch_arm() {
        let module = test_module_blocks(
            "fsym_switch_infeasible",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(2),
                            default_args: vec![],
                            cases: vec![SwitchCase {
                                value: Constant::Int(1),
                                target: BlockId::new(1),
                                args: vec![],
                            }],
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(10)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(10),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(11)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(11)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(7),
                        })
                        .with_result(v(20)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(20)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert!(report.unknown_obligations.is_empty());
    }

    #[test]
    fn records_symbolic_switch_unknown_solver_candidate() {
        let module = test_module_blocks(
            "fsym_switch_symbolic",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![(v(0), Ty::I8)],
                    body: vec![InstrNode::new(Inst::Switch {
                        value: v(0),
                        default: BlockId::new(2),
                        default_args: vec![],
                        cases: vec![SwitchCase {
                            value: Constant::Int(1),
                            target: BlockId::new(1),
                            args: vec![],
                        }],
                        exhaustive_enum_unreachable: false,
                    })],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::NullPtr).with_result(v(10)),
                        InstrNode::new(Inst::Load {
                            ty: Ty::I64,
                            ptr: v(10),
                            volatile: false,
                            align: None,
                        })
                        .with_result(v(11)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(11)],
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(20)),
                        InstrNode::new(Inst::Return {
                            values: vec![v(20)],
                        }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 1);
        assert!(report.skipped_functions.is_empty());
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unknown_obligations.len(), 1);
        assert_eq!(
            report.unknown_obligations[0].kind,
            FsymTrustIrDiagnosticKind::NullDeref
        );
        assert_eq!(report.unknown_obligations[0].path_guards.len(), 1);
        let solver_candidate = report.unknown_obligations[0]
            .solver_candidate
            .as_ref()
            .expect("switch null unknown should carry a typed solver candidate");
        assert_eq!(solver_candidate.path_guards.len(), 1);
        assert!(matches!(
            solver_candidate.obligation,
            FsymTrustIrSolverObligation::NullDeref { .. }
        ));
    }

    #[test]
    fn skips_large_switches() {
        let cases = (0..=FSYM_TRUST_IR_MAX_SWITCH_CASES)
            .map(|index| SwitchCase {
                value: Constant::Int(index as i128),
                target: BlockId::new(1),
                args: vec![],
            })
            .collect();
        let module = test_module_blocks(
            "fsym_large_switch_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(1),
                            default_args: vec![],
                            cases,
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(1)),
                        InstrNode::new(Inst::Return { values: vec![v(1)] }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Switch
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("over fsym bound")
        );
    }

    #[test]
    fn reports_typed_unsupported_switch_skip() {
        let module = test_module_blocks(
            "fsym_switch_unsupported_skip",
            vec![
                Block {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(true),
                        })
                        .with_result(v(0)),
                        InstrNode::new(Inst::Switch {
                            value: v(0),
                            default: BlockId::new(1),
                            default_args: vec![],
                            cases: vec![SwitchCase {
                                value: Constant::Bool(true),
                                target: BlockId::new(1),
                                args: vec![],
                            }],
                            exhaustive_enum_unreachable: false,
                        }),
                    ],
                },
                Block {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::Const {
                            ty: Ty::I64,
                            value: Constant::Int(0),
                        })
                        .with_result(v(1)),
                        InstrNode::new(Inst::Return { values: vec![v(1)] }),
                    ],
                },
            ],
        );

        let report = scan_module(&module);
        assert_eq!(report.scanned_functions, 0);
        assert_eq!(report.skipped_functions.len(), 1);
        assert_eq!(
            report.skipped_functions[0].reason,
            FsymTrustIrSkipReason::Switch
        );
        assert!(
            report.skipped_functions[0]
                .detail
                .contains("outside bounded fsym support")
        );
    }
}
