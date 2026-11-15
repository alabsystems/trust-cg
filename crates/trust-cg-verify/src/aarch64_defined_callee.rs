// Copyright 2026 Andrew Yates | Apache-2.0

//! A compact prerequisite for composing an actual defined scalar callee.
//!
//! Existing independent TrustIR/LIR/final-word affine checking establishes the
//! return/effect relation. An immutable captured Formal report must also match
//! the exact machine/LIR/module inputs and the original request capture. This
//! type does not create a proof, grant source/Core licensing, credit a caller's
//! BL/frame, discharge entry-stack storage, or authorize installation. In
//! particular it is not a `SourceBoundReplay` capability. Ordinary module,
//! source-certificate and license validation remain their existing owners'.
//!
//! The owned summary drops the machine graph and code borrow after minting. A
//! later attachment checks the same module/FuncId/body/LIR/code/request and
//! reapplies the existing final-byte owner. No byte clone, solver invocation,
//! policy capture, budget reset, serialization or public receipt constructor
//! is provided. Argument instantiation shares the caller's expression DAGs;
//! its aggregate shape/type inspection uses the existing raw-print limits and
//! allocates traversal state. The caller must still admit the combined theorem
//! under its existing aggregate limits.

use std::fmt::Write;
use std::sync::Arc;

use sha2::{Digest, Sha256};
use trust_cg_ir::MachFunction;
use trust_cg_lower::Function;
use trust_ir::proof::{ProofDigest, ProofEvidence, SourceDefinitionRef};
use trust_ir::{BodyGate, FuncId};

use super::super::{Affine, CompareKind, Predicate, ScalarType, ScalarValue};
use super::final_bytes::{
    AffineByteError, CheckedAarch64TrustIrAffineBytes, check_aarch64_trust_ir_affine_bytes,
};
use crate::FunctionSourceModules;
use crate::function_request::{CapturedFunctionVerificationReport, FunctionVerificationRequest};
use crate::function_verifier::InstructionVerificationResult;
use crate::provenance_xcheck::ProvenanceXCheckMode;
use crate::smt::{SmtExpr as E, SmtSort};
use crate::verify::VerificationStrength;

/// Scalar source result, with the existing homogeneous 32/64-bit parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefinedCalleeScalarType {
    BitVec(u32),
    Bool,
}

/// Conservative effects established by the existing complete byte checker.
/// The private window, when nonempty, is a REQUIREMENT on a real entry owner:
/// live, private, writable storage below aligned, nonwrapping entry SP. This
/// value grants none of those permissions. NZCV and X0-X17 may be clobbered;
/// SP, LR, X18-X29 and SIMD/FP registers are preserved on normal return, and
/// memory outside this window is unchanged. The callee returns via entry LR.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DefinedCalleeEffects {
    private_stack_bytes: usize,
}

impl DefinedCalleeEffects {
    pub fn required_private_stack_bytes(self) -> usize {
        self.private_stack_bytes
    }
    pub fn required_entry_sp_alignment(self) -> usize {
        16
    }
}

/// A refusal never grants a weaker relation or proof class.
#[derive(Debug, thiserror::Error)]
pub enum DefinedAffineCalleeError {
    #[error("defined callee requires the unchanged original/lowered module endpoints")]
    ModuleEndpoints,
    #[error("defined callee FuncId/name/body is missing or ambiguous")]
    FunctionIdentity,
    #[error(
        "defined callee requires the existing body gate's exact source-bearing certificate binding"
    )]
    MissingSourceBinding,
    #[error("defined callee report is not from the original enforced request capture")]
    RequestCapture,
    #[error("defined callee report does not match its exact machine/LIR/modules")]
    ReportInput,
    #[error(
        "defined callee requires a complete nondegenerate Formal report; structural/exhaustive/sampled metadata is insufficient"
    )]
    FormalReport,
    #[error("defined callee machine signature differs from its checked scalar ABI")]
    MachineAbi,
    #[error("defined callee machine/word stream is not exactly bound: {0}")]
    MachineWords(&'static str),
    #[error("defined callee final-byte relation refused: {0}")]
    Bytes(#[from] AffineByteError),
    #[error(
        "defined callee attachment differs from its sealed module/body/LIR/code/request endpoints"
    )]
    Attachment,
    #[error("defined callee argument arity/sort or finite relation is invalid")]
    Arguments,
    #[error("defined callee argument inspection refused: {0}")]
    ArgumentInspection(String),
}

type Result<T> = std::result::Result<T, DefinedAffineCalleeError>;

/// Move-only semantic prerequisite. It retains finite scalar forms and shared
/// captured evidence, never all allocated machine graphs or a second code copy.
#[derive(Debug)]
pub struct DefinedAffineCallee {
    function: FuncId,
    module_digest: [u8; 32],
    body_digest: ProofDigest,
    lir_digest: [u8; 32],
    machine_input_digest: [u8; 32],
    code_digest: [u8; 32],
    code_len: usize,
    source_definition: SourceDefinitionRef,
    captured: CapturedFunctionVerificationReport,
    parameter_bits: [u32; 8],
    arity: usize,
    bits: u32,
    result: Option<ScalarValue>,
    effects: DefinedCalleeEffects,
}

/// Reattached actual immutable endpoints. This owner remains only a callee
/// prerequisite; it cannot credit a caller or bypass source/install checks.
pub struct AttachedDefinedAffineCallee<'a> {
    summary: &'a DefinedAffineCallee,
    bytes: CheckedAarch64TrustIrAffineBytes<'a>,
}

impl std::fmt::Debug for AttachedDefinedAffineCallee<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AttachedDefinedAffineCallee")
            .field("function", &self.summary.function)
            .field("effects", &self.summary.effects)
            .finish_non_exhaustive()
    }
}

struct HashWriter(Sha256);
impl Write for HashWriter {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        self.0.update(text.as_bytes());
        Ok(())
    }
}
fn lir_digest(lir: &Function) -> [u8; 32] {
    let mut writer = HashWriter(Sha256::new());
    writer.0.update(b"trust-cg.defined-affine-callee.lir.v1\0");
    lir.write_canonical_verifier_identity(&mut writer)
        .expect("infallible SHA writer");
    writer.0.finalize().into()
}

fn function_ordinal(
    modules: &FunctionSourceModules<'_>,
    id: FuncId,
    lir: &Function,
) -> Result<usize> {
    if !std::ptr::eq(modules.original(), modules.lowered()) {
        return Err(DefinedAffineCalleeError::ModuleEndpoints);
    }
    let mut selected = modules
        .original()
        .functions
        .iter()
        .enumerate()
        .filter(|(_, f)| f.id == id);
    let (ordinal, function) = selected
        .next()
        .ok_or(DefinedAffineCalleeError::FunctionIdentity)?;
    if selected.next().is_some()
        || function.name != lir.name
        || function.blocks.is_empty()
        || modules
            .original()
            .functions
            .iter()
            .filter(|f| f.name == function.name)
            .count()
            != 1
    {
        return Err(DefinedAffineCalleeError::FunctionIdentity);
    }
    Ok(ordinal)
}

// This checks presence/exact selection of the source-bearing prerequisite. It
// deliberately does not reimplement the IR/Clean source-certificate validator.
fn source_definition(module: &trust_ir::Module, ordinal: usize) -> Result<&SourceDefinitionRef> {
    let function = &module.functions[ordinal];
    let Some(BodyGate::Gated {
        evidence: Some(gate),
        ..
    }) = &function.body_gate
    else {
        return Err(DefinedAffineCalleeError::MissingSourceBinding);
    };
    if module.function_body_digest(function.id) != Ok(gate.body_digest) {
        return Err(DefinedAffineCalleeError::MissingSourceBinding);
    }
    let mut obligations = module
        .proof_obligations
        .iter()
        .filter(|o| o.id == gate.obligation);
    if obligations
        .next()
        .is_none_or(|o| o.function != Some(function.id))
        || obligations.next().is_some()
    {
        return Err(DefinedAffineCalleeError::MissingSourceBinding);
    }
    let mut certificates = module
        .proof_certificates
        .iter()
        .filter(|c| c.obligation == gate.obligation);
    let certificate = certificates
        .next()
        .ok_or(DefinedAffineCalleeError::MissingSourceBinding)?;
    if certificates.next().is_some() {
        return Err(DefinedAffineCalleeError::MissingSourceBinding);
    }
    match &certificate.evidence {
        ProofEvidence::CleanCic {
            kernel_recheck: Some(recheck),
            ..
        } => recheck
            .binding
            .as_ref()
            .filter(|b| b.environment.is_some())
            .and_then(|b| b.source.as_ref())
            .ok_or(DefinedAffineCalleeError::MissingSourceBinding),
        _ => Err(DefinedAffineCalleeError::MissingSourceBinding),
    }
}

pub(super) fn scalar_abi(module: &trust_ir::Module, ordinal: usize, lir: &Function) -> Result<()> {
    let function = &module.functions[ordinal];
    let signature = module
        .func_types
        .get(function.ty.index() as usize)
        .ok_or(DefinedAffineCalleeError::MachineAbi)?;
    let target = module
        .target_info
        .as_ref()
        .ok_or(DefinedAffineCalleeError::MachineAbi)?;
    let abi = match target.triple.as_str() {
        "aarch64-apple-darwin" => "darwinpcs",
        "aarch64-unknown-linux-gnu" => "aapcs64",
        _ => return Err(DefinedAffineCalleeError::MachineAbi),
    };
    // LIR has no separate convention field. It retains scalar placement and
    // hidden-result sidecars; the ordinary, unrecorded C ABI is the qualified
    // domain here. A recorded frontend FnAbi needs its own placement owner.
    if function.calling_conv != trust_ir::CallingConv::C
        || signature.abi.is_some()
        || target.pointer_size != 8
        || target.endianness != trust_ir::Endianness::Little
        || target.abi.as_deref().is_some_and(|tag| tag != abi)
        || lir.abi_sret_param.is_some()
        || !lir.param_pointee_types.is_empty()
        || !lir.sret_arg_callees.is_empty()
        || !lir.sret_arg_indirect_callees.is_empty()
        || !lir.eh_info.is_empty()
        || !lir.eh_type_table.is_empty()
        || lir.stack_limit.is_some()
    {
        return Err(DefinedAffineCalleeError::MachineAbi);
    }
    Ok(())
}

fn bind_machine_words(machine: &MachFunction, code: &[u8]) -> Result<()> {
    let mut at = 0usize;
    for block in &machine.block_order {
        let block = machine
            .blocks
            .get(block.0 as usize)
            .ok_or(DefinedAffineCalleeError::MachineWords("foreign block"))?;
        for id in &block.insts {
            let inst =
                machine
                    .insts
                    .get(id.0 as usize)
                    .ok_or(DefinedAffineCalleeError::MachineWords(
                        "foreign instruction",
                    ))?;
            if inst.is_pseudo() {
                continue;
            }
            let bytes = code
                .get(at..at + 4)
                .ok_or(DefinedAffineCalleeError::MachineWords("missing word"))?;
            let word = u32::from_le_bytes(bytes.try_into().unwrap());
            let value_word = matches!(
                crate::aarch64_instruction_word_proofs::check_emitted_instruction_word(inst, word),
                Some(Ok(()))
            );
            let pair_word = crate::aarch64_pair_memory::check_pair_encoding(inst, bytes).is_ok();
            // Complete machine/source binding below has already checked the
            // canonical unchanged-LR RET operands. Reuse the control decoder
            // for its actual word; RET has no local arithmetic proof row.
            let return_word = inst.opcode == trust_cg_ir::AArch64Opcode::Ret
                && matches!(
                    crate::aarch64_control_decode::decode_a64_control_word(word),
                    Some(crate::aarch64_control_decode::A64ControlWord::Return { register: 30 })
                );
            if !(value_word || pair_word || return_word) {
                return Err(DefinedAffineCalleeError::MachineWords(
                    "word/operand disagreement or unsupported word",
                ));
            }
            at += 4;
        }
    }
    if at != code.len() {
        return Err(DefinedAffineCalleeError::MachineWords(
            "unowned trailing bytes",
        ));
    }
    Ok(())
}

impl DefinedAffineCallee {
    /// Check actual inputs, then retain only finite semantic facts and complete
    /// identities. This consumes no new request, solver run or proof budget.
    pub fn bind(
        modules: &FunctionSourceModules<'_>,
        request: &FunctionVerificationRequest,
        captured: &CapturedFunctionVerificationReport,
        function: FuncId,
        lir: &Function,
        machine: &MachFunction,
        code: &[u8],
    ) -> Result<Self> {
        let ordinal = function_ordinal(modules, function, lir)?;
        let definition = source_definition(modules.original(), ordinal)?;
        scalar_abi(modules.original(), ordinal, lir)?;
        if request.mode() != ProvenanceXCheckMode::Enforce
            || !captured.matches_request_capture(request)
        {
            return Err(DefinedAffineCalleeError::RequestCapture);
        }
        if !captured.matches_aarch64_input_with_modules(machine, Some(lir), modules) {
            return Err(DefinedAffineCalleeError::ReportInput);
        }
        let report = captured.report();
        if report.precondition_failure.is_some()
            || report.genuinely_verified_count() == 0
            || !report.emitted_opcode_inventory().is_promotable()
            || report.instructions.iter().any(|r| {
                matches!(r.result,
                InstructionVerificationResult::Verified { strength, degenerate, .. }
                    if strength != VerificationStrength::Formal || degenerate)
            })
        {
            return Err(DefinedAffineCalleeError::FormalReport);
        }
        let bytes = check_aarch64_trust_ir_affine_bytes(modules.original(), ordinal, lir, code)?;
        // Reuse the existing complete allocated source/return binders, including
        // their canonical RET and frame checks. These are admission witnesses,
        // not another discharge or a promotion of their Rust implementations.
        if crate::source_bound_frame::source_bound_frame(lir, machine).is_err()
            && crate::source_bound_a64_control::CheckedFramelessLinear::bind(lir, machine).is_err()
            && crate::source_bound_a64_body::source_bound_a64_body(lir, machine).is_err()
        {
            return Err(DefinedAffineCalleeError::MachineWords(
                "complete allocated source/return binding refused",
            ));
        }
        let source = super::trust_ir_contract(modules.original(), bytes.source())
            .map_err(AffineByteError::from)?;
        let mut parameter_bits = [0u32; 8];
        for (out, ty) in parameter_bits.iter_mut().zip(&source.signature.params) {
            *out = match ty {
                trust_ir::Ty::I32 | trust_ir::Ty::U32 => 32,
                trust_ir::Ty::I64 | trust_ir::Ty::U64 => 64,
                _ => return Err(DefinedAffineCalleeError::MachineAbi),
            };
        }
        let mt = |bits| {
            if bits == 32 {
                trust_cg_ir::function::Type::I32
            } else {
                trust_cg_ir::function::Type::I64
            }
        };
        let expected_return = source.return_type.map(|t| match t {
            ScalarType::Integer(bits) => mt(bits),
            ScalarType::Bool => trust_cg_ir::function::Type::B1,
        });
        if machine.name != lir.name
            || machine.signature.params.len() != source.signature.params.len()
            || machine
                .signature
                .params
                .iter()
                .zip(parameter_bits)
                .any(|(ty, bits)| *ty != mt(bits))
            || machine.signature.returns.len() != source.signature.returns.len()
            || machine.signature.returns.first() != expected_return.as_ref()
        {
            return Err(DefinedAffineCalleeError::MachineAbi);
        }
        bind_machine_words(machine, code)?;
        Ok(Self {
            function,
            module_digest: *modules.digest(),
            body_digest: modules
                .original()
                .function_body_digest(function)
                .map_err(|_| DefinedAffineCalleeError::FunctionIdentity)?,
            lir_digest: lir_digest(lir),
            machine_input_digest: *captured
                .aarch64_input_digest()
                .ok_or(DefinedAffineCalleeError::ReportInput)?,
            code_digest: Sha256::digest(code).into(),
            code_len: code.len(),
            source_definition: definition.clone(),
            captured: captured.clone(),
            parameter_bits,
            arity: source.signature.params.len(),
            bits: source.bits,
            result: bytes.scalar_result(),
            effects: DefinedCalleeEffects {
                private_stack_bytes: bytes.statistics().private_stack_bytes,
            },
        })
    }

    /// Reattach to actual immutable endpoints after streaming discarded the
    /// callee's machine graph. Hashes are custody; the byte checker is replayed.
    pub fn attach<'a>(
        &'a self,
        modules: &FunctionSourceModules<'a>,
        request: &FunctionVerificationRequest,
        function: FuncId,
        lir: &'a Function,
        code: &'a [u8],
    ) -> Result<AttachedDefinedAffineCallee<'a>> {
        let ordinal = function_ordinal(modules, function, lir)?;
        scalar_abi(modules.original(), ordinal, lir)?;
        if function != self.function
            || modules.digest() != &self.module_digest
            || !self.captured.matches_request_capture(request)
            || request.mode() != ProvenanceXCheckMode::Enforce
            || modules.original().function_body_digest(function) != Ok(self.body_digest)
            || lir_digest(lir) != self.lir_digest
            || code.len() != self.code_len
            || <[u8; 32]>::from(Sha256::digest(code)) != self.code_digest
            || source_definition(modules.original(), ordinal)? != &self.source_definition
        {
            return Err(DefinedAffineCalleeError::Attachment);
        }
        let bytes = check_aarch64_trust_ir_affine_bytes(modules.original(), ordinal, lir, code)?;
        if bytes.scalar_result() != self.result
            || bytes.statistics().private_stack_bytes != self.effects.private_stack_bytes
        {
            return Err(DefinedAffineCalleeError::Attachment);
        }
        Ok(AttachedDefinedAffineCallee {
            summary: self,
            bytes,
        })
    }

    pub fn function(&self) -> FuncId {
        self.function
    }
    pub fn source_definition(&self) -> &SourceDefinitionRef {
        &self.source_definition
    }
    pub fn effects(&self) -> DefinedCalleeEffects {
        self.effects
    }
    pub fn parameter_bits(&self) -> &[u32] {
        &self.parameter_bits[..self.arity]
    }
    pub fn machine_input_digest(&self) -> &[u8; 32] {
        &self.machine_input_digest
    }
    pub fn code_digest(&self) -> &[u8; 32] {
        &self.code_digest
    }
    pub fn result_type(&self) -> Option<DefinedCalleeScalarType> {
        self.result.map(|r| match r.ty() {
            ScalarType::Integer(bits) => DefinedCalleeScalarType::BitVec(bits),
            ScalarType::Bool => DefinedCalleeScalarType::Bool,
        })
    }
    /// Conservative retained-payload accounting, including shared proof data.
    pub fn estimated_payload_bytes(&self) -> usize {
        std::mem::size_of::<Self>()
            .saturating_add(self.source_definition.decl.len())
            .saturating_add(self.captured.estimated_payload_bytes())
    }
}

impl<'a> AttachedDefinedAffineCallee<'a> {
    /// A new request with identical settings is not the original capture.
    pub(crate) fn matches_request_capture(&self, request: &FunctionVerificationRequest) -> bool {
        self.summary.captured.matches_request_capture(request)
    }
    pub fn summary(&self) -> &DefinedAffineCallee {
        self.summary
    }
    pub fn checked_bytes(&self) -> &CheckedAarch64TrustIrAffineBytes<'a> {
        &self.bytes
    }

    // Future checked call-aware interpreters in this affine owner may compose
    // the same finite relation only after attachment, without another evaluator.
    pub(super) fn substitute_scalar(
        &self,
        arguments: &[ScalarValue],
    ) -> Result<Option<ScalarValue>> {
        let summary = self.summary;
        if arguments.len() != summary.arity
            || arguments
                .iter()
                .zip(summary.parameter_bits())
                .any(|(v, bits)| v.ty() != ScalarType::Integer(*bits))
        {
            return Err(DefinedAffineCalleeError::Arguments);
        }
        summary
            .result
            .map(|r| {
                r.substitute(arguments, summary.bits)
                    .ok_or(DefinedAffineCalleeError::Arguments)
            })
            .transpose()
    }

    /// Share actual same-width argument DAGs and instantiate the exact finite
    /// relation. All argument roots share ONE existing preflight node/edge/
    /// payload/depth budget; no result is built until every sort is checked.
    /// This is expression construction, not proof or permission. The combined
    /// caller theorem still needs its normal aggregate admission and replay.
    pub fn instantiate_result(&self, arguments: &[Arc<E>]) -> Result<Option<Arc<E>>> {
        if arguments.len() != self.summary.arity {
            return Err(DefinedAffineCalleeError::Arguments);
        }
        // Recheck closure over the exact declared finite parameter scope. This
        // rejects foreign coefficients or widths before sharing any supplied
        // term; it is the same checked substitution a call-aware interpreter
        // can later use for actual affine argument values.
        let mut parameters = [ScalarValue::Integer {
            bits: self.summary.bits,
            value: Affine::constant(0, u64::MAX),
        }; 8];
        for (index, (parameter, bits)) in parameters
            .iter_mut()
            .zip(self.summary.parameter_bits())
            .enumerate()
        {
            *parameter = ScalarValue::Integer {
                bits: *bits,
                value: Affine::parameter(index),
            };
        }
        let relation = self.substitute_scalar(&parameters[..self.summary.arity])?;
        let roots: Vec<_> = arguments.iter().map(Arc::as_ref).collect();
        let scanned = crate::smt_raw_print::preflight_roots(&roots)
            .map_err(|e| DefinedAffineCalleeError::ArgumentInspection(e.to_string()))?;
        // At most 103 nodes/144 child edges for the largest supported flat
        // selection of affine forms, plus the private type-view tuple root.
        if scanned.order.len().saturating_add(104) > crate::smt_raw_print::MAX_NODES
            || scanned.edges.saturating_add(152) > crate::smt_raw_print::MAX_EDGES
        {
            return Err(DefinedAffineCalleeError::ArgumentInspection(
                "combined relation shape limit".into(),
            ));
        }
        // The preflight bounds shallow root/string copies before this view is
        // made. Children are Arc-shared. Empty UF names were refused in the
        // actual roots, so only this private tuple has an empty name. Typed
        // aliases are inspection-only, never terms in the returned relation.
        let tuple = E::UF {
            name: String::new(),
            args: arguments.iter().map(|a| a.as_ref().clone()).collect(),
            ret_sort: SmtSort::Bool,
        };
        let typed = tuple
            .try_rewrite_dag(&mut |view| {
                let sort = crate::smt_raw_print::checked_sort(view)?;
                if matches!(view, E::UF { name, .. } if name.is_empty()) {
                    Ok(Some(view.clone()))
                } else {
                    Ok(Some(E::UF {
                        name: "callee-sort-view".into(),
                        args: Vec::new(),
                        ret_sort: sort,
                    }))
                }
            })
            .map_err(|e: crate::smt_raw_print::CompactPrintRefusal| {
                DefinedAffineCalleeError::ArgumentInspection(e.to_string())
            })?;
        let Some(E::UF { args, .. }) = typed else {
            return Err(DefinedAffineCalleeError::Arguments);
        };
        if args
            .iter()
            .zip(self.summary.parameter_bits())
            .any(|(a, bits)| a.sort() != SmtSort::BitVec(*bits))
        {
            return Err(DefinedAffineCalleeError::Arguments);
        }
        Ok(relation.map(|r| scalar_expression(r, arguments)))
    }
}

fn affine_expression(value: Affine, bits: u32, arguments: &[Arc<E>]) -> Arc<E> {
    let mut result = Arc::new(E::bv_const(value.0[8], bits));
    for (coefficient, argument) in value.0.iter().zip(arguments) {
        if *coefficient == 0 {
            continue;
        }
        let term = if *coefficient == 1 {
            argument.clone()
        } else {
            Arc::new(E::BvMul {
                lhs: argument.clone(),
                rhs: Arc::new(E::bv_const(*coefficient, bits)),
                width: bits,
            })
        };
        result = Arc::new(E::BvAdd {
            lhs: result,
            rhs: term,
            width: bits,
        });
    }
    result
}
fn predicate_expression(value: Predicate, arguments: &[Arc<E>]) -> Arc<E> {
    match value {
        Predicate::Constant(value) => Arc::new(E::bool_const(value)),
        Predicate::Compare {
            bits,
            kind,
            lhs,
            rhs,
            negated,
        } => {
            let lhs = affine_expression(lhs, bits, arguments);
            let rhs = affine_expression(rhs, bits, arguments);
            let result = Arc::new(match kind {
                CompareKind::Equal => E::Eq { lhs, rhs },
                CompareKind::SignedLess => E::BvSlt {
                    lhs,
                    rhs,
                    width: bits,
                },
                CompareKind::UnsignedLess => E::BvUlt {
                    lhs,
                    rhs,
                    width: bits,
                },
            });
            if negated {
                Arc::new(E::Not { operand: result })
            } else {
                result
            }
        }
    }
}
pub(super) fn scalar_expression(value: ScalarValue, arguments: &[Arc<E>]) -> Arc<E> {
    match value {
        ScalarValue::Integer { bits, value } => affine_expression(value, bits, arguments),
        ScalarValue::Bool(predicate) => predicate_expression(predicate, arguments),
        ScalarValue::Select {
            bits,
            predicate,
            then_value,
            else_value,
        } => Arc::new(E::Ite {
            cond: predicate_expression(predicate, arguments),
            then_expr: affine_expression(then_value, bits, arguments),
            else_expr: affine_expression(else_value, bits, arguments),
        }),
    }
}

#[cfg(test)]
#[path = "aarch64_defined_callee_tests.rs"]
mod tests;
