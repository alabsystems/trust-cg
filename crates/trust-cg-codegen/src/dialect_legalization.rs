// trust-cg-codegen/dialect_legalization.rs - registry-driven dialect legalization
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Ledger L05-P11. trust-ir is this backend's interface; its dialect model
// (`Inst::DialectOp`, `Ty::Dialect`, `trust_ir::dialect::{Dialect,
// LoweringPass, lower_module}`, the data-only `dialect::schema` registry) is
// read first and reused here rather than re-modelled.

//! Registry-driven legalization of trust-ir dialect operations and nominal
//! dialect types, with receipts.
//!
//! trust-ir carries operations (`Inst::DialectOp`) and nominal types
//! (`Ty::Dialect`) whose semantics the core format does not define: "a Core
//! consumer must require explicit legalization first" (`trust_ir::DialectTy`).
//! This module is that explicit legalization, as a contract:
//!
//! * A [`DialectRegistration`] names one namespace and schema version, WHO
//!   defines its semantics ([`DialectRegistration::owner`]), the grammar its
//!   payloads must satisfy ([`DialectGrammar`]: trust-ir's exact
//!   `OperationSchema`s, checked against the module's actual SSA types by
//!   trust-ir-build, or a dialect-owned `trust_ir::dialect::Dialect`
//!   validator for polymorphic ops), one [`OpRule`] per op it declares and one
//!   [`TypeRule`] per nominal type it declares. [`DialectLegalizationRegistry::new`]
//!   refuses a malformed registration by name ([`RegistrationError`]).
//! * [`legalize_module`] resolves every dialect occurrence by EXACT name
//!   (namespace, op, type name and version), checks the grammar, selects the
//!   rule, applies it, and returns one [`LegalizationReceipt`] per op site and
//!   per legalized type in a [`DialectLegalizationReport`]. An unknown
//!   namespace, op or type is refused by name; nothing is skipped.
//! * Op rules lower to core trust-ir ([`OpLowering::Rewrite`], driven through
//!   trust-ir's own `lower_module`, which refuses to rewrite a node carrying an
//!   unmapped semantic marker or call contract and invalidates the function's
//!   source provenance), keep the op for the adapter's own typed lowering
//!   ([`OpLowering::AdapterNative`]), call a named runtime entry
//!   ([`OpLowering::RuntimeCall`], the op's full payload passed as a read-only
//!   descriptor, [`encode_payload_descriptor`]), or refuse
//!   ([`OpLowering::Unbound`]). Type rules substitute a core scalar carrier
//!   for the nominal type everywhere it occurs; trust-ir's nominal rule (no
//!   `InvalidDialectType` finding: only exact-typed transport and dialect ops
//!   touch a nominal value) is the checked precondition.
//! * A legalized module is re-validated by trust-ir-build's `validate_module`
//!   (a finding the source module did not have refuses it) and then enters the
//!   same adapter, instruction-proof and object pipeline as core trust-ir.
//!   When proof is required, only rules whose evidence is checked in this
//!   compile are admitted ([`LegalizationEvidence::admitted_when_proof_required`]);
//!   any other rule is refused by name before anything is rewritten.
//! * [`verify_legalization`] replays a legalization and checks a report and
//!   legalized module exactly; any edited, dropped, added or reordered receipt
//!   field is named.
//!
//! The adapter's own refusals (`Ty::Dialect` "requires semantic legalization",
//! an unhandled `DialectOp`) stay in place as the backstop for any path that
//! does not run this legalization.
//!
//! # Evidence strength
//!
//! A receipt records which rule was applied and the evidence class that rule
//! rests on; it is not itself a proof. See [`LegalizationEvidence`] for what
//! each class does and does not establish.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::fmt;
use std::sync::{Arc, Mutex, OnceLock};

use sha2::{Digest, Sha256};
use thiserror::Error;
use trust_cg_ir::target_machine::Target;
use trust_ir::dialect::lowering::LoweringContext;
use trust_ir::dialect::schema::{
    AttributeKind, AttributeSchema, DialectSchema as IrDialectSchema, DialectSchemaRegistry,
    OperandType, OperationSchema,
};
use trust_ir::dialect::{AttrValue, Dialect, DialectInst, LoweringPass, RewriteOutcome};
use trust_ir::value::GlobalId;
use trust_ir::{
    BlockId, Constant, DialectTy, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage,
    Module, Ty, ValueId, Visibility,
};

/// Maximum fixpoint iterations of trust-ir's `lower_module` per function. Every
/// rule here lowers in one step; the bound only cuts off a misbehaving rule.
pub const MAX_LOWERING_ITERS: usize = 16;

/// Magic prefix of a runtime-call payload descriptor ([`encode_payload_descriptor`]).
pub const PAYLOAD_DESCRIPTOR_MAGIC: &[u8; 4] = b"TCGD";
/// Format version of a runtime-call payload descriptor.
pub const PAYLOAD_DESCRIPTOR_VERSION: u32 = 1;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// A dialect occurrence this backend refuses, or a legalization failure.
///
/// Every variant names the exact dialect, op or type it concerns.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum DialectPipelineError {
    /// trust-ir's lowering driver reported a failure (a rule's error, a node
    /// carrying an unmapped semantic marker, value-id exhaustion, or no
    /// fixpoint).
    #[error("trust_ir dialect lowering failed: {0}")]
    Lowering(String),
    /// A `DialectOp` or `Ty::Dialect` names a namespace no registration claims.
    #[error(
        "[TCG-DIALECT-UNREGISTERED] dialect `{namespace}` (used by {usage}) has no legalization \
         registered in this backend; it is refused by name"
    )]
    UnregisteredDialect { namespace: String, usage: String },
    /// A registered dialect does not declare this op.
    #[error(
        "[TCG-DIALECT-UNREGISTERED] op `{dialect}.{op}` (in function `{function}`) is not declared \
         by the `{dialect}` v{version} registration; it is refused by name"
    )]
    UnregisteredOp {
        dialect: String,
        version: u32,
        op: String,
        function: String,
    },
    /// A registered dialect does not declare this nominal type.
    #[error(
        "[TCG-DIALECT-UNREGISTERED] dialect type `{namespace}.{name}@{type_version}` is not \
         declared by the `{namespace}` v{version} registration; it is refused by name"
    )]
    UnregisteredType {
        namespace: String,
        name: String,
        type_version: u32,
        version: u32,
    },
    /// A nominal identity that is lexically malformed (trust-ir `DialectTy::validate`).
    #[error(
        "[TCG-DIALECT-GRAMMAR] dialect type `{namespace}.{name}@{version}` is malformed: {detail}"
    )]
    MalformedType {
        namespace: String,
        name: String,
        version: u32,
        detail: String,
    },
    /// The payload violates the registered grammar of its op.
    #[error(
        "[TCG-DIALECT-GRAMMAR] `{dialect}.{op}` (in function `{function}`) violates the `{dialect}` \
         v{version} registration's grammar: {detail}"
    )]
    Grammar {
        dialect: String,
        version: u32,
        op: String,
        function: String,
        detail: String,
    },
    /// trust-ir's nominal rule refuses a use of a dialect-typed value: only
    /// exact-typed transport and dialect operations may touch one before
    /// legalization, so a type substitution would be unsound.
    #[error(
        "[TCG-DIALECT-NOMINAL] a nominal dialect value is used outside exact-typed transport \
         ({detail}); its type cannot be legalized by carrier substitution"
    )]
    NominalUse { detail: String },
    /// The op is registered but this registry binds no lowering for it.
    #[error(
        "[TCG-DIALECT-UNBOUND] `{dialect}.{op}` (in function `{function}`) is registered by the \
         `{dialect}` v{version} registration but has no lowering in this registry: {reason}"
    )]
    Unbound {
        dialect: String,
        version: u32,
        op: String,
        function: String,
        reason: String,
    },
    /// The selected rule is not admitted for the compile target
    /// ([`RuleTargets::AArch64Only`]).
    #[error(
        "[TCG-DIALECT-TARGET] rule `{rule}` for `{dialect}.{op}` (in function `{function}`) is \
         admitted only for {supported}; this compile targets {target}"
    )]
    TargetUnsupported {
        dialect: String,
        op: String,
        function: String,
        rule: String,
        supported: &'static str,
        target: String,
    },
    /// Proof-required compilation and a rule whose evidence is not checked here.
    #[error(
        "[TCG-DIALECT-PROOF] proof-required compilation refuses rule `{rule}` for {subject} \
         (dialect `{dialect}` v{version}): its evidence is {evidence}, which this compile does \
         not check"
    )]
    ProofPolicy {
        dialect: String,
        version: u32,
        subject: String,
        rule: String,
        evidence: String,
    },
    /// A runtime binding names a symbol the module already uses differently.
    #[error("[TCG-DIALECT-RUNTIME] runtime binding for `{dialect}.{op}`: {detail}")]
    RuntimeBinding {
        dialect: String,
        op: String,
        detail: String,
    },
    /// The legalized module fails trust-ir-build's validator where the source
    /// module did not.
    #[error(
        "[TCG-DIALECT-VALIDATION] the legalized module fails trust-ir-build validation where its \
         source did not: {findings}"
    )]
    LegalizedModuleInvalid { findings: String },
    /// A legalization invariant failed (fail-closed; never expected).
    #[error("[TCG-DIALECT-INTERNAL] {0}")]
    Internal(String),
}

/// A malformed [`DialectRegistration`], refused by [`DialectLegalizationRegistry::new`].
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum RegistrationError {
    #[error("[TCG-DIALECT-REGISTRATION] dialect namespace {namespace:?} is malformed: {detail}")]
    InvalidNamespace { namespace: String, detail: String },
    #[error("[TCG-DIALECT-REGISTRATION] dialect `{namespace}` registers version 0")]
    ZeroVersion { namespace: String },
    #[error("[TCG-DIALECT-REGISTRATION] dialect `{namespace}` has no semantic owner statement")]
    MissingOwner { namespace: String },
    #[error("[TCG-DIALECT-REGISTRATION] dialect `{namespace}` is registered twice")]
    DuplicateNamespace { namespace: String },
    #[error(
        "[TCG-DIALECT-REGISTRATION] dialect `{namespace}` v{version} wraps a validator for \
         `{validator_name}` v{validator_version}"
    )]
    ValidatorMismatch {
        namespace: String,
        version: u32,
        validator_name: String,
        validator_version: u32,
    },
    #[error(
        "[TCG-DIALECT-REGISTRATION] dialect `{namespace}`: trust-ir rejects its schema: {detail}"
    )]
    Schema { namespace: String, detail: String },
    #[error("[TCG-DIALECT-REGISTRATION] dialect `{namespace}` declares op `{op}` with no rule")]
    OpWithoutRule { namespace: String, op: String },
    #[error("[TCG-DIALECT-REGISTRATION] dialect `{namespace}` has a rule for undeclared op `{op}`")]
    RuleWithoutOp { namespace: String, op: String },
    #[error("[TCG-DIALECT-REGISTRATION] dialect `{namespace}` has two rules for op `{op}`")]
    DuplicateOpRule { namespace: String, op: String },
    #[error("[TCG-DIALECT-REGISTRATION] `{namespace}.{op}`: {detail}")]
    Alternatives {
        namespace: String,
        op: String,
        detail: String,
    },
    #[error("[TCG-DIALECT-REGISTRATION] rule id {rule:?} in dialect `{namespace}` is malformed")]
    InvalidRuleId { namespace: String, rule: String },
    #[error("[TCG-DIALECT-REGISTRATION] rule id `{rule}` is registered twice")]
    DuplicateRuleId { rule: String },
    #[error("[TCG-DIALECT-REGISTRATION] runtime binding for `{namespace}.{op}`: {detail}")]
    RuntimeBinding {
        namespace: String,
        op: String,
        detail: String,
    },
    #[error(
        "[TCG-DIALECT-REGISTRATION] type rule `{namespace}.{name}@{version}` is malformed: {detail}"
    )]
    TypeRule {
        namespace: String,
        name: String,
        version: u32,
        detail: String,
    },
    #[error("[TCG-DIALECT-REGISTRATION] rule `{rule}` declares malformed evidence: {detail}")]
    Evidence { rule: String, detail: String },
}

// ---------------------------------------------------------------------------
// Evidence
// ---------------------------------------------------------------------------

/// The evidence class a legalization rule rests on, recorded in every receipt.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LegalizationEvidence {
    /// The op is kept as a `DialectOp` and lowered by trust-cg-lower's own
    /// typed arm, under the same instruction-level evidence (machine proofs,
    /// when requested) as any core instruction. The legalization step adds no
    /// claim of its own.
    AdapterInstructionLowering,
    /// The nominal type is replaced by a core scalar carrier everywhere it
    /// occurs. Checked in this compile: trust-ir's nominal rule reports no
    /// `InvalidDialectType` finding (every instruction touching the type is
    /// exact-typed transport or a dialect op of the type's own namespace), the
    /// substitution is complete (no `Ty::Dialect` survives), and the legalized
    /// module validates. Transport instructions move values without inspecting
    /// them, so their meaning does not depend on the carrier; that parametricity
    /// is an argument, not a mechanized theorem. The carrier is also the type's
    /// native ABI, which the registration declares.
    CheckedTransportSubstitution,
    /// A theorem proved upstream about a MODEL of the rule, cited by name at the
    /// pinned revision. Not replayed by trust-cg, and the correspondence of the
    /// Rust rule to the modelled one is not checked here.
    CitedUpstreamTheorem { theorem: String, source: String },
    /// Differential and native tests only.
    TestedOnly { tests: String },
    /// The op's meaning is the named runtime's; trust-cg's part is to pass the
    /// payload descriptor and operands and return the result, which only the
    /// native tests exercise.
    RuntimeContract { runtime: String },
    /// The alternative binds no lowering ([`OpLowering::Unbound`]): every site
    /// selecting it is refused before any receipt exists.
    Unbound,
}

impl LegalizationEvidence {
    /// The stable class name (`adapter-instruction-lowering`, ...).
    pub fn class(&self) -> &'static str {
        match self {
            Self::AdapterInstructionLowering => "adapter-instruction-lowering",
            Self::CheckedTransportSubstitution => "checked-transport-substitution",
            Self::CitedUpstreamTheorem { .. } => "cited-upstream-theorem",
            Self::TestedOnly { .. } => "tested-only",
            Self::RuntimeContract { .. } => "runtime-contract",
            Self::Unbound => "unbound",
        }
    }

    /// Whether proof-required compilation admits a rule with this evidence.
    /// Only classes checked in the compile itself are admitted.
    pub fn admitted_when_proof_required(&self) -> bool {
        matches!(
            self,
            Self::AdapterInstructionLowering | Self::CheckedTransportSubstitution
        )
    }

    fn validate(&self, rule: &str) -> Result<(), RegistrationError> {
        let empty = |what: &str| RegistrationError::Evidence {
            rule: rule.to_string(),
            detail: format!("{what} must be nonempty"),
        };
        match self {
            Self::CitedUpstreamTheorem { theorem, source } => {
                if theorem.trim().is_empty() {
                    return Err(empty("the cited theorem name"));
                }
                if source.trim().is_empty() {
                    return Err(empty("the cited theorem source"));
                }
            }
            Self::TestedOnly { tests } if tests.trim().is_empty() => {
                return Err(empty("the test list"));
            }
            Self::RuntimeContract { runtime } if runtime.trim().is_empty() => {
                return Err(empty("the runtime owner"));
            }
            _ => {}
        }
        Ok(())
    }
}

impl fmt::Display for LegalizationEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AdapterInstructionLowering => {
                f.write_str("adapter-instruction-lowering (kept for trust-cg-lower's typed arm)")
            }
            Self::CheckedTransportSubstitution => f.write_str(
                "checked-transport-substitution (trust-ir nominal rule checked, substitution \
                 complete, legalized module validated)",
            ),
            Self::CitedUpstreamTheorem { theorem, source } => write!(
                f,
                "cited-upstream-theorem `{theorem}` ({source}; not replayed by trust-cg)"
            ),
            Self::TestedOnly { tests } => write!(f, "tested-only ({tests})"),
            Self::RuntimeContract { runtime } => {
                write!(f, "runtime-contract (semantics owned by {runtime})")
            }
            Self::Unbound => f.write_str("unbound (no lowering)"),
        }
    }
}

// ---------------------------------------------------------------------------
// Registration model
// ---------------------------------------------------------------------------

/// How a registration's op payloads are checked before any rule applies.
#[derive(Clone)]
pub enum DialectGrammar {
    /// trust-ir's exact `OperationSchema`s: operand and result types and the
    /// required attribute names and kinds. Checked against the module's actual
    /// SSA types by trust-ir-build's `validate_module_with_dialect_schemas`.
    Exact(Vec<OperationSchema>),
    /// A dialect-owned validator (`trust_ir::dialect::Dialect::validate`) for
    /// polymorphic ops a fixed signature cannot state (trust-ir's portable
    /// `vector` dialect, trust-cg's typed ops). Its `ops()` are the declared
    /// op names; its `name()` and `version()` must equal the registration's.
    Validator(Arc<dyn Dialect>),
}

impl fmt::Debug for DialectGrammar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Exact(ops) => f.debug_tuple("Exact").field(ops).finish(),
            Self::Validator(dialect) => f
                .debug_struct("Validator")
                .field("name", &dialect.name())
                .field("version", &dialect.version())
                .field("ops", &dialect.ops())
                .finish(),
        }
    }
}

impl DialectGrammar {
    fn op_names(&self) -> Vec<String> {
        match self {
            Self::Exact(ops) => ops.iter().map(|op| op.name.clone()).collect(),
            Self::Validator(dialect) => dialect.ops().iter().map(|op| op.to_string()).collect(),
        }
    }
}

/// A guard selecting a [`RuleAlternative`] for one op site.
#[derive(Clone, Copy)]
pub struct SiteGuard {
    /// Stable name, recorded in the registry digest (the digest identifies
    /// the guard by this name; it cannot see `admits`).
    pub name: &'static str,
    /// Whether the alternative applies to the site.
    pub admits: fn(&SiteView<'_>) -> bool,
}

impl fmt::Debug for SiteGuard {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SiteGuard")
            .field("name", &self.name)
            .finish()
    }
}

/// Which compile targets admit a rewrite rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuleTargets {
    /// Every target: the rule emits target-independent core trust-ir.
    Any,
    /// AArch64 only: the rule emits AArch64-only typed ops, or its native
    /// execution evidence exists only for AArch64. Any other target is
    /// refused by name ([`DialectPipelineError::TargetUnsupported`]).
    AArch64Only,
}

/// The signature of a rewrite rule: trust-ir's `LoweringPass::rewrite`.
pub type RewriteFn =
    fn(&InstrNode, &DialectInst, &[ValueId], &mut LoweringContext<'_>) -> RewriteOutcome;

/// A rule that rewrites an op into core trust-ir (or trust-cg typed ops).
#[derive(Clone, Copy)]
pub struct RewriteRule {
    /// Stable implementation name, recorded in the registry digest (the
    /// digest identifies the rule by this name; it cannot see `rewrite`).
    pub name: &'static str,
    pub targets: RuleTargets,
    pub rewrite: RewriteFn,
}

impl fmt::Debug for RewriteRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RewriteRule")
            .field("name", &self.name)
            .field("targets", &self.targets)
            .finish()
    }
}

/// What a rule does with an op site.
#[derive(Debug, Clone)]
pub enum OpLowering {
    /// Keep the `DialectOp`; trust-cg-lower's adapter lowers it.
    AdapterNative,
    /// Rewrite through trust-ir's lowering driver.
    Rewrite(RewriteRule),
    /// Replace the op by a call to the runtime entry `symbol` with the C
    /// signature `R symbol(const uint8_t *payload, uint64_t payload_len,
    /// operands...)`: the payload descriptor ([`encode_payload_descriptor`])
    /// is a read-only object the legalization adds to the module, the operand
    /// types are the exact schema's (nominal types pass as their carriers),
    /// and the result (at most one) is the op's.
    RuntimeCall { symbol: String },
    /// Registered, but this registry binds no lowering: refused with `reason`.
    Unbound { reason: String },
}

/// One way to legalize an op.
#[derive(Debug, Clone)]
pub struct RuleAlternative {
    /// Rule id, unique in a registry and recorded in every receipt.
    pub rule: String,
    /// `None` for the unconditional (last) alternative.
    pub guard: Option<SiteGuard>,
    pub lowering: OpLowering,
    pub evidence: LegalizationEvidence,
}

/// The rule for one op: alternatives tried in order; the last is unguarded.
#[derive(Debug, Clone)]
pub struct OpRule {
    pub op: String,
    pub alternatives: Vec<RuleAlternative>,
}

impl OpRule {
    /// A rule with one unconditional alternative.
    pub fn single(
        op: impl Into<String>,
        rule: impl Into<String>,
        lowering: OpLowering,
        evidence: LegalizationEvidence,
    ) -> Self {
        Self {
            op: op.into(),
            alternatives: vec![RuleAlternative {
                rule: rule.into(),
                guard: None,
                lowering,
                evidence,
            }],
        }
    }
}

/// The legalization of one nominal type to a core scalar carrier.
#[derive(Debug, Clone)]
pub struct TypeRule {
    pub name: String,
    pub version: u32,
    /// `I8`..`I64`, `U8`..`U64` or `Ptr`: the value's whole machine
    /// representation and native ABI.
    pub carrier: Ty,
    pub rule: String,
    pub evidence: LegalizationEvidence,
}

/// One dialect's legalization contract.
#[derive(Debug, Clone)]
pub struct DialectRegistration {
    pub namespace: String,
    /// The registration's schema version. For [`DialectGrammar::Exact`], every
    /// op payload must carry exactly this `DialectInst::version`.
    pub version: u32,
    /// Who defines the dialect's semantics (recorded in every receipt).
    pub owner: String,
    pub grammar: DialectGrammar,
    pub ops: Vec<OpRule>,
    pub types: Vec<TypeRule>,
}

impl DialectRegistration {
    /// Bind `op` to a runtime entry: its alternatives become one
    /// [`OpLowering::RuntimeCall`] with [`LegalizationEvidence::RuntimeContract`].
    /// The binding is checked when the registry is built.
    pub fn bind_runtime_call(
        mut self,
        op: &str,
        symbol: impl Into<String>,
        runtime_owner: impl Into<String>,
    ) -> Self {
        let symbol = symbol.into();
        let rule = OpRule::single(
            op,
            format!("{}.{op}/runtime-call:{symbol}", self.namespace),
            OpLowering::RuntimeCall { symbol },
            LegalizationEvidence::RuntimeContract {
                runtime: runtime_owner.into(),
            },
        );
        match self.ops.iter_mut().find(|existing| existing.op == op) {
            Some(existing) => *existing = rule,
            None => self.ops.push(rule),
        }
        self
    }
}

/// What a [`SiteGuard`] sees of one op site.
pub struct SiteView<'a> {
    pub op: &'a DialectInst,
    pub function: &'a Function,
    defs: &'a HashMap<ValueId, &'a Inst>,
}

impl<'a> SiteView<'a> {
    /// The instruction defining operand `index` in this function, or `None`
    /// for a block parameter or an undefined value.
    pub fn operand_definition(&self, index: usize) -> Option<&'a Inst> {
        let value = self.op.operands.get(index)?;
        self.defs.get(value).copied()
    }

    /// [`Self::operand_definition`] looking through `Copy` chains (exactly
    /// the trace the adapter's typed arms make); `None` for a block parameter,
    /// an undefined value or a `Copy` cycle.
    pub fn operand_origin(&self, index: usize) -> Option<&'a Inst> {
        let mut inst = self.operand_definition(index)?;
        let mut seen = BTreeSet::new();
        loop {
            match inst {
                Inst::Copy { operand, .. } => {
                    if !seen.insert(*operand) {
                        return None;
                    }
                    inst = self.defs.get(operand).copied()?;
                }
                other => return Some(other),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The registry
// ---------------------------------------------------------------------------

/// A checked, frozen set of [`DialectRegistration`]s.
#[derive(Clone)]
pub struct DialectLegalizationRegistry {
    inner: Arc<RegistryInner>,
}

struct RegistryInner {
    /// Sorted by namespace.
    registrations: Vec<DialectRegistration>,
    /// The `Exact` grammars, frozen by trust-ir.
    exact: DialectSchemaRegistry,
    exact_namespaces: BTreeSet<String>,
    digest: String,
}

impl fmt::Debug for DialectLegalizationRegistry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DialectLegalizationRegistry")
            .field(
                "dialects",
                &self
                    .inner
                    .registrations
                    .iter()
                    .map(|r| (r.namespace.as_str(), r.version))
                    .collect::<Vec<_>>(),
            )
            .field("digest", &self.inner.digest)
            .finish()
    }
}

impl Default for DialectLegalizationRegistry {
    fn default() -> Self {
        Self::trust_cg_default()
    }
}

fn valid_ident(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(trust_ir::dialect::inst::is_valid_dialect_name_char)
}

fn valid_c_symbol(symbol: &str) -> bool {
    let mut chars = symbol.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn admissible_carrier(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::Ptr
    )
}

impl DialectLegalizationRegistry {
    /// Check and freeze `registrations`.
    pub fn new(registrations: Vec<DialectRegistration>) -> Result<Self, RegistrationError> {
        let mut registrations = registrations;
        registrations.sort_by(|a, b| a.namespace.cmp(&b.namespace));
        let mut rule_ids = BTreeSet::new();
        let mut exact_schemas = Vec::new();
        let mut exact_namespaces = BTreeSet::new();
        for pair in registrations.windows(2) {
            if pair[0].namespace == pair[1].namespace {
                return Err(RegistrationError::DuplicateNamespace {
                    namespace: pair[1].namespace.clone(),
                });
            }
        }
        for registration in &registrations {
            let namespace = registration.namespace.clone();
            // trust-cg's own typed dialects predate trust-ir's lexical rule
            // (`trust-cg`, `trust-cg-aarch64-fp`); they are admitted only
            // through their validator objects, which name themselves.
            let lexical_ok = match &registration.grammar {
                DialectGrammar::Exact(_) => valid_ident(&namespace),
                DialectGrammar::Validator(_) => {
                    !namespace.is_empty()
                        && !namespace.contains('.')
                        && namespace.chars().all(|c| c.is_ascii_graphic())
                }
            };
            if !lexical_ok {
                return Err(RegistrationError::InvalidNamespace {
                    namespace,
                    detail: "a namespace must be nonempty ASCII letters, digits or '_' (no '.')"
                        .to_string(),
                });
            }
            if registration.version == 0 {
                return Err(RegistrationError::ZeroVersion { namespace });
            }
            if registration.owner.trim().is_empty() {
                return Err(RegistrationError::MissingOwner { namespace });
            }
            match &registration.grammar {
                DialectGrammar::Validator(dialect) => {
                    if dialect.name() != namespace || dialect.version() != registration.version {
                        return Err(RegistrationError::ValidatorMismatch {
                            namespace,
                            version: registration.version,
                            validator_name: dialect.name().to_string(),
                            validator_version: dialect.version(),
                        });
                    }
                }
                DialectGrammar::Exact(ops) => {
                    exact_namespaces.insert(namespace.clone());
                    exact_schemas.push(IrDialectSchema {
                        namespace: namespace.clone(),
                        version: registration.version,
                        operations: ops.clone(),
                    });
                }
            }
            let declared: BTreeSet<String> = registration.grammar.op_names().into_iter().collect();
            let mut ruled = BTreeSet::new();
            for rule in &registration.ops {
                if !ruled.insert(rule.op.clone()) {
                    return Err(RegistrationError::DuplicateOpRule {
                        namespace,
                        op: rule.op.clone(),
                    });
                }
                if !declared.contains(&rule.op) {
                    return Err(RegistrationError::RuleWithoutOp {
                        namespace,
                        op: rule.op.clone(),
                    });
                }
                check_alternatives(registration, rule, &mut rule_ids)?;
            }
            if let Some(op) = declared.difference(&ruled).next() {
                return Err(RegistrationError::OpWithoutRule {
                    namespace,
                    op: op.clone(),
                });
            }
            let mut types = BTreeSet::new();
            for rule in &registration.types {
                let type_error = |detail: &str| RegistrationError::TypeRule {
                    namespace: namespace.clone(),
                    name: rule.name.clone(),
                    version: rule.version,
                    detail: detail.to_string(),
                };
                if !valid_ident(&namespace) {
                    return Err(type_error(
                        "a nominal type's namespace must be ASCII letters, digits or '_'",
                    ));
                }
                if !valid_ident(&rule.name) {
                    return Err(type_error(
                        "the type name must be nonempty ASCII letters, digits or '_'",
                    ));
                }
                if rule.version == 0 {
                    return Err(type_error("the type version must be nonzero"));
                }
                if !types.insert((rule.name.clone(), rule.version)) {
                    return Err(type_error("the type is registered twice"));
                }
                if !admissible_carrier(&rule.carrier) {
                    return Err(type_error(
                        "the carrier must be a core integer scalar of at most 64 bits or `ptr`",
                    ));
                }
                check_rule_id(&namespace, &rule.rule, &mut rule_ids)?;
                rule.evidence.validate(&rule.rule)?;
                if let Some(detail) = type_evidence_mismatch(&rule.evidence) {
                    return Err(RegistrationError::Evidence {
                        rule: rule.rule.clone(),
                        detail: detail.to_string(),
                    });
                }
            }
        }
        let exact = DialectSchemaRegistry::new(exact_schemas).map_err(|error| {
            RegistrationError::Schema {
                namespace: schema_error_namespace(&error),
                detail: format!("{error:?}"),
            }
        })?;
        let digest = registry_digest(&registrations);
        Ok(Self {
            inner: Arc::new(RegistryInner {
                registrations,
                exact,
                exact_namespaces,
                digest,
            }),
        })
    }

    /// The registrations of [`Self::trust_cg_default`], for a caller that
    /// replaces or adds dialects.
    pub fn default_registrations() -> Vec<DialectRegistration> {
        vec![
            vector_registration(),
            bitfield_registration(),
            aarch64_fp_registration(),
            verif_registration(),
        ]
    }

    /// The backend's default registry: trust-ir's portable `vector` dialect,
    /// trust-cg's typed bitfield/mask and AArch64 FP ops, and the `verif` v1
    /// payload contract (validated, unbound).
    pub fn trust_cg_default() -> Self {
        static DEFAULT: OnceLock<DialectLegalizationRegistry> = OnceLock::new();
        DEFAULT
            .get_or_init(|| {
                Self::new(Self::default_registrations())
                    .expect("the built-in dialect registrations are well-formed (unit-tested)")
            })
            .clone()
    }

    pub fn registrations(&self) -> &[DialectRegistration] {
        &self.inner.registrations
    }

    /// The registration for `namespace`.
    pub fn get(&self, namespace: &str) -> Option<&DialectRegistration> {
        self.inner
            .registrations
            .binary_search_by(|r| r.namespace.as_str().cmp(namespace))
            .ok()
            .map(|index| &self.inner.registrations[index])
    }

    /// SHA-256 over the registry's canonical description: namespaces,
    /// versions, owners, exact grammars, rule ids, evidence and carriers, and
    /// the NAMES (with targets and op lists) of validators, guards and rewrite
    /// rules.
    ///
    /// The digest cannot see code: two registries whose validators, guards or
    /// rewrite functions differ under the same names have the same digest, so
    /// an equal digest identifies the declared registry, not the rules that
    /// ran. [`verify_legalization`] replays the legalization under a registry
    /// and compares the module it produces, which does see the rules' effect.
    pub fn digest(&self) -> &str {
        &self.inner.digest
    }
}

fn schema_error_namespace(error: &trust_ir::dialect::schema::SchemaError) -> String {
    use trust_ir::dialect::schema::SchemaError;
    match error {
        SchemaError::DuplicateDialect(namespace) | SchemaError::UnknownDialect(namespace) => {
            namespace.clone()
        }
        _ => "(exact grammar)".to_string(),
    }
}

fn check_rule_id(
    namespace: &str,
    rule: &str,
    seen: &mut BTreeSet<String>,
) -> Result<(), RegistrationError> {
    if rule.trim().is_empty() || rule.chars().any(|c| c.is_control() || c.is_whitespace()) {
        return Err(RegistrationError::InvalidRuleId {
            namespace: namespace.to_string(),
            rule: rule.to_string(),
        });
    }
    if !seen.insert(rule.to_string()) {
        return Err(RegistrationError::DuplicateRuleId {
            rule: rule.to_string(),
        });
    }
    Ok(())
}

fn check_alternatives(
    registration: &DialectRegistration,
    rule: &OpRule,
    rule_ids: &mut BTreeSet<String>,
) -> Result<(), RegistrationError> {
    let alternatives_error = |detail: &str| RegistrationError::Alternatives {
        namespace: registration.namespace.clone(),
        op: rule.op.clone(),
        detail: detail.to_string(),
    };
    let Some(last) = rule.alternatives.last() else {
        return Err(alternatives_error("the rule has no alternative"));
    };
    if last.guard.is_some() {
        return Err(alternatives_error(
            "the last alternative must be unguarded, so every site selects one",
        ));
    }
    if rule.alternatives[..rule.alternatives.len() - 1]
        .iter()
        .any(|alternative| alternative.guard.is_none())
    {
        return Err(alternatives_error(
            "an unguarded alternative before the last makes the later ones unreachable",
        ));
    }
    for alternative in &rule.alternatives {
        check_rule_id(&registration.namespace, &alternative.rule, rule_ids)?;
        alternative.evidence.validate(&alternative.rule)?;
        let binding_error = |detail: String| RegistrationError::RuntimeBinding {
            namespace: registration.namespace.clone(),
            op: rule.op.clone(),
            detail,
        };
        match &alternative.lowering {
            OpLowering::RuntimeCall { symbol } => {
                if !valid_c_symbol(symbol) {
                    return Err(binding_error(format!(
                        "symbol {symbol:?} is not a C identifier"
                    )));
                }
                let DialectGrammar::Exact(ops) = &registration.grammar else {
                    return Err(binding_error(
                        "a runtime call needs an exact op schema to state its C signature"
                            .to_string(),
                    ));
                };
                let schema = ops
                    .iter()
                    .find(|schema| schema.name == rule.op)
                    .ok_or_else(|| binding_error("the op has no exact schema".to_string()))?;
                if schema.results.len() > 1 {
                    return Err(binding_error(format!(
                        "the op has {} results; a runtime call returns at most one",
                        schema.results.len()
                    )));
                }
                if schema
                    .operands
                    .iter()
                    .any(|operand| !matches!(operand, OperandType::Exact(_)))
                {
                    return Err(binding_error(
                        "variadic and function-typed operands have no fixed C signature"
                            .to_string(),
                    ));
                }
            }
            OpLowering::Unbound { reason } if reason.trim().is_empty() => {
                return Err(alternatives_error("an unbound alternative must state why"));
            }
            _ => {}
        }
        if let Some(detail) = op_evidence_mismatch(&alternative.lowering, &alternative.evidence) {
            return Err(RegistrationError::Evidence {
                rule: alternative.rule.clone(),
                detail: detail.to_string(),
            });
        }
    }
    Ok(())
}

/// Why `evidence` cannot describe `lowering`, or `None` when it can. Each
/// lowering kind has the evidence classes it can actually rest on, so a
/// registration cannot, for example, label a rewrite with the class that
/// proof-required compilation admits.
fn op_evidence_mismatch(
    lowering: &OpLowering,
    evidence: &LegalizationEvidence,
) -> Option<&'static str> {
    use LegalizationEvidence as E;
    match (lowering, evidence) {
        (OpLowering::AdapterNative, E::AdapterInstructionLowering)
        | (OpLowering::Rewrite(_), E::CitedUpstreamTheorem { .. } | E::TestedOnly { .. })
        | (OpLowering::RuntimeCall { .. }, E::RuntimeContract { .. })
        | (OpLowering::Unbound { .. }, E::Unbound) => None,
        (OpLowering::AdapterNative, _) => {
            Some("an adapter-native alternative's evidence must be `AdapterInstructionLowering`")
        }
        (OpLowering::Rewrite(_), _) => Some(
            "a rewrite's evidence must be a cited upstream theorem or tests; no rewrite is \
             checked in the compile",
        ),
        (OpLowering::RuntimeCall { .. }, _) => {
            Some("a runtime call's evidence must be a runtime contract")
        }
        (OpLowering::Unbound { .. }, _) => {
            Some("an unbound alternative's evidence must be `Unbound`")
        }
    }
}

/// Why `evidence` cannot describe a nominal type's carrier substitution, or
/// `None` when it can.
fn type_evidence_mismatch(evidence: &LegalizationEvidence) -> Option<&'static str> {
    match evidence {
        LegalizationEvidence::AdapterInstructionLowering | LegalizationEvidence::Unbound => Some(
            "a type rule substitutes a carrier; its evidence cannot be adapter lowering or \
             unbound",
        ),
        _ => None,
    }
}

fn registry_digest(registrations: &[DialectRegistration]) -> String {
    let mut hasher = Sha256::new();
    let mut put = |bytes: &[u8]| {
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    };
    put(b"trust-cg-dialect-legalization-registry-v1");
    for registration in registrations {
        put(registration.namespace.as_bytes());
        put(&registration.version.to_le_bytes());
        put(registration.owner.as_bytes());
        put(format!("{:?}", registration.grammar).as_bytes());
        let mut ops: Vec<&OpRule> = registration.ops.iter().collect();
        ops.sort_by(|a, b| a.op.cmp(&b.op));
        for rule in ops {
            put(rule.op.as_bytes());
            for alternative in &rule.alternatives {
                put(alternative.rule.as_bytes());
                put(format!("{:?}", alternative.guard).as_bytes());
                put(format!("{:?}", alternative.lowering).as_bytes());
                put(format!("{:?}", alternative.evidence).as_bytes());
            }
        }
        let mut types: Vec<&TypeRule> = registration.types.iter().collect();
        types.sort_by(|a, b| (&a.name, a.version).cmp(&(&b.name, b.version)));
        for rule in types {
            put(format!("{rule:?}").as_bytes());
        }
    }
    hex(&hasher.finalize())
}

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn digest_parts(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update((part.len() as u64).to_le_bytes());
        hasher.update(part);
    }
    hex(&hasher.finalize())
}

// ---------------------------------------------------------------------------
// Default registrations
// ---------------------------------------------------------------------------

const VECTOR_OWNER: &str = "trust-ir portable vector dialect (trust-ir docs/dialects.md; the \
                            reference interpreter and the Lean model define its semantics)";
const VECTOR_THEOREM_SOURCE: &str = "trust-ir lean/trust_ir-semantics/TrustIr/Proofs/VectorDialectProps.lean at the pinned revision";
const VECTOR_FMA_TESTS: &str = "crates/trust-cg-codegen/tests/dialect_legalization_corpus.rs \
                                (native AOT and JIT against the trust-ir interpreter)";

/// trust-cg's wrapper over trust-ir's `vector` dialect validator.
///
/// Identical to `trust_ir::dialect::vector::VectorDialect` except that it also
/// admits the 64-bit (D-register) `<8 x i8>` `vector.pack_lanes` splat
/// (hashbrown's `uint8x8_t` control-byte broadcast), which the adapter lowers
/// to `dup.8b`; every other payload goes to the real validator.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct LenientVectorDialect;

impl Dialect for LenientVectorDialect {
    fn name(&self) -> &'static str {
        trust_ir::dialect::vector::VectorDialect.name()
    }

    fn version(&self) -> u32 {
        trust_ir::dialect::vector::VectorDialect.version()
    }

    fn ops(&self) -> &'static [&'static str] {
        trust_ir::dialect::vector::VectorDialect.ops()
    }

    fn validate(&self, inst: &DialectInst) -> Result<(), trust_ir::dialect::DialectError> {
        inst.validate_names()?;
        if trust_ir::dialect::vector::is_pack_lanes_op(inst)
            && let Some(Ty::Vector(elem, 8)) = inst.result_tys.first()
            && elem.as_ref() == &Ty::I8
        {
            return Ok(());
        }
        trust_ir::dialect::vector::VectorDialect.validate(inst)
    }
}

fn trust_ir_vector_rewrite(
    node: &InstrNode,
    op: &DialectInst,
    results: &[ValueId],
    context: &mut LoweringContext<'_>,
) -> RewriteOutcome {
    trust_ir::dialect::vector::VectorLoweringPass.rewrite(node, op, results, context)
}

/// `vector.fma` on `<4 x f32>` / `<2 x f64>`: per lane, extract the three
/// operands and apply trust-cg's AArch64 `fmadd` typed op (one rounding step,
/// never unfused), then insert the lane into the result. The addend vector
/// seeds the insert chain; every lane is overwritten.
fn vector_fma_per_lane_rewrite(
    _node: &InstrNode,
    op: &DialectInst,
    results: &[ValueId],
    context: &mut LoweringContext<'_>,
) -> RewriteOutcome {
    let spec = match trust_ir::dialect::vector::decode_fma(op) {
        Ok(spec) => spec,
        Err(reason) => return RewriteOutcome::Err(reason),
    };
    let [result] = results else {
        return RewriteOutcome::Err(format!(
            "{} needs exactly one result id, got {}",
            op.qualified_name(),
            results.len()
        ));
    };
    let [a, b, c] = op.operands.as_slice() else {
        return RewriteOutcome::Err(format!("{} needs three operands", op.qualified_name()));
    };
    let Ty::Vector(elem, lanes) = &spec.vector_ty else {
        return RewriteOutcome::Err(format!("{} has no vector type", op.qualified_name()));
    };
    let elem = elem.as_ref().clone();
    let mut nodes = Vec::new();
    let mut accumulator = *c;
    for lane in 0..*lanes {
        let mut fresh = || context.alloc_value();
        let ids = (|| -> Result<[ValueId; 5], trust_ir::IdSpaceExhausted> {
            Ok([fresh()?, fresh()?, fresh()?, fresh()?, fresh()?])
        })();
        let Ok([index, lane_a, lane_b, lane_c, fused]) = ids else {
            return RewriteOutcome::Err(format!(
                "{} needs fresh value ids the function does not have",
                op.qualified_name()
            ));
        };
        nodes.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(lane)),
            })
            .with_result(index),
        );
        for (source, lane_value) in [(*a, lane_a), (*b, lane_b), (*c, lane_c)] {
            nodes.push(
                InstrNode::new(Inst::ExtractElement {
                    ty: elem.clone(),
                    array: source,
                    index,
                })
                .with_result(lane_value),
            );
        }
        nodes.push(
            InstrNode::new(Inst::DialectOp(Box::new(
                trust_cg_lower::aarch64_fp_dialect::instruction(
                    trust_cg_lower::aarch64_fp_dialect::Operation::Fmadd,
                    elem.clone(),
                    &[lane_a, lane_b, lane_c],
                ),
            )))
            .with_result(fused),
        );
        let inserted = if lane + 1 == *lanes {
            *result
        } else {
            match context.alloc_value() {
                Ok(value) => value,
                Err(_) => {
                    return RewriteOutcome::Err(format!(
                        "{} needs fresh value ids the function does not have",
                        op.qualified_name()
                    ));
                }
            }
        };
        nodes.push(
            InstrNode::new(Inst::InsertElement {
                ty: spec.vector_ty.clone(),
                array: accumulator,
                index,
                value: fused,
            })
            .with_result(inserted),
        );
        accumulator = inserted;
    }
    RewriteOutcome::Replace(nodes)
}

/// The adapter's typed `mask_to_bits` arm accepts a compare result or a
/// canonical constant (through copies), and only those; the shape and lane
/// type are then checked by the adapter itself, exactly as before this
/// registry existed.
fn mask_from_compare_or_constant(site: &SiteView<'_>) -> bool {
    matches!(
        site.operand_origin(0),
        Some(Inst::ICmp { .. } | Inst::Const { .. })
    )
}

/// trust-ir's lane expansion reads and writes single lanes with
/// `ExtractElement` / `InsertElement`, which the adapter lowers for the
/// 128-bit integer lane vectors but not for the 64-bit `<8 x i8>`.
fn lane_vector_is_v64(site: &SiteView<'_>) -> bool {
    let vector_ty = site
        .op
        .attrs
        .iter()
        .find_map(|attr| match (&attr.name[..], &attr.value) {
            ("vector_ty", AttrValue::Ty(ty)) => Some(ty),
            _ => None,
        })
        .or_else(|| site.op.result_tys.first());
    matches!(vector_ty, Some(Ty::Vector(elem, 8)) if matches!(elem.as_ref(), Ty::I8 | Ty::U8))
}

/// The reason the default `vector` registration refuses a lane expansion of
/// a 64-bit `<8 x i8>` vector.
pub const V64_LANE_EXPANSION_UNBOUND_REASON: &str = "trust-ir's lane expansion of a 64-bit \
     `<8 x i8>` vector reads and writes single lanes with ExtractElement / InsertElement, which \
     trust-cg-lower lowers only for the 128-bit integer lane vectors";

fn v64_lane_expansion_unbound(op: &str) -> RuleAlternative {
    RuleAlternative {
        rule: format!("vector.{op}/v64-lane-expansion-unbound"),
        guard: Some(SiteGuard {
            name: "lane-vector-is-v8i8",
            admits: lane_vector_is_v64,
        }),
        lowering: OpLowering::Unbound {
            reason: V64_LANE_EXPANSION_UNBOUND_REASON.to_string(),
        },
        evidence: LegalizationEvidence::Unbound,
    }
}

fn adapter_native(rule: &str) -> RuleAlternative {
    RuleAlternative {
        rule: rule.to_string(),
        guard: None,
        lowering: OpLowering::AdapterNative,
        evidence: LegalizationEvidence::AdapterInstructionLowering,
    }
}

fn cited_vector_theorem(theorem: &str) -> LegalizationEvidence {
    LegalizationEvidence::CitedUpstreamTheorem {
        theorem: format!("TrustIr.Proofs.VectorDialectProps.{theorem}"),
        source: VECTOR_THEOREM_SOURCE.to_string(),
    }
}

/// trust-ir's `VectorLoweringPass` emits target-independent core trust-ir, but
/// this backend has executed its output only on AArch64
/// (`tests/dialect_legalization_corpus.rs`); every other target refuses it by
/// name, as the adapter refused the op before this registry existed.
fn trust_ir_vector_pass(name: &'static str) -> OpLowering {
    OpLowering::Rewrite(RewriteRule {
        name,
        targets: RuleTargets::AArch64Only,
        rewrite: trust_ir_vector_rewrite,
    })
}

fn vector_registration() -> DialectRegistration {
    use trust_ir::dialect::vector as v;
    let native = |op: &str| OpRule {
        op: op.to_string(),
        alternatives: vec![adapter_native(&format!("vector.{op}/adapter-native"))],
    };
    DialectRegistration {
        namespace: v::DIALECT.to_string(),
        version: 1,
        owner: VECTOR_OWNER.to_string(),
        grammar: DialectGrammar::Validator(Arc::new(LenientVectorDialect)),
        ops: vec![
            native(v::PACK_LANES_OP),
            native(v::EXTRACT_LANE_OP),
            native(v::INSERT_LANE_OP),
            OpRule {
                op: v::MASK_TO_BITS_OP.to_string(),
                alternatives: vec![
                    RuleAlternative {
                        rule: "vector.mask_to_bits/adapter-native-compare-mask".to_string(),
                        guard: Some(SiteGuard {
                            name: "mask-from-compare-or-constant",
                            admits: mask_from_compare_or_constant,
                        }),
                        lowering: OpLowering::AdapterNative,
                        evidence: LegalizationEvidence::AdapterInstructionLowering,
                    },
                    RuleAlternative {
                        rule: "vector.mask_to_bits/opaque-mask-unbound".to_string(),
                        guard: None,
                        lowering: OpLowering::Unbound {
                            reason: OPAQUE_MASK_UNBOUND_REASON.to_string(),
                        },
                        evidence: LegalizationEvidence::Unbound,
                    },
                ],
            },
            OpRule {
                op: v::REDUCE_OP.to_string(),
                alternatives: vec![
                    v64_lane_expansion_unbound(v::REDUCE_OP),
                    RuleAlternative {
                        rule: "vector.reduce/trust-ir-lane-fold".to_string(),
                        guard: None,
                        lowering: trust_ir_vector_pass("trust-ir VectorLoweringPass (reduce)"),
                        evidence: cited_vector_theorem("runsAgreeFrom_reduce"),
                    },
                ],
            },
            OpRule {
                op: v::SHUFFLE_OP.to_string(),
                alternatives: vec![
                    v64_lane_expansion_unbound(v::SHUFFLE_OP),
                    RuleAlternative {
                        rule: "vector.shuffle/trust-ir-lane-gather".to_string(),
                        guard: None,
                        lowering: trust_ir_vector_pass("trust-ir VectorLoweringPass (shuffle)"),
                        evidence: cited_vector_theorem("runsAgreeFrom_shuffle"),
                    },
                ],
            },
            OpRule::single(
                v::FMA_OP,
                "vector.fma/aarch64-per-lane-fmadd",
                OpLowering::Rewrite(RewriteRule {
                    name: "per-lane extract + trust-cg-aarch64-fp.fmadd + insert",
                    targets: RuleTargets::AArch64Only,
                    rewrite: vector_fma_per_lane_rewrite,
                }),
                LegalizationEvidence::TestedOnly {
                    tests: VECTOR_FMA_TESTS.to_string(),
                },
            ),
        ],
        types: Vec::new(),
    }
}

fn typed_registration(
    dialect: Arc<dyn Dialect>,
    owner: &str,
    rule_prefix: &str,
) -> DialectRegistration {
    let namespace = dialect.name().to_string();
    let ops = dialect
        .ops()
        .iter()
        .map(|op| OpRule {
            op: op.to_string(),
            alternatives: vec![adapter_native(&format!(
                "{rule_prefix}.{op}/adapter-native"
            ))],
        })
        .collect();
    DialectRegistration {
        namespace,
        version: dialect.version(),
        owner: owner.to_string(),
        grammar: DialectGrammar::Validator(dialect),
        ops,
        types: Vec::new(),
    }
}

fn bitfield_registration() -> DialectRegistration {
    typed_registration(
        Arc::new(trust_cg_lower::bitfield_dialect::BitfieldDialect),
        "trust-cg typed bitfield and compact mask-extract ops (trust-cg-lower bitfield_dialect)",
        "trust-cg",
    )
}

fn aarch64_fp_registration() -> DialectRegistration {
    typed_registration(
        Arc::new(trust_cg_lower::aarch64_fp_dialect::Aarch64FpDialect),
        "trust-cg typed AArch64 FP ops (trust-cg-lower aarch64_fp_dialect)",
        "trust-cg-aarch64-fp",
    )
}

/// The reason the default `vector` registration refuses `vector.mask_to_bits`
/// on a mask that is not a compare result or canonical constant.
pub const OPAQUE_MASK_UNBOUND_REASON: &str = "the mask is not a compare result or a canonical \
     constant, so this backend has no defined lane image for it: a bool-lane vector crosses \
     parameters, returns and block parameters only as an opaque register value and never \
     reaches memory (trust-cg-lower AdapterError::BoolLaneLayoutNotAdmitted, ruling \
     2026-09-21), and trust-ir's lane expansion reads it with a bool-lane ExtractElement the \
     adapter does not lower";

/// The reason the default `verif` registration binds no lowering.
pub const VERIF_UNBOUND_REASON: &str = "the verif v1 payload contract (trust-ir \
     docs/dialects.md) names no runtime symbol, and trust-ir's reference lowering calls a \
     hard-coded function id (illustrative only); bind a runtime entry with \
     DialectRegistration::bind_runtime_call";

/// trust-ir's `verif` v1 payload contract: `bfs_step(frontier: ptr, seen_set:
/// ptr) -> ptr [parallel: bool]`, `frontier_drain(frontier: ptr)`,
/// `fingerprint_batch(states: ptr, count: i64) -> ptr`. The internal
/// `bfs_step_lowered` staging op is not part of the contract.
pub fn verif_contract_registration() -> DialectRegistration {
    let schema =
        |name: &str, operands: Vec<Ty>, results: Vec<Ty>, attrs: &[(&str, AttributeKind)]| {
            OperationSchema {
                name: name.to_string(),
                operands: operands.into_iter().map(OperandType::Exact).collect(),
                results,
                attributes: attrs
                    .iter()
                    .map(|(name, kind)| AttributeSchema {
                        name: name.to_string(),
                        kind: *kind,
                    })
                    .collect(),
            }
        };
    let unbound = |op: &str| {
        OpRule::single(
            op,
            format!("verif.{op}/unbound"),
            OpLowering::Unbound {
                reason: VERIF_UNBOUND_REASON.to_string(),
            },
            LegalizationEvidence::Unbound,
        )
    };
    DialectRegistration {
        namespace: "verif".to_string(),
        version: 1,
        owner: "trust-ir cross-repo verif v1 payload contract (docs/dialects.md); no executable \
                semantics in trust-ir"
            .to_string(),
        grammar: DialectGrammar::Exact(vec![
            schema(
                "bfs_step",
                vec![Ty::Ptr, Ty::Ptr],
                vec![Ty::Ptr],
                &[("parallel", AttributeKind::Bool)],
            ),
            schema("frontier_drain", vec![Ty::Ptr], vec![], &[]),
            schema(
                "fingerprint_batch",
                vec![Ty::Ptr, Ty::I64],
                vec![Ty::Ptr],
                &[],
            ),
        ]),
        ops: vec![
            unbound("bfs_step"),
            unbound("frontier_drain"),
            unbound("fingerprint_batch"),
        ],
        types: Vec::new(),
    }
}

fn verif_registration() -> DialectRegistration {
    verif_contract_registration()
}

// ---------------------------------------------------------------------------
// Payload descriptors
// ---------------------------------------------------------------------------

/// Encode `op`'s payload for a runtime call.
///
/// Layout (all integers little-endian; a string is a `u32` byte length then
/// its UTF-8 bytes): magic `TCGD`, format version `u32` (1), dialect, op,
/// payload version `u32`, attribute count `u32`, then each attribute in
/// payload order as name, tag `u8`, value: `0` I64 (8 bytes), `1` U64 (8),
/// `2` F64 (IEEE-754 bits, 8), `3` Bool (1), `4` Str (string), `5` Bytes
/// (`u32` length then the bytes), `6` Ty (string: trust-ir's canonical type
/// spelling, closed types only).
pub fn encode_payload_descriptor(op: &DialectInst) -> Result<Vec<u8>, String> {
    fn put_str(out: &mut Vec<u8>, text: &str) -> Result<(), String> {
        let len =
            u32::try_from(text.len()).map_err(|_| "a string exceeds u32 bytes".to_string())?;
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(text.as_bytes());
        Ok(())
    }
    let mut out = Vec::new();
    out.extend_from_slice(PAYLOAD_DESCRIPTOR_MAGIC);
    out.extend_from_slice(&PAYLOAD_DESCRIPTOR_VERSION.to_le_bytes());
    put_str(&mut out, &op.dialect)?;
    put_str(&mut out, &op.op)?;
    out.extend_from_slice(&op.version.to_le_bytes());
    let count =
        u32::try_from(op.attrs.len()).map_err(|_| "too many attributes for u32".to_string())?;
    out.extend_from_slice(&count.to_le_bytes());
    for attr in &op.attrs {
        put_str(&mut out, &attr.name)?;
        match &attr.value {
            AttrValue::I64(value) => {
                out.push(0);
                out.extend_from_slice(&value.to_le_bytes());
            }
            AttrValue::U64(value) => {
                out.push(1);
                out.extend_from_slice(&value.to_le_bytes());
            }
            AttrValue::F64(value) => {
                out.push(2);
                out.extend_from_slice(&value.to_bits().to_le_bytes());
            }
            AttrValue::Bool(value) => {
                out.push(3);
                out.push(u8::from(*value));
            }
            AttrValue::Str(value) => {
                out.push(4);
                put_str(&mut out, value)?;
            }
            AttrValue::Bytes(value) => {
                out.push(5);
                let len = u32::try_from(value.len())
                    .map_err(|_| "a bytes attribute exceeds u32 bytes".to_string())?;
                out.extend_from_slice(&len.to_le_bytes());
                out.extend_from_slice(value);
            }
            AttrValue::Ty(ty) => {
                if !closed_type(ty) {
                    return Err(format!(
                        "type attribute `{}` names a module table entry; only closed types have \
                         a module-independent spelling",
                        attr.name
                    ));
                }
                out.push(6);
                put_str(&mut out, &ty.to_string())?;
            }
        }
    }
    Ok(out)
}

/// A type with no module-table reference (its spelling means the same thing
/// in every module).
fn closed_type(ty: &Ty) -> bool {
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        match ty {
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Dialect(_) => {}
            Ty::Tuple(types) => pending.extend(types),
            Ty::Vector(elem, _)
            | Ty::Ref(elem)
            | Ty::RefMut(elem)
            | Ty::PtrConst(elem)
            | Ty::PtrMut(elem)
            | Ty::Rc(elem) => pending.push(elem),
            _ => return false,
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Receipts and the report
// ---------------------------------------------------------------------------

/// What a receipt legalized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LegalizationSubject {
    Op {
        op: String,
        payload_version: u32,
    },
    Type {
        name: String,
        version: u32,
        carrier: String,
    },
}

impl fmt::Display for LegalizationSubject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Op {
                op,
                payload_version,
            } => write!(f, "op `{op}` (payload v{payload_version})"),
            Self::Type {
                name,
                version,
                carrier,
            } => write!(f, "type `{name}@{version}` (carrier `{carrier}`)"),
        }
    }
}

/// Where a receipt's subject occurred in the SOURCE module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LegalizationSite {
    Instruction {
        function: String,
        block: u32,
        index: u32,
    },
    /// A nominal type, with its number of occurrences in the source module
    /// (the positions `trust_ir::Module::visit_types` inventories).
    Module { occurrences: u64 },
}

/// One applied legalization rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LegalizationReceipt {
    pub dialect: String,
    /// The registration's schema version.
    pub dialect_version: u32,
    pub owner: String,
    pub subject: LegalizationSubject,
    pub rule: String,
    pub evidence: LegalizationEvidence,
    pub site: LegalizationSite,
    /// SHA-256 over the source occurrence (the op's node, or the type identity
    /// and occurrence count).
    pub input_digest: String,
    /// SHA-256 over what replaced it (the replacement nodes, the kept node, or
    /// the carrier and occurrence count).
    pub output_digest: String,
}

/// The legalization record a compile carries (`CompilationResult::dialect_legalization`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DialectLegalizationReport {
    /// [`DialectLegalizationRegistry::digest`] of the registry applied (it
    /// names the declared rules; it does not identify their code).
    pub registry_digest: String,
    pub target: String,
    pub proof_required: bool,
    /// Op-site receipts in source order (function, block, instruction), then
    /// type receipts sorted by identity.
    pub receipts: Vec<LegalizationReceipt>,
    /// Functions whose `source_provenance` was cleared because legalization
    /// changed their body or signature (a source digest no longer describes them).
    pub provenance_invalidated: Vec<String>,
}

impl DialectLegalizationReport {
    /// The report as JSON (the CLI's metrics carry it).
    pub fn to_json(&self) -> serde_json::Value {
        let receipts: Vec<serde_json::Value> = self
            .receipts
            .iter()
            .map(|receipt| {
                let subject = match &receipt.subject {
                    LegalizationSubject::Op {
                        op,
                        payload_version,
                    } => serde_json::json!({
                        "kind": "op",
                        "op": op,
                        "payload_version": payload_version,
                    }),
                    LegalizationSubject::Type {
                        name,
                        version,
                        carrier,
                    } => serde_json::json!({
                        "kind": "type",
                        "name": name,
                        "version": version,
                        "carrier": carrier,
                    }),
                };
                let site = match &receipt.site {
                    LegalizationSite::Instruction {
                        function,
                        block,
                        index,
                    } => serde_json::json!({
                        "function": function,
                        "block": block,
                        "index": index,
                    }),
                    LegalizationSite::Module { occurrences } => {
                        serde_json::json!({ "occurrences": occurrences })
                    }
                };
                serde_json::json!({
                    "dialect": receipt.dialect,
                    "dialect_version": receipt.dialect_version,
                    "owner": receipt.owner,
                    "subject": subject,
                    "rule": receipt.rule,
                    "evidence_class": receipt.evidence.class(),
                    "evidence": receipt.evidence.to_string(),
                    "site": site,
                    "input_digest": receipt.input_digest,
                    "output_digest": receipt.output_digest,
                })
            })
            .collect();
        serde_json::json!({
            "registry_digest": self.registry_digest,
            "target": self.target,
            "proof_required": self.proof_required,
            "receipts": receipts,
            "provenance_invalidated": self.provenance_invalidated,
        })
    }

    /// Number of op sites rewritten (not kept for the adapter).
    pub fn rewritten_op_sites(&self) -> usize {
        self.receipts
            .iter()
            .filter(|receipt| {
                matches!(receipt.subject, LegalizationSubject::Op { .. })
                    && receipt.input_digest != receipt.output_digest
            })
            .count()
    }
}

/// Options of one legalization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LegalizationOptions {
    pub target: Target,
    /// Admit only rules whose evidence this compile checks.
    pub proof_required: bool,
}

impl LegalizationOptions {
    /// Options for `target` under the given proof requirement.
    pub fn new(target: Target, proof_required: bool) -> Self {
        Self {
            target,
            proof_required,
        }
    }

    /// The host's architecture, no proof requirement (legacy entries).
    pub fn host() -> Self {
        let target = if cfg!(target_arch = "x86_64") {
            Target::X86_64
        } else {
            Target::Aarch64
        };
        Self::new(target, false)
    }
}

/// A legalized module and its report.
#[derive(Debug)]
pub struct Legalized<'m> {
    /// Borrowed when nothing was rewritten.
    pub module: Cow<'m, Module>,
    /// `None` when the module carries no dialect op or dialect type.
    pub report: Option<DialectLegalizationReport>,
}

// ---------------------------------------------------------------------------
// The driver
// ---------------------------------------------------------------------------

/// Whether `module` carries any `DialectOp` or `Ty::Dialect` occurrence.
pub fn module_has_dialect_constructs(module: &Module) -> bool {
    if module
        .instructions()
        .any(|node| matches!(node.inst, Inst::DialectOp(_)))
    {
        return true;
    }
    let mut found = false;
    module.visit_types(|ty| found |= matches!(ty, Ty::Dialect(_)));
    found
}

struct PlannedSite {
    function: usize,
    block: u32,
    index: u32,
    namespace: String,
    version: u32,
    owner: String,
    node: InstrNode,
    op: DialectInst,
    rule: String,
    evidence: LegalizationEvidence,
    action: PlannedAction,
}

#[derive(Clone)]
enum PlannedAction {
    Keep,
    Rewrite(RewriteRule),
    RuntimeCall {
        symbol: String,
        signature: FuncTy,
        descriptor: Vec<u8>,
    },
}

/// What the lowering pass executes for one site.
#[derive(Clone)]
enum PassAction {
    Rewrite(RewriteRule),
    RuntimeCall {
        callee: FuncId,
        descriptor: GlobalId,
        descriptor_len: u64,
    },
}

struct PassEntry {
    site: usize,
    results: Vec<ValueId>,
    op: DialectInst,
    action: PassAction,
}

#[derive(Default)]
struct PassState {
    plan: VecDeque<PassEntry>,
    done: Vec<(usize, Vec<InstrNode>)>,
}

/// The single lowering pass handed to trust-ir's `lower_module` for one
/// function: it rewrites exactly the planned sites, in order, matching each by
/// its result ids and exact payload, and leaves every other op alone.
struct RegistryPass {
    state: Arc<Mutex<PassState>>,
}

fn same_payload(a: &DialectInst, b: &DialectInst) -> bool {
    a.dialect == b.dialect
        && a.op == b.op
        && a.operands == b.operands
        && a.result_tys == b.result_tys
        && a.version == b.version
        && a.attrs.len() == b.attrs.len()
        && a.attrs.iter().zip(&b.attrs).all(|(x, y)| {
            x.name == y.name
                && match (&x.value, &y.value) {
                    (AttrValue::F64(p), AttrValue::F64(q)) => p.to_bits() == q.to_bits(),
                    (p, q) => p == q,
                }
        })
}

impl LoweringPass for RegistryPass {
    fn name(&self) -> &'static str {
        "trust-cg.dialect-legalization"
    }

    /// The pass applies trust-ir's diagnostic carry rule itself (see
    /// [`carry_diagnostic_metadata`]) before it records a replacement, so the
    /// nodes a receipt digests are exactly the nodes spliced into the module.
    fn preserves_metadata(&self) -> bool {
        false
    }

    fn rewrite(
        &self,
        node: &InstrNode,
        op: &DialectInst,
        results: &[ValueId],
        context: &mut LoweringContext<'_>,
    ) -> RewriteOutcome {
        let Ok(mut state) = self.state.lock() else {
            return RewriteOutcome::Err("dialect legalization state is poisoned".to_string());
        };
        let matches_next = state
            .plan
            .front()
            .is_some_and(|entry| entry.results == results && same_payload(&entry.op, op));
        if !matches_next {
            return RewriteOutcome::NoChange;
        }
        let Some(entry) = state.plan.pop_front() else {
            return RewriteOutcome::NoChange;
        };
        let outcome = match &entry.action {
            PassAction::Rewrite(rule) => (rule.rewrite)(node, op, results, context),
            PassAction::RuntimeCall {
                callee,
                descriptor,
                descriptor_len,
            } => runtime_call_nodes(op, results, *callee, *descriptor, *descriptor_len, context),
        };
        match outcome {
            RewriteOutcome::Replace(mut nodes) => {
                if nodes.is_empty() {
                    return RewriteOutcome::Err(format!(
                        "rule for {} produced no replacement",
                        op.qualified_name()
                    ));
                }
                carry_diagnostic_metadata(node, &mut nodes);
                state.done.push((entry.site, nodes.clone()));
                RewriteOutcome::Replace(nodes)
            }
            RewriteOutcome::NoChange => RewriteOutcome::Err(format!(
                "the rule selected for {} declined the site",
                op.qualified_name()
            )),
            RewriteOutcome::Err(reason) => RewriteOutcome::Err(reason),
        }
    }
}

/// trust-ir `lower_module`'s carry rule for a pass that preserves metadata:
/// the last replacement node inherits the original node's diagnostic `span`
/// and `scope` where it has none of its own (never proofs, proof context or
/// semantic claims).
fn carry_diagnostic_metadata(original: &InstrNode, replacement: &mut [InstrNode]) {
    if let Some(last) = replacement.last_mut() {
        if last.span.is_none() {
            last.span = original.span;
        }
        if last.scope.is_none() {
            last.scope = original.scope;
        }
    }
}

fn runtime_call_nodes(
    op: &DialectInst,
    results: &[ValueId],
    callee: FuncId,
    descriptor: GlobalId,
    descriptor_len: u64,
    context: &mut LoweringContext<'_>,
) -> RewriteOutcome {
    let (Ok(address), Ok(length)) = (context.alloc_value(), context.alloc_value()) else {
        return RewriteOutcome::Err(format!(
            "{} needs fresh value ids the function does not have",
            op.qualified_name()
        ));
    };
    let length_value = i128::from(descriptor_len);
    let mut args = vec![address, length];
    args.extend(op.operands.iter().copied());
    RewriteOutcome::Replace(vec![
        InstrNode::new(Inst::GlobalAddr { global: descriptor }).with_result(address),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(length_value),
        })
        .with_result(length),
        InstrNode::new(Inst::Call { callee, args }).with_results(results.iter().copied()),
    ])
}

fn function_defs(function: &Function) -> HashMap<ValueId, &Inst> {
    let mut defs = HashMap::new();
    for block in &function.blocks {
        for node in &block.body {
            for result in &node.results {
                defs.insert(*result, &node.inst);
            }
        }
    }
    defs
}

/// An ordered key for a nominal identity (`DialectTy` is not `Ord`).
type TypeKey = (String, String, u32);

fn type_key(identity: &DialectTy) -> TypeKey {
    (
        identity.namespace.clone(),
        identity.name.clone(),
        identity.version,
    )
}

fn target_name(target: Target) -> String {
    format!("{target:?}")
}

/// Legalize every dialect construct of `module` under `registry`.
///
/// Returns the module unchanged (borrowed, no report) when it carries no
/// dialect construct.
pub fn legalize_module<'m>(
    module: &'m Module,
    registry: &DialectLegalizationRegistry,
    options: LegalizationOptions,
) -> Result<Legalized<'m>, DialectPipelineError> {
    if !module_has_dialect_constructs(module) {
        return Ok(Legalized {
            module: Cow::Borrowed(module),
            report: None,
        });
    }

    // 1. Exact-name resolution of every nominal type, counting its
    // occurrences in the SOURCE module (what a type receipt reports).
    let mut dialect_types: BTreeMap<TypeKey, DialectTy> = BTreeMap::new();
    let mut source_occurrences: BTreeMap<TypeKey, u64> = BTreeMap::new();
    module.visit_types(|ty| {
        if let Ty::Dialect(identity) = ty {
            let key = type_key(identity);
            *source_occurrences.entry(key.clone()).or_insert(0) += 1;
            dialect_types
                .entry(key)
                .or_insert_with(|| identity.as_ref().clone());
        }
    });
    let mut type_rules: BTreeMap<TypeKey, (DialectTy, &DialectRegistration, &TypeRule)> =
        BTreeMap::new();
    for (key, identity) in &dialect_types {
        if let Err(error) = identity.validate() {
            return Err(DialectPipelineError::MalformedType {
                namespace: identity.namespace.clone(),
                name: identity.name.clone(),
                version: identity.version,
                detail: error.to_string(),
            });
        }
        let registration = registry.get(&identity.namespace).ok_or_else(|| {
            DialectPipelineError::UnregisteredDialect {
                namespace: identity.namespace.clone(),
                usage: format!(
                    "nominal type `{}.{}@{}`",
                    identity.namespace, identity.name, identity.version
                ),
            }
        })?;
        let rule = registration
            .types
            .iter()
            .find(|rule| rule.name == identity.name && rule.version == identity.version)
            .ok_or_else(|| DialectPipelineError::UnregisteredType {
                namespace: identity.namespace.clone(),
                name: identity.name.clone(),
                type_version: identity.version,
                version: registration.version,
            })?;
        type_rules.insert(key.clone(), (identity.clone(), registration, rule));
    }
    let carriers: HashMap<DialectTy, Ty> = type_rules
        .values()
        .map(|(identity, _, rule)| (identity.clone(), rule.carrier.clone()))
        .collect();

    // 2. Exact-name resolution and dialect-owned grammar of every op.
    let mut has_exact_ops = false;
    for function in &module.functions {
        for block in &function.blocks {
            for node in &block.body {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                let registration = registry.get(&op.dialect).ok_or_else(|| {
                    DialectPipelineError::UnregisteredDialect {
                        namespace: op.dialect.clone(),
                        usage: format!(
                            "op `{}` in function `{}`",
                            op.qualified_name(),
                            function.name
                        ),
                    }
                })?;
                if !registration.ops.iter().any(|rule| rule.op == op.op) {
                    return Err(DialectPipelineError::UnregisteredOp {
                        dialect: op.dialect.clone(),
                        version: registration.version,
                        op: op.op.clone(),
                        function: function.name.clone(),
                    });
                }
                match &registration.grammar {
                    DialectGrammar::Validator(dialect) => {
                        dialect
                            .validate(op)
                            .map_err(|error| DialectPipelineError::Grammar {
                                dialect: op.dialect.clone(),
                                version: registration.version,
                                op: op.op.clone(),
                                function: function.name.clone(),
                                detail: error.to_string(),
                            })?;
                    }
                    DialectGrammar::Exact(_) => has_exact_ops = true,
                }
            }
        }
    }

    // 3. trust-ir-build's verdict on the source: exact grammars against the
    // module's SSA types, and the nominal rule a carrier substitution relies on.
    let substitutes = !type_rules.is_empty();
    let mut baseline: Option<BTreeSet<String>> = None;
    if has_exact_ops || substitutes {
        let findings =
            trust_ir_build::validate_module_with_dialect_schemas(module, &registry.inner.exact);
        let mut kept = BTreeSet::new();
        for finding in findings {
            match &finding {
                trust_ir_build::ValidationError::InvalidDialectSchema { op, reason, .. } => {
                    let (dialect, op_name) = op.split_once('.').unwrap_or((op.as_str(), ""));
                    if registry.inner.exact_namespaces.contains(dialect) {
                        let function = module
                            .functions
                            .iter()
                            .find(|function| {
                                function.blocks.iter().any(|block| {
                                    block.body.iter().any(|node| {
                                        matches!(&node.inst, Inst::DialectOp(candidate)
                                            if candidate.qualified_name() == *op)
                                    })
                                })
                            })
                            .map(|function| function.name.clone())
                            .unwrap_or_default();
                        return Err(DialectPipelineError::Grammar {
                            dialect: dialect.to_string(),
                            version: registry.get(dialect).map_or(0, |r| r.version),
                            op: op_name.to_string(),
                            function,
                            detail: reason.clone(),
                        });
                    }
                    // A validator-grammar namespace is absent from the exact
                    // registry by construction; its payloads were checked above.
                }
                trust_ir_build::ValidationError::InvalidDialectType { location, detail } => {
                    return Err(DialectPipelineError::NominalUse {
                        detail: format!("{location}: {detail}"),
                    });
                }
                _ => {
                    kept.insert(finding.to_string());
                }
            }
        }
        baseline = Some(kept);
    }

    // 4. Planning: one alternative per site, target support, the proof policy.
    let mut sites: Vec<PlannedSite> = Vec::new();
    for (function_index, function) in module.functions.iter().enumerate() {
        let defs = function_defs(function);
        for block in &function.blocks {
            for (index, node) in block.body.iter().enumerate() {
                let Inst::DialectOp(op) = &node.inst else {
                    continue;
                };
                let registration = registry.get(&op.dialect).ok_or_else(|| {
                    DialectPipelineError::Internal("resolved dialect vanished".into())
                })?;
                let rule = registration
                    .ops
                    .iter()
                    .find(|rule| rule.op == op.op)
                    .ok_or_else(|| DialectPipelineError::Internal("resolved op vanished".into()))?;
                let view = SiteView {
                    op,
                    function,
                    defs: &defs,
                };
                let alternative = rule
                    .alternatives
                    .iter()
                    .find(|alternative| alternative.guard.is_none_or(|guard| (guard.admits)(&view)))
                    .ok_or_else(|| {
                        DialectPipelineError::Internal(format!(
                            "no alternative of `{}` selected a site",
                            op.qualified_name()
                        ))
                    })?;
                let action = match &alternative.lowering {
                    OpLowering::AdapterNative => PlannedAction::Keep,
                    OpLowering::Unbound { reason } => {
                        return Err(DialectPipelineError::Unbound {
                            dialect: op.dialect.clone(),
                            version: registration.version,
                            op: op.op.clone(),
                            function: function.name.clone(),
                            reason: reason.clone(),
                        });
                    }
                    OpLowering::Rewrite(rewrite) => {
                        if rewrite.targets == RuleTargets::AArch64Only
                            && options.target != Target::Aarch64
                        {
                            return Err(DialectPipelineError::TargetUnsupported {
                                dialect: op.dialect.clone(),
                                op: op.op.clone(),
                                function: function.name.clone(),
                                rule: alternative.rule.clone(),
                                supported: "AArch64",
                                target: target_name(options.target),
                            });
                        }
                        PlannedAction::Rewrite(*rewrite)
                    }
                    OpLowering::RuntimeCall { symbol } => {
                        let DialectGrammar::Exact(schemas) = &registration.grammar else {
                            return Err(DialectPipelineError::Internal(
                                "runtime call without an exact schema".into(),
                            ));
                        };
                        let schema = schemas
                            .iter()
                            .find(|schema| schema.name == op.op)
                            .ok_or_else(|| {
                                DialectPipelineError::Internal("runtime op lost its schema".into())
                            })?;
                        // The declaration is spelled in carriers: a nominal
                        // type crosses the runtime ABI as the carrier its
                        // registration declares, and the declaration then
                        // needs no substitution of its own.
                        let mut params = vec![Ty::Ptr, Ty::I64];
                        for operand in &schema.operands {
                            let OperandType::Exact(ty) = operand else {
                                return Err(DialectPipelineError::Internal(
                                    "runtime operand is not exact".into(),
                                ));
                            };
                            params.push(with_carriers(ty, &carriers));
                        }
                        let returns: Vec<Ty> = schema
                            .results
                            .iter()
                            .map(|ty| with_carriers(ty, &carriers))
                            .collect();
                        if params.iter().chain(&returns).any(Ty::contains_dialect) {
                            return Err(DialectPipelineError::Internal(format!(
                                "the runtime signature of `{}` keeps a nominal type no rule \
                                 resolved",
                                op.qualified_name()
                            )));
                        }
                        let descriptor = encode_payload_descriptor(op).map_err(|detail| {
                            DialectPipelineError::RuntimeBinding {
                                dialect: op.dialect.clone(),
                                op: op.op.clone(),
                                detail,
                            }
                        })?;
                        PlannedAction::RuntimeCall {
                            symbol: symbol.clone(),
                            signature: FuncTy {
                                params,
                                returns,
                                abi: None,
                                is_vararg: false,
                            },
                            descriptor,
                        }
                    }
                };
                if options.proof_required && !alternative.evidence.admitted_when_proof_required() {
                    return Err(DialectPipelineError::ProofPolicy {
                        dialect: op.dialect.clone(),
                        version: registration.version,
                        subject: format!(
                            "op `{}` in function `{}`",
                            op.qualified_name(),
                            function.name
                        ),
                        rule: alternative.rule.clone(),
                        evidence: alternative.evidence.to_string(),
                    });
                }
                sites.push(PlannedSite {
                    function: function_index,
                    block: block.id.index(),
                    index: u32::try_from(index)
                        .map_err(|_| DialectPipelineError::Internal("block too long".into()))?,
                    namespace: registration.namespace.clone(),
                    version: registration.version,
                    owner: registration.owner.clone(),
                    node: node.clone(),
                    op: op.as_ref().clone(),
                    rule: alternative.rule.clone(),
                    evidence: alternative.evidence.clone(),
                    action,
                });
            }
        }
    }
    for (identity, registration, rule) in type_rules.values() {
        if options.proof_required && !rule.evidence.admitted_when_proof_required() {
            return Err(DialectPipelineError::ProofPolicy {
                dialect: registration.namespace.clone(),
                version: registration.version,
                subject: format!(
                    "type `{}.{}@{}`",
                    identity.namespace, identity.name, identity.version
                ),
                rule: rule.rule.clone(),
                evidence: rule.evidence.to_string(),
            });
        }
    }

    let rewrites_planned = sites
        .iter()
        .any(|site| !matches!(site.action, PlannedAction::Keep));
    if rewrites_planned && baseline.is_none() {
        baseline = Some(
            trust_ir_build::validate_module(module)
                .iter()
                .map(ToString::to_string)
                .collect(),
        );
    }
    // A dialect op may touch a nominal type only when both belong to one
    // namespace (its own rule then owns the semantic content): neither its
    // payload (result and type-attribute types) nor its operands may carry a
    // nominal type of another namespace. trust-ir's own nominal rule admits
    // any dialect op; this backend is stricter.
    if substitutes {
        let mut operand_types: HashMap<usize, HashMap<ValueId, Ty>> = HashMap::new();
        for site in &sites {
            let mut foreign: Option<(DialectTy, &str)> = None;
            site.node.inst.visit_types(|ty| {
                if let Ty::Dialect(identity) = ty
                    && identity.namespace != site.namespace
                {
                    foreign = Some((identity.as_ref().clone(), "spells"));
                }
            });
            let values = operand_types
                .entry(site.function)
                .or_insert_with(|| nominal_value_types(module, &module.functions[site.function]));
            for operand in &site.op.operands {
                if let Some(ty) = values.get(operand) {
                    ty.visit_types(|ty| {
                        if let Ty::Dialect(identity) = ty
                            && identity.namespace != site.namespace
                        {
                            foreign = Some((identity.as_ref().clone(), "consumes a value of"));
                        }
                    });
                }
            }
            if let Some((identity, how)) = foreign {
                return Err(DialectPipelineError::NominalUse {
                    detail: format!(
                        "op `{}` in function `{}` {how} nominal type `{}.{}@{}` of another \
                         namespace",
                        site.op.qualified_name(),
                        module.functions[site.function].name,
                        identity.namespace,
                        identity.name,
                        identity.version
                    ),
                });
            }
        }
    }

    // 5. Rewrite.
    let mut legalized: Cow<'m, Module> = Cow::Borrowed(module);
    let mut outputs: BTreeMap<usize, Vec<InstrNode>> = BTreeMap::new();
    let mut added_runtime_symbols: BTreeSet<String> = BTreeSet::new();
    let mut provenance_invalidated: BTreeSet<usize> = BTreeSet::new();
    if rewrites_planned {
        let owned = legalized.to_mut();
        let mut runtime_actions: HashMap<usize, PassAction> = HashMap::new();
        for (site_index, site) in sites.iter().enumerate() {
            if let PlannedAction::RuntimeCall {
                symbol,
                signature,
                descriptor,
            } = &site.action
            {
                let callee = ensure_runtime_declaration(
                    owned,
                    site,
                    symbol,
                    signature,
                    &carriers,
                    &mut added_runtime_symbols,
                )?;
                let (global, len) = ensure_descriptor_global(owned, site, descriptor)?;
                runtime_actions.insert(
                    site_index,
                    PassAction::RuntimeCall {
                        callee,
                        descriptor: global,
                        descriptor_len: len,
                    },
                );
            }
        }
        let functions_with_rewrites: BTreeSet<usize> = sites
            .iter()
            .filter(|site| !matches!(site.action, PlannedAction::Keep))
            .map(|site| site.function)
            .collect();
        for function_index in functions_with_rewrites {
            let mut plan = VecDeque::new();
            for (site_index, site) in sites.iter().enumerate() {
                if site.function != function_index {
                    continue;
                }
                let action = match &site.action {
                    PlannedAction::Keep => continue,
                    PlannedAction::Rewrite(rule) => PassAction::Rewrite(*rule),
                    PlannedAction::RuntimeCall { .. } => {
                        runtime_actions.get(&site_index).cloned().ok_or_else(|| {
                            DialectPipelineError::Internal("unplanned runtime site".into())
                        })?
                    }
                };
                plan.push_back(PassEntry {
                    site: site_index,
                    results: site.node.results.clone(),
                    op: site.op.clone(),
                    action,
                });
            }
            let state = Arc::new(Mutex::new(PassState {
                plan,
                done: Vec::new(),
            }));
            let function = std::mem::replace(
                &mut owned.functions[function_index],
                Function::new(
                    FuncId::new(0),
                    "",
                    trust_ir::FuncTyId::new(0),
                    BlockId::new(0),
                ),
            );
            let function_name = function.name.clone();
            let mut shell = Module::new(owned.name.clone());
            shell.functions.push(function);
            let passes: Vec<Box<dyn LoweringPass>> = vec![Box::new(RegistryPass {
                state: Arc::clone(&state),
            })];
            let lowered = trust_ir::dialect::lower_module(&mut shell, &passes, MAX_LOWERING_ITERS);
            let restored = shell.functions.pop().ok_or_else(|| {
                DialectPipelineError::Internal("lowering lost the function".into())
            })?;
            owned.functions[function_index] = restored;
            lowered.map_err(|error| {
                DialectPipelineError::Lowering(format!("function `{function_name}`: {error}"))
            })?;
            let mut state = state
                .lock()
                .map_err(|_| DialectPipelineError::Internal("poisoned state".into()))?;
            if let Some(missed) = state.plan.front() {
                return Err(DialectPipelineError::Internal(format!(
                    "planned site `{}` in function `{function_name}` was not reached",
                    missed.op.qualified_name()
                )));
            }
            for (site, nodes) in state.done.drain(..) {
                outputs.insert(site, nodes);
            }
            provenance_invalidated.insert(function_index);
        }
    }

    // 6. Substitute carriers for nominal types. Only source functions carry
    // a provenance a substitution can invalidate; a runtime declaration the
    // legalization appended is spelled in carriers already.
    if substitutes {
        let owned = legalized.to_mut();
        let touched = substitute_module_types(owned, &carriers);
        provenance_invalidated.extend(
            touched
                .into_iter()
                .filter(|index| *index < module.functions.len()),
        );
        let mut survivor = None;
        owned.visit_types(|ty| {
            if survivor.is_none()
                && let Ty::Dialect(identity) = ty
            {
                survivor = Some(identity.as_ref().clone());
            }
        });
        if let Some(identity) = survivor {
            return Err(DialectPipelineError::Internal(format!(
                "carrier substitution left `{}.{}@{}` in the module",
                identity.namespace, identity.name, identity.version
            )));
        }
    }
    if let Cow::Owned(owned) = &mut legalized {
        for index in &provenance_invalidated {
            owned.functions[*index].source_provenance = None;
        }
    }

    // 7. The legalized module meets the verifier its source met.
    if let (Cow::Owned(owned), Some(baseline)) = (&legalized, &baseline) {
        let mut new_findings = Vec::new();
        for finding in trust_ir_build::validate_module(owned) {
            let text = finding.to_string();
            if baseline.contains(&text) {
                continue;
            }
            // A runtime binding's declaration is an FFI boundary whose ABI the
            // registration declares; it is admitted under the compile target.
            if let trust_ir_build::ValidationError::TargetInfoRequired { boundary } = &finding
                && added_runtime_symbols
                    .iter()
                    .any(|symbol| boundary.contains(&format!("`{symbol}`")))
            {
                continue;
            }
            new_findings.push(text);
        }
        if !new_findings.is_empty() {
            return Err(DialectPipelineError::LegalizedModuleInvalid {
                findings: new_findings.join("; "),
            });
        }
    }

    // 8. Receipts.
    let mut receipts = Vec::with_capacity(sites.len() + type_rules.len());
    for (site_index, site) in sites.iter().enumerate() {
        let input = format!("{:?}", site.node);
        let output = match outputs.get(&site_index) {
            Some(nodes) => format!("{nodes:?}"),
            None if matches!(site.action, PlannedAction::Keep) => input.clone(),
            None => {
                return Err(DialectPipelineError::Internal(format!(
                    "rewritten site `{}` has no recorded replacement",
                    site.op.qualified_name()
                )));
            }
        };
        let kind: &[u8] = if outputs.contains_key(&site_index) {
            b"rewritten"
        } else {
            b"kept"
        };
        receipts.push(LegalizationReceipt {
            dialect: site.namespace.clone(),
            dialect_version: site.version,
            owner: site.owner.clone(),
            subject: LegalizationSubject::Op {
                op: site.op.op.clone(),
                payload_version: site.op.version,
            },
            rule: site.rule.clone(),
            evidence: site.evidence.clone(),
            site: LegalizationSite::Instruction {
                function: module.functions[site.function].name.clone(),
                block: site.block,
                index: site.index,
            },
            input_digest: digest_parts(&[b"op", input.as_bytes()]),
            output_digest: if kind == b"kept" {
                digest_parts(&[b"op", output.as_bytes()])
            } else {
                digest_parts(&[kind, output.as_bytes()])
            },
        });
    }
    for (key, (identity, registration, rule)) in &type_rules {
        let count = source_occurrences.get(key).copied().unwrap_or(0);
        let carrier = rule.carrier.to_string();
        let identity_text = format!(
            "{}.{}@{}",
            identity.namespace, identity.name, identity.version
        );
        receipts.push(LegalizationReceipt {
            dialect: registration.namespace.clone(),
            dialect_version: registration.version,
            owner: registration.owner.clone(),
            subject: LegalizationSubject::Type {
                name: identity.name.clone(),
                version: identity.version,
                carrier: carrier.clone(),
            },
            rule: rule.rule.clone(),
            evidence: rule.evidence.clone(),
            site: LegalizationSite::Module { occurrences: count },
            input_digest: digest_parts(&[b"type", identity_text.as_bytes(), &count.to_le_bytes()]),
            output_digest: digest_parts(&[b"carrier", carrier.as_bytes(), &count.to_le_bytes()]),
        });
    }
    let provenance_invalidated = provenance_invalidated
        .iter()
        .map(|index| {
            module
                .functions
                .get(*index)
                .map(|function| function.name.clone())
                .ok_or_else(|| {
                    DialectPipelineError::Internal(format!(
                        "function {index} whose provenance was invalidated is not a source function"
                    ))
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let report = DialectLegalizationReport {
        registry_digest: registry.digest().to_string(),
        target: target_name(options.target),
        proof_required: options.proof_required,
        receipts,
        provenance_invalidated,
    };
    Ok(Legalized {
        module: legalized,
        report: Some(report),
    })
}

/// Find or add the declaration of `symbol` with `signature` (spelled in
/// carriers). An existing function named `symbol` is reused only when its
/// signature, with the module's nominal types replaced by their carriers, is
/// exactly `signature`.
fn ensure_runtime_declaration(
    module: &mut Module,
    site: &PlannedSite,
    symbol: &str,
    signature: &FuncTy,
    carriers: &HashMap<DialectTy, Ty>,
    added: &mut BTreeSet<String>,
) -> Result<FuncId, DialectPipelineError> {
    let conflict = |detail: String| DialectPipelineError::RuntimeBinding {
        dialect: site.namespace.clone(),
        op: site.op.op.clone(),
        detail,
    };
    if let Some(existing) = module.functions.iter().find(|f| f.name == symbol) {
        let actual = module
            .func_type(existing.ty)
            .map(|actual| signature_with_carriers(actual, carriers));
        if actual.as_ref() != Some(signature) {
            return Err(conflict(format!(
                "the module already has a function `{symbol}` with signature {actual:?}, not the \
                 binding's {signature:?}"
            )));
        }
        return Ok(existing.id);
    }
    if module.globals.iter().any(|global| global.name == symbol) {
        return Err(conflict(format!("`{symbol}` already names a global")));
    }
    let next = module
        .functions
        .iter()
        .map(|function| function.id.index())
        .max()
        .map_or(Some(0), |max| max.checked_add(1))
        .ok_or_else(|| conflict("the function id space is exhausted".to_string()))?;
    let id = FuncId::new(next);
    let ty = module
        .intern_func_type(signature.clone())
        .map_err(|exhausted| conflict(exhausted.to_string()))?;
    let declaration = Function::new(id, symbol, ty, BlockId::new(0));
    module
        .try_add_function(declaration)
        .map_err(|_| conflict("the obligation id space is exhausted".to_string()))?;
    added.insert(symbol.to_string());
    Ok(id)
}

fn ensure_descriptor_global(
    module: &mut Module,
    site: &PlannedSite,
    descriptor: &[u8],
) -> Result<(GlobalId, u64), DialectPipelineError> {
    let digest = digest_parts(&[b"descriptor", descriptor]);
    let name = format!("__tcg_dialect_payload_{}", &digest[..16]);
    let len = u64::try_from(descriptor.len())
        .map_err(|_| DialectPipelineError::Internal("descriptor too large".into()))?;
    let initializer = Constant::Bytes {
        data: descriptor.to_vec(),
        utf8: false,
    };
    if let Some(position) = module.globals.iter().position(|global| global.name == name) {
        let global = &module.globals[position];
        let exact_byte_array = matches!(&global.ty, Ty::Array(byte, count)
            if *count == len
                && module.types.get(byte.index() as usize) == Some(&Ty::U8));
        if global.initializer.as_ref() != Some(&initializer)
            || !exact_byte_array
            || global.mutable
            || global.linkage != Linkage::Internal
            || global.tls.is_some()
            || global.section.is_some()
        {
            return Err(DialectPipelineError::RuntimeBinding {
                dialect: site.namespace.clone(),
                op: site.op.op.clone(),
                detail: format!(
                    "global `{name}` already exists without the exact private, immutable byte-array descriptor"
                ),
            });
        }
        let id = u32::try_from(position)
            .map_err(|_| DialectPipelineError::Internal("global id overflow".into()))?;
        return Ok((GlobalId::new(id), len));
    }
    let byte = match module.types.iter().position(|ty| *ty == Ty::U8) {
        Some(position) => trust_ir::TyId::new(
            u32::try_from(position)
                .map_err(|_| DialectPipelineError::Internal("type id overflow".into()))?,
        ),
        None => module
            .add_type(Ty::U8)
            .map_err(|_| DialectPipelineError::Internal("type id overflow".into()))?,
    };
    let id = u32::try_from(module.globals.len())
        .map_err(|_| DialectPipelineError::Internal("global id overflow".into()))?;
    module.globals.push(Global {
        name,
        ty: Ty::Array(byte, len),
        mutable: false,
        initializer: Some(initializer),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    Ok((GlobalId::new(id), len))
}

// ---------------------------------------------------------------------------
// Carrier substitution
// ---------------------------------------------------------------------------

/// Replace every nominal type in `ty` (inline children included, without
/// recursion); whether anything changed.
fn substitute_ty(ty: &mut Ty, carriers: &HashMap<DialectTy, Ty>) -> bool {
    let mut changed = false;
    let mut pending: Vec<&mut Ty> = vec![ty];
    while let Some(current) = pending.pop() {
        let replacement = match &*current {
            Ty::Dialect(identity) => carriers.get(identity.as_ref()).cloned(),
            _ => None,
        };
        if let Some(carrier) = replacement {
            *current = carrier;
            changed = true;
            continue;
        }
        match current {
            Ty::Vector(inner, _)
            | Ty::Ref(inner)
            | Ty::RefMut(inner)
            | Ty::PtrConst(inner)
            | Ty::PtrMut(inner)
            | Ty::Rc(inner) => pending.push(inner.as_mut()),
            Ty::Tuple(types) => pending.extend(types.iter_mut()),
            _ => {}
        }
    }
    changed
}

/// `ty` with every registered nominal type replaced by its carrier.
fn with_carriers(ty: &Ty, carriers: &HashMap<DialectTy, Ty>) -> Ty {
    let mut ty = ty.clone();
    substitute_ty(&mut ty, carriers);
    ty
}

/// `signature` with every registered nominal type replaced by its carrier.
fn signature_with_carriers(signature: &FuncTy, carriers: &HashMap<DialectTy, Ty>) -> FuncTy {
    FuncTy {
        params: signature
            .params
            .iter()
            .map(|ty| with_carriers(ty, carriers))
            .collect(),
        returns: signature
            .returns
            .iter()
            .map(|ty| with_carriers(ty, carriers))
            .collect(),
        is_vararg: signature.is_vararg,
        // Keep recorded carrier placement when comparing a real signature;
        // unrecorded runtime bindings must not erase a producer's ABI claims.
        abi: signature.abi.clone(),
    }
}

/// The types of the values `function` defines whose type spells a nominal
/// type. trust-ir's nominal rule (checked before this is used) admits a
/// nominal value only from a block parameter or the result of exact-typed
/// transport (`Copy`, `Select`, a call) or a dialect op, so those producers
/// are the complete set.
fn nominal_value_types(module: &Module, function: &Function) -> HashMap<ValueId, Ty> {
    let mut types = HashMap::new();
    let mut record = |value: ValueId, ty: &Ty| {
        if ty.contains_dialect() {
            types.insert(value, ty.clone());
        }
    };
    let returns_of = |signature: Option<&FuncTy>| -> Vec<Ty> {
        signature.map_or_else(Vec::new, |signature| signature.returns.clone())
    };
    for block in &function.blocks {
        for (value, ty) in &block.params {
            record(*value, ty);
        }
        for node in &block.body {
            let results: Vec<Ty> = match &node.inst {
                Inst::Copy { ty, .. } | Inst::Select { ty, .. } => vec![ty.clone()],
                Inst::DialectOp(op) => op.result_tys.clone(),
                Inst::MakeClosure { ty, .. } => vec![Ty::Closure(*ty)],
                Inst::Call { callee, .. }
                | Inst::CallCannotUnwind { callee, .. }
                | Inst::Invoke { callee, .. } => returns_of(
                    module
                        .functions
                        .iter()
                        .find(|candidate| candidate.id == *callee)
                        .and_then(|callee| module.func_type(callee.ty)),
                ),
                Inst::CallIndirect { sig, .. }
                | Inst::CallIndirectCannotUnwind { sig, .. }
                | Inst::InvokeIndirect { sig, .. } => returns_of(module.func_type(*sig)),
                _ => Vec::new(),
            };
            for (value, ty) in node.results.iter().zip(&results) {
                record(*value, ty);
            }
        }
    }
    types
}

/// Every type an instruction spells, mutably. The match is exhaustive so a
/// new trust-ir instruction is a build failure here, never a silent omission.
fn inst_types_mut(inst: &mut Inst, mut visit: impl FnMut(&mut Ty)) {
    match inst {
        Inst::Drop { ty, .. }
        | Inst::DropInvoke { ty, .. }
        | Inst::BinOp { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. }
        | Inst::TensorContract { ty, .. }
        | Inst::TensorReduce { ty, .. }
        | Inst::TensorView { ty, .. }
        | Inst::TensorGather { ty, .. }
        | Inst::TensorScatter { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => visit(ty),
        Inst::TensorMap { ty, body, .. } => {
            visit(ty);
            for node in body {
                *node = node
                    .try_map_level(&mut |ty| {
                        let mut mapped = ty.clone();
                        visit(&mut mapped);
                        Ok::<_, std::convert::Infallible>(mapped)
                    })
                    .unwrap_or_else(|never| match never {});
            }
        }
        Inst::Cast { src_ty, dst_ty, .. } => {
            visit(src_ty);
            visit(dst_ty);
        }
        // trust-ir v74: the pointer type and the pointee the validity fact is
        // about. The fact itself spells no type.
        Inst::BoxDeref {
            ptr_ty, pointee, ..
        } => {
            visit(ptr_ty);
            visit(pointee.ty_mut());
        }
        Inst::GEP { pointee_ty, .. } => visit(pointee_ty),
        Inst::PtrData { ptr_ty, .. } => visit(ptr_ty),
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => {
            visit(ptr_ty);
            visit(metadata_ty);
        }
        Inst::OpenFrame { def } => {
            for slot in &mut def.slots {
                visit(&mut slot.ty);
            }
        }
        Inst::DialectOp(op) => {
            for ty in &mut op.result_tys {
                visit(ty);
            }
            for attr in &mut op.attrs {
                if let AttrValue::Ty(ty) = &mut attr.value {
                    visit(ty);
                }
            }
        }
        // This stores a ClosureTyId, not an inline Ty. Capture types live
        // in module.closure_types and apparent signatures in func_types;
        // substitute_module_types visits both tables without changing IDs
        // or the constructor's ordered SSA captures.
        Inst::MakeClosure { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::Return { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::AssertInvoke { .. }
        | Inst::Unreachable
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::BindSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => {}
    }
}

/// Substitute carriers at every position `Module::visit_types` inventories.
/// Returns the indices of functions whose body or signature changed.
fn substitute_module_types(
    module: &mut Module,
    carriers: &HashMap<DialectTy, Ty>,
) -> BTreeSet<usize> {
    for ty in &mut module.types {
        substitute_ty(ty, carriers);
    }
    let mut changed_signatures = BTreeSet::new();
    for (index, signature) in module.func_types.iter_mut().enumerate() {
        let mut changed = false;
        for ty in signature
            .params
            .iter_mut()
            .chain(signature.returns.iter_mut())
        {
            changed |= substitute_ty(ty, carriers);
        }
        if changed {
            changed_signatures.insert(index);
        }
    }
    for definition in &mut module.structs {
        for field in &mut definition.fields {
            substitute_ty(&mut field.ty, carriers);
        }
    }
    for definition in &mut module.records {
        for field in &mut definition.fields {
            substitute_ty(&mut field.ty, carriers);
        }
    }
    for definition in &mut module.enums {
        for variant in &mut definition.variants {
            for ty in &mut variant.fields {
                substitute_ty(ty, carriers);
            }
        }
    }
    for closure in &mut module.closure_types {
        for ty in &mut closure.captures {
            substitute_ty(ty, carriers);
        }
    }
    for global in &mut module.globals {
        substitute_ty(&mut global.ty, carriers);
    }
    let mut touched = BTreeSet::new();
    for (index, function) in module.functions.iter_mut().enumerate() {
        let mut changed = changed_signatures.contains(&(function.ty.index() as usize));
        for block in &mut function.blocks {
            for (_, ty) in &mut block.params {
                changed |= substitute_ty(ty, carriers);
            }
            for node in &mut block.body {
                inst_types_mut(&mut node.inst, |ty| {
                    changed |= substitute_ty(ty, carriers);
                });
            }
        }
        if changed {
            touched.insert(index);
        }
    }
    touched
}

// ---------------------------------------------------------------------------
// Replay verification
// ---------------------------------------------------------------------------

/// A report or legalized module that does not match its replay.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ReceiptError {
    #[error("[TCG-DIALECT-RECEIPT] replaying the legalization refused the source: {0}")]
    ReplayRefused(DialectPipelineError),
    #[error(
        "[TCG-DIALECT-RECEIPT] the source carries no dialect construct, so no report can describe it"
    )]
    NoDialectConstructs,
    #[error(
        "[TCG-DIALECT-RECEIPT] report field `{field}` is {found:?}; the replay gives {expected:?}"
    )]
    ReportField {
        field: &'static str,
        expected: String,
        found: String,
    },
    #[error("[TCG-DIALECT-RECEIPT] the report has {found} receipts; the replay gives {expected}")]
    ReceiptCount { expected: usize, found: usize },
    #[error(
        "[TCG-DIALECT-RECEIPT] receipt {index} field `{field}` is {found:?}; the replay gives {expected:?}"
    )]
    ReceiptField {
        index: usize,
        field: &'static str,
        expected: String,
        found: String,
    },
    #[error("[TCG-DIALECT-RECEIPT] the legalized module differs from the replay's")]
    ModuleMismatch,
}

/// Replay `original`'s legalization under `registry` and `options`, and check
/// that `report` and `legalized` are exactly what it produces.
pub fn verify_legalization(
    original: &Module,
    legalized: &Module,
    report: &DialectLegalizationReport,
    registry: &DialectLegalizationRegistry,
    options: LegalizationOptions,
) -> Result<(), ReceiptError> {
    let replay =
        legalize_module(original, registry, options).map_err(ReceiptError::ReplayRefused)?;
    let Some(expected) = replay.report else {
        return Err(ReceiptError::NoDialectConstructs);
    };
    let field = |field: &'static str, expected: &dyn fmt::Debug, found: &dyn fmt::Debug| {
        ReceiptError::ReportField {
            field,
            expected: format!("{expected:?}"),
            found: format!("{found:?}"),
        }
    };
    if report.registry_digest != expected.registry_digest {
        return Err(field(
            "registry_digest",
            &expected.registry_digest,
            &report.registry_digest,
        ));
    }
    if report.target != expected.target {
        return Err(field("target", &expected.target, &report.target));
    }
    if report.proof_required != expected.proof_required {
        return Err(field(
            "proof_required",
            &expected.proof_required,
            &report.proof_required,
        ));
    }
    if report.provenance_invalidated != expected.provenance_invalidated {
        return Err(field(
            "provenance_invalidated",
            &expected.provenance_invalidated,
            &report.provenance_invalidated,
        ));
    }
    if report.receipts.len() != expected.receipts.len() {
        return Err(ReceiptError::ReceiptCount {
            expected: expected.receipts.len(),
            found: report.receipts.len(),
        });
    }
    for (index, (found, expected)) in report.receipts.iter().zip(&expected.receipts).enumerate() {
        let mismatch = |field: &'static str, e: &dyn fmt::Debug, f: &dyn fmt::Debug| {
            ReceiptError::ReceiptField {
                index,
                field,
                expected: format!("{e:?}"),
                found: format!("{f:?}"),
            }
        };
        if found.dialect != expected.dialect {
            return Err(mismatch("dialect", &expected.dialect, &found.dialect));
        }
        if found.dialect_version != expected.dialect_version {
            return Err(mismatch(
                "dialect_version",
                &expected.dialect_version,
                &found.dialect_version,
            ));
        }
        if found.owner != expected.owner {
            return Err(mismatch("owner", &expected.owner, &found.owner));
        }
        if found.subject != expected.subject {
            return Err(mismatch("subject", &expected.subject, &found.subject));
        }
        if found.rule != expected.rule {
            return Err(mismatch("rule", &expected.rule, &found.rule));
        }
        if found.evidence != expected.evidence {
            return Err(mismatch("evidence", &expected.evidence, &found.evidence));
        }
        if found.site != expected.site {
            return Err(mismatch("site", &expected.site, &found.site));
        }
        if found.input_digest != expected.input_digest {
            return Err(mismatch(
                "input_digest",
                &expected.input_digest,
                &found.input_digest,
            ));
        }
        if found.output_digest != expected.output_digest {
            return Err(mismatch(
                "output_digest",
                &expected.output_digest,
                &found.output_digest,
            ));
        }
    }
    if legalized != replay.module.as_ref() {
        return Err(ReceiptError::ModuleMismatch);
    }
    Ok(())
}

#[cfg(test)]
#[path = "dialect_legalization_tests.rs"]
mod tests;
