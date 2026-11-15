//! The consumer half of the trust-ir v41 CODEGEN LICENSE (`Function.body_gate`).
//!
//! trust-ir 6a7fe352 (binary v41) carries, per function, a three-valued
//! machine-checkable license that says whether a backend may emit code for the
//! body. trust-ir defines the values AND, since WS1.5, the evidence an
//! evidence-bound authority must carry; this module is the backend DECISION,
//! spelled once so every lowering entry (compatibility, prepared, strict,
//! validated-strict, single-function, JIT service, CLI, wasm) reaches the same
//! verdict for the same function under the same policy.
//!
//! | `body_gate`                    | meaning (trust-ir `BodyGate` docs)            | verdict here                                   |
//! |--------------------------------|-----------------------------------------------|------------------------------------------------|
//! | `None`                         | NO licensing claim (pre-v41 grandfather state) | REFUSED by default ([`UnlicensedBodyPolicy::Refuse`]); permitted only under a named, disclosed [`UnlicensedPermitException`] or an explicit test policy |
//! | `Some(Ungated)`                | AFFIRMATIVELY no gate was applied              | ALWAYS refuse — no policy can permit it        |
//! | `Some(Gated { authority, .. })` | passed the gate owned by `authority`          | permit iff trust-ir's license layer finds no refutation or missing evidence for the body AND `authority` is RECOGNIZED; else refuse |
//!
//! # `Gated` is bound to evidence, not to a string (roadmap WS7.5(b), F-006)
//!
//! Recognition alone never licenses a body. Before the recognized set is
//! consulted, trust-ir's OWN license layer
//! ([`trust_ir_build::codegen_license_errors`]) runs over the module, and its
//! findings for the function are refusals by name:
//!
//! * [`AdapterError::GatedWithoutEvidence`] — the authority is EVIDENCE-BOUND
//!   (`trust_ir_build::EVIDENCE_BOUND_GATE_AUTHORITIES`: `clean-kernel-tv`)
//!   and the module does not carry what it names: exactly one
//!   `TranslationValidation` obligation scoped to the function, `Certified`,
//!   whose `CleanCic` certificate uses trust-ir's checked backend-TV or
//!   source-bound defined-call-family anchor and was kernel-REPLAYED against
//!   the current body in this process (so a body
//!   edited after the certificate was minted loses its license). Two TV rows
//!   scoped to one body are ambiguous and refused the same way.
//! * [`AdapterError::GatedFunctionRefuted`] — whatever the authority, a
//!   `Failed` `TranslationValidation`, `Precondition` or `Postcondition` row
//!   scoped to the function revokes its license.
//!
//! The format owns that rule; this backend owns only the recognized set and
//! the claim-less policy. A finding the pinned trust-ir adds to its license
//! layer that this module does not yet name is refused (fail closed) as
//! [`AdapterError::TrustIrAdmissionRefused`], never ignored.
//!
//! The license layer is `codegen_license_errors`, not the composed admission
//! lane `validate_module_for_codegen_with`, because every module entry of this
//! crate already runs the full structural pass once
//! (`validate_codegen_prerequisites`); the license layer re-runs only the
//! certified-evidence replay, and only when some body is `Gated`. Recognition
//! is byte-exact membership in [`CodegenLicensePolicy::recognized_authorities`]
//! — the same rule as trust-ir's `CodegenAdmission::with_recognized`
//! (`UnrecognizedGateAuthority`), and the same refusal name.
//!
//! # `None` is refused by default (decision gate DG-73)
//!
//! `None` is a grandfather state, not a wildcard. Until WS7.5 it was
//! PERMITTED by default, which let any producer launder an unverified body by
//! dropping the field. The default is now [`UnlicensedBodyPolicy::Refuse`],
//! matching trust-ir's own codegen admission (`CodegenAdmission::pinned`).
//! A legacy pre-v41 corpus is compiled only through an explicit Permit:
//!
//! * in production code, ONLY through
//!   [`CodegenLicensePolicy::with_unlicensed_permit_exception`], whose
//!   [`UnlicensedPermitException`] names why; the set of production sites is
//!   pinned by a source census (`the_unlicensed_permit_exceptions_are_named_and_counted`
//!   below), so a new silent Permit fails a test by name;
//! * in tests, through `with_unlicensed(UnlicensedBodyPolicy::Permit)` — the
//!   hand-built fixtures of this workspace carry `body_gate: None` and are
//!   compiled under that stated policy, never under a silent default.
//!
//! `Gated.evidence` (trust-ir binary v61, `GateEvidence`) is not this
//! layer's: an evidence-bound authority (`clean-kernel-tv`) is held to its
//! evidence by the admission's license-EVIDENCE layer on every entry, beside
//! the kernel-certificate rule — an evidence-free license is
//! [`AdapterError::UnevidencedGate`], a present evidence that does not hold
//! is trust-ir's `GatedEvidenceMismatch` (see
//! `crate::adapter::validate_codegen_prerequisites`).
//!
//! A DECLARATION (no body) is never a codegen subject, so its gate is not
//! consulted — exactly trust-ir-build's own codegen-intent rule.
//!
//! The policy also carries trust-ir's one other opt-in codegen refusal,
//! [`CodegenLicensePolicy::refuse_unbacked_claims_on_checks`] (WS1.8 rule (f):
//! a safety claim on a runtime check is not a license to elide it unless a
//! `ProofRef` binds it to an obligation about that check). The rule is
//! trust-ir's (`trust_ir_build::validate::unbacked_claim_on_check_errors`);
//! this policy only decides whether a deployment applies it, and
//! [`CodegenLicensePolicy::enforce_module`] applies it at every entry. It is
//! off by default, as in trust-ir's `CodegenAdmission`.
//!
//! The default recognized set names the one authority a producer stamps today:
//! [`CLEAN_KERNEL_TV_AUTHORITY`], the Clean compiler's in-process kernel
//! translation-validation gate (`clean-compiler/src/emit_trust_ir_tv.rs`,
//! `CLEAN_KERNEL_TV_AUTHORITY`). `trust-direct-lane-structural` (the Rust
//! producer's structural stamp) is NOT recognized by default (decision gate
//! DG-22: structural-only is incomplete); a deployment that accepts it names
//! it through `--recognize-authority` /
//! [`CodegenLicensePolicy::with_recognized_authority`].
//!
//! The policy also carries, optionally, the IMPORT AUTHENTICATION a linked
//! compile established ([`CodegenLicensePolicy::with_authenticated_imports`],
//! roadmap WS7.9). It is not a license and grants no codegen authority; it
//! rides here because the license is the one per-compile admission policy
//! every license-aware lowering entry already receives, so the shared floor
//! can admit exactly the cross-crate inheritance certificates the linked walk
//! authenticated (see [`crate::linked_imports`]). [`CodegenLicensePolicy::enforce_module`]
//! binds it to the one module it was made for.

use std::collections::BTreeSet;
use std::sync::Arc;

use trust_ir::{BodyGate, FuncId, Function, Module};
use trust_ir_build::ValidationError;

use crate::adapter::AdapterError;
use crate::linked_imports::AuthenticatedImportSet;

/// The gate authority the Clean compiler stamps on a body its in-process
/// CleanCic kernel re-checked (`Some(BodyGate::Gated { authority })`).
///
/// Mirrors `clean_compiler::emit_trust_ir_tv::CLEAN_KERNEL_TV_AUTHORITY`
/// (verified at clean `76532a39`): the literal is `"clean-kernel-tv"`. It is
/// an EVIDENCE-BOUND authority in trust-ir
/// (`trust_ir_build::EVIDENCE_BOUND_GATE_AUTHORITIES`): recognizing it admits
/// a body only together with its kernel-replayed certificate.
pub const CLEAN_KERNEL_TV_AUTHORITY: &str = "clean-kernel-tv";

/// What to do with a body that carries NO licensing claim (`body_gate: None`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum UnlicensedBodyPolicy {
    /// Permit the grandfathered, claim-less body. Never the default: a
    /// production site reaches it only through a named
    /// [`UnlicensedPermitException`].
    Permit,
    /// Refuse a claim-less body. The default (DG-73), and trust-ir's own
    /// codegen-admission default.
    #[default]
    Refuse,
}

impl UnlicensedBodyPolicy {
    /// Stable token for diagnostics and identity strings.
    #[must_use]
    pub const fn token(self) -> &'static str {
        match self {
            UnlicensedBodyPolicy::Permit => "permit",
            UnlicensedBodyPolicy::Refuse => "refuse",
        }
    }
}

/// The named, counted exceptions under which PRODUCTION code of this
/// workspace permits claim-less (`body_gate: None`) bodies. Each is reached
/// only through [`CodegenLicensePolicy::with_unlicensed_permit_exception`],
/// and the production sites that name each variant are pinned by a source
/// census test, so a new Permit cannot appear silently.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnlicensedPermitException {
    /// An explicit, operator-spelled `--permit-unlicensed` (the `trust-cg`
    /// CLI and the `ty_replay_jit_probe` tool): a legacy pre-v41 corpus
    /// (every such blob decodes to `None`) compiled on the operator's word.
    /// Each prints a disclosure line naming the unlicensed bodies it
    /// compiled.
    LegacyCorpusFlag,
    /// Closed-JIT Core ADMISSION lowers under a floor that defers the `None`
    /// decision to the planner: a `CoreAdmittedModule` produces code only
    /// through `Compiler::plan_core_module_for_jit_compilation`, whose
    /// preflight re-decides the license under the compiler's own policy
    /// (default: refuse). Admission is not a codegen verdict.
    CoreAdmissionFloor,
    /// trust-cg's own in-process MIR lane (`rustc-codegen-trust-cg`) builds
    /// its trust-ir in memory and never stamps `body_gate`. Until it stamps
    /// its own disclosed license (roadmap WS7.5 DECIDE 1), it compiles under
    /// this named exception — never under a silent default. An in-process
    /// module has no legacy excuse, so this exception is the lane's debt, not
    /// a grandfathering.
    InProcessMirLane,
    /// `trust-cg-jit-matrix` JIT-compiles solver kernels (the BCP and
    /// parent-loop `SolverKernelProvider`s) it builds IN MEMORY from its own
    /// trust-ir templates, which carry no `body_gate`. The same debt as
    /// [`Self::InProcessMirLane`]: an in-process producer until it stamps a
    /// license of its own.
    InProcessJitKernel,
    /// `trust-cg-llvm-import` translates LLVM IR — a language with no
    /// licensing concept — into trust-ir and compiles it for external
    /// correctness corpora; nothing in its input could carry a license.
    LlvmImport,
    /// `trust-cg-fuzz` compiles GENERATED modules to exercise the lowering
    /// differentially; refusing them all at the license would make the
    /// harness vacuous. Test infrastructure, not a codegen service.
    FuzzHarness,
    /// A lane's OWN runtime helper bodies — the wasm32 lane's `fmod` and
    /// `divmod128` — which the lane builds in memory from fixed templates
    /// and lowers beside the producer's functions. They are never producer
    /// input and carry no `body_gate`; every producer body of the same
    /// module is still decided under the caller's policy.
    LaneRuntimeHelper,
    /// `trust-cg-jit-matrix`'s bench tools (`compile_corpus`,
    /// `tier_up_bench`) replay claim-less CORPORA — rustc-bridge module dumps,
    /// the repository's `scripts/fuzz` kernels — to measure compile cost and
    /// output identity against a baseline build. Refusing them at the license
    /// would make every measurement, and every build-to-build comparison of
    /// verdicts, vacuously "identical". Bench tooling, never a codegen service
    /// or a publication authority.
    BenchCorpus,
}

impl UnlicensedPermitException {
    /// Every exception, in declaration order.
    pub const ALL: [UnlicensedPermitException; 8] = [
        UnlicensedPermitException::LegacyCorpusFlag,
        UnlicensedPermitException::CoreAdmissionFloor,
        UnlicensedPermitException::InProcessMirLane,
        UnlicensedPermitException::InProcessJitKernel,
        UnlicensedPermitException::LlvmImport,
        UnlicensedPermitException::FuzzHarness,
        UnlicensedPermitException::LaneRuntimeHelper,
        UnlicensedPermitException::BenchCorpus,
    ];

    /// Stable token for diagnostics and identity strings.
    #[must_use]
    pub const fn token(self) -> &'static str {
        match self {
            UnlicensedPermitException::LegacyCorpusFlag => "legacy-corpus-flag",
            UnlicensedPermitException::CoreAdmissionFloor => "core-admission-floor",
            UnlicensedPermitException::InProcessMirLane => "in-process-mir-lane",
            UnlicensedPermitException::InProcessJitKernel => "in-process-jit-kernel",
            UnlicensedPermitException::LlvmImport => "llvm-import",
            UnlicensedPermitException::FuzzHarness => "fuzz-harness",
            UnlicensedPermitException::LaneRuntimeHelper => "lane-runtime-helper",
            UnlicensedPermitException::BenchCorpus => "bench-corpus",
        }
    }
}

/// The backend's codegen-license policy: which gate authorities it trusts,
/// whether a claim-less body may be compiled, and whether a bare safety claim
/// on a runtime check is refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodegenLicensePolicy {
    /// Gate authorities whose `Gated { authority }` license is honored — for
    /// an evidence-bound authority, only together with its evidence. Anything
    /// else is refused. The empty string is never recognized.
    pub recognized_authorities: BTreeSet<String>,
    /// Verdict for `body_gate: None`.
    pub unlicensed: UnlicensedBodyPolicy,
    /// Refuse a module in which an `Assert` / `CondBr` carries a safety-class
    /// claim (`NoOverflow`, `NoWrap`, `DivNonZero`, `ShiftInRange`, `InBounds`)
    /// that no `ProofRef` binds to a kind-matched obligation sited on that very
    /// node: trust-ir's WS1.8 rule (f), stated once in trust-ir
    /// (`trust_ir_build::validate::unbacked_claim_on_check_errors`) and applied
    /// here by [`Self::enforce_module`], which every entry reaches. Default
    /// `false`, as trust-ir's own codegen admission: the shape is what both
    /// producers emit beside every `Pending` arithmetic obligation until the
    /// producer fix (WS5). A deployment whose producers never emit it opts in.
    pub refuse_unbacked_claims_on_checks: bool,
    /// The import authentication of a linked compile (WS7.9), or `None`
    /// (every cross-crate inheritance refused). Private: only
    /// [`Self::with_authenticated_imports`] sets it, from a set only
    /// [`crate::authenticate_linked_imports`] mints.
    authenticated_imports: Option<Arc<AuthenticatedImportSet>>,
}

impl Default for CodegenLicensePolicy {
    /// Recognizes [`CLEAN_KERNEL_TV_AUTHORITY`] (evidence-bound), REFUSES
    /// claim-less bodies (DG-73), and does not refuse unbacked claims on
    /// checks.
    fn default() -> Self {
        Self {
            recognized_authorities: BTreeSet::from([CLEAN_KERNEL_TV_AUTHORITY.to_string()]),
            unlicensed: UnlicensedBodyPolicy::Refuse,
            refuse_unbacked_claims_on_checks: false,
            authenticated_imports: None,
        }
    }
}

impl CodegenLicensePolicy {
    /// A policy that recognizes NO authority and refuses claim-less bodies:
    /// every body is refused until an authority is added. Useful as a base
    /// for an explicit list.
    #[must_use]
    pub fn recognizing_nothing() -> Self {
        Self {
            recognized_authorities: BTreeSet::new(),
            unlicensed: UnlicensedBodyPolicy::Refuse,
            refuse_unbacked_claims_on_checks: false,
            authenticated_imports: None,
        }
    }

    /// Add `authority` to the recognized set. An empty name is ignored: the
    /// empty authority is never recognized, so it cannot be added.
    #[must_use]
    pub fn with_recognized_authority(mut self, authority: impl Into<String>) -> Self {
        let authority = authority.into();
        if !authority.is_empty() {
            self.recognized_authorities.insert(authority);
        }
        self
    }

    /// Set the verdict for claim-less (`body_gate: None`) bodies.
    ///
    /// Production code of this workspace never passes
    /// [`UnlicensedBodyPolicy::Permit`] here: it names its reason through
    /// [`Self::with_unlicensed_permit_exception`] (source census).
    #[must_use]
    pub fn with_unlicensed(mut self, unlicensed: UnlicensedBodyPolicy) -> Self {
        self.unlicensed = unlicensed;
        self
    }

    /// Carry the import authentication a linked compile established
    /// (WS7.9). The floor then admits exactly the cross-crate inheritance
    /// certificates `imports` authenticated, and [`Self::enforce_module`]
    /// refuses any module other than the root `imports` was made for.
    #[must_use]
    pub fn with_authenticated_imports(mut self, imports: AuthenticatedImportSet) -> Self {
        self.authenticated_imports = Some(Arc::new(imports));
        self
    }

    /// The import authentication this policy carries, if any.
    #[must_use]
    pub fn authenticated_imports(&self) -> Option<&AuthenticatedImportSet> {
        self.authenticated_imports.as_deref()
    }

    /// The policy to hand an adapter entry that lowers `derived`, the
    /// backend's own rewrite of the caller's module `source` (dialect
    /// legalization). Without an import authentication, or when `derived`
    /// IS `source`, this is the policy unchanged; otherwise the
    /// authentication moves onto `derived`
    /// ([`AuthenticatedImportSet::rebind_to_backend_rewrite`]) or the compile
    /// is refused. Without this, [`Self::enforce_module`] inside the adapter
    /// refuses every linked module whose dialect ops were legalized.
    pub fn for_backend_rewrite(
        &self,
        source: &Module,
        derived: &Module,
    ) -> Result<Self, AdapterError> {
        match self.authenticated_imports() {
            Some(imports) if !std::ptr::eq(source, derived) => Ok(Self {
                authenticated_imports: Some(Arc::new(
                    imports.rebind_to_backend_rewrite(source, derived)?,
                )),
                ..self.clone()
            }),
            _ => Ok(self.clone()),
        }
    }

    /// Set whether a bare safety claim on a runtime check is refused
    /// ([`Self::refuse_unbacked_claims_on_checks`]).
    #[must_use]
    pub fn with_refuse_unbacked_claims_on_checks(mut self, refuse: bool) -> Self {
        self.refuse_unbacked_claims_on_checks = refuse;
        self
    }

    /// Permit claim-less bodies under a named exception — the only
    /// production spelling of a Permit. The exception carries no runtime
    /// behavior: it is the NAME a reviewer and the source census
    /// (`the_unlicensed_permit_exceptions_are_named_and_counted`) read at the
    /// call site, which is what makes every production Permit a counted,
    /// named decision rather than a silent default.
    #[must_use]
    pub fn with_unlicensed_permit_exception(self, _exception: UnlicensedPermitException) -> Self {
        self.with_unlicensed(UnlicensedBodyPolicy::Permit)
    }

    /// Whether a `Gated { authority }` license from `authority` is honored
    /// by recognition. The empty authority is never recognized. Recognition
    /// is necessary, never sufficient: see [`Self::verdict`].
    #[must_use]
    pub fn recognizes(&self, authority: &str) -> bool {
        !authority.is_empty() && self.recognized_authorities.contains(authority)
    }

    /// The verdict for the function(s) of `module` with id `id`: every
    /// bodied function carrying that id must be licensed. A declaration
    /// (no body) is never a codegen subject and is always `Ok`. An id no
    /// function of `module` carries is refused (fail closed): the verdict is
    /// about a body this module holds, never about an absent one.
    ///
    /// The evidence rule needs the MODULE (obligations and certificates live
    /// there, not on the function), which is why this takes both.
    pub fn verdict(&self, module: &Module, id: FuncId) -> Result<(), AdapterError> {
        if !module.functions.iter().any(|function| function.id == id) {
            return Err(AdapterError::InvalidTrustIr(format!(
                "codegen license: module `{}` has no function FuncId({}) to license",
                module.name,
                id.index()
            )));
        }
        let findings = FormatLicenseFindings::of(module)?;
        module
            .functions
            .iter()
            .filter(|function| function.id == id)
            .try_for_each(|function| self.function_verdict(function, &findings))
    }

    /// Apply the license to every function of `module`, in module order,
    /// then, under [`Self::refuse_unbacked_claims_on_checks`], trust-ir's
    /// unbacked-claim rule to the module, returning the first refusal. The
    /// claim rule is trust-ir's own finding, reported in its own words
    /// ([`AdapterError::TrustIrAdmissionRefused`]). When the policy carries
    /// an import authentication (WS7.9), `module` must first be the exact
    /// root it was made for ([`AuthenticatedImportSet::bind_root`]).
    pub fn enforce_module(&self, module: &Module) -> Result<(), AdapterError> {
        if let Some(imports) = self.authenticated_imports() {
            imports.bind_root(module)?;
        }
        let findings = FormatLicenseFindings::of(module)?;
        module
            .functions
            .iter()
            .try_for_each(|function| self.function_verdict(function, &findings))?;
        self.unbacked_claim_refusal(module)
    }

    /// Under [`Self::refuse_unbacked_claims_on_checks`], trust-ir's
    /// unbacked-claim rule over the whole module (its first finding);
    /// `Ok` when the knob is off.
    fn unbacked_claim_refusal(&self, module: &Module) -> Result<(), AdapterError> {
        if self.refuse_unbacked_claims_on_checks
            && let Some(error) = trust_ir_build::validate::unbacked_claim_on_check_errors(module)
                .into_iter()
                .next()
        {
            return Err(AdapterError::TrustIrAdmissionRefused {
                error: error.to_string(),
            });
        }
        Ok(())
    }

    /// Apply the license to every function of `module` and RECORD each
    /// refusal, in module order, instead of stopping at the first (the
    /// translation census). trust-ir's license layer runs once; a finding it
    /// attributes to no one function is still the `Err` of the whole module,
    /// exactly as [`Self::enforce_module`] returns it; so is trust-ir's
    /// module-level unbacked-claim rule under
    /// [`Self::refuse_unbacked_claims_on_checks`], which no census lane may
    /// skip (the adapter's census route reaches this, not `enforce_module`).
    pub fn census_module(
        &self,
        module: &Module,
    ) -> Result<Vec<(FuncId, AdapterError)>, AdapterError> {
        if let Some(imports) = self.authenticated_imports() {
            imports.bind_root(module)?;
        }
        let findings = FormatLicenseFindings::of(module)?;
        self.unbacked_claim_refusal(module)?;
        Ok(module
            .functions
            .iter()
            .filter_map(|function| {
                self.function_verdict(function, &findings)
                    .err()
                    .map(|error| (function.id, error))
            })
            .collect())
    }

    /// The bodied functions of `module` this policy admits only because it
    /// PERMITS claim-less bodies — what a disclosure line names. Empty under
    /// [`UnlicensedBodyPolicy::Refuse`].
    #[must_use]
    pub fn unlicensed_bodies_permitted<'m>(&self, module: &'m Module) -> Vec<&'m str> {
        if self.unlicensed == UnlicensedBodyPolicy::Refuse {
            return Vec::new();
        }
        module
            .functions
            .iter()
            .filter(|function| !function.is_declaration() && function.body_gate.is_none())
            .map(|function| function.name.as_str())
            .collect()
    }

    /// Whether this policy admits a claim-less (`body_gate: None`) body: the
    /// one verdict on [`Self::unlicensed`], read both by this backend's
    /// license ([`Self::enforce_module`]) and by trust-ir's codegen admission
    /// ([`Self::trust_ir_unlicensed_policy`]), so the two cannot disagree.
    #[must_use]
    pub fn permits_unlicensed(&self) -> bool {
        match self.unlicensed {
            UnlicensedBodyPolicy::Permit => true,
            UnlicensedBodyPolicy::Refuse => false,
        }
    }

    /// This policy's claim-less verdict ([`Self::permits_unlicensed`]) in
    /// trust-ir's admission type, for an entry that runs trust-ir's composed
    /// codegen admission under the caller's license (the WS7.3 ingestion
    /// admission, [`crate::admit_module`]): trust-ir then raises
    /// `UnlicensedBodyForCodegen` for exactly the bodies
    /// [`Self::enforce_module`] refuses. It translates; it decides and sets
    /// nothing, so a Permit reaches it only through a policy that already
    /// permits ([`Self::with_unlicensed_permit_exception`] in production).
    #[must_use]
    pub fn trust_ir_unlicensed_policy(&self) -> trust_ir_build::UnlicensedBodyPolicy {
        if self.permits_unlicensed() {
            trust_ir_build::UnlicensedBodyPolicy::Permit
        } else {
            trust_ir_build::UnlicensedBodyPolicy::Refuse
        }
    }

    /// One function, against the module's trust-ir license findings.
    fn function_verdict(
        &self,
        function: &Function,
        findings: &FormatLicenseFindings,
    ) -> Result<(), AdapterError> {
        if function.is_declaration() {
            return Ok(());
        }
        // Pin-move floor for `BodyGate` (WS7.17): this match has no wildcard
        // arm and the `Gated { authority, evidence }` pattern no `..`, so a
        // variant or field a later trust-ir pin adds fails to compile here
        // until it is classified. Keep it that way.
        match &function.body_gate {
            None if self.permits_unlicensed() => Ok(()),
            None => Err(AdapterError::UnlicensedBody {
                function: function.name.clone(),
            }),
            Some(BodyGate::Ungated) => Err(AdapterError::UngatedBody {
                function: function.name.clone(),
            }),
            Some(BodyGate::Gated {
                authority,
                // CONSUMED by the license-EVIDENCE layer at admission, beside
                // trust-ir's `GatedWithoutEvidence` and on every entry that
                // runs it (trust-ir v61): absent for an evidence-bound
                // authority, `AdapterError::UnevidencedGate`
                // (`refuse_unevidenced_gates`); present, trust-ir's
                // `GatedEvidenceMismatch`. The field never stands in for
                // trust-ir's license findings or for recognition below.
                evidence: _,
            }) => {
                // trust-ir's order (`license_errors_against`): revocation and
                // evidence first, recognition after — recognition never
                // stands in for the evidence.
                findings.refusal_for(function)?;
                if self.recognizes(authority) {
                    Ok(())
                } else {
                    Err(AdapterError::UnrecognizedGateAuthority {
                        function: function.name.clone(),
                        authority: authority.clone(),
                    })
                }
            }
        }
    }

    /// Canonical, order-independent text identity of this policy, for
    /// diagnostics and identity strings: `unlicensed=<permit|refuse>;
    /// authorities=<a>,<b>,...` (sorted, so equal policies print equal),
    /// followed by `;linked=<root digest>` when the policy carries an import
    /// authentication (WS7.9) and then `;unbacked_claims=refuse` only when
    /// that knob is set, so every policy without either keeps its earlier
    /// identity byte for byte.
    #[must_use]
    pub fn canonical_identity(&self) -> String {
        let authorities = self
            .recognized_authorities
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join(",");
        let linked = self
            .authenticated_imports()
            .map(|imports| format!(";linked={}", imports.root_digest()))
            .unwrap_or_default();
        let mut identity = format!(
            "unlicensed={};authorities={authorities}{linked}",
            self.unlicensed.token()
        );
        if self.refuse_unbacked_claims_on_checks {
            identity.push_str(";unbacked_claims=refuse");
        }
        identity
    }
}

/// trust-ir's license-layer findings for one module (evidence table and
/// revocation), computed once per verdict.
struct FormatLicenseFindings {
    /// `(function index, refusal)`, in trust-ir's order.
    refusals: Vec<(u32, AdapterError)>,
}

impl FormatLicenseFindings {
    /// Run trust-ir's license layer over `module` iff some bodied function
    /// is `Gated` (the only shape it has findings for beyond the claim-less
    /// and `Ungated` partition this module decides itself). A finding this
    /// module does not attribute to one function refuses the whole module.
    fn of(module: &Module) -> Result<Self, AdapterError> {
        let any_gated = module.functions.iter().any(|function| {
            !function.is_declaration() && matches!(function.body_gate, Some(BodyGate::Gated { .. }))
        });
        if !any_gated {
            return Ok(Self {
                refusals: Vec::new(),
            });
        }
        // trust-ir states each finding against a `FuncId`, and this backend
        // attributes it the same way. Two functions sharing an id would let
        // one body's finding (or its absence) stand for the other's, so the
        // attribution is only sound over unique ids: refuse the module rather
        // than rely on how a by-id lookup resolves the tie (fail closed).
        let mut seen = BTreeSet::new();
        if let Some(duplicate) = module
            .functions
            .iter()
            .find(|function| !seen.insert(function.id))
        {
            return Err(AdapterError::InvalidTrustIr(format!(
                "codegen license: module `{}` has ambiguous FuncId({}) (`{}` and another \
                 function share it); a license finding is attributed by id, so no body with \
                 this id can be licensed",
                module.name,
                duplicate.id.index(),
                duplicate.name
            )));
        }
        let mut refusals = Vec::new();
        for error in trust_ir_build::codegen_license_errors(module) {
            let Some(refusal) = license_finding_refusal(module, &error) else {
                continue;
            };
            match license_finding_function(&error) {
                Some(function) => refusals.push((function, refusal)),
                None => return Err(refusal),
            }
        }
        Ok(Self { refusals })
    }

    /// The first finding about `function`, as its refusal.
    fn refusal_for(&self, function: &Function) -> Result<(), AdapterError> {
        match self
            .refusals
            .iter()
            .find(|(index, _)| *index == function.id.index())
        {
            Some((_, refusal)) => Err(refusal.clone()),
            None => Ok(()),
        }
    }
}

/// The function a trust-ir license finding is about, if it names one.
fn license_finding_function(error: &ValidationError) -> Option<u32> {
    match error {
        ValidationError::GatedWithoutEvidence { function, .. }
        | ValidationError::GatedFunctionRefuted { function, .. }
        | ValidationError::UnrecognizedGateAuthority { function, .. }
        | ValidationError::UngatedBodyForCodegen { function, .. }
        | ValidationError::UnlicensedBodyForCodegen { function, .. } => Some(*function),
        _ => None,
    }
}

/// The name of the function with index `function` in `module`, for a
/// refusal message (`FuncId(n)` if the index names none).
fn function_name(module: &Module, function: u32) -> String {
    module
        .functions
        .iter()
        .find(|candidate| candidate.id.index() == function)
        .map_or_else(|| format!("FuncId({function})"), |f| f.name.clone())
}

/// Whether `error` is a trust-ir license finding whose verdict belongs to
/// [`CodegenLicensePolicy`]: an affirmatively `Ungated` body, a claim-less
/// body, or a gate authority that the policy's recognized set decides. Every
/// lowering entry decides these through [`CodegenLicensePolicy::enforce_module`]
/// (or its census), with the named refusals `UngatedBody`, `UnlicensedBody`
/// and `UnrecognizedGateAuthority`. trust-ir's spelling of them is never this
/// backend's refusal, either here ([`license_finding_refusal`]) or in the
/// codegen prerequisites' panic-delivery verdict (decision LD-W7-8).
pub(crate) fn decided_by_license_policy(error: &ValidationError) -> bool {
    matches!(
        error,
        ValidationError::UngatedBodyForCodegen { .. }
            | ValidationError::UnlicensedBodyForCodegen { .. }
            | ValidationError::UnrecognizedGateAuthority { .. }
    )
}

/// Map ONE finding of trust-ir's codegen LICENSE layer to this backend's
/// refusal, or `None` for a finding this backend decides itself.
///
/// * `GatedWithoutEvidence` / `GatedFunctionRefuted` — the evidence and
///   revocation rules the format owns — become the NAMED
///   [`AdapterError::GatedWithoutEvidence`] / [`AdapterError::GatedFunctionRefuted`];
/// * `UngatedBodyForCodegen` / `UnlicensedBodyForCodegen` /
///   `UnrecognizedGateAuthority` are `None`: the claim-less policy and the
///   recognized set are [`CodegenLicensePolicy`]'s, decided on every entry
///   with the same rule and the same refusal names;
/// * any other finding is refused as [`AdapterError::TrustIrAdmissionRefused`]
///   (fail closed: a license rule a later trust-ir pin adds is never
///   ignored). The caller only passes license-layer findings.
///
/// Every trust-cg site that consumes trust-ir's license findings uses this
/// function. Evidence and revocation stay enforced in mutation-enabled builds
/// too; no test-only switch disables either rule.
pub(crate) fn license_finding_refusal(
    module: &Module,
    error: &ValidationError,
) -> Option<AdapterError> {
    match error {
        _ if decided_by_license_policy(error) => None,
        ValidationError::GatedWithoutEvidence {
            function,
            authority,
            detail,
        } => Some(AdapterError::GatedWithoutEvidence {
            function: function_name(module, *function),
            authority: authority.clone(),
            missing: detail.clone(),
        }),
        ValidationError::GatedFunctionRefuted {
            function,
            obligation,
        } => Some(AdapterError::GatedFunctionRefuted {
            function: function_name(module, *function),
            obligation: *obligation,
        }),
        other => Some(AdapterError::TrustIrAdmissionRefused {
            error: other.to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{BlockId, FuncTyId};

    fn module_with(gate: Option<BodyGate>) -> Module {
        let mut module = Module::new("m");
        let mut function = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        function.blocks.push(trust_ir::Block::new(BlockId::new(0)));
        function.body_gate = gate;
        module.functions.push(function);
        module
    }

    fn f() -> FuncId {
        FuncId::new(0)
    }

    #[test]
    fn default_policy_recognizes_clean_kernel_tv_and_refuses_none() {
        let policy = CodegenLicensePolicy::default();
        assert!(policy.recognizes(CLEAN_KERNEL_TV_AUTHORITY));
        assert!(!policy.recognizes(""));
        assert!(!policy.recognizes("someone-else"));
        assert!(!policy.recognizes("trust-direct-lane-structural"));
        assert_eq!(policy.unlicensed, UnlicensedBodyPolicy::Refuse);
        assert_eq!(
            UnlicensedBodyPolicy::default(),
            UnlicensedBodyPolicy::Refuse
        );
        assert!(matches!(
            policy.verdict(&module_with(None), f()),
            Err(AdapterError::UnlicensedBody { function }) if function == "f"
        ));
    }

    #[test]
    fn ungated_is_refused_under_every_policy() {
        for policy in [
            CodegenLicensePolicy::default(),
            CodegenLicensePolicy::recognizing_nothing(),
            CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
        ] {
            assert!(matches!(
                policy.verdict(&module_with(Some(BodyGate::Ungated)), f()),
                Err(AdapterError::UngatedBody { function }) if function == "f"
            ));
        }
    }

    #[test]
    fn gated_is_permitted_only_for_a_recognized_authority() {
        let gated = |authority: &str| module_with(Some(BodyGate::gated(authority)));
        let policy = CodegenLicensePolicy::default();
        assert!(matches!(
            policy.verdict(&gated("unknown-gate"), f()),
            Err(AdapterError::UnrecognizedGateAuthority { function, authority })
                if function == "f" && authority == "unknown-gate"
        ));
        // A blank authority is never recognized, and cannot be added.
        assert!(matches!(
            policy
                .clone()
                .with_recognized_authority("")
                .verdict(&gated(""), f()),
            Err(AdapterError::UnrecognizedGateAuthority { .. })
        ));
        let widened = policy.with_recognized_authority("unknown-gate");
        assert!(widened.verdict(&gated("unknown-gate"), f()).is_ok());
    }

    #[test]
    fn a_recognized_evidence_bound_authority_without_its_certificate_is_refused() {
        // consumer-trust-cg/04: recognition is not the evidence.
        let module = module_with(Some(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY)));
        for policy in [
            CodegenLicensePolicy::default(),
            CodegenLicensePolicy::recognizing_nothing(),
        ] {
            assert!(matches!(
                policy.verdict(&module, f()),
                Err(AdapterError::GatedWithoutEvidence { function, authority, missing })
                    if function == "f"
                        && authority == CLEAN_KERNEL_TV_AUTHORITY
                        && missing.contains("no TranslationValidation obligation")
            ));
            assert!(matches!(
                policy.enforce_module(&module),
                Err(AdapterError::GatedWithoutEvidence { .. })
            ));
        }
    }

    #[test]
    fn none_is_permitted_only_under_permit_and_declarations_are_ignored() {
        let permitting =
            CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
        assert!(permitting.verdict(&module_with(None), f()).is_ok());
        assert_eq!(
            permitting.unlicensed_bodies_permitted(&module_with(None)),
            ["f"]
        );
        assert!(
            CodegenLicensePolicy::default()
                .unlicensed_bodies_permitted(&module_with(None))
                .is_empty()
        );
        let mut declaration = module_with(Some(BodyGate::Ungated));
        declaration.functions[0].blocks.clear();
        assert!(declaration.functions[0].is_declaration());
        assert!(
            CodegenLicensePolicy::default()
                .verdict(&declaration, f())
                .is_ok()
        );
        assert!(
            CodegenLicensePolicy::default()
                .enforce_module(&declaration)
                .is_ok()
        );
    }

    /// A module of one bodied function per stamp, ids `0..`, in order.
    fn module_of(gates: &[Option<BodyGate>]) -> Module {
        let mut module = Module::new("m");
        for (index, gate) in gates.iter().enumerate() {
            let id = u32::try_from(index).expect("small fixture");
            let mut function = Function::new(
                FuncId::new(id),
                format!("f{index}"),
                FuncTyId::new(0),
                BlockId::new(0),
            );
            function.blocks.push(trust_ir::Block::new(BlockId::new(0)));
            function.body_gate = gate.clone();
            module.functions.push(function);
        }
        module
    }

    /// The translation census (`census_module`) records exactly the refusals
    /// the per-function verdict gives, in module order, and `enforce_module`
    /// returns the first of them: adversarially, a claim-less body under the
    /// default, an ungated body under `Permit` beside a permitted claim-less
    /// one, an unrecognized authority beside a recognized one, and a module
    /// every policy admits.
    #[test]
    fn the_census_records_exactly_the_per_function_verdicts() {
        let gated = |authority: &str| Some(BodyGate::gated(authority));
        let permit = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
        let cases: [(Module, CodegenLicensePolicy, Vec<u32>); 4] = [
            (
                module_of(&[None, None]),
                CodegenLicensePolicy::default(),
                vec![0, 1],
            ),
            (
                module_of(&[None, Some(BodyGate::Ungated), None]),
                permit.clone(),
                vec![1],
            ),
            (
                module_of(&[gated("vendor"), gated("someone-else")]),
                CodegenLicensePolicy::default().with_recognized_authority("vendor"),
                vec![1],
            ),
            (
                module_of(&[gated("vendor"), None]),
                permit.with_recognized_authority("vendor"),
                vec![],
            ),
        ];
        for (module, policy, refused) in cases {
            let rows = policy
                .census_module(&module)
                .expect("no module-level finding");
            let ids: Vec<u32> = rows.iter().map(|(id, _)| id.index()).collect();
            assert_eq!(ids, refused, "{policy:?}");
            for (id, error) in &rows {
                let verdict = policy
                    .verdict(&module, *id)
                    .expect_err("the census refuses only what the verdict refuses");
                assert_eq!(error.to_string(), verdict.to_string());
            }
            for function in &module.functions {
                assert_eq!(
                    policy.verdict(&module, function.id).is_err(),
                    rows.iter().any(|(id, _)| *id == function.id)
                );
            }
            match (rows.first(), policy.enforce_module(&module)) {
                (None, Ok(())) => {}
                (Some((_, first)), Err(error)) => assert_eq!(first.to_string(), error.to_string()),
                (rows, outcome) => panic!("census {rows:?} disagrees with enforce {outcome:?}"),
            }
        }
    }

    #[test]
    fn a_verdict_about_an_absent_function_is_refused() {
        assert!(matches!(
            CodegenLicensePolicy::default().verdict(&module_with(None), FuncId::new(9)),
            Err(AdapterError::InvalidTrustIr(message)) if message.contains("FuncId(9)")
        ));
    }

    #[test]
    fn every_permit_exception_permits_and_names_itself() {
        let gated = |authority: &str| module_with(Some(BodyGate::gated(authority)));
        let mut tokens = BTreeSet::new();
        for exception in UnlicensedPermitException::ALL {
            let policy =
                CodegenLicensePolicy::default().with_unlicensed_permit_exception(exception);
            assert_eq!(policy.unlicensed, UnlicensedBodyPolicy::Permit);
            assert!(tokens.insert(exception.token()), "{exception:?}");
            // A named exception concerns the claim-less state ONLY: it admits
            // `None`, and it widens nothing else — `Ungated`, an unrecognized
            // authority and an evidence-bound authority without its evidence
            // stay refused, exactly as under the default.
            assert!(
                policy.verdict(&module_with(None), f()).is_ok(),
                "{exception:?}"
            );
            assert!(
                matches!(
                    policy.verdict(&module_with(Some(BodyGate::Ungated)), f()),
                    Err(AdapterError::UngatedBody { .. })
                ),
                "{exception:?}"
            );
            assert!(
                matches!(
                    policy.verdict(&gated("unknown-gate"), f()),
                    Err(AdapterError::UnrecognizedGateAuthority { .. })
                ),
                "{exception:?}"
            );
            assert!(
                matches!(
                    policy.verdict(&gated(CLEAN_KERNEL_TV_AUTHORITY), f()),
                    Err(AdapterError::GatedWithoutEvidence { .. })
                ),
                "{exception:?}"
            );
            assert_eq!(
                policy.recognized_authorities,
                CodegenLicensePolicy::default().recognized_authorities,
                "{exception:?}"
            );
        }
    }

    #[test]
    fn canonical_identity_is_sorted_and_stable() {
        let policy = CodegenLicensePolicy::recognizing_nothing()
            .with_recognized_authority("zeta")
            .with_recognized_authority("alpha")
            .with_unlicensed(UnlicensedBodyPolicy::Permit);
        assert_eq!(
            policy.canonical_identity(),
            "unlicensed=permit;authorities=alpha,zeta"
        );
        assert_eq!(
            CodegenLicensePolicy::default().canonical_identity(),
            "unlicensed=refuse;authorities=clean-kernel-tv"
        );
    }

    /// How many times `tokens` NAME the type `ty`: its identifier as a code
    /// token (comments and literals never reach the token stream). The
    /// census below pins this per production file, because every way to reach
    /// a variant WITHOUT the `Type::Variant` path the Permit census counts —
    /// a glob import (`use ..::UnlicensedBodyPolicy::*;` then a bare
    /// `Permit`), a grouped import (`use ..::UnlicensedBodyPolicy::{Permit}`),
    /// a rename (`use .. as P;` then `P::Permit`), a type alias, or a foreign
    /// trait impl's `Self::Permit` — still has to name the type once.
    fn type_namings(tokens: &[crate::source_scan::Tok], ty: &str) -> usize {
        tokens
            .iter()
            .filter(|token| **token == crate::source_scan::Tok::Ident(ty.into()))
            .count()
    }

    /// The positions of every `ty::variant` path spelling in `tokens` (the
    /// Permit census's own rule).
    fn path_spellings(tokens: &[crate::source_scan::Tok], ty: &str, variant: &str) -> Vec<usize> {
        use crate::source_scan::Tok;
        tokens
            .windows(3)
            .enumerate()
            .filter(|(_, window)| {
                window[0] == Tok::Ident(ty.into())
                    && window[1] == Tok::PathSep
                    && window[2] == Tok::Ident(variant.into())
            })
            .map(|(at, _)| at)
            .collect()
    }

    /// Review adversarials for the census: each shape below reaches
    /// `UnlicensedBodyPolicy::Permit` WITHOUT the path spelling the Permit
    /// census counts (so that rule alone passes it), and each is caught by
    /// the per-file type-naming pin because it names the type. A shape that
    /// named the type zero times would slip both; none of these does.
    #[test]
    fn census_bypass_shapes_are_caught_by_the_type_naming_pin() {
        use crate::source_scan::scan;
        let shapes = [
            (
                "glob import",
                "use trust_cg_lower::UnlicensedBodyPolicy::*;\n\
                 fn policy() -> trust_cg_lower::CodegenLicensePolicy {\n\
                 trust_cg_lower::CodegenLicensePolicy::default().with_unlicensed(Permit) }",
            ),
            (
                "grouped import",
                "use trust_cg_lower::UnlicensedBodyPolicy::{Permit};\n\
                 fn p() { let _ = Permit; }",
            ),
            (
                "rename",
                "use trust_cg_lower::UnlicensedBodyPolicy as P;\n\
                 fn p() { let _ = P::Permit; }",
            ),
            (
                "type alias",
                "type P = trust_cg_lower::UnlicensedBodyPolicy;\n\
                 fn p() { let _ = P::Permit; }",
            ),
            (
                "foreign trait impl",
                "impl From<Legacy> for trust_cg_lower::UnlicensedBodyPolicy {\n\
                 fn from(_: Legacy) -> Self { Self::Permit } }",
            ),
        ];
        for (shape, source) in shapes {
            let tokens = scan(source).tokens;
            assert!(
                path_spellings(&tokens, "UnlicensedBodyPolicy", "Permit").is_empty(),
                "{shape}: the path rule sees it, so this shape is not a bypass of it"
            );
            assert!(
                type_namings(&tokens, "UnlicensedBodyPolicy") >= 1,
                "{shape}: the type-naming pin must see it"
            );
        }
        // Control: the sanctioned spelling is seen by BOTH rules, and a
        // comment or string naming the type is seen by neither.
        let sanctioned = scan(
            "fn p() { let _ = trust_cg_lower::UnlicensedBodyPolicy::Permit; }\n\
             // UnlicensedBodyPolicy::Permit\n\
             const S: &str = \"UnlicensedBodyPolicy::Permit\";",
        )
        .tokens;
        assert_eq!(
            path_spellings(&sanctioned, "UnlicensedBodyPolicy", "Permit").len(),
            1
        );
        assert_eq!(type_namings(&sanctioned, "UnlicensedBodyPolicy"), 1);
    }

    /// `fn checked_add(a: i32, b: i32) -> i32 { let (r, o) = a.overflowing_add(b);
    /// assert!(!o); r }` with `claims` on the `assert` node. The body is
    /// claim-less and the policies below state Permit (WS7.5: the default
    /// refuses it, and an evidence-bound authority would need a Certified
    /// TranslationValidation row), so the license layer is not what any
    /// assertion measures. Returns the module and the assert's site.
    fn checked_add(
        claims: &[trust_ir::proof::ProofAnnotation],
    ) -> (Module, trust_ir::proof::ObligationSite) {
        use trust_ir::{BinOp, Constant, Inst, OverflowOp, Ty};
        let mut mb = trust_ir_build::ModuleBuilder::new("unbacked_claim_knob");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("checked_add", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let (r, o) = fb.overflow(OverflowOp::AddOverflow, Ty::I32, a, b);
        let t = fb.const_value(Ty::Bool, Constant::Bool(true));
        let ok = fb.binop(BinOp::BXor, Ty::Bool, o, t);
        fb.assert(ok);
        for claim in claims {
            fb.annotate_last(claim.clone())
                .expect("the assert was just emitted");
        }
        fb.ret(vec![r]);
        let f = fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert!(module.functions[0].body_gate.is_none());
        let assert_index = module.functions[0].blocks[0]
            .body
            .iter()
            .position(|node| matches!(node.inst, Inst::Assert { .. }))
            .expect("the body carries the assert") as u32;
        (
            module,
            trust_ir::proof::ObligationSite::new(f, BlockId::new(0), assert_index),
        )
    }

    /// The default policy, stating Permit for the claim-less fixture.
    fn permitting() -> CodegenLicensePolicy {
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
    }

    fn refusing_unbacked_claims() -> CodegenLicensePolicy {
        permitting().with_refuse_unbacked_claims_on_checks(true)
    }

    #[test]
    fn an_unbacked_claim_on_a_check_is_refused_only_under_the_knob() {
        use trust_ir::proof::ProofAnnotation;
        let (module, _) = checked_add(&[ProofAnnotation::NoOverflow]);
        // The default is off (pending the producer fix, WS5): permitted.
        assert!(!CodegenLicensePolicy::default().refuse_unbacked_claims_on_checks);
        assert!(permitting().enforce_module(&module).is_ok());
        // On: refused with trust-ir's own finding, by name.
        match refusing_unbacked_claims().enforce_module(&module) {
            Err(AdapterError::TrustIrAdmissionRefused { error }) => {
                assert!(
                    error.contains("`NoOverflow` claim on the runtime check"),
                    "{error}"
                );
                assert!(error.contains("checked_add"), "{error}");
            }
            other => panic!("expected the unbacked-claim refusal, got {other:?}"),
        }
        // The claim-free twin is accepted under the knob: the refusal is the
        // claim's, not the check's.
        let (claim_free, _) = checked_add(&[]);
        assert!(
            refusing_unbacked_claims()
                .enforce_module(&claim_free)
                .is_ok()
        );
    }

    /// The census lane (`census_module`, which the adapter's per-function
    /// census route calls INSTEAD of `enforce_module`) refuses the module
    /// under the knob exactly as `enforce_module` does, and records nothing
    /// without it.
    #[test]
    fn the_census_lane_meets_the_unbacked_claim_knob() {
        use trust_ir::proof::ProofAnnotation;
        let (module, _) = checked_add(&[ProofAnnotation::NoOverflow]);
        assert!(permitting().census_module(&module).unwrap().is_empty());
        match refusing_unbacked_claims().census_module(&module) {
            Err(AdapterError::TrustIrAdmissionRefused { error }) => {
                assert!(
                    error.contains("`NoOverflow` claim on the runtime check"),
                    "{error}"
                );
            }
            other => panic!("expected the unbacked-claim refusal, got {other:?}"),
        }
        let (claim_free, _) = checked_add(&[]);
        assert!(
            refusing_unbacked_claims()
                .census_module(&claim_free)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn a_sited_kind_matched_proof_ref_backs_the_claim_under_the_knob() {
        use trust_ir::proof::{ObligationKind, ProofAnnotation, ProofObligation, ProofStatus};
        use trust_ir::value::ProofId;
        let (mut module, assert_site) = checked_add(&[
            ProofAnnotation::NoOverflow,
            ProofAnnotation::ProofRef(ProofId::new(0)),
        ]);
        let row = |kind| {
            ProofObligation::new(ProofId::new(0), kind, ProofStatus::Pending, "unbacked knob")
                .with_function(assert_site.function)
                .with_site(assert_site)
        };
        module
            .proof_obligations
            .push(row(ObligationKind::ArithmeticSafety));
        assert!(refusing_unbacked_claims().enforce_module(&module).is_ok());
        // Twin: right node, a kind that cannot be about a check: unbacked.
        module.proof_obligations[0] = row(ObligationKind::Postcondition);
        assert!(matches!(
            refusing_unbacked_claims().enforce_module(&module),
            Err(AdapterError::TrustIrAdmissionRefused { .. })
        ));
    }

    #[test]
    fn the_unbacked_claim_knob_enters_the_identity_only_when_set() {
        // The default identity is byte-identical to the knob-free policy's.
        assert_eq!(
            CodegenLicensePolicy::default()
                .with_refuse_unbacked_claims_on_checks(false)
                .canonical_identity(),
            "unlicensed=refuse;authorities=clean-kernel-tv"
        );
        assert_eq!(
            permitting()
                .with_refuse_unbacked_claims_on_checks(false)
                .canonical_identity(),
            "unlicensed=permit;authorities=clean-kernel-tv"
        );
        assert_eq!(
            refusing_unbacked_claims().canonical_identity(),
            "unlicensed=permit;authorities=clean-kernel-tv;unbacked_claims=refuse"
        );
        assert_ne!(refusing_unbacked_claims(), permitting());
    }

    /// trust-ir's claim-less admission policy is this policy's own verdict:
    /// `Refuse` by default (DG-73), `Permit` only for a permitting policy.
    #[test]
    fn trust_irs_claim_less_policy_is_this_policys_verdict() {
        for (policy, permits) in [
            (CodegenLicensePolicy::default(), false),
            (CodegenLicensePolicy::recognizing_nothing(), false),
            (permitting(), true),
            (
                CodegenLicensePolicy::default()
                    .with_unlicensed_permit_exception(UnlicensedPermitException::FuzzHarness),
                true,
            ),
        ] {
            assert_eq!(policy.permits_unlicensed(), permits, "{policy:?}");
            let expected = if permits {
                trust_ir_build::UnlicensedBodyPolicy::Permit
            } else {
                trust_ir_build::UnlicensedBodyPolicy::Refuse
            };
            assert!(
                policy.trust_ir_unlicensed_policy() == expected,
                "{policy:?}: trust-ir's policy is {}",
                policy.trust_ir_unlicensed_policy().name()
            );
        }
    }

    /// The production sites that PERMIT claim-less bodies, named and counted
    /// (roadmap WS7.5 DECIDE 1: "a named, counted exception, not a silent
    /// default"). Non-test code of EVERY workspace crate and of the
    /// out-of-workspace MIR lane may spell `UnlicensedBodyPolicy::Permit`
    /// only in this file (the variant, the verdict and the one exception
    /// constructor; trust-ir's `Permit` here only as that verdict's
    /// translation),
    /// and each [`UnlicensedPermitException`] is named exactly where the
    /// table says. A new Permit fails here by name.
    #[test]
    fn the_unlicensed_permit_exceptions_are_named_and_counted() {
        use crate::source_scan::{Tok, crate_files_from, scan};
        use std::collections::BTreeMap;
        use std::path::{Path, PathBuf};

        let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let mut files: BTreeMap<String, Vec<Tok>> = BTreeMap::new();
        let mut entries = std::fs::read_dir(&crates)
            .expect("read crates/")
            .map(|entry| entry.expect("crates/ entry").path())
            .filter(|path| path.join("Cargo.toml").is_file() && path.join("src").is_dir())
            .collect::<Vec<_>>();
        entries.sort();
        assert!(
            entries.len() > 10,
            "the workspace crates are found: {entries:?}"
        );
        for krate in &entries {
            let src = krate.join("src");
            let mut roots: Vec<PathBuf> = ["lib.rs", "main.rs"]
                .into_iter()
                .map(|root| src.join(root))
                .filter(|root| root.is_file())
                .collect();
            if let Ok(bins) = std::fs::read_dir(src.join("bin")) {
                for bin in bins {
                    let path = bin.expect("bin entry").path();
                    if path.extension().is_some_and(|e| e == "rs") {
                        roots.push(path);
                    } else if path.join("main.rs").is_file() {
                        roots.push(path.join("main.rs"));
                    }
                }
            }
            let name = krate
                .file_name()
                .expect("crate dir")
                .to_string_lossy()
                .to_string();
            for (path, test) in crate_files_from(&roots) {
                if test {
                    continue;
                }
                let relative = path
                    .strip_prefix(krate)
                    .map_or_else(|_| path.clone(), Path::to_path_buf)
                    .to_string_lossy()
                    .replace('\\', "/");
                let text = std::fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
                files.insert(format!("{name}/{relative}"), scan(&text).tokens);
            }
        }
        // The cargo-fuzz targets (their own workspace, `fuzz/`): each file is
        // a crate root.
        let fuzz_targets = crates.join("../fuzz/fuzz_targets");
        let mut targets = std::fs::read_dir(&fuzz_targets)
            .expect("read fuzz/fuzz_targets")
            .map(|entry| entry.expect("fuzz target").path())
            .filter(|path| path.extension().is_some_and(|e| e == "rs"))
            .collect::<Vec<_>>();
        targets.sort();
        for target in targets {
            let text = std::fs::read_to_string(&target).expect("read fuzz target");
            let name = target
                .file_name()
                .expect("file")
                .to_string_lossy()
                .to_string();
            files.insert(format!("fuzz/fuzz_targets/{name}"), scan(&text).tokens);
        }
        assert!(
            files.contains_key("rustc-codegen-trust-cg/src/lib.rs")
                && files.contains_key("trust-cg-cli/src/main.rs")
                && files.contains_key("trust-cg-lower/src/codegen_license.rs"),
            "the census reaches the MIR lane, the CLI and this file"
        );

        let path_uses = |tokens: &[Tok], ty: &str| -> Vec<String> {
            tokens
                .windows(3)
                .filter(|w| w[0] == Tok::Ident(ty.into()) && w[1] == Tok::PathSep)
                .filter_map(|w| match &w[2] {
                    Tok::Ident(variant) => Some(variant.clone()),
                    _ => None,
                })
                .collect()
        };

        // `(file, whose type)` -> count of `UnlicensedBodyPolicy::Permit`,
        // telling this crate's policy apart from trust-ir-build's admission
        // type of the same name (`trust_ir_build::UnlicensedBodyPolicy`).
        let mut permits: BTreeMap<(String, &str), usize> = BTreeMap::new();
        let mut exceptions: BTreeMap<(String, String), usize> = BTreeMap::new();
        for (file, tokens) in &files {
            for at in path_spellings(tokens, "UnlicensedBodyPolicy", "Permit") {
                let format_type = at >= 2
                    && tokens[at - 2] == Tok::Ident("trust_ir_build".into())
                    && tokens[at - 1] == Tok::PathSep;
                let owner = if format_type {
                    "trust_ir_build"
                } else {
                    "trust_cg_lower"
                };
                *permits.entry((file.clone(), owner)).or_default() += 1;
            }
            if file == "trust-cg-lower/src/codegen_license.rs" {
                continue;
            }
            for variant in path_uses(tokens, "UnlicensedPermitException") {
                *exceptions.entry((file.clone(), variant)).or_default() += 1;
            }
        }
        assert_eq!(
            permits,
            BTreeMap::from([
                // The variant's own `token` arm, the verdict's `Permit` arm
                // (`permits_unlicensed`) and the exception constructor.
                (
                    (
                        "trust-cg-lower/src/codegen_license.rs".to_string(),
                        "trust_cg_lower"
                    ),
                    3
                ),
                // `trust_ir_unlicensed_policy`: that one verdict in trust-ir's
                // admission type, for the WS7.3 ingestion admission
                // (`ingest::admission_findings`). It translates the caller's
                // policy and sets nothing.
                (
                    (
                        "trust-cg-lower/src/codegen_license.rs".to_string(),
                        "trust_ir_build"
                    ),
                    1
                ),
                // `validate_codegen_prerequisites`: trust-ir's STRUCTURAL
                // admission pass, which leaves the claim-less decision to
                // `CodegenLicensePolicy::enforce_module` on the same entry.
                (
                    (
                        "trust-cg-lower/src/adapter.rs".to_string(),
                        "trust_ir_build"
                    ),
                    1
                ),
            ]),
            "production code spells `UnlicensedBodyPolicy::Permit` outside the named-exception \
             constructor; name an `UnlicensedPermitException` instead"
        );
        let expected: BTreeMap<(String, String), usize> = [
            ("trust-cg-cli/src/main.rs", "LegacyCorpusFlag"),
            (
                "trust-cg-cli/src/bin/ty_replay_jit_probe.rs",
                "LegacyCorpusFlag",
            ),
            (
                "trust-cg-codegen/src/strict_adapter.rs",
                "CoreAdmissionFloor",
            ),
            ("rustc-codegen-trust-cg/src/lib.rs", "InProcessMirLane"),
            ("trust-cg-jit-matrix/src/lib.rs", "InProcessJitKernel"),
            ("trust-cg-jit-matrix/src/lib.rs", "BenchCorpus"),
            (
                "trust-cg-llvm-import/src/bin/trust-cg-ws2-import.rs",
                "LlvmImport",
            ),
            ("trust-cg-fuzz/src/lib.rs", "FuzzHarness"),
            (
                "fuzz/fuzz_targets/fuzz_translate_function.rs",
                "FuzzHarness",
            ),
            ("fuzz/fuzz_targets/fuzz_compile_function.rs", "FuzzHarness"),
            ("trust-cg-codegen/src/wasm/lower.rs", "LaneRuntimeHelper"),
        ]
        .into_iter()
        .map(|(file, variant)| ((file.to_string(), variant.to_string()), 1))
        .collect();
        assert_eq!(
            exceptions, expected,
            "the named Permit exceptions moved; update this census deliberately"
        );
        // Every exception is named at some production site.
        let named: BTreeSet<&str> = expected.keys().map(|(_, v)| v.as_str()).collect();
        assert_eq!(named.len(), UnlicensedPermitException::ALL.len());

        // The path census above counts `Type::Variant` spellings only. Every
        // other way to reach a variant (glob or grouped import, rename, type
        // alias, foreign trait impl: `census_bypass_shapes_are_caught_by_the_type_naming_pin`)
        // must NAME the type, so each production file's naming count of both
        // license types is pinned exactly: a new naming anywhere fails here
        // by file, and is reviewed before the pin moves.
        let mut namings: BTreeMap<(String, &str), usize> = BTreeMap::new();
        for (file, tokens) in &files {
            if file == "trust-cg-lower/src/codegen_license.rs" {
                continue;
            }
            for ty in ["UnlicensedBodyPolicy", "UnlicensedPermitException"] {
                let count = type_namings(tokens, ty);
                if count > 0 {
                    namings.insert((file.clone(), ty), count);
                }
            }
        }
        let expected_namings: BTreeMap<(String, &str), usize> = [
            // The re-exports (a type naming, no variant).
            ("trust-cg-lower/src/lib.rs", "UnlicensedBodyPolicy", 1),
            ("trust-cg-lower/src/lib.rs", "UnlicensedPermitException", 1),
            ("trust-cg-codegen/src/lib.rs", "UnlicensedBodyPolicy", 1),
            (
                "trust-cg-codegen/src/lib.rs",
                "UnlicensedPermitException",
                1,
            ),
            // trust-ir-build's STRUCTURAL admission type (the Permit counted
            // above as `trust_ir_build`'s).
            ("trust-cg-lower/src/adapter.rs", "UnlicensedBodyPolicy", 1),
            // The named exception sites of the table above; the CLI also
            // imports the type.
            ("trust-cg-cli/src/main.rs", "UnlicensedPermitException", 2),
            (
                "trust-cg-cli/src/bin/ty_replay_jit_probe.rs",
                "UnlicensedPermitException",
                1,
            ),
            (
                "trust-cg-codegen/src/strict_adapter.rs",
                "UnlicensedPermitException",
                1,
            ),
            (
                "rustc-codegen-trust-cg/src/lib.rs",
                "UnlicensedPermitException",
                1,
            ),
            // `in_process_kernel_license` and `bench_corpus_license`.
            (
                "trust-cg-jit-matrix/src/lib.rs",
                "UnlicensedPermitException",
                2,
            ),
            (
                "trust-cg-llvm-import/src/bin/trust-cg-ws2-import.rs",
                "UnlicensedPermitException",
                1,
            ),
            ("trust-cg-fuzz/src/lib.rs", "UnlicensedPermitException", 1),
            (
                "fuzz/fuzz_targets/fuzz_translate_function.rs",
                "UnlicensedPermitException",
                1,
            ),
            (
                "fuzz/fuzz_targets/fuzz_compile_function.rs",
                "UnlicensedPermitException",
                1,
            ),
            // `lane_helper_license`.
            (
                "trust-cg-codegen/src/wasm/lower.rs",
                "UnlicensedPermitException",
                1,
            ),
        ]
        .into_iter()
        .map(|(file, ty, count): (&str, &str, usize)| ((file.to_string(), ty), count))
        .collect();
        assert_eq!(
            namings, expected_namings,
            "a production file names a license type a new number of times; if it reaches a \
             Permit, it must do so through a named `UnlicensedPermitException`"
        );
    }
}
