// trust-cg-codegen/lir_module_prep.rs - The shared pre-ISel LIR module step for JIT consumers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The target-independent LIR module step a JIT compile runs between
//! translation (plus exact-binding replay) and instruction selection.
//!
//! `Compiler::compile` (AOT) has run two shared LIR passes at this seam since
//! OPT-4: the module inliner (`trust_cg_opt::ir_inline`) and unsigned-range
//! simplification (`trust_cg_opt::lir_unsigned_range`). [`prepare_jit_lir_module`]
//! is the same step for every JIT consumer (the range pass runs over the
//! functions the inliner changed, not the whole module: see the function):
//! `Compiler::compile_module_to_jit` on both targets, and any raw lane that
//! translates and replays its own LIR
//! before handing it to [`crate::Pipeline`] / [`crate::jit::JitCompiler`]
//! (TY's native lane, `trust-cg-jit-matrix`). A raw lane calls it instead of
//! re-implementing it.
//!
//! Both seams take one more input: **inline-only bodies**, the bodies of
//! trust-ir `AvailableExternally` functions ([`admit_inline_only_bodies`],
//! over [`trust_cg_lower::translate_inline_only_bodies`]). A frontend with a
//! runtime ships a helper's fast path this way — ONE definition (the runtime's
//! symbol, bound through the extern map in a JIT, or by the linker for an
//! object) plus a body the inliner may splice into generated code — instead
//! of hand-expanding the helper in its emitter. A call the inliner does not
//! replace stays exactly the external call.
//!
//! # What is and is not checked
//!
//! Every splice is checked as an AOT splice is: by the inliner's fail-closed
//! self-checks (instruction conservation, CFG well-formedness, value
//! freshness). Those checks are structural, and a wrong argument-to-parameter
//! mapping passes them. Every per-instruction lowering proof and
//! translation-validation gate downstream takes the spliced LIR as its source,
//! so it checks the lowering of a splice, not the splice ("Proof claims",
//! below). The range pass has no check at all. Beyond the splice, the one
//! premise nothing checks is the one-definition rule: that an inline-only body
//! computes what the definition its symbol binds to computes, unless the caller supplies
//! the dependency that defines it ([`InlineOnlyAuthority`]): a body is
//! AUTHENTICATED when an import row of the module that `verify_import`
//! accepts against a supplied dependency names one that defines the symbol
//! with an equal translation. [`InlineOnlyAdmission`] decides whether a
//! compile may rest on the unchecked premise; every body it admits and the
//! inliner splices is listed in [`InlineOnlyBodyEvidence::spliced`] (on a
//! `JitCompilationResult` and a `CompilationResult`, `inline_only_bodies`),
//! as a DISCLOSED premise or, when authenticated, a discharged one
//! ([`InlineOnlyBodyEvidence::authenticated`]). A compile that makes a proof
//! claim splices none (`docs/jit-inline-only-bodies.md`).
//!
//! # Proof claims (ruling OD-225)
//!
//! Neither pass of this step is validated, and every per-function proof
//! downstream (the x86-64 source-bound body theorem, the AArch64 source-bound
//! obligations, the per-instruction lowering proofs, the TV gates, the JIT
//! certificates) takes the LIR instruction selection receives as its source.
//! So a compile that makes a proof claim runs neither
//! ([`unvalidated_lir_passes_run`]). That is a compile that emits proofs, or a
//! JIT compile whose validation mode requires proof-grade evidence for every
//! function; its admission is [`InlineOnlyAdmission::Withhold`]
//! ([`InlineOnlyAdmission::for_proof_claim`]). The step returns at once with
//! [`LirModulePreparation::skipped_for_proof_claim`] set, so the LIR is the
//! adapter's exactly, and it lists every inline-only body as withheld
//! ([`InlineOnlyBodyEvidence::withheld_for_proof_claim`]). `Compiler::compile`
//! applies the same rule at the AOT seam. A pass may return to a
//! proof-claiming compile only with a validator of its own.
//!
//! # Binding in the JIT
//!
//! A JIT link resolves a by-name reference to an EXPLICIT extern binding
//! first, then to the module's own definition, then to process symbols
//! (`jit::resolve_raw_internal_fixup`). So an explicit binding interposes on
//! a non-local module definition of the same name (the
//! `direct_call_binding.rs` control): such a definition is never spliced. The
//! caller names those bindings ([`JitExternBindings`]); a module-local
//! (`Internal`/`Private`) definition is reached through its exact module edge,
//! which no binding overrides. An inline-only body's symbol is bound by the
//! extern map to the one definition the premise is about.
//!
//! # Kill switches
//!
//! Skipped at O0 and in a compile that makes a proof claim.
//! `TCG_NO_JIT_LIR_PREPARE` skips the whole step, restoring the
//! JIT's pre-step output byte for byte. `TCG_NO_INLINE_ONLY_BODIES` withholds
//! every inline-only body (JIT and AOT) and leaves the rest of the step: a
//! module without inline-only bodies compiles to the same bytes either way.
//! The inliner's own switches keep their meaning: `TCG_NO_INLINE` (both
//! tiers) and `TCG_NO_MB_INLINE` (the CFG-splicing tier).

use std::collections::HashSet;
use std::time::{Duration, Instant};

use trust_cg_lower::{
    CodegenLicensePolicy, Function, GuardCarrierArch, InlineOnlyBodies, InlineOnlyWithheld,
    ObjectAccessModel, ProofContext, TlsDialect, translate_body_template,
    translate_inline_only_bodies,
};
use trust_cg_opt::ir_inline::{InlineOnlyUse, InlineStats, inline_module_with_inline_only_bodies};
use trust_cg_opt::lir_unsigned_range::{LirUnsignedRangeStats, simplify_functions_at};

use crate::compiler::CompileError;
use crate::pipeline::OptLevel;

/// Environment variable that skips [`prepare_jit_lir_module`] entirely.
pub const JIT_LIR_PREPARE_KILL_SWITCH: &str = "TCG_NO_JIT_LIR_PREPARE";

/// Why a compile that makes a proof claim withholds every inline-only body
/// (module docs, "Proof claims"). It keeps the words the proof-claim admission
/// has always used (`proof-producing compile`).
const PROOF_CLAIM_WITHHELD_REASON: &str = "proof-producing compile: neither the LIR inliner nor \
     unsigned-range simplification runs (ruling OD-225), so no inline-only body is spliced and \
     every call to one stays a call";

/// The trace phase a compile that makes a proof claim records at O1 and above,
/// in place of `ir_inline` and `lir_unsigned_range` (module docs, "Proof
/// claims").
pub(crate) const PROOF_CLAIM_SKIP_PHASE: &str = "lir_passes_skipped";

/// [`PROOF_CLAIM_SKIP_PHASE`]'s detail.
pub(crate) const PROOF_CLAIM_SKIP_DETAIL: &str =
    "proof claim (ruling OD-225): neither ir_inline nor lir_unsigned_range runs";

/// Whether the shared pre-ISel LIR passes, the module inliner and
/// unsigned-range simplification, run in a compile at `opt_level` that does
/// (`makes_proof_claim`) or does not make a proof claim: at O1 and above, and
/// never under a proof claim (module docs, "Proof claims"; ruling OD-225).
/// Both seams decide through it: the JIT step ([`prepare_jit_lir_module`],
/// from its admission's [`InlineOnlyAdmission::makes_proof_claim`]) and the
/// AOT seam of `Compiler::compile` (from `emit_proofs`).
#[must_use]
pub fn unvalidated_lir_passes_run(opt_level: OptLevel, makes_proof_claim: bool) -> bool {
    opt_level != OptLevel::O0 && !makes_proof_claim
}

/// Environment variable that withholds every inline-only body, in the JIT
/// step and at the AOT seam alike ([`admit_inline_only_bodies`]); module
/// definitions are still inlined. The same-binary switch for measuring what
/// the inline-only splices alone change.
pub const INLINE_ONLY_BODIES_KILL_SWITCH: &str = "TCG_NO_INLINE_ONLY_BODIES";

/// Which names the JIT link will bind through an EXPLICIT extern binding —
/// which takes precedence over a module definition of the same name (module
/// docs, "Binding in the JIT").
#[derive(Clone, Copy)]
pub enum JitExternBindings<'a> {
    /// Exactly the names this map binds to a non-null address (the map the
    /// link will use: `Compiler::compile_module_to_jit`'s `extern_symbols`).
    Map(&'a std::collections::HashMap<String, *const u8>),
    /// Any name: every non-local module definition is treated as
    /// interposable. The safe answer for a raw lane that may relink its image
    /// under other bindings, or that cannot say.
    Any,
}

impl JitExternBindings<'_> {
    fn binds(self, name: &str) -> bool {
        match self {
            Self::Map(map) => map.get(name).is_some_and(|address| !address.is_null()),
            Self::Any => true,
        }
    }
}

/// The module definitions an explicit JIT extern binding may interpose on:
/// bodied, non-local (`Internal`/`Private` are reached through exact module
/// edges), not `AvailableExternally` (an inline-only body is never a
/// definition), and bound by `bindings`.
#[must_use]
pub fn jit_interposable_definitions(
    module: &trust_ir::Module,
    bindings: JitExternBindings<'_>,
) -> HashSet<String> {
    module
        .functions
        .iter()
        .filter(|function| {
            function.has_body()
                && !function.linkage.is_module_local()
                && function.linkage != trust_ir::Linkage::AvailableExternally
                && bindings.binds(&function.name)
        })
        .map(|function| function.name.clone())
        .collect()
}

/// Whether a compile may splice inline-only bodies (module docs, "What is and
/// is not checked").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineOnlyAdmission {
    /// Splice every body [`trust_cg_lower::translate_inline_only_bodies`]
    /// admits; each one spliced is a disclosed one-definition-rule premise.
    DisclosedPremise,
    /// Admit only AUTHENTICATED bodies ([`InlineOnlyAuthority`]). The
    /// admission of a compile that makes a proof claim: every other candidate
    /// is withheld, and its calls stay calls. Since ruling OD-225 the shared
    /// LIR step does not run at all under it (module docs, "Proof claims"),
    /// so no body is spliced, authenticated or not; this is still what
    /// [`admit_inline_only_bodies_with_authority`] answers under it.
    Withhold,
}

impl InlineOnlyAdmission {
    /// The admission of a compile that does (`true`) or does not make a proof
    /// claim about its output. A compile makes one when it emits proofs, or
    /// when it is a JIT compile whose validation mode requires proof-grade
    /// evidence for every published function
    /// ([`crate::compiler::JitValidationMode::requires_jit_verification`]):
    /// those claims are about the module's semantics, and the one-definition
    /// premise an inline-only splice rests on is not checked by any
    /// per-function lowering proof. Such a compile withholds every body.
    #[must_use]
    pub fn for_proof_claim(makes_proof_claim: bool) -> Self {
        if makes_proof_claim {
            Self::Withhold
        } else {
            Self::DisclosedPremise
        }
    }

    /// Whether this is the admission of a compile that makes a proof claim
    /// (`for_proof_claim(true)`). Under it the shared LIR step runs neither
    /// pass ([`unvalidated_lir_passes_run`]).
    #[must_use]
    pub fn makes_proof_claim(self) -> bool {
        matches!(self, Self::Withhold)
    }
}

/// What a compile did with the module's inline-only bodies.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InlineOnlyBodyEvidence {
    /// Inline-only bodies spliced into at least one caller, sorted by name.
    /// Each is the premise that the body computes what the definition its
    /// symbol binds to computes (the one-definition rule): DISCLOSED and not
    /// checked by this compile, unless [`Self::authenticated`] names the body.
    pub spliced: Vec<InlineOnlyUse>,
    /// Inline-only bodies not admitted, with the reason; their calls stayed
    /// external calls.
    pub withheld: Vec<InlineOnlyWithheld>,
    /// Spliced bodies whose premise is DISCHARGED rather than disclosed: an
    /// import of the module that `Module::verify_import` authenticates against
    /// a supplied dependency exports a definition of the symbol whose LIR
    /// translation equals the body's ([`InlineOnlyAuthority`]). Sorted by name.
    pub authenticated: Vec<InlineOnlyAuthentication>,
}

/// How an inline-only body was authenticated ([`InlineOnlyAuthority`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlineOnlyAuthentication {
    /// The inline-only body's symbol.
    pub name: String,
    /// The authenticated dependency's module name (its import row's `name`).
    pub dependency: String,
    /// The digest the dependency was authenticated under (the import row's
    /// recorded digest), lowercase hex.
    pub digest: String,
}

/// Dependencies a compile may authenticate inline-only bodies against.
///
/// A body `h` of the compiled module is AUTHENTICATED when, for some import
/// row of that module, [`trust_ir::Module::verify_import`] accepts one of
/// `dependencies` (the recorded digest, name, producer and target all match),
/// and that dependency defines `h` (bodied, `External`) with a translation
/// equal to the body's ([`trust_cg_lower::translate_body_template`],
/// [`trust_cg_lower::Function::canonical_body_identity`]). The premise that
/// the body computes what the linked definition computes then rests on the
/// import binding the symbol to the authenticated dependency, not on the
/// producer's word — the obligation trust-ir states on
/// `Linkage::AvailableExternally` (`refuse/available_externally_inline_unauthenticated`).
/// A compile that makes a proof claim splices ONLY authenticated bodies.
#[derive(Debug, Clone, Copy, Default)]
pub struct InlineOnlyAuthority<'a> {
    /// Candidate dependency modules, in any order; each is consulted only
    /// through an import row it authenticates against.
    pub dependencies: &'a [&'a trust_ir::Module],
}

impl InlineOnlyBodyEvidence {
    /// The evidence of one inliner run: the bodies it `spliced`, the
    /// `withheld` candidates, and — of the admitted bodies — those an
    /// authenticated import discharges (kept only for bodies actually
    /// spliced).
    #[must_use]
    pub fn from_splices(
        spliced: Vec<InlineOnlyUse>,
        withheld: Vec<InlineOnlyWithheld>,
        authenticated: Vec<InlineOnlyAuthentication>,
    ) -> Self {
        let authenticated = authenticated
            .into_iter()
            .filter(|auth| spliced.iter().any(|use_| use_.name == auth.name))
            .collect();
        Self {
            spliced,
            withheld,
            authenticated,
        }
    }

    /// The evidence of a compile that makes a proof claim at O1 or above,
    /// whose shared LIR step does not run (module docs, "Proof claims"): no
    /// body is spliced, and every inline-only body of `module` (a bodied
    /// `AvailableExternally` function) is withheld, so every call to it stays
    /// a call. Sorted by name.
    #[must_use]
    pub fn withheld_for_proof_claim(module: &trust_ir::Module) -> Self {
        let mut withheld: Vec<InlineOnlyWithheld> = module
            .functions
            .iter()
            .filter(|function| {
                function.linkage == trust_ir::Linkage::AvailableExternally && function.has_body()
            })
            .map(|function| InlineOnlyWithheld {
                name: function.name.clone(),
                reason: PROOF_CLAIM_WITHHELD_REASON.to_string(),
            })
            .collect();
        withheld.sort_by(|a, b| a.name.cmp(&b.name));
        Self {
            spliced: Vec::new(),
            withheld,
            authenticated: Vec::new(),
        }
    }

    /// One sentence per DISCLOSED premise, in [`Self::spliced`] order: every
    /// spliced body [`Self::authenticated`] does not name.
    #[must_use]
    pub fn premises(&self) -> Vec<String> {
        self.spliced
            .iter()
            .filter(|use_| !self.authenticated.iter().any(|auth| auth.name == use_.name))
            .map(|use_| {
                format!(
                    "inline-only body of `{}` ({} site(s)) is assumed to compute what the \
                     definition `{}` binds to computes (one-definition rule; not checked by this \
                     compile)",
                    use_.name, use_.sites, use_.name
                )
            })
            .collect()
    }
}

/// What [`prepare_jit_lir_module`] did.
#[derive(Debug, Clone, Default)]
pub struct LirModulePreparation {
    /// Whether the step ran (false at O0, under a proof claim and under
    /// [`JIT_LIR_PREPARE_KILL_SWITCH`]).
    pub ran: bool,
    /// Whether the step did not run because the compile makes a proof claim
    /// at O1 or above (module docs, "Proof claims"; ruling OD-225): the LIR
    /// is exactly the adapter's, and [`Self::inline_only`] withholds every
    /// inline-only body of the module.
    pub skipped_for_proof_claim: bool,
    /// Inliner statistics, inline-only splices included.
    pub inline: InlineStats,
    /// Wall time of candidate translation plus inlining.
    pub inline_duration: Duration,
    /// Unsigned-range simplification statistics.
    pub range: LirUnsignedRangeStats,
    /// Wall time of unsigned-range simplification.
    pub range_duration: Duration,
    /// Inline-only body use: the disclosed premises and the withheld bodies.
    pub inline_only: InlineOnlyBodyEvidence,
}

impl LirModulePreparation {
    /// The `ir_inline` trace detail, in the AOT seam's spelling.
    #[must_use]
    pub fn inline_trace_detail(&self) -> String {
        let spliced: usize = self.inline_only.spliced.iter().map(|u| u.sites).sum();
        format!(
            "{} sites / {} rounds / {} inline-only site(s) from {} body(ies), {} withheld",
            self.inline.sites,
            self.inline.rounds,
            spliced,
            self.inline_only.spliced.len(),
            self.inline_only.withheld.len()
        )
    }

    /// The `lir_unsigned_range` trace detail, in the AOT seam's spelling.
    #[must_use]
    pub fn range_trace_detail(&self) -> String {
        format!(
            "{} uadd / {} umul / {} cmp / {} select / {} assert / {} branch",
            self.range.checked_adds_simplified,
            self.range.checked_muls_simplified,
            self.range.comparisons_folded,
            self.range.selects_folded,
            self.range.asserts_removed,
            self.range.branches_folded,
        )
    }
}

/// Read through the thread-scoped override layer, so a caller (or a test) can
/// switch the step off for one compile without touching the process
/// environment. Like every `TCG_*` control it is an unkeyed artifact-reuse
/// control: its presence disables compile-artifact reuse.
fn jit_lir_prepare_disabled() -> bool {
    crate::env_lock::var_os(JIT_LIR_PREPARE_KILL_SWITCH).is_some()
}

/// [`INLINE_ONLY_BODIES_KILL_SWITCH`], read like [`JIT_LIR_PREPARE_KILL_SWITCH`].
fn inline_only_bodies_disabled() -> bool {
    crate::env_lock::var_os(INLINE_ONLY_BODIES_KILL_SWITCH).is_some()
}

/// The inline-only bodies of `module` a compile may splice under `admission`,
/// translated by [`translate_inline_only_bodies`] (which withholds, with a
/// reason, every body this backend cannot or must not use under
/// `access_model`). Under [`InlineOnlyAdmission::Withhold`], or while
/// [`INLINE_ONLY_BODIES_KILL_SWITCH`] is set, every candidate is withheld and
/// its calls stay external calls. `withheld` is sorted by name.
///
/// The JIT step ([`prepare_jit_lir_module`]) and the AOT seam
/// (`Compiler::compile`) both admit candidates here, so the two splice the
/// same bodies under the same rules.
#[must_use]
pub fn admit_inline_only_bodies(
    module: &trust_ir::Module,
    guard_carrier_arch: GuardCarrierArch,
    access_model: ObjectAccessModel,
    license: &CodegenLicensePolicy,
    admission: InlineOnlyAdmission,
) -> InlineOnlyBodies {
    let admitted = admit_inline_only_bodies_with_authority(
        module,
        guard_carrier_arch,
        access_model,
        license,
        admission,
        InlineOnlyAuthority::default(),
    );
    InlineOnlyBodies {
        bodies: admitted.bodies,
        withheld: admitted.withheld,
    }
}

/// [`admit_inline_only_bodies`] with dependencies to authenticate bodies
/// against ([`InlineOnlyAuthority`]).
#[derive(Debug, Default)]
pub struct AdmittedInlineOnlyBodies {
    /// Bodies the compile may splice, in module order.
    pub bodies: Vec<(Function, ProofContext)>,
    /// Bodies not admitted, sorted by name.
    pub withheld: Vec<InlineOnlyWithheld>,
    /// Admitted bodies whose premise an authenticated import discharges,
    /// sorted by name.
    pub authenticated: Vec<InlineOnlyAuthentication>,
}

/// Admit `module`'s inline-only bodies under `admission`, authenticating each
/// against `authority` ([`InlineOnlyAuthority`]). A compile that makes no
/// proof claim admits every translated body (authenticated or not); one that
/// makes a proof claim admits only the authenticated ones. Under
/// [`INLINE_ONLY_BODIES_KILL_SWITCH`] nothing is admitted.
#[must_use]
pub fn admit_inline_only_bodies_with_authority(
    module: &trust_ir::Module,
    guard_carrier_arch: GuardCarrierArch,
    access_model: ObjectAccessModel,
    license: &CodegenLicensePolicy,
    admission: InlineOnlyAdmission,
    authority: InlineOnlyAuthority<'_>,
) -> AdmittedInlineOnlyBodies {
    let InlineOnlyBodies {
        bodies,
        mut withheld,
    } = translate_inline_only_bodies(module, guard_carrier_arch, access_model, license);
    let mut admitted = Vec::new();
    let mut authenticated = Vec::new();
    if inline_only_bodies_disabled() {
        let reason = format!(
            "kill switch: `{INLINE_ONLY_BODIES_KILL_SWITCH}` withholds every inline-only body"
        );
        withheld.extend(bodies.into_iter().map(|(function, _)| InlineOnlyWithheld {
            name: function.name,
            reason: reason.clone(),
        }));
    } else {
        for (function, context) in bodies {
            let authentication = authenticate_inline_only_body(
                module,
                &function,
                guard_carrier_arch,
                access_model,
                license,
                authority,
            );
            match (admission, authentication) {
                (_, Some(authentication)) => {
                    authenticated.push(authentication);
                    admitted.push((function, context));
                }
                (InlineOnlyAdmission::DisclosedPremise, None) => {
                    admitted.push((function, context));
                }
                (InlineOnlyAdmission::Withhold, None) => withheld.push(InlineOnlyWithheld {
                    name: function.name,
                    reason: "proof-producing compile: an inline-only body is spliced only when \
                             an authenticated import exports an equal definition, and no \
                             supplied dependency authenticates one"
                        .to_string(),
                }),
            }
        }
    }
    withheld.sort_by(|a, b| a.name.cmp(&b.name));
    authenticated.sort_by(|a, b| a.name.cmp(&b.name));
    AdmittedInlineOnlyBodies {
        bodies: admitted,
        withheld,
        authenticated,
    }
}

/// The authentication of the inline-only body `body` of `module`, if an
/// import row of `module` that `verify_import` accepts against one of
/// `authority.dependencies` names a dependency exporting an equal
/// definition ([`InlineOnlyAuthority`]).
fn authenticate_inline_only_body(
    module: &trust_ir::Module,
    body: &Function,
    guard_carrier_arch: GuardCarrierArch,
    access_model: ObjectAccessModel,
    license: &CodegenLicensePolicy,
    authority: InlineOnlyAuthority<'_>,
) -> Option<InlineOnlyAuthentication> {
    if authority.dependencies.is_empty() || module.imports.is_empty() {
        return None;
    }
    let body_identity = body.canonical_body_identity()?;
    let hashed: Vec<trust_ir::imports::HashedModule<'_>> = authority
        .dependencies
        .iter()
        .map(|dependency| trust_ir::imports::HashedModule::new(dependency))
        .collect();
    for index in 0..module.imports.len() {
        let id = trust_ir::ImportId::new(u32::try_from(index).ok()?);
        for dependency in &hashed {
            let Ok(verified) = module.verify_import_hashed(id, dependency) else {
                continue;
            };
            let dependency_module = verified.module();
            let Some(definition) = dependency_module.functions.iter().find(|function| {
                function.name == body.name
                    && function.has_body()
                    && function.linkage == trust_ir::Linkage::External
            }) else {
                continue;
            };
            let Ok((translated, _)) = translate_body_template(
                dependency_module,
                definition,
                guard_carrier_arch,
                access_model,
                license,
            ) else {
                continue;
            };
            if translated.canonical_body_identity().as_deref() == Some(body_identity.as_str()) {
                return Some(InlineOnlyAuthentication {
                    name: body.name.clone(),
                    dependency: verified.import().name.clone(),
                    digest: verified
                        .digest()
                        .bytes
                        .iter()
                        .map(|byte| format!("{byte:02x}"))
                        .collect(),
                });
            }
        }
    }
    None
}

/// Run the shared pre-ISel LIR module step on a JIT compile's LIR (module
/// docs).
///
/// `lir` must be the LIR a `trust_cg_lower` translation entry produced from
/// `module` — the exact module it admitted, e.g. a
/// [`trust_cg_lower::PreparedModuleForLir`]'s — with its exact-binding report
/// already replayed. `guard_carrier_arch` and `tls_dialect` are that
/// translation's; `bindings` names what the JIT link will bind explicitly
/// ([`JitExternBindings`]). Under the proof-claim admission
/// ([`InlineOnlyAdmission::Withhold`]) the step runs neither pass and leaves
/// `lir` untouched (module docs, "Proof claims"). Returns what ran; fails only
/// when the inliner's fail-closed self-check does ([`CompileError::IrInline`]),
/// never because an inline-only body was unusable.
#[allow(clippy::too_many_arguments)]
pub fn prepare_jit_lir_module(
    lir: &mut [(Function, ProofContext)],
    module: &trust_ir::Module,
    guard_carrier_arch: GuardCarrierArch,
    tls_dialect: TlsDialect,
    opt_level: OptLevel,
    admission: InlineOnlyAdmission,
    license: &CodegenLicensePolicy,
    bindings: JitExternBindings<'_>,
) -> Result<LirModulePreparation, CompileError> {
    prepare_jit_lir_module_with_authority(
        lir,
        module,
        guard_carrier_arch,
        tls_dialect,
        opt_level,
        admission,
        license,
        bindings,
        InlineOnlyAuthority::default(),
    )
}

/// [`prepare_jit_lir_module`] that may authenticate inline-only bodies
/// against `authority` ([`InlineOnlyAuthority`]): an authenticated body's
/// premise is discharged instead of disclosed, and it is the only kind a
/// proof-claiming compile splices.
#[allow(clippy::too_many_arguments)]
pub fn prepare_jit_lir_module_with_authority(
    lir: &mut [(Function, ProofContext)],
    module: &trust_ir::Module,
    guard_carrier_arch: GuardCarrierArch,
    tls_dialect: TlsDialect,
    opt_level: OptLevel,
    admission: InlineOnlyAdmission,
    license: &CodegenLicensePolicy,
    bindings: JitExternBindings<'_>,
    authority: InlineOnlyAuthority<'_>,
) -> Result<LirModulePreparation, CompileError> {
    prepare_jit_lir_module_never_inlining(
        lir,
        module,
        guard_carrier_arch,
        tls_dialect,
        opt_level,
        admission,
        license,
        bindings,
        authority,
        &std::collections::BTreeSet::new(),
    )
}

/// [`prepare_jit_lir_module_with_authority`] that also never splices a body
/// named in `never_inline` (the compiler's
/// [`crate::CompilerConfig::never_inline`]): a call to one stays a call.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare_jit_lir_module_never_inlining(
    lir: &mut [(Function, ProofContext)],
    module: &trust_ir::Module,
    guard_carrier_arch: GuardCarrierArch,
    tls_dialect: TlsDialect,
    opt_level: OptLevel,
    admission: InlineOnlyAdmission,
    license: &CodegenLicensePolicy,
    bindings: JitExternBindings<'_>,
    authority: InlineOnlyAuthority<'_>,
    never_inline: &std::collections::BTreeSet<String>,
) -> Result<LirModulePreparation, CompileError> {
    let mut preparation = LirModulePreparation::default();
    if opt_level == OptLevel::O0 || jit_lir_prepare_disabled() || lir.is_empty() {
        return Ok(preparation);
    }
    if !unvalidated_lir_passes_run(opt_level, admission.makes_proof_claim()) {
        // Ruling OD-225 (module docs, "Proof claims"): neither pass is
        // validated, so a compile that makes a proof claim keeps the adapter's
        // LIR as the source of every proof downstream.
        preparation.skipped_for_proof_claim = true;
        preparation.inline_only = InlineOnlyBodyEvidence::withheld_for_proof_claim(module);
        return Ok(preparation);
    }
    preparation.ran = true;

    let inline_start = Instant::now();
    let candidates = admit_inline_only_bodies_with_authority(
        module,
        guard_carrier_arch,
        ObjectAccessModel::from(tls_dialect),
        license,
        admission,
        authority,
    );
    let (bodies, withheld) = (candidates.bodies, candidates.withheld);
    // An explicit extern binding interposes on a non-local module definition
    // of its name (module docs, "Binding in the JIT"): never splice one, nor
    // a body the caller marked never-inline.
    let mut interposable = jit_interposable_definitions(module, bindings);
    interposable.extend(never_inline.iter().cloned());
    let report =
        inline_module_with_inline_only_bodies(lir, &bodies, &interposable).map_err(|error| {
            CompileError::IrInline {
                detail: error.to_string(),
            }
        })?;
    preparation.inline_duration = inline_start.elapsed();
    preparation.inline = report.stats;
    preparation.inline_only = InlineOnlyBodyEvidence::from_splices(
        report.inline_only_uses.clone(),
        withheld,
        candidates.authenticated,
    );

    // After inlining (which can expose new masked operands), before ISel —
    // but, unlike the AOT seam's whole-module pass, only over the functions
    // the inliner changed. Measured on the 139-module JIT compile corpus
    // (2026-09-28): the whole-module pass folded nothing and cost 0.65% of
    // every JIT compile's instructions, 97% of this step's cost; a function
    // the inliner did not touch keeps its pre-step LIR exactly.
    let range_start = Instant::now();
    preparation.range = simplify_functions_at(lir, &report.changed_functions);
    preparation.range_duration = range_start.elapsed();
    Ok(preparation)
}
