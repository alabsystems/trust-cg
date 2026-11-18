//! INGESTION ADMISSION (roadmap WS7.3, finding F-113): every entry that takes
//! a trust-ir module from outside the backend and lowers it refuses exactly
//! what trust-ir's own codegen validator refuses.
//!
//! # The hole this closes
//!
//! Before WS7.3 the object/CLI path (`Compiler::compile`), the host JIT and the
//! wasm lane enforced only the v41 codegen LICENSE and otherwise lowered
//! whatever they were handed. The adapter's own trust-ir walk
//! (`validate_codegen_prerequisites`) refuses a NAMED subset of findings and
//! deliberately tolerates the rest, because the adapter's diagnostic entries
//! are also used on partially built modules. So a module trust-ir refuses — an
//! `Int(0)` seed at a `RefMut` tuple lane (`ConstTypeMismatch`, the c06(g)
//! shape), a store-form `InsertField`, an overlapping `StructDef` — compiled.
//!
//! # The rule
//!
//! [`admit_module`] is the one admission every ingestion entry runs:
//!
//! 1. the backend's [`CodegenLicensePolicy`] (`enforce_module`) — first, so a
//!    license refusal keeps the adapter's named `UngatedBody` /
//!    `UnlicensedBody` / `UnrecognizedGateAuthority` diagnostics; authority
//!    RECOGNITION stays the consumer's, per the ratified design;
//! 2. trust-ir's composed codegen admission,
//!    [`trust_ir_build::validate_module_for_codegen_with`]: the structural
//!    validator, the license-EVIDENCE layer, the lowerability layer and the
//!    `global_asm` layer — under the authority tier's import policy, so a
//!    PROOF-BEARING import row is `UnauthenticatedImport` (this entry holds no
//!    dependency module; WS7.9's `--link` is what may supply one). Claim-less
//!    bodies are admitted exactly when the policy permits them: trust-ir's
//!    claim-less policy is the license policy's own verdict
//!    ([`CodegenLicensePolicy::trust_ir_unlicensed_policy`]), so
//!    `UnlicensedBodyForCodegen` is raised exactly for the bodies step 1
//!    refuses, and never for a permitted one;
//! 3. every finding is a refusal. The findings the adapter already consumes
//!    by name keep their own refusal ([`crate::adapter::AdapterError`]'s
//!    `InvalidRefinement`, `TrustIrAdmissionRefused`, the G18-1 `Dealloc`
//!    refusal, …); every other finding is
//!    [`AdapterError::InvalidTrustIrModule`], naming each finding.
//!
//! The exemptions are consumer-owned knowledge, not tolerances: trust-ir's
//! lowerability layer refuses a `DialectOp` whose namespace is outside its
//! in-tree list ("no registered lowering"). A namespace the CONSUMER's
//! registry registers has one. The caller passes those namespaces
//! (`lowerable_dialects`); only an `UnlowerableForCodegen { inst:
//! "DialectOp" }` finding whose text is EXACTLY trust-ir's "unknown dialect
//! namespace <ns>: no registered lowering" for a registered `<ns>` is dropped.
//! Any other spelling (a later pin rewording the detail) stays a refusal —
//! the fail-closed direction.
//!
//! A linked compile also holds an `AuthenticatedImportSet` earned by the
//! complete dependency walk. Only for its exact bound root, this supplies
//! the import context the standalone validator lacks: authenticated import
//! rows and the exact inherited obligations already discharged by that walk.
//! Other findings remain refusals, including local unreplayed certificates.
//!
//! # The typestate
//!
//! [`AdmittedModule`] can be constructed only here. The production adapter
//! entries the ingestion paths lower through take it instead of a bare
//! `&Module`, so a new ingestion entry cannot reach them without admission;
//! `trust-cg-codegen`'s `tests/ingest_admission.rs` enumerates every public
//! `compile*` / `translate_*` entry that accepts a trust-ir module and holds
//! each to admission or to a named, shrink-only diagnostic allowlist.
//!
//! # Validating what is LOWERED
//!
//! A pre-adapter rewrite produces new core IR nothing else checks. A caller
//! that rewrites the admitted module (the codegen crate's dialect lowering)
//! re-admits the REWRITTEN module with [`AdmittedModule::readmit_rewritten`]
//! before lowering it, recording [`AdmissionStage::Rewritten`] so a refusal
//! says which module failed.

use std::fmt;

use trust_ir::Module;
use trust_ir_build::ValidationError;

use crate::adapter::{AdapterError, named_validation_refusal};
use crate::codegen_license::CodegenLicensePolicy;

/// The proof authority of the authority tier: replays nothing. Selecting it
/// through `ValidationConfig::with_authority` changes exactly one thing
/// relative to `ValidationConfig::pinned()` — the import policy becomes
/// REFUSE — which is why it is used here.
static REJECTING_AUTHORITY: trust_ir::proof::RejectingModuleProofAuthority =
    trust_ir::proof::RejectingModuleProofAuthority;

/// How many findings [`InvalidTrustIr`]'s `Display` spells (each as
/// `<variant>: <trust-ir's text>`) before it summarizes the rest as a count.
/// The payload always carries every finding.
pub const INVALID_TRUST_IR_NAMED_FINDINGS: usize = 3;

/// Which module an admission judged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AdmissionStage {
    /// The module exactly as the caller handed it to the backend.
    Received,
    /// The module a backend-owned pre-adapter rewrite (dialect lowering)
    /// produced from an admitted module.
    Rewritten,
}

impl AdmissionStage {
    /// Stable token for diagnostics.
    #[must_use]
    pub const fn token(self) -> &'static str {
        match self {
            AdmissionStage::Received => "received",
            AdmissionStage::Rewritten => "after pre-adapter rewrite",
        }
    }
}

/// trust-ir's validator refused a module at an ingestion entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvalidTrustIr {
    /// `Module::name` of the refused module.
    pub module: String,
    /// Which module was judged.
    pub stage: AdmissionStage,
    /// EVERY finding, in trust-ir's order (structural first, then the
    /// license, lowerability and `global_asm` layers). Never empty.
    pub errors: Vec<ValidationError>,
}

impl InvalidTrustIr {
    /// Whether some finding satisfies `predicate` (test and diagnostic aid).
    pub fn any(&self, predicate: impl Fn(&ValidationError) -> bool) -> bool {
        self.errors.iter().any(predicate)
    }
}

impl fmt::Display for InvalidTrustIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "trust-ir validation refused module `{}` ({}): {} finding(s): ",
            self.module,
            self.stage.token(),
            self.errors.len()
        )?;
        for (index, error) in self
            .errors
            .iter()
            .take(INVALID_TRUST_IR_NAMED_FINDINGS)
            .enumerate()
        {
            if index > 0 {
                f.write_str("; ")?;
            }
            write!(f, "{}: {error}", finding_name(error))?;
        }
        let rest = self
            .errors
            .len()
            .saturating_sub(INVALID_TRUST_IR_NAMED_FINDINGS);
        if rest > 0 {
            write!(f, "; and {rest} more")?;
        }
        Ok(())
    }
}

impl std::error::Error for InvalidTrustIr {}

/// The `ValidationError` variant name of `error` (its `Debug` spelling up to
/// the payload), so a refusal names the rule as well as trust-ir's text.
fn finding_name(error: &ValidationError) -> String {
    format!("{error:?}")
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .next()
        .unwrap_or_default()
        .to_string()
}

/// Whether `error` is trust-ir's "no registered lowering" refusal of a
/// `DialectOp` namespace in `lowerable_dialects` — matched on trust-ir's exact
/// text, so any other spelling (a later pin rewording the detail) stays a
/// refusal.
fn exempt_by_consumer_registry(error: &ValidationError, lowerable_dialects: &[&str]) -> bool {
    let ValidationError::UnlowerableForCodegen {
        inst: "DialectOp",
        detail,
        ..
    } = error
    else {
        return false;
    };
    detail
        .strip_prefix("unknown dialect namespace ")
        .and_then(|rest| rest.strip_suffix(": no registered lowering"))
        .is_some_and(|namespace| lowerable_dialects.contains(&namespace))
}

/// A module an ingestion entry admitted: trust-ir's codegen admission found
/// nothing (after the one consumer-owned exemption) and the license policy
/// permits every body. Constructible only by [`admit_module`] and
/// [`AdmittedModule::readmit_rewritten`].
#[derive(Debug, Clone)]
pub struct AdmittedModule<'m> {
    module: &'m Module,
    license: CodegenLicensePolicy,
    lowerable_dialects: Vec<String>,
    stage: AdmissionStage,
}

impl<'m> AdmittedModule<'m> {
    /// The admitted module.
    #[must_use]
    pub fn module(&self) -> &'m Module {
        self.module
    }

    /// The license policy the module was admitted under; the adapter entries
    /// that take an [`AdmittedModule`] lower under exactly this policy.
    #[must_use]
    pub fn license(&self) -> &CodegenLicensePolicy {
        &self.license
    }

    /// Which module was admitted.
    #[must_use]
    pub fn stage(&self) -> AdmissionStage {
        self.stage
    }

    /// The `DialectOp` namespaces the consumer declared lowerable at
    /// admission.
    #[must_use]
    pub fn lowerable_dialects(&self) -> &[String] {
        &self.lowerable_dialects
    }

    /// Re-admit `rewritten`, the output of a backend-owned pre-adapter
    /// rewrite of this admitted module, under the same license policy and
    /// the same lowerable dialects. The rewrite produced IR nothing else has
    /// checked.
    pub fn readmit_rewritten<'r>(
        &self,
        rewritten: &'r Module,
    ) -> Result<AdmittedModule<'r>, AdapterError> {
        self.readmit_rewritten_with_runtime_bindings(rewritten, &[])
    }

    /// [`Self::readmit_rewritten`] for a rewrite that may BIND RUNTIME CALLS:
    /// replace a dialect op by a call to a runtime entry it declares in the
    /// rewritten module (a bodyless `External` declaration — an FFI boundary).
    /// `runtime_symbols` names every runtime entry the caller's rewrite may
    /// bind (the consumer's registry declares each one's C ABI).
    ///
    /// The one finding this excuses is trust-ir's `TargetInfoRequired`, and
    /// only when ALL of these hold — the backend's own rewrite introduced the
    /// boundary, so the rewrite's ABI is the registration's under the compile
    /// target, exactly as the rewrite's own re-validation admits it:
    ///
    /// * the RECEIVED module (admitted, so it had no FFI boundary of its own)
    ///   and the rewritten one both carry no `target_info`;
    /// * every bodyless declaration of the rewritten module that the received
    ///   module did not declare under the same name is in `runtime_symbols`,
    ///   and there is at least one;
    /// * the finding's boundary names one of those added runtime entries.
    ///
    /// Every other finding refuses as in [`Self::readmit_rewritten`]. The
    /// residual, stated: trust-ir names only the FIRST boundary, so once that
    /// one is excused a second boundary is reported by no rule. The census of
    /// added declarations above is total, so a second boundary can only be a
    /// call edge whose convention differs from its caller's that the rewrite
    /// itself emitted (a runtime call is one).
    pub fn readmit_rewritten_with_runtime_bindings<'r>(
        &self,
        rewritten: &'r Module,
        runtime_symbols: &[&str],
    ) -> Result<AdmittedModule<'r>, AdapterError> {
        let lowerable: Vec<&str> = self.lowerable_dialects.iter().map(String::as_str).collect();
        let added = added_runtime_declarations(self.module, rewritten, runtime_symbols);
        let excused = |error: &ValidationError| match (&added, error) {
            (Some(added), ValidationError::TargetInfoRequired { boundary }) => added
                .iter()
                .any(|symbol| boundary.contains(&format!("`{symbol}`"))),
            _ => false,
        };
        // A linked compile's import authentication binds the received
        // module; it moves onto the rewrite only when the rewrite kept every
        // table an admission reads (WS7.9,
        // `CodegenLicensePolicy::for_backend_rewrite`), else refused.
        let license = self.license.for_backend_rewrite(self.module, rewritten)?;
        admit_at(
            rewritten,
            &license,
            &lowerable,
            AdmissionStage::Rewritten,
            &excused,
        )
    }
}

/// The runtime entries a rewrite of `received` into `rewritten` declared, when
/// the excusal of [`AdmittedModule::readmit_rewritten_with_runtime_bindings`]
/// can apply at all: both modules target-free, at least one added bodyless
/// declaration, and every added bodyless declaration a `runtime_symbols`
/// entry. `None` otherwise (nothing is excused).
fn added_runtime_declarations<'r>(
    received: &Module,
    rewritten: &'r Module,
    runtime_symbols: &[&str],
) -> Option<Vec<&'r str>> {
    if received.target_info.is_some() || rewritten.target_info.is_some() {
        return None;
    }
    let declared: std::collections::BTreeSet<&str> = received
        .functions
        .iter()
        .filter(|function| function.is_declaration())
        .map(|function| function.name.as_str())
        .collect();
    let added: Vec<&str> = rewritten
        .functions
        .iter()
        .filter(|function| function.is_declaration() && !declared.contains(function.name.as_str()))
        .map(|function| function.name.as_str())
        .collect();
    (!added.is_empty() && added.iter().all(|symbol| runtime_symbols.contains(symbol)))
        .then_some(added)
}

/// Admit `module` for codegen under `license` (see the module docs for the
/// rule). `lowerable_dialects` names the `DialectOp` namespaces the caller's
/// pre-adapter registry lowers (empty: trust-ir's in-tree list only).
pub fn admit_module<'m>(
    module: &'m Module,
    license: &CodegenLicensePolicy,
    lowerable_dialects: &[&str],
) -> Result<AdmittedModule<'m>, AdapterError> {
    admit_at(
        module,
        license,
        lowerable_dialects,
        AdmissionStage::Received,
        &|_| false,
    )
}

fn admit_at<'m>(
    module: &'m Module,
    license: &CodegenLicensePolicy,
    lowerable_dialects: &[&str],
    stage: AdmissionStage,
    excused: &dyn Fn(&ValidationError) -> bool,
) -> Result<AdmittedModule<'m>, AdapterError> {
    license.enforce_module(module)?;
    let errors: Vec<ValidationError> = admission_findings(module, license, lowerable_dialects)
        .into_iter()
        .filter(|error| !excused(error))
        .collect();
    if let Some(refusal) = errors
        .iter()
        .find_map(|error| named_validation_refusal(module, license.box_validity_floor(), error))
    {
        return Err(refusal);
    }
    if !errors.is_empty() {
        return Err(AdapterError::InvalidTrustIrModule(InvalidTrustIr {
            module: module.name.clone(),
            stage,
            errors,
        }));
    }
    Ok(AdmittedModule {
        module,
        license: license.clone(),
        lowerable_dialects: lowerable_dialects
            .iter()
            .map(|namespace| (*namespace).to_owned())
            .collect(),
        stage,
    })
}

/// trust-ir's codegen admission findings for `module` under `license`, minus
/// the consumer-owned dialect exemption. Empty means admitted (the license
/// verdict aside, which [`admit_module`] decides first).
#[must_use]
pub fn admission_findings(
    module: &Module,
    license: &CodegenLicensePolicy,
    lowerable_dialects: &[&str],
) -> Vec<ValidationError> {
    let config = trust_ir_build::ValidationConfig::pinned().with_authority(&REJECTING_AUTHORITY);
    // The claim-less verdict is the license policy's, stated in trust-ir's
    // type by `codegen_license` (the one file the Permit census lets name a
    // Permit); this entry decides nothing about it.
    // trust-ir v74 `Inst::BoxDeref` is held to the license policy's floor
    // (default: refuse); the finding is named by the shared classifier in
    // `named_validation_refusal`.
    let admission = crate::box_deref::admission_at(
        trust_ir_build::CodegenAdmission::from_config(config)
            .with_unlicensed(license.trust_ir_unlicensed_policy()),
        license.box_validity_floor(),
    );
    let linked = license
        .authenticated_imports()
        .and_then(|imports| imports.bind_for_ingestion(module));
    // A Box floor finding is discharged only at a license floor that
    // consults this backend's re-derivation (never the default `Refuse`) and
    // only when its conjunct is re-derived from the function itself, by the
    // shared acceptance check's own predicate; every other finding stands.
    let box_floor = license.box_validity_floor();
    let mut rederiver = crate::box_deref::ModuleRederiver::new(module);
    trust_ir_build::validate_module_for_codegen_with(module, &admission)
        .into_iter()
        .filter(|error| {
            !crate::box_deref::discharged_by_rederivation(&mut rederiver, box_floor, error)
        })
        .filter(|error| !linked.as_ref().is_some_and(|imports| imports.covers(error)))
        .filter(|error| !exempt_by_consumer_registry(error, lowerable_dialects))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Ty, ValueId,
    };

    /// `entry: () -> i64` returning 7: target-free, no FFI boundary.
    fn received() -> Module {
        let mut module = Module::new("ws7_3_runtime_binding");
        let sig = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
        entry.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(7),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        });
        module.functions.push(entry);
        module
    }

    /// `received` with each of `symbols` declared bodyless `() -> i64` and
    /// called from `entry` (what a runtime-call rewrite produces).
    fn rewritten_with(symbols: &[&str]) -> Module {
        let mut module = received();
        let sig = module.functions[0].ty;
        let mut calls = Vec::new();
        for (index, symbol) in symbols.iter().enumerate() {
            let id = FuncId::new(u32::try_from(index + 1).expect("small"));
            module
                .functions
                .push(Function::new(id, *symbol, sig, BlockId::new(0)));
            calls.push(
                InstrNode::new(Inst::Call {
                    callee: id,
                    args: vec![],
                })
                .with_result(ValueId::new(u32::try_from(index + 1).expect("small"))),
            );
        }
        let body = &mut module.functions[0].blocks[0].body;
        for (offset, call) in calls.into_iter().enumerate() {
            body.insert(offset, call);
        }
        module
    }

    /// The policy these fixtures are admitted under. They are hand-built and
    /// claim-less (`body_gate: None`), which the default policy refuses
    /// (DG-73, `the_default_policy_refuses_the_claim_less_fixture`), so they
    /// state `Permit`, the workspace's test spelling. Every rule these tests
    /// pin is decided after the license.
    fn permitting() -> CodegenLicensePolicy {
        CodegenLicensePolicy::default()
            .with_unlicensed(crate::codegen_license::UnlicensedBodyPolicy::Permit)
    }

    fn admitted(module: &Module) -> AdmittedModule<'_> {
        admit_module(module, &permitting(), &[]).expect("admitted")
    }

    /// The default policy refuses the claim-less fixture by its license, at
    /// this entry, before trust-ir's admission is consulted.
    #[test]
    fn the_default_policy_refuses_the_claim_less_fixture() {
        let source = received();
        let error = admit_module(&source, &CodegenLicensePolicy::default(), &[])
            .expect_err("a claim-less body is refused by default");
        assert!(
            matches!(&error, AdapterError::UnlicensedBody { function } if function == "entry"),
            "{error:?}"
        );
    }

    fn target_info_required(error: AdapterError) -> bool {
        matches!(
            error,
            AdapterError::InvalidTrustIrModule(InvalidTrustIr { ref errors, stage: AdmissionStage::Rewritten, .. })
                if errors.iter().any(|error| matches!(error, ValidationError::TargetInfoRequired { .. }))
        )
    }

    #[test]
    fn a_bound_runtime_declaration_is_admitted_in_a_target_free_rewrite() {
        let source = received();
        let received = admitted(&source);
        let rewritten = rewritten_with(&["tcg_runtime_entry"]);
        let readmitted = received
            .readmit_rewritten_with_runtime_bindings(&rewritten, &["tcg_runtime_entry"])
            .expect("the bound runtime entry is the registration's ABI");
        assert_eq!(readmitted.stage(), AdmissionStage::Rewritten);
    }

    /// The plain re-admission excuses nothing: the same rewrite is refused.
    #[test]
    fn the_plain_readmission_refuses_the_runtime_declaration() {
        let source = received();
        let rewritten = rewritten_with(&["tcg_runtime_entry"]);
        let error = admitted(&source)
            .readmit_rewritten(&rewritten)
            .expect_err("no runtime binding is named");
        assert!(target_info_required(error));
    }

    /// A declaration the registry does not bind is an FFI boundary the rewrite
    /// has no ABI for: refused, also when it sits beside a bound one.
    #[test]
    fn an_unbound_added_declaration_is_refused() {
        let source = received();
        for symbols in [
            &["not_a_runtime_entry"][..],
            &["tcg_runtime_entry", "not_a_runtime_entry"][..],
            &["not_a_runtime_entry", "tcg_runtime_entry"][..],
        ] {
            let rewritten = rewritten_with(symbols);
            let error = admitted(&source)
                .readmit_rewritten_with_runtime_bindings(&rewritten, &["tcg_runtime_entry"])
                .expect_err("an unbound declaration is refused");
            assert!(target_info_required(error), "{symbols:?}");
        }
    }

    /// A rewrite that adds NO declaration excuses nothing (an empty census).
    #[test]
    fn only_added_declarations_are_excused() {
        let source = received();
        let rewritten = received();
        assert!(added_runtime_declarations(&source, &rewritten, &["tcg_runtime_entry"]).is_none());
        // A module that already names a target is never excused (it needs
        // no excuse, and its target is the one the ABI is checked against).
        let mut pinned = rewritten_with(&["tcg_runtime_entry"]);
        pinned.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        assert!(added_runtime_declarations(&source, &pinned, &["tcg_runtime_entry"]).is_none());
    }

    /// The excusal is the one finding: any OTHER finding of the rewritten
    /// module still refuses (here a call that binds no result of a callee
    /// that returns one is not the point; a duplicate value definition is).
    #[test]
    fn every_other_finding_still_refuses_beside_a_bound_runtime_entry() {
        let source = received();
        let mut rewritten = rewritten_with(&["tcg_runtime_entry"]);
        // Redefine %0 (already the constant): `DuplicateValueDef`, a finding
        // the adapter refuses by name.
        rewritten.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(0)),
        );
        let error = admitted(&source)
            .readmit_rewritten_with_runtime_bindings(&rewritten, &["tcg_runtime_entry"])
            .expect_err("a duplicate definition is refused");
        assert!(
            matches!(error, AdapterError::InvalidTrustIr(_)),
            "{error:?}"
        );
    }

    #[test]
    fn the_dialect_exemption_matches_trust_irs_exact_text_only() {
        let finding = |detail: &str| ValidationError::UnlowerableForCodegen {
            function: 0,
            name: "f".into(),
            block: 0,
            inst: "DialectOp",
            detail: detail.to_string(),
        };
        let registered = ["acme"];
        assert!(exempt_by_consumer_registry(
            &finding("unknown dialect namespace acme: no registered lowering"),
            &registered
        ));
        for detail in [
            "unknown dialect namespace acme2: no registered lowering",
            "unknown dialect namespace acm: no registered lowering",
            "unknown dialect namespace acme: no registered lowering (reworded)",
            "unknown dialect namespace acme:  no registered lowering",
            "dialect namespace acme: no registered lowering",
        ] {
            assert!(
                !exempt_by_consumer_registry(&finding(detail), &registered),
                "{detail}"
            );
        }
        // The same text on another instruction is never exempt.
        let other = ValidationError::UnlowerableForCodegen {
            function: 0,
            name: "f".into(),
            block: 0,
            inst: "Dealloc",
            detail: "unknown dialect namespace acme: no registered lowering".into(),
        };
        assert!(!exempt_by_consumer_registry(&other, &registered));
    }
}
