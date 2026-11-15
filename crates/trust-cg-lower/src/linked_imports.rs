// trust-cg-lower/linked_imports.rs - authenticated cross-crate imports (WS7.9)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Authenticated cross-crate imports (roadmap WS7.9).
//!
//! A trust-ir module records its dependencies in `Module::imports` (v41) and
//! may discharge an obligation by INHERITING a dependency's discharged
//! obligation (`ProofEvidence::InheritedFromCallee { external: Some(_) }`).
//! A single-module consumer cannot check either claim, so the shared adapter
//! floor refuses every such certificate
//! ([`AdapterError::ExternalEvidenceInheritance`]).
//!
//! This module is the one way to lift that refusal: run trust-ir's linked
//! validator, `trust_ir_build::validate_linked_module`, over the root and the
//! dependency modules the caller supplies, under
//! `RejectingModuleProofAuthority` (trust-cg replays no solver verdict of its
//! own). The linked walk authenticates EVERY import row of the root against
//! the supplied modules' stable digests (cited or not), resolves every call
//! edge to a body-less declaration against the defining dependency with a
//! structurally equal signature, validates every dependency under the same
//! rules, and re-earns each cross-crate inheritance. Only when the whole walk
//! is clean does [`authenticate_linked_imports`] return an
//! [`AuthenticatedImportSet`]: the root's digest, every authenticated row,
//! and exactly the inheritance certificates the walk admitted.
//!
//! The set is carried to the adapter with the codegen license
//! ([`crate::CodegenLicensePolicy::with_authenticated_imports`]), the one
//! per-compile admission policy that reaches every license-aware entry.
//! [`crate::CodegenLicensePolicy::enforce_module`] binds it to the exact
//! module being compiled (its stable digest), and the floor admits an
//! external inheritance only when its lineage reference is in the set AND the
//! import row it names is the authenticated row. An entry that does not carry
//! the license keeps the unconditional refusal.
//!
//! What an admitted certificate is NOT: codegen authority. It is data. The
//! backend takes no lowering decision from it, so admitting it changes no
//! emitted byte; it only stops refusing a module whose cross-crate proof
//! claim has been authenticated.
//!
//! What the digest authenticates is the dependency MODULE, not the object file
//! a later link step binds. [`AuthenticatedImportSet::dependencies`] lists
//! every authenticated `(name, digest, producer)` so a link step (or a human)
//! can bind the object to the module it was compiled from; nothing here
//! claims that binding.

use std::collections::BTreeSet;
use std::fmt;

use trust_ir::proof::{
    ProofCertificate, ProofCertificateRef, ProofDigest, ProofEvidence, ProofObligation,
    RejectingModuleProofAuthority,
};
use trust_ir::{ExternRef, ImportId, ImportVerificationError, Module, ModuleImport};
use trust_ir_build::{ImportResolver, ModuleSet, ValidationError, validate_linked_module};

/// One import row of the root that the linked walk authenticated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkedDependency {
    /// The row's id in the root's import table.
    pub import: ImportId,
    /// The exact authenticated row: name, digest, producer and scheme.
    pub row: ModuleImport,
}

/// One admitted cross-crate inheritance, as the linked walk saw it in the
/// root: the certificate's lineage reference, the LOCAL obligation it
/// discharges, and the name of the local callee its evidence names.
///
/// `lineage_ref` digests only the certificate (obligation id, prover,
/// evidence), never the obligation it discharges, so without the obligation
/// a module that kept the certificate but rewrote the claim (`ensures (= 1
/// 2)` for `ensures (= 1 1)`) would match. The floor compares all three.
#[derive(Debug, Clone, PartialEq)]
struct AdmittedInheritance {
    reference: ProofCertificateRef,
    obligation: ProofObligation,
    callee: String,
}

/// What [`authenticate_linked_imports`] re-earned for ONE root module.
///
/// Constructible only by [`authenticate_linked_imports`] (or, under the
/// test-only `mutation-knobs` feature, by its deliberately unsound skip), so
/// holding one means the complete linked walk accepted the root it names.
/// [`Self::rebind_to_backend_rewrite`] moves it onto the backend's own
/// rewrite of that root, and only when the rewrite keeps the root's name,
/// import table and proof tables.
#[derive(Debug, Clone, PartialEq)]
pub struct AuthenticatedImportSet {
    root_name: String,
    root_digest: ProofDigest,
    dependencies: Vec<LinkedDependency>,
    admitted: BTreeSet<ProofCertificateRef>,
    inheritances: Vec<AdmittedInheritance>,
}

// `ProofObligation` is `PartialEq` only; its equality is still an equivalence
// on every obligation a validated module can carry, which is all a set holds.
impl Eq for AuthenticatedImportSet {}

/// A linked context bound once to the immutable module being admitted.
pub(crate) struct BoundIngestionImports<'a> {
    imports: &'a AuthenticatedImportSet,
    _module: &'a Module,
}

impl BoundIngestionImports<'_> {
    /// Only findings caused by the standalone validator's missing context.
    pub(crate) fn covers(&self, finding: &ValidationError) -> bool {
        match finding {
            ValidationError::UnauthenticatedImport { import, .. } => self
                .imports
                .dependencies
                .iter()
                .any(|dependency| dependency.import.index() == *import),
            ValidationError::DischargedWithoutCertificate { obligation } => self
                .imports
                .inheritances
                .iter()
                .any(|inheritance| inheritance.obligation.id.index() == *obligation),
            _ => false,
        }
    }
}

impl AuthenticatedImportSet {
    /// `Module::name` of the root this set was authenticated for.
    #[must_use]
    pub fn root_name(&self) -> &str {
        &self.root_name
    }

    /// `Module::stable_digest` of the root this set was authenticated for.
    #[must_use]
    pub fn root_digest(&self) -> &ProofDigest {
        &self.root_digest
    }

    /// Every import row of the root, each authenticated against a supplied
    /// dependency module, in `ImportId` order.
    #[must_use]
    pub fn dependencies(&self) -> &[LinkedDependency] {
        &self.dependencies
    }

    /// The inheritance certificates whose cross-crate claim re-earned.
    #[must_use]
    pub fn admitted_certificates(&self) -> &BTreeSet<ProofCertificateRef> {
        &self.admitted
    }

    /// Bind the exact root once, rather than hashing it again per finding.
    pub(crate) fn bind_for_ingestion<'a>(
        &'a self,
        module: &'a Module,
    ) -> Option<BoundIngestionImports<'a>> {
        self.bind_root(module).ok()?;
        Some(BoundIngestionImports {
            imports: self,
            _module: module,
        })
    }

    /// Whether `certificate`, an `InheritedFromCallee` naming `reference`,
    /// is admitted in `module`: its lineage reference was authenticated; the
    /// local obligation it discharges in `module` is EQUAL to the one the walk
    /// checked it against, and the local callee its evidence names has the
    /// same name; and the import row it names in `module` is the
    /// authenticated row with the same id. The later clauses keep a set
    /// authenticated for one module from admitting a look-alike certificate
    /// in another — one that rewrote the claim the certificate discharges, or
    /// whose `ImportId` names a different dependency — since the lineage
    /// reference digests the certificate alone.
    #[must_use]
    pub fn admits_external_inheritance(
        &self,
        module: &Module,
        certificate: &ProofCertificate,
        reference: &ExternRef,
    ) -> bool {
        let lineage = certificate.lineage_ref();
        if !self.admitted.contains(&lineage) {
            return false;
        }
        let ProofEvidence::InheritedFromCallee { callee, .. } = &certificate.evidence else {
            return false;
        };
        let Some(obligation) = obligation_named(module, certificate) else {
            return false;
        };
        let Some(callee) = function_name(module, *callee) else {
            return false;
        };
        if !self.inheritances.iter().any(|admitted| {
            admitted.reference == lineage
                && &admitted.obligation == obligation
                && admitted.callee == callee
        }) {
            return false;
        }
        let Some(row) = module.import(reference.module) else {
            return false;
        };
        self.dependencies
            .iter()
            .any(|dependency| dependency.import == reference.module && &dependency.row == row)
    }

    /// This set, moved onto `derived`: the backend's OWN rewrite of the
    /// authenticated root `source` (dialect legalization runs before the
    /// adapter, so the module the adapter sees is not the module that was
    /// authenticated). Refused unless `source` is the authenticated root and
    /// `derived` keeps its name, its import table, and its proof obligations
    /// and certificates exactly — the only tables an admission reads — and
    /// has a wire identity to bind. Nothing else is re-checked: the rewrite is
    /// trust-cg's own, and it is trusted exactly as far as it is for an
    /// unlinked compile.
    pub fn rebind_to_backend_rewrite(
        &self,
        source: &Module,
        derived: &Module,
    ) -> Result<Self, crate::AdapterError> {
        self.bind_root(source)?;
        let refuse = |detail: String| crate::AdapterError::AuthenticatedImportsBoundElsewhere {
            module: derived.name.clone(),
            authenticated_for: self.root_name.clone(),
            detail,
        };
        let changed = [
            ("name", derived.name != source.name),
            ("import table", derived.imports != source.imports),
            (
                "proof obligations",
                derived.proof_obligations != source.proof_obligations,
            ),
            (
                "proof certificates",
                derived.proof_certificates != source.proof_certificates,
            ),
        ];
        if let Some((table, _)) = changed.iter().find(|(_, changed)| *changed) {
            return Err(refuse(format!(
                "the backend's rewrite of the authenticated root changed its {table}"
            )));
        }
        if let Some(blocker) = trust_ir_build::wire_identity_blocker(derived) {
            return Err(refuse(format!(
                "the backend's rewrite of the authenticated root has no wire identity: {blocker}"
            )));
        }
        Ok(Self {
            root_digest: derived.stable_digest(),
            ..self.clone()
        })
    }

    /// Refuse unless `module` is the exact root this set was authenticated
    /// for (equal `Module::stable_digest`). A module without a wire identity
    /// has no digest to compare and is refused.
    pub fn bind_root(&self, module: &Module) -> Result<(), crate::AdapterError> {
        let actual = match trust_ir_build::wire_identity_blocker(module) {
            Some(blocker) => {
                return Err(crate::AdapterError::AuthenticatedImportsBoundElsewhere {
                    module: module.name.clone(),
                    authenticated_for: self.root_name.clone(),
                    detail: format!("the module has no wire identity: {blocker}"),
                });
            }
            None => module.stable_digest(),
        };
        if actual == self.root_digest {
            Ok(())
        } else {
            Err(crate::AdapterError::AuthenticatedImportsBoundElsewhere {
                module: module.name.clone(),
                authenticated_for: self.root_name.clone(),
                detail: format!(
                    "stable digest {} differs from the authenticated root's {}",
                    actual, self.root_digest
                ),
            })
        }
    }
}

/// Why [`authenticate_linked_imports`] refused.
#[derive(Debug, Clone)]
pub enum LinkedImportRefusal {
    /// The linked walk refused the root or its closure. Every error, as the
    /// walk reported it (closure errors folded into
    /// `ValidationError::ImportedModuleInvalid`).
    ///
    /// `rows` names, per import row that a supplied module answers (by
    /// digest or by name), the typed `Module::verify_import` verdict that
    /// failed (`DigestMismatch`, `NameMismatch`, `ProducerMismatch`, …):
    /// diagnostics for the operator, never a second decision.
    Refused {
        errors: Vec<ValidationError>,
        rows: Vec<(u32, ImportVerificationError)>,
    },
    /// The walk accepted the root but did not authenticate this import row.
    /// trust-ir's walk authenticates every row since WS1.7, so this is a
    /// tripwire: a pin that regressed the all-rows pass is refused here
    /// rather than admitting an unauthenticated row.
    UncitedImportRow { import: u32, name: String },
    /// The walk reports a caller-supplied handle registry; trust-cg admits
    /// only the pinned one.
    UnpinnedHandleRegistry,
}

impl fmt::Display for LinkedImportRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refused { errors, rows } => {
                write!(
                    f,
                    "linked import validation refused the module ({} error(s))",
                    errors.len()
                )?;
                for error in errors {
                    write!(f, "\n  {error} [{error:?}]")?;
                }
                for (import, error) in rows {
                    write!(f, "\n  import row {import}: {error:?}")?;
                }
                Ok(())
            }
            Self::UncitedImportRow { import, name } => write!(
                f,
                "UncitedImportRow: import row {import} (`{name}`) was not authenticated by the \
                 linked walk; an unauthenticated row is never admitted"
            ),
            Self::UnpinnedHandleRegistry => f.write_str(
                "the linked walk ran under a caller-supplied handle registry; only the pinned \
                 registry is admitted",
            ),
        }
    }
}

impl std::error::Error for LinkedImportRefusal {}

/// The `--link` dependencies as an import resolver: by digest first (the
/// exact module the row names), else the ONE supplied module with the row's
/// name. The name fallback is a lookup, never an authority — the walk
/// authenticates whatever it returns, so a rebuilt dependency is reported as
/// the precise `DigestMismatch` rather than as no module at all
/// (`ImportUnavailable`). Two supplied modules sharing the name resolve to
/// neither.
struct SuppliedDependencies<'a> {
    by_digest: ModuleSet<'a>,
    supplied: &'a [Module],
}

impl<'a> ImportResolver<'a> for SuppliedDependencies<'a> {
    fn resolve(&self, import: &ModuleImport) -> Option<&'a Module> {
        if let Some(module) = self.by_digest.resolve(import) {
            return Some(module);
        }
        let mut named = self
            .supplied
            .iter()
            .filter(|module| module.name == import.name);
        match (named.next(), named.next()) {
            (Some(module), None) => Some(module),
            _ => None,
        }
    }
}

/// Authenticate `root`'s imports against `dependencies` (roadmap WS7.9).
///
/// Runs `trust_ir_build::validate_linked_module(root, ModuleSet(dependencies),
/// RejectingModuleProofAuthority)`. Every module of the closure must
/// validate, every import row of the root must authenticate against a
/// supplied module's digest, and every call edge to an imported declaration
/// must bind a structurally equal signature; otherwise this refuses with the
/// walk's own errors (`DigestMismatch`, `CallEdgeSignatureMismatch`,
/// `ImportTableNotInterned`, …).
pub fn authenticate_linked_imports(
    root: &Module,
    dependencies: &[Module],
) -> Result<AuthenticatedImportSet, LinkedImportRefusal> {
    #[cfg(feature = "mutation-knobs")]
    if crate::mutation_knobs::skip_import_authentication() {
        return Ok(unauthenticated_for_mutation_control(root));
    }
    let resolver = SuppliedDependencies {
        by_digest: ModuleSet::new(dependencies.iter()),
        supplied: dependencies,
    };
    let report = validate_linked_module(root, &resolver, &RejectingModuleProofAuthority);
    if !report.is_ok() {
        let rows = root
            .imports
            .iter()
            .enumerate()
            .filter_map(|(index, row)| {
                let import = ImportId::new(u32::try_from(index).ok()?);
                let candidate = resolver.resolve(row)?;
                root.verify_import(import, candidate)
                    .err()
                    .map(|error| (import.index(), error))
            })
            .collect();
        return Err(LinkedImportRefusal::Refused {
            errors: report.into_errors(),
            rows,
        });
    }
    if !report.handle_registry_is_pinned() {
        return Err(LinkedImportRefusal::UnpinnedHandleRegistry);
    }
    let (Some(digests), Some(admitted)) = (
        report.authenticated_imports(),
        report.authenticated_certificate_refs(),
    ) else {
        // `is_ok` held, so both are present; refuse rather than assume.
        return Err(LinkedImportRefusal::Refused {
            errors: Vec::new(),
            rows: Vec::new(),
        });
    };
    let mut dependencies = Vec::with_capacity(root.imports.len());
    for (index, row) in root.imports.iter().enumerate() {
        let import = ImportId::new(u32::try_from(index).unwrap_or(u32::MAX));
        if digests.get(&import) != Some(&row.digest) {
            return Err(LinkedImportRefusal::UncitedImportRow {
                import: import.index(),
                name: row.name.clone(),
            });
        }
        dependencies.push(LinkedDependency {
            import,
            row: row.clone(),
        });
    }
    Ok(AuthenticatedImportSet {
        root_name: root.name.clone(),
        root_digest: root.stable_digest(),
        dependencies,
        inheritances: inheritances_of(root, admitted),
        admitted: admitted.clone(),
    })
}

/// The obligation `certificate` discharges in `module`, by id.
fn obligation_named<'m>(
    module: &'m Module,
    certificate: &ProofCertificate,
) -> Option<&'m ProofObligation> {
    module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == certificate.obligation)
}

/// The name of `module`'s function `id`.
fn function_name(module: &Module, id: trust_ir::FuncId) -> Option<&str> {
    module
        .functions
        .iter()
        .find(|function| function.id == id)
        .map(|function| function.name.as_str())
}

/// Every external inheritance of `root` whose lineage reference is in
/// `admitted`, with the local obligation and callee it was authenticated
/// against. A certificate whose obligation or callee does not resolve is
/// left out, so it is never admitted.
fn inheritances_of(
    root: &Module,
    admitted: &BTreeSet<ProofCertificateRef>,
) -> Vec<AdmittedInheritance> {
    root.proof_certificates
        .iter()
        .filter_map(|certificate| {
            let ProofEvidence::InheritedFromCallee {
                callee,
                external: Some(_),
                ..
            } = &certificate.evidence
            else {
                return None;
            };
            let reference = certificate.lineage_ref();
            if !admitted.contains(&reference) {
                return None;
            }
            Some(AdmittedInheritance {
                reference,
                obligation: obligation_named(root, certificate)?.clone(),
                callee: function_name(root, *callee)?.to_string(),
            })
        })
        .collect()
}

/// The `skip_import_authentication` mutation: every row and every external
/// inheritance of `root` "authenticated" without consulting a dependency.
/// Exists so a test can prove a refusal comes from the authentication.
#[cfg(feature = "mutation-knobs")]
fn unauthenticated_for_mutation_control(root: &Module) -> AuthenticatedImportSet {
    let admitted: BTreeSet<ProofCertificateRef> = root
        .proof_certificates
        .iter()
        .filter(|certificate| {
            matches!(
                certificate.evidence,
                ProofEvidence::InheritedFromCallee {
                    external: Some(_),
                    ..
                }
            )
        })
        .map(ProofCertificate::lineage_ref)
        .collect();
    AuthenticatedImportSet {
        inheritances: inheritances_of(root, &admitted),
        root_name: root.name.clone(),
        root_digest: root.stable_digest(),
        dependencies: root
            .imports
            .iter()
            .enumerate()
            .map(|(index, row)| LinkedDependency {
                import: ImportId::new(u32::try_from(index).unwrap_or(u32::MAX)),
                row: row.clone(),
            })
            .collect(),
        admitted,
    }
}
