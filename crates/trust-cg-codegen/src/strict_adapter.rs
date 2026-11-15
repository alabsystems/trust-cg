// trust-cg-codegen/strict_adapter.rs - No-pre-LIR-rewrite TrustIR adapter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Exact-target, no-pre-LIR-rewrite entry for TrustIR diagnostics and Core
//! admission.
//!
//! The compatibility compiler path may still perform useful source-IR
//! rewrites before LIR lowering. A proof-carrying Core boundary cannot: a
//! backend-owned clone would no longer be the exact module admitted by the
//! frontend/legalizer. This module therefore binds the existing compiler
//! [`TargetSpec`] and product [`TargetDescriptor`] / [`AbiDescriptor`] to an
//! object format and TLS policy, invokes the no-source-rewrite lowerer, and
//! proves its sparse authorization inventory exhausts the final LIR's
//! exact-call carriers before returning an owned result.
//!
//! This is not semantic identity authority by itself. Lowering still maps
//! TrustIR operations into LIR and recognizes selected non-module-local call
//! names as intrinsic operations. [`crate::core_admission::CoreAdmittedModule`]
//! adds the executable-surface checks that reject those undeclared semantic
//! substitutions in the first Core profile.

use thiserror::Error;

use crate::jit_contract::{AbiDescriptor, TargetDescriptor};
use crate::target::{Target, TargetOperatingSystem, TargetSpec};
use trust_cg_lower::{
    AArch64AbiVariant, AdapterError, CodegenLicensePolicy, Function, GuardCarrierArch,
    ProofContext, TlsDialect,
    translate_module_strict_for_arch_with_tls_and_validation_with_license,
};

/// Object container implied by an exact compiler target specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StrictCoreObjectFormat {
    /// ELF object/link semantics.
    Elf,
    /// Mach-O object/link semantics.
    MachO,
    /// PE/COFF object/link semantics.
    Coff,
}

/// Fully resolved target identity used by strict Core TrustIR lowering.
///
/// `TargetSpec` remains the canonical architecture/vendor/OS/environment
/// authority. The existing product descriptors retain the exact target triple
/// and a derived ABI description. Object format and TLS are derived once from
/// that same spec and stored here so downstream code cannot independently
/// guess them from the host. Downstream compilation must still check and bind
/// the calling convention and object policy it actually consumes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StrictCoreAdapterTarget {
    target_spec: TargetSpec,
    target_descriptor: TargetDescriptor,
    abi_descriptor: AbiDescriptor,
    object_format: StrictCoreObjectFormat,
    tls_dialect: TlsDialect,
    aarch64_abi: Option<AArch64AbiVariant>,
}

impl StrictCoreAdapterTarget {
    /// Exact compiler target, including its ABI/environment component.
    pub const fn target_spec(&self) -> TargetSpec {
        self.target_spec
    }

    /// Existing product-contract target descriptor for this exact spec.
    pub const fn target_descriptor(&self) -> &TargetDescriptor {
        &self.target_descriptor
    }

    /// Existing product-contract ABI descriptor selected for this target.
    pub const fn abi_descriptor(&self) -> &AbiDescriptor {
        &self.abi_descriptor
    }

    /// Object container selected from the exact target OS.
    pub const fn object_format(&self) -> StrictCoreObjectFormat {
        self.object_format
    }

    /// TLS access policy selected from the exact object target.
    pub const fn tls_dialect(&self) -> TlsDialect {
        self.tls_dialect
    }

    /// AArch64 calling convention resolved from the exact target triple by
    /// [`AArch64AbiVariant::from_target_triple`]; `None` for other
    /// architectures and for AArch64 targets without a modeled convention,
    /// whose ABI-dependent adapter decisions are refused.
    pub const fn aarch64_abi(&self) -> Option<AArch64AbiVariant> {
        self.aarch64_abi
    }
}

/// Owned result of strict TrustIR-to-LIR translation.
///
/// Construction replays and then drops the borrowing
/// `ModuleTranslationValidationReport`. Consequently this value can be stored
/// next to (or inside an owner of) the source module without a self-reference.
#[derive(Debug)]
pub struct StrictCoreAdapterResult {
    target: StrictCoreAdapterTarget,
    functions: Vec<(Function, ProofContext)>,
    exact_module_call_count: usize,
    declared_external_call_count: usize,
}

impl StrictCoreAdapterResult {
    /// Exact target identity used for every translated function.
    pub const fn target(&self) -> &StrictCoreAdapterTarget {
        &self.target
    }

    /// Completed LIR functions after exact-call replay.
    pub fn functions(&self) -> &[(Function, ProofContext)] {
        &self.functions
    }

    /// Number of exact closed-image module calls replayed before sealing.
    pub const fn exact_module_call_count(&self) -> usize {
        self.exact_module_call_count
    }

    /// Number of imported direct-call carriers exhaustively authenticated
    /// against bodyless External `FuncId`s before sealing.
    pub const fn declared_external_call_count(&self) -> usize {
        self.declared_external_call_count
    }

    /// Mutable access exists only inside the opaque Core planning transaction.
    pub(crate) fn functions_mut(&mut self) -> &mut [(Function, ProofContext)] {
        &mut self.functions
    }

    /// Move the replayed LIR into the sealed, non-executable Core JIT plan.
    ///
    /// Kept crate-private so callers cannot detach raw LIR from its admitted
    /// module/target/receipt owner and feed it to an unchecked backend route.
    pub(crate) fn into_functions(self) -> Vec<(Function, ProofContext)> {
        self.functions
    }
}

/// Fail-closed strict-adapter errors.
#[derive(Debug, Error)]
pub enum StrictCoreAdapterError {
    /// Architecture aliases are compatibility requests: they may inherit the
    /// host OS/ABI and therefore are not exact Core target authority.
    #[error(
        "strict Core adapter requires an explicit target triple, not architecture alias `{target}`"
    )]
    TargetNotExplicit {
        /// Canonical unresolved target text.
        target: String,
    },

    /// The public fields did not form one of TrustCG's supported target specs.
    #[error("strict Core adapter rejected target `{target}`: {reason}")]
    InvalidTargetSpec {
        /// Canonical target text.
        target: String,
        /// Exact parse/consistency failure.
        reason: String,
    },

    /// Identity-only TrustIR-to-LIR translation failed.
    #[error(transparent)]
    Adapter(#[from] AdapterError),
}

/// Diagnose whether a module can lower for one exact target without any
/// backend-owned pre-LIR source rewrite.
///
/// TLS is not caller-selectable here: Mach-O selects Darwin TLV, ELF selects
/// local-exec, and COFF selects a fail-closed no-TLS policy until a COFF TLS
/// lowering exists. Sparse exact-local and declared-import call authorizations
/// are replayed only after one complete carrier census proves that they exhaust
/// the completed LIR.
///
/// This raw-module entry is not Core admission authority: it does not bind the
/// module's target metadata, proof replay, or host imports. Production Core
/// admission uses `translate_validated_core_module_for_target`, a helper private
/// to `core_admission.rs` that calls
/// `translate_validated_core_module_under_core_qualification`, after obtaining
/// a successful full TrustIR validation report. It also does not reject every
/// name-classified intrinsic substitution; callers needing that guarantee must
/// use Core admission rather than treating this diagnostic result as an
/// identity receipt.
pub fn translate_core_module_for_target_with_validation(
    module: &trust_ir::Module,
    target_spec: TargetSpec,
) -> Result<StrictCoreAdapterResult, StrictCoreAdapterError> {
    translate_core_module_for_target_with_validation_and_license(
        module,
        target_spec,
        &trust_cg_lower::CodegenLicensePolicy::default(),
    )
}

/// [`translate_core_module_for_target_with_validation`] under an explicit
/// trust-ir v41 codegen-license policy.
pub fn translate_core_module_for_target_with_validation_and_license(
    module: &trust_ir::Module,
    target_spec: TargetSpec,
    license: &trust_cg_lower::CodegenLicensePolicy,
) -> Result<StrictCoreAdapterResult, StrictCoreAdapterError> {
    let target = resolve_strict_target(target_spec)?;
    let guard_arch = guard_carrier_arch(target_spec.architecture);
    // `guard_carrier_arch` is the ISA alone, and the adapter's Swift return
    // budget for x86-64 is System V's. Refuse every Swift edge on an x86 C ABI
    // with no witnessed swiftcc placement rather than let it inherit those
    // numbers; see `compiler::reject_unwitnessed_swift_conv_for_spec`.
    crate::compiler::reject_unwitnessed_swift_conv_for_spec(module, target_spec)?;
    let (functions, validation) =
        translate_module_strict_for_arch_with_tls_and_validation_with_license(
            module,
            guard_arch,
            target.tls_dialect,
            license,
        )?;
    let exact_module_call_count = validation.exact_module_call_count();
    let declared_external_call_count = validation.declared_external_call_count();
    validation.replay_strict_call_bindings_exhaustive(&functions)?;

    Ok(StrictCoreAdapterResult {
        target,
        functions,
        exact_module_call_count,
        declared_external_call_count,
    })
}

/// Lower the exact module authenticated by `report` without repeating full
/// TrustIR validation, for closed-JIT Core admission.
///
/// This is an implementation-facing Core-admission building block, not an
/// admission authority. The caller is responsible for target metadata,
/// host-import closure, proof disposition, and digest sealing before the owned
/// result can become `CoreAdmittedModule`. It takes the caller's
/// [`trust_cg_lower::CoreQualificationFollows`], whose constructor is
/// `unsafe`; Core admission constructs it in its own private helper.
pub(crate) fn translate_validated_core_module_under_core_qualification(
    report: &trust_ir_build::ModuleValidationReport<'_>,
    target_spec: TargetSpec,
    core_qualification: trust_cg_lower::CoreQualificationFollows,
) -> Result<StrictCoreAdapterResult, StrictCoreAdapterError> {
    let target = resolve_strict_target(target_spec)?;
    let guard_arch = guard_carrier_arch(target_spec.architecture);
    if let Some(module) = report.validated_module() {
        // Same fail-closed rule as the raw-module entry above; the report's
        // module is the exact one that will be lowered.
        crate::compiler::reject_unwitnessed_swift_conv_for_spec(module, target_spec)?;
    }
    // Core admission's planning path: Core's proof-grade qualification and
    // address-free compilation refuse every backend call a module body could
    // receive, so the translation skips the backend-symbol refusal that every
    // other entry applies.
    //
    // The license FLOOR admission lowers under: `Ungated`, an unrecognized
    // authority, and a `Gated` body without its evidence (or refuted
    // in-module) are refused here; a claim-less body is DEFERRED, under the
    // named `CoreAdmissionFloor` exception, to the planner — an admitted
    // owner produces code only through `plan_core_module_for_jit_compilation`,
    // whose preflight re-decides the whole license under the compiler's own
    // policy (default: refuse claim-less bodies, DG-73).
    let floor = CodegenLicensePolicy::default().with_unlicensed_permit_exception(
        trust_cg_lower::UnlicensedPermitException::CoreAdmissionFloor,
    );
    let (functions, validation) =
        trust_cg_lower::translate_validated_module_strict_for_core_qualification(
            report,
            guard_arch,
            target.tls_dialect,
            &floor,
            core_qualification,
        )?;
    let exact_module_call_count = validation.exact_module_call_count();
    let declared_external_call_count = validation.declared_external_call_count();
    validation.replay_strict_call_bindings_exhaustive(&functions)?;

    Ok(StrictCoreAdapterResult {
        target,
        functions,
        exact_module_call_count,
        declared_external_call_count,
    })
}

fn resolve_strict_target(
    target_spec: TargetSpec,
) -> Result<StrictCoreAdapterTarget, StrictCoreAdapterError> {
    let target_text = target_spec.triple();
    if !target_spec.has_explicit_os_abi() {
        return Err(StrictCoreAdapterError::TargetNotExplicit {
            target: target_text,
        });
    }

    // Reparse the public components through TargetSpec's authoritative support
    // matrix. This catches a manually-constructed incoherent combination while
    // keeping one source of truth for supported triples.
    let reparsed = TargetSpec::parse(&target_text).map_err(|error| {
        StrictCoreAdapterError::InvalidTargetSpec {
            target: target_text.clone(),
            reason: error.reason().to_owned(),
        }
    })?;
    if reparsed != target_spec {
        return Err(StrictCoreAdapterError::InvalidTargetSpec {
            target: target_text,
            reason: "canonical target triple does not round-trip to the supplied TargetSpec"
                .to_owned(),
        });
    }

    let (object_format, tls_dialect) = match target_spec.operating_system {
        TargetOperatingSystem::Linux => (StrictCoreObjectFormat::Elf, TlsDialect::ElfLocalExec),
        TargetOperatingSystem::Darwin => (StrictCoreObjectFormat::MachO, TlsDialect::MachOTlv),
        TargetOperatingSystem::Windows => {
            (StrictCoreObjectFormat::Coff, TlsDialect::RejectThreadLocals)
        }
        TargetOperatingSystem::Unknown => {
            return Err(StrictCoreAdapterError::InvalidTargetSpec {
                target: target_text,
                reason: "unknown OS has no exact ABI, object-format, or TLS policy".to_owned(),
            });
        }
    };

    // The same resolution the pipeline's instruction selection uses, from the
    // same canonical triple. A target without a modeled convention keeps
    // `None`: the adapter then refuses only the decisions that depend on it.
    let aarch64_abi = if target_spec.architecture == Target::Aarch64 {
        AArch64AbiVariant::from_target_triple(&target_text).ok()
    } else {
        None
    };

    let target_descriptor = TargetDescriptor::for_trust_cg_target_spec(target_spec);
    let abi_descriptor = AbiDescriptor::for_trust_cg_target_os(
        target_spec.architecture,
        target_descriptor.operating_system.clone(),
    );

    Ok(StrictCoreAdapterTarget {
        target_spec,
        target_descriptor,
        abi_descriptor,
        object_format,
        tls_dialect,
        aarch64_abi,
    })
}

const fn guard_carrier_arch(target: Target) -> GuardCarrierArch {
    match target {
        Target::Aarch64 => GuardCarrierArch::AArch64,
        Target::X86_64 => GuardCarrierArch::X86_64,
        Target::Riscv64 => GuardCarrierArch::Riscv64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// This file's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
    /// them passes because it was silently refused.
    fn permit_unlicensed() -> crate::CodegenLicensePolicy {
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
    }
    use crate::target::{TargetEnvironment, TargetVendor};
    use trust_cg_lower::PreLirTransform;
    use trust_ir::{
        BinOp, Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Global, Inst,
        InstrNode, Linkage, TlsModel, Ty, ValueId,
    };

    fn empty_module(name: &str) -> trust_ir::Module {
        let mut module = trust_ir::Module::new(name);
        let func_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "entry", func_ty, BlockId::new(0));
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        module
    }

    fn exact_spec(architecture: Target, operating_system: TargetOperatingSystem) -> TargetSpec {
        match operating_system {
            TargetOperatingSystem::Linux => TargetSpec::new(
                architecture,
                TargetVendor::Unknown,
                TargetOperatingSystem::Linux,
                TargetEnvironment::Gnu,
            ),
            TargetOperatingSystem::Darwin => TargetSpec::new(
                architecture,
                TargetVendor::Apple,
                TargetOperatingSystem::Darwin,
                TargetEnvironment::Unknown,
            ),
            TargetOperatingSystem::Windows => TargetSpec::new(
                architecture,
                TargetVendor::Pc,
                TargetOperatingSystem::Windows,
                TargetEnvironment::Msvc,
            ),
            TargetOperatingSystem::Unknown => TargetSpec::new(
                architecture,
                TargetVendor::Unknown,
                TargetOperatingSystem::Unknown,
                TargetEnvironment::Unknown,
            ),
        }
    }

    fn binding_frame_across_edge(close_before_edge: bool) -> trust_ir::Module {
        let mut module = empty_module("frame_across_edge");
        let frame = ValueId::new(0);
        let next = BlockId::new(1);
        let mut body = vec![
            InstrNode::new(Inst::OpenFrame {
                def: trust_ir::inst::BindingFrameDef::new(
                    trust_ir::value::BindingFrameId::new(0),
                    "frame",
                    vec![],
                ),
            })
            .with_result(frame),
        ];
        if close_before_edge {
            body.push(InstrNode::new(Inst::CloseFrame { frame }));
        }
        body.push(InstrNode::new(Inst::Br {
            target: next,
            args: vec![],
        }));
        module.functions[0].blocks[0].body = body;
        module.functions[0].blocks.push(Block {
            id: next,
            params: vec![],
            body: vec![
                InstrNode::new(Inst::CloseFrame { frame }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        });
        module
    }

    #[test]
    fn binding_frame_closed_in_a_predecessor_is_refused_by_the_strict_adapter() {
        let module = binding_frame_across_edge(true);
        assert!(
            trust_ir_build::validate_module(&module)
                .iter()
                .any(|error| {
                    matches!(
                        error,
                        trust_ir_build::ValidationError::BindingUseAfterClose { .. }
                    )
                })
        );
        let error = translate_core_module_for_target_with_validation_and_license(
            &module,
            exact_spec(Target::Aarch64, TargetOperatingSystem::Darwin),
            &permit_unlicensed(),
        )
        .expect_err("a predecessor close cannot be forgotten at the next block");
        assert!(matches!(
            error,
            StrictCoreAdapterError::Adapter(AdapterError::TrustIrAdmissionRefused { ref error })
                if error.contains("binding frame %0 is used after close_frame on the same path")
        ));
    }

    #[test]
    fn binding_frame_live_across_an_edge_can_be_closed_by_the_strict_adapter() {
        let module = binding_frame_across_edge(false);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let result = translate_core_module_for_target_with_validation_and_license(
            &module,
            exact_spec(Target::Aarch64, TargetOperatingSystem::Darwin),
            &permit_unlicensed(),
        )
        .expect("the live frame must remain accepted until its one close");
        assert_eq!(result.functions().len(), 1);
    }

    #[test]
    fn exact_target_derives_object_abi_and_tls_from_one_spec() {
        let module = empty_module("exact_targets");
        let darwin_spec = exact_spec(Target::Aarch64, TargetOperatingSystem::Darwin);
        let darwin = translate_core_module_for_target_with_validation_and_license(
            &module,
            darwin_spec,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_eq!(darwin.target().target_spec(), darwin_spec);
        assert_eq!(
            darwin.target().target_descriptor().triple,
            "aarch64-apple-darwin"
        );
        assert_eq!(
            darwin.target().abi_descriptor().calling_convention,
            "darwinpcs"
        );
        assert_eq!(
            darwin.target().object_format(),
            StrictCoreObjectFormat::MachO
        );
        assert_eq!(darwin.target().tls_dialect(), TlsDialect::MachOTlv);

        let linux_spec = exact_spec(Target::X86_64, TargetOperatingSystem::Linux);
        let linux = translate_core_module_for_target_with_validation_and_license(
            &module,
            linux_spec,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_eq!(
            linux.target().target_descriptor().triple,
            "x86_64-unknown-linux-gnu"
        );
        assert_eq!(
            linux.target().abi_descriptor().calling_convention,
            "sysv_amd64"
        );
        assert_eq!(linux.target().object_format(), StrictCoreObjectFormat::Elf);
        assert_eq!(linux.target().tls_dialect(), TlsDialect::ElfLocalExec);

        let windows_spec = exact_spec(Target::X86_64, TargetOperatingSystem::Windows);
        let windows = translate_core_module_for_target_with_validation_and_license(
            &module,
            windows_spec,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_eq!(
            windows.target().target_descriptor().triple,
            "x86_64-pc-windows-msvc"
        );
        assert_eq!(
            windows.target().abi_descriptor().calling_convention,
            "windows_x64"
        );
        assert_eq!(
            windows.target().object_format(),
            StrictCoreObjectFormat::Coff
        );
        assert_eq!(
            windows.target().tls_dialect(),
            TlsDialect::RejectThreadLocals
        );
    }

    #[test]
    fn architecture_alias_is_not_exact_target_authority() {
        let error = translate_core_module_for_target_with_validation_and_license(
            &empty_module("alias"),
            TargetSpec::unknown_for_architecture(Target::Aarch64),
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            StrictCoreAdapterError::TargetNotExplicit { .. }
        ));
    }

    #[test]
    fn strict_entry_rejects_both_legacy_pre_lir_rewrite_triggers() {
        let spec = exact_spec(Target::Aarch64, TargetOperatingSystem::Darwin);

        let aggregate = Ty::Tuple(vec![Ty::I64, Ty::I64]);
        let mut swift = trust_ir::Module::new("swift_trigger");
        let swift_ty = swift
            .add_func_type(FuncTy {
                params: vec![aggregate.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut swift_function =
            Function::new(FuncId::new(0), "swift_pair", swift_ty, BlockId::new(0));
        swift_function.calling_conv = CallingConv::Swift;
        swift_function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), aggregate)],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        swift
            .try_add_function(swift_function)
            .expect("Module::try_add_function: test fixture");
        assert!(matches!(
            translate_core_module_for_target_with_validation_and_license(
                &swift,
                spec,
                &permit_unlicensed()
            ),
            Err(StrictCoreAdapterError::Adapter(
                AdapterError::PreLirTransformForbidden {
                    transform: PreLirTransform::SwiftAggregateScalarization,
                    ..
                }
            ))
        ));

        let mut division = trust_ir::Module::new("div_trigger");
        let div_ty = division
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut div_function =
            Function::new(FuncId::new(0), "div_by_seven", div_ty, BlockId::new(0));
        div_function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(7),
                })
                .with_results(vec![ValueId::new(1)]),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_results(vec![ValueId::new(2)]),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                }),
            ],
        }];
        division
            .try_add_function(div_function)
            .expect("Module::try_add_function: test fixture");
        assert!(matches!(
            translate_core_module_for_target_with_validation_and_license(
                &division,
                spec,
                &permit_unlicensed()
            ),
            Err(StrictCoreAdapterError::Adapter(
                AdapterError::PreLirTransformForbidden {
                    transform: PreLirTransform::DivNonZeroConstAnnotation,
                    ..
                }
            ))
        ));
    }

    #[test]
    fn exact_module_call_report_is_replayed_before_owned_result_escapes() {
        let mut module = trust_ir::Module::new("strict_exact_call");
        let func_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut caller = Function::new(FuncId::new(0), "caller", func_ty, BlockId::new(0));
        caller.linkage = Linkage::Internal;
        caller.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }];
        let mut callee = Function::new(FuncId::new(1), "callee", func_ty, BlockId::new(0));
        callee.linkage = Linkage::Internal;
        callee.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        }];
        module
            .try_add_function(caller)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");

        let result = translate_core_module_for_target_with_validation_and_license(
            &module,
            exact_spec(Target::Aarch64, TargetOperatingSystem::Darwin),
            &permit_unlicensed(),
        )
        .expect("strict wrapper must replay exact-call authority internally");
        assert_eq!(result.functions().len(), 2);
        assert_eq!(result.exact_module_call_count(), 1);
    }

    #[test]
    fn validated_entry_reuses_the_exact_successful_full_report() {
        let module = empty_module("validated_strict_entry");
        let report = trust_ir_build::validate_module_report(&module);
        // SAFETY: the translated functions are inspected and dropped; nothing
        // is emitted or run.
        let core_qualification =
            unsafe { trust_cg_lower::CoreQualificationFollows::caller_runs_core_qualification() };
        let result = translate_validated_core_module_under_core_qualification(
            &report,
            exact_spec(Target::Aarch64, TargetOperatingSystem::Darwin),
            core_qualification,
        )
        .expect("successful full report must feed identity-only lowering directly");

        assert_eq!(result.functions().len(), 1);
        assert_eq!(result.exact_module_call_count(), 0);
        assert!(std::ptr::eq(
            report.validated_module().expect("report is valid"),
            &module
        ));
    }

    #[test]
    fn coff_target_has_explicit_fail_closed_tls_policy() {
        let mut module = empty_module("coff_tls");
        module.globals.push(Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "tls_counter".to_owned(),
            ty: Ty::I64,
            mutable: true,
            initializer: None,
            linkage: Linkage::External,
            tls: Some(TlsModel::LocalExec),
            align: None,
        });
        // Make the global observable by the only function.
        module.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::GlobalAddr {
                global: trust_ir::value::GlobalId::new(0),
            })
            .with_results(vec![ValueId::new(0)]),
        );

        let error = translate_core_module_for_target_with_validation_and_license(
            &module,
            exact_spec(Target::X86_64, TargetOperatingSystem::Windows),
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(matches!(
            error,
            StrictCoreAdapterError::Adapter(AdapterError::UnsupportedInstruction(ref reason))
                if reason.contains("target TLS policy rejects thread-local global `tls_counter`")
        ));
    }
}
