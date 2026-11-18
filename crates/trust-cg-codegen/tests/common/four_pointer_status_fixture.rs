// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent canonical ByteV1 source, never a reflected target comparand.
use super::cg;
use trust_ir::proof::{
    IslandEnvironment, ProofLineageId, ProofTransform, ProofTransformStage, SourceDefinitionRef,
    encode_island_declarations_v1,
};
use trust_ir::{BodyGate, CallingConv, Endianness, GateEvidence, Module, ProofId, TargetInfo, Ty};
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name, env::Declaration};
use trust_ir_build::{
    ModuleBuilder, ValidationConfig, certify_source_bound_word_status_entry,
    validate_module_with_config,
};
fn c(n: &str) -> Expr {
    Expr::const_str(n)
}
fn a(n: &str, xs: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), xs)
}
fn lam(t: Expr, b: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, t, b)
}
fn bind(op: Expr, good: Expr, erase_fault: bool) -> Expr {
    let failure = if erase_fault {
        a(
            "IRByteMemoryResultV1.value",
            [a("IRScalar.int_", [Expr::nat_lit(0)]), Expr::bvar(0)],
        )
    } else {
        a("IRByteMemoryResultV1.fault", [Expr::bvar(1), Expr::bvar(0)])
    };
    Expr::apps(
        Expr::const_(
            Name::from_string("IRByteMemoryResultV1.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            lam(c("IRByteMemoryResultV1"), c("IRByteMemoryResultV1")),
            lam(c("IRScalar"), lam(c("IRByteMemoryV1"), good)),
            lam(c("IROutcome"), lam(c("IRByteMemoryV1"), failure)),
            op,
        ],
    )
}
#[derive(Clone, Copy)]
pub(crate) enum Change {
    None,
    ReadOther,
    SwapOutputs,
    WrongStatus,
    EraseFault,
}
pub(crate) fn source(change: Change) -> IslandEnvironment {
    // All references originate in this independently authored six-binder source.
    // Each successful memory operation binds scalar=1,memory=0 and lifts every
    // prior reference by two. No module/denotation is read to assemble this body.
    fn step(
        i: usize,
        ctx: Expr,
        mem: Expr,
        ptr: [Expr; 4],
        values: Vec<Expr>,
        change: Change,
    ) -> Expr {
        if i == 4 {
            return a(
                "IRByteMemoryResultV1.value",
                [
                    values[usize::from(matches!(change, Change::WrongStatus))].clone(),
                    mem,
                ],
            );
        }
        let ty = a("IRTy.uint_", [Expr::nat_lit(64)]);
        let op = if i < 2 {
            a(
                "ir_byte_load_v1",
                [
                    ctx.clone(),
                    ty,
                    ptr[if i == 1 && matches!(change, Change::ReadOther) {
                        0
                    } else {
                        i
                    }]
                    .clone(),
                    Expr::nat_lit(8),
                    c("Bool.false"),
                    mem,
                ],
            )
        } else {
            let output = if matches!(change, Change::SwapOutputs) {
                5 - i
            } else {
                i
            };
            a(
                "ir_byte_store_v1",
                [
                    ctx.clone(),
                    ty,
                    ptr[output].clone(),
                    values[i - 2].clone(),
                    Expr::nat_lit(8),
                    c("Bool.false"),
                    mem,
                ],
            )
        };
        let mut lifted = values.into_iter().map(|v| v.lift(2)).collect::<Vec<_>>();
        if i < 2 {
            lifted.push(Expr::bvar(1));
        }
        let good = step(
            i + 1,
            ctx.lift(2),
            Expr::bvar(0),
            ptr.map(|p| p.lift(2)),
            lifted,
            change,
        );
        bind(op, good, matches!(change, Change::EraseFault))
    }
    let domains = [
        c("IRByteContextV1"),
        c("IRByteMemoryV1"),
        c("Nat"),
        c("Nat"),
        c("Nat"),
        c("Nat"),
    ];
    let body = step(
        0,
        Expr::bvar(5),
        Expr::bvar(4),
        [3, 2, 1, 0].map(|n| a("IRScalar.ptr_", [Expr::bvar(n)])),
        vec![],
        change,
    );
    let ty = domains
        .iter()
        .rev()
        .fold(c("IRByteMemoryResultV1"), |b, t| {
            Expr::pi(BinderInfo::Default, t.clone(), b)
        });
    let value = domains.into_iter().rev().fold(body, |b, t| lam(t, b));
    IslandEnvironment::new(
        encode_island_declarations_v1(&[Declaration::Definition {
            name: Name::from_string("Source.copyTwoStatus"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        }])
        .unwrap(),
    )
}
pub(crate) fn module() -> Module {
    let mut m = ModuleBuilder::new_with_target_info(
        "ordinary_four_pointer_status",
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("darwinpcs".into()),
            struct_passing: Default::default(),
        },
    );
    let sig = m.add_func_type(vec![Ty::Ptr; 4], vec![Ty::U64]);
    let mut f = m.function("copy_two_status", sig);
    f.set_calling_conv(CallingConv::C);
    let b = f.create_block();
    let ptr: [_; 4] = std::array::from_fn(|_| f.add_block_param(b, Ty::Ptr));
    f.switch_to_block(b);
    let x = f.load_aligned(Ty::U64, ptr[0], 8);
    let y = f.load_aligned(Ty::U64, ptr[1], 8);
    f.store_aligned(Ty::U64, ptr[2], x, 8);
    f.store_aligned(Ty::U64, ptr[3], y, 8);
    f.ret(vec![x]);
    f.build();
    m.build().unwrap()
}
pub(crate) fn mint(
    m: &Module,
    s: &IslandEnvironment,
) -> Result<trust_ir_build::SourceBoundCallCertificates, String> {
    certify_source_bound_word_status_entry(
        m,
        ProofLineageId::new(10),
        ProofId::new(20),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "word-status-entry",
            "independent-flat-source",
            "1",
        ),
        s,
        &[(
            m.functions[0].id,
            SourceDefinitionRef {
                decl: "Source.copyTwoStatus".into(),
                closure_digest: s.digest,
            },
        )],
    )
}
pub(crate) fn certified() -> Module {
    let started = std::time::Instant::now();
    let mut m = module();
    let s = source(Change::None);
    let rows = mint(&m, &s).unwrap();
    let lineage = trust_ir::proof::ProofLineageManifest {
        schema_version: trust_ir::proof::ProofLineageManifest::SCHEMA_VERSION,
        roots: rows.nodes.iter().map(|n| n.id).collect(),
        nodes: rows.nodes,
    };
    m.proof_obligations.extend(rows.obligations);
    m.proof_certificates.extend(rows.certificates);
    let body_digest = m.function_body_digest(m.functions[0].id).unwrap();
    m.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: Some(GateEvidence {
            obligation: ProofId::new(20),
            body_digest,
        }),
    });
    assert_eq!(
        trust_ir_build::lineage_closed_with_validated_authority(&m, &lineage),
        Ok(())
    );
    let report = validate_module_with_config(&m, &config());
    assert!(report.is_ok(), "{:?}", report.errors());
    trust_ir_build::source_word_status_entry::check_word_status_entry_source(&report).unwrap();
    println!(
        "FOUR_POINTER_SOURCE_KERNEL_SECONDS={:.9}",
        started.elapsed().as_secs_f64()
    );
    m
}
fn config() -> ValidationConfig<'static> {
    ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
        .with_gate_evidence(true)
}

pub(crate) fn plan(module: Module) -> cg::compiler::PolicyQualifiedCoreJitCompilationPlan {
    let target = cg::CoreHostJitTarget::detect().unwrap();
    let core = cg::admit_identity_core_module_for_host_jit(
        module,
        &target,
        cg::CoreDeclaredImportManifest::empty(),
    )
    .unwrap();
    let mut config = cg::CompilerConfig::for_host_jit();
    config.emit_proofs = true;
    config.jit_validation_mode_override = Some(cg::compiler::JitValidationMode::AlwaysVerify);
    config.jit_external_symbol_resolution = cg::JitExternalSymbolResolutionPolicy::ExplicitOnly;
    cg::Compiler::new_for_target_spec(config, target.target_spec())
        .plan_core_module_for_jit_compilation(core)
        .unwrap()
        .qualify_for_proof_grade_compilation()
        .unwrap()
}
pub(crate) fn manifest(module: &Module) -> cg::jit_contract::ArtifactManifestV1 {
    use cg::jit_contract::*;
    let target = TargetDescriptor::for_trust_cg_host_jit();
    let abi = AbiDescriptor::for_trust_cg_target_os(
        cg::target::Target::Aarch64,
        target.operating_system.clone(),
    );
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let policy = ProofPolicy::require_certificates(std::iter::empty::<String>());
    let generation = cg::compile_service::CompileGeneration::new(1);
    let invalidation = InvalidationKey::new(
        "source:Source.copyTwoStatus",
        "sealed-four-pointer-status",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        policy.checksum(),
        generation.get(),
    );
    let mut manifest = ArtifactManifestV1::new(
        "source-bound-four-pointer-status",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: module.functions[0].name.clone(),
        visibility: SymbolVisibility::Exported,
        signature: cg::compile_service::symbol_signature_for_core_function(
            module,
            module.functions[0].id,
            cg::CoreHostJitTarget::detect().unwrap().target_spec(),
        )
        .unwrap(),
        offset_bytes: None,
        checksum: None,
    });
    manifest
}
