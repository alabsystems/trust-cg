// Copyright 2026 Andrew Yates | Apache-2.0
//! `Inst::Dealloc` is REFUSED for codegen, in every body, whatever its
//! pointer's provenance (G18-1, re-decided 2026-09-27; trust-ir
//! `docs/SPEC_RATIFICATIONS.md` "Deallocation is refused for codegen,
//! whatever its provenance", must-refuse corpus row
//! `refuse/dealloc_instruction`, trust-ir `7b0947ee`).
//!
//! `Dealloc { ptr }` names a pointer and nothing else: neither the
//! `AllocOrigin` whose runtime owns the region nor the layout being released.
//! Until this change the adapter RECOVERED both from the same-function
//! `HeapAlloc` sites the pointer provably originated from (`translate_dealloc`,
//! 2887cbf01) and emitted `__rust_dealloc(ptr, size, align)` / `free(ptr)`.
//! trust-ir refuses every `Dealloc` for codegen (`UnlowerableForCodegen`) and
//! says a backend MUST NOT recover origin or layout from dataflow; this backend
//! now conforms, so the two sides state and enforce one rule.
//!
//! Every shape the retired lowering lowered, and every shape it refused for a
//! provenance reason, is kept here and must be refused by the ONE refusal:
//! `[TCG-DEALLOC]` naming trust-ir's `UnlowerableForCodegen`. Every public
//! entry refuses BY trust-ir's own verdict, over every body, before any
//! lowering (the message quotes trust-ir's finding: "trust-ir refuses it for
//! codegen"):
//!
//! * the entries that run the codegen prerequisites
//!   (`validate_codegen_prerequisites`) consume the finding
//!   `validate_module_for_codegen_with` reports;
//! * the validated strict (Core admission) entry reuses a full
//!   `validate_module` report instead — and `validate_module` deliberately
//!   admits a well-formed `Dealloc` — so it reads the same verdict from
//!   trust-ir's lowerability layer (`codegen_lowerability_errors`) on its own.
//!
//! That includes a body this backend would SKIP rather than lower (an
//! `AvailableExternally` definition): trust-ir's rule is "every body", and
//! before the strict entry read the verdict it admitted such a module, because
//! the instruction arm never ran on the skipped body. The instruction arm
//! (message: "names only a pointer") stays as a backstop behind every entry;
//! no public entry reaches it, so it is pinned by the adapter's own unit test
//! `dealloc_instruction_arm_refuses_behind_no_entry_layer`.
//!
//! A claim-less body (`body_gate: None`) is refused too, under a policy that
//! PERMITS claim-less bodies: the rule is about every body this backend would
//! lower, not only a licensed one. The default license policy REFUSES a
//! claim-less body before any lowering (roadmap WS7.5, decision gate DG-73),
//! so every compile here states `Permit` ([`permit_unlicensed`]) — a refusal
//! asserted below is the `Dealloc`'s, never the license's.
//!
//! These are refusal-shape tests (test rung), not proof.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::{
    CodegenLicensePolicy, GuardCarrierArch, TlsDialect, UnlicensedBodyPolicy,
    translate_function_with_license, translate_module_for_arch_with_tls_with_license,
    translate_validated_module_strict_for_arch_with_tls_and_validation_with_license,
};
use trust_ir::inst::AllocOrigin;
use trust_ir::{
    Block as TrustIrBlock, BlockId, BodyGate, CastOp, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, Global, Inst, InstrNode, Linkage, Module as TrustIrModule,
    ProofAnnotation, Ty, ValueId,
};

/// The refusal every `Dealloc` gets, on every layer.
const MARKER: &str = "[TCG-DEALLOC]";
const VERDICT: &str = "UnlowerableForCodegen";
/// Every entry quotes trust-ir's own finding.
const PREREQUISITE_LAYER: &str = "trust-ir refuses it for codegen";

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn def(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}

fn ret() -> InstrNode {
    node(Inst::Return { values: vec![] })
}

fn block(id: u32, params: Vec<(u32, Ty)>, body: Vec<InstrNode>) -> TrustIrBlock {
    TrustIrBlock {
        id: b(id),
        params: params.into_iter().map(|(n, ty)| (v(n), ty)).collect(),
        body,
    }
}

fn heap(ty: Ty, count: Option<u32>, align: Option<u64>, origin: AllocOrigin) -> Inst {
    Inst::HeapAlloc {
        ty,
        count: count.map(v),
        align,
        origin,
    }
}

fn int(ty: Ty, value: i128) -> Inst {
    Inst::Const {
        ty,
        value: Constant::Int(value),
    }
}

fn dealloc(ptr: u32) -> InstrNode {
    node(Inst::Dealloc { ptr: v(ptr) })
}

/// One void function `dealloc_fixture(params) -> ()` whose entry block is
/// bb0, plus any bodyless `externs` declared after it.
fn module(
    params: Vec<Ty>,
    blocks: Vec<TrustIrBlock>,
    externs: &[(&str, Vec<Ty>, Vec<Ty>)],
) -> TrustIrModule {
    let mut module = TrustIrModule::new("dealloc_fixture");
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "dealloc_fixture", ty, b(0));
    func.blocks = blocks;
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    for (index, (name, params, returns)) in externs.iter().enumerate() {
        let ty = module
            .add_func_type(FuncTy {
                params: params.clone(),
                returns: returns.clone(),
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut declaration = TrustIrFunction::new(FuncId::new(index as u32 + 1), *name, ty, b(0));
        declaration.linkage = Linkage::External;
        module
            .try_add_function(declaration)
            .expect("Module::try_add_function: test fixture");
    }
    module
}

/// The license every compile here states: the default policy with
/// claim-less bodies PERMITTED, so the `Dealloc` rule is what is tested.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

fn lower(module: &TrustIrModule) -> Result<(), AdapterError> {
    translate_function_with_license(&module.functions[0], module, &permit_unlicensed()).map(|_| ())
}

/// The same `module` with `dealloc` nodes removed: the control twin that must
/// lower, so a refusal is attributable to the `Dealloc` and nothing else.
fn without_deallocs(module: &TrustIrModule) -> TrustIrModule {
    let mut twin = module.clone();
    for func in &mut twin.functions {
        for block in &mut func.blocks {
            block
                .body
                .retain(|node| !matches!(node.inst, Inst::Dealloc { .. }));
        }
    }
    twin
}

/// Refused by the ONE refusal on the function entry (prerequisite layer
/// first), and by the module entry on both native ISAs.
fn expect_refused(label: &str, module: &TrustIrModule) {
    let refusal = |error: &AdapterError| match error {
        AdapterError::UnsupportedInstruction(message) => {
            message.contains(MARKER) && message.contains(VERDICT)
        }
        _ => false,
    };
    match lower(module) {
        Err(AdapterError::UnsupportedInstruction(message)) => assert!(
            message.contains(MARKER)
                && message.contains(VERDICT)
                && message.contains(PREREQUISITE_LAYER),
            "{label}: expected the prerequisite layer's {MARKER} {VERDICT} refusal, got `{message}`"
        ),
        Err(other) => panic!("{label}: expected {MARKER} {VERDICT}, got {other:?}"),
        Ok(()) => panic!("{label}: a Dealloc LOWERED; every Dealloc must be refused"),
    }
    for arch in [GuardCarrierArch::AArch64, GuardCarrierArch::X86_64] {
        match translate_module_for_arch_with_tls_with_license(
            module,
            arch,
            TlsDialect::default(),
            &permit_unlicensed(),
        ) {
            Err(error) if refusal(&error) => {}
            Err(other) => {
                panic!("{label} ({arch:?} module entry): expected {MARKER}, got {other:?}")
            }
            Ok(_) => panic!("{label} ({arch:?} module entry): a Dealloc LOWERED"),
        }
    }
}

/// The shapes the retired provenance lowering LOWERED (2887cbf01): each was a
/// `Dealloc` of a pointer that provably originated from a same-function
/// `HeapAlloc` of one origin and a layout it could repeat.
fn formerly_lowered_shapes() -> Vec<(&'static str, TrustIrModule)> {
    let mut shapes = Vec::new();
    // (element type, constant count, explicit align)
    for (label, ty, count, align) in [
        ("static u64", Ty::U64, None, None),
        ("static i32 x 5", Ty::I32, Some(5), None),
        ("static u8 x 3 align 64", Ty::U8, Some(3), Some(64)),
        ("static u16 x 0", Ty::U16, Some(0), None),
    ] {
        let mut body = Vec::new();
        if let Some(count) = count {
            body.push(def(int(Ty::U64, count), 1));
        }
        body.push(def(
            heap(ty.clone(), count.map(|_| 1), align, AllocOrigin::RustHeap),
            2,
        ));
        body.push(dealloc(2));
        body.push(ret());
        shapes.push((label, module(vec![], vec![block(0, vec![], body)], &[])));
    }
    for (label, count_ty) in [
        ("dynamic u64 count", Ty::U64),
        ("dynamic u32 count", Ty::U32),
    ] {
        shapes.push((
            label,
            module(
                vec![count_ty.clone()],
                vec![block(
                    0,
                    vec![(0, count_ty)],
                    vec![
                        def(heap(Ty::U32, Some(0), None, AllocOrigin::RustHeap), 1),
                        dealloc(1),
                        ret(),
                    ],
                )],
                &[],
            ),
        ));
    }
    shapes.push((
        "libc malloc block",
        module(
            vec![],
            vec![block(
                0,
                vec![],
                vec![
                    def(int(Ty::U64, 4), 1),
                    def(heap(Ty::I64, Some(1), None, AllocOrigin::CMalloc), 2),
                    dealloc(2),
                    ret(),
                ],
            )],
            &[],
        ),
    ));
    shapes.push((
        "through copies and thin-pointer casts",
        module(
            vec![],
            vec![block(
                0,
                vec![],
                vec![
                    def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 1),
                    def(
                        Inst::Copy {
                            ty: Ty::Ptr,
                            operand: v(1),
                        },
                        2,
                    ),
                    def(
                        Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: Ty::Ptr,
                            dst_ty: Ty::PtrMut(Box::new(Ty::U64)),
                            operand: v(2),
                        },
                        3,
                    ),
                    def(
                        Inst::Cast {
                            op: CastOp::PtrToPtr,
                            src_ty: Ty::PtrMut(Box::new(Ty::U64)),
                            dst_ty: Ty::Ptr,
                            operand: v(3),
                        },
                        4,
                    ),
                    dealloc(4),
                    ret(),
                ],
            )],
            &[],
        ),
    ));
    shapes.push((
        "through a Select of same-layout allocations",
        module(
            vec![Ty::Bool],
            vec![block(
                0,
                vec![(0, Ty::Bool)],
                vec![
                    def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 1),
                    def(heap(Ty::I64, None, None, AllocOrigin::RustHeap), 2),
                    def(
                        Inst::Select {
                            ty: Ty::Ptr,
                            cond: v(0),
                            then_val: v(1),
                            else_val: v(2),
                        },
                        3,
                    ),
                    dealloc(3),
                    ret(),
                ],
            )],
            &[],
        ),
    ));
    shapes.push((
        "through a block-parameter join (RustHeap, align 16)",
        join_module(
            heap(Ty::U64, None, Some(16), AllocOrigin::RustHeap),
            heap(Ty::I64, None, Some(16), AllocOrigin::RustHeap),
        ),
    ));
    shapes.push((
        "through a block-parameter join (CMalloc, any size)",
        join_module(
            heap(Ty::U64, None, None, AllocOrigin::CMalloc),
            heap(Ty::U8, None, None, AllocOrigin::CMalloc),
        ),
    ));
    shapes.push((
        "sibling Deallocs of one dynamic allocation",
        module(
            vec![Ty::U64, Ty::Bool],
            vec![
                block(
                    0,
                    vec![(0, Ty::U64), (1, Ty::Bool)],
                    vec![
                        def(heap(Ty::U64, Some(0), None, AllocOrigin::RustHeap), 2),
                        node(Inst::CondBr {
                            cond: v(1),
                            then_target: b(1),
                            then_args: vec![],
                            else_target: b(2),
                            else_args: vec![],
                        }),
                    ],
                ),
                block(1, vec![], vec![dealloc(2), ret()]),
                block(2, vec![], vec![dealloc(2), ret()]),
            ],
            &[],
        ),
    ));
    shapes.push((
        "a ValidDealloc-annotated release",
        module(
            vec![],
            vec![block(
                0,
                vec![],
                vec![
                    def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 1),
                    dealloc(1).with_proof(ProofAnnotation::ValidDealloc),
                    ret(),
                ],
            )],
            &[],
        ),
    ));
    shapes.push((
        "sequential releases of distinct allocations",
        module(
            vec![],
            vec![block(
                0,
                vec![],
                vec![
                    def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 1),
                    def(heap(Ty::U16, None, Some(32), AllocOrigin::RustHeap), 2),
                    dealloc(1),
                    dealloc(2),
                    ret(),
                ],
            )],
            &[],
        ),
    ));
    shapes
}

/// The shapes the retired lowering REFUSED for a provenance reason (no
/// visible origin, mixed origins or layouts, a dynamic count through a merge,
/// an unreachable release, Swift/Clean cells, definite double frees, an
/// escaping join edge). They are refused now by the same one rule, not by an
/// analysis.
fn formerly_refused_shapes() -> Vec<(&'static str, TrustIrModule)> {
    let producer = |prelude: Vec<InstrNode>| {
        let mut body = prelude;
        body.push(dealloc(1));
        body.push(ret());
        module(vec![], vec![block(0, vec![], body)], &[])
    };
    let mut shapes = vec![
        (
            "a function parameter",
            module(
                vec![Ty::Ptr],
                vec![block(0, vec![(1, Ty::Ptr)], vec![dealloc(1), ret()])],
                &[],
            ),
        ),
        (
            "a stack Alloca",
            producer(vec![def(
                Inst::Alloca {
                    ty: Ty::U64,
                    count: None,
                    align: None,
                },
                1,
            )]),
        ),
        ("the null pointer", producer(vec![def(Inst::NullPtr, 1)])),
        (
            "an interior GEP",
            producer(vec![
                def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 0),
                def(int(Ty::U64, 1), 2),
                def(
                    Inst::GEP {
                        pointee_ty: Ty::U64,
                        base: v(0),
                        indices: vec![v(2)],
                        inbounds: true,
                    },
                    1,
                ),
            ]),
        ),
        (
            "mixed allocator origins",
            join_module(
                heap(Ty::U64, None, None, AllocOrigin::RustHeap),
                heap(Ty::U64, None, None, AllocOrigin::CMalloc),
            ),
        ),
        (
            "mismatched layouts",
            join_module(
                heap(Ty::U64, None, None, AllocOrigin::RustHeap),
                heap(Ty::U32, None, None, AllocOrigin::RustHeap),
            ),
        ),
        (
            "a dynamic count through a merge",
            join_module(
                heap(Ty::U64, Some(10), None, AllocOrigin::RustHeap),
                heap(Ty::U64, Some(10), None, AllocOrigin::RustHeap),
            ),
        ),
        (
            "a definite double free",
            module(
                vec![],
                vec![block(
                    0,
                    vec![],
                    vec![
                        def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 1),
                        dealloc(1),
                        dealloc(1),
                        ret(),
                    ],
                )],
                &[],
            ),
        ),
        (
            "a SwiftHeap cell",
            runtime_origin_module(AllocOrigin::SwiftHeap, false),
        ),
        (
            "a CleanHeap cell beside the Clean RC triple",
            runtime_origin_module(AllocOrigin::CleanHeap, true),
        ),
    ];
    let mut with_call = module(
        vec![],
        vec![block(
            0,
            vec![],
            vec![
                def(
                    Inst::Call {
                        callee: FuncId::new(1),
                        args: vec![],
                    },
                    1,
                ),
                dealloc(1),
                ret(),
            ],
        )],
        &[("make_pointer", vec![], vec![Ty::Ptr])],
    );
    shapes.push(("a call result", with_call.clone()));
    with_call.globals.push(Global {
        name: "dealloc_static".to_string(),
        ty: Ty::U64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    with_call.functions[0].blocks[0].body[0] = def(
        Inst::GlobalAddr {
            global: trust_ir::value::GlobalId::new(0),
        },
        1,
    );
    shapes.push(("a global's address", with_call));
    shapes.push((
        "a join fed by the caller's pointer",
        escaping_edge_module(
            block(
                0,
                vec![(10, Ty::U64), (11, Ty::Ptr)],
                vec![
                    def(int(Ty::U64, 0), 13),
                    def(
                        Inst::ICmp {
                            op: trust_ir::ICmpOp::Eq,
                            ty: Ty::U64,
                            lhs: v(10),
                            rhs: v(13),
                        },
                        14,
                    ),
                    node(Inst::CondBr {
                        cond: v(14),
                        then_target: b(1),
                        then_args: vec![],
                        else_target: b(2),
                        else_args: vec![v(11)],
                    }),
                ],
            ),
            vec![],
        ),
    ));
    shapes
}

/// Every shape the retired provenance lowering lowered is refused, on the
/// function entry and on both native module entries, and its Dealloc-free
/// twin lowers (so the refusal is the Dealloc's).
///
/// MUTATION CONTROL (recorded in the commit): restoring `translate_dealloc`
/// behind the instruction arm and removing the prerequisite layer's
/// `UnlowerableForCodegen { inst: "Dealloc" }` arm makes the static RustHeap
/// shape lower, and this test fails naming it.
#[test]
fn every_formerly_lowered_dealloc_shape_is_refused() {
    for (label, module) in formerly_lowered_shapes() {
        assert!(
            module.functions.iter().all(|func| func.body_gate.is_none()),
            "{label}: the fixture is claim-less"
        );
        lower(&without_deallocs(&module))
            .unwrap_or_else(|error| panic!("{label}: the Dealloc-free twin must lower: {error:?}"));
        expect_refused(label, &module);
    }
}

/// Every shape the retired lowering refused for a provenance reason is
/// refused by the same one rule (its message names no provenance analysis).
#[test]
fn every_formerly_refused_dealloc_shape_is_refused_by_the_one_rule() {
    for (label, module) in formerly_refused_shapes() {
        expect_refused(label, &module);
        if let Err(AdapterError::UnsupportedInstruction(message)) = lower(&module) {
            for retired in [
                "function parameter",
                "wrong runtime",
                "exact layout",
                "count is dynamic",
                "definite double free",
            ] {
                assert!(
                    !message.contains(retired),
                    "{label}: refused by a retired provenance arm (`{retired}`): {message}"
                );
            }
        }
    }
}

/// The validated strict (Core admission) entry reuses a full `validate_module`
/// report — which ADMITS a well-formed `Dealloc` — and runs no codegen
/// prerequisite layer, so it reads trust-ir's CODEGEN verdict itself and
/// refuses with the same quoted finding as every other entry.
///
/// MUTATION CONTROL (recorded in the commit): removing that read
/// (`refuse_dealloc_by_trust_ir_verdict` on the complete-report policy)
/// leaves only the instruction arm to refuse here, and this test fails on the
/// message.
#[test]
fn the_strict_entry_refuses_dealloc_on_trust_irs_verdict() {
    for (label, module) in formerly_lowered_shapes() {
        let report = trust_ir_build::validate_module_report(&module);
        assert!(
            report.is_ok(),
            "{label}: validate_module admits a well-formed Dealloc: {:?}",
            report.errors()
        );
        for arch in [GuardCarrierArch::AArch64, GuardCarrierArch::X86_64] {
            expect_strict_verdict_refusal(&format!("{label} ({arch:?})"), &report, arch);
        }
    }
}

fn expect_strict_verdict_refusal(
    label: &str,
    report: &trust_ir_build::ModuleValidationReport<'_>,
    arch: GuardCarrierArch,
) {
    match translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
        report,
        arch,
        TlsDialect::default(),
        &permit_unlicensed(),
    ) {
        Err(AdapterError::UnsupportedInstruction(message)) => assert!(
            message.contains(MARKER)
                && message.contains(VERDICT)
                && message.contains(PREREQUISITE_LAYER),
            "{label}: expected the strict entry's refusal on trust-ir's verdict, got `{message}`"
        ),
        Err(other) => panic!("{label}: expected {MARKER} {VERDICT}, got {other:?}"),
        Ok(_) => panic!("{label}: the strict entry LOWERED a Dealloc"),
    }
}

/// `keep()` (an External definition) beside `freeing()`, an
/// `AvailableExternally` DEFINITION whose body allocates and frees. This
/// backend skips an `AvailableExternally` body rather than lowering it, so no
/// instruction arm ever sees the `Dealloc`; trust-ir's rule is about every
/// body, and its codegen admission refuses this module.
fn skipped_body_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("dealloc_fixture");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut keep = TrustIrFunction::new(FuncId::new(0), "keep", ty, b(0));
    keep.blocks = vec![block(0, vec![], vec![ret()])];
    module
        .try_add_function(keep)
        .expect("Module::try_add_function: test fixture");
    let mut freeing = TrustIrFunction::new(FuncId::new(1), "freeing", ty, b(0));
    freeing.linkage = Linkage::AvailableExternally;
    freeing.blocks = vec![block(
        0,
        vec![],
        vec![
            def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 1),
            dealloc(1),
            ret(),
        ],
    )];
    module
        .try_add_function(freeing)
        .expect("Module::try_add_function: test fixture");
    module
}

/// A `Dealloc` in a body this backend would SKIP is refused on every module
/// entry, the strict one included, exactly where trust-ir's codegen admission
/// refuses it; the `Dealloc`-free twin is admitted by every entry, so the
/// refusal is the `Dealloc`'s. Review finding on bc1b09c17 (a scratch probe):
/// the strict entry returned `Ok` on this module while the other entries and
/// trust-ir refused it.
///
/// MUTATION CONTROL (recorded in the commit): the same removal as above makes
/// the strict entry admit this module, and this test fails naming it.
#[test]
fn a_dealloc_in_a_skipped_body_is_refused_on_every_entry() {
    let module = skipped_body_module();
    let report = trust_ir_build::validate_module_report(&module);
    assert!(report.is_ok(), "well-formed: {:?}", report.errors());
    let admission = trust_ir_build::CodegenAdmission::pinned()
        .with_unlicensed(trust_ir_build::UnlicensedBodyPolicy::Permit);
    let verdict = trust_ir_build::validate_module_for_codegen_with(&module, &admission);
    assert!(
        verdict.iter().any(|error| matches!(
            error,
            trust_ir_build::ValidationError::UnlowerableForCodegen { inst: "Dealloc", name, .. }
                if name == "freeing"
        )),
        "trust-ir's codegen admission refuses the skipped body's Dealloc: {verdict:?}"
    );
    for arch in [GuardCarrierArch::AArch64, GuardCarrierArch::X86_64] {
        match translate_module_for_arch_with_tls_with_license(
            &module,
            arch,
            TlsDialect::default(),
            &permit_unlicensed(),
        ) {
            Err(AdapterError::UnsupportedInstruction(message)) => assert!(
                message.contains(MARKER)
                    && message.contains(VERDICT)
                    && message.contains(PREREQUISITE_LAYER),
                "({arch:?} module entry): `{message}`"
            ),
            Err(other) => panic!("({arch:?} module entry): expected {MARKER}, got {other:?}"),
            Ok(_) => panic!("({arch:?} module entry): admitted a skipped body's Dealloc"),
        }
        expect_strict_verdict_refusal(&format!("skipped body ({arch:?})"), &report, arch);
    }

    let twin = without_deallocs(&module);
    let twin_report = trust_ir_build::validate_module_report(&twin);
    assert!(twin_report.is_ok(), "twin: {:?}", twin_report.errors());
    for arch in [GuardCarrierArch::AArch64, GuardCarrierArch::X86_64] {
        translate_module_for_arch_with_tls_with_license(
            &twin,
            arch,
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap_or_else(|error| panic!("twin ({arch:?} module entry) must lower: {error:?}"));
        translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
            &twin_report,
            arch,
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap_or_else(|error| panic!("twin ({arch:?} strict entry) must lower: {error:?}"));
    }
}

/// The rule covers every body a consumer would lower, not only a licensed
/// one: a claim-less body (`body_gate: None`) under a policy that PERMITS
/// claim-less bodies (the default refuses them at the license, DG-73), and a
/// licensed (`Gated`) body under a policy that recognizes its authority. Each control twin without the `Dealloc` lowers
/// under the same policy.
///
/// MUTATION CONTROL (recorded in the commit): exempting claim-less bodies
/// (`func.body_gate.is_none()`) in both layers makes the claim-less case lower
/// and this test fail, while the licensed case still passes.
#[test]
fn dealloc_is_refused_in_a_claimless_and_in_a_licensed_body() {
    const AUTHORITY: &str = "tcg-dealloc-test-license";
    let (_, claimless) = formerly_lowered_shapes()
        .into_iter()
        .next()
        .expect("the static RustHeap shape");
    assert!(claimless.functions[0].body_gate.is_none());
    let mut licensed = claimless.clone();
    licensed.functions[0].body_gate = Some(BodyGate::gated(AUTHORITY.to_string()));
    for (label, module, policy) in [
        (
            "claim-less body, claim-less bodies permitted",
            claimless,
            permit_unlicensed(),
        ),
        (
            "licensed body, its authority recognized",
            licensed,
            CodegenLicensePolicy::default().with_recognized_authority(AUTHORITY),
        ),
    ] {
        translate_function_with_license(
            &without_deallocs(&module).functions[0],
            &without_deallocs(&module),
            &policy,
        )
        .unwrap_or_else(|error| panic!("{label}: the control twin must lower: {error:?}"));
        match translate_function_with_license(&module.functions[0], &module, &policy) {
            Err(AdapterError::UnsupportedInstruction(message)) => assert!(
                message.contains(MARKER) && message.contains(VERDICT),
                "{label}: `{message}`"
            ),
            Err(other) => panic!("{label}: expected {MARKER}, got {other:?}"),
            Ok(_) => panic!("{label}: a Dealloc LOWERED"),
        }
        for arch in [GuardCarrierArch::AArch64, GuardCarrierArch::X86_64] {
            match translate_module_for_arch_with_tls_with_license(
                &module,
                arch,
                TlsDialect::default(),
                &policy,
            ) {
                Err(AdapterError::UnsupportedInstruction(message)) => assert!(
                    message.contains(MARKER) && message.contains(VERDICT),
                    "{label} ({arch:?}): `{message}`"
                ),
                Err(other) => panic!("{label} ({arch:?}): expected {MARKER}, got {other:?}"),
                Ok(_) => panic!("{label} ({arch:?}): a Dealloc LOWERED"),
            }
        }
    }
}

/// bb0(%0: Bool, %10: U64) branches to bb1/bb2, each allocating, joining at
/// bb3(p) which frees p.
fn join_module(left: Inst, right: Inst) -> TrustIrModule {
    module(
        vec![Ty::Bool, Ty::U64],
        vec![
            block(
                0,
                vec![(0, Ty::Bool), (10, Ty::U64)],
                vec![node(Inst::CondBr {
                    cond: v(0),
                    then_target: b(1),
                    then_args: vec![],
                    else_target: b(2),
                    else_args: vec![],
                })],
            ),
            block(
                1,
                vec![],
                vec![
                    def(left, 1),
                    node(Inst::Br {
                        target: b(3),
                        args: vec![v(1)],
                    }),
                ],
            ),
            block(
                2,
                vec![],
                vec![
                    def(right, 2),
                    node(Inst::Br {
                        target: b(3),
                        args: vec![v(2)],
                    }),
                ],
            ),
            block(3, vec![(3, Ty::Ptr)], vec![dealloc(3), ret()]),
        ],
        &[],
    )
}

/// A Dealloc of a Swift/Clean allocation. The Dealloc block is stored before
/// the entry so it is translated first and its own refusal is observable;
/// the allocation itself is independently refused.
fn runtime_origin_module(origin: AllocOrigin, declare_clean_rc: bool) -> TrustIrModule {
    let externs: &[(&str, Vec<Ty>, Vec<Ty>)] = if declare_clean_rc {
        &[
            ("clean_inc", vec![Ty::Ptr], vec![]),
            ("clean_dec", vec![Ty::Ptr], vec![]),
            ("clean_is_exclusive", vec![Ty::Ptr], vec![Ty::U8]),
        ]
    } else {
        &[]
    };
    module(
        vec![],
        vec![
            block(1, vec![], vec![dealloc(1), ret()]),
            block(
                0,
                vec![],
                vec![
                    def(heap(Ty::U64, None, None, origin), 1),
                    node(Inst::Br {
                        target: b(1),
                        args: vec![],
                    }),
                ],
            ),
        ],
        externs,
    )
}

/// A join `bb2(%20: Ptr)` that frees its parameter, fed by a `HeapAlloc`
/// through a `Br` from bb1 and by the function parameter `%11` through the
/// `terminator` ending `feeder`. The join is stored first so its `Dealloc` is
/// translated before any other block.
fn escaping_edge_module(feeder: TrustIrBlock, extra: Vec<TrustIrBlock>) -> TrustIrModule {
    let mut blocks = vec![
        block(2, vec![(20, Ty::Ptr)], vec![dealloc(20), ret()]),
        block(
            1,
            vec![],
            vec![
                def(heap(Ty::U64, None, None, AllocOrigin::RustHeap), 12),
                node(Inst::Br {
                    target: b(2),
                    args: vec![v(12)],
                }),
            ],
        ),
        feeder,
    ];
    blocks.extend(extra);
    module(
        vec![Ty::U64, Ty::Ptr],
        blocks,
        &[("may_unwind", vec![], vec![])],
    )
}
