//! WS7.17 — the pin-move floor, table-driven.
//!
//! `reject_unconsumed_v41_target_neutral_surface` (and its target-dependent
//! wrapper `reject_unconsumed_v41_surface`) read every trust-ir record whose
//! fields reach codegen — `Module`, `Function`, `FuncAttrs`, `ParamAttrs`,
//! `Global`, `StructDef`, `EnumDef`, `ProofObligation`, and `TargetInfo` —
//! through `..`-free destructures. Each field is classified in a comment as
//! CONSUMED (naming the lowering site) or REFUSED-WHEN-NON-DEFAULT (naming its
//! own `AdapterError`). `BodyGate` is classified by
//! `CodegenLicensePolicy::verdict`, whose match is wildcard-free.
//!
//! What this file pins:
//!
//! * **Positive:** the unmodified control module is accepted on every native
//!   entry, as is each accepted neighbour of a refused value (a 64-bit
//!   little-endian `NativeC`/`Unclassified` target, a definition's
//!   visibility, a pending obligation of an unrecognized kind). The rest of
//!   this crate's suite is the existing corpus, which still compiles.
//! * **Negative twin, one row per REFUSED field:** a module that differs from
//!   the control ONLY in that field's non-default value is refused on every
//!   native module entry with that field's OWN named error — never a generic
//!   one, and never by a different entry disagreeing.
//! * **Mutation control (compile-time, run once, recorded here):** the floor's
//!   real gate is that a field added by a trust-ir pin move fails to compile
//!   this crate. At the pin `d41fa3f8b7d8e2dba3f6e5b5a0b6217194e2a9f5`
//!   (2026-09-18), a scratch copy of trust-ir whose `Function` gained
//!   `pub ws7_17_mutation: bool` (initialized at trust-ir's own two
//!   `Function` construction sites in `lib.rs` and the one in `binary.rs`)
//!   was patched in with
//!
//!   ```text
//!   cargo check -p trust-cg-lower \
//!     --config 'patch."https://github.com/alabsystems/trust-ir.git".trust-ir.path="<scratch>/crates/trust-ir"' \
//!     --config 'patch."https://github.com/alabsystems/trust-ir.git".trust-ir-build.path="<scratch>/crates/trust-ir-build"' \
//!     --config 'patch."https://github.com/alabsystems/trust-ir.git".trust-ir-giveback.path="<scratch>/crates/trust-ir-giveback"'
//!   ```
//!
//!   and failed with `error[E0027]: pattern does not mention field
//!   `ws7_17_mutation`` at the `Function` destructure in
//!   `function_surface_floor` (`src/adapter.rs`), alongside the `Function`
//!   destructure the static-call identity check
//!   (`src/static_call_devirtualization.rs`) already carried. The same
//!   command against the unmodified scratch copy compiles. A future pin move
//!   is expected to hit exactly that error and classify the field in the same
//!   commit.
//!
//!   (`<scratch>` is `git archive d41fa3f8` of trust-ir; run with a scratch
//!   `CARGO_TARGET_DIR`, and restore `Cargo.lock` afterwards — the patch
//!   rewrites its trust-ir `source` rows.)

use std::collections::HashMap;

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::{
    GuardCarrierArch, TlsDialect, prepare_module_for_lir, reject_unconsumed_v41_surface,
    reject_unconsumed_v41_target_neutral_surface,
};
use trust_ir::proof::{
    FormulaSite, ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation,
    ProofStatus,
};
use trust_ir::{
    AssertKind, Block, BlockId, CallingConv, Constant, Endianness, ExternRef, FieldDef, FuncId,
    FuncTy, Function, Global, Inst, InstrNode, Linkage, Module, ModuleCompleteness, ModuleImport,
    Ordering, PanicLocation, PanicSite, ParamAttrs, ProofId, StructDef, StructId,
    StructPassingPolicy, StructRepr, TargetInfo, Ty, UnloweredRow, ValueId, Visibility,
};

const ARCHES: [GuardCarrierArch; 3] = [
    GuardCarrierArch::AArch64,
    GuardCarrierArch::X86_64,
    GuardCarrierArch::Riscv64,
];

/// One defined function `entry: (ptr) -> i64` returning the constant 7, with
/// a 64-bit little-endian native-C target declared.
fn control_module() -> Module {
    let mut module = Module::new("pin_move_floor");
    module.target_info = Some(target(8, Endianness::Little, StructPassingPolicy::NativeC));
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    entry.blocks.push(block);
    module.functions.push(entry);
    module
}

fn target(pointer_size: u32, endianness: Endianness, policy: StructPassingPolicy) -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size,
        endianness,
        abi: None,
        struct_passing: policy,
    }
}

fn data_global(name: &str) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(1)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn obligation(id: u32, kind: ObligationKind, status: ProofStatus) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status,
        description: "hand-built".to_string(),
        formula: None,
        function: Some(FuncId::new(0)),
        source: None,
        site: None,
        spec: None,
    }
}

/// Give `module` a bodyless external declaration `take: (ptr) -> i64` whose
/// only parameter carries `attrs`, and make `entry` call it INDIRECTLY through
/// its address: `entry(p) = (&take)(p)`. The call edge's `FuncTy` carries no
/// parameter attributes, so nothing at the call site says `byval`.
fn call_declaration_through_its_address(module: &mut Module, attrs: ParamAttrs) {
    let sig = module.functions[0].ty;
    let mut take = Function::new(FuncId::new(1), "take", sig, BlockId::new(0));
    take.linkage = Linkage::External;
    take.blocks = Vec::new();
    take.attrs.params = vec![attrs];
    module.functions.push(take);
    let body = &mut module.functions[0].blocks[0].body;
    body.clear();
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Func(sig),
            value: Constant::FnDef(FuncId::new(1)),
        })
        .with_result(ValueId::new(1)),
    );
    body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(1),
            sig,
            args: vec![ValueId::new(0)],
            calling_conv: CallingConv::C,
        })
        .with_result(ValueId::new(2)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
}

/// `control_module`'s entry block with `inst` inserted at `index`.
fn insert_in_entry(module: &mut Module, index: usize, node: InstrNode) {
    module.functions[0].blocks[0].body.insert(index, node);
}

/// v54: the panic entry `panic_const_div_by_zero: (ptr) -> ()` (FuncId 1), a
/// definition that never returns — the signature a zero-operand kind's entry
/// must have.
fn add_panic_entry(module: &mut Module) {
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(
        FuncId::new(1),
        "panic_const_div_by_zero",
        sig,
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.body.push(InstrNode::new(Inst::Unreachable));
    entry.blocks.push(block);
    module.functions.push(entry);
}

/// `%8 = const true`, the checked condition of the v54 rows.
fn true_condition() -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::Bool,
        value: Constant::Bool(true),
    })
    .with_result(ValueId::new(8))
}

/// A site calling the panic entry with the entry's pointer parameter as the
/// run-time location.
fn entry_pointer_panic_site() -> PanicSite {
    PanicSite {
        entry: FuncId::new(1),
        location: PanicLocation::Value(ValueId::new(0)),
    }
}

/// v55 (amendment D): the struct `Owner` (`struct.0`, not trivially
/// droppable) and its drop glue `owner_drop: (ptr) -> ()` (FuncId 1),
/// registered in the module drop-glue table.
fn add_owner_drop_glue(module: &mut Module) {
    module.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Owner".to_string(),
        fields: vec![FieldDef {
            name: "handle".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: StructRepr::default(),
    });
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut glue = Function::new(FuncId::new(1), "owner_drop", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    glue.blocks.push(block);
    module.functions.push(glue);
    module
        .set_drop_glue(Ty::Struct(StructId::new(0)), FuncId::new(1))
        .expect("one row for one type and one glue");
}

/// v55 / v56: end the control's entry block with `terminator` (continuing to
/// bb1, which holds the control's return, or unwinding to the cleanup pad
/// bb2, which re-raises), after `prefix`.
fn split_entry_at_unwinding_twin(module: &mut Module, prefix: Vec<InstrNode>, terminator: Inst) {
    let entry = &mut module.functions[0];
    let tail = entry.blocks[0].body.split_off(0);
    entry.blocks[0].body.extend(prefix);
    entry.blocks[0].body.push(InstrNode::new(terminator));
    let mut normal = Block::new(BlockId::new(1));
    normal.body = tail;
    let mut pad = Block::new(BlockId::new(2));
    pad.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results([ValueId::new(20), ValueId::new(21)]),
    );
    pad.body.push(InstrNode::new(Inst::Resume {
        exn: ValueId::new(20),
    }));
    entry.blocks.push(normal);
    entry.blocks.push(pad);
}

/// A strong or weak compare-exchange on the entry's pointer parameter,
/// comparing and storing the constant the control module returns.
fn cmpxchg_on_entry_pointer(weak: bool) -> InstrNode {
    InstrNode::new(Inst::CmpXchg {
        ty: Ty::I64,
        ptr: ValueId::new(0),
        expected: ValueId::new(1),
        desired: ValueId::new(1),
        success: Ordering::SeqCst,
        failure: Ordering::SeqCst,
        weak,
    })
    .with_results([ValueId::new(2), ValueId::new(3)])
}

/// A two-lane tuple whose second lane is UNWRITTEN (trust-ir v49).
fn tuple_with_unwritten_lane() -> Constant {
    Constant::Aggregate(vec![Constant::Int(1), Constant::Uninit])
}

/// Where a refused field is decided.
#[derive(Clone, Copy, Debug)]
enum Scope {
    /// The shared floor: every lane, wasm included.
    TargetNeutral,
    /// The target-dependent wrapper only: the wasm lane owns its own target.
    TargetDependent,
    /// Refused where the function is lowered (not by the floor itself).
    Lowering,
}

struct Row {
    /// `<Record>.<field>` — the field whose non-default value is refused.
    field: &'static str,
    scope: Scope,
    mutate: fn(&mut Module),
    /// The field's own named refusal.
    named: fn(&AdapterError) -> bool,
}

const ROWS: &[Row] = &[
    Row {
        field: "Module.completeness",
        scope: Scope::TargetNeutral,
        mutate: |module| module.completeness = Some(ModuleCompleteness::Complete),
        named: |error| {
            matches!(error, AdapterError::ModuleCompletenessUnsupported { module }
                if module == "pin_move_floor")
        },
    },
    Row {
        field: "Module.tuple_layouts",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            // WS7.7: a row EQUAL to the declaration-order layout is consumed
            // (see `accepted_neighbours_of_refused_values_still_compile`);
            // the refused value is a row that disagrees with it.
            let tuple_type = module
                .add_type(Ty::Tuple(vec![Ty::U8, Ty::U8]))
                .expect("Module::add_type: test fixture");
            module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
                tuple_type,
                size: 2,
                align: 1,
                field_offsets: vec![1, 0],
            });
        },
        named: |error| {
            matches!(error, AdapterError::DeclaredTupleLayoutDisagrees {
                module, declared: 1, emitted: 0, ..
            } if module == "pin_move_floor")
        },
    },
    Row {
        field: "Module.global_asm",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            module
                .global_asm
                .push(".globl marker\nmarker:\n  ret".into())
        },
        named: |error| {
            matches!(error, AdapterError::GlobalAsmUnsupported { module, blocks: 1 }
                if module == "pin_move_floor")
        },
    },
    Row {
        field: "Function.linkage",
        scope: Scope::TargetNeutral,
        mutate: |module| module.functions[0].linkage = Linkage::ExternalWeak,
        named: |error| {
            matches!(error, AdapterError::UnsupportedLinkage { symbol, linkage: Linkage::ExternalWeak, .. }
                if symbol == "entry")
        },
    },
    Row {
        // The default entries refuse every function section; the AArch64
        // ELF module policy that admits one on a definition is pinned in
        // `v41_contract_surface.rs`.
        field: "Function.section",
        scope: Scope::TargetNeutral,
        mutate: |module| module.functions[0].section = Some(".text.hot".into()),
        named: |error| {
            matches!(error, AdapterError::UnsupportedV45FunctionSurface { function, facet: "section", .. }
                if function == "entry")
        },
    },
    Row {
        field: "Function.section (malformed name)",
        scope: Scope::TargetNeutral,
        mutate: |module| module.functions[0].section = Some(".text hot".into()),
        named: |error| {
            matches!(error, AdapterError::MalformedFunctionSection { function, section, .. }
                if function == "entry" && section == ".text hot")
        },
    },
    Row {
        field: "Function.visibility",
        scope: Scope::TargetNeutral,
        mutate: |module| module.functions[0].visibility = Visibility::Protected,
        named: |error| {
            matches!(error, AdapterError::UnsupportedV45FunctionSurface { function, facet: "visibility", value }
                if function == "entry" && value == "protected")
        },
    },
    Row {
        field: "Function.retained",
        scope: Scope::TargetNeutral,
        mutate: |module| module.functions[0].retained = true,
        named: |error| {
            matches!(error, AdapterError::UnsupportedV45FunctionSurface { function, facet: "retained", .. }
                if function == "entry")
        },
    },
    Row {
        field: "FuncAttrs.naked",
        scope: Scope::TargetNeutral,
        mutate: |module| module.functions[0].attrs.naked = true,
        named: |error| matches!(error, AdapterError::NakedFunction { function } if function == "entry"),
    },
    Row {
        field: "FuncAttrs.target_features",
        scope: Scope::TargetDependent,
        mutate: |module| module.functions[0].attrs.target_features = vec!["not-a-feature".into()],
        named: |error| {
            matches!(error, AdapterError::UnknownTargetFeature { function, feature, .. }
                if function == "entry" && feature == "not-a-feature")
        },
    },
    Row {
        field: "ParamAttrs.byval",
        scope: Scope::Lowering,
        mutate: |module| {
            module.functions[0].attrs.params = vec![ParamAttrs {
                byval: true,
                ..ParamAttrs::default()
            }];
        },
        named: |error| {
            matches!(error, AdapterError::ByvalParamUnsupported { function, index: 0 }
                if function == "entry")
        },
    },
    Row {
        // Adversarial review: before this row a byval DECLARATION reached
        // through its address was lowered with a plain-pointer indirect call
        // on every entry, the caller-made copy silently dropped.
        field: "ParamAttrs.byval (declaration reached through its address)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            call_declaration_through_its_address(
                module,
                ParamAttrs {
                    byval: true,
                    ..ParamAttrs::default()
                },
            );
        },
        named: |error| {
            matches!(error, AdapterError::ByvalParamUnsupported { function, index: 0 }
                if function == "take")
        },
    },
    Row {
        field: "Global.linkage",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            let mut global = data_global("TABLE");
            global.linkage = Linkage::ExternalWeak;
            global.initializer = None;
            module.globals.push(global);
        },
        named: |error| {
            matches!(error, AdapterError::UnsupportedLinkage { symbol, linkage: Linkage::ExternalWeak, .. }
                if symbol == "TABLE")
        },
    },
    Row {
        // A WELL-FORMED name is target-dependent (placed on AArch64, refused
        // elsewhere); `v41_contract_surface.rs` pins that split. The name
        // itself is refused on every lane when no object format can carry it.
        field: "Global.section (malformed name)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            let mut global = data_global("TABLE");
            global.section = Some("__DATA, __custom".into());
            module.globals.push(global);
        },
        named: |error| {
            matches!(error, AdapterError::MalformedGlobalSection { global, section, .. }
                if global == "TABLE" && section == "__DATA, __custom")
        },
    },
    Row {
        field: "Global.visibility (import)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            let mut global = data_global("TABLE");
            global.linkage = Linkage::External;
            global.initializer = None;
            global.visibility = Visibility::Hidden;
            module.globals.push(global);
        },
        named: |error| {
            matches!(error, AdapterError::ImportVisibilityUnsupported { global, visibility: Visibility::Hidden }
                if global == "TABLE")
        },
    },
    Row {
        field: "ProofObligation.kind+status",
        scope: Scope::TargetNeutral,
        // `Discharged`, not `Certified`: a `Certified` row with no CleanCic
        // certificate is refused first by trust-ir's structural pass
        // (`CertifiedWithoutCleanCic`, consumed by name in
        // `validate_codegen_prerequisites` since KIND 4), so the twin claims
        // completion with the status that reaches THIS field's own arm.
        mutate: |module| {
            module.proof_obligations.push(obligation(
                0,
                ObligationKind::Termination,
                ProofStatus::Discharged,
            ));
        },
        named: |error| {
            matches!(
                error,
                AdapterError::UnrecognizedObligationKind {
                    obligation: 0,
                    status: ProofStatus::Discharged,
                    ..
                }
            )
        },
    },
    Row {
        field: "ProofCertificate.evidence (external inheritance)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            module.proof_obligations.push(obligation(
                0,
                ObligationKind::MemorySafety,
                ProofStatus::Pending,
            ));
            module.proof_obligations.push(obligation(
                1,
                ObligationKind::MemorySafety,
                ProofStatus::Discharged,
            ));
            let import = module
                .intern_import(ModuleImport::new(
                    "sibling",
                    trust_ir::proof::ProofDigest::zero(),
                ))
                .expect("Module::intern_import: test fixture");
            module.proof_certificates.push(ProofCertificate {
                obligation: ProofId::new(0),
                prover: "hand".to_string(),
                evidence: ProofEvidence::InheritedFromCallee {
                    callee: FuncId::new(0),
                    obligation: ProofId::new(1),
                    external: Some(ExternRef::new(import, "sibling_fn")),
                },
                assurance: None,
            });
        },
        named: |error| {
            matches!(error, AdapterError::ExternalEvidenceInheritance { certificate: 0, symbol, .. }
                if symbol == "sibling_fn")
        },
    },
    // trust-ir v47-v49 (the crystal lane): body and constant constructs no
    // lane models, refused on the shared floor before any lane transforms
    // or lowers a body.
    Row {
        field: "Inst::Drop (v47)",
        scope: Scope::TargetNeutral,
        // Since trust-ir v55 a drop of a trivially droppable type is not the
        // one spelling of a drop (trust-ir's own verdict refuses it first),
        // so the row drops a struct whose glue the table RESOLVES: a resolved
        // drop is refused by name all the same.
        mutate: |module| {
            add_owner_drop_glue(module);
            insert_in_entry(
                module,
                0,
                InstrNode::new(Inst::Drop {
                    ty: Ty::Struct(StructId::new(0)),
                    ptr: ValueId::new(0),
                }),
            )
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct { location, construct: "Inst::Drop", .. }
                if location == "function `entry` bb0")
        },
    },
    Row {
        field: "Inst::CmpXchg.weak (v48)",
        scope: Scope::TargetNeutral,
        mutate: |module| insert_in_entry(module, 1, cmpxchg_on_entry_pointer(true)),
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct {
                location,
                construct: "Inst::CmpXchg { weak: true }",
                ..
            } if location == "function `entry` bb0")
        },
    },
    Row {
        field: "Constant::Uninit (v49, an Inst::Const lane)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            insert_in_entry(
                module,
                0,
                InstrNode::new(Inst::Const {
                    ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
                    value: tuple_with_unwritten_lane(),
                })
                .with_result(ValueId::new(9)),
            )
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct { location, construct: "Constant::Uninit", .. }
                if location == "function `entry` bb0")
        },
    },
    Row {
        field: "Constant::Uninit (v49, a Global.initializer)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            let mut global = data_global("TABLE");
            global.ty = Ty::Tuple(vec![Ty::I64, Ty::I64]);
            global.initializer = Some(tuple_with_unwritten_lane());
            module.globals.push(global);
        },
        // Not valid TrustIR at all: every entry that consumes TrustIR's typed
        // admission refuses it there, naming the global and the unwritten
        // lane; the floors that do not run admission name the construct.
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct { location, construct: "Constant::Uninit", .. }
                if location == "global `TABLE`")
                || matches!(error, AdapterError::TrustIrAdmissionRefused { error }
                    if error == "global 'TABLE': const type mismatch: expected `uninit` only as a \
                        direct lane of an Inst::Const struct/tuple aggregate, got an unwritten \
                        lane (uninit) in a global initializer")
        },
    },
    // trust-ir v53: the non-propagating call boundaries. Enforce-or-refuse
    // (trust-ir LIMITATIONS.md): no lane emits the abort-on-unwind call-site
    // range, so the shared floor refuses both by name, and an ordinary call
    // in the same place still compiles (`accepted_neighbours_...`).
    Row {
        field: "Inst::CallCannotUnwind (v53)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            insert_in_entry(
                module,
                0,
                InstrNode::new(Inst::CallCannotUnwind {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(0)],
                })
                .with_result(ValueId::new(9)),
            )
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct { location, construct: "Inst::CallCannotUnwind", .. }
                if location == "function `entry` bb0")
        },
    },
    Row {
        field: "Inst::CallIndirectCannotUnwind (v53)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            let sig = module.functions[0].ty;
            insert_in_entry(
                module,
                0,
                InstrNode::new(Inst::Const {
                    ty: Ty::Func(sig),
                    value: Constant::FnDef(FuncId::new(0)),
                })
                .with_result(ValueId::new(8)),
            );
            insert_in_entry(
                module,
                1,
                InstrNode::new(Inst::CallIndirectCannotUnwind {
                    callee: ValueId::new(8),
                    sig,
                    args: vec![ValueId::new(0)],
                    calling_conv: CallingConv::C,
                })
                .with_result(ValueId::new(9)),
            )
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct {
                location,
                construct: "Inst::CallIndirectCannotUnwind",
                ..
            } if location == "function `entry` bb0")
        },
    },
    // trust-ir v55 / v56 (amendment D): the unwinding twins of a drop and of
    // an indirect call. No lane lowers a drop, and none routes an indirect
    // callee's unwind to an in-frame pad, so the shared floor refuses both by
    // name; the drop is refused even at a type the drop-glue table resolves.
    Row {
        field: "Inst::DropInvoke (v55)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            add_owner_drop_glue(module);
            split_entry_at_unwinding_twin(
                module,
                vec![],
                Inst::DropInvoke {
                    ty: Ty::Struct(StructId::new(0)),
                    ptr: ValueId::new(0),
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                },
            );
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct {
                location,
                construct: "Inst::DropInvoke",
                ..
            } if location == "function `entry` bb0")
        },
    },
    Row {
        field: "Inst::InvokeIndirect (v56)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            let sig = module.functions[0].ty;
            split_entry_at_unwinding_twin(
                module,
                vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::Func(sig),
                        value: Constant::FnDef(FuncId::new(0)),
                    })
                    .with_result(ValueId::new(8)),
                ],
                Inst::InvokeIndirect {
                    callee: ValueId::new(8),
                    sig,
                    args: vec![ValueId::new(0)],
                    calling_conv: CallingConv::C,
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                },
            );
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct {
                location,
                construct: "Inst::InvokeIndirect",
                ..
            } if location == "function `entry` bb0")
        },
    },
    Row {
        field: "TargetInfo.pointer_size",
        scope: Scope::TargetDependent,
        mutate: |module| {
            module.target_info = Some(target(4, Endianness::Little, StructPassingPolicy::NativeC));
        },
        named: |error| {
            matches!(error, AdapterError::TargetPointerSizeMismatch {
                module,
                pointer_size: 4,
                expected: 8,
                ..
            } if module == "pin_move_floor")
        },
    },
    Row {
        field: "TargetInfo.endianness",
        scope: Scope::TargetDependent,
        mutate: |module| {
            module.target_info = Some(target(8, Endianness::Big, StructPassingPolicy::NativeC));
        },
        named: |error| {
            matches!(error, AdapterError::TargetEndiannessUnsupported {
                module,
                endianness: Endianness::Big,
            } if module == "pin_move_floor")
        },
    },
    Row {
        field: "TargetInfo.struct_passing",
        scope: Scope::TargetDependent,
        mutate: |module| {
            module.target_info = Some(target(
                8,
                Endianness::Little,
                StructPassingPolicy::AlwaysMemory,
            ));
        },
        named: |error| {
            matches!(error, AdapterError::TargetStructPassingUnsupported {
                module,
                policy: StructPassingPolicy::AlwaysMemory,
            } if module == "pin_move_floor")
        },
    },
];

/// Every native module entry must refuse `module` with the row's OWN named
/// error. A refusal only one entry enforces is a bypass, and a refusal under
/// a different name is not the field's refusal.
// Precision migration: these identical original modules now retain real native
// call/location/unwind delivery, rather than universal panic-site refusal.
const PANIC_DELIVERY_ROWS: &[Row] = &[
    // trust-ir v54 (amendment P): the panic site. A sited check's failure
    // calls its entry with the location; no lane lowers that call, so the
    // shared floor's assert clause refuses both spellings by name, before the
    // check's kind is consulted.
    Row {
        field: "Inst::Assert { site: Some(_) } (v54)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            add_panic_entry(module);
            insert_in_entry(module, 0, true_condition());
            insert_in_entry(
                module,
                1,
                InstrNode::new(Inst::Assert {
                    cond: ValueId::new(8),
                    kind: AssertKind::DivByZero,
                    site: Some(entry_pointer_panic_site()),
                }),
            );
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct {
                location,
                construct: "Inst::Assert { site: Some(_) }",
                ..
            } if location == "function `entry` bb0 instruction 1")
        },
    },
    Row {
        field: "Inst::AssertInvoke (v54)",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            add_panic_entry(module);
            // bb0: the check, continuing to bb1 (the control's return) or
            // unwinding to the cleanup pad bb2.
            let entry = &mut module.functions[0];
            let tail = entry.blocks[0].body.split_off(1);
            entry.blocks[0].body.insert(0, true_condition());
            entry.blocks[0]
                .body
                .push(InstrNode::new(Inst::AssertInvoke {
                    cond: ValueId::new(8),
                    kind: AssertKind::DivByZero,
                    site: entry_pointer_panic_site(),
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                }));
            let mut normal = Block::new(BlockId::new(1));
            normal.body = tail;
            let mut pad = Block::new(BlockId::new(2));
            pad.body.push(
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results([ValueId::new(20), ValueId::new(21)]),
            );
            pad.body.push(InstrNode::new(Inst::Resume {
                exn: ValueId::new(20),
            }));
            entry.blocks.push(normal);
            entry.blocks.push(pad);
        },
        named: |error| {
            matches!(error, AdapterError::UnmodeledTrustIrConstruct {
                location,
                construct: "Inst::AssertInvoke",
                ..
            } if location == "function `entry` bb0 instruction 2")
        },
    },
];

#[test]
fn original_panic_site_rows_keep_inputs_and_gain_native_call_delivery() {
    for row in PANIC_DELIVERY_ROWS {
        let mut module = control_module();
        (row.mutate)(&mut module);
        let original = module.clone();
        assert_accepted_everywhere(row.field, &module);
        let lir = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap()
        .0;
        assert_eq!(
            lir.blocks
                .values()
                .flat_map(|b| &b.instructions)
                .filter(|i| matches!(
                    i.opcode,
                    trust_cg_lower::instructions::Opcode::Call { .. }
                        | trust_cg_lower::instructions::Opcode::Invoke { .. }
                ))
                .count(),
            1
        );
        assert_eq!(module, original);
    }
}

fn assert_refused_by_name_everywhere(row: &Row, module: &Module) {
    assert_refused_everywhere(row.field, row.scope, module, row.named);
}

fn assert_refused_everywhere(
    field: &str,
    scope: Scope,
    module: &Module,
    named: impl Fn(&AdapterError) -> bool,
) {
    let check = |entry: &str, result: Result<(), AdapterError>| match result {
        Err(error) => assert!(
            named(&error),
            "{field}: {entry} refused under the wrong name: {error:?}"
        ),
        Ok(()) => panic!("{field}: {entry} accepted a non-default value"),
    };
    check(
        "translate_module",
        permit_translate_module(module).map(drop),
    );
    for arch in ARCHES {
        check(
            "translate_module_for_arch",
            permit_translate_module_for_arch(module, arch).map(drop),
        );
    }
    check(
        "translate_module_for_arch_with_tls_and_validation",
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            module,
            GuardCarrierArch::AArch64,
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .map(drop),
    );
    check(
        "translate_function",
        trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            module,
            &permit_unlicensed(),
        )
        .map(drop),
    );
    check(
        "translate_function_with_names",
        trust_cg_lower::translate_function_with_names_and_license(
            &module.functions[0],
            module,
            &HashMap::new(),
            &permit_unlicensed(),
        )
        .map(drop),
    );
    // The strict, already-validated entry (Core admission) skips the
    // compatibility prerequisites and must run the floor itself.
    // `validate_module` lets a module CARRY these values, so when the report
    // is clean the refusal must be ours.
    let report = trust_ir_build::validate_module_report(module);
    if report.is_ok() {
        check(
            "translate_validated_module_strict_for_arch_with_tls_and_validation",
            trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                &report,
                GuardCarrierArch::AArch64,
                TlsDialect::default(),
            &permit_unlicensed(),)
            .map(drop),
        );
    }
    match scope {
        Scope::TargetNeutral => {
            check(
                "reject_unconsumed_v41_target_neutral_surface",
                reject_unconsumed_v41_target_neutral_surface(module),
            );
            check(
                "prepare_module_for_lir",
                prepare_module_for_lir(module, GuardCarrierArch::AArch64).map(drop),
            );
            for arch in ARCHES {
                check(
                    "reject_unconsumed_v41_surface",
                    reject_unconsumed_v41_surface(module, arch),
                );
            }
        }
        Scope::TargetDependent => {
            // The shared floor the wasm lane applies must NOT decide it: that
            // lane owns its own target and feature vocabulary.
            reject_unconsumed_v41_target_neutral_surface(module)
                .unwrap_or_else(|error| panic!("{field}: target-neutral floor refused: {error:?}"));
            check(
                "prepare_module_for_lir",
                prepare_module_for_lir(module, GuardCarrierArch::AArch64).map(drop),
            );
            for arch in ARCHES {
                check(
                    "reject_unconsumed_v41_surface",
                    reject_unconsumed_v41_surface(module, arch),
                );
            }
        }
        Scope::Lowering => {
            // Refused where the function is lowered; the floor classifies it
            // and lets the lowering site name it.
            reject_unconsumed_v41_target_neutral_surface(module)
                .unwrap_or_else(|error| panic!("{field}: floor refused: {error:?}"));
        }
    }
}

fn assert_accepted_everywhere(label: &str, module: &Module) {
    permit_translate_module(module)
        .unwrap_or_else(|error| panic!("{label}: translate_module: {error:?}"));
    for arch in ARCHES {
        permit_translate_module_for_arch(module, arch)
            .unwrap_or_else(|error| panic!("{label}: {arch}: {error:?}"));
        reject_unconsumed_v41_surface(module, arch)
            .unwrap_or_else(|error| panic!("{label}: {arch} floor: {error:?}"));
    }
    prepare_module_for_lir(module, GuardCarrierArch::AArch64)
        .unwrap_or_else(|error| panic!("{label}: prepare_module_for_lir: {error:?}"));
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{label}: translate_function: {error:?}"));
}

#[test]
fn control_module_is_accepted_on_every_native_entry() {
    let module = control_module();
    assert_eq!(module.completeness, None);
    reject_unconsumed_v41_target_neutral_surface(&module).expect("None makes no claim");
    assert_accepted_everywhere("completeness: None", &module);
    assert_eq!(
        module.completeness, None,
        "admission must not stamp a claim"
    );
}

#[test]
fn disagreeing_formula_texts_are_refused_on_every_native_entry() {
    let row = Row {
        field: "ProofObligation.formula",
        scope: Scope::TargetNeutral,
        mutate: |module| {
            let mut formula = ProofFormula::smtlib2("(>= 0 5)", "Bool");
            formula.smtlib = Some("(>= 5 0)".into());
            let mut claim = obligation(0, ObligationKind::Postcondition, ProofStatus::Pending);
            claim.formula = Some(formula);
            module.proof_obligations.push(claim);
        },
        named: |error| {
            matches!(error, AdapterError::TrustIrAdmissionRefused { error }
                if error.contains("obligation #0")
                    && error.contains("formula states two SMT-LIB texts"))
        },
    };
    // Consistency is a property of the formula, not of its completion status.
    for status in [ProofStatus::Pending, ProofStatus::Discharged] {
        let mut module = control_module();
        (row.mutate)(&mut module);
        module.proof_obligations[0].status = status;
        let original = module.proof_obligations[0].clone();
        assert_refused_by_name_everywhere(&row, &module);
        assert_eq!(
            module.proof_obligations[0], original,
            "do not repair the claim"
        );
    }
}

/// One stated formula per case (except the consistent other LeadsTo leaf).
/// These are unproved summaries and non-certifying DesignOnly specs.
fn summary_and_spec_formula_cases(formula: &ProofFormula) -> Vec<(FormulaSite, Module)> {
    use trust_ir::{FunctionSummary, SpecInvariant, SpecModule, SpecTemporal, TemporalForm};

    let mut cases = Vec::new();
    for (clause, summary) in [
        (
            "requires",
            FunctionSummary::new().requiring(formula.clone()),
        ),
        ("ensures", FunctionSummary::new().ensuring(formula.clone())),
        (
            "decreases",
            FunctionSummary::new().decreasing(formula.clone()),
        ),
    ] {
        let mut module = control_module();
        module.functions[0].summary = Some(summary.with_params(vec!["p".into()]));
        cases.push((
            FormulaSite::SummaryClause {
                function: FuncId::new(0),
                clause,
                index: 0,
            },
            module,
        ));
    }
    let mut spec = SpecModule::design_only("formula_floor");
    spec.invariants
        .push(SpecInvariant::new("Invariant", "design predicate").with_typed(formula.clone()));
    let mut module = control_module();
    module.spec_modules.push(spec);
    cases.push((
        FormulaSite::SpecInvariant {
            machine: "formula_floor".into(),
            invariant: "Invariant".into(),
        },
        module,
    ));
    let other = ProofFormula::smtlib2("true", "Bool");
    for (property, form) in [
        ("Always", TemporalForm::Always(formula.clone())),
        ("Eventually", TemporalForm::Eventually(formula.clone())),
        (
            "LeadsToLeft",
            TemporalForm::LeadsTo(formula.clone(), other.clone()),
        ),
        (
            "LeadsToRight",
            TemporalForm::LeadsTo(other, formula.clone()),
        ),
        (
            "WeakFair",
            TemporalForm::WeakFair {
                action: "Step".into(),
                relation: Some(formula.clone()),
            },
        ),
        (
            "StrongFair",
            TemporalForm::StrongFair {
                action: "Step".into(),
                relation: Some(formula.clone()),
            },
        ),
    ] {
        let mut spec = SpecModule::design_only("formula_floor");
        spec.actions.push("Step".into());
        spec.temporal.push(SpecTemporal::new(property, form));
        let mut module = control_module();
        module.spec_modules.push(spec);
        cases.push((
            FormulaSite::SpecTemporal {
                machine: "formula_floor".into(),
                property: property.into(),
            },
            module,
        ));
    }
    cases
}

#[test]
fn summary_and_spec_formula_texts_are_refused_on_every_native_entry() {
    let mut formula = ProofFormula::smtlib2("(>= 0 5)", "Bool");
    formula.smtlib = Some("(>= 5 0)".into());
    for (site, module) in summary_and_spec_formula_cases(&formula) {
        let original = module.clone();
        let expected = trust_ir_build::ValidationError::FormulaTextsDisagree { site: site.clone() }
            .to_string();
        assert_refused_everywhere(
            &site.to_string(),
            Scope::TargetNeutral,
            &module,
            |error| matches!(error, AdapterError::TrustIrAdmissionRefused { error } if error == &expected),
        );
        assert_eq!(module, original, "{site}: do not repair the formula");
    }
}

#[test]
fn consistent_and_opaque_formula_metadata_remain_admissible() {
    let consistent = ProofFormula::smtlib2("(>= 5 0)", "Bool");
    let mut absent = consistent.clone();
    absent.smtlib = None;
    let mut opaque = ProofFormula::new("test.opaque@1", "{\"predicate\":\"opaque\"}");
    opaque.smtlib = Some("(>= 5 0)".into());
    for status in [ProofStatus::Pending, ProofStatus::Discharged] {
        for (label, formula) in [
            ("equal SMT-LIB rendering", &consistent),
            ("absent SMT-LIB rendering", &absent),
            ("opaque payload with rendering", &opaque),
        ] {
            let mut module = control_module();
            let mut claim = obligation(0, ObligationKind::Postcondition, status);
            claim.formula = Some(formula.clone());
            module.proof_obligations.push(claim.clone());
            // Carrying opaque metadata is not using its rendering as evidence.
            reject_unconsumed_v41_target_neutral_surface(&module).expect(label);
            assert_accepted_everywhere(label, &module);
            assert_eq!(
                module.proof_obligations[0], claim,
                "{label}: do not rewrite metadata"
            );
        }
    }
    for formula in [&consistent, &absent, &opaque] {
        for (site, module) in summary_and_spec_formula_cases(formula) {
            let original = module.clone();
            reject_unconsumed_v41_target_neutral_surface(&module).expect("consistent carrier");
            assert_accepted_everywhere(&site.to_string(), &module);
            assert_eq!(module, original, "{site}: do not rewrite metadata");
        }
    }
}

#[test]
fn completeness_claims_are_refused_even_when_well_formed() {
    let missing = UnloweredRow {
        symbol: "missing".into(),
        display_path: Some("source::missing".into()),
        reason: "producer could not lower the body".into(),
    };
    let row = ROWS
        .iter()
        .find(|row| row.field == "Module.completeness")
        .expect("the field has a named floor refusal");
    for (label, claim, valid) in [
        ("complete", ModuleCompleteness::Complete, true),
        (
            "valid partial",
            ModuleCompleteness::Partial(vec![missing.clone()]),
            true,
        ),
        ("empty partial", ModuleCompleteness::Partial(vec![]), false),
        (
            "partial naming a definition",
            ModuleCompleteness::Partial(vec![UnloweredRow {
                symbol: "entry".into(),
                ..missing.clone()
            }]),
            false,
        ),
        (
            "duplicate partial rows",
            ModuleCompleteness::Partial(vec![missing.clone(), missing]),
            false,
        ),
    ] {
        let mut module = control_module();
        module.completeness = Some(claim.clone());
        let errors = trust_ir_build::validate_module(&module);
        assert_eq!(errors.is_empty(), valid, "{label}: {errors:?}");
        assert_refused_by_name_everywhere(row, &module);
        assert_eq!(module.completeness, Some(claim), "{label}: claim erased");
    }
}

#[test]
fn every_refused_field_is_refused_by_its_own_name() {
    for row in ROWS {
        let mut module = control_module();
        (row.mutate)(&mut module);
        assert_ne!(
            module,
            control_module(),
            "{}: mutation is a no-op",
            row.field
        );
        assert_refused_by_name_everywhere(row, &module);
    }
}

#[test]
fn refused_rows_name_distinct_fields() {
    let mut fields: Vec<&str> = ROWS
        .iter()
        .chain(PANIC_DELIVERY_ROWS.iter())
        .map(|row| row.field)
        .collect();
    fields.sort_unstable();
    let before = fields.len();
    fields.dedup();
    assert_eq!(before, fields.len(), "a field has two rows");
}

/// The accepted neighbours of the refused values: the refusal is exactly the
/// non-default value, not the field's presence.
#[test]
fn accepted_neighbours_of_refused_values_still_compile() {
    // Target-free IR declares nothing to contradict.
    let mut module = control_module();
    module.target_info = None;
    assert_accepted_everywhere("target_info: None", &module);

    // v55: the drop-glue table itself is inert. A module that registers the
    // glue of a type it never drops compiles on every native entry; only a
    // drop site (`Inst::Drop` / `Inst::DropInvoke`) is refused.
    let mut module = control_module();
    add_owner_drop_glue(&mut module);
    assert_eq!(module.drop_glue.len(), 1);
    assert_accepted_everywhere("drop_glue: one row, no drop site", &module);

    // v53: the ORDINARY call in the place of a refused non-propagating
    // boundary compiles; the refusal is the boundary, not the call.
    let mut module = control_module();
    insert_in_entry(
        &mut module,
        0,
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(9)),
    );
    assert_accepted_everywhere("ordinary Call (v53 neighbour)", &module);

    // WS7.7: a declared tuple layout EQUAL to the declaration-order layout the
    // byte path emits is consumed — honoured by construction.
    let mut module = control_module();
    let tuple_type = module
        .add_type(Ty::Tuple(vec![Ty::U8, Ty::U8]))
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type,
        size: 2,
        align: 1,
        field_offsets: vec![0, 1],
    });
    assert_accepted_everywhere("tuple_layouts: declaration-order row", &module);

    // `Unclassified` records the absence of a producer classification (v36);
    // while no aggregate crosses a call edge by value there is nothing to
    // classify, and the native lanes lower exactly as for `NativeC`. Beside a
    // by-value aggregate signature or indirect call it is refused
    // (`TargetStructPassingUnclassified`, KIND 4; the indirect shape below).
    let mut module = control_module();
    module.target_info = Some(target(
        8,
        Endianness::Little,
        StructPassingPolicy::Unclassified,
    ));
    assert_accepted_everywhere("struct_passing: Unclassified", &module);

    // A DEFINITION's visibility is consumed by the object emitters.
    let mut module = control_module();
    let mut global = data_global("TABLE");
    global.linkage = Linkage::External;
    global.visibility = Visibility::Hidden;
    module.globals.push(global);
    assert_accepted_everywhere("hidden definition", &module);

    // A kind this backend grants nothing for, claiming nothing.
    let mut module = control_module();
    module.proof_obligations.push(obligation(
        0,
        ObligationKind::Termination,
        ProofStatus::Pending,
    ));
    assert_accepted_everywhere("pending termination obligation", &module);

    // Optimization-hint attributes are sound to ignore.
    let mut module = control_module();
    let attrs = &mut module.functions[0].attrs;
    attrs.readonly = true;
    attrs.readnone = true;
    attrs.inlinehint = true;
    attrs.cold = true;
    attrs.params = vec![ParamAttrs {
        dereferenceable: Some(8),
        nonnull: true,
        align: Some(8),
        noalias: true,
        readonly: true,
        byval: false,
        sret: false,
        ext: Default::default(),
        pass: None,
    }];
    assert_accepted_everywhere("hint attributes", &module);
}

/// v48: the refusal is the WEAK flag, not the instruction — the strong
/// compare-exchange the weak row mutates passes the floor and lowers.
#[test]
fn strong_cmpxchg_is_the_accepted_neighbour_of_the_weak_refusal() {
    let mut module = control_module();
    insert_in_entry(&mut module, 1, cmpxchg_on_entry_pointer(false));
    reject_unconsumed_v41_target_neutral_surface(&module)
        .unwrap_or_else(|error| panic!("strong CmpXchg: floor refused: {error:?}"));
    permit_translate_module_for_arch(&module, GuardCarrierArch::AArch64)
        .unwrap_or_else(|error| panic!("strong CmpXchg: AArch64 lowering refused: {error:?}"));
}

/// The target-dependent rows are decided per architecture, and a 32-bit or
/// big-endian target is refused on EVERY one this backend lowers for.
#[test]
fn target_info_refusals_hold_on_every_architecture() {
    for arch in ARCHES {
        let mut module = control_module();
        module.target_info = Some(target(4, Endianness::Little, StructPassingPolicy::NativeC));
        assert!(matches!(
            reject_unconsumed_v41_surface(&module, arch),
            Err(AdapterError::TargetPointerSizeMismatch { arch: refused, expected: 8, .. })
                if refused == arch
        ));
        module.target_info = Some(target(16, Endianness::Little, StructPassingPolicy::NativeC));
        assert!(matches!(
            reject_unconsumed_v41_surface(&module, arch),
            Err(AdapterError::TargetPointerSizeMismatch {
                pointer_size: 16,
                ..
            })
        ));
    }
}

/// Adversarial review, the accepted twin of the byval-declaration row: the
/// same indirect call through a declaration's address, without the attribute,
/// still lowers on every native entry. The refusal is the attribute, not the
/// shape.
#[test]
fn plain_declaration_reached_through_its_address_still_compiles() {
    let mut module = control_module();
    call_declaration_through_its_address(&mut module, ParamAttrs::default());
    assert_accepted_everywhere("plain declaration through its address", &module);
}

/// Adversarial review: a declaration that is BOTH a malformed sret one and
/// byval keeps the direct-call route's `[TCG-SRET-ABI]` diagnostic when the
/// floor refuses it, on every entry, whether or not anything calls it.
#[test]
fn byval_sret_declaration_keeps_the_sret_diagnostic() {
    for reached in [false, true] {
        let mut module = control_module();
        let attrs = ParamAttrs {
            byval: true,
            sret: true,
            ..ParamAttrs::default()
        };
        if reached {
            call_declaration_through_its_address(&mut module, attrs);
        } else {
            let sig = module.functions[0].ty;
            let mut take = Function::new(FuncId::new(1), "take", sig, BlockId::new(0));
            take.blocks = Vec::new();
            take.attrs.params = vec![attrs];
            module.functions.push(take);
        }
        let sret = |label: &str, result: Result<(), AdapterError>| {
            let error = result.expect_err(label);
            assert!(
                error.to_string().contains("[TCG-SRET-ABI]"),
                "{label} (reached={reached}): {error}"
            );
        };
        sret(
            "neutral floor",
            reject_unconsumed_v41_target_neutral_surface(&module),
        );
        sret(
            "translate_module",
            permit_translate_module(&module).map(drop),
        );
        for arch in ARCHES {
            sret(
                "translate_module_for_arch",
                permit_translate_module_for_arch(&module, arch).map(drop),
            );
        }
        sret(
            "translate_function",
            trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed(),
            )
            .map(drop),
        );
    }
}

/// Adversarial review: the `TargetInfo` values the real producers stamp must
/// NOT be refused on the architecture they name — the new target rows refuse
/// a contradiction, never a producer's honest declaration. The stamps are
/// copied from `rustc-codegen-trust-cg` (`NativeC`, no ABI name — since
/// 2026-09-25; it stamped `Unclassified` before, which the KIND 4 floor
/// refuses beside every by-value C-ABI aggregate the bridge emits), Clean's
/// general-island emitter (`NativeC`, no ABI name), a producer that
/// classifies nothing (`Unclassified`, no ABI name — admitted while no
/// aggregate crosses by value), and the tRust frontend's module test fixture
/// (`NativeC`, `aapcs64`).
#[test]
fn producer_target_stamps_are_accepted_on_their_own_architecture() {
    let stamps = [
        (
            "aarch64-apple-darwin",
            None,
            StructPassingPolicy::NativeC,
            GuardCarrierArch::AArch64,
        ),
        (
            "x86_64-unknown-linux-gnu",
            None,
            StructPassingPolicy::NativeC,
            GuardCarrierArch::X86_64,
        ),
        (
            "aarch64-apple-darwin",
            None,
            StructPassingPolicy::Unclassified,
            GuardCarrierArch::AArch64,
        ),
        (
            "x86_64-unknown-linux-gnu",
            None,
            StructPassingPolicy::Unclassified,
            GuardCarrierArch::X86_64,
        ),
        (
            "riscv64gc-unknown-linux-gnu",
            None,
            StructPassingPolicy::Unclassified,
            GuardCarrierArch::Riscv64,
        ),
        (
            "aarch64-apple-darwin",
            Some("aapcs64"),
            StructPassingPolicy::NativeC,
            GuardCarrierArch::AArch64,
        ),
        (
            "x86_64-apple-darwin",
            Some("sysv64"),
            StructPassingPolicy::NativeC,
            GuardCarrierArch::X86_64,
        ),
    ];
    for (triple, abi, struct_passing, arch) in stamps {
        let mut module = control_module();
        module.target_info = Some(TargetInfo {
            triple: triple.into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: abi.map(str::to_string),
            struct_passing,
        });
        reject_unconsumed_v41_surface(&module, arch)
            .unwrap_or_else(|error| panic!("{triple}: floor: {error:?}"));
        permit_translate_module_for_arch(&module, arch)
            .unwrap_or_else(|error| panic!("{triple}: translate_module_for_arch: {error:?}"));
    }
}

/// Under `Unclassified`, a by-value aggregate crossing through a FUNCTION
/// POINTER is refused even when NO function of the module carries the
/// aggregate signature: the `CallIndirect`'s `sig` is the only signature that
/// edge has. `entry(p, f) = f(*p)` with `f: (tuple) -> i64`; every function
/// type a function of the module declares is scalar.
///
/// Mutation control (measured 2026-09-25, before the floor walked
/// `CallIndirect` signatures): this module was ACCEPTED on every native entry
/// (`validate_module` empty), while its direct twin — the same aggregate
/// signature on a `take` declaration — was refused by the signature walk
/// alone. The reviewer's probe that found it is the same shape.
#[test]
fn unclassified_struct_passing_refuses_an_indirect_by_value_aggregate_call() {
    fn indirect_aggregate_call_module(policy: StructPassingPolicy) -> Module {
        let mut module = control_module();
        module.target_info = Some(target(8, Endianness::Little, policy));
        let pair = Ty::Tuple(vec![Ty::I64, Ty::I64]);
        let callee_sig = module
            .add_func_type(FuncTy {
                params: vec![pair.clone()],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let entry_sig = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::Func(callee_sig)],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let entry = &mut module.functions[0];
        entry.ty = entry_sig;
        let block = &mut entry.blocks[0];
        block.params.push((ValueId::new(1), Ty::Func(callee_sig)));
        block.body.clear();
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: pair,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(2)),
        );
        block.body.push(
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(1),
                sig: callee_sig,
                args: vec![ValueId::new(2)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(3)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }));
        // The premise: no function of the module carries an aggregate in its
        // own signature, so a walk of `Function.ty` alone sees nothing.
        for func in &module.functions {
            let sig = &module.func_types[func.ty.as_usize()];
            assert!(
                sig.params
                    .iter()
                    .chain(&sig.returns)
                    .all(|ty| !matches!(ty, Ty::Tuple(_))),
                "the premise needs every function signature scalar"
            );
        }
        assert!(
            trust_ir_build::validate_module(&module).is_empty(),
            "the shape is well-formed by every trust-ir rule; the refusal must be this backend's"
        );
        module
    }

    let row = Row {
        field: "TargetInfo.struct_passing (Unclassified beside an indirect by-value aggregate call)",
        scope: Scope::TargetDependent,
        mutate: |_| {},
        named: |error| {
            matches!(error, AdapterError::TargetStructPassingUnclassified { module, function, edge }
                if module == "pin_move_floor"
                    && function == "entry"
                    && edge.starts_with("calls indirectly through a signature that passes parameter 0"))
        },
    };
    let module = indirect_aggregate_call_module(StructPassingPolicy::Unclassified);
    assert_refused_by_name_everywhere(&row, &module);

    // The accepted neighbour: the same edge under a producer classification.
    let module = indirect_aggregate_call_module(StructPassingPolicy::NativeC);
    assert_accepted_everywhere(
        "NativeC beside an indirect by-value aggregate call",
        &module,
    );
}

/// trust-ir `docs/SPEC_RATIFICATIONS.md` §17 (trust-ir `7b0947ee`): ONE
/// by-value-aggregate-slot predicate, `Module::is_by_value_aggregate_slot`
/// (through one `Refine`: `Struct`, `Tuple`, `Array`, `Enum`, `Record`,
/// `Sequence`, `Set`, `Closure`, `Vector`), is the set a consumer's
/// `Unclassified` gate must use. This backend's gate used its own narrower set
/// (struct, tuple, array, record, enum) until this change, and ADMITTED an
/// `Unclassified` module passing a refined tuple, a `<4 x i32>` or a closure
/// by value — lowering each by the native C ABI the producer never
/// established (rustc's Rust ABI passes `int32x4_t` indirectly where
/// `extern "C"` passes it in a vector register).
///
/// Each shape is a bodyless declaration `take: (X) -> i64` beside the control
/// function, plus the refined tuple through a `CallIndirect` signature; each
/// is refused by name on every native entry under `Unclassified`, and its
/// `NativeC` twin is admitted everywhere (the refusal is the policy's).
///
/// MUTATION CONTROL (recorded in the commit): reverting `by_value_aggregate_edge`
/// to `TrustIrAdapter::trust_ir_ty_is_aggregate` makes all three
/// `Unclassified` shapes ACCEPTED on every entry and this test fail.
#[test]
fn unclassified_refuses_refined_vector_and_closure_by_value_slots() {
    fn with_slot(policy: StructPassingPolicy, slot: fn(&mut Module) -> Ty) -> Module {
        let mut module = control_module();
        module.target_info = Some(target(8, Endianness::Little, policy));
        let ty = slot(&mut module);
        let sig = module
            .add_func_type(FuncTy {
                params: vec![ty],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut take = Function::new(FuncId::new(1), "take", sig, BlockId::new(0));
        take.blocks = Vec::new();
        take.linkage = Linkage::External;
        module.functions.push(take);
        module
    }
    fn refined_tuple(module: &mut Module) -> Ty {
        let base = module
            .add_type(Ty::Tuple(vec![Ty::I64, Ty::I64]))
            .expect("Module::add_type: test fixture");
        let top = module
            .intern_pred(trust_ir::Pred::Top)
            .expect("Module::intern_pred: test fixture")
            .expect("Top is canonical");
        Ty::Refine(base, top)
    }
    fn vector(_: &mut Module) -> Ty {
        Ty::Vector(Box::new(Ty::I32), 4)
    }
    fn closure(module: &mut Module) -> Ty {
        let apparent = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        Ty::Closure(
            module
                .add_closure_type(trust_ir::ClosureTy {
                    func: apparent,
                    captures: vec![Ty::I64, Ty::I64, Ty::I64],
                })
                .expect("Module::add_closure_type: test fixture"),
        )
    }
    type SlotCtor = fn(&mut Module) -> Ty;
    let slots: [(&str, SlotCtor); 3] = [
        ("Refine(Tuple)", refined_tuple),
        ("Vector(I32, 4)", vector),
        ("Closure(3 captures)", closure),
    ];
    for (what, slot) in slots {
        let module = with_slot(StructPassingPolicy::Unclassified, slot);
        assert!(
            module.is_by_value_aggregate_slot(&slot(&mut module.clone())),
            "{what}: trust-ir's predicate calls it an aggregate slot"
        );
        let row = Row {
            field: "TargetInfo.struct_passing (Unclassified beside a §17 aggregate slot)",
            scope: Scope::TargetDependent,
            mutate: |_| {},
            named: |error| {
                matches!(error, AdapterError::TargetStructPassingUnclassified { module, function, edge }
                    if module == "pin_move_floor"
                        && function == "take"
                        && edge.starts_with("passes parameter 0"))
            },
        };
        assert_refused_by_name_everywhere(&row, &module);
        assert_accepted_everywhere(
            &format!("NativeC beside a by-value {what}"),
            &with_slot(StructPassingPolicy::NativeC, slot),
        );
    }

    // The refined tuple through a function POINTER: the `CallIndirect`'s
    // `sig` is the only signature that edge has.
    let indirect = |policy: StructPassingPolicy| {
        let mut module = control_module();
        module.target_info = Some(target(8, Endianness::Little, policy));
        let refined = refined_tuple(&mut module);
        let callee_sig = module
            .add_func_type(FuncTy {
                params: vec![refined],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let entry_sig = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::Func(callee_sig)],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let entry = &mut module.functions[0];
        entry.ty = entry_sig;
        let block = &mut entry.blocks[0];
        block.params.push((ValueId::new(1), Ty::Func(callee_sig)));
        block.body.clear();
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(2)),
        );
        block.body.push(
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(1),
                sig: callee_sig,
                args: vec![ValueId::new(2)],
                calling_conv: CallingConv::C,
            })
            .with_result(ValueId::new(3)),
        );
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }));
        module
    };
    let row = Row {
        field: "TargetInfo.struct_passing (Unclassified beside an indirect refined-aggregate call)",
        scope: Scope::TargetDependent,
        mutate: |_| {},
        named: |error| {
            matches!(error, AdapterError::TargetStructPassingUnclassified { function, edge, .. }
                if function == "entry"
                    && edge.starts_with("calls indirectly through a signature that passes parameter 0"))
        },
    };
    assert_refused_by_name_everywhere(&row, &indirect(StructPassingPolicy::Unclassified));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}

/// `translate_module_for_arch` under [`permit_unlicensed`].
fn permit_translate_module_for_arch(
    module: &trust_ir::Module,
    arch: trust_cg_lower::GuardCarrierArch,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        arch,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
