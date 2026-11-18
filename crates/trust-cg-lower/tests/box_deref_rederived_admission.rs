// trust-cg-lower/tests/box_deref_rederived_admission.rs - the opt-in re-derived floor admits only what this backend re-derives
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The consumer re-derivation of `Inst::BoxDeref` validity
//! (`trust_cg_lower::box_deref_rederive`) through every entry that admits a
//! module or a function:
//!
//! * at the DEFAULT floor (`Refuse`, trust-ir's `ConsumerRederived`) even a
//!   deref this backend wholly re-derives is refused by every entry, with
//!   trust-ir's verdict unchanged: the default never consults the
//!   re-derivation;
//! * at the opt-in `LocallyRederived` floor a deref whose three conjuncts
//!   this backend re-derives from the function is admitted by
//!   `admit_box_derefs`, the license policy's verdicts, `ingest::admit_module`
//!   and `translate_function_with_license`, with a manifest row that keeps
//!   the fact's own tier, lists the re-derived conjuncts, and is not an
//!   assumption;
//! * a near miss (one escape before the deref) is refused by every one of
//!   those entries with the same typed error, naming the conjunct and why it
//!   was not re-derived;
//! * the floors' names, order and license identities keep the consumer-local
//!   verdict apart from trust-ir's tier;
//! * the structural rules of the carried fact still refuse first;
//! * at the named-premise floor a wholly re-derived row is not disclosed as
//!   an assumption, and a partly re-derived one still is;
//! * the lowering of an admitted, re-derived deref is still exactly one
//!   `Copy` (no licence).
//!
//! Test rung. Nothing here is proof evidence: the re-derivation is this
//! consumer's decision and is never written into the module.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::box_deref::BoxDerefRefusal;
use trust_cg_lower::box_deref_rederive::NotRederived;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{
    BoxDerefDisclosure, BoxValidityFloor, CodegenLicensePolicy, Function, UnlicensedBodyPolicy,
    admit_box_derefs, admit_module, translate_function_with_license,
};
use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxValidityFact, BoxValidityTier, PremiseRoot, ValidityConjunct,
};
use trust_ir::inst::{AllocOrigin, CastOp, ICmpOp};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_owned(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn fact(ordinal: u32) -> BoxValidityFact {
    BoxValidityFact::premise(
        BoxDerefSite {
            item: [0x6b; 16],
            ordinal,
        },
        BoxFactSession::PROOF_SNAPSHOT,
        PremiseRoot::ParamByValue,
    )
}

/// The body of one fixture function `name(p: ptr) -> i64`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Body {
    /// A stack slot, stored to, dereffed as a box, read back.
    Slot,
    /// The same with the slot handed to the parameter's store first: an
    /// escape before the deref.
    SlotEscaping,
    /// The same body with the slot used directly: the no-licence control.
    SlotWithoutDeref,
    /// A guarded Rust-heap allocation dereffed as a box.
    GuardedHeap,
    /// The parameter dereffed as a box (the named-premise shape).
    Param,
}

fn emit(fb: &mut FunctionBuilder<'_>, body: Body, fact: &BoxValidityFact) {
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let deref = |fb: &mut FunctionBuilder<'_>, pointer: ValueId| -> ValueId {
        fb.box_deref(Ty::I64, pointer, fact.clone())
    };
    let boxed = match body {
        Body::Slot | Body::SlotEscaping | Body::SlotWithoutDeref => {
            let slot = fb.alloca(Ty::I64);
            let seven = fb.iconst(Ty::I64, 7);
            fb.store(Ty::I64, slot, seven);
            if body == Body::SlotEscaping {
                fb.store(Ty::Ptr, p, slot);
            }
            if body == Body::SlotWithoutDeref {
                slot
            } else {
                deref(fb, slot)
            }
        }
        Body::GuardedHeap => {
            let raw = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
            let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, raw);
            let zero = fb.iconst(Ty::I64, 0);
            let failed = fb.icmp(ICmpOp::Eq, Ty::I64, bits, zero);
            let error = fb.create_block();
            let ready = fb.create_block();
            fb.condbr(failed, error, vec![], ready, vec![]);
            fb.switch_to_block(error);
            let minus_one = fb.iconst(Ty::I64, -1);
            fb.ret(vec![minus_one]);
            fb.switch_to_block(ready);
            let nine = fb.iconst(Ty::I64, 9);
            fb.store(Ty::I64, raw, nine);
            deref(fb, raw)
        }
        Body::Param => deref(fb, p),
    };
    let read = fb.load(Ty::I64, boxed);
    fb.ret(vec![read]);
}

fn module(bodies: &[(&str, Body)]) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("box_deref_rederived", target());
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    for (ordinal, (name, body)) in bodies.iter().enumerate() {
        let mut fb = mb.function(*name, ft);
        emit(&mut fb, *body, &fact(ordinal as u32));
        fb.build();
    }
    mb.build().expect("the module builds")
}

fn default_license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// The opt-in consumer-local floor.
fn rederived_license() -> CodegenLicensePolicy {
    default_license().with_locally_rederived_box_floor()
}

/// Every entry that admits a module or a function, under `license`.
fn every_entry(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> [(&'static str, Result<(), AdapterError>); 5] {
    [
        (
            "admit_box_derefs",
            admit_box_derefs(module, license.box_validity_floor()).map(|_| ()),
        ),
        ("policy", license.admit_box_derefs(module).map(|_| ())),
        ("enforce_module", license.enforce_module(module)),
        ("ingest", admit_module(module, license, &[]).map(|_| ())),
        (
            "translate",
            translate_function_with_license(&module.functions[0], module, license).map(|_| ()),
        ),
    ]
}

fn reason(result: Result<impl std::fmt::Debug, AdapterError>) -> (String, BoxDerefRefusal) {
    match result {
        Ok(value) => panic!("admitted: {value:?}"),
        Err(error @ AdapterError::BoxDerefNotAdmitted { .. }) => {
            let text = error.to_string();
            let AdapterError::BoxDerefNotAdmitted { reason, .. } = error else {
                unreachable!()
            };
            (text, reason)
        }
        Err(other) => panic!("refused, but not as a BoxDeref: {other}"),
    }
}

#[test]
fn the_default_floor_refuses_even_a_wholly_rederivable_deref_on_every_entry() {
    for body in [Body::Slot, Body::GuardedHeap] {
        let module = module(&[("f", body)]);
        let license = default_license();
        assert_eq!(license.box_validity_floor(), BoxValidityFloor::Refuse);
        for (entry, result) in every_entry(&module, &license) {
            let (text, refusal) = reason(result);
            // trust-ir's verdict exactly as it stands: no re-derivation was
            // consulted, so no reason from one is attached.
            assert_eq!(
                refusal,
                BoxDerefRefusal::EvidenceBelowFloor {
                    conjunct: "nonnull",
                    tier: "named_premise",
                    floor: "consumer_rederived",
                    not_rederived: None,
                },
                "{body:?} {entry}: {text}"
            );
            assert!(!text.contains("re-derive"), "{body:?} {entry}: {text}");
        }
        // trust-ir's own findings, as the ingestion entry reads them: at the
        // default floor every Box floor finding stands; at the re-derived
        // floor every one is discharged.
        let box_findings = |license: &CodegenLicensePolicy| {
            trust_cg_lower::admission_findings(&module, license, &[])
                .into_iter()
                .filter(|error| {
                    matches!(
                        error,
                        trust_ir_build::ValidationError::BoxValidityEvidenceBelowFloor { .. }
                    )
                })
                .count()
        };
        assert_eq!(box_findings(&license), 3, "{body:?}");
        assert_eq!(box_findings(&rederived_license()), 0, "{body:?}");
    }
}

#[test]
fn the_floors_keep_the_consumer_local_verdict_apart_from_trust_irs_tier() {
    assert!(!BoxValidityFloor::Refuse.rederives());
    assert!(BoxValidityFloor::LocallyRederived.rederives());
    assert!(BoxValidityFloor::NamedPremise.rederives());
    assert!(BoxValidityFloor::Refuse < BoxValidityFloor::LocallyRederived);
    assert!(BoxValidityFloor::LocallyRederived < BoxValidityFloor::NamedPremise);
    assert_eq!(
        BoxValidityFloor::MOST_PERMISSIVE,
        BoxValidityFloor::NamedPremise
    );
    assert_eq!(BoxValidityFloor::Refuse.name(), "consumer_rederived");
    assert_eq!(BoxValidityFloor::NamedPremise.name(), "named_premise");
    assert_eq!(
        BoxValidityFloor::LocallyRederived.name(),
        "trust_cg_locally_rederived_v1"
    );
    assert_eq!(
        BoxValidityFloor::LocallyRederived.tier(),
        BoxValidityTier::ConsumerRederived
    );
    let default = default_license();
    let rederived = rederived_license();
    assert_eq!(
        rederived.box_validity_floor(),
        BoxValidityFloor::LocallyRederived
    );
    assert!(rederived.box_deref_disclosure().is_none());
    assert!(
        !default.canonical_identity().contains("box_validity_floor"),
        "{}",
        default.canonical_identity()
    );
    assert_eq!(
        rederived.canonical_identity(),
        format!(
            "{};box_validity_floor=trust_cg_locally_rederived_v1",
            default.canonical_identity()
        )
    );
    // The named-premise opt-in wins over the re-derived one (a superset).
    let both = rederived.with_named_premise_box_floor(&BoxDerefDisclosure::new());
    assert_eq!(both.box_validity_floor(), BoxValidityFloor::NamedPremise);
}

#[test]
fn the_rederived_floor_admits_a_wholly_rederived_deref_on_every_entry() {
    for body in [Body::Slot, Body::GuardedHeap] {
        let module = module(&[("f", body)]);
        let manifest = admit_box_derefs(&module, BoxValidityFloor::LocallyRederived)
            .unwrap_or_else(|error| panic!("{body:?}: {error}"));
        assert_eq!(manifest.floor, BoxValidityFloor::LocallyRederived);
        assert_eq!(manifest.rows.len(), 1, "{body:?}");
        let row = &manifest.rows[0];
        // The fact's own tier, never raised to trust-ir's top tier.
        assert_eq!(row.tier, BoxValidityTier::NamedPremise, "{body:?}");
        assert_eq!(row.rederived, ValidityConjunct::THIN.to_vec(), "{body:?}");
        assert!(row.assumed.is_empty(), "{body:?}");
        assert!(!row.is_assumption(), "{body:?}");
        // Re-derived rows are not assumptions, so nothing is disclosed.
        assert!(manifest.disclosure().is_none(), "{body:?}");

        let license = rederived_license();
        license
            .admit_box_derefs(&module)
            .unwrap_or_else(|error| panic!("{body:?} policy: {error}"));
        license
            .enforce_module(&module)
            .unwrap_or_else(|error| panic!("{body:?} enforce: {error}"));
        license
            .verdict(&module, module.functions[0].id)
            .unwrap_or_else(|error| panic!("{body:?} verdict: {error}"));
        admit_module(&module, &license, &[])
            .map(|_| ())
            .unwrap_or_else(|error| panic!("{body:?} ingest: {error}"));
        translate_function_with_license(&module.functions[0], &module, &license)
            .map(|_| ())
            .unwrap_or_else(|error| panic!("{body:?} translate: {error}"));
    }
}

#[test]
fn one_escape_before_the_deref_is_refused_on_every_entry_with_its_reason() {
    let module = module(&[("f", Body::SlotEscaping)]);
    let license = rederived_license();
    let why = NotRederived::EscapesBeforeDeref.reason();
    for (entry, result) in every_entry(&module, &license) {
        let (text, refusal) = reason(result);
        assert_eq!(
            refusal,
            BoxDerefRefusal::EvidenceBelowFloor {
                conjunct: "dereferenceable",
                tier: "named_premise",
                floor: "consumer_rederived",
                not_rederived: Some(why),
            },
            "{entry}: {text}"
        );
        assert!(
            text.contains("below this lane's Box validity floor consumer_rederived")
                && text.contains("this backend does not re-derive it")
                && text.contains(why),
            "{entry}: {text}"
        );
    }
}

#[test]
fn a_named_premise_is_still_refused_at_the_rederived_floor() {
    let module = module(&[("f", Body::Param)]);
    let (text, refusal) = reason(admit_box_derefs(
        &module,
        BoxValidityFloor::LocallyRederived,
    ));
    assert!(
        matches!(
            refusal,
            BoxDerefRefusal::EvidenceBelowFloor {
                conjunct: "nonnull",
                not_rederived: Some(_),
                ..
            }
        ),
        "{text}"
    );
    assert!(
        text.contains(NotRederived::NoDominatingNullTest.reason()),
        "{text}"
    );
}

#[test]
fn a_structural_rule_still_refuses_a_rederivable_deref_first() {
    let mut module = module(&[("f", Body::Slot)]);
    for node in module.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
    {
        if let trust_ir::Inst::BoxDeref { fact, .. } = &mut node.inst {
            fact.not_claimed.clear();
        }
    }
    for floor in [
        BoxValidityFloor::Refuse,
        BoxValidityFloor::LocallyRederived,
        BoxValidityFloor::NamedPremise,
    ] {
        let (text, refusal) = reason(admit_box_derefs(&module, floor));
        assert!(
            matches!(
                refusal,
                BoxDerefRefusal::FactRefused {
                    rule: "BoxDerefNonClaimsNotPinned",
                    ..
                }
            ),
            "{floor:?}: {text}"
        );
    }
}

#[test]
fn only_assumed_rows_are_disclosed_at_the_named_premise_floor() {
    // Wholly re-derived: admitted, nothing disclosed.
    let disclosure = BoxDerefDisclosure::new();
    let license = default_license().with_named_premise_box_floor(&disclosure);
    let rederived = module(&[("f", Body::Slot)]);
    license.enforce_module(&rederived).expect("admitted");
    assert!(disclosure.is_empty(), "{:?}", disclosure.records());

    // One premise row and one re-derived row: one record, the premise only.
    let mixed = module(&[("premise", Body::Param), ("rederived", Body::Slot)]);
    license.enforce_module(&mixed).expect("admitted");
    let records = disclosure.records();
    assert_eq!(records.len(), 1, "{records:?}");
    let rows = &records[0].manifest.rows;
    assert_eq!(rows.len(), 2);
    assert!(
        rows[0].is_assumption() && !rows[1].is_assumption(),
        "{rows:?}"
    );
    let lines = disclosure.lines();
    assert_eq!(lines.len(), 1);
    assert!(
        lines[0].contains("Box validity at 1 instruction(s) is assumed")
            && lines[0].contains("param_by_value x1"),
        "{}",
        lines[0]
    );

    // Partly re-derived (an escape): admitted on its premise, and disclosed.
    let disclosure = BoxDerefDisclosure::new();
    let license = default_license().with_named_premise_box_floor(&disclosure);
    let partial = module(&[("f", Body::SlotEscaping)]);
    let manifest = license.admit_box_derefs(&partial).expect("admitted");
    assert_eq!(manifest.rows[0].tier, BoxValidityTier::NamedPremise);
    assert_eq!(
        manifest.rows[0].rederived,
        vec![ValidityConjunct::NonNull, ValidityConjunct::Aligned]
    );
    assert_eq!(
        manifest.rows[0].assumed,
        vec![ValidityConjunct::Dereferenceable]
    );
    assert!(manifest.rows[0].is_assumption());
    assert_eq!(disclosure.records().len(), 1);
}

/// The LIR opcodes of `function`, by variant name, sorted.
fn opcode_names(function: &Function) -> Vec<String> {
    let mut names: Vec<String> = function
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .map(|inst| {
            let debug = format!("{:?}", inst.opcode);
            debug
                .split(|c: char| !c.is_alphanumeric() && c != '_')
                .next()
                .unwrap_or_default()
                .to_owned()
        })
        .collect();
    names.sort();
    names
}

#[test]
fn a_rederived_deref_lowers_to_one_copy_and_takes_no_licence() {
    let license = rederived_license();
    let with = module(&[("f", Body::Slot)]);
    let without = module(&[("f", Body::SlotWithoutDeref)]);
    let (lowered_with, _) = translate_function_with_license(&with.functions[0], &with, &license)
        .expect("admitted at the re-derived floor");
    let (lowered_without, _) =
        translate_function_with_license(&without.functions[0], &without, &license)
            .expect("the control lowers");
    let mut expected = opcode_names(&lowered_without);
    expected.push("Copy".to_owned());
    expected.sort();
    assert_eq!(opcode_names(&lowered_with), expected);
    assert_eq!(lowered_with.blocks.len(), lowered_without.blocks.len());
    let copies = |function: &Function| {
        function
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .filter(|inst| matches!(inst.opcode, Opcode::Copy))
            .count()
    };
    assert_eq!(copies(&lowered_with), copies(&lowered_without) + 1);
}

/// `module` with an assumed-root premise on every fact, plus a function
/// `checked` holding a sited `Assert` (a v54 panic delivery) and its panic
/// entry. A panic delivery makes `validate_codegen_prerequisites` refuse
/// every finding it does not discharge or classify, so this is the shape in
/// which that entry's own discharge decides.
fn module_with_panic_delivery(body: Body) -> Module {
    use trust_ir::{
        AssertKind, Block, BlockId, Constant, FuncId, FuncTy, Inst, InstrNode, PanicLocation,
        PanicSite,
    };
    let mut mb = ModuleBuilder::new_with_target_info("box_deref_rederived_panic", target());
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("f", ft);
    let assumed = BoxValidityFact::premise(
        BoxDerefSite {
            item: [0x6b; 16],
            ordinal: 0,
        },
        BoxFactSession::PROOF_SNAPSHOT,
        PremiseRoot::ReferenceArgBoxValid,
    );
    emit(&mut fb, body, &assumed);
    fb.build();
    let mut module = mb.build().expect("the module builds");
    let entry_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("entry type");
    let checked_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("checked type");
    let entry_id = FuncId::new(module.functions.len() as u32);
    let mut entry = trust_ir::Function::new(
        entry_id,
        "panic_const_div_by_zero",
        entry_ty,
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.body.push(InstrNode::new(Inst::Unreachable));
    entry.blocks.push(block);
    module.functions.push(entry);
    let checked_id = FuncId::new(module.functions.len() as u32);
    let mut checked = trust_ir::Function::new(checked_id, "checked", checked_ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(true),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Assert {
        cond: ValueId::new(1),
        kind: AssertKind::DivByZero,
        site: Some(PanicSite {
            entry: entry_id,
            location: PanicLocation::Value(ValueId::new(0)),
        }),
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    checked.blocks.push(block);
    module.functions.push(checked);
    module
}

#[test]
fn the_prerequisite_entry_discharges_a_rederived_finding_beside_a_panic_delivery() {
    use trust_cg_lower::adapter::validate_codegen_prerequisites;
    // Control: the panic delivery alone is acceptable to this entry.
    validate_codegen_prerequisites(&module_with_panic_delivery(Body::SlotWithoutDeref))
        .expect("the panic-delivery control is accepted");
    // An assumed root (below this entry's named-premise floor) on a deref
    // this backend wholly re-derives: discharged, not refused.
    validate_codegen_prerequisites(&module_with_panic_delivery(Body::Slot))
        .expect("a wholly re-derived deref is discharged");
    // The near miss: the same refusal as every other entry.
    let (_, refusal) = reason(validate_codegen_prerequisites(&module_with_panic_delivery(
        Body::SlotEscaping,
    )));
    assert_eq!(
        refusal,
        BoxDerefRefusal::EvidenceBelowFloor {
            conjunct: "dereferenceable",
            tier: "assumed_root_premise",
            floor: "named_premise",
            not_rederived: Some(NotRederived::EscapesBeforeDeref.reason()),
        }
    );
}
