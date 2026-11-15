//! Canonical TrustIR ExtractField declares its result type. Legacy adapter
//! aggregate spelling remains a compatibility input, not valid Core TrustIR.

use trust_ir::{FieldDef, Inst, StructDef, StructId, StructRepr, Ty, ValueId};
use trust_ir_build::{ModuleBuilder, validate_module};

fn nested() -> trust_ir::Module {
    let mut m = ModuleBuilder::new("field_result_types");
    let inner = Ty::Struct(m.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Inner".into(),
        fields: vec![
            FieldDef {
                name: "first".into(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "second".into(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    }));
    let outer = Ty::Struct(m.add_struct(StructDef {
        origin: None,
        id: StructId::new(1),
        name: "Outer".into(),
        fields: vec![
            FieldDef {
                name: "prefix".into(),
                ty: Ty::U8,
                offset: None,
            },
            FieldDef {
                name: "nested".into(),
                ty: inner.clone(),
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    }));
    let sig = m.add_func_type(vec![outer.clone()], vec![Ty::U64]);
    let mut f = m.function("nested", sig);
    let entry = f.create_block();
    let middle = f.create_block();
    let exit = f.create_block();
    let arg = f.add_block_param(entry, outer);
    f.switch_to_block(entry);
    f.br(middle, vec![]);
    f.switch_to_block(middle);
    let pair = f.extract_field(inner, arg, 1);
    f.br(exit, vec![]);
    f.switch_to_block(exit);
    let result = f.extract_field(Ty::U64, pair, 1);
    f.ret(vec![result]);
    f.build();
    let mut m = m.build().expect("ModuleBuilder::build: test fixture");
    // Resolve SSA from dependencies, never physical block storage order.
    m.functions[0].blocks.reverse();
    m
}

#[test]
fn nested_result_spelling_matches_legacy_layout_with_reversed_blocks() {
    let canonical = nested();
    assert_eq!(validate_module(&canonical), []);
    let canonical_lir = trust_cg_lower::translate_function_with_license(
        &canonical.functions[0],
        &canonical,
        &permit_unlicensed(),
    )
    .unwrap()
    .0;
    let mut legacy = canonical.clone();
    for block in &mut legacy.functions[0].blocks {
        for node in &mut block.body {
            if let Inst::ExtractField { ty, .. } = &mut node.inst {
                *ty = if *ty == Ty::U64 {
                    Ty::Struct(StructId::new(0))
                } else {
                    Ty::Struct(StructId::new(1))
                };
            }
        }
    }
    assert!(
        !validate_module(&legacy).is_empty(),
        "compatibility is not Core validity"
    );
    let legacy_lir = trust_cg_lower::translate_function_with_license(
        &legacy.functions[0],
        &legacy,
        &permit_unlicensed(),
    )
    .unwrap()
    .0;
    assert_eq!(canonical_lir.blocks.len(), legacy_lir.blocks.len());
    for (id, block) in &canonical_lir.blocks {
        assert_eq!(format!("{block:?}"), format!("{:?}", legacy_lir.blocks[id]));
    }
}

#[test]
fn bad_result_type_missing_operand_and_bad_nested_field_are_rejected() {
    for corruption in 0..4 {
        let mut m = nested();
        let node = &mut m.functions[0].blocks[0].body[0];
        let Inst::ExtractField {
            ty,
            aggregate,
            field,
        } = &mut node.inst
        else {
            panic!()
        };
        match corruption {
            0 => *ty = Ty::U32,
            1 => *aggregate = ValueId::new(9999),
            2 => *field = 2,
            _ => *ty = Ty::Tuple(vec![Ty::U64]),
        }
        assert!(
            trust_cg_lower::translate_function_with_license(
                &m.functions[0],
                &m,
                &permit_unlicensed()
            )
            .is_err(),
            "corruption {corruption}"
        );
    }
}

#[test]
fn cyclic_extraction_dependencies_fail_without_recursion() {
    let mut m = nested();
    let result = m.functions[0].blocks[0].body[0].results[0];
    let Inst::ExtractField { aggregate, .. } = &mut m.functions[0].blocks[1].body[0].inst else {
        panic!()
    };
    *aggregate = result;
    let err =
        trust_cg_lower::translate_function_with_license(&m.functions[0], &m, &permit_unlicensed())
            .unwrap_err()
            .to_string();
    assert!(err.contains("cyclic ExtractField"), "{err}");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
