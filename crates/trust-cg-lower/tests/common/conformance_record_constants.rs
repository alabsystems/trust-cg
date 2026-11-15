// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Retain each original malformed record fixture before constructing its
//! explicitly ordered, fully source-validated positive counterpart.

use super::canonical_constants;
use trust_ir::{Constant, Inst, Module, RecordId, Ty, ValueId};

pub(super) fn canonical_fixture(mut module: Module, name: &str, extract: bool) -> Module {
    let location = format!("function '{name}' bb0");
    canonical_constants::assert_refused(
        &module,
        &[
            (
                &format!("{location}.left"),
                "field 'left'",
                "field 'right' at index 0",
            ),
            (
                &format!("{location}.right"),
                "field 'right'",
                "field 'left' at index 1",
            ),
        ],
    );
    let block = &mut module.functions[0].blocks[0];
    let constant = &mut block.body[0];
    assert_eq!(constant.results, [ValueId::new(0)]);
    let Inst::Const { ty, value } = &mut constant.inst else {
        panic!("the retained record fixture begins with its actual constant");
    };
    assert_eq!(*ty, Ty::Record(RecordId::new(0)));
    assert_eq!(
        *value,
        Constant::Record(vec![
            ("right".into(), Constant::Int(2)),
            ("left".into(), Constant::Int(1)),
        ])
    );
    *value = Constant::Record(vec![
        ("left".into(), Constant::Int(1)),
        ("right".into(), Constant::Int(2)),
    ]);
    if extract {
        // The declaration is the selected I64 RESULT, not its Record input.
        // Correct only this concrete retained projection, preserving its IDs.
        let projection = &mut block.body[1];
        assert_eq!(projection.results, [ValueId::new(1)]);
        let Inst::ExtractField {
            ty,
            aggregate,
            field,
        } = &mut projection.inst
        else {
            panic!("the retained source projection is an actual ExtractField");
        };
        assert_eq!(*ty, Ty::Record(RecordId::new(0)));
        assert_eq!(*aggregate, ValueId::new(0));
        assert_eq!(*field, 1);
        *ty = Ty::I64;
    }
    let findings = trust_ir_build::validate_module(&module);
    assert!(
        findings.is_empty(),
        "the positive fixture must be fully canonical: {findings:?}"
    );
    module
}
