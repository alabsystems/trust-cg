// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Strict test-only custody of canonical malformed-constant findings.
//! Source fixtures remain owned by each inventory's existing constructor.

use super::const_module;
use trust_cg_lower::adapter::AdapterError;
use trust_ir::{Constant, FuncId, FuncTyId, Module, Ty};
use trust_ir_build::ValidationError;

pub(super) fn assert_refused(module: &Module, expected: &[(&str, &str, &str)]) -> String {
    let expected: Vec<_> = expected
        .iter()
        .map(
            |(location, expected, actual)| ValidationError::ConstTypeMismatch {
                location: (*location).into(),
                expected: (*expected).into(),
                actual: (*actual).into(),
            },
        )
        .collect();
    assert!(
        !expected.is_empty(),
        "a malformed source needs a real typed finding"
    );
    let before = module.clone();
    let findings = trust_ir_build::validate_module(module);
    let mismatches: Vec<_> = findings
        .iter()
        .filter(|error| matches!(error, ValidationError::ConstTypeMismatch { .. }))
        .collect();
    assert_eq!(mismatches, expected.iter().collect::<Vec<_>>());
    let error = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &super::permit_unlicensed(),
    )
    .expect_err("the actual malformed source must not reach carrier lowering");
    match &error {
        AdapterError::TrustIrAdmissionRefused { error } => {
            assert_eq!(*error, expected[0].to_string());
        }
        other => panic!("expected the exact canonical typed refusal, got {other}"),
    }
    assert_eq!(*module, before);
    error.to_string()
}

pub(super) fn fndef_unregistered(name: &str) -> String {
    let module = const_module(
        name,
        Ty::Func(FuncTyId::new(0)),
        Constant::FnDef(FuncId::new(99)),
    );
    body_refused(
        &module,
        name,
        "a unique module-owned function item",
        "missing or ambiguous func.99",
    )
}

pub(super) fn body_refused(module: &Module, name: &str, expected: &str, actual: &str) -> String {
    assert_refused(
        module,
        &[(&format!("function '{name}' bb0"), expected, actual)],
    )
}

/// `phantomdata` at `i64` is no constant of `i64`: TrustIR's exact typed
/// refusal, which every adapter entry consumes first.
pub(super) fn phantom_non_unit(name: &str) -> String {
    let malformed = const_module(name, Ty::I64, Constant::PhantomData);
    body_refused(&malformed, name, "i64", "phantomdata")
}

pub(super) fn phantom_subject(name: &str) -> Module {
    // Retain the original malformed I64 fixture as an exact typed negative.
    phantom_non_unit(name);
    // `phantomdata` is the one spelling of `()`'s value: a Unit constant.
    let valid = const_module(name, Ty::Unit, Constant::PhantomData);
    assert!(trust_ir_build::validate_module(&valid).is_empty());
    valid
}
