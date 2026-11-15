// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The exact refusal the public adapter entry returns when TrustIR's typed
//! admission rejects a module before carrier lowering. The entry consumes
//! that verdict first, so a fixture that used to reach one of the adapter's
//! own range or shape checks now stops here, with TrustIR's typed finding.

use trust_cg_lower::adapter::AdapterError;
use trust_ir_build::ValidationError;

/// The public entry's refusal for TrustIR's `ConstTypeMismatch` at `location`.
#[allow(dead_code)] // Not every target that includes this file renders it.
pub(crate) fn typed_const_refusal(location: &str, expected: &str, actual: &str) -> AdapterError {
    AdapterError::TrustIrAdmissionRefused {
        error: ValidationError::ConstTypeMismatch {
            location: location.into(),
            expected: expected.into(),
            actual: actual.into(),
        }
        .to_string(),
    }
}

/// `err` is exactly TrustIR's `ConstTypeMismatch` at `location`.
#[allow(dead_code)] // Not every target that includes this file asserts on it.
pub(crate) fn assert_typed_const_refusal(
    err: &AdapterError,
    location: &str,
    expected: &str,
    actual: &str,
) {
    let AdapterError::TrustIrAdmissionRefused { error: want } =
        typed_const_refusal(location, expected, actual)
    else {
        unreachable!("typed_const_refusal builds an admission refusal")
    };
    assert!(
        matches!(err, AdapterError::TrustIrAdmissionRefused { error } if *error == want),
        "expected TrustIR's typed refusal `{want}`, got: {err:?}"
    );
}
