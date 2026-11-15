// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Recorded ABI custody, not ABI classification or machine-code evidence.
//! An absent descriptor is unrecorded, never a wildcard for a recorded claim.

use std::fmt;

use trust_ir::FuncTy;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CustodyError {
    MissingSignature,
    RecordingDisagrees,
    ClaimsDisagree,
}

impl fmt::Display for CustodyError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::MissingSignature => "function signature is missing",
            Self::RecordingDisagrees => "recorded and unrecorded signature ABI cannot be unified",
            Self::ClaimsDisagree => "recorded signature ABI claims disagree",
        })
    }
}

pub(super) fn require_same(
    left: Option<&FuncTy>,
    right: Option<&FuncTy>,
) -> Result<(), CustodyError> {
    let (Some(left), Some(right)) = (left, right) else {
        return Err(CustodyError::MissingSignature);
    };
    match (&left.abi, &right.abi) {
        (None, None) => Ok(()),
        (Some(left), Some(right)) if left == right => Ok(()),
        (Some(_), Some(_)) => Err(CustodyError::ClaimsDisagree),
        (None, Some(_)) | (Some(_), None) => Err(CustodyError::RecordingDisagrees),
    }
}
