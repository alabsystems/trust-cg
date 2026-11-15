// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Trust checks the entire dispatch specification during bridge compilation.
//! The model's explicit hand-mirror and abstraction boundaries still apply;
//! this module grants no Rust-body, codegen-license or machine-code verdict.

#[path = "../../../proofs/mir_place_resolution_spec.lean"]
clean mod checked_dispatch;
