// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compile complete proof-indexed mathematical sources that the selected Trust
//! compiler actually accepts with the verifier.  The remaining original
//! sources stay in the port inventory until their own full declarations pass;
//! an unconditional failing include is not port progress.  These theorems do
//! not establish the Rust implementation's refinement or grant a license to
//! emit a particular native body.

#[path = "../../../reports/fixtures/ProofIndexedExtraction.lean"]
clean mod extraction;

#[path = "../../../reports/fixtures/ProofIndexedRewriteSemantic.lean"]
clean mod semantic;
