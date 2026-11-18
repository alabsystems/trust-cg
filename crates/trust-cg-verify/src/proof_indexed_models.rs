// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Kernel-check the complete proof-indexed mathematical sources during
//! verifier compilation. Rust implementation refinement and codegen authority
//! require separate evidence.

#[path = "../../../reports/fixtures/ProofIndexedEGraph.lean"]
clean mod egraph;

#[path = "../../../reports/fixtures/ProofIndexedExtraction.lean"]
clean mod extraction;

#[path = "../../../reports/fixtures/ProofIndexedRewriteCore.lean"]
clean mod rewrite_core;

#[path = "../../../reports/fixtures/ProofIndexedRewriteSemantic.lean"]
clean mod semantic;
