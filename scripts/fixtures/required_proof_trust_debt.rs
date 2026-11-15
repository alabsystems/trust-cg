// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Compile-fail control: preserve the complete original explicit-sorry source.
#[path = "../../reports/fixtures/ProofIndexedRewriteTrustDebt.lean"]
clean mod rewrite_trust_debt;

fn main() {}
