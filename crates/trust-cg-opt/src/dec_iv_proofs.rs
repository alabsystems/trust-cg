// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Compile the complete reverse-induction arithmetic with the optimizer.
//! The source theorem is not a proof of Rust CFG construction, a body license,
//! or evidence that a particular bounds check was removed.

#[path = "../../../benchmarks/step0-oracles/revloop/proof/dec_iv_bound.lean"]
clean mod checked_bounds;
