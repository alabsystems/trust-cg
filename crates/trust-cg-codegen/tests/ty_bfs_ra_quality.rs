// trust-cg-codegen/tests/ty_bfs_ra_quality.rs - the TY BFS kernel with the
// x86-64 allocation-quality policy installed
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `ty_bfs_minimal`'s tests, compiled as a driver that installs the four x86-64
// allocation-quality changes as enabled (`install_driver_ra_policy`), the way
// the rustc bridge installs them for a compile without proof certificates.
// Since 2026-11-15 a TY compile that keeps no certificates requests the same
// four through `CompilerConfig::x86_certificate_free_allocation`, with no
// installed policy (`X86AllocationQuality::CertificateFree`), so this target
// and `ty_bfs_minimal` agree; it keeps the installed-policy path exercised.
// The executed legs check that the
// kernel still computes the same results under that policy; the objects are
// kept under `CARGO_TARGET_TMPDIR/ty_bfs_ra_quality/` for measurement.

#[path = "ty_bfs_minimal.rs"]
mod ty_bfs_minimal;
