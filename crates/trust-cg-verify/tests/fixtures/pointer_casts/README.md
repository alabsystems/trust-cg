# Actual Rust frontend pointer casts

The O0/O1 JSON files are unchanged module captures from the genuine Trust
frontend with the pointer-cast repair. The Rust inputs, diagnostic patch,
compiler identity, full logs and native execution records are retained in
[the qualification archive](../../../../../reports/perf/2026-09-20-frontend-pointer-casts/README.md).

`before_ref_ordered.trust-ir.json` retains the historical failure: a reference
copied to a differently typed raw pointer, followed by a typed-source
`PtrToInt`. Both fail the TrustIR validator. The regression requires both
repairs and checks that other module fields remain unchanged.

All 18 thin-pointer captures validate. Twelve scalar cases also compile and
execute through the normal backend. Aggregate-reference cases retain
Unclassified ABI metadata, no inferred tuple layout, and the native stack-frame
proof refusal. The fat-pointer source also retains its native frame refusal;
the integer-to-reference source is rejected before producing a module.

These are development-lane frontend captures and finite execution controls,
not a proof of Rust pointer provenance or complete native correctness.
