# Linux AArch64: final slice-tail / x86 CSE main reconciliation

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The [slice-tail fix](../2026-09-29-slice-tail-from-end/README.md) and
[main-alignment evidence](../2026-09-29-slice-tail-main-alignment/README.md)
were committed through `8ea702892`. The attempted atomic synchronization
stopped at its ancestry check because remote main had advanced to `80b0e03aa`.
No push or history rewrite occurred in that attempt. Merge `4fcaecf83`
incorporates the new main; the sole inventory conflict was regenerated.

The incoming change fixes x86 CSE invalidation across register-width aliases,
rejects self-aliasing seeds, and preserves proof-annotated instructions and
barriers. It also adds tracked x86 vectorizer opt-outs and a test-elision
measurement switch, retaining their defaults. The peer's performance reports
are not measurements on this Linux AArch64 host. TrustIR remains
`8e81e98aa92d78934548ec435218ce530294f2c5`; no AArch64 lowering algorithm changes.

The frozen backend built from `4fcaecf83` is SHA-256
`c16e04f9de9232dae5bd80ce3b8afc9c47549414b0bc470fb6861080e819815a`.
It passes the permanent from-end matrix: **16 LLVM/CG executions, 391,424
checks and four retained projected-field refusals**, across O0–O3 and both panic
policies. Strict O0/O2 checks retain 10/9 functions, 14/14 refined obligations,
nine/nine memo hits, zero skips and zero unmodeled shapes. Machine-proof
admission still fails at `TCG-PROOF-465`.

The merged optimizer passes **419 tests**: Boolean policy 1, peephole 240,
CSE 34 and vectorization 144. The CSE suite includes fresh processes with the
option on and off. All 26 bridge option tests pass.

The latest completed O2 std census remains **216 failing roots**, bound to the
first merged backend in the preceding report. It was not repeated for these
x86-only changes. The previous report retains three reproduced pre-existing
proof-test failures and the x86 memory qualification's checker-identity
mismatch. Those gaps were not waived or represented as passing checks here.
Full CG std, self-hosting, complete machine proofs and speed superiority over
LLVM/clang remain unfinished.

Source hashes, build receipts and complete transcripts are attached and bound
by `assets.json`. Compiler artifacts are frozen outside Cargo's mutable output
paths. The earlier reports remain immutable.

## Final x86-only follow-up

Remote `f29ffe3fd` was merged as `4a8857884` while the frozen native run above
finished. Its only production-source change is the x86 peephole's redundant
self-test pass: register-width aliases, secondary writes and proof boundaries
now block an unsafe elision. No bridge or AArch64 source changes. The native
and bridge artifact qualifications above remain explicitly bound to
`4fcaecf83`; the final x86 change is checked on its own combined source.

The final source passes **427 optimizer tests**: Boolean policy 1,
peephole 248, CSE 34 and vectorization 144. The retained logs include the new
width-alias, secondary-write, exact-operand and proof-boundary controls.
Documentation and diagnostic-inventory checks also pass.
