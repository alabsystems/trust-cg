# Caller-location ABI — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now declares and receives the hidden trailing `&'static Location`
argument on `#[track_caller]` functions, forwards it through direct and virtual
calls, and implements the `caller_location` intrinsic. It uses rustc's
`Body::caller_location_span` to honor inlined tracked functions and stop at
untracked boundaries. Reification shims retain rustc's definition-site boundary.
The panic-raise path uses that same resolution; untracked MIR assertions now
use the failing expression's span instead of the whole function's span.

The native corpus passes **10,304 checks** in eight LLVM/trust-cg executions
at O0–O3. It checks exact file, line and column across direct calls, recursion,
tracked and untracked inline boundaries, function-pointer reification, tracked
trait dispatch and an untracked trait with a tracked implementation. Ten scalar
arguments exercise stack placement of the hidden pointer; a buffered aggregate
return exercises coexistence with the hidden return pointer. An LLVM-built
driver calls both libraries, and each library calls an LLVM-built companion.
Caught panics cover the external companion, a local literal panic, and tracked
and untracked division assertions. All lanes use `panic=unwind`.

The prior backend refuses this same corpus at `Location::caller`; LLVM accepts
it. On the frozen full-core diagnostic, the final backend reduces failing roots
from **four to three**. Only `Location::caller` disappears. The remaining roots
are u128 `overflowing_pow`, `TwoWaySearcher::maximal_suffix` and `Request::fmt`.
This is still a failed, partial core build and does not close self-hosting.

Qualification on the final backend:

| Check | Result |
| --- | --- |
| Caller-location native regression | Passed, 10,304 checks at O0–O3 |
| Aggregate captures, closure wrappers, control-flow residuals, overflow loops, scalar-cell returns and zero-sized drops | 6 native regressions passed |
| Overflow-loop and zero-sized-drop refusal controls | 2 passed |
| Mandatory ABI proof admission | Failed with `TCG-PROOF-465`: 14 uncovered instructions across 12 opcode kinds; first `StpPreIndex` |
| Bridge all-targets check, new-file formatting, diff and documentation checks | Passed |

The full control invocation reports 8 passed and 1 failed, with no ignored tests.
Both core censuses exit 1 and retain 44 partial objects. The three remaining
root diagnostics are byte-for-byte unchanged. The archive also retains the
initial successful native probes and the intermediate build failure from an
incorrect assertion-block variable name; final qualification uses the corrected
and formatted source.

The backend SHA-256 is
`73cee19644bfdccf95d2bf19e3b6b62f90ad22b517eb57e9a9223b397681e988`.
It was built with Trust-authored `trustc` 1.99.0-dev,
`ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, using LLVM 22.1.2 for this
development bootstrap. The base checkout is
`e0ac540a363e36c0f28bea7a4831aca10345c313` plus the archived changes.
The previous backend is identified in the
[overflow-loop report](../2026-09-27-overflow-loop-threading/README.md).
All 721 frozen core files were rehashed and matched their manifest.

results.json records the final outcomes.
evidence.tar.gz contains 1,287 files: source snapshots,
patches, commands, logs, all frozen core sources, the primary native executables
and libraries, and both censuses' partial core objects. It also includes the
installed rustc source files consulted for caller-location and shim semantics.
Large rebuildable backend libraries and other control executables are recorded
by hash. assets.json hashes every tar member; each member was
independently rehashed after archiving. The stored archive SHA-256 is
`8b64e2f50503e7bdb9e4af0926a69f763e141fdd2bc92664ca6ea0d8548e027f`.
inventory.json includes stored and decoded archive identities.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-27-track-caller
```

Trust/Targo verification is disabled in this development lane, and codegen uses
`no-proof-certs`. Native correctness does not establish complete machine proofs.
No qualifying performance comparison was made. Linux completion, mandatory
proof admission, and compile/runtime dominance over LLVM and Clang remain open.

The raw `evidence.tar.gz` archive is retained in the qualification workspace; this repository records its hashes and manifests. Publishing those raw archives for independent download remains part of clean-source acceptance.
