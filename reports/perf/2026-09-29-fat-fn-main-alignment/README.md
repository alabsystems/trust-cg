# Dynamic Fn arguments after the verifier/main merge

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The [dynamic Fn repair](../2026-09-29-fat-fn-arguments/README.md) is qualified
again after merging remote `main` through `79d8f26ba`. Merge commit
`9b08de131` brings instruction-word obligations and encoder binding, proof-wall
census support, an opt-in x86 LICM experiment, and the accompanying tests and
documentation. The IR dependency pin is unchanged.

The frozen backend built from `9b08de131` has SHA-256
`51c1361202aa32382cea2d68f917a6dd6571640a66b86b5c8522c83494e82881`.
Its complete recorded source manifest and patch are attached. Later commit
`942d7ecdb` changes only the Python Darwin test inventory and its unit assertions:
it adds the host-neutral `rust_empty_filter` adapter target, already required
on Linux, with a minimum of two tests. The Darwin inventory now requires 273
targets and 1,906 passes. This is inventory maintenance, not a Darwin native run.

The same frozen native harness from the primary report passes all seven
selected integration tests: **66 LLVM/CG executions, 153,668 counted checks,
16,384 caught panics, 16 counted SIGABRTs and six named refusals**. It includes
the new pointer arguments, borrowed Box calls, closure-target refusal, existing
virtual cleanup/termination/forced-unwind controls and closure-wrapper mixed
objects. Counters are the harness's reported totals; support-runtime setup
checks are not added.

Strict bridge runs at O0 and O2 again report 13 functions, four refined
obligations, no skips or memo hits and no unmodeled MIR shapes. Both
machine-proof-required runs still refuse by name with `TCG-PROOF-465`. The
incoming instruction-derived rows remain uncredited; no proof requirement is
waived by this merge.

Selected incoming-change checks pass:

| Check | Tests passed |
| --- | ---: |
| x86 LICM | 58 |
| Instruction-word proof module | 8 |
| Function verifier | 201 |
| AArch64 decoder | 34 |
| Instruction-word binding, including native JIT comparisons | 4 |
| In-process formal-probe construction | 1 |
| CLI proof publication | 13 |
| Python census and Darwin gate | 44 |

The 201 verifier test results include an internally reported skip for the
external Clean-checker ROR probe because that checker is not configured.
The selected formal-probe test checks its obligations in process; external
solver/checker probes were not run. These are unit/native results, not new
proof credit. The Python run first exposed the missing empty-filter inventory
entry (42 passed, two failed); all 44 pass after the fix. Both transcripts are
retained.

The additional `overflow_asserts` suite remains **nine failures before and
nine after**, each at the existing Linux AArch64 machine-proof admission wall,
before its runtime assertions. Its refusal exception is scoped to macOS, so
this is not a passing Linux runtime suite. The same test executable was run
against both frozen backends in separate `deps` directories; backend and test
hashes are recorded. An earlier attempt to launch the copied executable outside
a `deps` directory failed artifact discovery before invoking the compiler;
those harness-error logs are retained separately. No test guard was weakened.

The complete std census and mixed-library run remain those of the primary
report: the pre-verifier-merge first backend reduced O2 std failures from 223
to 219 with no new or changed diagnostics. They are not rerun by this
supplement. Latest O0 remains 197. Full CG std, self-hosting, complete machine
proofs and speed superiority remain open.

The attached build receipts, source/test manifests, commands and transcripts
are bound by `assets.json`. The CLI tests embed their Cargo binary path; its
hash is checked again after those tests to detect replacement during the run.
