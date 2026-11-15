# Linux AArch64 captured closure storage

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

This closes the `escape_debug().to_string()` SIGSEGV recorded in
[the raw-reference milestone](../2026-09-29-raw-reference-storage/README.md).
A closure containing a single scalar capture qualified for both an aggregate
environment slot and a scalar cell. An incoming closure parameter initialized
the environment slot, but a nested closure captured the address of the separate,
uninitialized cell. The same duplication could split local closure accesses.

On Linux AArch64, a closure already selected for aggregate storage now keeps
that environment as its sole home. The change does not alter call signatures or
relax a refusal. Production commit: `ae7e8f0bc`; remote integration checkpoints:
`84fa9b8ff` and `621b9d03c`.

## Native and real-library results

A reduced nested-closure program crashes with the previous backend at O0/O2;
the LLVM twin passes. With this fix both backends pass. Retained IR shows the
extra uninitialized cell before the change and its removal afterward. The text
renderings are diagnostic; the binary IR files retain the original identities.
A separate exploratory attempt using the external core iterator directly was
refused by the existing iterator interception boundary, so it was not used as
the reproducer.

The permanent C-oracle fixture covers shared/mutable/value captures, repeated
calls and subsequent aliased reads, a local closure captured by another closure,
multiple captures, FnOnce, and empty environments. It passes O0–O3, abort/unwind,
and LLVM/trust-cg: **1,048,576 checks in 16 executions**. Running this same fixture
against the old backend fails with SIGSEGV at the first trust-cg O0 execution,
after the LLVM O0 control passes.

Including six existing regression groups, the initial fixed backend and the
first merged backend each pass **12,566,484 checks in 90 executions**, plus two
named partial-copy refusals. The second remote merge adds an x86 diagnostic
switch; the final rebuilt backend repeats the full new closure fixture
successfully. The frozen native harness hash is unchanged across the builds.

A fresh mixed library build succeeds: trust-cg compiles core at O2, and LLVM
builds the rest of std (375.45 seconds overall; a diagnostic timing, not a
performance comparison). Dynamic consumers load that exact mixed libstd and
pass 21,504 network/escape formatting checks, two sets of 81,097 UTF-8 and
character-count checks, and 112 caught panics with payload/destructor checks.
The formerly crashing `escape_debug` probe is included. That mixed-library run
uses the initial fixed backend; it is not a full trust-cg std build or a claim
of complete core correctness.

## Proof and provenance

Strict bridge probes pass O0/O2 on all three fixed backends: 74/69 functions,
23/37 accepted scalar obligations, 10/24 memo hits, zero skipped obligations and
zero unmodeled shapes. Memory, operand wiring and control-flow behavior remain
outside those scalar proofs. Machine-proof-required runs refuse at both levels
with `TCG-PROOF-465`; no runtime sampling is counted as proof. Native and strict
probes use the private AY cache; the core/stdlib census uses its recorded
baseline diagnostic cache policy.

Frozen backend SHA256 identities:

- Initial: `e2c221b18e08c70827f9de7f3e3317b2aac72c1815c904b76f4945cf9fab0967`
- First merge: `be8cf6245d146a47cec6f9631029d6aa3a598db01990aa852b291db091b5aec0`
- Final merge: `b56e0c5ab586f8f2df7b98751960b87c0577afe74e845f4347ca728872020775`

Source manifests, the initial patch, build/test receipts, compiler commands and
compressed logs accompany this report. Full binaries, the mixed sysroot, ELF
inspection and loader records remain local in `target/escape-debug-investigation/`;
independent artifact publication remains open. Full trust-cg std, indirect
cleanup calls, complete machine proof, and compile/runtime wins over LLVM and
Clang remain unfinished.
