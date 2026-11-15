# try_fold return representations — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bridge now lowers `ControlFlow<Never, integer>` results when rustc proves
that `Continue` is the only inhabited variant. It also binds both results of
scalar-pair closure returns, storing each at rustc's declared byte offset.
The intercepted call retains its cleanup edge for either return representation.

This is a native lowering repair on `e46434fcd87d5435bc18a55a5dc41f396efa409d`
with the seven source hashes in the qualification receipt. It uses genuine
Trust `ae9c2c1da`, TrustIR `794227ad`, and backend SHA-256
`76a91b6f8da14169927b10d4f81685987d607c6fd26d9692a9444bec28f16763`. Frontend verification and diagnostic codegen
certificates are explicitly disabled. No installed toolchain is promoted.

## Admission and behavior

The tagless path requires core's actual `ControlFlow` type, a rustc single
Continue variant, an uninhabited Break variant, the exact accumulator type at
offset zero, and one full integer lane of at most 64 bits. The accumulator
travels on the loop back edge; the iterator cursor stays in its live slot.
The final accumulator is written on exhaustion. Existing iterator, adapter,
closure-capture and ABI refusals remain in force.

Scalar pairs use the existing ABI plan, including carrier narrowing and boolean
normalization. Result size, alignment and slot type must match. Stores touch
only the declared lanes, without inventing padding. The shared intercepted-call
helper accepts zero, one or multiple results for both Call and Invoke.

## Validation

- Genuine Targo all-targets check and backend build pass. The maintained test
  target has exactly 13 tests; both new regressions pass.
- LLVM and TrustCG at O0–O3 pass 380,824 independent C checks: original residual
  reproducer; empty, exhausted and repeatedly drained iterators; reference
  captures and mutation; u8/u32/i64/u64 accumulator behavior; tagged early exits;
  returned cursor/call counts and adjacent memory guards.
- Another 96 checks use real Rust unwinding through both return shapes. An LLVM
  driver checks normal results, caught panic payloads, the dropped guard's
  payload and callback counts at O0–O3.
- Nine unchanged diagnostic regressions pass 4,537,220 checks. Together with the
  new tests, this run records 4,918,140 native checks.
- Root formatting passes. Private formatting adds no differences to the 59
  pre-existing library formatting blocks; new test/fixture sources pass in full.
- Full original core diagnostic: 23 failed roots;
  command exit 1. This is a current
  census on the combined main and repair, not a clean core/self-host build.
- Unchanged proof-required C ABI test: exit 101,
  passed=false, TCG-PROOF-465=true.
  The native diagnostic passes do not satisfy that proof gate.

## Retained failures and limits

The original tagless prototype passed its first reproducer but failed the
expanded tagged control with a one-versus-two Call-result arity mismatch.
The scalar-pair repair passes that unchanged control and additional narrow
payload controls. The first maintained runner supplied the edition twice;
that invocation failed, and the corrected runner retains the full inventory.

The first unwind probe used a zero-sized Guard and still refuses both functions
with `Slice-1 drop-glue receiver ... has no scalarized aggregate image`.
That reproducer remains archived and open. The passing unwind regression uses
a scalar Guard. No zero-sized drop support or broader unwind/proof coverage is
claimed. All product completion gates remain open.

## Reproduction and records

The maintained regressions live in
`crates/rustc-codegen-trust-cg/tests/support/untagged_try_fold.rs`, selected as
`untagged_try_fold::` in `aarch64_c_fnabi_aggregate_linux`. The archived
qualification scripts bind the compiler, private sysroot, backend and test
binary by hash, run all-targets first, and retain exact commands and outputs.
`manifest.json`, `assets.json`, `excluded.json` and `inventory.json` bind each
compressed record and asset. Rebuildable backend/runtime archives are excluded
with their hashes; sources, logs, objects and native executables are retained.
