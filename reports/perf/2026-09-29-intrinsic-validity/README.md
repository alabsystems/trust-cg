# Linux AArch64 initialization validity intrinsics

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`assert_inhabited`, `assert_zero_valid` and `assert_mem_uninitialized_valid` now
use the frontend's monomorphized validity query on Linux AArch64. Valid checks
continue normally. Invalid checks call the real `panic_nounwind` language item
with the frontend-compatible message, then become unreachable. This preserves
panic hooks and abort behavior, including when the caller has unwind cleanup.
The default mitigated uninitialized check and `-Zstrict-init-checks=yes` retain
their distinct behavior. No proof gate is relaxed.

Source commit: `a284c422e`. Remote x86 proof-credit and documentation changes are
merged at `3bd1e3de8`. The merged backend is rebuilt and independently qualified.

## Native qualification

The permanent fixture passes **655,360 value checks in 32 executions**, with
**208 expected SIGABRT outcomes**. It covers LLVM and trust-cg at O0–O3, abort and
unwind panic modes, and both initialization policies. Invalid reference,
nonzero-integer, function-pointer and uninhabited-type checks verify the panic
payload and exactly one hook call. A destructor sentinel detects erroneous
unwinding. The boolean policy check directly invokes the intrinsic; it does not
construct an invalid boolean.

The existing residual-conversion and scalar-union-storage controls also pass.
Together, the three groups on the first frozen backend pass **4,227,072 checks
in 56 executions**, with the above 208 abort checks and two expected refusals.
The merged backend separately passes the focused O0/O2, unwind, two-policy
matrix: **163,840 checks in eight executions and 52 expected aborts**.

The corrected baseline probe passes all four LLVM controls; the old CG backend
refuses all four compilation lanes. An earlier version of the driver incorrectly
expected the uninhabited type suffix `::Empty`; LLVM and CG both print `Empty`.
The original failures and corrected driver/results are retained separately.

The small stable `mem::zeroed::<[u64; 4]>()` reproducer now passes at O0. It still
fails at O2 on an existing `Ty::[u64; 4]` conversion limitation. Its source, MIR
and failure are retained; the intrinsic repair does not claim general optimized
array/MaybeUninit conversion support.

## Library qualification

A fresh mixed library builds with CG-generated **core and alloc at O2** and
LLVM-generated remaining std crates. Exact-library dynamic consumers pass:
21,504 network/escape-formatting checks, 81,097 UTF-8/character checks with each
consumer backend, and 112 caught-panic payload/destructor cases.

The new validity consumer also links this exact mixed library and passes
**81,920 checks in four executions and 26 expected aborts**. Both LLVM and CG
consumers exercise the CG-built core's actual `panic_nounwind`, under both
initialization policies. Invocation records, sysroot hashes and loader logs
identify the library used. These runs are correctness checks, not controlled
compile-time or runtime comparisons.

The isolated full-std O0 census completes with **197 failed roots**, down from
213. All 16 removed roots were unsupported `assert_zero_valid` intrinsics.
There are no added roots or changed surviving diagnostic texts. Both runs use
the recorded LLVM dependency configuration; this is not a complete CG-built std
dependency graph. The old run uses TrustIR 96e3885 and the new one 824174a. The
retained cohort identity check establishes identical core IR and conformance
source trees between those pins; intervening CG changes before this repair are
x86-only. Full CG std, self-hosting and performance superiority remain open.

## Proof boundaries and provenance

Strict bridge coverage passes O0/O2 under both initialization policies, before
and after the remote merge: 20/12 MIR functions, 14/10 refined scalar obligations,
1/0 memo hits, zero skips and zero unmodeled shapes. The validity query, memory,
operand wiring and control flow remain trusted. Machine-proof-required probes
still refuse with `TCG-PROOF-465`; complete machine proof is unfinished. Native
runs use diagnostic `no-proof-certs`, and frontend verification is off.

Frozen backend SHA256 identities:

- Baseline: `ef6ecd5c809d7725e4a970948b1f7d787c6a4c76ebf90f8a215b5397f3a3df45`
- First repair: `fb31640d13ce42b7bef8e8c813c414d33c7d12354e6fe3c305386e58350036c2`
- Merged repair: `e5cea9df8db3585ac7a5c696571bc9e7ce68391947f8afa390071daca7836b99`

The first backend is built from `4b1c3d5a6` plus the recorded 72-line production
patch. The merged backend is built from clean production source at `3bd1e3de8`.
Harness receipts and input hashes identify the later permanent test additions.
Trust frontend: `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`; TrustIR:
`824174a164de10dba2053e387dfc4b1140960885`. Exact source snapshots, commands,
receipts, compressed logs and evidence hashes accompany this report. Frozen
binaries and full ELF inventories remain local under
`target/std-intrinsic-validity-investigation/`; independent binary publication
remains open. The subsequent O2 std investigation is outside this report.
