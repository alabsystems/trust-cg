# Linux x86-64: re-measurement after merging origin/main's 148 commits (2026-09-22)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`origin/main` moved 148 commits ahead of the Linux x86-64 completion wave
(`integrate/upstream-round2`, 46 commits). The merge is
`9a276a0c1`; everything below was produced from that merged tree with a clean
working tree, and every artifact it cites is retained beside this file.

Host: `x86_64-unknown-linux-gnu`, Ryzen 9 9900X3D, 24 cores, 61 GiB, GCC
15.2.0. Root workspace built with the pinned stock Rust 1.97.1
(`rust-toolchain.toml`; the project's own pin overrides this machine's Trust
default toolchain). Bridge built with the tree-built stage2 `trustc`
(`rustc 1.99.0-dev (3a3e781fe 2026-09-14)`) through
`targo --unverified build --release --locked`. Backend SHA-256 in
`census/backend.sha256`. Every build and test ran under a memory guard
(`CARGO_BUILD_JOBS=3`, one of two flock slots, `MemoryMax=22G`).

This is a regression and refusal measurement in the explicit unverified
frontend lane. It is not a proof claim, and it does not establish compiler
completion or release readiness.

⚑ **Superseded for the tree, retained for its commit.** `origin/main` moved
two further commits (`4ded2b97c`, `b943790f0`) while this round was under
review, and the second of them rewrote the very vacuity rule this round had
reconciled. They were merged in a second round and the whole measurement was
re-run; see
[the round-2 report](../2026-09-22-linux-x86-64-upstream-round2/README.md).
Everything here remains the record of the tree at `9a276a0c1`, and the
`[TCG-PROOF-465]` section below is superseded by the round-2 reconciliation.

## What the merge brought in

| Side | What it carries |
| --- | --- |
| upstream (148) | Darwin AArch64 code signing and MAP_JIT entitlements, Mach-O dylibs and `__DATA_CONST`, the JIT data image and JIT unwind tables, the AArch64 frame dataflow net and independent physical liveness, NZCV producer/consumer and half-precision FCVT proofs, first-class closures, direct-tag enums, i128 switch selectors and the checked-multiply obligation, the trust-ir construct inventory gate, and three trust-ir pin moves |
| this branch (46) | two-carrier `PassMode::Pair` ARGUMENTS on x86-64 (XD-05), the `call_only_body` certificate category, the shared pure-trap predicate and the x86 vectorizer's carrier guards and memset route, the composed 3/5/6/7-byte SysV eightbyte lane, the Linux x86-64 floor's repairs, decided-absent lane and bridge lane, and the Clean/TY host-target loaders |

The trust-ir pin moved `dfdb950a` -> `7b9146ba` (both manifests, both
lockfiles). Two new IR surface facts arrive with it: `Inst::MakeAggregate`
(refused by name in the lowering adapter, counted in the SSA use walk, module
merge, the compile service and the opcode-name tables) and `ScopeData`'s
`inlined_at` inlining chain (remapped and fail-closed through module merge,
its call-site file index range-checked).

## `library/core` refusal census, O0, certificates on

`scripts/trust_ir_cg_census.py` from the Trust checkout
(`ceb94fe99`) against the merged bridge, `--panic abort --opt-level 0`.
Retained in `census/`.

| Measurement | Failed roots | Distinct reasons | Objects emitted |
| --- | ---: | ---: | ---: |
| 2026-09-21 merged wave 1 | 183 | 27 | 3,249 |
| 2026-09-21 after reconciling with upstream | 183 | 27 | 3,249 |
| **2026-09-22 after merging origin/main's 148** | **183** | **27** | **3,249** |

The baseline HELD EXACTLY. The failed-root SYMBOL SET is identical to the
retained 2026-09-21 reconciled census (0 added, 0 removed, compared symbol by
symbol), and the per-reason table is line-identical: `[TCG-POINTEE-DYN-VALUE]`
30, `[TCG-PASSVAL-067]` 27, `[TCG-POINTEE-LANES]` 21, fat-pointer union fields
21, `[TCG-POINTEE-UNSIZED-TAIL]` 16, memory-backed slice `Rvalue::Cast` 11,
`[TCG-REGALLOC-063]` 8, `[TCG-RET-REGCLASS]` 6, `[TCG-ARG-ABI]` 2, then a tail
of 18 reasons at five roots or fewer. In particular `[TCG-PROOF-465]` stays at
0 under the reconciled single vacuity mechanism (below), and the pin move
introduced no new refusal.

## Linux x86-64 regression floor

`scripts/check_linux_x86_64.py --jobs 4 --max-rss-gib 20 --trust-driver
<stage2>/bin/trustc`, every per-target log retained in `floor/`.

| Run | Targets | Pass | Fail |
| --- | ---: | ---: | ---: |
| 2026-09-21 merged wave 1 | 68 | 57 | 11 |
| 2026-09-21 after reconciling with upstream | 68 | 57 | 11 |
| **2026-09-22 after merging origin/main's 148** | **68** | **57** | **11** |

Target for target identical to the retained reconciled run: no target added or
removed and no status change. The 11 failures are the same two open items —
XD-01 proof promotion on a formal-capable host (8 targets, all
`ProofPromotionRejected … validated only by bounded statistical sampling`) and
X03 ELF exception handling (3 targets, still Darwin-guarded). `e2e_x86_64_swiftcc`
is printed as decided absent under XD-03, as before.

## Root workspace unit tests

All on the merged tree with a clean working tree.

| Suite | Result |
| --- | --- |
| `trust-cg-lower --lib` | 1,882 passed / 0 failed |
| `trust-cg-opt --lib` | 3,550 passed / 0 failed |
| `trust-cg-codegen --lib` | 3,988 passed / **16 failed** |
| `trust-cg-verify --lib post_ra_dataflow` | 74 passed |
| `trust-cg-verify --lib x86_64_lowering_proofs` | 176 passed |
| `trust-cg-verify --test coverage_gate_tests` | 49 passed |
| `trust-cg-verify --test meta_theorems` | 8 passed |
| `trust-cg-verify --test soundness_manifest` | 11 passed |
| `trust-cg-verify --test x86_addressing_gate` | 10 passed |
| `trust-cg-verify --test x86_volatile_trace_gate` | 8 passed |
| `trust-cg-codegen --test e2e_x86_64_aggregate_abi` | 30 passed |
| `trust-cg-codegen --test e2e_x86_64_aggregate_byval_arg` | 8 passed |

The 16 `trust-cg-codegen --lib` failures are byte-identical to the list
retained from the 2026-09-21 reconciled run
(`codegen-lib-failures.txt` here equals
`../2026-09-21-linux-x86-64-integrated/reconciled-codegen-lib-failures.txt`):
fifteen `compile_service` tests and
`test_aarch64_parallel_and_serial_multi_function_byte_identical`, all
`ProofPromotionRejected`, the same XD-01 class as the floor's eight. The merge
introduced no regression and added 71 passing tests to that crate.

`cargo test -p trust-cg-verify --lib` in full is NOT measured here and remains
the open question the 2026-09-21 report records: its solver-backed tests
(`ay_bridge`, `cegis`, `canary_cert`, the Z3 CLI test) are wall-clock flaky on
a loaded host, and two other agents were building throughout this session.

## Bridge cross-backend lanes

Two bridge lanes exercise the merged instruction-selection work end to end
against LLVM, in the explicit unverified frontend lane
(`targo --unverified test --release --locked`). Logs in `bridge/`.

| Lane | Result |
| --- | --- |
| `m142_x86_scalar_pair_arg_xback` (XD-05 two-carrier `PassMode::Pair` ARGUMENTS, 26 shapes × four backend combinations × O0–O3) | **1 passed / 0 failed**, 1,213 s |
| `m141_x86_partial_eightbyte_aggregate_xback` (composed 3/5/6/7-byte SysV eightbyte lanes) | **1 failed**, 345 s — one combination |

⚑ `m141` is RED, and it was red before this merge. The failing combination is
`O1 opt_ipv4`, trust-cg callee + trust-cg caller, and it fails at the LINK step
(`collect2: error: ld returned 1 exit status`, the symbol reported as `defined
at callee…rcgu.o:(.text+0x140)`), not on a value mismatch. The PRE-MERGE run of
the same lane on this branch's HEAD is retained beside this file as
`bridge/m141-pre-merge-2026-09-21.log` (2026-09-21 15:55, before the
2026-09-22 merge): it carries the same failure with the same combination and
the same text, so the pre-existence is checkable from the tree rather than from
a session log. It is therefore NOT a merge regression, and the merge did not
change it. `m141` is not registered in the Linux x86-64 floor (of
the three bridge lanes only `m143_x86_vectorize_trace` is), so the floor's 57/68
does not cover it. Diagnosing that link failure is owed work, tracked here
rather than left in a session log.

## The one merge decision that changed behaviour

THREE lanes had independently attacked the `[TCG-PROOF-465]` vacuity class,
and the third one arrived after this branch's first merge was cut.

* Upstream `3b80e9497` measured the class WITHOUT the bridge dylib and widened
  the anonymous empty-body escape by OPCODE SHAPE to `[Ud2]` /
  `[Push, MovRR, Ud2]`, explicitly declining `[Call, Ud2]`.
* This branch measured the census WITH the dylib on this Linux host and added
  the named `call_only_body` certificate keyed on the verifier's per-row
  DISPOSITION, measuring the class 46 → 0.
* Upstream `b943790f0` (2026-09-22, merged here in the second round) got the
  bridge running on the Darwin workstation, DISASSEMBLED the remaining roots
  and replaced its own guess with a SOURCE-bound rule: the call-then-trap shape
  is admitted only when the LIR handed to instruction selection is exactly
  `Jump* ; Call (no args, no results) ; Trap`
  (`lir_is_zero_arg_direct_call_then_trap`, threaded through every
  `proof_certificates_from_x86_64_report` call site).

**Resolved to ONE mechanism whose gate is the CONJUNCTION of the second and
third lanes' facts.** `call_only_body` is now issued only when every report row
carries the verifier's own by-design disposition AND the LIR source is a bare
diverging transfer (`Jump* ; Trap`, or upstream's zero-argument call then
trap). `x86_64_report_is_empty_body` stays at exactly `[Ret]`.

That conjunction is strictly stronger than either lane alone, and the
difference is not theoretical. The disposition half ALONE promoted
`call f; ret` — a forwarding shim that returns to its caller and discharges
nothing — with a `verified: true` certificate; the source half alone would
promote a body whose rows the verifier FAILED. Both holes are now pinned shut
by measurement, not prose:

* `x86_call_only_bodies_certify_through_the_real_verifier` drives
  `unreachable`, `call f; unreachable` (one-block and two-block) and
  `call f; ret` through the real instruction selector and the real verifier,
  and REQUIRES the last one to be refused, naming the source half in its
  refusal text;
* `x86_call_only_body_is_certified_on_verifier_dispositions_and_lir_source`
  holds each half fixed and varies the other, and subsumes upstream's four
  raw-report controls (`[Call, Ud2]`, `[Push, MovRR, Call, Ud2]`,
  `[Jmp, Call, Ud2]`, `[Push, MovRR, Jmp, Call, Ud2]` refused without a
  source);
* `x86_trap_only_body_certifies_and_argument_shims_are_not_vacuous` requires
  upstream's own trap-only shim AND its two new call-then-trap shims
  (`shim_abort_call`, `shim_jump_abort_call`) to promote under the NAMED
  certificate through the whole module-compile boundary on both
  `x86_64-apple-darwin` and `x86_64-unknown-linux-gnu`.

Upstream's improved vacuity DIAGNOSTICS are kept verbatim: a refusal now names
the report rows and either the source's own shape or the fact that no source
was supplied. The rationale is in the merge commit,
`docs/linux-x86-64-completion.md` and `LIMITATIONS.md`.

## What this does not measure

No `alloc` or `std` census, no performance run (the beat-llvm ledger row is
still owed and no runtime number here is evidence), no Trust-verified
compilation of trust-cg itself, no bridge-corpus floor, no AArch64 or Darwin
floor (this host runs neither), and no full `trust-cg-verify --lib` run.
