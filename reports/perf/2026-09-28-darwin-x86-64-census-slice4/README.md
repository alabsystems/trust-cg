# Darwin x86-64 `library/core` census — slice 4 (memory), 2026-09-28

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

One proof row, same host and toolchains as the
[slice-3 census](../2026-09-28-darwin-x86-64-census-slice3/README.md): native
stage-1 `trustc 1.99.0-dev (d7f143f3b 2026-09-21)`, bridge built on this host
against the stage-1 `stage0-sysroot` (`targo --unverified build --release
--locked`), `-Ztrust-verify=off`, O0, `-Cpanic=abort`, one CGU, proofs
required (the bridge default), `-Ztrust-ir-cg-args=x86-body-trace` and
`-Ztrust-ir-cg-args=x86-body-dump=DIR`. Nothing here is a completion claim.

| Row | trust-cg | Mode | Failed roots | Distinct reasons |
| --- | --- | --- | --- | --- |
| `core-x86_64-darwin-O0-proof-slice4` | slice-4 branch (see Tree) | proofs required | 2727 | 1 |
| `core-x86_64-darwin-O0-proof-slice4-review` | review fixes, merged with `main` (see below) | proofs required | 2727 | 1 |

## What was measured

- **Tree.** The bridge was built from the slice-4 worktree. The production
  code of the commit that adds this report is the code the dylib was built
  from; after the build only comments, `rustfmt` layout, one clippy rewrite
  (`bool::then(|| r)` to `then_some(r)` in `stack_range`), tests and
  documentation changed. `backend.sha256` is the dylib's digest. The census
  tool's `provenance.json` records `trust_cg_rev` = `de1f19099`: that is the
  `~/trust` superproject's pin, not the measured tree.
- **Replay tools.** As for slice 3: the toolchain AY recorded by the bridge
  build (`ay 0.27.0+build.10530`) and the default checker discovery, which
  resolves `store/clean/current` -> `~/clean-checker/bin/clean` (Clean
  `5f09e36c`) on this host.
- **Memory.** No `[TCG-COMPILE-DRIVER]` resource-budget refusal occurred.
- **Wall time** was 1892 s, against 1203 s for the `census-r38P` baseline
  (single runs each on this shared four-core host, so a trend, not a
  measurement). Much of the rise is real: a body the lane now admits but AY
  does not certify runs AY to its answer or its 30 s budget, and a codegen
  unit whose batched compile fails is recompiled per function, replaying
  its theorems again (LIMITATIONS.md, slice 4, "Cost").

## Result

2727 failed roots, all `[TCG-PROOF-465]`. The baseline is `census-r38P`
(`main` at `94652175d`, the slice-3 tree): 2887 roots, all
`[TCG-PROOF-465]`. Compared with it:

- **160** roots newly promote. By their baseline uncovered-opcode set the
  largest groups are `Lea, MovMR, MovRM, MovRR` (47), `MovRM, MovRR, MovRR32,
  Movzx` (26), `MovRM, MovRR` (19) and `AddRR, Lea, MovMR, MovRM, MovRR[,
  MovRR32, Movzx]` (28).
- **0** roots newly fail. Every failed root here is also a baseline root.
- No `[TCG-SOURCE-BOUND-X86-MISMATCH]` occurred.

The body trace shows 654 functions whose theorem replayed `Valid`, 64 with
`replay=none` and 1 refuted; `body_trace_gaps.tsv` lists the 65 with their
raw outcome.

- All 64 `replay=none` are AY rejecting its own proof (`strict UNSAT proof
  validation failed: step t1 uses unverified trust rule`, `unknown`,
  `(:reason-unknown (incomplete self-check-rejected))`). Twelve are the
  slice-2/3 gaps (`NonNull::add`/`offset`, `i32::wrapping_mul`,
  `try_parse_digits`); the other 52 are new memory bodies of 54 to 242 rows,
  mostly constructors (`new`, `into_iter`, `clone`) that write an aggregate
  through an sret buffer. For each, AY computes UNSAT (it finds no
  counterexample) and then rejects its own proof in strict certification,
  the class slice 3 recorded for a seven-item concatenation; the rows stay
  unverified, never credited, and the encoding is not reshaped per function. The replayed queries were dumped with
  `x86-body-dump` and reproduce the outcome outside the compiler.
- The refuted one is `PanicInfo::can_unwind`, which returns a `bool` field:
  the slice-4 FINDING (the selector returns a loaded `bool` as `mov r8, m;
  mov eax, r32`, leaving EAX bits 8..31 undefined against the backend's
  clean 32-bit `bool` result contract). It was a failed root before and
  still is; its rows now fail with an AY counterexample instead of staying
  unverified.

## Remaining blockers

Of the 2727 failed roots, 1418 have no flag or control-flow row among their
uncovered opcodes. The lane's refusal for them (one line per root):

| Roots | Refusal |
| ---: | --- |
| 433 | two scalar results (a `ScalarPair` return in RAX:RDX) |
| 231 | a call to an sret callee |
| 150 | a non-scalar result (float, `i128`, ...) |
| 113 | a non-scalar parameter |
| 101 | a private slot's address passed to a call (the slot escapes) |
| 79 | no observable (the `#[track_caller]` panic helpers) |
| 51 / 43 | `GlobalRef` / `ExternRef` (a global's address) |
| 40 | a call with two results |
| 64 | bound, AY does not certify (above) |

## Earlier runs of this row

The same host measured two earlier builds of the slice-4 tree, both
against the same baseline with 0 newly failing roots: without `StructGep`,
sret and constant folding, 68 roots promoted (2819 failed); with
`StructGep` and sret but without constant folding of slot offsets, 135
promoted (2752 failed).

The row keeps `gap_table.md`, `provenance.json` (home directory shortened to
`~`, the census scratch directory to `<scratch>`), `failed_roots.jsonl.gz`,
`body_trace_gaps.tsv` and the bridge's `backend.sha256`.

## Review-fix row (`core-x86_64-darwin-O0-proof-slice4-review`)

The same census after the review of fd126a8ad, on the branch merged with
`main` (`3165aae51`, trust-ir pin `3f0ffd70`) plus the review fixes: a narrow
load's upper bits are always a free input, a store's register operand must
name the stored width, a `bool` is never loaded from incoming memory, the
reordering exemption requires the values to move with their addresses, the
merged per-condition frame refusal, and the body dump rendered with the
replay's own configuration. The bridge was built from that tree
(`backend.sha256`); after the build only documentation, tests, `rustfmt`
layout and this report changed. Same trustc, flags, AY (build 10530) and checker
(`store/clean/current`, Clean `5f09e36c`) as above; no resource-budget
refusal; wall 1818 s (single run).

- **2727 failed roots, all `[TCG-PROOF-465]`**: the same root set as the
  row above (0 promoted, 0 newly failing against it), so against
  `census-r38P` again 160 promote and 0 newly fail. No
  `[TCG-SOURCE-BOUND-X86-MISMATCH]`.
- **Per function**, against the row above: 404 refusals now name their
  frame condition (`has an sret-arg callee`, main's attribution), and
  `PanicInfo::can_unwind`, the one refuted body, is now outside the domain
  (`loads a bool from incoming memory`). No other function changed outcome:
  no body that replayed Valid lost it.
- **Trace:** 654 functions replay `Valid` and 64 `replay=none`, all
  `(:reason-unknown (incomplete self-check-rejected))` (`body_trace_gaps.tsv`,
  the row above's list minus `can_unwind`); 1308 `Valid` and 128 `none`
  trace lines, so every bound body is judged twice (the batched compile of
  the one codegen unit, then its per-function CT-BATCH fallback).

### Corpus (same bridge, O0, proofs required)

The slice-4 corpus (26 memory bodies; an sret writer and two struct-field
readers; the two `bool` finding bodies; nine further sret and gap bodies,
`extern "C"` functions compiled as five crates) compiles
with the same per-function trace outcomes and exit codes as with the
slice-4 bridge, except
that `f_load_bool` (`*p` of a `*const bool`) is now outside the domain
instead of refuted (still a refused compile). The promoting objects pass
their native C harnesses again: 18876 checks (26 memory bodies, aliased
pointers included) and 1568 checks (sret writer and struct-field readers),
0 failures. Four admitted corpus bodies do not certify; `corpus-gaps/` holds
the queries the bridge dumped for them (`x86-body-dump`), which replay on
the toolchain AY (`-smt2 FILE --strict-proofs --proof OUT --proof-format
alethe`) as:

| Query | Body | Rows | AY outcome | AY time |
| --- | --- | ---: | --- | ---: |
| `m_store_mixed.smt2` | four field stores through `*mut Mixed` (`u32`, `u16`, `u8`, `bool`) | 31 | `unknown` / `(:reason-unknown timeout)` | 32.9 s |
| `m_spill_store.smt2` | `*p = x` with `p` spilled to a slot | 11 | self-check rejected | 11.1 s |
| `r_big_swap.smt2` | sret writer of a three-`u64` struct | 64 | self-check rejected | 5.0 s |
| `r_copy_big.smt2` | sret copy of a three-`u64` struct | 76 | self-check rejected | 1.4 s |

"Self-check rejected" is the exact output `c !! MODEL-UNCONFIRMED ...
computed UNSAT rejected by mandatory strict certification: strict UNSAT
proof validation failed: step t1 uses unverified trust rule` / `unknown` /
`(:reason-unknown (incomplete self-check-rejected))`. Their rows stay
Unverified; the encoding is not changed for them.
