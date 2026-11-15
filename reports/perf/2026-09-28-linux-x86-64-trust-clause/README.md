# The Trust clause on x86-64 Linux, first measurement (2026-09-28): existing corpora barely reach the backend, and a constructed one passes end to end

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The completion objective names four program classes — Trust, Rust,
Lean-through-Clean and TY. Rust has a `core` census, Lean-through-Clean has the
38-fixture sweep, TY has `ty_bfs_minimal`. The **Trust** class had never been
measured on this host, and every other measurement in this round used
`-Ztrust-verify=off` (the explicit unverified frontend lane), so nothing said
anything about programs compiled WITH Trust verification.

This is that measurement. Two findings: the existing Trust corpora cannot answer
the question, because Trust's own strict verification stops most files before
codegen; and a CONSTRUCTED corpus of seven strict-verified functions compiles through
trust-ir, links, runs, and matches an LLVM-built reference exactly.

## Method

All 47 `.rs` files under `tests/daily-driver-realistic/` in the Trust checkout,
each compiled through the trust-cg backend with Trust verification **ON** (no
`-Ztrust-verify=off`), `--edition=2024`, `--crate-type lib`,
`-Copt-level=2 -Cpanic=abort --emit=obj` into a PER-FILE output directory, with
`-Ztrust-ir-cg-args=no-proof-certs` so the proof-promotion gate does not mask the
lowering question (the same posture as the `core` census). Per-file outcomes are
retained in `per-file-outcomes.log`.

Emitted code is counted by summing `.text` section sizes with `objdump -h`, NOT by
exit status — see the vacuity note below.

## Result

| Outcome | Count |
| --- | ---: |
| compiled AND emitted machine code | **3** |
| compiled, exit 0, but emitted NO `.text` | 15 |
| Trust STRICT verification refused | 24 |
| Trust obligation not proved | 1 |
| **trust-cg (backend) refused** | **0** |
| Lean-island elaboration errors | 4 |
| total | 47 |

**trust-cg refused nothing.** That is the good news and it is also nearly all this
measurement establishes, because the backend was only EXERCISED on 3 of the 47
files. The other 44 never produced code:

* **24 + 1 never reached codegen.** Trust's own strict verification rejected them,
  e.g. `derive_debug_alone.rs` — two lines, `#[derive(Debug)] pub struct W(pub u32);`
  — fails with `Trust strict verification failed for
  <derive_debug_alone::W as core::fmt::Debug>::fmt: 1 obligation(s) were not fully
  verified`. Its verification report reads `0 proved, 0 failed, 0 unknown, 1
  runtime-checked`, so the obligation was RETAINED as a runtime check rather than
  refuted, and strict mode declines that. This is a Trust FRONTEND policy and says
  nothing about trust-cg.
* **15 had nothing to emit.** Library files of type definitions, generic functions
  with no monomorphic use, or `derive`s alone produce no monomorphized items, so
  `trustc` exits 0 having codegen'd nothing.
* **4 are Lean-island errors**, of which two are DELIBERATE negative tests —
  `false_theorem_must_be_rejected.rs` (rejected: "omega: constraints are
  satisfiable, goal not provable") and `mathlib_proof_must_be_refused.rs` (refused:
  "depends on trust provenance: Nat.Prime"). Both are working as designed. The other
  two fail Lean elaboration (`five` registered with a different signature), which is
  also outside trust-cg.

## A vacuity trap this measurement walked into first

The first pass counted `trustc` exit status and reported "18 compiled OK". That was
wrong in the way this round has repeatedly caught elsewhere: exit 0 on a library
with no monomorphized items means the backend was never asked to lower anything.
Counting `.text` bytes instead drops 18 to **3**. Two further harness bugs were
found and fixed on the way — an `--edition=2021` invocation that failed five files
on let-chains (a harness error misread as a backend refusal), and unquoted word
splitting over log lines that inflated one run's iteration count to 120 over a
47-file corpus.

## What this does and does not say

* It does NOT show the Trust clause is satisfied. Three programs is not a corpus.
* It does NOT show the emitted code is correct — there is no execution oracle here,
  only "an object with a non-empty `.text` was produced".
* It DOES show trust-cg is not the limiting factor for this corpus: zero backend
  refusals across 47 files, and the binding constraint is Trust's strict
  verification rejecting 24 of them before codegen.

The three other candidate corpora were then measured the same way —
`tests/trust-provability` (8 files), `tests/trust-witness` (10) and
`tests/idiomatic-rust-sample` (14), 32 in total. They are WORSE for this purpose:
**0 emitted code, 10 compiled with no `.text`, 20 refused by Trust strict
verification, 0 trust-cg refusals, 2 other.** So no existing corpus in the Trust
checkout exercises the x86-64 backend under verification, which is what motivated
constructing one.

## A CONSTRUCTED corpus that does reach the backend — and it passes

Since no existing corpus exercises the backend, one was built. `strict-verified-corpus.rs`
and `strict-verified-driver.c` are retained beside this file.

Method: seven `extern "C"` functions in a `--crate-type staticlib`, compiled with
Trust verification **ON**, `--edition=2024`, `-Copt-level=2 -Cpanic=abort`, once
through trust-cg (`no-proof-certs`) and once through LLVM; each archive linked by
`gcc -O2` against the SAME C driver, which loops 64 times over an xorshift stream
feeding every function and prints one `u64` checksum.

Result: both builds print **15978519021491720076** — byte-identical. So seven
Trust-strict-verified functions compile via trust-ir on x86-64 Linux AND execute
correctly against an LLVM-built reference.

Getting there required narrowing to what Trust's strict mode can actually prove, and
each rejection was IDENTICAL in both lanes, which confirms it is frontend and not
trust-cg:

* `rotate_left` — `Trust strict verification failed for lib::t_rotl: 1 obligation(s)
  were not fully verified`.
* a raw-pointer loop (`*p.add(k)` over a fixed array) — `Trust Level 0 safety
  verification incomplete: 8 obligation(s) were not proved`. Correctly so: it is
  genuinely unsafe.
* `#![no_std]` with a `#[panic_handler]` returning `!` via `loop {}` — `native typed-
  TrustIr lowering did not complete, so the panic-freedom` obligation fails. Dropping
  `no_std` removes the need for the handler.

What survives and verifies: `wrapping_add`, `wrapping_mul`, `xor`, masked `shl`,
masked `shr`, a three-step xorshift, and a one-branch conditional select.

### WIDENED from 7 to 17 functions — and the "narrow surface" claim was wrong

The 7-function result above led me to conclude Trust's verifiable surface is narrow.
That was wrong, and it came from generalising off two unlucky shapes. Ten further
candidate shapes were tried, one file each, and **all ten strict-verified and
compiled through trust-cg**:

| shape | function |
| --- | --- |
| struct construct + field read | `s01` |
| tuple construct + element read | `s02` |
| cross-function call | `s03` |
| bounded `while` loop (8 trips) | `s04` |
| fixed `[u64; 4]` array | `s05` |
| 4-way `match` dispatch | `s06` |
| signed `i32` wrapping arithmetic | `s07` |
| `bool` comparison result to `u32` | `s08` |
| `Option<u64>` construct + match (niche) | `s09` |
| `count_ones` after an xorshift | `s10` |

The combined 17-function corpus (`strict-verified-corpus.rs`, driver
`strict-verified-driver.c`) builds under both backends and both binaries print
**5937917942593127082** — identical. trust-cg emits **1984 bytes** of `.text` for it.

So the clause's coverage is: scalar ALU across `u32`/`u64`/`i32`, wrapping add/sub/mul,
masked shifts, xor, a three-step xorshift, `count_ones`, conditional select, struct,
tuple, array, `Option` niche, 4-way match, a cross-function call, and a bounded loop —
all Trust-strict-verified, all lowered by trust-cg, all executing correctly against
LLVM.

### WIDENED AGAIN, 17 -> 23, and the provable/unprovable boundary MAPPED

Twelve more shapes were tried. Six more strict-verify and compile, six do not — and
every one of the six failures reproduces IDENTICALLY through the LLVM backend, so all
six are Trust Level 0 frontend limits and none is attributable to trust-cg.

| INSIDE Trust's provable set (compiles + runs) | OUTSIDE it (frontend refusal) |
| --- | --- |
| 3-variant enum with payloads (`e01`) | `f64` / `f32` ARITHMETIC (`f01`, `f02`) |
| `f64` COMPARISON to `u32` (`f03`) | generic `T: Add` (`g01`) |
| instantiated generic, `T: Copy` (`g02`) | slice indexing in a loop (`h01`, 7 obligations) |
| `u128` multiply + shift (`i01`) | `dyn` trait dispatch (`tr01`, 4 obligations) |
| trait with STATIC dispatch (`tr02`) | `checked_add` (`u01`) |
| `saturating_sub` (`u02`) | `rotate_left`, raw-pointer loops |

The boundary is informative in both directions: floating-point COMPARISON verifies
while floating-point ARITHMETIC does not; a generic instantiated at a `Copy` bound
verifies while one behind `Add` does not; a trait dispatched STATICALLY verifies while
`dyn` does not. Those are frontend facts, not backend ones.

The 23-function corpus builds under both backends and both binaries print
**267826962111695130** — identical.

A VACUITY CHECK THAT FIRED HERE, recorded because it nearly passed unnoticed: the
first 23-function run printed the SAME checksum as the 17-function run. The six new
declarations had been added to the driver but their CALL sites had not, so the new
functions were compiled and never executed. A checksum that does not move when six
functions are added is the tell; after fixing the driver it moved to
267826962111695130.

### What this positive result is worth, stated narrowly

* It is still a FLOOR rather than a survey, but a much wider one: 23 functions over 18
  shape families, with the provable boundary mapped in both directions. The corpus was CONSTRUCTED to pass strict verification, so it
  measures that trust-cg handles what Trust can prove — not how much Trust can prove.
  Still absent: floating-point ARITHMETIC, `unsafe`, heap/allocation, `dyn` dispatch,
  slice indexing, `checked_*`, panic paths, and anything reaching `std` — and every one
  of those is a Trust FRONTEND limit, verified by identical failure through LLVM, not a
  trust-cg gap.
* It DOES establish the thing the earlier sections could not: the Trust lane reaches
  the backend, the backend lowers it, and the result runs and agrees with LLVM. Zero
  backend refusals across 47 + 32 corpus files now has one positive data point behind
  it instead of none.
* The surface is NOT narrow, and my first reading of it was wrong. `rotate_left` and
  raw-pointer loops fall outside, but structs, tuples, arrays, matches, calls, bounded
  loops and `Option` niches are all inside. Two unlucky shapes are not a ceiling.

## Status of the clause, and what would measure it FULLY

The Trust clause is **partially measured**: seven strict-verified functions compile
via trust-ir and execute correctly against LLVM, with zero backend refusals across 79
corpus files. It is NOT satisfied, because seven scalar functions are a floor rather
than a survey — no aggregates, no calls, no loops, no floating point, no unsafe.

What would measure it fully is a corpus that both passes Trust's STRICT verification
and contains a broad range of reachable monomorphic executable code. None of the four
corpora examined does: `daily-driver-realistic` (47), `trust-provability` (8),
`trust-witness` (10) and `idiomatic-rust-sample` (14) together yield 3 files with
emitted code and 45 strict-verification refusals. `tests/trust-falsification` (438
files) was not measured and is, by its name, mostly deliberate negatives.

The honest reading is that the clause's ceiling is set by Trust's verifiable surface
rather than by trust-cg: a single intrinsic (`rotate_left`) and any raw-pointer loop
fall outside it, and both were rejected IDENTICALLY through the LLVM backend, so
neither is attributable to trust-cg. Widening that surface is Trust frontend work.

The constructed corpus here should be promoted to a committed test target so the
positive result is a ratchet rather than a one-off reading; it is retained as source
plus driver plus expected checksum (`expected-checksum.txt`) so that is mechanical.
