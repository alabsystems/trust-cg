# compile-apples — proofs-off compile time vs LLVM

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## What this measures

`benchmarks/beat-llvm` measures the **production** lane (certs + solver + cache
on) and deliberately refuses to mark a proof-weakened run `headline_eligible`.
That is the right policy for a headline number, but it leaves the lane we
actually optimise against untracked.

This harness measures the narrow, specific target: with verification **off** on
both sides — rustc's LLVM backend at `-C opt-level=N` versus trust-cg at the
same `-C opt-level=N` — trust-cg should be strictly faster to compile on *every*
program. Verification cost gets added back only once that holds.

```sh
./run.py --opt 2 -n 7                    # median-of-7, interleaved A/B
./run.py --opt 3 -n 15 --out-dir /tmp/x
```

## Why it reports CPU time as the primary signal

These compiles are ~120 ms wall and the difference being chased is 5–15 ms —
**the same size as the scheduling noise on a shared box.** Two runs of the
identical binary moved `p1_xorshift` from 1.153x to 0.994x and `m1_call_chain`
from 1.049x to 0.884x. Wall-clock ranking at this scale is not evidence.

Child CPU time (`RUSAGE_CHILDREN`, user+sys) is not perturbed by descheduling,
so it separates *"our compiler did more work"* from *"the machine was busy"*.
The spread tightens from 0.86–1.21 (wall) to 1.11–1.29 (CPU), and the ordering
becomes stable across runs.

Both are reported. They say different things and both are true.

## The finding that motivated the switch

Measured at `-C opt-level=2`, median-of-5, interleaved, on a quiet 20-core box:

| lane | geomean vs LLVM | trust-cg faster on |
| --- | --- | --- |
| wall clock | **1.029x** | 4/18 |
| CPU time | **1.186x** | **0/18** |

rustc's LLVM backend runs at `cpu/wall = 1.00` through this path — exactly
single-threaded. trust-cg runs at 1.13–1.18, i.e. it spends **~19% more total
CPU** and hides part of it behind threads. Near-parity on wall clock is bought
with cores.

That trade is real, not waste. Forcing `TRUST_CG_MAX_PARALLELISM=1`:

| | geomean CPU | geomean wall |
| --- | --- | --- |
| default parallelism | 1.186x | **1.029x** |
| `TRUST_CG_MAX_PARALLELISM=1` | **1.121x** | 1.058x |

Single-threaded wins CPU on 17/18 and loses wall on 11/18. So roughly 6.5 points
of the CPU gap is thread-pool overhead that genuinely buys wall-clock time; the
remaining ~12% is extra work trust-cg does that LLVM does not.

**This matters for the goal.** A single interactive `rustc` invocation cares
about wall clock, where we are close. A real build is `cargo -j N` with every
core already busy — there is no idle core to hide CPU behind, and the CPU number
is what the user pays. Claiming compile-time superiority on wall clock alone,
while losing 18/18 on CPU, would not survive contact with a parallel build.

## Discipline

* **Interleaved A/B** — each repetition compiles LLVM then trust-cg back to
  back, so drift hits both arms equally.
* **Real output files** — never `-o /dev/null`.
* **Median, not mean.**
* **Load gate** — refuses to run above a 1-minute load of 2.0 (`--allow-loaded`
  overrides, and the row is then not evidence).
* **Staleness gate** — refuses to measure a dylib older than any `.rs` in the
  tree, so results are never attributed to the wrong build.

## Where the proofs-ON gap actually is (2026-08-25)

`compile-apples` reports 0.9588x with verification off on both sides. The
production lane (`beat-llvm`, certs+solver on) reports ~2.0x. That whole
difference is ONE thing, and it is worth writing down because it is not what
the shape of the number suggests.

**It is not per-function work, and it does not scale with the program.**
Proofs-ON trust-cg vs LLVM at `-Copt-level=2`, median of 5:

```text
  functions   llvm      trust-cg   ratio    delta
      8      108.8ms    195.8ms    1.801x    87ms
     64      127.3ms    209.9ms    1.649x    83ms
    256      141.4ms    255.4ms    1.807x   114ms
```

A 32x increase in function count moves the DELTA by 27ms. The ratio only looks
flat because LLVM grows too. The cost is a FIXED per-process charge.

**That fixed charge is the statistical sweep lane.** Isolated with the env
kill-switches (child CPU, median of 9): an empty `fn main() {}` costs 154.8ms
production and 114.0ms with `TCG_NO_PROOF_CERTS=1` — a 40.7ms difference — and
per-obligation tracing (`TCG_TIME_SWEEP=1`) accounts for essentially all of it
as first-touch sweeps of ~15 distinct obligation KINDS at
`DEFAULT_SAMPLE_COUNT` = 100,000 samples each. Take that away and trust-cg is
at ~1.05x of LLVM on the same program, which is consistent with the 0.9588x
this harness measures with both sides unverified.

**Per-function fanout does not fix it, and the measurement explains why.** The
certificate lane already fans out (`verification_worker_count_for_items` has no
minimum-items gate), and it demonstrably works when there is enough
independent work — a 64-function module runs at 1.35x concurrency and 16% less
wall. But on the beat-llvm corpus concurrency is 0.98-1.00x, because every
function needs the SAME ~15 obligation kinds: the first worker to reach a kind
computes it while the other workers BLOCK on that kind's memo cell. Fanning out
across functions cannot parallelise a cost that is shared between them.

The lever is to parallelise across obligation KINDS rather than across
functions — collect the distinct obligations first, sweep them concurrently,
then generate certificates against a warm memo. That landed
(`registry_obligations_for_functions` enumerates without re-implementing the
walk's selection), and four more levers followed it, each measured on this box
(bridge -O3 vs LLVM -O2 is the gate's definition; see `ratchet/ledger.jsonl`):

| lever | what it is | measured |
| --- | --- | --- |
| kind-parallel pre-warm | sweep the distinct kinds on a wide default-stack pool, walk against a warm memo | empty 1.270x -> 1.136x (3-prog, paired) |
| sample chunking | split each kind's 100k samples across the pool; the LCG is affine, so chunk `i` starts at the exact sequential state — samples, verdicts and counterexample text byte-identical | corpus 1.257x -> 1.117x, 18/18 faster |
| lane-batched evaluator | 8 samples per op dispatch on u64 lanes (poison as a per-lane bit); failing lanes re-checked by the scalar path | user CPU -35..-45%, 2891/3552 registry tapes |
| speculative init sweep | the 13 registry kinds EVERY program needs, swept from backend `init` while rustc's front end runs | codegen_crate -3..-4ms |
| wide (u128-lane) evaluator | the NEON tapes (661 registry tapes; CntV.16B is 803 ops) | v3_popcount user CPU 396 -> 179ms; 3552/3552 tapes batched |

| release the sweep pool at `join_codegen` end | its 20 workers are torn down while rustc links, not inside exit — 5-10ms of the after-join segment | p2_collatz 123.8 -> 118.8ms (n=11) |
| memo without tree hashes/clones; tier-0 answers "no solver" first | per instruction of every walk: two tree hashes + a clone + a global mutex, gone | within noise (±1%) |
| asynchronous pre-warm | the walk starts while the sweeps run; a kind the walk reaches first fans out to the registered helper pool | v3 main CGU pre-warm+certs 11.8 -> 7.4ms; wall within noise |
| registry queries resolved once per process | the walk lowercased every candidate name per instruction | proof_certs p7 4.7 -> 4.0ms, v3 8.3 -> 7.2 (timers, n=15) |
| fixed modules off the critical path | the entry wrapper, allocator shim and referenced `__trustcg_*` helpers used to compile serially on the main thread AFTER the user CGUs; they now run through a reusable bounded executor (`TyCtxt`-free compile core; `spawn_fixed_module_compile`) — one 32 MiB-stack worker by default, at most two when explicitly widened — with entry+allocator scheduled from the end of the mono pre-pass and helpers at their FIRST reference during lowering; every result is joined where it used to be compiled, so `modules` order and every object byte are unchanged (18/18 `.text` identical) | serial fixed-module tail 2.44ms mean (1.3-5.0ms/program); the original unbounded implementation measured B/A 0.989, 0.978 (pre-batch spawn), **0.974** (first-reference spawn), interleaved n=15 against serial; bounded-executor validation is correctness/resource evidence, not a new timing claim; kill switch `TCG_NO_HELPER_OVERLAP=1` |
| merge validates merged-first | `merge_modules` ran the full trust-ir validation on every input AND the merged module (N+1 deep passes through the global pool); validation is pure and only decides Ok/Err, so the merged module is validated first and the inputs only when it fails — outcome-identical (case table in the doc comment) | B/A 0.994 (n=15, at the ±1% floor); row 1.046x -> 1.025x vs -O2 includes drift |
| MEASURED OUT (2026-08-26 evening, each an interleaved n=15 A/B on identical `.text`): build reconstructed obligations once (enumeration hands pairs to the walk) B/A 1.014 — the enumeration's rebuild is 0.01ms and the bookkeeping cost more than the 0.3ms it saved; a fan-out cap for fixed-module sweeps (threads/4) B/A 1.007, 1.022 — the capped helper becomes the join's critical path; skipping the adapter's repeat validation of the merge-validated CGU — the main CGU's adapter phase is 0.3ms, neutral; a 2-worker certificate walk pool B/A 1.001; EARLY PRE-WARM after isel (start each function's sweeps before opt+regalloc) B/A 1.007 / 1.013 / 1.010 / 1.003 uncapped and capped at 4 and 2 — it cuts the walk's wait (`TCG_TIME_WALK=1` `TCG_TIME_CERTS` lines: p7 proof_certs 3.7 -> 2.5ms) but contends with `prepare_function` (b1 5.2 -> 11ms) | none kept |
| `TCG_TIME_WALK=1` (diagnostic; prints per-function `TCG_TIME_CERTS fn=... walk= dataflow_integrity= certs_build=` lines) | per-function split of the certificate phase: the walk loop is ~0.3ms of p7's 3.8ms `proof_certs`, ~2ms of v3's 7ms; the rest is the walk waiting on memo cells whose sweeps are in flight — the residual proof cost is sweep CPU on the critical path, not walk CPU | — |

Harness (n=3, headline-eligible rows): warm compile vs -O2 **1.997x -> 1.161x
-> 1.10x -> 1.081x -> 1.093x -> 1.062x -> 1.057x -> 1.056x -> 1.046x -> 1.025x ->
1.003x -> 1.050x -> 1.034x -> 1.013x -> 1.032x -> 0.971x**
(2026-08-26 evening/night: carry-out C flag / dead-NZCV DCE / fixed modules off the
critical path / merge-first / the opt no-change-path stack; vs -O3 1.075x -> 1.060x
-> 1.049x -> 1.032x -> 1.033x -> 1.027x -> 1.034x -> 0.991x -> 1.009x -> 1.009x -> 0.998x
-> 1.003x -> 0.974x; the last six rows are CODE-IDENTICAL builds — that spread is
the harness's between-run scatter, and the 0.971x/0.974x row (`d3f11e8c`, every
evaluated gate passing) is a favourable draw at the line, not a robust margin;
the harness's own n=3 rows scatter ±3%, so read the trend, not one row). Within ONE
interleaved n=25 run the resolution is ±1% (an identical-dylib control reads
0.995-1.009 on the 18-way geomean), and between runs the same dylib drifts
1.037-1.088, so nothing under ~2% can be claimed from wall here. The
proofs-OFF floor under the gate's definition is **0.981x**, so the gate IS
reachable by proof work — what remains is ~7-8ms of proof wall per compile: ~4-8ms inside `compile_module` (pre-warm 1-8ms, now
CPU-bound across 20 cores, plus the certificate walk 1-5ms on the bridge's
one-worker verifier pool) and ~3ms outside it that this box cannot attribute
further (the backend as a whole is 21-47ms of a 117-148ms compile; `perf` is
unavailable, and the after-join segment's own noise is ±5ms). Measured NON-levers:
widening the certificate walk's pool (4 workers: p7_sieve +8%), the cache/store
tiers (no wall), narrower sweep pools, spawning each function's sweeps as soon
as it is prepared (oversubscribes the cores against `prepare_function`;
neutral-to-negative over three n=15 runs), and nicing the sweep workers (the
other pools' idle rayon workers spin at normal priority and starve them: -5%). Per-program wall noise here is ±6% at
n=25 even for identical dylibs, so only the 18-program geomean at n>=7 resolves
2-3% effects.

The owner's decisions (2026-08-26): `DEFAULT_SAMPLE_COUNT` stays at 100,000 —
the assurance is the product, and the compile-time gate is not to be met by
weakening it; the init-time speculative sweep stays on the invariant kinds —
no CPU spent on kinds a program does not use. With those fixed, the two G2
gates remain unmet on this box by design, and the remaining routes are OWNER
decisions rather than engineering ones: `DEFAULT_SAMPLE_COUNT`, a cross-process verdict cache (deliberately
excluded — an attacker-writable verdict file must never establish proof
authority), or baking registry verdicts in at build time (which changes what
"verified at compile time" means).

## Certificate precision: what each CMP / B.cond actually cites (2026-08-26)

The certificate walk credits an instruction by a query FRAGMENT: `"cmp"`
resolves to the first `Icmp_*` proof in registry order, so every CMP in every
program cited `Icmp_Eq_I32 -> CMP+CSET_EQ` whatever its width and whatever
condition its consumer read, and every `B.cond` cited `CondBr_Eq_I32`. The
verdicts were never wrong (every family member is Valid), but the certificate
named a proof that is not this instruction's lowering. Pinned by the golden
test `walk_query_resolution_golden::every_literal_query_resolves_as_pinned`
(`crates/trust-cg-verify/tests/fixtures/walk_query_resolution.txt`: 99 literal
queries, 38 ambiguous).

**`TCG_PRECISE_CITATIONS=1`** (opt-in; `TCG_TRACE_CITATIONS=1` prints one line
per site) refines the two families at the walk: a CMP cites `Icmp_<cc>_I<w>`
from its compared register's width and the single condition its NZCV
consumers read (CSET/CSEL/CSINC/CSINV/CSNEG/B.cond, scanned to where the flags
die); a `B.cond` cites `CondBr_<cc>_I<w>` from its own condition and the width
of the CMP that produced the flags. Anything undeterminable keeps the fragment.

Turning the trace on over the 18-program corpus found the real gap: **388 of
744 sites were `HS` (unsigned >=) — the bounds-check shape — and the registry
had NO `Icmp_UGE` / `CondBr_UGE` proof.** The four constructors existed and
were unit-tested Valid, but retraction #62 (group b) had removed them from the
registry as degenerate: the NZCV model spelled the C flag as `bvuge(Rn, Rm)`,
so `Icmp_UGE -> CMP+CSET_HS` was the tautology `X == X`. The fix is in the
model, not the registry list: `nzcv.rs` now derives C the way the ARM ARM
does — the carry-out of `AddWithCarry(Rn, NOT Rm, 1)`, written as the
full-adder carry-out identity at the MSB, entirely at the operand width (so the
tapes stay on the u64 lane path). `C == (Rn >=_u Rm)` is then a theorem every
unsigned comparison/branch proof establishes (`nzcv::tests` checks it
exhaustively at 8 bits and at the 32/64-bit edges; `lowering_proof::tests::
uge_proofs_are_no_longer_degenerate` pins that the machine side never spells
`bvuge`/`bvult` and that the four proofs are registered). Registry: 1907 ->
1911 proofs; the golden's only change is `cmp`/`condbr` matching 20 instead of
18 members, still resolving to `Eq`.

| | flag off (default) | flag on |
| --- | --- | --- |
| corpus sites refined / kept fragment | 0 / 744 | **714 / 30** |
| `.text` | identical 18/18 | identical 18/18 |
| kinds swept per compile | unchanged | up to +10 (`Icmp_*`/`CondBr_*` members actually cited), 21-23 ops each, ~0.5-1ms of pool CPU per kind |

The remaining fragment credits were 22, all in h1-h4: 20 CMPs with no NZCV
consumer in their block and 2 `B.cond` fed by `TST`. The 20 were DEAD flag
writes — `cmp x20, x5` (x5 = isize::MAX/8, a folded capacity check) whose
flags the very next CMP overwrote, sitting in the scalar sum loop (1 of its 6
instructions). DCE kept them because CMP carries `HAS_SIDE_EFFECTS`. Certified
DCE now removes a def-less NZCV writer whose flags die unread: overwritten by
the next NZCV writer in the same block, or carried by a non-flag-reading
terminator (B, CBZ/CBNZ, TBZ/TBNZ, RET — NZCV is caller-saved) into successors
on which NZCV is dead on entry (every path reaches a writer or the function's
exit before any reader; cycle-safe, 64-block budget, the same rule the
verifier's own `nzcv_dead_on_entry` uses). Calls are neutral — a callee cannot
rely on incoming NZCV under AAPCS64, but a reader after the call on the same
path still counts. Certificate: `DceContract::DeadNzcvWriteUnobservable`,
instance `dce:nzcv:dead-write:v1`, facts = the overwriting instruction or the
list of successor blocks proven dead-on-entry, re-checked locally;
`TCG_TRACE_DEADFLAGS=1` prints why a cross-block scan said "live". h1 `main`:
13 -> 11 CMPs, the loop is `ldr; add; add; cmp; b.cc`; `.text` changes on
h1-h4 only, outputs identical 18/18. Compile-time cost of the DCE slice: the
first version walked the CFG per CMP per DCE wave and read B/A 1.027 in an
interleaved n=15 A/B (p4_matmul +11ms user CPU) — the 1.057 -> 1.085 harness
move was that, not drift; the once-per-wave block-level NZCV liveness that
replaced it reads B/A 1.01 (identical code, 18/18). TST-fed branches now cite the TST
obligation for their condition (`tst w64: ne`, CmpCombine), so with the flag on
**every one of the corpus's 744 CMP / B.cond sites cites its own proof** (0
fragment credits). Whether the refined citation becomes the default is the
owner's call — it changes the certificate's `rule_name` and adds the cited
kinds' sweeps to a compile that uses them, never the verdict or the code.

## Tools (`tools/`)

Scripts used for every measurement in this document (all take the dylib
path; `TCG_PROGS` overrides the corpus directory):
`ident.py A B` (`.text` sha256 identity over the corpus — the gate for every
change), `ab.py` (paired interleaved LLVM/A/B compile-wall A/B; always run an
identical-dylib control), `pass_times.py N A B [pass..]` (per-pass corpus
time from `TRUST_CG_TIME_PASSES`), `ra_stages_all.py N A [B]` (regalloc /
validator / post-RA / adapter stage timers), `timepasses.py N DYLIB PROG`
(rustc `-Z time-passes`, LLVM vs bridge), `fixed_charge.py N DYLIB` (empty
`main` fixed per-process cost), `fixpoint_scan.py DYLIB` — the
convergence scan that found the vectorizer remainder re-fire class — and
`harness_row.sh [REPO] [DYLIB]`, the one-row evidence runner (`run.py --cold`
plus gate check and ratchet stamp; one row per landed change, never re-run to
fish). `python3 tools/test_harness_row.py` adversarially proves that failed or
result-less runs cannot select and ratchet an older JSON result.
