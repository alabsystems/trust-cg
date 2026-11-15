# Size and memory accounting on Darwin arm64: emitted-code size, median-of-N peak RSS, and a lower compiler peak (L14-P10)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Ledger row `L14-P10`: "Size and compile/runtime memory accounting are not defined or
resolved per the contract." This records the three changes that address it and the
measurements behind them. Host: Apple M4 Max (`Mac16,5`, 12 performance and 4
efficiency cores), macOS 26.6.2, the shared development machine. Driver: Trust
package 9192 (`trustc` `321aaeda7`, explicit unverified frontend lane
`-Ztrust-verify=off`). Every number is a measurement, not a proof.

**The host was loaded.** Other agents kept the 1-minute load between about 6 and 15
during this work (the harness threshold is 8.0 on 16 CPUs), so both harness runs are
stamped `LOADED`. The metrics reported here were chosen to be robust to load: byte
counts, the peak resident set (the kernel's high-water mark, not a rate), and
instructions retired. Wall-clock compile and runtime ratios from the same runs are
listed but not claimed. Memory figures are MiB (2^20 bytes) throughout, including
where a tool's output says "MB".

## Summary

| What | Before | After |
| --- | --- | --- |
| Size measure | linked file `st_size`, shared std included: 1.00060x LLVM `-O3` | emitted-code size from the linker map: **1.147x** LLVM `-O3` (linked file still 1.00060x) |
| Peak RSS | one dedicated sample per lane | median of 5 interleaved samples per lane, all retained; R1 band `max(5%, 2 x spread)`, a spread above 0.25 unresolved |
| Compiler peak RSS, corpus geomean (no-proof-certs) | 1.188x LLVM `-O2` | **1.109x** LLVM `-O2` |
| Compiler peak RSS, `scale_gate.py` `large` (800 functions) | 298.1 MiB (1.48x LLVM `-O2`) | 240.8 MiB (1.20x) |
| Compiler peak RSS, `scale_gate.py` `xlarge` (2,400 functions) | 541.0 MiB (1.45x) | 422.7 MiB (1.13x) |
| Emitted bytes | — | identical: every object and the linked image's sections, 18 corpus programs and 4 scale crates |
| Compile instructions retired (`p1`, `h1`, `large`) | 4.755G, 4.855G, 26.60G | 4.723G, 4.807G, 26.56G |

The production lane (certificates on) still compiles none of the corpus on this host
(`[TCG-PROOF-465]`, ledger `L07-P2`), so every ratio above comes from the
`no-proof-certs` diagnostic lane, which is never evidence and is refused by the
ledger ratchet. No ledger row was appended.

## 1. Emitted-code size

`benchmarks/beat-llvm/emitted_size.py` defines it: the bytes of the **linked**
executable that the system linker places from object files **the compile produced**,
counted in **code** sections (`__TEXT,__text`, `.text*`) and **read-only data**
sections (`__TEXT` constants and literals, `__DATA_CONST,__const`, `.rodata*`,
`.data.rel.ro*`), after dead stripping.

- "Produced by the compile" means a relocatable object inside the compile's own
  fresh, private output directory: rustc's codegen-unit objects and the allocator
  shim, written by the backend under test, including the standard-library generics
  the crate instantiates. Sysroot `.rlib` members (`std`, `core`, `alloc`,
  `compiler_builtins`, ...), system startup objects, dylibs and text stubs, and
  linker-synthesized atoms (stubs, GOT, compact unwind) are not the program's.
- The attribution is the linker's own map (`ld -map` on Darwin, GNU `ld -Map` on
  Linux), never a guess from symbol names. The map comes from a second link of the
  same compile (`-C link-arg=-Wl,-map,<file>`), and `run.py` refuses the reading
  unless that image's section bytes equal the timed binary's
  (`emitted_size.image_digest` ignores only load commands, `__LINKEDIT` and the ELF
  build ID; `LC_UUID` differs between two links of the same code).
- Writable data, zero fill and unwind tables are recorded per class
  (`emitted_size` in the results JSON) but not counted: Darwin's compact unwind table
  is linker-synthesized and cannot be attributed per object.
- An unsupported map format, an unreadable map or a map that attributes no byte to
  the program is a missing reading (never zero), which nulls the aggregate and makes
  the row ineligible.

Gates S3 (emitted-code geomean at most 1.10x LLVM `-O3`) and S4 (at most 1.00x) are
preregistered in `contract/gates.json` version 3; S1/S2 keep the linked size. On
this corpus the new measure resolves what the old one could not: linked file sizes
differ by 0.2-0.3% (`p7_sieve` -3.2%), emitted code by -87% to +100%.

## 2. Median-of-N peak RSS

Program and compiler peak RSS are the exact median of `--n-rss` dedicated samples per
lane (contract N = 5, odd so the median is itself a reading), interleaved lane by
lane outside the timed loops, every sample retained with the sampler's status in
`rss_samples`. A lane with any failed sample has no reading; the median of the
survivors is never used. `check_gates.py` recomputes every median from the samples
and refuses a stamped reading that disagrees. R1's parity band for a program is the
contract's runtime rule, `max(5%, 2 x relative spread)`, the spread being
`(max - min) / median` of the lane with the larger spread. A range moves with one
outlier sample that the median ignores (bridge samples 90, 90, 90, 90 and 180 MiB
against 50 MiB have a +80% median and a 3x band), so a comparison whose spread
exceeds 0.25, the runtime lane's resolvability cap, is unresolved: a median beyond
its band is still a loss, but a noisy comparison never counts as parity, and R1 then
reads unmeasured. Evidence needs N >= 5 in provenance and in every retained lane of a
MATCH row; a run with no MATCH row (the production lane on this host) has no reading
and is held to the provenance N only. In these runs the largest relative spread was
0.028 (program) and 0.043 (compiler), so the cap changes no verdict recorded here.

The ledger row gains `ledger_row_schema` 2, `n_rss`, the emitted-size aggregates and
the RSS spreads. Older rows stay readable (`--check-ledger`, `--render`), and rows of
gates.json version 2 or earlier are not baselines for the redefined metrics (no such
row had a non-null RSS value).

## 3. What the compiler's peak RSS was made of

Method (all on `h1_vec_push_sum` or `p1_xorshift`, `no-proof-certs`, through the
harness's own sampler, `commands/pm.py`): the process's RSS over time
(`commands/rss_trace.py`, `proc_pid_rusage` every 0.3 ms), `vmmap` of the process at
breakpoints (`commands/vmmap_two.py`, `commands/vmdiff.py`, which excludes the dyld
shared cache that `ru_maxrss` does not count), per-phase RSS probes compiled into a
throwaway backend build, backtraces at `mmap` and at rustc's def-path printer after a
given lowering (`commands/bt_after.py`), and one-shot breakpoints on every backend
function (`commands/exec_funcs2.py`).

Only some of the numbers in this section and the next have a retained log (`logs/`):
the executed-function list, the instructions retired, the scale-crate RSS and the
identity checks. The others come from attribution runs whose output was not kept:
the `lang_start` step, every `vmmap` page count (the load-and-bind breakdown and the
resident-text figures included), the 23 to 32 MB fall after `codegen_crate`, the
`large` crate's 303.8 and 247.8 MB, the table of which change buys what, and the
refuted candidates' medians. Treat them as indicative. The evidence
review reproduced the combined effect independently at `a2216b002`
(`logs/review-rss-ab.txt`), but not the split between the
two changes.

Before the change, for `p1_xorshift` (median of 3, MiB, load 5.9; `commands/decomp.sh`;
the evidence review reproduced the `--emit=metadata` row as 113.6 and 119.3 MiB, median
of 5, also without a retained log):

| | LLVM `-O2` | bridge |
| --- | ---: | ---: |
| `--emit=metadata` (front end only; the bridge lane also loads the backend) | 113.6 | 119.5 |
| full compile | 135.7 | 162.2 |

The bridge's 26.5 MiB excess over LLVM `-O2` came from the following.

- **The last function lowered, `std::rt::lang_start::<()>`, raised the resident set by
  10.4 MB** (4.8 MB of it heap). Lowering its `&dyn Fn() -> i32 + Sync +
  RefUnwindSafe` capture made two eager `{:?}` renderings of rustc types: the
  fat-pointer refusal string of `scalar_leaf_trust_ir_fields` (which
  `compute_memory_backed_locals` probes with `.is_ok()` and discards) and the site
  string `emit_vtable_global_at_depth` built for every vtable method. The first such
  rendering runs rustc's visible-path printer, whose first use computes
  `visible_parent_map`, a sweep of every crate's `module_children`: `vmmap` shows
  +3.7 MB of `libcore.rmeta`, +1.0 MB of `libstd.rmeta`, +0.7 MB of
  `liballoc.rmeta` and +4.8 MB of heap across that one lowering. `rust_ty_to_trust_ir_ty`
  had already been wrapped against exactly this; these two sites had not.
- **The object compile ran on top of the type context.** The batched per-CGU compile
  ran inside `codegen_crate`, while rustc's query arenas and the `.rmeta` pages that
  lowering touched were still resident. rustc drops them right after `codegen_crate`
  returns, and the process's RSS then falls by 23 to 32 MB on the corpus programs.
  There the compile itself adds only about 2 MB, but on larger crates its heap
  stacks on the arenas: `scale_gate.py` `large`
  peaked at 303.8 MB, and 247.8 MB with only the deferral below (attribution run,
  section 4).
- **Loading the backend costs about 6 MB** (the `--emit=metadata` row): dyld binding
  the backend's 796 undefined symbols touches 2.8 MB more of `librustc_driver`'s
  export trie (`__LINKEDIT`), plus 1.2 MB of the backend's own `__LINKEDIT` and 0.7 MB of fixed-up
  `__DATA_CONST`.
- **Code working set (not isolated).** Compiling `p1_xorshift` executes 3,927 backend
  functions totalling 5.5 MB of machine code (`logs/exec-functions-p1.tsv.gz`),
  spread over about 16.5 MB of resident backend text pages; the LLVM lane touches
  about 17 MB more of `librustc_driver`'s text, so text is roughly even at exit, but
  the bridge's pages become resident while the metadata is still mapped. No
  measurement here isolates how much of the remaining excess this accounts for.
- **Refuted candidates** (attribution runs with diagnostic knobs, never evidence;
  medians of 3 against the default's 161.9 MB unless noted): jemalloc retention
  (`_RJEM_MALLOC_CONF=dirty_decay_ms:0`, single runs: -3.7 MB bridge, -2.2 MB LLVM),
  thread fan-out (`max-parallelism=1`: -0.4 MB; `batch-parallel=0`: +0.1 MB), the
  solver refinement lane (`refine-solver=0`: -1.2 MB), `no-helper-overlap`
  (-0.4 MB), `no-identity-warm` (-0.1 MB). The embedded verdict database and
  canary certificates are not paged in: the backend's whole `__TEXT` segment is
  16.5 MB resident at exit, against 43 MB of `__TEXT,__const` in the file.

## 4. The changes (commit `f87c5959e`)

- The object compile of the lowered trust-ir, its per-function fallback and the
  decisions after it (deferred-unlowerable resolution, failed roots,
  `[TCG-LINK-UNDEF]`, entry wrapper, allocator shim, helpers) run in `join_codegen`
  (`OngoingCodegen::finish`), after rustc has dropped the type context. Everything
  the tail read from `TyCtxt` is captured before `codegen_crate` returns:
  `CompileCtx` (compile environment and `OutputFilenames`), the batch target info,
  each pending function's `FailureRoute` (the instance-dependent half of
  `handle_failed_fn_object`'s decision tree, split from the error-dependent half),
  and the crate's mono symbols and v0 tag. A helper first referenced after the plan
  is taken cannot occur (helpers are registered only by MIR lowering) and now fails
  closed by name if it ever did.
- The vtable site string is built only for a refusal (text unchanged), and
  `scalar_leaf_trust_ir_fields` renders under `with_no_visible_paths!`. That does
  change text: a surfaced scalar-leaf refusal that embeds a type now names the
  defining crate's path (`core::…` or `alloc::…` where it said `std::…`), as
  `rust_ty_to_trust_ir_ty`'s refusals already did. The classifiers on this path
  decide by layout, not by path strings, and no emitted byte depends on the text.
- A committed test pins the captured route (fix round 1, `da3ceaf97`):
  `unsupported_program::no_mangle_roots_are_never_dropped_when_their_object_compile_fails`
  compiles two `#[no_mangle]` exports whose object emission this host refuses
  (`[TCG-PROOF-465]`) and requires each to be a named failed root, never a
  skipped-internal record, and every export of a successful compile to be defined.
  It passes at this branch; with every deferred route mutated to the
  std-internal drop it fails (`logs/route-test-mutation.txt`).

Which change buys what (an earlier attribution run with intermediate backend builds,
median of 3, MiB; its log was not retained): on the `large` scale crate, baseline
303.8, visible-path fixes only 293.8, deferral only 247.8, both 241.2; on
`h1_vec_push_sum`, baseline 168.0, fixes only 157.9, both 155.5. The fixes remove a
fixed 10-12 MB per compile that prints a `dyn` type; the deferral's gain grows with
the crate.

## 5. Emitted bytes are unchanged

`commands/identity.py` compiles every input with the baseline and the candidate
backend and compares every object the compile wrote (`-C save-temps`) and the linked
image's section digest in the `no-proof-certs` lane, and the complete stderr (temp
paths normalized) in the production lane, where every program is refused:
`logs/identity-corpus.txt` (18 programs) and
`logs/identity-scale.txt` (4 crates), 0 differences. On
these inputs the refusals, including the `lang_start` route now taken in
`join_codegen`, are byte-identical text; none of them surfaces a scalar-leaf refusal
that embeds a type, whose text did change (section 4).

Bridge fixtures at `f87c5959e`, before the merges of `main` (`targo --unverified test
--release`, the eight Darwin bridge-gate targets run directly,
`logs/bridge-targets.txt`): seven pass (13 tests);
`real_program_corpus_a64_compile_gate` fails with 0 of 26 rows compiled, all
`[TCG-PROOF-465]`, and the same test binary run against the baseline backend fails
identically with identical per-row verdicts.

After merging `main` (fix round 1, HEAD `7904b1ee8`, load 8.4 to 16.0,
`logs/bridge-targets-merged.txt`), six of the eight
targets pass (10 tests). `fixed_cost_budget_aarch64::a_trivial_compile_stays_within_its_fixed_cost_budget`
now fails too: its cold certificates-on compile is refused (`[TCG-PROOF-465]`, three
uncovered opcodes). `real_program_corpus_a64` still compiles 0 of 26 rows.
`unsupported_program` passes 8 of 13, including the new route test; its five
"must now COMPILE" rows are refused on this host. Run against the backend built from
`main` `272ab14c9`'s bridge sources (the same test binaries,
`logs/bridge-targets-main-backend.txt`), every
one of these fails the same way: the fixed-cost test with the same refusal, the corpus
with the same 26 per-row verdicts, and `unsupported_program` with the same five tests.
The new failure comes from `main`, not from this branch.

A second merge of `main` made `unsupported_program` a required target of the Darwin
bridge runner (`L06-P10`), so the route test now prints its positive-evidence marker
(an expected refusal today, a compile once both roots compile) and the runner counts
13 tests there, 81 in all. The runner itself, run at `4796025fe` from a clean tree
with a scoped rustup home as its own record did
(`logs/bridge-runner-summary.txt`, load 5.9 to 7.5),
fails as that record does: 6 of 13 targets pass, 30 of 81 tests are credited (the
record at `ae3f0c539`: 29 of 80), the route test is credited as an expected refusal
with certificates on, and the 51 failing tests are the record's, test by test.

At `f87c5959e` the gate runner
`scripts/check_darwin_aarch64_bridge.py` itself refused this host before building
(`DARWIN_BRIDGE_TRUST_TOOLCHAINS_DIVERGENT`: the rustup `trust` link names
`~/.trust-tc-recon`, not the package; `logs/bridge-gate-refusal.log`).

The bridge's library unit tests (`--lib`, release): 471 pass, 23 fail
(`logs/bridge-lib-test-failures.txt`), all in code
the change does not touch: 21 `mem_refine` tests whose AY verdict comes back
`Inconclusive (incomplete self-check-rejected)`,
`abi_reg_lanes::tests::a_three_value_x86_64_return_exhausts_the_integer_file`, and
`tests::fat_pointer_leaf_predicates_match_rustc_layout`, whose `&Dst` row expects the
kind predicate to answer `false` although `slice_tail::is_pointer` (`56b557ea4`, on
the base) answers `true`. After the merge of `main` (`7904b1ee8`) the same 471 pass
and the same 23 fail, and the evidence review's run of the merge-base backend failed
the same 23 (`logs/bridge-lib-test-failures-merged.txt`).

## 6. The corpus, before and after

Both runs used the same harness (`benchmarks/beat-llvm/run.py` at `f87c5959e2bc`, the
gates.json version 3 definitions), `--bridge-cg-arg no-proof-certs --allow-loaded`, the
contract N (3 compiles, 5 runs, 5 RSS samples) and the same driver. "Before" loaded
the backend built from `main` `7a713cf6f`'s bridge sources (sha256 `ba9abd2549b1…`,
`--allow-stale-dylib` because the sources had moved on); "after" loaded the backend
built at `f87c5959e` (`18cea93e5d68…`). Records: [`before/`](before/README.md) (load
9.92 to 11.16) and [`after/`](after/README.md) (load 9.96 to 15.37), each with its
results JSON, raw samples and hashed inventory.

| program | emitted B LLVM -O3 | emitted B bridge | emitted x | linked x | compiler RSS MiB LLVM -O2 | bridge before | bridge after | x -O2 before | x -O2 after | program RSS x |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| b1_mispredict | 564 | 1128 | 2.000 | 1.00286 | 137.1 | 164.6 | 153.3 | 1.198 | 1.118 | 1.000 |
| h1_vec_push_sum | 936 | 860 | 0.919 | 1.00203 | 141.5 | 167.9 | 155.9 | 1.150 | 1.102 | 1.000 |
| h2_vec_grow | 940 | 884 | 0.940 | 1.00193 | 141.6 | 168.7 | 156.0 | 1.158 | 1.102 | 1.000 |
| h3_box_leak | 956 | 788 | 0.824 | 1.00190 | 142.0 | 168.6 | 156.5 | 1.185 | 1.102 | 1.000 |
| h4_vec_dropper | 1412 | 844 | 0.598 | 1.00200 | 141.9 | 168.4 | 156.5 | 1.186 | 1.103 | 1.000 |
| m1_call_chain | 396 | 560 | 1.414 | 1.00269 | 136.6 | 163.0 | 151.6 | 1.186 | 1.110 | 0.989 |
| m2_call_heavy | 424 | 564 | 1.330 | 1.00248 | 135.4 | 162.2 | 150.7 | 1.189 | 1.112 | 1.000 |
| p1_xorshift | 488 | 540 | 1.107 | 1.00266 | 135.8 | 162.1 | 150.7 | 1.196 | 1.110 | 1.011 |
| p2_collatz | 384 | 556 | 1.448 | 1.00262 | 135.4 | 162.0 | 150.7 | 1.193 | 1.113 | 1.000 |
| p3_gcd | 436 | 648 | 1.486 | 1.00255 | 136.6 | 162.2 | 150.7 | 1.183 | 1.104 | 1.000 |
| p4_matmul | 984 | 1748 | 1.776 | 1.00276 | 137.5 | 165.8 | 153.8 | 1.200 | 1.119 | 1.011 |
| p5_struct_acc | 400 | 560 | 1.400 | 1.00273 | 137.5 | 164.4 | 152.4 | 1.197 | 1.108 | 1.000 |
| p6_branch_match | 524 | 716 | 1.366 | 1.00279 | 137.5 | 164.6 | 152.1 | 1.195 | 1.106 | 1.000 |
| p7_sieve | 9248 | 1160 | 0.125 | 0.96825 | 136.4 | 163.8 | 152.2 | 1.195 | 1.116 | 0.990 |
| p8_closure_nest | 396 | 576 | 1.455 | 1.00279 | 136.3 | 163.0 | 151.5 | 1.192 | 1.112 | 1.000 |
| v1_saxpy | 656 | 1012 | 1.543 | 1.00273 | 137.6 | 164.6 | 153.2 | 1.196 | 1.113 | 1.000 |
| v2_memfill | 420 | 780 | 1.857 | 1.00273 | 137.6 | 163.5 | 152.8 | 1.190 | 1.110 | 0.989 |
| v3_popcount | 568 | 996 | 1.754 | 1.00283 | 138.7 | 164.4 | 152.9 | 1.197 | 1.102 | 0.989 |
| **geomean** | | | **1.1474** | 1.00060 | | | | **1.1880** | **1.1090** | 0.9988 |

"x -O2 before" divides by the before run's own LLVM `-O2` median, "x -O2 after" by the
after run's (the column shown). Emitted bytes and linked sizes are from the after run
and equal the before run's.

Emitted-code size is the same number of bytes before and after for every program
(the backend change emits the same code). The runtime geomeans of the two runs
(0.903x and 0.961x LLVM `-O3`) and warm-compile geomeans (1.338x and 1.262x `-O2`)
differ although the binaries are byte-identical: the host was loaded, so neither is
a result. Instructions retired, which load does not move, are in
`logs/instructions-retired.txt`: the candidate
compiles `p1_xorshift`, `h1_vec_push_sum` and the `large` crate in 0.2-1.0% fewer
instructions.

Scale crates (`scale_gate.py`'s generated sources; compiler peak RSS, median of 3,
MiB; bridge at `-Copt-level=3` with `no-proof-certs`, the two backends and LLVM run
back to back; `logs/scale-rss.txt`, load 12.5 to 13.8):

| crate | functions | LLVM `-O2` | bridge before | bridge after | x `-O2` before | x `-O2` after | change |
|---|---:|---:|---:|---:|---:|---:|---:|
| `small` | 25 | 137.3 | 168.1 | 153.1 | 1.225 | 1.115 | -15.0 MiB (-8.9%) |
| `medium` | 200 | 147.3 | 200.8 | 166.4 | 1.363 | 1.130 | -34.3 MiB (-17.1%) |
| `large` | 800 | 200.9 | 298.1 | 240.8 | 1.484 | 1.198 | -57.4 MiB (-19.2%) |
| `xlarge` | 2,400 | 373.1 | 541.0 | 422.7 | 1.450 | 1.133 | -118.3 MiB (-21.9%) |

## What remains

Compiler peak RSS is still 1.11x LLVM `-O2` on the corpus, about 15 MiB on
`p1_xorshift`. About 6 MiB of that is the backend's load and binding (the
`--emit=metadata` row); the rest is not isolated by any measurement here. The
backend's code working set is the leading candidate, not a measured share. A linker
order file that packs the executed functions would test that and shrink it, but it is
not done:
v0 symbol names carry per-build crate disambiguators, so a committed order file goes
stale at the next version bump and would have to be generated at build time. R2
(compiler RSS at most 1.00x `-O2`) is still unmet, and nothing here is evidence
until the production lane compiles the corpus (`L07-P2`).

The GNU `ld -Map` reader is tested only on a synthetic map and has not yet run on a
Linux host.

## Files

- `before/`, `after/`: the harness's retained records (`run.py --retain-dir`).
- `logs/`: identity checks, bridge fixture and unit-test results (with the
  real-program corpus's per-row verdicts for both backends; after the merge of
  `main`, for the merged backend and `main`'s), the Darwin bridge runner's
  verdict, the route test against a mutated backend, the evidence review's RSS
  reproduction, scale RSS, instructions
  retired, the before/after table, the executed-function list for `p1_xorshift`,
  and the gate runner's refusal.
- `commands/`: the scripts used. They name this session's scratch paths; adjust
  them to rerun.
