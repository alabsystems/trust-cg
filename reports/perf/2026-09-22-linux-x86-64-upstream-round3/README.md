# Linux x86-64: round 3 — `origin/main`'s three x86-64 lanes become the base (2026-09-22)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`origin/main` moved 15 commits further while this branch carried its Linux
x86-64 completion wave, and **three of them reimplement lanes this branch
already had**:

| upstream commit | lane | what this branch had |
| --- | --- | --- |
| `e449ee87d` | the two-value `PassMode::Pair` **argument** lane (`[TCG-ARG-ABI]` 74 → 2) | `902c69b18` + `04b1050bb`: `scalar_pair_param_plans` and the `lower_call_arg_for_input` per-argument marshaller |
| `92025e14b` | tuple pointee with a nested struct/array field (`[TCG-POINTEE-LANES]` 21 → 11) | **nothing** — no commit on this branch touches that region |
| `b04d8bd07` | union with a fat-pointer leaf (`ManuallyDrop<Part>` 21 → 0) | **nothing** — same |

Upstream's Darwin `core` census reads **127** failed roots; this branch's last
Linux census read **183**. Upstream is ahead on these lanes, so upstream's
implementations are the base and the duplicate is deleted.

The 127 is a DARWIN number and does not compare directly to a Linux one, so
this round built `origin/main` on its own in a detached worktree and censused
it on THIS host: **`origin/main` alone reads 152 here**, and the merged tree
reads 152 as well — symbol for symbol, 0 roots added, 0 removed, 0 reasons
moved. That identity, not the totals, is the round's result.

Merge commit: `d4ceec6b4`. Everything below was produced from the merged
tree with a clean working tree, and every artifact it cites is retained beside
this file. Rounds 1 and 2 are retained at
[`2026-09-22-linux-x86-64-upstream-merge`](../2026-09-22-linux-x86-64-upstream-merge/README.md)
and
[`2026-09-22-linux-x86-64-upstream-round2`](../2026-09-22-linux-x86-64-upstream-round2/README.md).

Host: `x86_64-unknown-linux-gnu`, Ryzen 9 9900X3D, 24 cores, 61 GiB, GCC 15.2.0.
Root workspace built with the pinned stock Rust 1.97.1 (`rust-toolchain.toml`;
the project's own pin overrides this machine's Trust default toolchain). Bridge
built with the tree-built stage2 `trustc` (`rustc 1.99.0-dev (3a3e781fe
2026-09-14)`) through `targo --unverified build --release --locked`. Backend SHA-256 in `census/backend.sha256` (the bridge dylib is not
byte-reproducible on this host — measured in `1d0364f8d` — so the hash
identifies the run, not the source). Every build and test ran under the memory
guard (`CARGO_BUILD_JOBS=3`, one of two flock slots, `MemoryMax=22G`); another
agent was building in `trust-cg-wt-ptr` throughout.

This is a regression and refusal measurement in the explicit unverified frontend
lane. It is not a proof claim, and it does not establish compiler completion or
release readiness.

## The duplicate that had to be decided: the `PassMode::Pair` ARGUMENT lane

Only ONE of upstream's three lanes was actually duplicated. The tuple pointee
(`92025e14b`) and the fat-leaf union (`b04d8bd07`) touch regions of
`crates/rustc-codegen-trust-cg/src/lib.rs` that **no commit on this branch
touches** — checked, not assumed:

```
git log --oneline b943790f0..0769dac85 -- crates/rustc-codegen-trust-cg/src/lib.rs
  68c3db0b5 merge: wave1/vectorize
  04b1050bb bridge: declare through extern_callee before reading a pair-argument plan …
  d307f7c66 bridge: forward the x86 vectorizer trace and fill-memset knobs
  902c69b18 feat(bridge): two-carrier PassMode::Pair arguments on x86-64 (XD-05)
```

so those two lanes arrive whole and unopposed.

### The two pair-argument implementations, side by side

| | this branch (`902c69b18` + `04b1050bb`) | upstream (`e449ee87d`) |
| --- | --- | --- |
| decision fn | `scalar_pair_param_plan` → cached `scalar_pair_params`, read by `scalar_pair_param_plans` | `scalar_pair_param_plan`, asked directly by all three consumers |
| how the hand-built lists were made consistent | a REFACTOR: every argument list routes through one per-argument marshaller `lower_call_arg_for_input`, closure calls included (`closure_body_call_args`, `emit_closure_call_n`) | a SCOPE RULE: the lane declines closure / coroutine-closure instances and `FnOnce::call_once` vtable parameter 0 by name, because those are the only hand-built lists for a rustc-declared Rust callee |
| scope gate | slices declined; `check_aggregate_abi_scope` + `check_param_abi_lanes` | additionally declines when `check_param_abi` already conforms, C-compatible ABIs, float-carrier pairs, `Sext` lanes |
| carriers | `scalar_pair_abi_plan` (the return side's) | `scalar_pair_abi_plan` (the same) |
| measured residual | `[TCG-ARG-ABI]` 74 → 2, both `Option<u128>` | `[TCG-ARG-ABI]` 74 → 2, both `Option<u128>` |
| cross-backend test | `m142_x86_scalar_pair_arg_xback`, 26 shapes | `m141_x86_scalar_pair_arg_xback`, 12 shapes |

**Decided by building both and diffing the root SET, not by reading.** The
pre-merge tree (round 2, this branch's lane) and the merged tree (upstream's
lane) were censused on the same host with the same stage2 `trustc`:

* `[TCG-ARG-ABI]` is **2 before and 2 after**, the same two `Option<u128>`
  symbols.
* **0 roots added** across the whole census. No `library/core` root that
  compiled under this branch's marshaller stops compiling under upstream's scope
  rule; in particular `core` contains no root of the closure-parameter shape
  that upstream declines by name, so that capability difference is invisible
  where the rule looks. It is NOT invisible in the differential — see the
  finding below.
* **0 reasons moved** on a shared root.

On the census — the comparison the rule names — neither implementation covers
a shape the other refuses, so **upstream's survives and this branch's is deleted
whole.** `lib.rs` is taken from `origin/main` verbatim and the only thing
re-applied on top is this branch's 22-line knob forward in
`install_knob_backed_library_settings` (below).

**It is not a clean tie OFF the census**, and that is recorded below rather than
smoothed over: `m142_x86_scalar_pair_arg_xback` — kept precisely so the lane is
measured against whichever implementation survives — now refuses 16 combinations
that this branch's lane compiled (a pair passed into a `Fn` / `FnOnce` closure).
See **FINDING** under *Bridge cross-backend lanes*.

### The placement gate: upstream's arm, with this branch's refusal kept inside it

`abi_reg_lanes::trust_cg_param_placement`'s x86-64 multi-value arm was
implemented on both sides. Upstream's per-value classification is the surviving
body and this branch's `x86_64_scalar_param_lanes` helper is deleted — but the
two are not equivalent: this branch's additionally REFUSED a declared value that
is not a BARE SCALAR (an `I128`, which takes a GPR pair; an aggregate, which is
classified by eightbytes), because "the next register of its class" — the rule
the arm states — does not describe such a value.

Taking upstream's body verbatim dropped that refusal. **A fail-closed refusal is
not something this merge trades away to take the other side's code**, so the
check is reinstated INSIDE upstream's loop (one mechanism, one extra guard) and
the unit test that pinned it,
`a_non_scalar_value_is_refused_in_the_multi_value_argument_arm_on_x86_64`, is
restored with it rather than deleted. The guard sits after
`x86_64_type_lanes`, so upstream's own MEMORY-class message and its test
(`a_memory_class_value_inside_a_multi_value_argument_is_refused_on_x86_64`) are
untouched. It costs no capability: the surviving `scalar_pair_param_plan`
declines 128-bit lanes and non-`ScalarPair` shapes by name before the gate is
asked, and the re-census after the change is symbol-identical.

Net result in this file, measured with `git diff 749731ce8 HEAD` (the upstream
tip actually merged — `origin/main` has since moved): **+264 lines, 0
deletions**, i.e. six unit tests, the one guard and this branch's earlier
return-side helpers, with no line of upstream's own body removed. Across the
whole bridge crate the delta to `749731ce8` is **+1,668 / −8** (corrected
2026-09-22 in round 4: this report first said +1,606, which no measurement
supports —
`git diff --shortstat 749731ce8 <rev> -- crates/rustc-codegen-trust-cg` reads
10 files, 1,668 insertions, 8 deletions at both `8159a9943` and `44facace6`),
and the eight deleted lines are all in test files this branch edited on purpose
(the portable backend lookup in two differentials, the page-boundary corpus
fixture).

## What only this branch has, and what the merge had to re-wire

* **The bridge knobs** (`crates/rustc-codegen-trust-cg/src/knobs.rs`:
  `trace-vectorize`, `trace-vectorize-dump`, `no-x86-fill-memset`) and their
  22-line forward in `install_knob_backed_library_settings`. Upstream's `lib.rs`
  does not have the forward, so taking upstream's file verbatim DELETED it; it
  is re-applied on top. This is load-bearing: `trustc` refuses the `TCG_*`
  environment spellings before the backend loads, so without the forward the
  floor target `m143_x86_vectorize_trace` — which asserts the exact
  `x86_vectorize::run_impl` accept lines and the manifest exit codes 111 / 60 /
  44 through `-Ztrust-ir-cg-args` — cannot express them at all.
* `crates/trust-cg-opt/src/x86_trap_block.rs` and all four users
  (`x86_bounds_check_elim`, `x86_branch_layout`, `x86_cmov_swap`,
  `x86_vectorize`) — verified present after the silent auto-merge of
  `x86_cmov_swap.rs`, which upstream's `511fc6bad` also touched.
* The saxpy-Q carrier-guard arms and the fill-tier memset route in
  `x86_vectorize.rs`. Upstream's `09dd766ef` quarantines a rewrite in
  `vectorize.rs` — a DIFFERENT file; there is no overlap.
* The NAMED `call_only_body` certificate as the CONJUNCTION of the verifier row
  dispositions and the LIR source shape, and its publication through
  `crates/trust-cg-cli/src/emit_proofs.rs`. Upstream's only `compiler.rs` commit
  in these 15 is `0b34081c3` (RISC-V ELF), so the auto-merge could not disturb
  it; checked by grep after the merge.
* `DECIDED_ABSENT` in both floor runners and the swiftcc lane; the Clean-fixture
  host-target loader; `ty_bfs_minimal`; the floor fixture repairs; the portable
  backend lookup in `fat_pointer_lane_differential.rs` and
  `virtual_call_aggregate_return_differential.rs`.
* Every retained report under `reports/perf/2026-09-21-*` and `2026-09-22-*`.

`tests/bridge_differential_x86.rs` keeps BOTH sides' corpus cases — this
branch's `fix_o_byval_arg_high_bytes`, `fix_o_byval_arg_page_boundary`,
`fix_p_exact_width_aggregate_return` and upstream's `pointee_lanes_tuple_nested`,
`pair_arg_lanes`, `union_fat_leaf`. They are disjoint evidence, not two
mechanisms for one lane.

## `library/core` refusal census, O0, certificates on

`scripts/trust_ir_cg_census.py` from the Trust checkout against the bridge
rebuilt from this tree. Retained in `census/` (`gap_table.md`,
`provenance.json`, `failed_roots.jsonl.gz`, `backend.sha256`), and the
upstream-only comparison base in `census-upstream-only/`.

| Measurement | Failed roots | Distinct reasons | Objects | Backend |
| --- | ---: | ---: | ---: | --- |
| 2026-09-22 round 2 (this branch, pre-merge) | 183 | 27 | 3,249 | `baf97456…` |
| 2026-09-22 `origin/main` alone, THIS host | 152 | 26 | 3,280 | `c1348026…` |
| **2026-09-22 round 3 (this tree)** | **152** | **26** | **3,280** | **`8df4e9a5…`** |

Upstream's own Darwin census reads 127. The difference to this host's 152 is
`[TCG-PASSVAL-067]` — **27 here, 0 on Darwin**, the checker-qualification
difference already recorded in `docs/linux-x86-64-completion.md`. Excluding
that class this host reads **125**, and the Darwin class table sums to the same
125 with every shared class equal.

### Against this branch's own pre-merge census, symbol by symbol

**31 roots cleared, 0 added, 0 reasons moved on a shared root.** The 31 are
exactly:

| cleared | reason |
| ---: | --- |
| 21 | `union field mem::manually_drop::ManuallyDrop<num::imp::fmt::Part<'{erased}>> is a fat pointer` (upstream `b04d8bd07`) |
| 10 | `[TCG-POINTEE-LANES]` — the `unicode_data::conversions` tuple pointees (upstream `92025e14b`) |

`[TCG-ARG-ABI]` stays at 2 across the substitution of the pair-argument
implementation. Class order after the merge: `[TCG-POINTEE-DYN-VALUE]` 30,
`[TCG-PASSVAL-067]` 27, `[TCG-POINTEE-UNSIZED-TAIL]` 16, `[TCG-POINTEE-LANES]`
11, memory-backed slice `Rvalue::Cast` 11, `[TCG-REGALLOC-063]` 8,
`[TCG-RET-REGCLASS]` 6, `[TCG-ARG-ABI]` 2, then 18 reasons at five roots or
fewer.

The round-3 line was measured TWICE — once on the tree as first merged and
again after the placement-gate guard was reinstated (below). Both read 152 and
their root sets are identical to each other and to `origin/main` alone, so the
guard costs nothing; the table's backend hash is the dylib the SECOND run used,
which is the tree as committed.

### Against `origin/main` alone on this host, symbol by symbol

`origin/main` alone (`749731ce8`) was built as a detached worktree and censused
on THIS host with the same stage2 `trustc` and the same command, so the
comparison is like for like rather than Darwin-against-Linux:

**152 roots, 26 reasons, 3,280 objects — and the failed-root SYMBOL SET is
IDENTICAL: 0 added, 0 removed, 0 reasons changed on a shared root.**

That is the whole answer to the round's question. Everything this branch carries
on top of `origin/main` — the vectorizer knobs and their plumbing,
`x86_trap_block.rs`, the saxpy-Q carrier guards and the fill-tier memset route,
the `call_only_body` certificate and its audit publication, the floor lanes and
fixture repairs, three cross-backend tests — costs the `core` census exactly
nothing, and upstream's three lanes are fully present. Upstream's own Darwin
figure of 127 is not the comparison: on Linux, upstream alone is 152 too.

## Bridge cross-backend lanes

Each run alone through the memory guard, `targo --unverified test --release
--locked --test <target>`. Logs in `bridge/`.

| target | result | note |
| --- | --- | --- |
| `m143_x86_vectorize_trace` | **2 passed / 0 failed** (23.25s) | the vectorizer trace and the `no-x86-fill-memset` opt-out still reach the pass through `-Ztrust-ir-cg-args` after `lib.rs` was replaced wholesale — this is what the re-applied knob forward buys |
| `m141_x86_partial_eightbyte_aggregate_xback` | **0 passed / 1 failed** (346.21s) | the KNOWN red: `O1 opt_ipv4`, trust-cg callee + trust-cg caller, at the LINK step. Byte-for-byte the pre-merge failure, down to the CGU hash and the `.text+0x140` offset — see below |
| `m142_x86_scalar_pair_arg_xback` | **0 passed / 1 failed** (1236.01s) — **16 combinations refuse**; see the finding below | this branch's 26-shape differential, run against UPSTREAM's pair-argument lane |
| `m141_x86_scalar_pair_arg_xback` | **1 passed / 0 failed** (516.42s) | UPSTREAM's own 12-shape differential for the lane, green on the merged tree — the lane itself works for everything upstream measured |

### ⚠ FINDING: upstream's pair-argument lane REFUSES a shape this branch's admitted

`m142_x86_scalar_pair_arg_xback` — this branch's 26-shape differential, kept
precisely so the lane is measured against whichever implementation survives —
**fails on 16 combinations** against upstream's lane. It passed whole against
this branch's own lane (round 1's retained log:
`../2026-09-22-linux-x86-64-upstream-merge/bridge/m142_x86_scalar_pair_arg_xback.log`,
1 passed, 1212.65s).

The 16 cells are exactly two shapes × the two trust-cg-CALLER combinations ×
O0/O1/O2/O3:

| shape | source | what it passes |
| --- | --- | --- |
| `apply_fn` | `pub fn apply_fn<F: Fn(Option<u8>, u32) -> u64>(v: Option<u8>, f: F, k: u32) -> u64 { f(v, k) }` called with `&g` | a pair into a `Fn` closure through the `impl Fn for &F` blanket |
| `apply_once` | the `FnOnce` twin, closure by value | a pair into a `FnOnce` closure |

Upstream's own differential for the same lane, `m141_x86_scalar_pair_arg_xback` (12 shapes), PASSES whole on this tree, so
the lane is not broken — it is narrower than this branch's was.

The other 24 shapes — including the float pairs (`(f64,f64)`, `(u64,f64)`,
`(f32,u64)`), the six-integer and eight-float register-exhaustion shapes,
`apply_fnptr` (the same call through a `fn` POINTER), `slice_arg` and `str_arg`
— pass in all four combinations at all four optimization levels.

The refusal, verbatim (O0, LLVM callee + trust-cg caller):

```
- _RNvXNtNtNtCsbnHOy3xFHYD_4core3ops8function5implsRNCNvCs76x7Di1DIDm_15caller_apply_fn4main0
  INtB4_2FnTINtNtB8_6option6OptionhEmEE4callBP_
  (reachable Rust-internal monomorphization, not a std-internal shim):
  [TCG-ARG-ABI] by-value aggregate argument 1 `std::option::Option<u8>` (2 bytes):
  rustc's own FnAbi passes it in 2 register lane(s) … but trust-cg would pass it in
  1 register lane(s) … (rustc `PassMode::Pair(…Zext…)`; bridge argument type [Array(TyId(0), 2)])
```

i.e. `<&{closure} as core::ops::function::Fn<(Option<u8>, u32)>>::call` — the
`extern "rust-call"` closure-forwarding shim — keeps the WHOLE-SLOT declaration
for its own untupled `Option<u8>` parameter, and the one-value gate then refuses
it. This is the family upstream's own commit declines by name ("a closure whose
OWN parameter is a pair stays refused, and the refusal text says so"); this
branch's lane admitted it, because its prerequisite refactor put every argument
list — the closure-call builders included — behind one per-argument marshaller.

**WHICH decline fires is NOT established here, and is not guessed.** The
observed fact is the refusal text above and the 16 combinations; the exact gate
in `scalar_pair_param_plan` that returns `Ok(None)` for this instance (the
`rust-call` untupling path not asking the plan at all is the leading candidate,
the `ty::Closure` / `CoroutineClosure` arm is not, since the instance is a
`ty::FnDef` method of `core::ops::function::impls`) needs one instrumented
bridge build to pin down. Stating it without that build would be the kind of
read-not-measure claim this round exists to avoid.

**Why upstream's is still the base.** The rule for this round is to decide a
duplicated lane by comparing the census root SET by symbol, and that comparison
is an exact tie — 152 = 152, symbol for symbol, with `[TCG-ARG-ABI]` at 2 on
both. On real `library/core` there is no root of this shape, so the capability
difference is not measurable where the rule looks. Reinstating this branch's
lane would mean reinstating the ~1,300-line marshaller refactor next to
upstream's scope rule, i.e. two mechanisms for one lane, which this round is
explicitly not allowed to leave behind.

**What is owed, and it is owed rather than hidden.** The capability is a real
regression against this branch's pre-merge tree, and `m142` is left RED rather
than weakened — the test is the evidence, and a test that stops asserting is
worth nothing. The next step is one instrumented bridge build against the
reproducer below to name the declining gate, then the contained repair on
upstream's single mechanism: let the plan claim this family and teach whichever
hand-built list serves it to push the plan's two carriers, so the declaration
and the list keep agreeing. Reproducer, in a directory the test leaves behind
(`/tmp/rcl2_pairarg_xback_<pid>/`, which it does not clean up):

```
trustc --edition=2021 -Ztrust-verify=off --crate-type bin \
  -Zcodegen-backend=<librustc_codegen_trust_cg.so> --target x86_64-unknown-linux-gnu \
  -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Copt-level=0 \
  --extern calleearg=calleearg_llvm_O0/libcalleearg.rlib -L calleearg_llvm_O0 \
  -o repro caller_apply_fn.rs
```

### The `m141` partial-eightbyte red PERSISTS and is pre-existing

Round 3:

```
O1 `opt_ipv4` trust-cg callee + trust-cg caller: trust-cg caller failed closed:
  error: aborting due to 1 previous error | collect2: error: ld returned 1 exit status
  >>> defined at callee.callee.ae2add452474a0f0-cgu.0.rcgu.o:(.text+0x140)
      in archive /tmp/rcl2_parteb_xback_1620724/callee_tcg_O1/libcallee.rlib
```

The pre-merge run retained at
`../2026-09-22-linux-x86-64-upstream-merge/bridge/m141-pre-merge-2026-09-21.log`
has the identical line, with the identical CGU hash `ae2add452474a0f0` and the
identical `.text+0x140`; only the temp-directory PID differs. It is not a
regression of this merge, it is not covered by the floor (only
`m143_x86_vectorize_trace` is a registered bridge target), and diagnosing the
link failure is still owed.

## Root workspace suites

Pinned stock Rust 1.97.1, all under the guard. Logs in `suites/`.

| suite | result |
| --- | --- |
| `cargo test --workspace --no-run` | builds |
| `trust-cg-lower --lib` | 1,882 passed / 0 failed |
| `trust-cg-codegen --lib` | 4,003 passed / **16 failed** |
| `trust-cg-opt --lib` | 3,562 passed / 0 failed |
| `trust-cg-verify --lib post_ra_dataflow` | 74 passed / 0 failed |
| `trust-cg-verify --lib x86_64_lowering_proofs` | 176 passed / 0 failed |
| `x86_volatile_trace_gate` | 8 passed |
| `x86_addressing_gate` | 10 passed |
| `coverage_gate_tests` | 49 passed |
| `meta_theorems` | 8 passed |
| `soundness_manifest` | 11 passed |
| `e2e_x86_64_aggregate_abi` | 30 passed |
| `e2e_x86_64_aggregate_byval_arg` | 8 passed |
| bridge workspace `--lib` | 286 passed / **13 failed** (13 solver/checker reds — see below) |
| bridge `--test bridge_differential_x86 --no-run` | compiles (both sides' corpus cases) |

**The 16 `trust-cg-codegen --lib` failures are the KNOWN pre-existing set, and
the set is identical name for name** to the round-2 list retained at
`../2026-09-22-linux-x86-64-upstream-round2/codegen-lib-failures.txt`
— fifteen `compile_service::*` and
`compiler::tests::test_aarch64_parallel_and_serial_multi_function_byte_identical`.
The last one reports `ProofPromotionRejected` directly (the AArch64
`StpPreIndex` / `LdpPostIndex` opcode-inventory row); the fifteen assert
`Compiled` where the XD-01 promotion gate produced `Failed`. Diffed, not
eyeballed (`sort | diff` against the round-2 file); the list is retained again
as `codegen-lib-failures.txt`.

## Pre-existing reds found by measuring something earlier rounds did not

The bridge workspace's OWN unit tests (`targo --unverified test --release
--locked --lib`) were never run in rounds 1 or 2, so there is no in-tree
baseline for them. Run here: **286 passed / **13 failed****. The failures are all
`mem_refine::tests::correct_*_is_not_refuted` — the SOLVER-backed POSITIVE
controls of the `p3c-refine` lane, whose assertion is "with a solver the correct
emission must Refine". Every one of them reports:

```
got Inconclusive { reason: "unknown: incomplete AY proof certificate:
  c ay.proof.certificate path=/tmp/trust-cg-ay-query-*.smt2.alethe
  unproved_steps=1 foreign_assumes=no trust_free=no ay_self_checkable=yes" }
```

That is the checker-pairing condition this host is already recorded as having
(the stage2 `clean` on the bridge's PATH is not the carcara-capable one), not a
refutation: the NEGATIVE controls in the same module — the ones that must refute
a wrong emission — all pass, and the same 13 names fail in both runs of this
suite (before and after the placement-gate guard was reinstated), with the
`abi_reg_lanes` count going 33 → 34 as the restored test joins them. Nothing in this merge touches `mem_refine.rs`
(`git diff origin/main HEAD -- crates/rustc-codegen-trust-cg/src/mem_refine.rs`
is empty), so these are host reds, not merge reds. They are recorded here so the
next round has a baseline; `suites/bridge-lib.log` (the run on the final tree) and
`suites/bridge-lib-preguard.log` (the run before the placement guard was
reinstated) are both retained.

## Linux x86-64 regression floor

`python3 scripts/check_linux_x86_64.py --jobs 4 --max-rss-gib 20 --trust-driver
<stage2>/bin/trustc`. Per-target logs and `report.json` in `floor/`, run on the
committed tree.

**57 of 68 targets pass, 11 fail** — `status: fail`, **`errors: []`**, `final_source.dirty: false`, `source_sha: 8159a9943` (the report commit), so the
record is of the committed tree. The failing targets:

* `trust-cg-codegen :: e2e_x86_64_eh_catch`
* `trust-cg-codegen :: e2e_x86_64_eh_invoke_trust_ir_run`
* `trust-cg-codegen :: e2e_x86_64_eh_resume_trust_ir`
* `trust-cg-codegen :: jit_cert_cache_identity_x86_64`
* `trust-cg-codegen :: jit_sysv_x86_64_spill_replay`
* `trust-cg-codegen :: jit_validation_modes_x86_64`
* `trust-cg-codegen :: jit_x86_64_aggregate_abi_fail_closed`
* `trust-cg-codegen :: jit_x86_64_profile_modes`
* `trust-cg-codegen :: x86_64_constant_pool`
* `trust-cg-codegen :: x86_64_sysv_ay_abi`
* `trust-cg-codegen :: x86_64_target_features`

**Target for target identical to rounds 1 and 2** — diffed against round 2's
retained `report.json`, not eyeballed: **0 targets added, 0 removed, 0 status
changes** across all 68. The eleven failures are the two standing open items and
nothing else: three under X03 (ELF exception handling, still Darwin-guarded) and
eight under XD-01 (`ProofPromotionRejected`: statistical credit on a
formal-capable host). `e2e_x86_64_swiftcc` is recorded decided-absent (XD-03) and
not run, and `m143_x86_vectorize_trace` — the one bridge-workspace target the
floor registers — passes, which is the floor's own check that the vectorizer
knob forward survived `lib.rs` being replaced wholesale.

## What this does not measure

* No proof claim. The bridge is built in the explicitly unverified frontend
  lane (`targo --unverified`), and the root workspace is built by stock
  rustc 1.97.1 — a successful build is not a claim that trust-cg was compiled
  by a verifying compiler.
* No `alloc` / `std` census, no compiler-crate or rebuilt-compiler run, and no
  Trust bootstrap `trust-ir-cg` dylib step on this host.
* The census is a REFUSAL count on `library/core` at O0 with `-Cpanic=abort`.
  It says nothing about the correctness of what did compile beyond what the
  differential and cross-backend tests above measure.
* The 11 floor failures are the two standing open items (XD-01 statistical
  credit on a formal-capable host; X03 ELF exception handling), not new work of
  this merge.

## ⚑ The race did not stop: `origin/main` moved again during round 3

Fetched at the end of this round, `origin/main` is `3b6b64484`, **5 commits
ahead of `749731ce8`** (the tip merged here). They are NOT merged in this round:

```
3b6b64484 bridge(x86-64): three small `library/core` classes — the `Array(I128, 1)` return-gate arm,
          a self-recursive body's own symbol, `type_of` — core census 148 -> 140
793954443 tests(bridge): the x86 corpus harness builds a std fixture as a binary and the mangled
          `const_bounds_check_elim` parses again
2725108dc bridge(x86-64): type a thin raw pointer to a `&dyn Trait` pointee as the two-lane image —
          [TCG-POINTEE-DYN-VALUE] 28 -> 15, core census 161 -> 148
9ee5abf9e bridge: lower `raw_eq` against a PROMOTED array literal — `arr == [..]` at -O refused on the
          current core
9fa83cfc1 bridge: refuse a one-lane wide-pointer signature at the boundary — `NonNull<[T]>` by value
          was emitted with one register where rustc passes `{data, len}`
```

Two of them touch classes this round measured: `[TCG-POINTEE-DYN-VALUE]`, the
largest remaining class here (30 roots), and `[TCG-RET-REGCLASS]` (6 roots, the
`Array(I128, 1)` return gate). Their census line (161 → 148 → 140) is a
different baseline from the 127 this round's merge base reports, so those
numbers do not compare directly to the 152 measured here. None of the five
duplicates work on this branch, so round 4 should be an ordinary merge.
