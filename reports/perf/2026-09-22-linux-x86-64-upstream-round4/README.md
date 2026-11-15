# Linux x86-64: round 4 — the branch made current with `origin/main`, and the m142 cause named (2026-09-22)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Round 3 closed with its own check (1) failing: `git log --oneline origin/main
--not HEAD` returned five commits, because `origin/main` moved to `3b6b64484`
while the round ran. Nothing upstream had been LOST (the merged tip
`749731ce8` is an ancestor of round 3's HEAD), but the branch was not current —
and two of the five land exactly where round 3 had just fought:

| upstream commit | what it does | where it lands on this branch |
| --- | --- | --- |
| `9fa83cfc1` | refuse a one-lane wide-pointer signature at the boundary (`NonNull<[T]>` by value); Darwin census 127 → **161**, a deliberate RISE | `tests/bridge_differential_x86.rs` (hand-merged in round 3) and a new `m142_*` test file |
| `9ee5abf9e` | lower `raw_eq` against a PROMOTED array literal | no overlap |
| `2725108dc` | type a thin raw pointer to a `&dyn Trait` pointee as the two-lane image; 161 → 148 | no overlap |
| `793954443` | the x86 corpus harness builds a std fixture as a binary | `tests/bridge_differential_x86.rs` |
| `3b6b64484` | three small classes (`Array(I128, 1)` return gate, self-recursive symbol, `type_of`); 148 → **140** | **+88 lines in `src/abi_reg_lanes.rs`** — the file where round 3 reinstated the multi-value-argument bare-scalar refusal |

Merge commit: `8de8af0d8`. The reinstated fail-closed refusal and its unit test
were verified BY HAND after the auto-merge, because round 3's own risk note said
this is the guard the next merge must not silently drop. It did not: the
`!bare_scalar || l.len() != 1` allowlist is intact and all three unit tests —
ours, upstream's MEMORY-class one and upstream's new I128-leaf one — pass side by
side.

Host: `x86_64-unknown-linux-gnu`, Ryzen 9 9900X3D, 24 cores, 61 GiB, GCC 15.2.0.
Root workspace on the pinned stock Rust 1.97.1 (`rust-toolchain.toml`; the
project's own pin overrides this machine's Trust default toolchain). Bridge built
with the tree-built stage2 `trustc` (`rustc 1.99.0-dev (3a3e781fe 2026-09-14)`)
through `targo --unverified build --release --locked`. Every build, test and
census ran under the memory guard (`CARGO_BUILD_JOBS=3`, one of two flock slots,
`MemoryMax=22G`); another agent was building in a sibling worktree throughout.

This is a regression and refusal measurement in the explicit unverified frontend
lane. It is not a proof claim, and it does not establish compiler completion or
release readiness.

## The m142 red: cause named, and one real defect fixed on the way

Round 3 left `m142_x86_scalar_pair_arg_xback` RED on 16 combinations and said
naming the cause needed "one instrumented bridge build". It did not. The two
failing shapes were cut out of that 1,236-second differential into a three-file
driver (`m142-reproducer/`) and each refusal comes back in about a second from
the release dylib. What it shows is that round 3 had recorded ONE refusal where
there were TWO:

* **`apply_fn`** — `[TCG-ARG-ABI] by-value aggregate argument 1
  `Option<u8>` … rustc requires 2 register lane(s) and trust-cg would emit 1`.
  This is the lane's OWN scope. `scalar_pair_param_plan` declines a
  `ty::Closure` instance by name — closure calls are hand-built one value per
  argument by six different builders — so the CLOSURE BODY keeps its whole-slot
  declaration and `check_param_abi` refuses it. The symbol the error is
  attributed to is the caller being compiled
  (`<&{closure} as Fn<(Option<u8>, u32)>>::call`, the `impl Fn for &F` blanket
  shim), which is why round 3 read it as a shim problem; the declined instance
  is the closure body.
* **`apply_once`** — `[TCG-ARG-ABI] rustc's FnAbi argument 0 is `Closure(…)`,
  which does not describe the bridge's classified by-value argument
  `Option<u8>` … Report this — it is a bridge bug`. A different symbol
  (`calleearg::apply_once::<{closure}>`), a different arm, and it really was a
  bridge bug — **fixed in `b27752696`**.

`func_ty_for_instance` does not prepend the env input for a closure body whose
by-value environment is ZERO-SIZED (a non-capturing `FnOnce`), because the entry
block drops it too. rustc's `fn_sig_for_fn_abi` does not drop it: the receiver
stays `FnAbi::args[0]` with `PassMode::Ignore`. The bridge used its own `inputs`
index as the `FnAbi::args` index at four gate call sites, and
`param_input_index_for_mir_arg` subtracted a SECOND 1 on the body side, so both
ends asked rustc about the argument one position too early and the gate compared
the closure ENV against the first real parameter. No miscompile was possible —
the gate type-checks the `ArgAbi` before reading any placement, so a misaligned
index always REFUSED — but it refused ordinary program shapes with "report this,
it is a bridge bug". The mapping is now stated once at each end
(`closure_env_abi_index_offset` for the declaration,
`rustc_fn_abi_arg_index_for_mir_arg` for the body) and a unit test pins that the
two halves name the same argument.

Scope of that fix, stated exactly: the observable change today is on the
DECLARATION side (`classify_func_ty`'s `check_param_abi`), because the body side's
only consumer is the pair plan, which declines a closure instance before the
index is used. The body side is corrected anyway so the two ends cannot disagree
if the closure decline is ever lifted — which is precisely the change XD-05 owes.

After the fix both shapes report the SAME honest lane refusal (see
`m142-reproducer/after-fix.txt`), which is what bounds the finding: **one gate,
one code, two shapes** — the `ty::Closure` decline, and nothing wider.

`m142` is still RED and is not weakened. Closing it means teaching the pair lane
to the six hand-built closure-call argument builders (`emit_closure_call_n`,
`build_tuple_item_arg`, `finish_closure_call`,
`finish_closure_call_aggregate_return`, `spread_fn_call_tuple_untupled`,
`untuple_const_tuple_call_args`) — a lane change with its own census and its own
arity risk, the class of change that cost 606 `core` roots on 2026-09-11 — or
reverting to this branch's deleted marshaller (`902c69b18` + `04b1050bb`, intact
in history). That choice is the owner's; this round did the diagnosis and left
both doors open.

## The `core` census: 152 → 165, and the Darwin gap is now exact arithmetic

Same instrument, same compiler, same flags as rounds 1-3
(`trust_ir_cg_census.py --crate core --opt-level 0 --panic abort`, stage2
`trustc 3a3e781fe`, `-Ztrust-verify=off`, certificates on):

| tree | roots | reasons | objects | backend |
| --- | ---: | ---: | ---: | --- |
| round 3 (`44facace6`) | 152 | 26 | 3,280 | `8df4e9a5…` |
| **round 4, merge only (`8de8af0d8`)** | **165** | **25** | **3,267** | `f86af202…` |
| **round 4, with the index fix (`b27752696`)** | **165** | **25** | **3,267** | `900d7f15…` |

The RISE is upstream's intent, not a regression: `9fa83cfc1`'s boundary guard
refuses signatures the bridge used to emit with a silently wrong ABI. Against
round 3, by symbol: **34 added** (9 `[TCG-ARG-ABI]` + 25 `[TCG-RET-ABI]`, all the
guard's), **21 removed** (13 `[TCG-POINTEE-DYN-VALUE]`, 6 `[TCG-RET-REGCLASS]`,
1 `[TCG-REGALLOC-063]`, 1 `unsupported intrinsic`) and **13 moved** onto the
guard's codes (11 from `memory-backed slice Rvalue::Cast`, 2 from
`[TCG-POINTEE-DYN-VALUE]`) — every published Darwin effect of upstream's three
lanes reproduced class for class on this host (`census/diff-vs-round3.txt`).

**The index fix costs the census exactly nothing**: the merge-only tree and the
fixed tree have the identical root set, symbol for symbol — 0 added, 0 removed,
0 reasons moved (`census/diff-index-fix-attribution.txt`, both censuses
retained). That is expected and it was measured rather than assumed: no `core`
root carries the misaligned-index arm.

**The Darwin/Linux gap.** Upstream's own `3b6b64484` census reads **140** on
Darwin. Round 3's text said this host read 125 against "the same 125 with every
shared class equal"; recomputed from the retained artifacts, the then-current
Darwin census was 127 with a remainder of **43**, not 41, so the two sides were
2 roots apart and stated as identical. On the round-4 baseline the identity is
exact and every shared class is equal:

```
Linux 165  =  Darwin 140  +  27 [TCG-PASSVAL-067]  -  2 Darwin-only atomic-element roots
Linux 138  =  Darwin 140  -  2                        (excluding PASSVAL-067)
```

The two Darwin-only roots are `atomic over non-I<n>..I<n>-scalar element i<n>`
and `… u<n>`. Every other class is equal count for count: `[TCG-RET-ABI]` 26,
`[TCG-ARG-ABI]` 23, `[TCG-POINTEE-UNSIZED-TAIL]` 16,
`[TCG-POINTEE-DYN-VALUE]` 15, `[TCG-POINTEE-LANES]` 11, `[TCG-REGALLOC-063]` 7,
`[TCG-RET-REGCLASS]` 0, fat-leaf union 0, memory-backed slice `Rvalue::Cast` 0,
`whole scalarized aggregate` 5, `[TCG-SSA-071]` 4.

**What was NOT measured, and what stands in for it.** This round did not build
`origin/main` alone in a detached worktree as round 3 did, so there is no
Linux upstream-only census for `3b6b64484`. The substitute is the class-by-class
identity above: the four things this branch carries on top of upstream are one
fail-closed REFUSAL (the bare-scalar guard), a knob forward, an index mapping and
two string literals, and any refusal they added would show up as an extra Linux
root in some class — instead every shared class equals upstream's own
Darwin-measured count for the same commit, and the two totals differ by exactly
the two classes that are host-specific for reasons this report names. A detached
upstream-only census would be a stronger statement and is worth one census slot
in round 5.

## The repository's own documentation gate was RED on the merge

`python3 scripts/check_documentation.py --check` fails on `origin/main`:

```
diagnostic census failed: lib.rs:9678: string literal holds a malformed or computed code `TCG-`
```

`9fa83cfc1` emits its code as `format!("[TCG-{}-ABI] …", if arg_index.is_some()
{ "ARG" } else { "RET" })`, and `scripts/generate_diagnostics_inventory.py`
refuses a code it cannot read out of a string literal — correctly: a code that
only exists after `format!` runs is a code no inventory, no gap table and no grep
can find. Measured both ways (`origin/main`'s `lib.rs` swapped in, census run,
swapped back). The two codes are now literals of the same shape
`abi_reg_lanes::rustc_placement` already takes, the emitted message bytes are
unchanged, and `docs/diagnostics.md` gained the two emission sites it could not
see before (120 → 122 string-literal sites).

## What this round did NOT re-run, and why that is sound

`git diff --name-only 44facace6..HEAD` outside the bridge crate is
`CHANGELOG.md`, `INVENTORY.md`, `docs/` and `reports/` — **nothing in the root
workspace changed**. Round 3's root-suite numbers therefore stand unchanged and
are not restated here as if they had been re-measured:
`trust-cg-codegen --lib` 4,003 / the identical 16 XD-01 failures,
`trust-cg-lower --lib` 1,882 / 0, `trust-cg-opt --lib` 3,562 / 0,
`trust-cg-verify --lib` `post_ra_dataflow` 74 / 0 and `x86_64_lowering_proofs`
176 / 0, and the gate suites (`coverage_gate_tests` 49, `meta_theorems` 8,
`soundness_manifest` 11, `x86_addressing_gate` 10, `x86_volatile_trace_gate` 8,
`e2e_x86_64_aggregate_abi` 30, `e2e_x86_64_aggregate_byval_arg` 8). The root
formatting gate and the documentation gates WERE re-run, because this round edits
`docs/` and regenerates both inventories.

`crates/trust-cg-codegen/tests/clean_fixture_host_lowering.rs` is recorded as an
uncovered lane rather than claimed: 39 Clean fixtures × O0/O1 through
`Compiler::compile`, registered in NONE of `check_linux_x86_64.py`,
`check_linux_aarch64.py`, `check_darwin_aarch64.py` (grep: zero hits), and its
two sweeps do not finish in ~75 minutes of unoptimized CPU on this host. It has
no recorded pass on this tree. Registering it needs a recorded runtime first,
which this round did not spend.

## Owed, and unchanged owner decisions

* **The m142 closure-parameter capability.** Cause named above; the choice
  between extending upstream's one mechanism to the six closure-call argument
  builders and reverting to this branch's marshaller is the owner's. `m142` stays
  RED until one of them is taken.
* **`m141_x86_partial_eightbyte_aggregate_xback`'s `O1 opt_ipv4` LINK failure**
  remains undiagnosed, and `m141` is not a registered floor target, so 57/68 does
  not cover it.
* **The 13 `mem_refine` solver-backed positive controls** still report an
  incomplete AY certificate on this host. `src/mem_refine.rs` is untouched by
  this merge and every one of the module's negative controls passes; it is the
  host's degraded-checker condition, not a merge red, and re-running it against
  the dev-linked carcara Clean still needs the Trust sysroot on
  `LD_LIBRARY_PATH`.
* **XD-01** (8 floor targets + 16 `trust-cg-codegen --lib` failures) and **X03**
  (3 ELF exception-handling targets) are unchanged owner-decision items.
* **`[TCG-PASSVAL-067]`** (27 roots, the `x86-popcnt-expand` solver-unknown) is
  the one class this host carries and Darwin does not; it needs the
  qualification replay on this host.
* **The capability half of upstream's boundary guard** — a two-lane boundary slot
  for the `NonNull<[T]>` / `Unique<[T]>` transparent newtype carriers — is now
  the largest single class on this host at 49 roots (`[TCG-RET-ABI]` 26 +
  `[TCG-ARG-ABI]` 23). It is upstream's own declared next step.

## Risks

* The bridge dylib is not byte-reproducible on this host (measured in
  `1d0364f8d`), so a recorded backend SHA-256 identifies a RUN, not a source
  state. Three are recorded here for three distinct runs.
* `abi_reg_lanes.rs` still diverges from upstream by one guard (+264 / −0). The
  next merge must not silently drop it; this round checked it by hand precisely
  because round 3's risk note said so.
* `docs/linux-x86-64-completion.md`'s X01 row remains a hand-merged conjunction
  of Darwin-measured and Linux-measured clauses, and says so.
* `bridge_differential_x86.rs`'s merged corpus list had compile-time evidence
  only after round 3. It is executed in this round (below); before this run,
  nothing in any gate covered it.
* Every build, test and census ran under the memory guard while another agent
  built in a sibling worktree. No build ran outside the guard, and
  `CARGO_BUILD_JOBS` was never raised above 3.

## `origin/main` moved again DURING this round — stated, not hidden

`git log --oneline origin/main --not HEAD` was EMPTY when this round's merge was
made and is **3 commits** again as it closes (the ref advanced in the shared
object store while the round's own measurements ran; the newest is dated
2026-09-22 14:39):

| commit | what | why it matters here |
| --- | --- | --- |
| `ea9bea36b` | four more small `library/core` classes; Darwin census 140 → 128 | ordinary merge |
| `c8338c62f` | i128 shift count in the selector, whole scalar-union read, over-aligned `#[repr(simd)]` pointee shell; 128 → **109** | ordinary merge |
| `16c4a4a3f` | **a closure's own `&[T]` / `str` parameter is passed as its `{data, len}` slot address** — a SIGSEGV at O0 found by a corpus sweep, census unchanged | lands in `lower_closure_call_terminator`, the same closure-call argument builder the m142 pair lane would have to reach. Round 5 should read it before touching XD-05 |

Nothing upstream is LOST — `origin/main`'s `3b6b64484` is an ancestor of HEAD —
but a round cannot be both current and measured while upstream commits faster
than a census-plus-differential cycle (about 45 minutes here). This round chose
MEASURED, merged everything through `3b6b64484`, and names what it did not merge.

**Four divergences from upstream that the next merge must not silently drop**
(the first is round 3's, the rest are this round's):

1. `src/abi_reg_lanes.rs`: the multi-value-argument BARE-SCALAR refusal and
   `a_non_scalar_value_is_refused_in_the_multi_value_argument_arm_on_x86_64`
   (+264 / −0 against upstream).
2. `src/lib.rs`: the 22-line vectorizer / fill-memset knob forward in
   `install_knob_backed_library_settings` (`m143` is the floor's proof that it is
   load-bearing).
3. `src/lib.rs`: the `FnAbi::args` index mapping —
   `classify_func_ty`'s `abi_arg_index_offset`, `closure_env_abi_index_offset`
   and `rustc_fn_abi_arg_index_for_mir_arg`. **Upstream still carries the
   double-subtracting `param_input_index_for_mir_arg`**, so this is a real
   conflict next round, not a coincidence.
4. `src/lib.rs`: the boundary guard's `"[TCG-ARG-ABI]"` / `"[TCG-RET-ABI]"`
   literals. Upstream still computes the code, so
   `scripts/check_documentation.py --check` is still RED on `origin/main`.

## Bridge workspace suites, on the merged + fixed tree

| target | result | note |
| --- | --- | --- |
| `--lib` | **288 passed / 13 failed** | the identical 13 `mem_refine` names as round 3 (sorted diff empty); +2 passes are upstream's I128-leaf placement test and this round's `FnAbi`-index test. `abi_reg_lanes` is 35 / 0, including BOTH multi-value-argument refusal tests and upstream's new one |
| `m142_x86_wide_newtype_boundary_guard` (upstream's new) | **1 passed / 0** | upstream's negative pin for the one-lane wide-pointer guard executes on Linux |
| `dyn_fat_leaf_differential` (upstream's new fixture) | **1 passed / 0** | `bridge_corpus/dyn_slice_iter_raw_ptr.rs` agrees with LLVM on this host too |
| `m143_x86_vectorize_trace` | **2 passed / 0** | the knob forward is still load-bearing and still survives a `lib.rs` merge |
| `m141_x86_scalar_pair_arg_xback` (upstream's) | **1 passed / 0** (518.94s) | upstream's own 12-shape pair-argument differential is whole |
| `m141_x86_partial_eightbyte_aggregate_xback` | {{M141_PARTIAL}} | |
| `m142_x86_scalar_pair_arg_xback` | {{M142_PAIR}} | |
| `bridge_differential_x86` | {{BRIDGEDIFF}} | first EXECUTION of the corpus list round 3 hand-merged; round 3 had `--no-run` evidence only |

## The Linux x86-64 regression floor

`python3 scripts/check_linux_x86_64.py --jobs 4 --max-rss-gib 20 --trust-driver
<stage2>/bin/trustc`, run on the committed tree with the round's artifacts
already in place (round 3's first floor run recorded "source changed while
required targets were running" because its own artifacts were being written
during it; this one writes outside the source tree with `--out`):

{{FLOOR}}

## Files

```
census/                              165 / 25 / 3,267 on b27752696 (backend 900d7f15…)
census-without-index-fix/            165 / 25 / 3,267 on 8de8af0d8 (backend f86af202…)
census/diff-vs-round3.txt            34 added / 21 removed / 13 moved, by symbol
census/diff-index-fix-attribution.txt  0 / 0 / 0 — the fix costs the census nothing
m142-reproducer/                     the two failing shapes, the driver, before/after refusals
suites/bridge-lib.log                288 / 13
bridge/*.log                         every bridge cross-backend target of this round
floor/                               the floor record and every per-target log
```
