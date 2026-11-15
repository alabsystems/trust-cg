# The first x86-64 Linux runtime measurement: 18/18 MATCH, runtime geomean 0.886x LLVM -O3

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`benchmarks/beat-llvm/run.py` on `x86_64-unknown-linux-gnu`, AMD Ryzen 9 9900X3D,
kernel 7.0.0-34-generic, host `QUIET` (loadavg 0.47 before, 1.16 after, threshold
12.0). Driver: the tree-built stage2 `trustc`. Backend: the bridge dylib built from
this worktree, `dylib_sha256 7d6e9243…`. Clean tree: `git_sha f4cc61ca7153`,
`git_dirty false`. Retained: `clean-run-results.json`, `clean-run.log.gz`.

## THIS IS NOT A LEDGER ROW, and the harness says so itself

`headline_eligible = false` in the results JSON. The run requires
`--bridge-cg-arg no-proof-certs`, and `benchmarks/beat-llvm/contract` records a
non-default backend knob as a DIAGNOSTIC lane it does not accept as evidence. No
row was added to `ratchet/ledger.jsonl` and none should be from this.

The knob is not a convenience here — it is the only way the measurement exists at
all. In the default lane the bridge cannot compile a trivial Rust program: proof
promotion refuses `std::rt::lang_start` because `MovRR`, `MovRR32`, `Lea`,
`LeaRip`, `MovRM`, `MovMR` and `Movzx` have no operand-exact evidence
(see the [core census](../2026-09-28-linux-x86-64-core-census/README.md) and XD-01
in the completion plan). So this report
measures what the x86-64 backend's CODE does, with the evidence gate off, and says
nothing about proof credit.

## What it measured

Coverage **100.0%: 18 of 18 MATCH, 0 INCOMPLETE, 0 MISMATCH**, 0 NONDET-FAILCLOSED,
0 NONDET-CANDIDATE. Output equality is exit code with a full-width checksum folded
in (mod 126); per the contract a MATCH is probabilistic and a MISMATCH would be a
definitive P0. Every program in the corpus compiled through the bridge and agreed
with the LLVM-built reference.

| Axis | vs LLVM | Reading |
| --- | --- | ---: |
| runtime geomean | -O3 | **0.886x** |
| runtime, resolvable rows only (12 programs, llvm median >= 0.05s, rel_spread <= 0.25) | -O3 | **0.788x** |
| scalar runtime geomean | -O3 | 0.990x |
| worst single program | -O3 | 2.611x |
| compile, warm | -O2 | 1.301x |
| compile, warm | -O3 | 1.301x |
| linked size geomean | -O3 | 1.00024x (worst 1.00051x) |
| program peak-RSS geomean | -O3 | 0.997x (16 of 18 floor-bound) |
| compiler peak-RSS geomean | -O2 | 1.057x |

By category:

| Category | match/total | runtime geomean x |
| --- | ---: | ---: |
| vectorizable | 5/5 | **0.540** |
| multifn | 2/2 | 0.863 |
| scalar | 6/6 | 0.990 |
| branch | 1/1 | 1.157 |
| heap | 4/4 | 1.321 |

## Reproduced, and which numbers are soft

The suite was run twice on the same dylib. The first run is retained as
`reproducibility-run-results.json` and is stamped `git_dirty true` — it was launched
while this round's census report edits were uncommitted. That dirt was
documentation only and the dylib predates it, so the two runs are a fair
reproducibility pair, but the DIRTY run is not quoted as the result:

| | clean run | first run | spread |
| --- | ---: | ---: | ---: |
| runtime geomean vs -O3 | 0.886x | 0.889x | 0.3% |
| resolvable-rows-only | 0.788x | 0.791x | 0.4% |
| scalar | 0.990x | 0.992x | 0.2% |
| compile warm vs -O2 | 1.301x | 1.301x | 0% |
| worst single program | 2.611x | 2.483x | **5.2%** |

So the geomeans and the compile ratio are firm to a fraction of a percent, and the
WORST-PROGRAM figure is the soft one — quote it as "about 2.5x", not to three
digits.

## Read against the goal, strictly

The objective is "a performance at least matching LLVM and clang". Taking that
axis by axis rather than on the flattering average alone:

* **Runtime geomean: MET.** 0.886x is 11% faster than LLVM -O3, and 0.788x on the
  rows whose timings resolve. The vectorizable category at 0.540x is the reason,
  and it is a real reversal: the last diagnostic pass on this host had
  `p4_matmul` at 4.079x and `v2_memfill` at 4.029x, i.e. four times SLOWER.
* **Per-program: NOT MET, but by 15.7% and not by 2.6x.** The worst program whose
  timing the harness RESOLVES is `b1_mispredict` at 1.157x, and 8 of those 12 rows
  are at or better than LLVM -O3. The 2.611x row (`h1_vec_push_sum`) is a 9.1ms
  LLVM median, below the harness's own 0.05s floor — see the correction section.
* **Compile time: NOT MET.** 1.301x LLVM -O2 warm. Better than the 2.43x this host
  last recorded, still not matching.
* **Eligibility: NOT MET.** Diagnostic lane, `headline_eligible = false`.

Correctness on this corpus is the strongest part of the result and the part most
worth keeping: 18 of 18 programs matched, which is the first time any x86-64 Linux
run of this suite has been complete.

## CORRECTION: the 2.611x "worst program" is BELOW THE HARNESS'S OWN RESOLUTION

This report quoted "worst single program 2.611x" as an unmet axis, and a later
section diagnoses that program at length. Both stand as facts about `h1`, but the
headline was wrong to treat it as the per-program result, and this section says so
before the diagnosis rather than after it.

`h1_vec_push_sum`'s LLVM -O3 median is **0.0091s — 9.1 milliseconds**. The harness's
own resolvability criterion for a runtime row is `llvm median >= 0.05s` with
`rel_spread <= 0.25`; that is why its headline carries a "resolvable-rows-only"
figure over 12 of the 18 programs. `h1` is one of the SIX it excludes. The 2.611x is
a 9ms-versus-24ms reading, a 15ms absolute difference, on a measurement the harness
declines to resolve.

Recomputing per-program over the resolvable set only (the same filter, reproduced
here — it yields exactly the harness's 12 rows):

| program | llvm -O3 median | bridge median | ratio |
| --- | ---: | ---: | ---: |
| b1_mispredict | 0.1850s | 0.2140s | **1.157** |
| p6_branch_match | 1.5345s | 1.5885s | 1.035 |
| p2_collatz | 0.1590s | 0.1630s | 1.025 |
| p4_matmul | 0.0566s | 0.0619s | 1.094 |
| m1_call_chain | 0.0656s | 0.0656s | 1.000 |
| p8_closure_nest | 0.1469s | 0.1470s | 1.000 |
| p1_xorshift | 0.4363s | 0.4357s | 0.999 |
| p5_struct_acc | 0.4356s | 0.4346s | 0.998 |
| p3_gcd | 0.2822s | 0.2519s | 0.893 |
| m2_call_heavy | 0.0592s | 0.0441s | 0.745 |
| v1_saxpy | 0.0728s | 0.0474s | 0.651 |
| v3_popcount | 0.1238s | 0.0123s | 0.100 |

**The worst RESOLVABLE program is `b1_mispredict` at 1.157x, not 2.611x**, and 8 of
the 12 are at or better than LLVM -O3. The six excluded rows are `h1` (9.1ms),
`h2` (14.9ms), `h3` (35.3ms), `h4` (7.8ms), `p7_sieve` (32.1ms) and `v2_memfill`
(3.1ms) — every one a sub-50ms LLVM median.

Two consequences, stated plainly because the second is a process failure of mine:

* The per-program axis is much closer to met than this report first said. The real
  remaining gap is **15.7% on one branch-heavy program**, not a 2.6x outlier.
* The `h1` investigation below — including an optimization built, tested and
  reverted — was aimed at a sub-resolution measurement. I quoted the
  resolvable-rows filter in this very report and then took the unfiltered "worst"
  at face value. The diagnosis it produced is still correct and still useful (the
  un-hoisted `Vec` header loads are real, and so is the preheader wall), but it was
  not the highest-value target and should not have been chosen without checking
  resolvability first.

## The `h1_vec_push_sum` diagnosis (sub-resolution; kept for its mechanism)

One program carries the whole per-program gap. Ranked by runtime vs LLVM -O3:

| program | category | runtime/O3 | compile/O2 |
| --- | --- | ---: | ---: |
| **h1_vec_push_sum** | heap | **2.611** | 1.248 |
| b1_mispredict | branch | 1.157 | 1.263 |
| p4_matmul | vectorizable | 1.094 | 1.293 |
| h4_vec_dropper | heap | 1.082 | 1.255 |
| h2_vec_grow | heap | 1.080 | 1.257 |
| p6_branch_match | scalar | 1.035 | 1.272 |
| p2_collatz | scalar | 1.025 | 1.263 |
| p8_closure_nest | scalar | 1.000 | 1.262 |
| m1_call_chain | multifn | 0.9996 | 1.262 |
| p1_xorshift | scalar | 0.9986 | 1.262 |
| p5_struct_acc | scalar | 0.9976 | 1.257 |
| h3_box_leak | heap | 0.9964 | 1.253 |
| p3_gcd | scalar | 0.893 | 1.260 |
| v2_memfill | vectorizable | 0.885 | 1.295 |
| m2_call_heavy | multifn | 0.745 | 1.265 |
| p7_sieve | vectorizable | 0.727 | 1.289 |
| v1_saxpy | vectorizable | 0.651 | 1.292 |
| **v3_popcount** | vectorizable | **0.0997** | 2.037 |

Drop `h1_vec_push_sum` and the worst program becomes 1.157x. So this is one
defect, not a broad deficit — and `v3_popcount` at 0.0997x (TEN times faster than
LLVM -O3) shows the backend is not uniformly behind.

### Where the 2.611x goes

The program's cost is one loop: 300 passes over 300 000 elements is **90 million**
iterations of `acc = acc.wrapping_add(v[k]); k += 1` under `k < v.len()`. The push
loop is 300 000 iterations and is noise beside it. Both disassemblies are retained
(`h1_vec_push_sum.llvm.disasm.txt.gz`, `…tcg…`); the two inner loops are:

```
LLVM -O3                                  trust-cg
movdqu (%rsi,%rdi,8),%xmm2                jae  20b3b            <- bounds check 1
paddq  %xmm2,%xmm1                        cmpq %rax,%rcx
movdqu 0x10(%rsi,%rdi,8),%xmm2            jae  20b5e            <- bounds check 2
paddq  %xmm2,%xmm0                        movq (%rdx,%rcx,8),%rax
addq   $0x4,%rdi                          addq %rax,%r14
cmpq   %rdx,%rdi                          addq $0x1,%rbx
                                          jmpq 20b0d            <- unconditional
4 u64 per iteration, 1 compare,           1 u64 per iteration, 2 compares,
2 accumulators, + scalar epilogue         + an unconditional branch back
```

### CORRECTED: it is ONE cause, and the other two are its symptoms

The first version of this section listed the bounds check and the missing
vectorization as two independent gaps. An isolating A/B shows they are not
independent — both are BLOCKED BY a third thing, which is the real defect.

`slice-vs-vec-probe.rs` (retained, with its disassembly) puts the SAME loop in two
functions, differing only in whether the pointer and length arrive as arguments or
must be loaded through a reference:

* `sum_slice(s: &[u64])` — ptr and len arrive in registers. trust-cg **VECTORIZES
  it**: `movdqu` into `xmm`, with `andq $0xfffffffffffffffc` rounding the trip count
  down to a multiple of four.
* `sum_vec(v: &Vec<u64>)` — identical loop text, but per iteration it emits:

```
movq (%r8),%rax        <- reload the Vec's buf field
movq (%rax),%rbx       <- reload the data pointer
movq (%r8),%rax        <- reload the Vec's buf field AGAIN
leaq 0x10(%rax),%rcx   <- address of len
movq (%rcx),%rax       <- reload len AGAIN
cmpq %rax,%rdx ; jae   <- bounds check
movq (%rbx,%rdx,8),%rax
```

FOUR loads per element exist only to re-establish `v.ptr` and `v.len`, which are
loop-invariant. That single failure to hoist them causes the other two symptoms
directly:

* **It blocks BCE.** `x86_bounds_check_elim` requires condition (3), an IDENTICAL
  comparison whose operands canonicalize to the SAME vregs. The guard compares
  against one `len` load and the check against a DIFFERENT `len` load, so they are
  different vregs and the pass correctly declines. The pass is not missing this
  shape — it is being handed a shape it cannot prove.
* **It blocks vectorization.** With `len` re-loaded inside the loop the trip count
  is not invariant, so the recognizer that fires for `sum_slice` cannot fire for
  `sum_vec`.

So the actionable defect is ONE: loop-invariant load hoisting for the `Vec`/fat
header fields through a `&Vec<T>` — establishing that the loop body cannot write
the header. Fixing it should let the existing BCE pass and the existing vectorizer
both fire unchanged, which is why it is worth far more than either symptom.

### Located exactly, down to the declining condition

The pass and the tier both already exist and are ON by default
(`x86_licm_load_hoisting_enabled`, kill switch `TCG_NO_LICM_LOADS`), so this is not
a missing pass. `x86_licm::hoistable_invariant_load` declines on ONE condition: it
accepts only an address that is *a fixed stack slot plus a static offset*, and
requires `info.allocation == StackSlotAllocationKind::Fixed` with the access
proven in bounds of that frame slot. `sum_vec`'s loads go through the `&Vec`
argument pointer — a heap address, not a frame slot — so they are refused.

The refusal is CORRECT as the pass is currently structured, and the module says
why: its pure tier deliberately hoists into a preheader that may run zero
iterations ("the value is simply dead"), which is safe for pure arithmetic and
UNSAFE for a load, since a zero-trip path would dereference an address the
original program never touched. A fixed frame slot is always mapped, so the
restriction is what makes the tier sound without any dominance reasoning.

The argument that licenses a POINTER base already exists in the tree, on the
AArch64 side: `alias_hoist` (LICM tier (c)) hoists loop-invariant loads whose base
is a runtime heap pointer, and earns fault-safety by requiring that the preheader
UNCONDITIONALLY enters the loop and that each hoisted load's block DOMINATES the
latch and every loop-exiting block — so the address is already dereferenced on
iteration 1 and the loop cannot be zero-trip. `alias_hoist` additionally emits a
runtime byte-range disjointness check because its target loop also STORES.

For `sum_vec` that second half is unnecessary: the loop contains no stores, calls
or barriers at all, so disjointness is trivial. The x86 extension is therefore
`alias_hoist`'s fault-safety argument WITHOUT its versioning machinery, gated on
"this loop writes no memory". The pieces missing on the x86 side are dominance
facts: `x86_licm` states that its IR has no predecessor list and no dominator tree
and that it never synthesizes a preheader, so the dominates-latch-and-exits check
has to be built (as `alias_hoist` builds it) rather than reused.

### ATTEMPTED AND REVERTED — the real blocker is the CONDITIONAL preheader

That extension was implemented and then reverted, because measuring it showed it
cannot fire on the shape Rust actually emits. Recording the outcome so the next
attempt starts from the wall rather than rediscovering it.

The tier was built exactly as specified above: an extra `LoadTierAnalysis` fact
(`no_memory_writers`, true only when NO instruction in the body writes memory,
inheriting the existing call/atomic veto) plus a `compute_fault_safe_blocks`
analysis deriving latches and exiting blocks from the predecessor map, and a
pointer-base arm taken where `resolve_frame_address` fails. It passed: four new
tests (one positive, three refutations — storing loop, in-loop base, call-bearing
loop), `trust-cg-opt` 3682/0, `trust-cg-codegen --lib` at the byte-identical
19-failure baseline, and 160/0 across 14 x86 correctness suites including the
cross-backend differentials and the triple oracle.

It also caught a genuine soundness limit on the way: the first version hoisted the
CELLED-POINTER FORWARDING chain that
`x86_licm_load_tier_forwarding_requires_non_escaped_cell` and
`..._requires_unique_cell_store` deliberately refuse. Those refutations are right
and the tier was tightened to require a base defined OUTSIDE the loop rather than
weakening them.

What it did NOT do is hoist anything in `sum_vec`, and the reason is structural.
Disassembling the loop shows the back-edge is `jb` to the BODY block, so the block
that tests `k < len` and branches to the exit is a *conditional preheader* with two
successors — enter the loop, or skip it. Fault-safety condition (1) requires the
preheader's ONLY successor to be the header, because hoisting into a
conditionally-entered preheader dereferences the pointer on the skip path, which is
exactly the fault the frame-slot restriction existed to prevent. So the tier
declines, CORRECTLY.

Every Rust loop over a container has that shape: the zero-trip guard makes the
preheader conditional. The positive unit test only fires because its helper builds
an unconditional `Jmp` preheader. A safety-critical tier in a hot pass that cannot
fire on real code is not worth carrying, so it was reverted rather than shipped
unexercised.

THE ACTUAL PREREQUISITE, therefore, is preheader SYNTHESIS — splitting the
guard's loop-entry edge so there is a block executed if and only if the loop is
entered, and hoisting there. `x86_licm` states it "never synthesize[s] a preheader
(CFG/Phi mutation is not sound here)", while AArch64 `alias_hoist` DOES create a
fast preheader as part of versioning the loop. So the capability exists in the
codebase's vocabulary and not in this pass, and closing `h1_vec_push_sum` means
bringing it here — a CFG-mutating change of a different size and risk class than
the tier itself, and the honest next step rather than a relaxed condition.

For the record, the symptoms as they appear in `h1_vec_push_sum`:

1. **The bounds check is not eliminated.** `k < v.len()` IS the loop condition, so
   `v[k]` cannot be out of range; LLVM proves that and drops the check. trust-cg
   keeps TWO conditional branches per element, one of them to a panic path. This
   needs the range fact from the loop guard to reach the index access — a dominator
   plus range argument, not a new proof obligation.
2. **The u64 reduction is not vectorized.** LLVM emits `movdqu`/`paddq` four
   elements at a time with two accumulators. trust-cg's vectorizer demonstrably
   works on this host — `v1_saxpy` 0.651x, `p7_sieve` 0.727x, `v3_popcount`
   0.0997x — so this is a recognizer gap for the indexed-load reduction shape,
   not an absent capability.
3. **The loop closes with an unconditional `jmpq` to its head** rather than a
   conditional backward branch, costing an extra taken branch per element.

None of the three needs an owner decision, a solver or a certificate: they are
ordinary backend optimisation work. Fixing (1) alone removes two branches from
every one of the 90 million iterations.

## The genuine per-program gap, diagnosed: `b1_mispredict` 1.157x is UN-COALESCED COPIES

This is the worst RESOLVABLE row (LLVM -O3 median 0.185s, comfortably above the
0.05s floor), so unlike `h1` it is a real target. Its hot loop runs 60 million
iterations of an RNG stream with two deliberately unpredictable branches and a
store into a `[u64; 16]` stack array.

What it is NOT: there is no redundant bounds check. `t[j]` with `j = (s>>4)&15`
compiles to a single `xorq %r12,-0xa8(%rbp,%rcx,8)` after `andq $0xf,%rcx` — the
mask is recognized and the check is gone. Nor is the branch layout at fault:
`x86_branch_layout` already applies its latch rule here (its own doc credits
`b1_mispredict -13%`), and it deliberately declines to swap the in-loop two-way
branch because both arms stay inside the loop and there is no profile to justify a
direction — the general fallthrough rule was REFUTED for exactly that shape.

What it IS, counted over `main` and then over the hot loop alone (both
disassemblies retained as `b1_mispredict.{tcg,llvm}-hot-loop.txt`):

| | LLVM | trust-cg |
| --- | ---: | ---: |
| `main`, total instructions | 81 | 115 |
| `main`, register-to-register `movq` | 6 | **23** |
| `main`, `lea` | 1 | 5 |
| `main`, nop padding | 1 | 3 |
| **hot loop, total instructions** | **35** | **49** |
| hot loop, reg-to-reg moves (`movq` only — BIASED, see below) | 5 | 15 |
| **hot loop, ALL reg-to-reg moves (`mov[lq]`)** | **7** | **15** |
| hot loop, `cmov` | 1 | **1** |
| hot loop, conditional branches | 2 | **2** |
| hot loop, unconditional `jmp` | 1 | 2 |

CORRECTED: the first version of this table counted only `movq %r..,%r..` and so
missed LLVM's 32-bit `movl` reg-reg copies, reporting 5 against 15 and "ten extra
copies". The honest figures are **7 against 15 — eight extra copies** — and the
14-instruction gap is eight copies plus six other instructions.

The same recount kills a tempting wrong answer. LLVM's loop contains
`cmovneq %r9,%rdi`, which looks like it if-converts the nested unpredictable
`s & 6 == 2` branch where trust-cg branches — that would be a large win in a
mispredict-bound loop. It does not: **trust-cg emits a `cmov` there too**, and both
loops carry exactly 2 conditional branches. Branch structure is equivalent and
if-conversion is NOT the gap.

Nor is this a coalescer failing, which the first version also claimed. Two reasons:

* The copies are not naively coalescable. `movq %r12,%rcx ; shrq $0x3,%rcx` keeps
  `%r12` LIVE — it is read again for the second shift — and `shr` destroys its
  destination, so a copy is genuinely required there given that register assignment.
  Coalescing is only available when the source dies at the copy.
* `post_ra_coalesce` operates on `PSEUDO_COPY` (phi-elimination copies), not on the
  `MovRR` that two-address expansion inserts, so it was never a candidate to catch
  these.

What LLVM actually does differently, read off its loop: it narrows to 32-bit ops
where the value provably fits (`movl %r8d,%edi ; shrl $1,%edi ; andl $0x78,%edi`) and
FOLDS the index scaling into the mask — `(s>>1) & 0x78` is `((s>>4)&15) * 8`, so it
addresses with `0x10(%rsp,%rdi,1)` at scale 1 where trust-cg computes
`shrq $0x4 ; andq $0xf` and addresses at scale 8. Same instruction count for that
sub-expression, but LLVM's register assignment then needs fewer live copies around
it.

So the target is not "fix the coalescer". Reading trust-cg's 49-instruction loop
line by line finds SIX instructions of concretely nameable waste, each with a
distinct cause, out of the 14-instruction gap:

1. **TWO DEAD INSTRUCTIONS.** In the else-arm,
   `209f9: movq %r13,%rcx ; 209fc: addq %rax,%rcx` computes an address that is never
   read: the next mention of `%rcx` is `20a07: movq %r12,%rcx`, a WRITE, and the
   flags `addq` sets are overwritten by `andq`/`cmpq` before any use. Verified by
   scanning every `%rcx` and `%r13` mention in `main` after that point. The store
   itself uses the rbp-relative form (`-0xa8(%rbp,%rax,1)`), so the `%r13`-based
   address is vestigial.

   MECHANISM CONFIRMED by tracing the vreg chain rather than guessing. Post-ISel,
   BOTH the load and the store of `t[j]` carry the same address chain:

   ```
   ImulRR v52 = v50 * v51        ; j * 8
   AddRR  v53 = v49 + v52        ; base + scaled
   MovRR  v54 = v53
   MovMR  [v54 + 0], v63         ; the store
   ```

   CORRECTION, and the mechanism is again NOT what I claimed. I attributed the
   orphaning to frame lowering running after the last DCE. That does not hold:
   `resolve_x86_stack_slots_in_operand` (x86_64/pipeline.rs) only rewrites a
   `[StackSlot + disp]` operand into `[RBP + resolved_disp]` — for both `MemAddr` and
   `SibMemAddr` — and creates or deletes NO instructions, so it cannot be what leaves
   a chain dead. The rewrite that orphans the chain must therefore happen inside the
   trust-cg-opt passes (the peephole SIB/addr-chain folds, or `x86_sroa` promoting the
   array), and DCE runs IMMEDIATELY AFTER the peephole in both pipeline sites
   (`X86Peephole` then `X86DeadCodeElimination`). Which pass orphans it, and why DCE
   then declines to sweep it, is NOT established — `AddRR` is in DCE's pure
   flag-writing allowlist and `MovRR` is in `x86_is_removable`, so the obvious
   explanations do not apply either. The dead pair is a measured FACT; its cause is an
   open question, and resolving it needs a dump between passes rather than more
   reading.

   At that point the chain is LIVE and DCE is CORRECT to keep it. In the final code
   the LOAD has been folded to
   `-0xa8(%rbp,%rax,8)` (scale 8, chain gone) while the STORE became
   `imulq $0x8,%rsi,%rax` plus `-0xa8(%rbp,%rax,1)` at scale 1, leaving the `add`
   chain with nothing reading it. The rbp-relative form is produced by FRAME
   LOWERING, which runs in `x86_64/pipeline.rs` AFTER the trust-cg-opt pass manager
   (`fixup_two_address` and the frame rewrites are pipeline code, not passes), and no
   DCE runs after it. The chain therefore becomes dead only from frame lowering
   onward, by which point the last sweep has already happened.

   Defect 3 below is the same event seen from the other side: the store ends up
   addressing at scale 1 with a pre-scaled index (`imulq $0x8,%rsi,%rax` then
   `-0xa8(%rbp,%rax,1)`) while the load addresses at scale 8 with the raw index
   (`-0xa8(%rbp,%rax,8)`), so one path folded the scale and the other did not. Both
   defects are real and measured; the fix cannot be specified until the orphaning pass
   is identified, and the earlier "sweep after frame lowering / fold the scale in the
   frame rewrite" prescription is withdrawn because frame lowering is not where this
   happens.
2. **A REDUNDANT COMPARE.** `20a0e: cmpq $0x2,%rcx` and `20a19: cmpq $0x2,%rcx` are
   the SAME comparison three instructions apart. The second is necessary only
   because `20a15: rolq $0x7,%rsi` sits between them and `rol` WRITES FLAGS,
   clobbering the first. LLVM emits one compare by ordering the flag-clobbering
   `rol` BEFORE it (`andl $0x6,%r8d ; movq %r9,%rdi ; rolq $0x7,%rdi ;
   cmpl $0x2,%r8d ; cmovneq %r9,%rdi`). This is a scheduling defect, not a missing
   transform: place the flag producer after flag-clobbering instructions.
3. **AN `imul` THAT SHOULD BE AN ADDRESSING MODE.** `209f5: imulq $0x8,%rsi,%rax`
   scales the index by 8 so the store can use `-0xa8(%rbp,%rax,1)` at scale 1 —
   while the SAME FUNCTION's other arm already folds it, addressing
   `-0xa8(%rbp,%rcx,8)` at scale 8 (and the else-arm's own LOAD at `209e9` uses
   scale 8 too). So the fold exists and is applied inconsistently: the store path
   misses it.
4. **`i += 1` COSTS TWO INSTRUCTIONS.** `20a21: leaq 0x1(%r8),%rax ;
   20a25: movq %rax,%r8` where LLVM emits `incq`. The `lea`-then-copy shape is the
   three-address form surviving into the emitted code.
5. **NOP PADDING INSIDE THE HOT LOOP.** `2099b: nopl 0x0(%rax,%rax,1)`, five bytes
   fetched 60 million times for an alignment that buys nothing at that position.

Four of the five are ordinary, local fixes — dead-code elimination after frame
lowering, one scheduling rule, one addressing-mode fold already present elsewhere in
the same function, and a strength-reduction of `lea`+`mov` to `add`. Only the
remaining eight-copy difference is the vaguer register-assignment question, and it is
now a MINORITY of the gap rather than the whole of it.

It still needs no owner decision and no new evidence: none of it changes a proof
obligation, and the always-on regalloc translation validator plus the x86 TV-4/TV-5
recheck already gate any change. Whether it is systemic across the corpus is
UNMEASURED — the clustering of resolvable rows between 0.998x and 1.157x is
consistent with it but does not establish it.

### Measured BEFORE building: the overhead is proportional, not mispredict-shadowed

The obvious objection to the copy theory is that this loop is
branch-misprediction bound by construction, so ten extra instructions might sit in
the shadow of the mispredicts and cost nothing. That objection is testable without
writing any compiler code, and it is the check that was skipped on `h1`.

`perf` counters are unavailable here (`perf_event_paranoid = 4`), so the probe is at
source level: the same program with both unpredictable tests (`s & 1`, `s & 6`)
replaced by predictable ones on the loop counter (`i & 1`, `i & 6`), everything else
identical. If the copies were hidden by mispredicts, removing the mispredicts should
WIDEN trust-cg's relative gap.

| variant | LLVM | trust-cg | ratio |
| --- | ---: | ---: | ---: |
| mispredicting (as shipped) | 0.18s | 0.21s | 1.167x |
| predictable branches | 0.06s | 0.07s | 1.167x |

Absolute time falls ~3x when the branches become predictable, confirming the loop
really is mispredict-dominated as designed — and the RATIO is unchanged. So
trust-cg's overhead is PROPORTIONAL to the work, not absorbed by the mispredict
shadow, which is what the extra instructions (including the ten copies) would
predict. Cutting the hot loop from 49 instructions to ~39 should therefore recover a
real fraction of the 17%, rather than nothing.

Held at arm's length, because the probe is coarse: these are best-of-three
wall-clock readings at 10ms granularity, and the predictable variant's 0.06s LLVM
baseline sits near the harness's own 0.05s resolvability floor, so THAT row is weak
evidence on its own. The mispredicting row (0.18 vs 0.21) is solid and reproduces
the harness's 1.157x independently. The conclusion this supports is directional —
the copies are not free — not a prediction of how much a coalescer would recover.

## The compile-time axis, diagnosed: 96% is ONE always-on refinement lane

The 1.301x compile ratio had no diagnosis at all. It has one now, and it is not
codegen.

First, the ratio is a FIXED cost, not proportional work. An empty `#![no_std]` lib
compiles in 1.52s under LLVM and 1.53s through the bridge — the backend's
initialization and its 121 MB dylib load are unmeasurable. A program that fails
type-checking is 0.02s in both lanes, so the dylib is loaded lazily at first
codegen. Yet `tiny.rs` (`fn main() { exit(0) }`) is 1.56s against 1.94s. Subtracting
the shared ~1.52s rustc frontend leaves the MARGINAL codegen cost:

| | LLVM | bridge | marginal ratio |
| --- | ---: | ---: | ---: |
| empty no_std lib | 1.52s | 1.53s | — |
| tiny bin | +0.04s | +0.41s | ~10x |
| corpus, 17 of 18 programs | +0.051–0.081s | +0.463–0.524s | **5.9x–10.1x** |
| `v3_popcount` | +0.061s | +1.700s | 27.9x |

The bridge's marginal cost is nearly CONSTANT at ~0.46s across programs of quite
different shapes, which is the signature of a per-compile charge rather than
per-instruction work. The observed 1.301x is that constant divided by rustc's ~1.5s
frontend.

`-Ztrust-ir-cg-args=time` names it exactly. On `tiny.rs`:

```
codegen_crate=402.0ms
  mir_to_trust_ir=392.5ms  fns=8  per_fn=49.07ms
    checks=391.1ms [ssa_loop=0.1ms definite_init=0.0ms
                    refine=391.1ms (p3c_scalar=390.7ms p1_lanes=0.0ms)]
  other_in_codegen_crate=9.4ms
x86 ISel + optimization + emit, all three CGUs:  ~6.9ms
```

**`p3c_scalar` is 390.7ms of 402ms — 97%** — while the actual x86 work is under 7ms.
On `h1_vec_push_sum`: 414.1ms of 432.7ms, 96%, 9 functions at 46.3ms each.
`v3_popcount` is the one program with a different story: `p3c_scalar` is 422.0ms
but `other_in_codegen_crate` is 1239.8ms, the popcnt SWAR certificate work, which
is why it alone reads 2.037x.

So the compile axis is ~46ms PER FUNCTION in one check, against LLVM's 50–80ms for
an entire program.

### CORRECTED: the 1.301x is the SOLVER refinement lane, which THIS SESSION enabled

The paragraphs above located the cost correctly and then drew the wrong conclusion
about what it is. `p3c_scalar` is not one always-on lane: the dispatch picks
between two, and the expensive one was reachable only because of a host change made
earlier in this same session.

```rust
let solver_lane = !ctx.emit_refinements
    && trust_cg_verify::ay_bridge::ay_available()
    && !crate::knobs::is_disabled(crate::knobs::REFINE_SOLVER);
```

* **FAST lane** (when no solver is reachable): only obligations the mock evaluator
  can decide COMPLETELY — ≤8-bit scalar ops, ≤2 inputs, no FP — exhaustively and
  with no solver, "cheap enough for every compile". Wider obligations are skipped.
* **DEFAULT SOLVER lane** (when a solver IS reachable): discharges EVERY obligation
  at all widths, so the 16/32/64-bit rvalue lowerings are genuinely verified. Its
  own comment records the cost: a SERIAL loop spawning one `ay` subprocess per
  distinct wide obligation, so the wall cost is ~sum(solve) plus a fork/exec of the
  ~90 MB `ay` binary per obligation.

`~/.cache/trust-cg` was mode 0775 on this host, so AY could not materialize and the
FAST lane ran. The `chmod -R go-w` applied earlier in this session (recorded in the
round-5 report) made AY available — which flipped this dispatch to the solver lane.
So the 1.301x is the price of the extra evidence that repair unlocked, not a
pre-existing codegen defect, and every compile figure in this report was taken in
that configuration.

Measured both ways, best of three per cell, same dylib:

| program | LLVM -O2 | bridge, solver lane | bridge, fast lane | fast ratio |
| --- | ---: | ---: | ---: | ---: |
| `h1_vec_push_sum` | 1.59s | 2.00s | 1.58s | **0.994x** |
| `p1_xorshift` | 1.57s | 1.98s | 1.57s | **1.000x** |
| `v1_saxpy` | 1.58s | 2.04s | 1.62s | 1.025x |
| `v3_popcount` | 1.57s | 3.23s | 2.80s | 1.783x |
| `tiny.rs` | 1.56s | 1.95s | 1.56s | **1.000x** |

`refine-solver=0` is the documented escape hatch for exactly this ("a
perf-sensitive build that still wants the always-on ≤8-bit op-selection coverage"),
and the binary it produces runs correctly. Note also that batching is ALREADY the
default — the knob is `no-refine-batch`, and `refine-batch` is not a knob name — so
the per-obligation spawn cost is what remains after batching.

**So the compile axis is an evidence/time trade-off with parity available at one
end, not a defect.** At the cheap end, ordinary programs compile at 0.994x-1.025x
of LLVM -O2, i.e. AT PARITY, with ≤8-bit exhaustive op-selection coverage only. At
the verified end they cost ~1.30x and every rvalue width is checked. The
verified end stays the default (OD-47 in the decision record, ruled
2026-10-02); the 1.301x headline belongs to it.

`v3_popcount` is unaffected by the choice in kind — 1.783x even on the fast lane —
because its cost is the SWAR certificate work, not refinement, and that cost buys
its 0.0997x runtime.

### What the check establishes

`p3c_scalar` is the scalar refinement lane in the MIR→trust-ir path. It is NOT
certificate generation: these numbers were taken with `no-proof-certs`, and the
solver lane (`p3c-refine`) was not requested. What ran is the **always-on fast
solver-free** refinement lane (`fast_refinements` in
`RustcCodegenTrustCg::refinements_active`), which checks that the trust-ir the
bridge emitted refines the MIR it was given.

That is load-bearing evidence, so the honest framing is that trust-cg buys its
refinement claim with roughly an order of magnitude of codegen time, and on these
small programs that purchase is 96% of the backend's cost. Two routes follow, and
they are not equivalent:

* **Make the lane cheaper.** Ordinary optimisation work, needs no decision, and it
  is where the whole compile axis lives. 46ms per function for functions this small
  suggests per-obligation overhead rather than intrinsic difficulty, but that is a
  hypothesis this report does not test.
* **Run less of it.** That trades evidence for time and is refused (OD-47).
  Nothing here proposes it.

Also worth separating: `v3_popcount`'s 1.24s of certificate work is a different
cost with a different owner, and it buys the 0.0997x runtime that makes it ten
times faster than LLVM.

## What this does not measure

No proof credit, and therefore no claim about the default lane. No `alloc`/`std`
corpus, no PGO or JIT lane, no Trust/TY/model-checker workload, and no comparison
against clang directly (the reference is LLVM through the pinned Trust compiler).
The RSS rows are largely floor-bound, so R1 losses are unmeasured. A ledger row
still requires the default lane, which requires XD-01.
