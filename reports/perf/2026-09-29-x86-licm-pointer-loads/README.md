# h3_box_leak: the LICM pointer-base load arm goes DEFAULT ON, and a measurement that turned it off had to be RETIRED rather than repealed (2026-09-29)

`h3_box_leak` was 1.0954x LLVM -O3 — one of six programs above parity. It is now
**0.9993x**, closed by flipping a lever that had been DEFAULT OFF for one day on a
measurement that was correct when it was taken and had since stopped applying to
anything.

This report is mostly about that second part. The lever is four lines; the
methodological point is the reusable one.

## The lever

`trust_cg_opt::x86_licm`'s invariant-load tier has two arms. The FRAME-SLOT arm
hoists a load whose address resolves to a stack slot the loop provably never
writes. The POINTER-BASE arm hoists a load through a pointer *defined outside the
loop* in a loop that writes no memory at all — `pointer_base_load_is_hoistable`.
The second arm is the one that reaches a `Box`/`Vec` payload, because a heap
address is not a frame slot.

It was written on 2026-09-28, measured, and turned OFF the same day.

## The reading that turned it off, and why it was right

On `h1_vec_push_sum`, 41 runs each arm, one dylib with the arm toggled by knob:

| arm | median | vs LLVM -O3 | rel_spread |
| --- | ---: | ---: | ---: |
| ON | 33.79 ms | 3.685x | 0.066 |
| OFF | 23.21 ms | 2.531x | 0.186 |

**1.456x SLOWER**, far outside the spread. The arm did exactly what it claimed —
the hot loop went 18 instructions to 10 and six invariant loads became one — and
the loop still got slower. The disassembly said why: with the length load hoisted,
the allocator stopped keeping the data base in a register across the loop and
reloaded it from the frame each iteration (`mov -0x58(%rbp),%r10` then
`mov (%r10),%rsi`), converting two INDEPENDENT loads into a two-deep DEPENDENT
chain on the critical path. Classic LICM register pressure. Off it went, with the
number recorded as the baseline to beat.

Nothing about that is being withdrawn. It is still the correct reading of that
build on that program.

## Why it stopped applying — and why re-measuring was MANDATORY

`h1_vec_push_sum` now VECTORIZES (2026-09-29, three capabilities landing together:
the post-SROA vectorizer run, bound rematerialisation, and the own-length
proof — `reports/perf/2026-09-29-h1-vectorized-parity/`). Its scalar loop is now
the packed loop's remainder tail, entered at most three times.

So the program the lever was measured on no longer contains the loop that was
measured. The arm leaves h1's binary **byte-identical**.

That is the trap worth naming: a lever's default was justified by a regression on
program P, and a LATER, UNRELATED change removed P's regressing loop from the
corpus. The default is now resting on a fact about a loop that is not compiled any
more. Nothing fails, no test goes red, and the lever silently becomes
unjustified. **Every measured-OFF default acquires an expiry date the moment the
program it was measured on changes shape.**

## The re-measurement

First question: what does the arm still change? Both arms built for all 18
programs from ONE dylib, the arm toggled by its tracked knob, binaries compared
byte-for-byte:

```
DIFFERS    h3_box_leak
IDENTICAL  b1_mispredict h1_vec_push_sum h2_vec_grow h4_vec_dropper
IDENTICAL  m1_call_chain m2_call_heavy
IDENTICAL  p1_xorshift p2_collatz p3_gcd p4_matmul p5_struct_acc
IDENTICAL  p6_branch_match p7_sieve p8_closure_nest
IDENTICAL  v1_saxpy v2_memfill v3_popcount
```

**One program.** 17 of 18 byte-identical, so the arm's entire regression surface on
this corpus is `h3_box_leak` and the execution differential is 18/18 MATCH either
way. Whatever it does, it does it in one place.

Then h3, `taskset -c 2`, 40 INTERLEAVED rounds (one sample of every arm per
round, so drift hits all of them equally), the MINIMUM of each, and a
byte-identical copy of the ON binary carried in every batch as the noise floor:

| arm | hot loop | memory ops | bytes | min | vs LLVM -O3 |
| --- | ---: | ---: | ---: | ---: | ---: |
| LLVM -O3 | 6 insns | 2 | 16 | 23.554 ms | 1.0000 |
| arm OFF | 14 insns | 6 | 51 | 25.556 ms | 1.0850 |
| **arm ON** | **10 insns** | **3** | **32** | **23.287 ms** | **0.9887** |
| ON, byte-identical copy | — | — | — | 23.389 ms | 0.9930 |

**8.9% faster**, against a 0.43% floor from the identical copy. h3 goes from 8.5%
behind LLVM to matching it, and the three loads the arm removes were three of the
six memory operations in a 14-instruction loop.

Re-measured on the SHIPPING default binaries (not the A/B pair), with a second,
independently built LLVM reference carried as a second control:

| binary | min | vs LLVM -O3 |
| --- | ---: | ---: |
| LLVM -O3 | 23.272 ms | 1.0000 |
| **trust-cg default** | **23.140 ms** | **0.9943** |
| trust-cg default, byte-identical copy | 23.124 ms | 0.9936 |
| a second, independently built LLVM -O3 | 23.235 ms | 0.9984 |

The two independently built LLVM binaries agree to 0.16%, and trust-cg's margin
over LLVM (0.57%) is inside its own copy-to-copy floor (0.64%) — so the honest
claim is PARITY, not a win.

## The repo harness disagrees, and why the pinned measurement is the evidence

`benchmarks/beat-llvm/run.py` reads h3 at **1.052x** with the arm ON, and read it
at 1.046x with the arm OFF — i.e. it sees no effect at all. That disagreement is
resolved by looking at its own baseline: run.py's `llvm-O3` time for h3 was
0.0356 s on 2026-09-28 and 0.0263 s today, a **35% swing in the reference** on an
unchanged binary. A harness whose control moves 35% between runs cannot resolve
an 8.9% effect, and it publishes no noise floor with which to notice.

This is not a claim that run.py is wrong about the corpus — it is the right tool
for the 18-program execution differential, which is what it was used for here and
which is 18/18 MATCH. It is a claim about resolution: for a ~23 ms program, only
the pinned, interleaved, minimum-of-N measurement with a byte-identical control
in the batch can separate this size of effect from the machine, and that control
is what makes the reading falsifiable.

The pressure hazard the h1 reading found is real and still unmodelled. What these
numbers show is narrower and sufficient: on a loop whose base pointer stays in a
register, removing three invariant loads is a straight win, and that is the only
loop on this corpus the arm touches.

## What landed

* `pointer_base_loads_default()` returns TRUE. The knob inverted from the opt-in
  `licm-pointer-loads` to the opt-out `no-licm-pointer-loads`
  (`-Ztrust-ir-cg-args=`; it must be a TRACKED option, because `trustc` refuses
  every `TCG_*` environment variable).
* `with_invariant_load_hoisting()` now READS that default, so the pipeline, the
  library and every in-process test get one answer from one place. The pipeline's
  duplicate `.with_pointer_base_loads(...)` wire is gone.
* `x86_licm_pointer_base_arm_is_default_off` became
  `x86_licm_pointer_base_arm_is_default_on_and_its_opt_out_restores_the_load`,
  with the same assertion inverted under the builder opt-out as the falsifiability
  arm — without it a `MovRM` the pass never emitted would satisfy the default-on
  half vacuously. The opt-out is spelled through the builder and NOT through
  `set_pointer_base_loads_disabled`, because that installer is process-global and
  install-once: a test using it would decide the default for every other test in
  the binary.
* `pointer_base_load_is_hoistable`'s doc comment now carries BOTH measurements,
  the h1 one first, with why it no longer applies. A superseded measurement that
  is deleted cannot be audited.

One cross-reference was left standing deliberately.
`set_outer_iv_invariance_enabled` — a different, still-OFF lever — cites the h1
regression as its reason for staying opt-in. That citation is annotated, not
removed: the specific 1.46x reading is superseded for THIS arm, but the pressure
hazard it demonstrated is exactly why an unmeasured hoisting lever stays off.

## Verification

* 18-program execution differential: **18/18 MATCH** on the default build.
* Trust clause: the verification-ON corpus test (`trust_verified_corpus_x86`,
  23 strict-verified functions against an LLVM-built reference) **passes**.
* Lean-through-Clean: `clean_fixture_host_lowering` **5/5**.
* TY: `ty_bfs_minimal` **9/9**.
* `trust-cg-opt` library suite: **3862 passed, 0 failed**.
* `trust-cg-codegen` library suite: **4425 passed, 2 failed** — the two failures
  are the pre-existing `compile_service_refuses_variadic_definition_with_shared_diagnostic`
  and `object_and_executable_payloads_disclose_the_spliced_bodies`, both of which
  assert an AArch64 host and fail identically with this change stashed.

## Remaining

Five programs are still above LLVM: `b1_mispredict` 1.1199x, `p4_matmul` 1.0825x
(1.026x clang; most of that gap is gcc-vs-LLVM, not this backend),
`h4_vec_dropper` 1.0537x, `p2_collatz` 1.0190x, `h2_vec_grow` 1.0117x.

Two of those five were diagnosed while this was being measured, and the diagnosis
is recorded here because it names a capability rather than a tuning knob. Both
`h2_vec_grow` and `h4_vec_dropper` have, in their hot loop, a redundant reload of
a frame slot and a load immediately after a store to the same slot — three such
in h2, two in h4. Disassembly and the x86 ISel source together place them in two
different worlds:

* the `%r10`/`%r11` traffic is register-allocator SPILL code
  (`x86_spill_gpr_scratch_regs` reserves exactly those two), materialized long
  after every optimization pass runs, and the spiller emits each instruction's
  reloads immediately in front of it with no memory of the previous
  instruction's. Removing those needs a POST-RA reload elision — the x86
  counterpart of AArch64's `elide_redundant_spill_slot_reloads`, and a transform
  TV-5 will not police, because its documented v1 misses include spill-slot and
  memory dataflow.
* the `v.len`/`v.cap` traffic is ordinary program memory, and a pre-RA block-local
  forward would remove it — but only via a resolver, because x86 ISel emits a
  frame address ONLY as `Lea root, [StackSlot(s)+0]` and never as a direct
  `[StackSlot(s)+d]` operand. A pass matching the direct form alone is
  structurally incapable of firing: measured, 22 candidate loads in h2's `main`
  and 0 of them resolving to a slot.
