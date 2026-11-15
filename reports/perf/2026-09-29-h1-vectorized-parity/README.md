# h1_vec_push_sum reaches PARITY: 2.4890x -> 1.0037x LLVM, in the DEFAULT build (2026-09-29)

The corpus's worst program is no longer h1. Three capabilities built earlier today were flipped
DEFAULT ON together, and h1's owning-container reduction now vectorizes:

| | h1 vs LLVM -O3 | worst program in corpus | geomean vs LLVM -O3 |
| --- | ---: | ---: | ---: |
| before | **2.4890x** | 2.4890x (h1) | — |
| after | **1.0037x** | **1.1308x** (b1) | **0.8413x** |

`taskset -c 2`, 30 interleaved rounds, `min` plus a byte-identical control per program. h1's
control sits at 0.9989, so the 0.37% residual is about 3x its floor — parity to within a third of
a percent, from 149% slower.

## What was flipped, and why it needed all three

| capability | knob (now an OPT-OUT) | what it does |
| --- | --- | --- |
| post-SROA vectorizer run | `no-vectorize-post-sroa` | a SECOND run right after SROA, where an owning-container reduction first has a recognisable shape — the slice temp promoted, the peephole not yet having re-spelled the header test or the element address |
| trip-bound rematerialization | `no-x86-vec-bound-remat` | replays the header's bound-computing prefix into fresh vregs in the vector preheader, instead of USING a vreg defined only in a block VP0 precedes |
| own-length same-pointer proof | `no-x86-vec-ownlen-reload` | proves the header's bound and the guard's bound are one value when they load the same address in a write-free loop, instead of demanding exact register identity |

None of the three alone does anything for h1 — the bail simply moves. The early vectorizer
position cannot help at all, because at that point h1's sum loop still contains a store and so is
not a pure reduction. This is exactly the route the completion plan named:

> reaching LLVM's 4-wide SIMD needs the recognizer taught the two-level/invariant-vreg base+len
> form, **or the vectorizer moved after LICM**

## Upstream's refutation: converted, with its assertion retained verbatim

`rejects_regarg_header_length_reload_before_vector_entry` pinned this shape as refused. Its doc:

> The address is invariant and the loop never writes memory, but the sole length definition is in
> the original header. VP0 would use it before that header; **value invariance is not definition
> availability**.

That is a use-before-def objection, and the same review said admitting the shape "also requires a
proven-safe dominating rematerialization in the plan". The rematerialization now exists, and VP0
does not USE the header's vreg — it REPLAYS the header's prefix. So the test is now
`header_length_reload_is_replayed_into_the_vector_entry`, which asserts:

1. it vectorizes;
2. **no `AndRI` anywhere reads the header's own `len`** — i.e. the bound really comes from the
   replay, so the exact use-before-def the refutation refused is still refused;
3. and then, **verbatim, the original assertion** under the forensic opt-out: with
   `with_bound_remat(false)`, a header-only length must still not be read by an earlier vector
   entry.

The pin moved from "declines" to "declines unless the replay is present, and the replay is what
supplies the bound". Nothing was relaxed silently.

## A real unsoundness this work introduced, and the committed test that caught it

Worth recording plainly: my first own-length proof was **unsound**, and
`rejects_regarg_stale_preheader_length_reload` caught it on the first run after the flip. That
fixture is exactly the counterexample the retained CROSS-LENGTH comment described:

```
preheader:  MovMR [base] <- 3      ; store
            MovRM len,  [base]     ; the HEADER's bound reads 3
            MovMR [base] <- 0      ; store
guard:      MovRM glen, [base]     ; the GUARD's bound reads 0
```

Same address, and the loop body writes nothing — yet the values differ, because a **preheader**
store separates them. My proof scanned only the loop BODY for stores, on the reasoning that "both
loads are inside the body, so a preheader store precedes both". Here the header's bound is loaded
in the *preheader*, so that reasoning did not apply and the proof admitted a false equality.

Fixed by requiring **both loads to lie inside the loop body**, which is what makes the body-only
store scan sufficient: every instruction between them is then inside the scanned region. h1
satisfies it (header block and guard block are both body blocks).

This is the second time today an upstream refutation caught a defect in my reasoning, and in both
cases the refutation's stated reason was precisely right.

## Correctness, on the DEFAULT build

| check | result |
| --- | ---: |
| Rust — execution differential, 18 programs | **18/18 MATCH** |
| Trust — 23 strict-verified functions, verification ON | checksum `267826962111695130`, as expected |
| Lean-through-Clean — `clean_fixture_host_lowering` | **5/5** |
| TY — `ty_bfs_minimal` | **9/9** |
| `trust_verified_corpus_x86` (bridge, release) | **1/1** |
| `library/core` at O3 | 1278 objects, 6 pre-existing failed roots, 0 typed refusals, 0 harness errors — unchanged |
| `trust-cg-opt --lib` | 3839 pass, 0 fail |
| `trust-cg-codegen --lib` | 4406 pass, 2 fail — both PRE-EXISTING |
| fmt | clean |

Pass-schedule expectations were updated in three places (the O2/O3 schedule now carries a second
`x86-vectorize` after `x86-sroa`; `total_pass_runs` and `optimization_passes_run` go 17 -> 18),
each with the reason recorded inline rather than just the new number.

THREE PRE-EXISTING REDS, verified by stashing so none is mistaken for fallout:
`compile_service_refuses_variadic_definition_with_shared_diagnostic`,
`object_and_executable_payloads_disclose_the_spliced_bodies`, and
`opt_parity_x86::opt_level_parity_sweep_gate` ("PARITY-CLEAN 0 < floor 9" — identical with all
local changes stashed).

## Per-program state, DEFAULT build

| program | ratio | | program | ratio |
| --- | ---: | --- | --- | ---: |
| v3_popcount | **0.0995x** | | p1_xorshift | 0.9998x |
| v1_saxpy | **0.6499x** | | m1_call_chain | 1.0003x |
| p7_sieve | **0.7209x** | | p5_struct_acc | 1.0005x |
| m2_call_heavy | **0.7553x** | | p8_closure_nest | 1.0006x |
| p3_gcd | **0.8934x** | | v2_memfill | 1.0002x |
| p6_branch_match | **0.9792x** | | **h1_vec_push_sum** | **1.0037x** |
| | | | h2_vec_grow | 1.0103x |
| | | | p2_collatz | 1.0195x |
| | | | h4_vec_dropper | 1.0454x |
| | | | h3_box_leak | 1.0824x |
| | | | p4_matmul | 1.0922x |
| | | | b1_mispredict | 1.1308x |

## Status of the clause

Still NOT met, but the shape of what remains has changed completely. Six programs are above
LLVM: b1 1.1308x, p4 1.0922x, h3 1.0824x, h4 1.0454x, p2 1.0195x, h2 1.0103x. The 2.5x outlier is
gone, the worst case is 13%, and eight of eighteen programs now beat LLVM outright.

h3_box_leak and h4_vec_dropper appear on that list for the first time — they were previously
below the harness's 50 ms resolvability floor and unexamined, and their in-batch controls (1.0063,
1.0048) are now tight enough to read their gaps as real.
