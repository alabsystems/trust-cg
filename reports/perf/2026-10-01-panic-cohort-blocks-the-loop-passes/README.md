# The v52 panic cohort and the x86 loop passes: what will need to change, and what must NOT

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux · main at `5e9780753`

This report exists because the refusal that landed in `1014261ee` names a second half of
its own problem, and that half is in `trust-cg-opt` rather than the bridge:

> Routing the failure edge to a raise block (as every other `AssertKind` below now does,
> `panic_edge_raises`) would replace the canonical compare/assert pair formerly fused
> into a guard carrier — **and consumed by NEON/x86 loop passes** — with a side-exit
> branch.

## Measured state

With the harness's `-Cpanic=abort`, **10 of 18** programs are `INCOMPLETE — bridge
fail-closed` (b1, h1, h2, h3, h4, p4, p7, v1, v2, v3), and `library/core` at O3 reports
**119 failed roots, all `[TCG-ASSERT-PANIC]`** (1165 objects), against 0 failed / 1284
objects earlier the same day. Merging all 247 commits since the refusal landed does not
restore them. The eight that compile: m1 0.999, m2 0.754, p1 1.000, p2 1.011, p3 0.893,
p5 0.996, p6 0.985, p8 1.001 — so only p2's 1.1% is a real performance gap among them.

## Which predicate the loop passes key on

`crates/trust-cg-opt/src/x86_trap_block.rs::is_pure_trap_block` is the single shared
definition used by `x86_vectorize`, `x86_bounds_check_elim`, `x86_branch_layout` and
`x86_cmov_swap`. It accepts a no-successor block that is, modulo pseudo padding, exactly
`[Ud2]` or `[Call Symbol("abort"), Ud2]` with no argument or result registers.

The heap vectorizer tier's `L5046` requires every off-chain edge from the loop body to
satisfy it. That is the gate under `h1_vec_push_sum`'s 1.887x, beneath the four already
cleared (`reports/perf/2026-10-01-h1-vectorizer-dialect-gates/`).

## The unwind lane's refusal is CORRECT — verified, not assumed

Under `-Cpanic=unwind` h1 compiles, and its bounds-check failure block is NOT a sink:

```text
  block 21 succs=[22, 25]   LeaRip <alloc157> ; MovRI 19 ; LeaRip <alloc159> ;
                            MovRR rdi.. ; Call <panic>
  block 22 succs=[]         Ud2
  block 25 -> 27 succs=[]   ... Call _Unwind_Resume ; Ud2
```

It has a live unwind successor into cleanup code that runs destructors. That is a live
exit, and refusing it is right. **There is no unwind-lane fix to make.**

## What the panic=abort shape will need, and the per-consumer proofs

When the faithful route lands, the failure block under `panic=abort` will be argument
setup plus a `-> !` call plus `Ud2`, with no successors. Accepting it needs
`is_pure_trap_block` widened, and the soundness argument is available: with no successors
AND a trailing `Ud2`, control cannot leave the block by any path, so it diverges
unconditionally exactly as shapes 1 and 2 do. It differs in doing observable work (it
prints a message), and that is admissible only because every consumer has independently
proven the guard cannot fail on the path it rewrites. Those proofs were checked, one by
one:

| consumer | its own proof |
|---|---|
| `x86_vectorize` | the packed footprint covers only `iv < vN <= len` |
| `x86_bounds_check_elim` | a dominating IDENTICAL compare |
| `x86_cmov_swap` | its doc: the check "is required to be IDENTICAL to a dominating one, so the trap's exact shape only serves to tell the trap edge from `cont`" |
| `x86_branch_layout` cold-trap | only REORDERS the edge; never drops it |

## Why this report instead of that change

I implemented the widening and **reverted it**. Two committed negative tests reject
exactly what it would admit:

* `rejects_call_to_other_symbol`
* `rejects_abort_call_with_registers_or_extra_operands`

and the module doc states the policy outright: "a call to any other symbol, a call with
argument or result registers, a successor edge — is refused". Those tests are a decision,
not an oversight. Loosening a safety predicate that four passes share, against committed
intent, to admit a shape the compiler does not yet emit, is the same move as the
`same_value_or_same_reload` relaxation that was reverted with its missing premise named.

So the widening belongs with the cohort that produces the shape, where it can be tested
against a real block instead of a synthetic one, and where whoever owns the panic
identity can confirm the payload is genuinely unreachable on each rewritten path. What
is recorded here is the inventory that work needs: the one predicate, its four
consumers, each consumer's existing proof, the exact shape to accept, and the two tests
that must be revisited deliberately rather than deleted.
