# The faithful raise sink blocks the vectorizer — and the sink shape is NOT the soundness license

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux

## What changed upstream

`c876e3bd0` ("Restore source-kind Rust panic and foreign-abort cleanup paths") deletes the
`[TCG-ASSERT-PANIC]` bounds-check refusal and routes **every** MIR assertion's failure edge
through the new `src/assert_panic.rs`: `BoundsCheck { index, len }` →
`LangItem::PanicBoundsCheck`, with the queried `FnAbi`, the real caller-location argument,
and a diverging call. Unconditionally, native x86-64 included.

That is the right lowering — it is what makes a failed bounds check run the panic hook with
the real payload instead of dying in a generic trap. Its stated evidence, per the CLAUDE.md
note the same commit adds, is a **"fourteen-form ARM64/macOS differential"**. x86-64 has no
counterpart, and x86-64 is where the loop passes keyed on the old shape.

## What it costs here, and why

`reports/perf/2026-10-01-bounds-check-raise-trade/` measured this route before it became the
default (behind a now-removed opt-in). On the 8 programs that compile either way it is free
(largest move 1.7%); on the vector class it is **2.03x–54.93x**. The mechanism is a shape
mismatch, and it is worth being exact about where it bites.

### The raise block's actual shape

`assert_panic::emit` calls `lower_direct_call_args(ctx, body, block, …)`, which marshals
arguments **into the raise block itself**. So at ISel the block is not a sink of one or two
instructions; it is argument marshalling for `index`, `len` and `&Location`, then a `Call`
with three argument registers, then `Ud2`.

`x86_trap_block::is_pure_trap_block` admits exactly `[Ud2]` or
`[Call Symbol("abort") (no arg/result regs), Ud2]`. The raise block fails it three ways: the
symbol is not `abort`, the call carries argument registers, and there is real work before the
trap. Two committed negative tests (`rejects_call_to_other_symbol`,
`rejects_abort_call_with_registers_or_extra_operands`) pin exactly those refusals.

## The finding: every vectorizer site already proves the guard dead

`is_pure_trap_block` has 10 call sites in `x86_vectorize.rs`, all of the form
"every out-of-body successor must be a trap sink, else decline". The question that decides
whether they may admit a raise sink is **what actually licenses dropping that edge**. Reading
each site, it is never the sink's shape:

| sites (10) | the independent dead-guard proof |
|---|---|
| 1995, 2324, 3084, 4859, 9176 | `block_has_iv_bound_compare(.., iv, .., n_trip)` — whose own doc says "a bounds check that **provably never traps** for `iv in [0, n_trip)`" |
| 3669, 4321 | `classify_guard_compare` → `GuardClass::StaticOk`, or `GuardClass::Inv` + `record_obligation` (a hoisted **runtime** precondition) |
| 5879, 12939 | `chase_below_branch_cc`/`_either` guard matching: the guard's LHS must canonicalize to the loop `iv` AND its RHS must load the SAME `len` field the loop test uses |
| 10453 | `is_safe_iv_bounds_carrier` against the carrier's own bound |
| 14407 (string/substring tier) | explicit `proven_dead`, matching the guard's bound against `n` — and it calls `is_pure_trap_block` nowhere |

That last tier is the precedent that settles the design: it **does not call
`is_pure_trap_block` at all**. It proves the guard can never fail over every window the
vector loop replaces and records the edge in `proven_dead`. Its comment states the rule
plainly — the panic edge is "sound to drop from the VECTOR body only because the guard
proving it dead is matched here".

**So the sink-shape test is defense in depth everywhere in this pass, not the soundness
license.** Where the guard is proven never to fail, the failure edge is unreachable and what
its sink contains cannot affect any execution — `Ud2`, `abort()`, or a faithful
`panic_bounds_check(index, len, &Location)` alike.

## Therefore the fix, and the one real hazard

1. Add a second predicate beside `is_pure_trap_block` — do **not** loosen that one, whose doc
   promises the block "does no observable work" and whose contract other callers rely on. The
   new one admits a *divergent sink*: no successors, terminated by `Ud2`, exactly one `Call`,
   no stores and nothing else observable.
2. Admit it at the 10 vectorizer sites, as `is_pure_trap_block(..) || is_divergent_sink(..)`,
   and document at each that the dead-guard proof already present is what carries soundness.
3. **A hazard checked and found NOT to apply here.** The marshalling instructions *read
   vregs defined in the scalar body* (`index`, `len`), so a pass that discarded the body
   while the raise block survived would leave dangling reads. Checked: the `x86_vectorize`
   appliers neither delete blocks nor strip instructions (the one `insts.retain` that looked
   like stripping, at line 15261, is a **test fixture builder**). The scalar body and its
   raise block therefore survive with their definitions intact, unreachable but well formed.
   The hazard is real for any future pass that *does* delete, and for
   `x86_bounds_check_elim`'s orphan deletion (`if !has_pred && is_pure_trap_block(func, tb)`),
   which is left alone here and still recognises only the pure-trap shape.
4. `x86_cmov_swap` must be examined separately and is **excluded** until it is: it converts a
   branch into a conditional move, and a sink that must not execute is a different obligation
   from a sink that is merely unreachable.

## Status

Analysis only — nothing in this report is implemented. The soundness argument is settled and
the scope is bounded, but the predicate change touches four passes that elide guard failure
edges, and this lane has already shipped one hole this session by widening an admission
before its conditions were complete. The implementation gets its own commit, with the
negative tests written first.
