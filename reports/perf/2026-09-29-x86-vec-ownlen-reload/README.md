# The vectorizer's own-length identity, proved rather than assumed — and h1's real wall, located (2026-09-29)

h1's 2.488x is **1.9738x vectorization** x 1.1898x scalar quality (after the
[bounds-check win](../2026-09-29-x86-bce-pointer-reload/)). The vectorization half is by far the
largest single item left in the corpus, so this went after it. It did not close it, but it moved
the blocker three times and the wall is now named precisely instead of vaguely.

## The obligation, and why it was not assumed

The reg-arg reduction tier requires the OWN-LENGTH identity: the header's bound and every
per-element guard bound must canonicalize to the same vreg. For `while k < v.len() { .. v[k] .. }`
they do not — the header loads the length, the bounds-check guard reloads it — so the tier
reported CROSS-LENGTH. I had once relaxed that by asserting a write-free loop was enough;
**upstream reverted it and left the reason in the source**:

> Same-address loads need reaching-memory equivalence, not merely a write-free loop: a preheader
> store may separate the trip-bound load from the element guard's reload. Until that equivalence
> is established, retain exact copy-canonical register identity.

`same_ownlen_by_pointer_reload` establishes it instead of asserting it. It is the same argument
`x86_bounds_check_elim::same_value_by_pointer_reload` makes — measured at **11.1%** on this very
program earlier today — transplanted to this tier's premise:

* **Same address.** Both bounds are single-def loads of the same opcode whose addresses resolve to
  the same base expression and the same displacement.
* **The address cannot move.** The base's VALUE must be loop-invariant.
* **The memory cannot change.** NO store and no call anywhere in the loop body — scanned here,
  independently of the tier's own later store check, so the proof stands alone.
* **Why a preheader store cannot separate them.** Both loads are INSIDE the loop body, so a
  preheader store precedes both and affects them equally; and with `x86-vec-bound-remat` the
  replayed load sits on the preheader → header edge, after any such store. That is exactly the
  separation the retained comment guarded against, and it cannot arise for this shape.

Two supporting notions were needed, and both are narrow on purpose:

* `address_value_is_loop_invariant` — `is_reg_loop_invariant` asks "is there no definition in the
  loop", which an owning container's field address fails for an uninteresting reason: `Lea a,[p+16]`
  is recomputed in the header every iteration (exactly why the trip bound needs `BoundRemat`), yet
  its value cannot change because `p` is defined outside and `Lea` is pure. This admits an in-loop
  definition only for `Lea`/`LeaSib`/`MovRR`/`MovRR32`/`MovRI`/`AddRI` whose every register input is
  itself invariant. **Loads are excluded** — a loaded value's stability is a memory argument, and
  the caller makes that separately.
* `address_exprs_equal` — `canon` equates vregs only through copy chains, but an owning container
  computes the field address TWICE (`Lea ah,[p+16]` in the header, `Lea ag,[p+16]` in the guard).
  This decides structural equality: same opcode from the same short pure list, pairwise equal
  operands, immediates by value and registers recursively. It equates only identical operations on
  identical inputs, never two different computations that happen to agree at runtime.

DEFAULT OFF: `-Ztrust-ir-cg-args=x86-vec-ownlen-reload`. A wrong answer here elides a trap the
scalar program would take. Five tests, both directions: it admits two identical field-address
loads; and it refuses a different field offset, a store in the body, a call in the body, and a base
whose value is loaded inside the loop.

## What it achieved: the blocker moved three times, and is now named

Each step here came from `trace-vectorize-bail`, with the decline reason widened to report which
condition of the proof failed:

| # | bail | what it revealed |
| --- | --- | --- |
| 1 | `len_reg not loop-invariant and its header slice is not replayable` | the trip bound — closed by `x86-vec-bound-remat` |
| 2 | `(CROSS-LENGTH): own-length reload proof not enabled` | the own-length identity — this work |
| 3 | `(CROSS-LENGTH): header bound address is not an invariant base` | the base is a header `Lea` — closed by `address_value_is_loop_invariant` |
| 4 | `(CROSS-LENGTH): bound addresses differ: (v94,0) vs (v106,0)` | two identical `Lea`s — closed by `address_exprs_equal` |
| 5 | `(CROSS-LENGTH): MovMR in Block(11) writes memory` | **a real store in the loop body at the EARLY position** |

At the EARLY vectorizer position h1's sum loop is **not a pure reduction** — it still contains a
store, so the tier's central premise genuinely fails there and no amount of bound reasoning helps.

At the **post-SROA** position (`-Ztrust-ir-cg-args=vectorize-post-sroa`), where the store is gone,
**the own-length proof succeeds** and the tier advances past CROSS-LENGTH to its step 3, declining
with `load is neither an element address nor an invariant address`.

So h1's vectorization now needs, in order: (a) the post-SROA position, (b) the bound remat, (c) this
own-length proof — all three now exist — plus (d) step 3's load classifier extended to account for
the two bound loads it currently cannot classify (their bases are header `Lea`s, so
`invariant_load_addr` refuses them; the header's is already skipped via the remat slice, the
guard's is not), and then (e) the `MovRMSib` element spelling the tier documents as its remaining
blocker. (d) and (e) are the wall, and they are ordinary classifier work rather than a missing
theorem.

## Correctness

| check | result |
| --- | ---: |
| execution differential, default build | **18/18 MATCH** |
| `trust-cg-opt` lib suite | 3839 pass, 0 fail |
| clippy | 162, the pre-change baseline |
| effect on the default build | none — every lever added here is DEFAULT OFF |

## Status of the clause

Unchanged by this report: h1 2.3488x, b1 1.1326x, p4 1.0929x, p2 1.0191x versus LLVM. What it
adds is the premise upstream asked for, discharged rather than assumed, with tests — and h1's
vectorization wall reduced from "needs reaching-memory equivalence" to two named classifier gaps.
