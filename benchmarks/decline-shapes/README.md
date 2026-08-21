# decline-shapes — the `[TCG-SSA-071]` boundary, as minimal programs

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## Why

Roughly **38% of generated safe Rust fails closed**, and essentially all of it is
one diagnostic. Measured over bridge-fuzz seeds 24000–24059 at `-C opt-level=2`:
23 of 60 programs declined. Of the decline messages collected across three fuzz
runs, `[TCG-MIR-UNSUPPORTED]` turns out to be only the outer wrapper — the inner
cause is `[TCG-SSA-071]` in ~44 of 58 cases.

A percentage is not actionable. This pins the boundary as minimal programs.

| prefix | today | meaning |
| --- | --- | --- |
| `d_*` | DECLINE | a tracked gap; should flip to MATCH when the class is fixed |
| `ok_*` | COMPILE | the near-miss neighbours; must never regress |

## The rule

A loop-carried local declines when **its new value is computed from *another*
loop-carried local without involving its own previous value** — the
rotation / "last value" idiom.

```rust
while i < n { a = a.wrapping_add(i ^ p0); i += 1; }  // ok_carried   depends on self
while i < n { a = a.wrapping_mul(2);      i += 1; }  // ok_selfmul   depends on self
while i < n { a = i;                      i += 1; }  // ok_fromi     a pure copy
while i < n { a = p0;                     i += 1; }  // ok_constset  not loop-carried

while i < n { a = i.wrapping_add(p0);     i += 1; }  // d_lastval    DECLINES
while i < n { let t = i.wrapping_mul(p0); a = a.wrapping_add(prev); prev = t; i += 1; }
                                                     // d_prevval    DECLINES
while i < n { let t = x.wrapping_add(y^p0); x = y; y = t; i += 1; }
                                                     // d_twovar     DECLINES  (Fibonacci)
```

`a = i` compiles but `a = i + p0` does not, so it is not "reads another carried
local" — it is specifically a *computed* value that does not read its own phi.

## This is a latent wrong-code bug, not just a completeness gap

The diagnostic is not "cannot model this":

```
loop header bb1 param ValueId(9) (slot 0) is threaded the wrong value:
back-edge bb2->bb1 passes ValueId(14), which belongs to a different slot
  [semantic back-edge threading VC did not refine:
   REFUTED (counterexample: [("l3",0),("l2",1),("l1",1),("l0",0), ...])]
```

The semantic VC was **REFUTED with a counterexample** — the checker *proved* the
back-edge threads the wrong value into the header slot. `patch_loop_header_edge`
(`crates/rustc-codegen-trust-cg/src/lib.rs`) builds the args in header-param
order, so the ordering is right and the wrong value comes from the scalarized
out-state. Without this check these programs would MISCOMPILE. Fibonacci-style
rotation is not an exotic shape.

`TCG_P3C_REFINE=1` does **not** help: measured over the same 60 seeds it recovers
**0** declines (23 declined either way, 0 wrong answers introduced). The knob
targets the "in-loop diamond" sub-shape, which is a small minority here.

## Evidence the semantic VC OVER-REFUTES

The structural check cannot distinguish a genuine swap from a legitimate
rotation: for Fibonacci `x = y; y = t`, slot `x` receives `y_phi`, which is
*exactly* the signature check (2) fires on. That is why a semantic VC exists to
disambiguate — and on these shapes it returns REFUTED.

So: is the LOWERING wrong, or is the VC mis-modelling? That is testable — admit
the refuted VC and run the program against the LLVM oracle. Done with a
temporary diagnostic bypass (`TCG_UNSAFE_ADMIT_MISTHREAD`, **reverted, never
committed**):

| | |
| --- | --- |
| `d_lastval`, `d_prevval`, `d_twovar` | all MATCH LLVM |
| `d_lastval` over 40 inputs at O0/O2/O3 | MATCH |
| bridge-fuzz seeds 24000–24079 @ O2 | declines **40.0% → 25.0%**, 12 recovered, **0 wrong** |
| same seeds @ O1 and O3 | 25 more recovered, **0 wrong, 0 NONDET** |

**37 recovered declines across three opt levels with zero wrong answers and zero
nondeterminism.** The lowering produces correct code on every one; the VC is
refuting threading that is in fact value-correct.

### The exact trigger

`ssa_loop_complete.rs` check (2) computes, per header param `p_j`, the set
`in_loop_derivations(p_j)` — everything transitively computed from `p_j` inside
the loop — and says a back-edge arg "belongs to" slot `j` iff it equals `p_j` or
lies in that set. Slot `k` is flagged when its arg belongs to some other slot `j`
and not to `k`.

For a variable that is **overwritten rather than accumulated**, nothing in the
loop reads its phi, so `in_loop_derivations(p_k)` is **empty** — its own arg can
therefore never "belong to" its own slot, while the value it is assigned is
naturally derived from whichever other phi computed it. The check fires by
construction:

```
a = i + p0     derivations(a_phi) = {}          -> a_next belongs to no slot k
               a_next ∈ derivations(i_phi)      -> ...but does belong to slot i
                                                -> flagged as a swap
```

"derived from `p_j`" is strictly coarser than "is slot `j`'s next value":
`a_next = i_phi + p0` is derived from `i_phi` yet is not `i`'s next value
(that is `i_phi + 1`). The structural check is deliberately over-approximate here
— which is precisely why the semantic VC exists to rescue it, and precisely why
the VC's model is the thing to fix.

### What this does NOT mean

It does **not** mean the check should be removed or relaxed. Check (2) catches
genuine cross-slot swaps — `crates/trust-cg-verify/src/ssa_loop_complete.rs` has
`rejects_swapped_slot_threading` for `br bb1(%6,%5)`, an unsound misroute that
only a positional check finds. And exit-code agreement over 37 programs is
evidence, not proof.

The defect is in `semantic_backedge_threading_vc`
(`crates/rustc-codegen-trust-cg/src/lib.rs`): it returns `REFUTED` with a
concrete counterexample rather than "outside my slice", so it is building a model
and disproving it. For a rotation that runs correctly, that model does not match
the MIR semantics. Fixing the model — not weakening the gate — is what recovers
~15 points of decline rate.

## Usage

```sh
./run.sh
DECLINE_OUT=/tmp/x ./run.sh
```

Exits non-zero on any WRONG-ANSWER or on an `ok_*` regression. A `d_*` that
starts compiling and matching prints `PROGRESS`.
