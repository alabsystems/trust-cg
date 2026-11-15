# The x86 vectorizer's legality gates were CLASS-SENSITIVE, which is fail-open (2026-09-29)

While looking for the trip-bound rematerialization that `h1_vec_push_sum` needs, I read
`is_reg_loop_invariant` — the gate that decides whether a loop's trip bound and data
pointer are fixed for the whole loop — and found it comparing the WHOLE TYPED `VReg`:

```rust
if x86_produces_value(inst.opcode)
    && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == c)
```

A `VReg` is `{ id, class }`. A write to the `Gpr32` view of a register clobbers the whole
register — `eax` clobbers `rax` — so a body `MovRR32 v{95,Gpr32}, x` is a write to
`v{95,Gpr64}`. The typed comparison does not see it, reports the register
**loop-invariant**, and the tier vectorizes a loop whose trip count the body is changing.

This is the direction that matters. The gate's `true` answer is a PREMISE ("the bound
cannot change, so bound == trip count"), so a missed def is **fail-open**: it admits
loops, it does not decline them.

`crates/trust-cg-opt/src/reaching_const.rs` already states the rule the rest of the
backend follows, and states why:

> Defs are matched by **id only**, ignoring the register class: a W-view write clobbers
> the X view and vice versa, so class-blind matching only ever ADDS reaching defs
> (fail-closed for uniqueness).

`x86_cse`, `x86_licm` and `x86_peephole` all use the audited table
`crate::effects::x86_may_defined_vregs` with `.any(|d| d.id == v.id)`. **`x86_vectorize`
was the only x86 pass not using it** — in the pass where a wrong answer is a miscompile
rather than a missed optimization.

## Second, independent under-approximation: operand 0 only

`x86_produces_value` answers for operand 0 alone. The audited table additionally reports
the `Xchg`/`Cmpxchg`/`AtomicRmwCasLoop` family, whose SECONDARY register operands are
also defs. That leg is screened for the reg-arg tier by its body-opcode whitelist
(`is_whitelisted_body_opcode` contains no exchange form), but a legality gate should not
depend on a caller's whitelist for its own soundness, and the same helper is called from
tiers with different whitelists.

`x86_produces_value`'s own doc records that this exact hazard class has already bitten
the project once: it used to be a `!matches!` blacklist, every opcode appended after it
silently answered `true`, and `StackAlloc` answered `false` although it writes its
destination — "so every def map built on this function" was wrong.

## What was changed

One new predicate, and five gates routed through it:

```rust
fn inst_defines_vreg_id(inst: &X86ISelInst, v: VReg) -> bool {
    if crate::effects::x86_may_defined_vregs(inst).any(|d| d.id == v.id) {
        return true;
    }
    x86_produces_value(inst.opcode)
        && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if d.id == v.id)
}
```

It is the UNION of the audited table and the (now class-blind) positional check, which
makes it a provable SUPERSET of the old def set — the table deliberately yields nothing
for proof-guard carriers, so keeping the positional arm means no opcode can lose a def it
used to report. **A superset can only decline more loops; it can never admit one the old
gate refused.** That is what makes this change safe to land without a proof obligation of
its own.

| gate | what a missed def used to do |
| --- | --- |
| `is_reg_loop_invariant` (5 call sites: trip bound, both data pointers, 2 window tiers) | report a varying register as invariant |
| `vreg_defined_in_body` (the k-nest tier's invariance gate) | same, for that tier's leaves |
| `iv_enters_as_zero` outside-def count (3 sites) | count too SMALL, so `outside_defs == 1` admits an entry value the packed-tail argument assumes cannot occur |
| reg-arg step 7, carried in-body def count | report the single writeback while a second, narrower write also modified `acc`/`iv` — and "exactly one writeback" is what makes reassociating the reduction exact |
| reg-arg step 8 + the k-nest carrier hygiene, escape scan | miss a body def that ESCAPES the loop; the packed path may skip the body's final execution, so the escaping value is stale |

The escape scans additionally match USES class-blind (`operand_references_vreg_id`,
and `outside_reads` reduced to ids): an outside read recorded at a different class than
the in-body def is precisely the mention the typed set drops.

Two gates were deliberately LEFT typed. The `dominated` scans that look for a def
dominating the preheader fail-CLOSED on a missed def (no dominating def ⇒ decline), so
class-blindness there would let a def of a DIFFERENT register satisfy the check — it
would weaken them. Direction, not uniformity, is the rule.

## The defect is real in the pass — proven, not argued

Three tests were added to `build_regarg_sumq_loop` via two new knobs:

* `rejects_regarg_len_redefined_through_narrow_width_view` — the body redefines the trip
  bound through `MovRR32 v{len.id, Gpr32}`.
* `rejects_regarg_inner_def_escaping_through_narrow_width_view` — a body def is read
  after the loop through its `Gpr32` view.
* `narrow_view_regarg_refutations_are_not_vacuous` — FALSIFIABILITY: the same builder
  with the knobs cleared MUST vectorize, so the knob is what declines the other two.
  (Both refutations assert a loop does NOT vectorize, which passes for free if the shape
  never vectorized at all — the trap this round has caught twice before.)

**Both refutations FAIL against the old def model.** Restoring the typed comparison and
re-running gives:

```
---- rejects_regarg_len_redefined_through_narrow_width_view ----
panicked: a narrow-width-view redefinition of the trip bound must stay scalar
---- rejects_regarg_inner_def_escaping_through_narrow_width_view ----
panicked: a body def escaping through its narrow view must stay scalar
test result: FAILED. 0 passed; 2 failed
```

So the old gate really did vectorize both shapes. This is a legality defect in the pass,
not a stylistic inconsistency.

## Cost: measured at ZERO, and reachability NOT claimed

The hardening can only decline more, so the question is whether it declines anything
real. Measured with an instrumented bridge that prints whenever the hardened predicate
sees a def the typed one would have missed:

| corpus | width-view divergences |
| --- | ---: |
| all 18 `beat-llvm` programs at O3 (each statically links all of `std`) | **0** |
| `library/core` at O3, 1278 objects | **0** |

So the change is **behaviour-neutral on everything measured**: no loop loses
vectorization, no performance risk. Confirmed independently — the 18-program execution
differential against LLVM is **18/18 MATCH**, and the per-program SIMD counts are
unchanged (p4 78 `paddq`, v1 6 `paddd`, h2/h4 65, p7/v3 63, baseline 62 from `std`).

**Reachability from real Rust input is therefore UNPROVEN.** These two corpora do not
produce a same-id-different-class def in a vectorizable loop, so what is fixed here is a
LATENT fail-open gate: real in the pass's logic, not observed to fire on measured input.
I am not claiming a miscompile was happening on this corpus, and the honest reading is
that the gate was one ISel change away from being wrong rather than wrong today.

It is still worth landing: the premise is load-bearing, the fix is provably conservative,
it costs nothing measurable, and review repaired a defect of exactly this class in my
`x86_cse` work earlier today — a 32-bit load failing to invalidate a tracked 64-bit
value. That one WAS a live miscompile.

## Also recorded

* `library/core` at **O3** has **6 failed roots** on 2 reasons — `Rvalue::RawPtr` (4) and
  `Rvalue::Ref aggregate source is unsupported ADT` (2) — with certificates off. The
  committed O0 census reports 0 in that lane, so these are O3-only lowering gaps and are
  unrelated to this change. Not previously recorded anywhere.
* `rust-toolchain.toml` now selects the `trust` channel (owner directive 2026-09-28), so
  root-workspace builds need an explicit lane: `targo --unverified test -p ...`. CLAUDE.md
  still describes the retired stock-1.97.1 pin.
* `trust-cg-codegen` has **2** pre-existing red tests on clean `main`, not 1:
  `compile_service_refuses_variadic_definition_with_shared_diagnostic` and
  `object_and_executable_payloads_disclose_the_spliced_bodies`. Verified by stashing.

## What this does NOT do

It does not close h1's gap. h1 still declines with `len_reg ... not loop-invariant`, and
that bail is CORRECT: the bound is a genuine reload from the `Vec` header inside the loop
header. Closing it needs the proven-safe dominating rematerialization upstream named —
emitting the bound's load into the vector preheader — which this change does not attempt.

One correction to my own earlier note while I was here: I had recorded that the
`vectorize-late` position "gets past" the trip bound and stops at `MovRMSib`. It does
not. The bail trace at the late position is the SAME
`len_reg VReg { id: 95, class: Gpr64 } not loop-invariant`. `MovRMSib` is the tier's
SECOND blocker, reached only after the bound check passes, and it is documented as such
in the tier's own source. All three vectorizer positions fail on the bound.
