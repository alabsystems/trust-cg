# Closing `p2_collatz`: a specification, not an attempt

> **AMENDED** after reading the PRE-RA form. The fix is simpler than the rotation described
> below — it is moving ONE instruction out of the loop, not carrying an extra register. The
> simpler statement is in "The actual transformation, post-RA" near the end; the rotation
> framing is kept because it explains the shape, but it is not what should be implemented.

`p2_collatz` is the smallest remaining parity gap — **1.017x vs clang**, 167.05ms against
164.18ms, `P(tcg<clang) = 0.000` so it is real. Its cause is now fully identified, and this
file specifies the transformation rather than attempting it. The reason for stopping at a
specification is given at the end and is about my error rate today, not about the problem.

## The two loops, exactly

Source: `while c != 1 { if c & 1 == 0 { c >>= 1 } else { c = c*3+1 }; steps += 1 }`.

clang, **8 instructions** (`c` lives in `%r8` AND `%rsi`):

```text
  lea    (%r8,%r8,2),%r9     ; r9 = 3c        -- reads the OLD c from r8
  add    $0x1,%r9            ; r9 = 3c+1
  shr    $1,%rsi             ; rsi = c>>1     -- mutates the NEW c IN PLACE
  test   $0x1,%r8b           ; CF/ZF from the OLD c in r8
  cmovne %r9,%rsi            ; rsi = odd ? 3c+1 : c>>1   -- IN PLACE
  add    $0x1,%rdx           ; steps++
  mov    %rsi,%r8            ; ONE copy: rotate new -> old for the next iteration
  cmp    $0x1,%rsi
  jne
```

trust-cg, **10 instructions** (`c` lives in `%rcx`, recomputed into `%rdx`):

```text
  mov    %rcx,%rdx           ; COPY 1 -- make a mutable temp because SHR is two-address
  shr    $0x1,%rdx
  lea    (%rcx,%rcx,2),%rax
  add    $0x1,%rax
  bt     $0x0,%rcx
  cmovb  %rax,%rdx
  inc    %rsi
  mov    %rdx,%rcx           ; COPY 2 -- write the temp back to the carrier
  cmp    $0x1,%rdx
  jne
```

Both need the OLD `c` alive across the computation of the new one, because `lea` and the bit
test read it while `shr` destroys it. Both therefore pay one register-to-register move. The
difference is that **trust-cg pays two**: it copies IN at the top to obtain a mutable
temporary and copies BACK at the bottom, where clang copies once at the latch to ROTATE.

## The transformation

Not a peephole — a loop-carried register rotation, and it needs the preheader.

For a loop body of the form

```text
  tmp = carrier                    ; a copy whose only purpose is mutability
  <ops mutating tmp in place>
  <ops reading `carrier` (the OLD value)>
  carrier = tmp                    ; write-back at the latch
```

where `carrier` is loop-carried and its OLD value is read in the body, rewrite to carry two
registers:

* **Preheader:** initialise both `old` and `new` from the incoming value (one extra copy,
  paid once per loop entry, not per iteration).
* **Body:** mutate `new` in place; every read of the old value uses `old`.
* **Latch:** a single `MovRR old, new`.

Net: one copy per iteration instead of two, and the loop becomes clang's shape exactly.

## Side conditions

1. `tmp` is single-def (the top copy) and its only escape is the latch write-back.
2. Every in-body read of the old value is a read of `carrier`, and `carrier` is not written
   in the body except by that write-back.
3. The rotation copy at the latch must not sit between a flag producer and its consumer —
   `MovRR` writes no flags, so this is satisfied by placing it where the write-back already
   was.
4. **Width discipline.** The rotation and the reads must agree on register class. A narrow
   copy aliases the same underlying register at a different class, which is the exact hazard
   that produced a miscompile in my CSE change today
   (`../../2026-09-29-x86-cse-alias-fix/README.md`): any kill or redefinition test involved
   here must compare VReg `.id`, CLASS-BLIND, never the whole typed VReg.
5. The preheader must be the header's unique out-of-body predecessor, so the doubled
   initialisation runs on every entry — the same condition `find_preheader` already
   establishes for LICM.

## Expected gain, stated honestly

One instruction of ten in a loop that runs to completion for every `n < 2_000_000`. p2 is
1.017x, so the headroom is about 1.7%, and closing it exactly would put p2 at or just under
parity. It is NOT a large win; it is the smallest of the four remaining gaps and the only one
whose mechanism is this precisely pinned.

⚠️ And note the alignment caveat measured three times in this round
(`../2026-09-29-x86-scalar-gap-refutations/README.md`): removing one instruction from a hot
loop has twice been cancelled or reversed by padding appearing inside the body. This
transformation should be measured with its own lever and an interleaved A/B, not assumed to
pay because it shortens the loop.

## Why this is a specification and not a commit

This is register-allocation-adjacent, width-sensitive work. In this session review repaired
**six** defects in changes of mine, including a genuine wrong replacement where a 32-bit load
failed to invalidate a tracked 64-bit value — and I had read the governing rule
("CLASS-BLIND on the id") earlier in the same session without applying it. Side condition 4
above is that same rule. Writing this transformation carefully is a fresh-session task with
its own tests-first pass; writing it now would most likely add a seventh defect to a
correctness-critical area for a 1.7% gain.

## The actual transformation, post-RA (AMENDMENT — implement THIS)

Reading the pre-RA dump changes the diagnosis. Pre-RA there is **no top copy at all**:

```text
  Block(5):  MovRR v21, v12 ; BtRI v21, 0 ; Jcc AE -> even ; Jmp odd
  Block(6):  ShrRI v26, v12, 1 ; MovRR v27, v26            ; even arm, THREE-address
  Block(7):  LeaSib v29,[v12+v12*2] ; AddRI v31, v29, 1 ; MovRR v27, v31
  Block(8):  AddRI v13, v13, 1 ; MovRR v12, v27            ; latch: the PHI copy
```

The loop-top copy appears only downstream, from TWO-ADDRESS EXPANSION of the three-address
`ShrRI v26, v12, 1` (which becomes `mov v26, v12 ; shr v26, 1` because destination and source
differ), combined with IF-CONVERSION folding the diamond into a `cmov` so both arms' values
are computed and `v12` stays live across them.

And then the post-RA code contains a redundancy that is far easier to state than a rotation:

```text
  header:  mov %rcx,%rdx        <- FIRST instruction of the loop header
  ...
  latch:   mov %rdx,%rcx        <- makes %rcx == %rdx
           cmp $0x1,%rdx
           jne header
```

**The latch already establishes `%rcx == %rdx`, so on the BACK EDGE the header copy is a
no-op.** It is needed only on the ENTRY edge from the preheader.

So the transformation is: **hoist the header copy into the preheader and delete it from the
header.** One instruction leaves the loop. No extra register, no rotation, no new live range.

### Conditions to check (post-RA, all local)

1. The header's first instruction is `MovRR a, b`.
2. The latch's last non-terminator instruction is `MovRR b, a` — the inverse copy.
3. Nothing between that latch copy and the header's first instruction writes `a` or `b`. In
   `p2_collatz` the only things there are `cmp $0x1,%rdx` (reads `b`, writes flags) and the
   terminator, so this holds.
4. The header's ONLY predecessors are the preheader and the latch, and the preheader is the
   unique out-of-body predecessor (the condition `find_preheader` already establishes).
5. Width discipline, as in condition 4 of the original spec: the two copies must name the
   same registers at the same class, and any redefinition test must compare VReg `.id`
   CLASS-BLIND — the rule whose violation produced a miscompile in my CSE change today.

### Why it is still not committed tonight

Unchanged from below: this is post-RA editing of final code in a backend where review
repaired six defects in my changes today, including one in exactly this width-sensitive
class. It is a ~15-line transformation with five local conditions and should be written
tests-first in a fresh session. The simpler framing above should make that materially easier
than the rotation I first described, which is the point of this amendment.

## Where it must go, and why the verifier is NOT a safety net there

I checked whether existing machinery de-risks this. It does not, and the reason is worth
recording because it is the opposite of what I assumed.

The transformation belongs in the x86 POST-RA RENAME site in
`crates/trust-cg-codegen/src/x86_64/pipeline.rs` (around the comment beginning "This is the
x86 analogue of `trust_cg_regalloc::post_ra_coalesce`'s rename phase"). That is the one place
that already deletes post-allocation copies and rewrites reads, operating directly on the
post-fixup `X86ISelFunction` because the VReg-keyed regalloc replay cannot carry
physical-register renames.

**TV-5 will not catch a mistake here.** Its own documentation in that comment says so
explicitly:

> TV-5 ... is defense-in-depth, NOT a license: it fail-closes tied-site misroutes and
> deleted two-address bridge copies with a `[TCG-POST-RA-DATAFLOW]` compile error, but its
> documented v1 misses (wrong-value renames of NON-tied use slots, spill-slot/memory
> dataflow) mean a bad rename of a PLAIN read would still miscompile SILENTLY — exactly the
> class the first draft of this pass exhibited before TV-5 existed.

So three things are true at once about this site: it is where the change must go; the
verifier does not cover the failure mode; and **this pass has already shipped that exact bug
once**. The surrounding conditions are described as carrying the soundness argument on their
own, at "64-bit-root granularity with x86 partial-register aliasing handled explicitly (a
partial-width read of the destination that cannot be rewritten to the source bails the whole
copy)" — which is the same partial-register/class hazard that produced the one miscompile
review found in my work today.

That converts "I would rather not do this tonight" into a documented reason: the area is
silently-miscompiling by construction, the guard rail does not guard this, and the specific
hazard is the one I demonstrably got wrong today. An implementer should port the existing
conditions rather than invent new ones, work at 64-bit-root granularity, and treat any
partial-width read as a bail — and should expect the review bar that this file's own history
implies.

