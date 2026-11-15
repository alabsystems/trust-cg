# A trait-object unsize needs its referent's address, and the cell pre-pass only watched `&raw`: `library/core` at O3 goes 15 failed roots to 8 (2026-09-29)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

| | objects | failed roots | reasons |
| --- | ---: | ---: | --- |
| before | 1269 | **15** | `DYN-REF-IDENTITY` 10, `Ref` aggregate ADT 2, `Ty::[u8; N]` 2, `RawPtr` 1 |
| **after** | **1276** | **8** | deref-store `RawPtr` 2, `Ref` aggregate ADT 2, `Ty::[u8; N]` 2, deref-store `Ref` 1, `RawPtr` 1 |

Set difference, which is the claim that matters for a change that turns refusals into
lowerings:

```
FIXED (failed before, compile now):        7
NEW failures (compiled before, fail now):  0
```

The other three of the ten move to a DIFFERENT, deeper refusal rather than compiling
— named below. No function that compiled before this change fails after it.

## The defect

`materialize_trait_object_data_ptr` needs the referent's canonical address for the
fat pointer's data lane. When the referent is scalarized it has none, and the
function refuses — correctly, because a fresh copy would change pointer identity and
lose writes made through interior mutability:

> `[TCG-DYN-REF-IDENTITY]` unsizing a shared reference to `char` from a scalarized
> borrow has no canonical referent address. A fresh copy would change pointer
> identity and lose interior writes; failing closed.

The remedy the message itself names — "pass an existing thin reference whose referent
has real storage" — is a mechanism this backend already has: the scalar CELL. The
pre-pass that installs it was watching the wrong MIR shape. Its only trigger is a
`&raw` of the referent:

```
  _p = &raw const x                         <- the trigger it had
  _p = &raw const (*_r)   where _r = &x     <- and this one
```

whereas a trait-object argument is built with an ordinary borrow and then unsized:

```
  _r = &x                                   (Rvalue::Ref, no `&raw` anywhere)
  _d = move _r as &dyn Debug (Unsize)       <- the trigger it did not have
```

So the pass never considered these referents at all. Measured: ten failed roots, all
this message, on four referent types — `char`, `*const RawWakerVTable`,
`&*const c_void`, and a `CodeUnit` newtype. **Every one is a type the existing
predicates already admit.**

## The fix, and what it deliberately does not widen

A second scan over the body adds the unsize trigger: for
`Rvalue::Cast(PointerCoercion(Unsize), operand, dst)` with a TRAIT-OBJECT
destination and an unprojected reference operand, resolve the operand through the
same `ref_to_referent` map the `&raw` pass uses and apply the SAME three predicates
verbatim (`is_scalar_referent`, `is_pointer_scalar_storage_referent`, and the thin
pointer/reference one).

Reusing the predicates rather than writing new ones is the point: **no new type is
admitted.** A union, a `Vec`-as-`Ptr`, a needs-drop `Box`, a `core::fmt` plumbing
type, a wide-slice newtype carrier and every non-scalar aggregate keep failing closed
exactly as before. This adds a REASON to cell an already-admissible referent and
nothing else. Celling stays semantically inert for the reason the original pass
records: the construct and every whole-local assignment store into the cell, and
reads load from it.

A `[T; N] -> [T]` unsize is excluded — only a trait-object destination reaches
`materialize_trait_object_data_ptr`, and array unsizing takes a different path.

## What the three remaining ex-`DYN-REF` roots hit now

`Waker::fmt` and `LocalWaker::fmt` reach `Place deref memory store from
Rvalue::RawPtr`, and `VaListInner::fmt` reaches `Place deref memory store from
Rvalue::Ref (projected source's base is not a reference to a memory-eligible
aggregate)`. Both are the direct consequence of celling: the local now lives in a
slot, so a write to it is a store through a deref place, and that path does not yet
handle a pointer-valued rvalue source. That is a narrower and more local gap than the
one it replaced, and it is the next increment.

## The remaining 8, by capability

* **a deref store of a pointer-valued rvalue** — 3 (the two above plus its `Ref` form)
* **a by-reference pointee with a nested array field** — 3 (`Ty::[u8; 4]`,
  `Ty::[u8; 16]`, and the last `Rvalue::RawPtr`); pinned in
  `reports/perf/2026-09-29-core-ref-referent-cell/` to the `ty::Adt(struct)` arm of
  `aggregate_reference_pointee_to_trust_ir_ty`
* **an addressable `slice::Iter` ADT** — 2 (`Rvalue::Ref aggregate source is
  unsupported ADT`)

## Verification

Retained: `gap_table-before.md`, `gap_table-after.md`, `provenance-after.json`,
`stderr-after.log.gz`. The 18-program execution differential, the verification-ON
Trust corpus, Clean, TY and both library suites were run on the shipping default; the
counts are in the commit message.
