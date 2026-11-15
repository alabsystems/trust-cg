# A `library/core` capability was gated to aarch64-linux with no stated reason; ungating it on x86-64 takes the O3 census from 16 failed roots to 15 (2026-09-29)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The thin-reference referent cell — the mechanism that gives a `&T` local a real
address when a `&raw` of it is taken — was landed upstream this morning
(`ee201313a`, "fix(bridge): preserve live reference storage across raw pointer
conversions") behind

```rust
|| (ctx.tcx.sess.target.arch.desc() == "aarch64"
    && ctx.tcx.sess.target.os == rustc_target::spec::Os::Linux
    && matches!(referent_ty.kind(), ty::Ref(..)))
```

That commit carries a one-line message and the gate carries no comment, so there is
no recorded arch-specific fact behind it. On x86-64 it cost four `library/core`
roots.

## Result

`scripts/trust_ir_cg_census.py --crate core --opt-level 3 --panic abort` with
`-Ztrust-ir-cg-args=no-proof-certs`, both arms from ONE dylib via the tracked
`no-x86-ref-referent-cell` opt-out:

| arm | objects | failed roots | reasons |
| --- | ---: | ---: | --- |
| cell OFF (the gate) | 1268 | **16** | `DYN-REF-IDENTITY` 10, `Rvalue::RawPtr` 4, `Ref aggregate unsupported ADT` 2 |
| **cell ON** | **1269** | **15** | `DYN-REF-IDENTITY` 10, `Ref aggregate unsupported ADT` 2, `Ty::[u8; N]` 2, `Rvalue::RawPtr` 1 |

Three of the four `Rvalue::RawPtr` roots are gone and one more object is emitted.
The count moves 16 → 15 rather than 16 → 12 because two of the newly-compiling
functions get FURTHER and stop on a different, deeper gap.

## How the four roots were identified

The census only said `Rvalue::RawPtr`. The fail-closed diagnostic already printed
the source place's projection and type; this work added the two classification bits
it was missing (`cell=`, `memory_backed=`), which turned the reading into one line:

```
unsupported &raw shape: source local _4 projection [Deref]
  type &'{erased} &'{erased} net::ip_addr::Ipv4Addr;
  base bound=false cell=false memory_backed=false entry_arg=false
```

All four are `&raw const (*_r)` with `_r: &&Ipv4Addr` / `&&Ipv6Addr` / `&u8` /
`&&u16` — the `format_args!` `&&value` chain. `bound=false cell=false
memory_backed=false entry_arg=false` says the referent had NO address mechanism at
all, which is exactly what the ungated cell supplies.

## A wrong first attempt, and why its arm was REMOVED rather than kept

The first attempt assumed the source local was MEMORY-BACKED and added an arm for
`&raw const (*r)` with `r` in a slot — a real hole in the arm coverage, since
memory-backed thin `[Deref]` sat between the empty-projection arm and the
fat-reference arm. The `memory_backed=` bit added to the diagnostic refuted it on
the next census run: the local is in NONE of the four categories.

That arm was then deleted rather than kept, and the reasoning is worth stating
because it cuts the other way from the usual "keep the machinery" instinct. An arm
like this converts a REFUSAL into a lowering. With no measured firing and no test,
keeping it ships an unexercised soundness surface: if it is wrong it miscompiles
exactly where the compiler used to fail closed — strictly worse than an
unexercised optimization, which can only be slow. It is also not constructible on
demand (whether a given local ends up slot-backed is not under the test author's
control), so "add a test" was not available.

Removal was verified byte-neutral: all 18 runtime programs compile IDENTICALLY with
and without it, and the `core` census is unchanged (15 roots, the same 4 reasons,
1269 objects). It fired on nothing. If a future root reports
`memory_backed=true` with a `[Deref]` projection, that root is the arm's test and
the arm can come back with it.

## What the remaining 15 are, now sharply identified

* **`[TCG-DYN-REF-IDENTITY]` (10)** — the deliberate fail-closed rule `1048f47f3`
  landed today: unsizing a shared reference to an aggregate with no canonical
  referent address would change pointer identity and lose interior-mutability
  writes. The fix is the same shape as this one — give the referent real storage —
  but for an AGGREGATE rather than a thin pointer.
* **`Rvalue::Ref aggregate source is unsupported ADT: slice::iter::Iter<'_, u8>`
  (2)** — taking a reference to a two-field iterator local; needs that ADT in the
  addressable set.
* **`Ty::[u8; 4]` / `Ty::[u8; 16]` (2)** — NEW, and the more informative of the
  two newcomers. Pinned to an exact site with the tracked `trace-ty` knob, which
  prints a backtrace at each refusal. Of the six distinct call chains that reach
  `rust_ty_to_trust_ir_ty([u8; N])`, five are PROBES — `memory_scalar_leaf_ty(..)
  .is_ok()` and friends, whose `Err` is a test, not a propagation. The one that
  propagates is:

  ```
  rust_ty_to_trust_ir_ty  <-  aggregate_reference_pointee_to_trust_ir_ty
    <- reference_pointee_to_trust_ir_ty  <- mir_to_trust_ir_for_body_with_cells
  ```

  ⚠ **THIS PIN WAS WRONG, corrected later the same day; see below.**

### The correction, and how it was settled

The reading above blamed the `ty::Adt(struct)` arm of
`aggregate_reference_pointee_to_trust_ir_ty`, which does demand exactly one lane
per field and does trip on an array. But that arm's `Err` is CAUGHT:
`reference_pointee_to_trust_ir_ty` falls through to a last-resort memory-layout
route, and on a double failure it emits a COMBINED message —

```
{flattening error} [and the memory-aggregate lane fallback declined: {reason}]
```

— which exists precisely because a reasonless decline there once mis-attributed
fifteen `core` roots. That combined message appears **zero times** in the census
stderr, and the reason recorded is the BARE `Ty::[u8; 4_usize]`. So the flattening
arm is not what propagates.

What propagates is the `?` on the fallback itself:

```rust
Err(aggregate_err) => {
    return match memory_aggregate_reference_pointee_lane_ty_reasoned(tcx, ty)? {
        //                                                                  ^ here
```

an OUTER `Err` from the memory route goes out verbatim. The 274-occurrence
backtrace chain matches it exactly:

```
rust_ty_to_trust_ir_ty <- scalar_leaf_trust_ir_fields_inner
  <- scalar_field_aggregate_trust_ir_fields <- memory_aggregate_layout_shared
  <- memory_aggregate_reference_pointee_lane_ty_reasoned <- reference_pointee_to_trust_ir_ty
```

So the blocker is the MEMORY route's lane producer:
`scalar_field_aggregate_trust_ir_fields` flattens a struct or tuple into lanes but
has no `ty::Array` case, so `scalar_leaf_trust_ir_fields_inner` falls through to
`rust_ty_to_trust_ir_ty`, which refuses an array.

That is a better target than the arm first blamed, and for two reasons. It is the
route DESIGNED for this case — its own comment opens "An ARRAY POINTEE THE
SCALAR-FIELD FLATTENING CANNOT REPRESENT" and covers "the nested-field STRUCT
below". And the ABI worry cited above does not apply to it: that tuple describes a
SLOT, not a call contract, and the same comment says "every element access through
the reference routes over the REAL array/element layout (the runtime-index byte
walker + tag decode), never this tuple."

What it still needs, and why it was not done here: `ty::Array` support in a lane
producer with many callers, plus the element-count cap the sibling array arm
already carries (it records a `[u8; 4 << 20]` local driving 640 MB of RSS and a
2.0 s compile without one).

### Correction #2 — and this one is measured, not read

⚠ **The correction above is ALSO wrong.** It replaced one guess with another. The
route is neither `aggregate_reference_pointee_to_trust_ir_ty` (pin 1) nor
`memory_aggregate_reference_pointee_lane_ty_reasoned` (pin 2); NEITHER function is
on the path at all.

**Method that settled it.** `bridge-notes` appends `[ty site:]` / `[agg site:]` /
`[leaf site:]` to a refusal, and each note is captured with `#[track_caller]` *in
the frame that propagates the `Err`*. So the notes can only record the chain the
error actually travelled. That is the property a `trace-ty` backtrace lacks — it
also records `.is_ok()` probes, and this refusal had 315 distinct chains, five of
them probes. Both earlier pins came from reading those probe chains. The census was
simply re-run with `--extra-flag=-Ztrust-ir-cg-args=bridge-notes`, and both roots
carry one annotated reason:

```
Ty::[u8; 4_usize]  [ty site: src/lib.rs:101876] [leaf site: src/lib.rs:101759]
                   [agg site: src/lib.rs:102753] [ty site: src/lib.rs:113572]
Ty::[u8; 16_usize] [same four sites]
```

Innermost note first, so the real chain is:

| frame | site | what it is |
| --- | --- | --- |
| `memory_aggregate_ref_address_from_base` | `113572` | asks `walk_memory_projection_offset` for a projection's leaf type |
| `rust_ty_to_trust_ir_ty(Ipv4Addr)` | — | reached through the `#[track_caller]`-transparent walker |
| `rust_ty_to_trust_ir_ty_inner`, `ty::Adt(struct)` arm | `102753` | calls the flattener |
| `scalar_field_aggregate_trust_ir_fields`, struct arm | `101759` | one leaf per field |
| `scalar_leaf_trust_ir_fields_inner` | `101876` | `rust_ty_to_trust_ir_ty([u8; 4])` → `Err` |

So the consumer is the memory-projection ADDRESS walker, asking for the single
trust-ir leaf type of a projection that stops at `Ipv4Addr`.

**And the fix proposed in correction #1 is refuted.** Adding `ty::Array` flattening
to `scalar_field_aggregate_trust_ir_fields` cannot close these roots, because the
consumer at `102753` accepts only a ONE-lane answer:

```rust
Some(fields) if fields.len() == 1 => fields.into_iter().next().unwrap(),
...
Some(_) => return Err(format!("Ty::Adt multi-field struct {ty:?}")),
```

`Ipv4Addr { octets: [u8; 4] }` would flatten to FOUR `I8` lanes, so the refusal
would merely change text — `Ty::[u8; 4_usize]` becomes
`Ty::Adt multi-field struct Ipv4Addr`. Same root, same count.

**What would actually close them**, neither attempted: either (a) have the memory
projection walker DESCEND through the array leaf (element addressing over the real
array layout) instead of demanding one scalar for it, or (b) give `[u8; N]` a
memory-scalar spelling for small `N`, which is an endianness and ABI decision, not
a local edit.

**Standing method note.** Three pins, two wrong, and the two wrong ones were both
produced by reading a backtrace that mixes probes with the propagating path. For a
refusal that could come from more than one route, the site notes are the
measurement; a backtrace is a hypothesis.
* **`Rvalue::RawPtr` (1)** — `&raw const (*_5)` with `_5: &u8`, in the same
  `Ipv4Addr` formatting path. Its referent is an array ELEMENT, not a simple local,
  so the pre-pass's `ref_to_referent` map has no entry for it and nothing is
  celled. Blocked on the same `[u8; N]` support.

So three of the four remaining reasons now reduce to two named capabilities —
**fixed-size array aggregates** and **a canonical address for an aggregate
referent** — rather than four unrelated diagnostics.

## Verification

Retained: `gap_table-cell-on.md`, `gap_table-cell-off.md`,
`provenance-cell-on.json`, `stderr-cell-on.log.gz`. The 18-program execution
differential, the verification-ON Trust corpus, Clean, TY and both library suites
were run on the shipping default; see the commit message for the counts.
