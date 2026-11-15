# The deref-store path had no thin-reborrow arm and an aarch64-only address arm: `library/core` at O3 goes 8 failed roots to 6 (2026-09-29)

Third step of the day on the `core` census, and the one that shows the method more
clearly than the result.

| step | roots | objects |
| --- | ---: | ---: |
| this morning | 16 | 1268 |
| ungate the thin-reference referent cell | 15 | 1269 |
| add the trait-object UNSIZE trigger to that cell | 8 | 1276 |
| **this change** | **6** | **1278** |

`FIXED 2` (`Waker::fmt`, `LocalWaker::fmt`), `NEW failures 0`.

## The two changes that landed

**(1) A thin-reborrow arm for the deref store.** `*place = &raw const (*r)` where `r`
is a scalar-bound thin reference: the address of the place `*r` IS `r`'s own pointer
value, so the stored value is a read of `r`. `lower_assign` has had this arm for the
non-deref-store case for a long time; the deref-store match did not, so the shape fell
to its fail-closed catch-all.

**(2) The address arm accepts `&raw` and lost its arch gate.** The arm that stores
`&local`'s address into a cell was `Rvalue::Ref`-only and gated to aarch64-linux. The
address of a non-deref place is the same whether spelled `&place` or
`&raw const place` — `memory_place_address_raw` is the helper the `&raw` arms in
`lower_assign` already use for it — and nothing in the arm is architecture-specific.

Both can only turn a REFUSAL into a lowering; neither changes code that already
compiled, on either target.

## How the shape was found, which is the reusable part

The catch-all said only `Place deref memory store from Rvalue::RawPtr`. That is an
anonymous bucket, and change (2) was made FIRST on the guess that the source was a
non-deref place — it built, and the census did not move at all (8 roots before, 8
after, 0 fixed). The guess was wrong and the diagnostic could not say so.

So the catch-all was taught to classify, exactly as the `&raw` catch-all in
`lower_assign` already does:

```
Place deref memory store from Rvalue::RawPtr (source local _12 projection [Deref]
  type &'{erased} task::wake::RawWakerVTable; dst ty PtrConst(Tuple([Ptr,Ptr,Ptr,Ptr]));
  base bound=true cell=false memory_backed=false entry_arg=false)
```

One reading names the shape — a `[Deref]` of a scalar-BOUND reference — and change (1)
follows directly. This is the third time today that adding classification bits to a
refusal turned an unsolvable bucket into a one-line diagnosis, and the second time it
refuted a guess that had already been implemented.

## A widening that was tested and NOT shipped

`memory_aggregate_ref_pointee`'s over-aligned-pointee path is gated to aarch64-linux
with no stated reason, and every condition in it is about the POINTEE's Rust layout
(over-16-byte alignment, struct or tuple, all-`Field` projection, scalar leaf) — it
looks like one more rollout gate. Ungating it was built and measured: `core` is
UNCHANGED (6 roots, same 4 reasons, 1278 objects, 0 fixed, 0 newly broken) and so are
all 18 runtime programs. It fires on nothing here.

It was therefore reverted, and the measurement is recorded at the gate itself. The
reasoning is the same one that deleted an arm earlier today: a widening that converts
a refusal into a lowering, with no measured firing and no test, ships an unexercised
soundness surface — if it is wrong it miscompiles exactly where the compiler used to
fail closed. Unlike that arm, this one IS constructible (an over-aligned struct behind
a reference with a field read), so the gate's comment now says to bring a test and then
remove it.

## The remaining 6, by capability

* **a by-reference pointee with a nested ARRAY field** — 3 (`Ty::[u8; 4]`,
  `Ty::[u8; 16]`, and the last `Rvalue::RawPtr`, all in the `Ipv4Addr`/`SocketAddrV4`
  formatting path). Pinned in `2026-09-29-core-ref-referent-cell/` to the
  `ty::Adt(struct)` arm of `aggregate_reference_pointee_to_trust_ir_ty`; blocked on an
  ABI contract three sites must agree on.
* **an addressable `slice::Iter` ADT** — 2 (`Rvalue::Ref aggregate source is
  unsupported ADT`).
* **a memory-eligible pointee for `VaListInner`** — 1 (`Place deref memory store from
  Rvalue::Ref`); NOT the over-aligned path above, which was measured not to be it.
