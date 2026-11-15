# `library/core` lowers completely at -Copt-level=3: 16 failed roots -> 0

Host x86-64 Linux, `trustc` stage2 + the bridge dylib, `panic=abort`, one dylib per
step, every step verified by SET DIFFERENCE of the emitted object sets rather than
by counts alone.

## The lane, stated precisely

This is the **LOWERING** census: does the backend produce an object for every
externally-required root, or does it fail closed? It is NOT the proof-credit lane.
`reports/perf/2026-09-28-linux-x86-64-core-census/` records that O0 `core` has
**3363 roots** whose lowering carries no proof credit, on one reason. That number is
untouched here and remains open. Zero failed roots means the backend compiles
`core`; it does not mean `core` is verified.

## Result

| lane | failed roots | objects |
| --- | ---: | ---: |
| O3, this morning | 16 | 1268 |
| O3, after the five earlier steps | 3 | 1282 |
| O3, + thin-ref aggregate address | 1 | 1284 |
| O3, + agreeing-lane pointee | **0** | **1285** |
| O0 (unchanged, already clean) | **0** | 44 |

Set difference across the last two steps: **3 objects gained, 0 lost.** The gained
objects are exactly the three roots named below. The O0 lane has always been 0 roots
/ ~45 objects (the 2026-09-28 census records 45), so it is unchanged.

## Root 1 and 2 — `SocketAddrV4`/`SocketAddrV6` `Display::fmt`

Refusal: the bare `Ty::[u8; 4_usize]` / `Ty::[u8; 16_usize]`.

Pinned with `bridge-notes` after two WRONG pins read off `trace-ty` backtraces
(see `2026-09-29-core-ref-referent-cell/`). The propagating chain ends at the
`Rvalue::Ref` address-taking arm, which on x86-64 fell through to
`memory_aggregate_ref_address(..)?.0` — a call that DISCARDS the leaf type but whose
computation demands a single scalar trust-ir leaf for the projection's final type.
`&self.ip` where `ip: Ipv4Addr { octets: [u8; 4] }` therefore reached
`rust_ty_to_trust_ir_ty([u8; 4])` and failed closed.

The fix was already written, one arch test away. The arm directly above it does the
right thing and says so — "The pointee can itself be an aggregate. A thin reference
stores its address, so no scalar-leaf load is required" — and was gated to
`aarch64` + Linux. That is the **14th aarch64-only capability gate** this campaign
has found in the MIR bridge and the 5th that accounts for real roots. Admitted for
x86-64 Linux; the three other predicates (`is_pointer_like_trust_ir_ty` on the
destination, the `is_sized` test on the source place, and the thin-reference
requirement) are unchanged and still load-bearing. Opt out with
`-Ztrust-ir-cg-args=no-x86-thin-ref-aggregate-addr`.

Note what did NOT work, because it looks obvious: adding `ty::Array` flattening to
`scalar_field_aggregate_trust_ir_fields`. The consumer accepts only a ONE-lane
answer and otherwise returns `Ty::Adt multi-field struct`, so `Ipv4Addr`'s four `I8`
lanes would have changed the refusal's text and nothing else.

## Root 3 — `<VaListInner as Debug>::fmt`

Refusal: `Place deref memory store from Rvalue::Ref (projected source's base is not
a reference to a memory-eligible aggregate)` — text that named none of the several
independent conditions behind it, which is why it stayed unpinned.

Classification bits were added to the refusal BEFORE proposing a fix, the discipline
this campaign settled on. They read:

```
source local _1 projection [Deref, Field(3, *const ffi::c_void)]
base ty &'{erased} ffi::va_list::VaListInner
pointee ffi::va_list::VaListInner is memory-eligible
base thin=true bound=false cell=false memory_backed=false entry_arg=true scalar_value=false
```

So the pointee IS memory-eligible and the base IS a thin entry-argument reference —
`memory_aggregate_ref_pointee` simply had no arm for this shape. The nearby arms
cover an ARRAY pointee, and a struct/tuple pointee whose declaration-order lane
offsets DISAGREE with rustc's. A struct whose offsets AGREE fell through all of them.

The codebase warns explicitly against widening this family: "a reordered
memory-backed struct accessed by reference is a separate, pre-existing gap in the
systemic declaration-vs-rustc-order frontier, to fix comprehensively, not
piecemeal", because "switching only its ACCESS to rustc order would BREAK it" for a
slot built at declaration order.

**That hazard requires the two orders to differ.** The admission added here is
guarded by exactly the property that rules it out: every field a memory scalar leaf
AND every declaration-order lane offset EQUAL to rustc's. When they are equal the
byte walker and the lane model are the same function, so the arm cannot move any
address — it only stops the shape from reaching the fail-closed catch-all. It is
therefore not the piecemeal order-switch the warning forbids. `VaListInner` is
`#[repr(C)]`, hence agreeing.

To express this, `lane_offset_mismatched_scalar_leaf_aggregate_pointee` was
refactored into a 3-way classifier
(`scalar_leaf_aggregate_pointee_lane_offsets -> Result<Option<bool>>`): `None` =
not this surface, `Some(true)` = disagrees, `Some(false)` = agrees. The old `bool`
could not express it, because `false` meant both "agrees" and "not this surface".
The original predicate is preserved as a thin wrapper so its existing caller is
unchanged. Opt out with `-Ztrust-ir-cg-args=no-x86-agreeing-lane-pointee`.

## Reproduce

```sh
cd trust
python3 scripts/trust_ir_cg_census.py --trustc build/host/stage2/bin/trustc \
  --crate core --opt-level 3 --panic abort \
  --backend <trust-cg>/target-bridge/release/librustc_codegen_trust_cg.so \
  --extra-flag=-Ztrust-ir-cg-args=no-proof-certs --out-dir /tmp/core-o3
# failed roots: 0; objects: 1285
```

Add `--extra-flag=-Ztrust-ir-cg-args=bridge-notes` to get the `[ty site:]` /
`[agg site:]` / `[leaf site:]` annotations that pin a refusal's propagating route.

## A dedicated differential for the agreeing-lane arm was attempted and NOT shipped

The arm's whole risk is a wrong byte offset, which only executing the code catches, so
a synthetic differential was written — fixture plus a falsifiability gate asserting
that `-Ztrust-ir-cg-args=no-x86-agreeing-lane-pointee` makes the bridge REFUSE the
same program, because a differential that cannot tell a correct lowering from a
fixture that never reaches the arm proves nothing.

**It is not shipped, because it never reached the arm.** Four attempts, each blocked by
a DIFFERENT and unrelated bridge gap in the fixture itself:

| fixture shape | blocked by |
| --- | --- |
| `&(*r).field` bound to a local, printed with `{:#x}` | `[TCG-FMT-DECLINED]` — a width/precision placeholder the `core::fmt` interception declines |
| same, printed with plain `{}` | compiled, but the opt-out ALSO compiled — the plain field borrow is handled by an earlier path, so the arm was never reached |
| `*out = &(*r).field` with `out: &mut &'a T` | `[TCG-FMT-ARGPLACE]`, then with printing removed `[TCG-SSA-071]` "value ValueId(15) used in bb5 is never defined" |
| `*out = &(*r).field` with `out: *mut &'a T` | `[TCG-MIR-UNSUPPORTED] borrowed scalar reference used without deref` |

Shipping the third or fourth as-is would have produced a test that fails for a reason
unrelated to the arm; shipping the second would have produced one that passes without
exercising it. Both are worse than none.

**What the arm's regression gate actually is**, therefore: the `library/core` census at
O3. `<VaListInner as Debug>::fmt` is the arm's real exercised instance, it is in the
1285-object set, and a regression drops the root count from 0. The opt-out knob remains
for forensics. This is weaker than an execution differential and is recorded as such.

**Four follow-ups fell out of the attempt**, each a real coverage gap independent of
this work and none of them previously written down: the two `core::fmt` interception
declines above, `[TCG-SSA-071]` on a `&mut &'a T` out-parameter, and "borrowed scalar
reference used without deref" on `&mut local as *mut &'a T`. The last two are ordinary
Rust out-parameter idioms.
