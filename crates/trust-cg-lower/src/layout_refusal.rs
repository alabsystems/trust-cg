// trust-cg-lower/layout_refusal.rs - M0.5 struct-layout refusal predicate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! M0.5 refusal predicate: does the producer's struct layout agree with the
//! layout the byte-generating path actually computes?
//!
//! # The defect this guards
//!
//! Two independent layout authorities exist on the Rust -> THIR -> `trust_ir`
//! -> trust-cg path, and today nothing compares them:
//!
//! * **Producer (authority A).** `trust-thir-lower` reads field offsets from
//!   rustc's **reorder-aware** layout — `tcx.layout_of(..)` then
//!   `l.fields.offset(i).bytes()`, at
//!   `crates/trust-thir-lower/src/lib.rs:9327-9329` (the mint site is guarded
//!   by `layout_query_is_reentrant_safe`, `lib.rs:9263`, which leaves
//!   `size`/`align`/every offset `None` for param/opaque types). Those offsets
//!   land in [`trust_ir::FieldDef::offset`]
//!   (`first-party/trust-ir/crates/trust-ir/src/ty.rs:709-712`, the `offset`
//!   field at :712).
//! * **Consumer (authority B).** The LIR type recomputes layout as
//!   **declaration-ordered natural C**: [`crate::types::Type::offset_of`],
//!   `first-party/trust-cg/crates/trust-cg-lower/src/types.rs:169-183`, walks
//!   fields in declaration order doing
//!   `offset = align_to(offset, f.align()); offset += f.bytes()`.
//!
//! For `#[repr(Rust)]` rustc is free to reorder fields by alignment, so A and B
//! diverge. The byte path never notices: `StructGep` lowers through
//! `Type::offset_of` (`isel.rs:9306`, `x86_64_isel.rs:13208`) and the **only**
//! non-test reader of `FieldDef::offset` in this crate is DWARF debug-info
//! emission (`adapter.rs:16357`). So for a `repr(Rust)` struct the adapter does
//! not otherwise reject, it **silently computes a different address than the
//! producer specified**.
//!
//! (a) DOC CLAIMS, from `designs/2026-08-03-trustir-to-lir-converter.md` §9.1
//! and §9.3, measured 2026-08-03 over a 69-crate corpus: 166 / 2,487
//! LIR-comparable struct defs with full producer offsets disagree (6.7%), 161
//! of them load-bearing, 100% `repr=rust`; `clean_kernel` alone 56 / 522
//! (10.7%). 1,039 / 5,197 struct defs (20.0%) carry no layout at all; MIXED
//! (some fields with offsets, some without) measured **0**.
//!
//! (c) MEASURED 2026-08-08 by running [`census_module_struct_layouts`] over 68
//! `trust-ir` module dumps (`cargo build --offline --release -p clean-kernel`
//! in the Clean workspace; 6,040 struct defs). This supersedes the figures
//! above as the live number for THIS predicate:
//!
//! | disposition | rows |
//! |---|---|
//! | `Agrees` | 3,331 |
//! | `Disagrees`, a non-ZST FIELD moves | 204 |
//! | `Disagrees`, no field moves | 47 (42 of them a SIZE/ALIGN divergence) |
//! | `LayoutAbsent` | 952 |
//! | `MixedOffsets` | 0 |
//! | `NotComparable` | 1,506 (`AdapterRejected` 1,184, `UnstatedInterior` 313, `PackedNoSingleAuthority` 9) |
//! | `StructIdCollision` | 0 |
//!
//! **That table predates the C1/C2/C3 corrections below and has NOT been
//! re-measured against them.** Three buckets move under the corrected
//! predicate and the direction of each is known, the magnitude is not:
//! the 9 `PackedNoSingleAuthority` rows are re-partitioned (a packed struct
//! whose clamp is a no-op now leaves the bucket and is compared; one matching
//! neither authority becomes the new refusal), and `StructIdCollision` can only
//! fall (the gate got strictly narrower). It was 0, so it stays 0. Re-running
//! the census needs a `trust_ir` corpus dump, which is not in the tree —
//! **not established** for this change.
//!
//! Two derived figures that the four headline buckets do NOT show, and that
//! [`StructLayoutDisposition::moves_bytes`] /
//! [`StructLayoutCensus::unrefused_exposures`] exist to make un-hideable:
//! **246 of the 251 disagreements relocate a byte that is really loaded or
//! stored** (only 5 are ZST-only), and **322 of the 1,506 `NotComparable` rows
//! are emitted with nothing blocking them** — the adapter rejects only the
//! other 1,184.
//!
//! Six classes are **absent from that corpus**, so their gates are sound but
//! unexercised by it and must not be quoted as "measured working": `Ty::Record`
//! fields (0), `Ty::Closure` fields (0, though 20 `ClosureTy` entries exist
//! unreferenced), `Ty::Refine` (0 entries in any type table), duplicate
//! `StructId`s (0 groups), offset-less structs that still record a size or
//! align (0 of 952 offset-less rows), and `MixedOffsets` (0).
//!
//! # WHAT THE DECLARED-OFFSET REPAIR CHANGED HERE (2026-08-08, later)
//!
//! The defect above is **closed for the offset half**. The byte path no longer
//! recomputes a struct's field offsets when the producer stated a complete,
//! coherent, emittable layout whose totals already match the recomputation: it
//! READS them, through [`crate::declared_layout`], and materialises
//! `base + offset` explicitly because `Opcode::StructGep` cannot express
//! anything but the recomputation. Authority D — the producer's own layout — is
//! therefore a real emitted authority, and `recompute_layout` asks
//! [`declared_authority`] first.
//!
//! Three consequences, and the third is the one to be honest about:
//!
//! 1. **The `Disagrees` population fell on its own.** (c) MEASURED 2026-08-08
//!    over the same 69-module corpus (69/69 deserialized, 6,051 struct defs):
//!    `Disagrees` **251 -> 54**, load-bearing **204 -> 12**, modules carrying at
//!    least one disagreement **42 -> 17**. `Agrees` 3,339 -> 3,522,
//!    `NotComparable` 1,509 -> 1,523 (rows that used to refuse at step 4 now
//!    reach the interior gate at step 7), `LayoutAbsent` 952, `MixedOffsets` 0,
//!    `StructIdCollision` 0 — all unchanged. No predicate gate was loosened to
//!    get there; the byte path genuinely stopped disagreeing.
//! 2. **Every one of the 54 survivors is a SIZE/ALIGN divergence**
//!    (`size_disagreements` = 54 of 54). That is exactly the population the
//!    repair's totals gate declines on purpose: the `#[repr(align(N))]` /
//!    128-bit / `CachePadded` / NEON-vector family, whose totals are read by
//!    consumers that only ever see the LIR `Type` (`abi::classify_params` on
//!    `sig.params`, byval slots, the small-aggregate `<= 16` decisions). They
//!    keep the recomputation and keep refusing.
//! 3. **For a struct authority D owns, this predicate is now VACUOUS**, and
//!    that is intrinsic, not hidden: the emitted layout IS the producer's, so
//!    comparing them can only agree. What that certification is still worth is
//!    the *authority selection* — [`declared_authority`] calls the same
//!    function the adapter calls, so if the adapter stopped honouring declared
//!    offsets these rows would go straight back to `Disagrees`
//!    (machine-checked by
//!    [`tests::test_a_reordered_struct_with_coherent_totals_is_now_emitted_as_declared`]).
//!    The check that the OFFSETS actually reach emitted instructions lives
//!    where it belongs, in `tests/declared_struct_layout.rs`, which reads the
//!    opcode stream out of the public `translate_function`.
//!
//! Naming note: the dedicated `TrustIrAdapter::packed_field_offset` /
//! `packed_struct_size` accessors were folded into
//! `TrustIrAdapter::explicit_field_offset` /
//! `TrustIrAdapter::aggregate_value_extent`, which select among all three
//! authorities in one place. Prose and refusal reasons below still name the old
//! accessors; they name the same authority-P path, which is otherwise
//! unchanged — a `#[repr(packed(N))]` struct is deliberately never handed to
//! authority D (see [`crate::declared_layout`] for why: it would close the
//! packed OFFSET split while leaving the packed SIZE split open).
//!
//! # What this module does
//!
//! [`classify_struct_layout`] maps one [`trust_ir::StructDef`] to a
//! [`StructLayoutDisposition`], and [`census_module_struct_layouts`] runs it
//! over a whole module so the disagreement becomes a **census row or a
//! refusal** instead of a wrong address. It deliberately compares against the
//! same conversion the byte path uses — each field type is routed through the
//! adapter's module-aware type translation and then measured with the byte
//! path's own layout authority for that `repr` — so it cannot measure a layout
//! nobody emits.
//!
//! # Which authority is B, per `repr`
//!
//! * `Rust` / `C` / `Transparent` — [`crate::types::Type::offset_of`] /
//!   `bytes()` / `align()`, the natural-C model `StructGep` lowers through.
//! * [`trust_ir::StructRepr::Packed`] — trust-cg lays a packed struct out TWO
//!   ways, so the question is asked **per struct, not per `repr`**: both
//!   authorities are computed and compared. `#[repr(packed(N))]` clamps each
//!   field's alignment to `min(natural, N)`, which is a NO-OP whenever no
//!   field's natural alignment exceeds `N`; for those structs the two
//!   authorities land on the identical offsets, size and alignment, there is
//!   one emitted layout after all, and the struct is compared like any other.
//!   Keying the gate on `repr` instead swallowed load-bearing refusals — (c)
//!   MEASURED 2026-08-08, `#[repr(packed)] { a: u8@0, b: u8@1, c: u8@7 }` was
//!   reported `NotComparable` while the reason it printed quoted BOTH
//!   authorities as `offsets [0, 1, 2], size 3, align 1`, i.e. it discarded two
//!   agreeing measurements and a producer that contradicted both. Pinned by
//!   `test_packed_whose_clamp_is_a_noop_still_refuses_a_moved_field`.
//!
//!   When they DO disagree, the verdict depends on the producer:
//!   - the producer matches exactly one authority — scoring means picking a
//!     winner, so the disposition is
//!     [`StructLayoutDisposition::NotComparable`] /
//!     [`NotComparableKind::PackedNoSingleAuthority`], naming both;
//!   - the producer matches **neither** — a TOTAL statement over both
//!     authorities that needs no choice between them, so it **refuses** as
//!     [`StructLayoutDisposition::PackedMatchesNeitherAuthority`], carrying
//!     both authorities in full.
//!
//!   (c) MEASURED, `#[repr(packed)] struct P { a: u8 @0, b: u64 @1 }`, size 9 /
//!   align 1 — the shape where the clamp really does bite:
//!   - `crate::adapter::packed_struct_layout` — the authority behind
//!     `TrustIrAdapter::packed_field_offset` (`adapter.rs:11549`, reached from
//!     `StructGep` at `:3302`, field insert at `:6934`, field extract at
//!     `:11654` and — since the 2026-08-08 repair — the aggregate-constant
//!     path at `:14541`) and `packed_struct_size` (`adapter.rs:11586`, packed
//!     array stride at `:3240` / `:6325`) — places `b` at **1**, total size
//!     **9**.
//!   - Natural C — `Type::bytes()` / `Type::align()` / `Type::offset_of` —
//!     says `b` at **8**, size **16**, align **8**.
//!
//!   **What the 2026-08-08 repair changed, and what it did not.** Authority C
//!   no longer emits any packed struct's FIELD OFFSETS:
//!   `fill_aggregate_at_ptr` was the last natural-C offset site for a packed
//!   struct and now routes through `packed_field_offset` like every other
//!   field-addressing path (`adapter.rs:14541-14570`), so the offset half of
//!   the split is closed. The SIZE/ALIGN half is not. Authority C survives as
//!   a size/align authority in:
//!   - `TrustIrAdapter::translate_alloc` (`adapter.rs:8958-8963`), which
//!     strides an alloca element by `lir_ty.bytes()` and aligns it by
//!     `lir_ty.align()` while `Inst::GEP` over the very same pointer strides
//!     by `packed_struct_size` (`:6325`). (c) MEASURED: `Inst::Alloca { ty: P,
//!     count: 2 }` reserves **32/8**; the packed authority says 9 per element.
//!     Pinned by
//!     `tests/packed_aggregate_constants.rs::alloca_stride_for_a_packed_struct_still_disagrees_with_gep_stride`;
//!   - `translate_heap_alloc` (`adapter.rs:9163`), the heap twin of that
//!     stride;
//!   - the aggregate-constant stack SLOT (`adapter.rs:14285-14287`) and the
//!     aggregate `Load` slot + copy length (`:8706`), which are EXTENTS rather
//!     than placements and are deliberately left at natural C — see
//!     **Named gaps**;
//!   - the aggregate-field `Memmove` LENGTH on the NON-packed `InsertField`
//!     arm (`:6989`), where the destination is a natural-C `StructGep` slot
//!     with natural-C room for it.
//!
//!   **What the nested-packed repair (same day, later) changed.** Two of the
//!   extents above moved to authority P, because they HAD to move with it: the
//!   aggregate-field `Memmove` on the PACKED `InsertField` arm and the
//!   aggregate `Store` arm now take their length from
//!   `TrustIrAdapter::aggregate_value_extent`, i.e. `packed_struct_size` for a
//!   packed struct. Before, `packed_struct_layout` advanced past a packed
//!   interior by its natural-C extent, which put the next sibling exactly flush
//!   against the end of the natural-C copy — `#[repr(packed)]
//!   { h: u8, inner: P, t: u8 }` placed `t` at 17 and the 16-byte copy into
//!   `inner` at offset 1 covered 1..17. Once the advance became `P`'s real 9
//!   (rustc: `t@10`, size 11), a natural-C-lengthed copy would CLOBBER `t`.
//!   Pinned by `tests/packed_nested_layout.rs`.
//!
//!   So for THAT struct there is still no single total size, certifying
//!   `Agrees` would still certify a struct the compiler sizes two ways, and
//!   this predicate still declines to pick a winner. It is now
//!   over-conservative on the OFFSET component, in the safe direction: a
//!   packed producer whose offsets contradict authority P is reported as the
//!   `PackedNoSingleAuthority` non-answer where it could now be refused
//!   outright. Tightening the predicate to score offsets against authority P
//!   alone is the named follow-up. See **Named gaps**.
//!
//! # Classification order (fixed, and load-bearing)
//!
//! 0. **[`StructLayoutDisposition::StructIdCollision`]** — `sdef.id` resolves,
//!    under the byte path's FIRST-MATCH rule (`adapter.rs:1250`,
//!    `structs.iter().find(|s| s.id == *sid)`), to a `StructDef` with a
//!    *different emitted layout*. Checked before everything else because it
//!    invalidates every subsequent measurement: no value of `sdef`'s type is
//!    ever addressed with `sdef`'s layout, so `sdef`'s own offsets are moot.
//!    The comparison is over `emitted_layout_identity` — `repr` plus the field
//!    TYPE sequence — not over `StructDef: PartialEq`. See **Id collision**.
//! 1. **Mixed offsets** — some fields `Some`, some `None`. Checked before any
//!    conversion because it depends only on producer data. Measured 0 today;
//!    the producer can still mint it (`trust-thir-lower/src/lib.rs:9328`,
//!    `.filter(|l| i < l.fields.count())`
//!    drops an offset for scalable-vector shapes), so it is detected and
//!    reported as a defect rather than assumed away.
//! 2. **[`StructLayoutDisposition::LayoutAbsent`]** — **nothing to compare at
//!    all**: no field carries an offset AND the producer recorded neither
//!    `size` nor `align`. Not an error; a distinct state the design requires.
//!    An offset-less struct that DOES record a size or an alignment falls
//!    through to the size/align comparison in step 4 — the producer mints all
//!    three from one `layout` binding
//!    (`trust-thir-lower/src/lib.rs:9269-9271`), but the offsets carry an extra
//!    bounds check the size/align do not (`lib.rs:9328`,
//!    `.filter(|l| i < l.fields.count())`): a struct whose layout reports FEWER
//!    field entries than the variant has — the `#[rustc_scalable_vector]`
//!    shape that check exists for — drops *every* offset while `size`/`align`
//!    stay `Some`. "Sized but offset-less" is therefore mintable, and its
//!    size divergence must not be swallowed by an early `LayoutAbsent`.
//! 3. **[`StructLayoutDisposition::NotComparable`]** — a field type that does
//!    not convert to LIR (so authority B has nothing to say), a LIR layout that
//!    is not representable in the byte path's `u32` arithmetic (see
//!    **Totality** below), or a `repr(packed)` struct whose two authorities
//!    genuinely disagree *and* whose producer matches one of them (see above).
//!    A packed struct whose two authorities disagree and whose producer matches
//!    NEITHER exits here instead as the refusing
//!    [`StructLayoutDisposition::PackedMatchesNeitherAuthority`]; a packed
//!    struct whose two authorities AGREE does not exit here at all and
//!    continues to step 4.
//! 4. Compare every field offset (skipped when there are none), then the
//!    struct's total size and alignment. Any divergence is `Disagrees`, and it
//!    **outranks** step 5 — a measured disagreement must refuse, and
//!    `NotComparable` does not.
//! 5. Only if everything measurable agrees: `LayoutAbsent` when no field
//!    carried an offset (the offsets went UNCHECKED — agreeing on the total
//!    size says nothing about where the fields sit); otherwise `NotComparable`
//!    for an *interior* the producer states no layout for (see **Interior
//!    gaps** below); otherwise `Agrees`.
//!
//! A struct with **zero fields** classifies as
//! [`StructLayoutDisposition::Agrees`] **vacuously** — there is no field that
//! can land at a wrong address, and a field-less struct's size/align are still
//! compared if the producer recorded them.
//!
//! # Id collision
//!
//! [`trust_ir::Module::add_struct`] honours declared ids verbatim with no
//! collision check, and the byte path resolves `Ty::Struct(sid)` by FIRST
//! MATCH. So when two `StructDef`s share an id, every value of the *later*
//! one is addressed with the *earlier* one's layout. When those layouts
//! **differ** that is strictly worse than a field disagreement and not
//! something either def's own offsets describe: measuring `sdef`'s own fields
//! would report a layout NOBODY EMITS, and re-resolving `Ty::Struct(sdef.id)`
//! would report another struct's layout as if it were this one's. Neither is
//! the truth, so it is its own disposition and it **refuses**.
//!
//! What counts as "differ" is the **emitted** layout, not the whole
//! `StructDef`. (b) CODE DOES: the byte path builds
//! `Type::Struct([translate(f.ty) …])` from the resolved def's fields and picks
//! the packed or natural-C authority from its `repr`. It never reads
//! `StructDef::name`, `FieldDef::name`, `FieldDef::offset`, `size` or `align`
//! to lay a value out. `StructDef: PartialEq` compares all of them
//! (`trust-ir/src/ty.rs:689`, `:691-692`, `:710`), so using it here refused
//! shadows that misaddress nothing — (c) MEASURED 2026-08-08: `Feet` vs
//! `Meters` (identical fields, different struct name), `T` vs `T` (identical
//! type and offset, different FIELD name) and `S` vs `S` (identical fields,
//! different producer `size`/`align`) all reported `StructIdCollision` with
//! `refusal=true` while every value of the shadowed type was addressed with a
//! byte-identical layout. The gate now compares `emitted_layout_identity`
//! (`repr` + the field TYPE sequence), which is exactly the condition steps 1-7
//! need in order to be measuring what the byte path emits — see that
//! function's docs for why nothing narrower is sound and nothing wider is
//! honest, and why the alternative (keep full equality, add a non-refusing
//! collision kind) was rejected: a producer offset that is wrong under a
//! harmless shadow is still wrong and must still refuse, naming the field.
//!
//! Once no collision is established, `sdef` and the def `sdef.id` resolves to
//! emit the same layout, so assembling the LIR type from `sdef`'s own fields
//! and resolving by id are provably the same measurement — and the field-wise
//! route is kept because it can name the offending field.
//!
//! # Interior gaps (measured, not silent)
//!
//! [`trust_ir::FieldDef::offset`] on a [`trust_ir::StructDef`] is the ONLY
//! offset carrier the producer fills, so producer offsets exist only for
//! `Ty::Struct` fields. These field types therefore have interiors this
//! predicate cannot score, and whose emitted layout is *synthesized*:
//!
//! * `Ty::Tuple` — lowered declaration-ordered natural-C by the adapter, while
//!   rustc reorders tuple fields exactly as it does struct fields. `(u8, u64)`
//!   is 0/8 on the byte path and 8/0 in rustc; the containing struct's offsets
//!   still agree because the sizes coincide.
//! * `Ty::Record` — the adapter lowers it to the *identical* synthesized
//!   `Type::Struct([field types...])` in declaration order
//!   (`adapter.rs:1406-1433`), and [`trust_ir::RecordDef`]'s fields reuse
//!   `FieldDef` with `offset` documented as ALWAYS `None`
//!   (`first-party/trust-ir/crates/trust-ir/src/ty.rs:596-598`). Same gap as
//!   `Ty::Tuple`, same synthesized aggregate.
//! * `Ty::Closure` — likewise `Type::Struct([capture types...])` in capture
//!   order (`adapter.rs:1443-1467`), and [`trust_ir::ClosureTy::captures`] is a
//!   bare `Vec<Ty>` with no offset carrier at all. rustc reorders closure
//!   captures exactly as it reorders `repr(Rust)` struct fields.
//! * `Ty::Enum` whose `EnumDef.layout` is `None` — the adapter fail-closes only
//!   when `layout` / `discriminants` / `repr` are PRESENT, so the common enum
//!   translates and gets LIR's canonical tagged-union layout, which is not
//!   rustc's (niche optimisation, tag placement).
//! * A nested **`#[repr(packed(N))]` `Ty::Struct`** — the one interior trust-cg
//!   provably lays out TWO ways (see **Which authority is B** above). The
//!   packed struct's own census row already declines to score itself; that says
//!   nothing about a CONTAINER, whose own offsets can only be recomputed with
//!   the natural-C authority. Gating only the struct's own `repr` let a
//!   container be certified `Agrees` over an interior addressed at two
//!   different sets of offsets.
//! * `Ty::Refine(base, _)` over any of the above. A refinement is
//!   REPRESENTATION-PRESERVING by construction
//!   (`first-party/trust-ir/crates/trust-ir/src/ty.rs:183-190`) and the adapter
//!   ERASES it, lowering the base carrier verbatim (`adapter.rs:1512-1522`).
//!   The scan must follow that edge, charging the same one level of depth the
//!   adapter charges it; not following it let a refinement hide any interior
//!   gap and mint a false `Agrees`.
//!
//! None can be *compared*, so none is reported as agreement: they are
//! `NotComparable` / [`NotComparableKind::UnstatedInterior`] with a reason
//! naming the field.
//!
//! # Totality
//!
//! `Type::bytes()` multiplies and accumulates in unchecked `u32`
//! (`types.rs:124` for `Array`, `types.rs:113-123` for `Struct`): debug builds
//! abort and release builds WRAP, and a wrapped offset can mint either verdict.
//! The predicate therefore proves the whole LIR type is representable
//! ([`layout_is_representable`], checked `u64`) BEFORE calling into the byte
//! path, and answers `NotComparable` otherwise. `types.rs` semantics are
//! deliberately left unchanged — the guard lives here.
//!
//! # Named gaps
//!
//! * **`repr(packed)`'s SIZE still has two authorities in trust-cg** (see
//!   above). The OFFSET half was repaired on 2026-08-08 —
//!   `fill_aggregate_at_ptr` now routes field addressing through
//!   `packed_struct_layout` — which closed a live wrong-value miscompile:
//!   the aggregate-constant path wrote field 1 of `#[repr(packed)] { u8, u64 }`
//!   at byte 8 while every read path loaded it from byte 1. Recorded in
//!   `designs/2026-08-03-trustir-to-lir-converter.md` §10; pinned by
//!   `tests/packed_aggregate_constants.rs`.
//!
//!   The SIZE half was deliberately NOT repaired in the same change, and the
//!   reason is a memory-safety one, not an oversight. The LIR `Type` carries
//!   no repr (`Type::Struct(Vec<Type>)`), so every consumer that measures an
//!   EXTENT of an aggregate value measures it with `Type::bytes()`. Shrinking
//!   the aggregate-constant slot to the packed size while those still copy the
//!   natural size would turn a wrong-value bug into an out-of-bounds read AND
//!   write. Keeping the slot natural is provably safe in the other direction:
//!   the packed clamp only ever LOWERS an alignment and every alignment is a
//!   power of two, so authority P is pointwise <= authority C on offsets, size
//!   and align — machine-checked by
//!   [`tests::test_packed_authority_is_dominated_by_natural_c`] and, for the
//!   nested shapes, by
//!   `tests/packed_nested_layout.rs::the_stack_slot_for_a_nested_packed_struct_stays_at_the_natural_c_size`.
//!
//!   **The nested-packed repair (2026-08-08, later the same day) closed part of
//!   the size half and named the rest.** `packed_struct_layout` itself was
//!   wrong: it advanced its running offset by the natural-C `Type::bytes()` of
//!   each field and clamped the natural-C `Type::align()`, so a field that was
//!   ITSELF packed was measured with an authority that does not apply to it.
//!   (c) MEASURED against stock `rustc 1.97.0`: `#[repr(packed)]
//!   N { h: u8, inner: P }` was 17 where rustc says 10, and
//!   `#[repr(C,packed(4))] { h: u8, inner: P }` placed `inner` at 4 where rustc
//!   says 1 — so with a clamp above 1 the OFFSETS were wrong too, not only the
//!   stride. Since the size IS the `Inst::GEP` element stride, `&[N]` indexing
//!   strode 17 over memory rustc laid out at 10. Repaired by recursing into a
//!   packed field's own packed layout for both its extent and its alignment.
//!
//!   That repair could not land alone, and the reason is the same
//!   memory-safety one: the natural-C over-report was exactly what kept the
//!   natural-C-lengthed aggregate-field copies inside their own field. The
//!   packed `InsertField` arm and the aggregate `Store` arm therefore moved
//!   onto `packed_struct_size` in the same change
//!   (`TrustIrAdapter::aggregate_value_extent`).
//!
//!   STILL natural-C, and still a live two-authority exposure: the
//!   alloca/heap element stride (`translate_alloc`, `translate_heap_alloc`),
//!   the aggregate-constant slot, the aggregate `Load` slot and copy length,
//!   the NON-packed `InsertField` arm's copy length, and the C ABI classifier.
//!   Unifying THOSE means moving the extents and the slot together, since a
//!   shrunken slot under a natural-C copy is an out-of-bounds write — on the
//!   heap path an out-of-bounds HEAP write.
//!
//!   Two further packed divergences from rustc are named, measured and NOT
//!   fixed, both pinned in `tests/packed_nested_layout.rs`:
//!   - an ARRAY or TUPLE of packed elements still contributes its natural-C
//!     extent to a packed container, because its ELEMENTS are still addressed
//!     at the natural stride by `ArrayGep`/`StructGep` on the repr-less LIR
//!     type. rustc: `#[repr(C,packed)] { h: u8, arr: [P; 2] }` is 19; trust-cg
//!     says 33. Reporting 19 while the addressing stayed natural would place
//!     the next sibling INSIDE the bytes element 1 actually writes — an
//!     overlap, strictly worse than an over-report;
//!   - a NON-packed struct CONTAINING a packed one is laid out natural-C with
//!     no packed authority consulted at all. rustc: `#[repr(C)]
//!     OuterC { h: u8, inner: P }` is 10/1 with `inner@1`, because `P`'s own
//!     alignment is 1; trust-cg says 24/8 with `inner@8`. The fix is in the
//!     repr-blindness of `Type::bytes()`/`align()`/`offset_of()` themselves,
//!     which every NON-packed path uses, so it cannot be made without moving
//!     non-packed output.
//!
//!   The bound that leaves on this predicate is narrower than "no packed
//!   struct is ever certified and no packed struct is ever refused" — that
//!   sentence used to sit here and was too strong in both halves. What holds
//!   is: **this predicate never picks a winner between the two authorities.**
//!   It certifies a packed struct only when the two authorities computed the
//!   IDENTICAL layout (so no winner exists to pick), and it refuses one only
//!   when the producer contradicts BOTH (so no winner needs picking). The
//!   population left unanswered is exactly the packed structs whose authorities
//!   disagree and whose producer matches one of them, and those are still
//!   `NotComparable` / [`NotComparableKind::PackedNoSingleAuthority`], still a
//!   live exposure, and still counted by
//!   [`StructLayoutCensus::unrefused_exposures`].
//! * **The offset half of the packed gate is now over-conservative** — named,
//!   not silent. Since the repair, authority C emits no packed struct's field
//!   offsets at all, so a packed producer whose offsets match authority C and
//!   contradict authority P states offsets NO path emits and could be refused
//!   outright. `recompute_layout` still compares the two authorities on
//!   offsets+size+align together, so such a row is reported as the
//!   `PackedNoSingleAuthority` non-answer instead. That is over-conservative
//!   in the SAFE direction (it under-refuses; it never certifies), exactly
//!   like the interior-gate asymmetry below. Scoring offsets against authority
//!   P alone while leaving the totals unscored needs a disposition for
//!   "offsets compared, totals not", which is a predicate-shaped change and
//!   was deliberately not bundled with a codegen fix.
//! * **The two packed gates are asymmetric, deliberately and namedly.** The
//!   struct's OWN gate (`recompute_layout`) now asks whether the two
//!   authorities actually disagree; the INTERIOR gate (`interior_layout_gap`'s
//!   `Ty::Struct` arm) still keys on `repr` alone, so a container of a packed
//!   struct whose clamp is a no-op is reported `NotComparable` /
//!   [`NotComparableKind::UnstatedInterior`] where it could be compared. That
//!   is over-conservative in the SAFE direction and it cannot swallow a
//!   refusal: step 4 compares the container's own offsets and size first and
//!   **outranks** step 7, so a real container disagreement still refuses. The
//!   cost is a slightly inflated `UnstatedInterior` / `unrefused_exposures`
//!   figure, not a false certification. Left unchanged rather than fixed
//!   speculatively alongside the gate that WAS swallowing refusals.
//! * **Reachability of the packed offset defect WAS ESTABLISHED** (2026-08-03,
//!   superseding the "NOT ESTABLISHED" note that stood here). (c) MEASURED
//!   from real `trustc -Ztrust-dump=ir` output, two distinct producer shapes
//!   emit `Constant::Aggregate` under a `StructRepr::Packed` type:
//!   `seed_lane_ty`'s `Ty::Struct(sid)` arm (`trust-thir-lower/src/lib.rs`),
//!   whose seed is then overwritten by an `InsertField` chain at packed
//!   offsets and so was MASKED; and `finalize_valtree_to_constant`'s struct arm
//!   (`trust-thir-lower/src/crate_module.rs:3160-3172`), which decodes a CTFE
//!   valtree straight into the constant with NO `InsertField` chain — the
//!   UNMASKED case. `pub const K: P = P { a: 7, b: 0x1122334455667788 };
//!   pub fn read_k() -> u64 { K.b }` stored the u64 at slot+8 and loaded it
//!   from slot+1, returning seven never-written stack bytes. That is the
//!   miscompile the 2026-08-08 repair closes. Whether the 69-crate corpus
//!   contains such a constant is still a corpus measurement not run here — no
//!   `trust_ir` corpus dump exists in the tree to grep — so no corpus-visible
//!   improvement is claimed.
//! * `NotComparable` and `LayoutAbsent` are census rows, not refusals;
//!   `StructIdCollision` is a refusal — see
//!   [`StructLayoutDisposition::is_refusal`]. That non-refusal used to be
//!   justified with "an unconvertible struct is already rejected by the
//!   adapter's own type translation", which is FALSE for three of the four
//!   [`NotComparableKind`]s and measurably so — only
//!   [`NotComparableKind::AdapterRejected`] has that property. The kind is now
//!   carried on the disposition and
//!   [`StructLayoutCensus::unrefused_exposures`] counts the rows nothing
//!   blocks.
//! * A `Disagrees` in which no FIELD moves is NOT the mild case.
//!   [`StructLayoutDisposition::is_load_bearing_disagreement`] counts moved
//!   fields, by design, so a diverging total size or alignment answers `false`
//!   there while relocating every array element past the first.
//!   [`StructLayoutDisposition::moves_bytes`] is the severity question.
//! * The interior scan follows the `Struct` / `Array` / `Tuple` / `Record` /
//!   `Closure` / `Enum` spine. Pointer pointees (`Ref` / `PtrConst` / …)
//!   deliberately are not followed, since a pointee's layout is not part of
//!   this struct's layout. It does not recurse into `Ty::Enum` variant
//!   payloads either: a descriptor-less enum is already the whole gap, and a
//!   descriptor-bearing one is refused by the adapter's own translation.
//! * The scan terminates on [`MAX_INTERIOR_SCAN_DEPTH`] alone. That bound now
//!   **fails CLOSED** (depth exhaustion reports a gap; it used to report "no
//!   gap", the one answer that certifies), and it is *defined as* the adapter's
//!   `MAX_TYPE_TRANSLATION_DEPTH` rather than copied from it, with
//!   `test_the_interior_scan_bound_is_the_adapter_translation_bound` pinning
//!   the coupling the unreachability argument rests on. It remains
//!   **unreachable in normal classification**:
//!   every edge the scan follows is also an edge the adapter's type translation
//!   follows, so a cyclic or over-deep type graph blows
//!   `MAX_TYPE_TRANSLATION_DEPTH` at step 3a first — measured, by neutering the
//!   bound and finding the suite (including a 200-deep struct chain) still
//!   green with no hang. It is kept as a *structural* totality guarantee, so
//!   `interior_layout_gap` is total without depending on the adapter, and it is
//!   deliberately not claimed as covered. What IS pinned is that step 3a is the
//!   authority that answers a cyclic struct
//!   (`test_a_self_referential_struct_is_answered_by_the_translation_depth_limit`).

use trust_ir::{Module, StructDef, StructId, StructRepr, Ty};

use crate::adapter::{
    MAX_TYPE_TRANSLATION_DEPTH, packed_struct_layout, translate_type_with_enum_tables,
};
use crate::declared_layout::{LayoutSource, LayoutTables, emitted_struct_layout};
use crate::types::Type;

/// Recursion bound for the interior scan.
///
/// **Defined AS the adapter's bound, not merely "mirroring" it.** The scan's
/// termination-and-unreachability argument is that every edge the scan follows
/// is an edge `translate_type_with_enum_tables` follows with the SAME depth
/// increment, so step 3a always reports first. That argument is only valid
/// while the two bounds are equal, and a stale copy of the number would make
/// the scan silently authoritative for depths the adapter still accepts. The
/// definition below makes divergence impossible, and
/// `test_the_interior_scan_bound_is_the_adapter_translation_bound` pins it.
const MAX_INTERIOR_SCAN_DEPTH: usize = MAX_TYPE_TRANSLATION_DEPTH;

/// One field whose producer offset differs from the recomputed LIR offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldOffsetMismatch {
    /// Declaration index of the field within the struct.
    pub field_index: usize,
    /// Declared field name, carried so a refusal can name the field.
    pub field_name: String,
    /// What the producer recorded (rustc's reorder-aware layout).
    pub producer_offset: u64,
    /// What [`Type::offset_of`] recomputes (declaration-ordered natural C).
    pub recomputed_offset: u64,
    /// `true` when the field's LIR type occupies at least one byte, i.e. real
    /// data moves. A disagreement that only relocates a zero-sized field
    /// changes no address that is ever loaded or stored.
    pub load_bearing: bool,
}

/// A struct whose producer-recorded **total size or alignment** differs from
/// the size/alignment the byte path computes.
///
/// This is NOT a field-offset mismatch and is reported separately: every field
/// can sit at the agreed offset while the struct's total size is wrong, which
/// is exactly what a niche-optimised enum field produces — the producer's
/// `Option<&T>`-shaped field is 8 bytes, the byte path's synthesized
/// tagged-union is 16. A wrong size is a wrong array stride, a wrong
/// allocation and a wrong `memcpy` length.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructSizeMismatch {
    /// `StructDef::size`, when the producer recorded one.
    pub producer_size: Option<u64>,
    /// What the byte path's layout authority computes for the whole struct.
    pub recomputed_size: u64,
    /// `StructDef::align`, when the producer recorded one.
    pub producer_align: Option<u64>,
    /// What the byte path's layout authority computes for the alignment.
    pub recomputed_align: u64,
}

impl StructSizeMismatch {
    /// `true` when the producer recorded a size and it differs.
    pub fn size_differs(&self) -> bool {
        self.producer_size
            .is_some_and(|s| s != self.recomputed_size)
    }

    /// `true` when the producer recorded an alignment and it differs.
    pub fn align_differs(&self) -> bool {
        self.producer_align
            .is_some_and(|a| a != self.recomputed_align)
    }
}

/// One layout authority's complete answer for a struct: an offset per field,
/// the total size and the alignment.
///
/// Used to carry BOTH of trust-cg's packed authorities on a refusal, so a
/// reader never has to take the predicate's word for which one it picked — it
/// picked neither.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorityLayout {
    /// One entry per declared field, in declaration order.
    pub offsets: Vec<u64>,
    /// The struct's total size under this authority.
    pub size: u64,
    /// The struct's alignment under this authority.
    pub align: u64,
}

impl AuthorityLayout {
    /// `offsets [..], size N, align M` — the form both packed reasons quote.
    fn render(&self) -> String {
        format!(
            "offsets {:?}, size {}, align {}",
            self.offsets, self.size, self.align
        )
    }
}

/// Why a [`StructLayoutDisposition::NotComparable`] row could not be measured
/// — and, decisively, whether the byte path is nevertheless free to emit it.
///
/// `NotComparable` does not refuse (see
/// [`StructLayoutDisposition::is_refusal`]). For exactly ONE of these kinds
/// that is because the adapter's own type translation independently rejects the
/// struct, so nothing is emitted either way. For the other three the adapter
/// accepts the struct and emits bytes for it: declining to score them is a
/// statement about this predicate's reach, **not** a safety property. Keeping
/// the kinds apart is what stops "1,506 NotComparable" from reading as "1,506
/// rows something else already caught".
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NotComparableKind {
    /// A field type does not convert to LIR at all. The adapter's own
    /// `translate_type_with_enum_tables` returns the same `Err` for this struct
    /// wherever the byte path meets it, so emission is already blocked and this
    /// row adds no exposure.
    AdapterRejected,
    /// The LIR layout does not fit the byte path's `u32` arithmetic.
    ///
    /// This kind USED TO BE live exposure, and the change is worth stating
    /// rather than quietly editing: `Type::bytes()` aborted in a debug build
    /// and WRAPPED in a release one, so emission proceeded with a wrapped
    /// extent. (c) MEASURED at the time: an array of 2^28 sixteen-byte structs
    /// produced a 4 GiB `Memmove` against a carrier that reported 0 bytes.
    ///
    /// `translate_type_*` now refuses any type whose natural extent does not
    /// fit the carrier ([`crate::types::Type::checked_bytes`]), so emission is
    /// blocked before it starts — the same standing as [`Self::AdapterRejected`],
    /// reached by a different gate. A struct still lands here when every FIELD
    /// is individually representable and their SUM is not, which is the one
    /// shape the per-type gate cannot see from a field.
    Unrepresentable,
    /// A `#[repr(packed(N))]` struct, which trust-cg lays out TWO ways (see the
    /// module docs). The adapter does **not** reject it — both authorities
    /// happily emit. Live exposure, and the reason names both.
    PackedNoSingleAuthority,
    /// An interior the producer states no layout for (`Ty::Tuple`,
    /// `Ty::Record`, `Ty::Closure`, a descriptor-less `Ty::Enum`, or a nested
    /// `#[repr(packed)]` struct). The adapter converts all of these and the
    /// byte path emits a synthesized layout for them. Live exposure — this
    /// predicate simply has nothing to score it against.
    UnstatedInterior,
}

impl NotComparableKind {
    /// `true` when the adapter's own type translation independently rejects
    /// this struct, so `is_refusal() == false` costs nothing.
    ///
    /// (b) CODE DOES: TWO kinds have that property. [`Self::AdapterRejected`]
    /// is the field type that does not convert at all; [`Self::Unrepresentable`]
    /// joined it when `translate_type_*` began refusing types whose natural
    /// extent does not fit the u32 carrier — before that it was live exposure,
    /// and its doc records the measured hazard it used to represent.
    ///
    /// The remaining two convert successfully — verified by
    /// `test_two_of_the_four_not_comparable_kinds_are_NOT_rejected_by_the_adapter`,
    /// which translates each fixture through the byte path's own conversion and
    /// asserts what it returns, in both directions.
    pub fn is_rejected_by_the_adapter(self) -> bool {
        matches!(self, Self::AdapterRejected | Self::Unrepresentable)
    }

    /// `true` when this row is declined by the predicate and accepted by
    /// everything else — the byte path emits, and no gate stopped it.
    pub fn is_live_exposure(self) -> bool {
        !self.is_rejected_by_the_adapter()
    }
}

/// Disposition of a single [`trust_ir::StructDef`] under the M0.5 predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StructLayoutDisposition {
    /// Every producer offset equals the recomputed offset, and the producer's
    /// size/align (where recorded) match too. Vacuously true for a field-less
    /// struct that records no size.
    Agrees,
    /// At least one producer offset — or the struct's total size/alignment —
    /// differs from the recomputation.
    Disagrees {
        /// Every differing field, in declaration order. **May be empty** when
        /// only `size` differs.
        mismatches: Vec<FieldOffsetMismatch>,
        /// The struct-level size/alignment divergence, when there is one.
        size: Option<StructSizeMismatch>,
    },
    /// No field carries an offset — the producer's layout query declined
    /// (generic / param / opaque) — and nothing else contradicts. Not an error.
    ///
    /// Deliberately NOT [`Self::Agrees`]: the offsets went unchecked, so
    /// agreement on the total size (when the producer recorded one) says
    /// nothing about where the fields sit.
    LayoutAbsent,
    /// Some fields carry an offset and some do not. A defect: half the struct
    /// would be checked and half silently recomputed.
    MixedOffsets {
        /// Declaration indices of fields that carry an offset.
        with_offset: Vec<usize>,
        /// Declaration indices of fields that do not.
        without_offset: Vec<usize>,
    },
    /// Nothing on the consumer side is scoreable: either the struct does not
    /// convert to a LIR [`Type`] at all, or it converts to a layout no single
    /// authority owns.
    ///
    /// `kind` is load-bearing, not decoration: it is the only thing that
    /// separates the rows the adapter independently rejects from the rows the
    /// byte path is still free to emit. See [`NotComparableKind`].
    NotComparable {
        /// Which of the four non-comparable situations this is.
        kind: NotComparableKind,
        /// Why conversion failed, verbatim from the adapter.
        reason: String,
    },
    /// `sdef.id` resolves, under the byte path's FIRST-MATCH rule
    /// (`adapter.rs:1250`), to a `StructDef` with a **different emitted
    /// layout**. A malformed module: every value of `sdef`'s type is addressed
    /// with the resolved struct's layout, so `sdef`'s own offsets describe
    /// nothing that is ever emitted.
    ///
    /// Strictly worse than a field disagreement — the whole type is shadowed,
    /// not one field — and therefore a refusal.
    ///
    /// "Different" is measured by `emitted_layout_identity` (`repr` plus the
    /// field TYPE sequence), NOT by `StructDef: PartialEq`. A shadow that
    /// differs only in a struct name, a field name, a producer offset or a
    /// producer size/align emits a byte-identical layout, misaddresses nothing,
    /// and is measured normally — the justification above ("describes nothing
    /// that is ever emitted") is false for it, which is precisely why it is not
    /// reported here.
    StructIdCollision {
        /// The id both definitions declare.
        struct_id: StructId,
        /// Name of the definition the byte path resolves `struct_id` to.
        resolved_name: String,
        /// Index of that definition in `module.structs`.
        resolved_index: usize,
    },
    /// A `#[repr(packed(N))]` struct whose producer layout matches **NEITHER**
    /// of trust-cg's two packed layout authorities.
    ///
    /// This is the one packed verdict that needs no authority choice.
    /// [`NotComparableKind::PackedNoSingleAuthority`] exists because scoring a
    /// packed struct means picking one of two layouts the compiler really
    /// emits, and picking is what this predicate must not do. "The producer
    /// agrees with NONE of them" is a **total** statement over both: whichever
    /// authority the byte path reaches for a given value, the producer's stated
    /// addresses are wrong. So it refuses.
    ///
    /// Kept apart from [`Self::Disagrees`] deliberately: a
    /// [`FieldOffsetMismatch`] carries ONE `recomputed_offset`, and there is no
    /// single recomputation here. Both authorities are carried in full instead,
    /// and the row is counted by
    /// [`StructLayoutCensus::packed_matches_neither_authority`] rather than
    /// folded into the `Disagrees` figures.
    PackedMatchesNeitherAuthority {
        /// Authority P — `packed_struct_layout` /
        /// `TrustIrAdapter::packed_field_offset` (`adapter.rs:11549`) /
        /// `packed_struct_size` (`:11586`).
        packed: AuthorityLayout,
        /// Authority C — natural-C `Type::bytes()` / `align()` /
        /// `offset_of`. Since the 2026-08-08 aggregate-constant repair this is
        /// a SIZE/ALIGN authority only: `TrustIrAdapter::translate_alloc`
        /// (`adapter.rs:8958-8963`) and `translate_heap_alloc` (`:9163`)
        /// stride an element by `lir_ty.bytes()`, while `Inst::GEP` over the
        /// same pointer strides by `packed_struct_size` (`:6325`). No path
        /// emits a packed struct's field OFFSETS from this authority any more.
        natural: AuthorityLayout,
        /// What the producer claimed, what each authority says, and why no
        /// choice between them rescues the claim.
        reason: String,
    },
}

impl StructLayoutDisposition {
    /// `true` when this disposition must block byte emission for the struct.
    ///
    /// `Disagrees`, `MixedOffsets`, `StructIdCollision` and
    /// `PackedMatchesNeitherAuthority` refuse. `LayoutAbsent` and
    /// `NotComparable` do **not**.
    ///
    /// # What the non-refusal actually costs (corrected)
    ///
    /// This doc used to justify the `NotComparable` non-refusal with "an
    /// unconvertible struct is already rejected by the adapter's own type
    /// translation". **That is false for three of the four
    /// [`NotComparableKind`]s**, and measurably so: (c) MEASURED over the
    /// 68-module corpus, 322 of 1,506 `NotComparable` rows are
    /// [`NotComparableKind::PackedNoSingleAuthority`] or
    /// [`NotComparableKind::UnstatedInterior`] — rows whose field types convert
    /// perfectly well and for which the byte path emits a synthesized layout
    /// with nothing stopping it. Only
    /// [`NotComparableKind::AdapterRejected`] is covered by the old sentence.
    ///
    /// So the honest statement is:
    ///
    /// * `LayoutAbsent` — a normal producer state. The producer's layout query
    ///   declined; there is no producer claim to contradict.
    /// * `NotComparable` with [`NotComparableKind::AdapterRejected`] — the
    ///   adapter blocks emission independently, so not refusing costs nothing.
    /// * every other `NotComparable` kind — a **deliberate, named non-refusal**.
    ///   The predicate cannot score the row and refusing every such row would
    ///   refuse a fifth of the corpus, so the exposure is reported rather than
    ///   blocked. [`Self::is_unrefused_exposure`] counts exactly these, and
    ///   [`StructLayoutCensus::unrefused_exposures`] surfaces them so the
    ///   number can never again hide inside a single `NotComparable` total.
    pub fn is_refusal(&self) -> bool {
        matches!(
            self,
            Self::Disagrees { .. }
                | Self::MixedOffsets { .. }
                | Self::StructIdCollision { .. }
                | Self::PackedMatchesNeitherAuthority { .. }
        )
    }

    /// The [`NotComparableKind`] of this row, or `None` for every other
    /// disposition.
    pub fn not_comparable_kind(&self) -> Option<NotComparableKind> {
        match self {
            Self::NotComparable { kind, .. } => Some(*kind),
            _ => None,
        }
    }

    /// `true` when this row neither refuses nor is independently blocked: the
    /// predicate declined to score it and the byte path emits anyway.
    ///
    /// This is the number that must be quoted next to any "N rows agree"
    /// claim. It is NOT a defect count — an unstated interior may well be laid
    /// out correctly — it is the size of the population this predicate is
    /// silent about while bytes are being emitted.
    pub fn is_unrefused_exposure(&self) -> bool {
        self.not_comparable_kind()
            .is_some_and(NotComparableKind::is_live_exposure)
    }

    /// `true` when this is a disagreement in which a **non-zero-sized** field
    /// moves.
    ///
    /// This counts moved FIELDS only, and on its own it **understates
    /// severity** — do not read its complement as "harmless". (c) MEASURED
    /// over the 68-module corpus with the closed predicate: of the
    /// disagreements this returns `false` for, the overwhelming majority are
    /// SIZE/ALIGN divergences, which relocate every array element past the
    /// first and mint a wrong `memcpy` length. Use [`Self::moves_bytes`] for
    /// the severity question and keep this one for the field-offset figure,
    /// whose whole purpose is to stay comparable across measurements.
    pub fn is_load_bearing_disagreement(&self) -> bool {
        match self {
            Self::Disagrees { mismatches, .. } => mismatches.iter().any(|m| m.load_bearing),
            _ => false,
        }
    }

    /// `true` when this disposition puts at least one byte that is really
    /// loaded or stored at an address the producer did not specify.
    ///
    /// The union of the two independent ways that happens, which is why
    /// neither accessor alone answers "is this severe":
    ///
    /// * a **non-zero-sized field moves** ([`Self::is_load_bearing_disagreement`]);
    /// * the struct's **total size or alignment diverges**
    ///   ([`Self::is_size_disagreement`]) — a wrong size is a wrong array
    ///   stride, a wrong allocation and a wrong `memcpy` length, and a wrong
    ///   alignment is a wrong placement inside every containing aggregate.
    ///
    /// A disagreement that only relocates a zero-sized field satisfies
    /// neither, and is the one genuinely address-preserving kind.
    ///
    /// **Scope, stated so it cannot be over-read:** this accessor and
    /// [`StructLayoutCensus::byte_moving_disagreements`] range over
    /// [`Self::Disagrees`] rows only. [`Self::PackedMatchesNeitherAuthority`]
    /// answers `false` here and is nevertheless a REFUSAL — it has no single
    /// recomputed layout, so there is no `FieldOffsetMismatch` to ask about
    /// load-bearingness, and inventing one would mean picking an authority.
    /// Count it with [`StructLayoutCensus::packed_matches_neither_authority`];
    /// [`StructLayoutCensus::refusals`] is the complete blocking set.
    pub fn moves_bytes(&self) -> bool {
        self.is_load_bearing_disagreement() || self.is_size_disagreement()
    }

    /// `true` when the producer's total size or alignment diverges.
    pub fn is_size_disagreement(&self) -> bool {
        self.size_mismatch().is_some()
    }

    /// The struct-level size/alignment divergence, if any.
    pub fn size_mismatch(&self) -> Option<&StructSizeMismatch> {
        match self {
            Self::Disagrees { size, .. } => size.as_ref(),
            _ => None,
        }
    }

    /// The differing fields, empty for every non-`Disagrees` disposition.
    pub fn mismatches(&self) -> &[FieldOffsetMismatch] {
        match self {
            Self::Disagrees { mismatches, .. } => mismatches,
            _ => &[],
        }
    }
}

/// A census row: one struct, its identity, and its disposition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructLayoutRow {
    pub struct_id: StructId,
    pub name: String,
    pub repr: StructRepr,
    pub disposition: StructLayoutDisposition,
}

/// The M0.5 census over a module's struct table.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct StructLayoutCensus {
    pub rows: Vec<StructLayoutRow>,
}

impl StructLayoutCensus {
    /// Rows whose disposition matches `pred`.
    fn count_by(&self, pred: impl Fn(&StructLayoutDisposition) -> bool) -> usize {
        self.rows.iter().filter(|r| pred(&r.disposition)).count()
    }

    pub fn agrees(&self) -> usize {
        self.count_by(|d| matches!(d, StructLayoutDisposition::Agrees))
    }

    pub fn disagrees(&self) -> usize {
        self.count_by(|d| matches!(d, StructLayoutDisposition::Disagrees { .. }))
    }

    /// Disagreements in which a non-ZST field moves.
    ///
    /// Deliberately narrower than [`Self::byte_moving_disagreements`] — see
    /// [`StructLayoutDisposition::is_load_bearing_disagreement`] for why its
    /// complement must not be read as "harmless".
    pub fn load_bearing_disagreements(&self) -> usize {
        self.count_by(StructLayoutDisposition::is_load_bearing_disagreement)
    }

    /// Disagreements that relocate at least one byte that is really loaded or
    /// stored — a moved non-ZST field **or** a diverging total size/alignment.
    ///
    /// This is the severity headline **for `Disagrees` rows**.
    /// `disagrees() - byte_moving_disagreements()` is the count of genuinely
    /// address-preserving (ZST-only) disagreements. It does NOT include
    /// [`Self::packed_matches_neither_authority`] — see
    /// [`StructLayoutDisposition::moves_bytes`] for why that row cannot answer
    /// the question without picking an authority.
    pub fn byte_moving_disagreements(&self) -> usize {
        self.count_by(StructLayoutDisposition::moves_bytes)
    }

    /// Disagreements in which the struct's TOTAL SIZE or ALIGNMENT diverges —
    /// disjoint from [`Self::load_bearing_disagreements`] only in what it
    /// measures, not in which rows it may count.
    pub fn size_disagreements(&self) -> usize {
        self.count_by(StructLayoutDisposition::is_size_disagreement)
    }

    pub fn layout_absent(&self) -> usize {
        self.count_by(|d| matches!(d, StructLayoutDisposition::LayoutAbsent))
    }

    pub fn mixed_offsets(&self) -> usize {
        self.count_by(|d| matches!(d, StructLayoutDisposition::MixedOffsets { .. }))
    }

    pub fn not_comparable(&self) -> usize {
        self.count_by(|d| matches!(d, StructLayoutDisposition::NotComparable { .. }))
    }

    /// `NotComparable` rows of one [`NotComparableKind`].
    pub fn not_comparable_of_kind(&self, kind: NotComparableKind) -> usize {
        self.count_by(|d| d.not_comparable_kind() == Some(kind))
    }

    /// Rows this predicate declined to score that **nothing else blocked** —
    /// the byte path emits a synthesized layout for every one of them.
    ///
    /// Quote this next to [`Self::agrees`]. A census that reports only
    /// `agrees` / `disagrees` / `not_comparable` lets the live-exposure
    /// population hide inside the last bucket, which is exactly the reading
    /// error the old [`StructLayoutDisposition::is_refusal`] doc invited.
    pub fn unrefused_exposures(&self) -> usize {
        self.count_by(StructLayoutDisposition::is_unrefused_exposure)
    }

    /// `#[repr(packed(N))]` rows whose producer layout matches NEITHER packed
    /// authority — a refusal, and deliberately NOT part of the `Disagrees`
    /// figures (there is no single recomputed layout to score against).
    pub fn packed_matches_neither_authority(&self) -> usize {
        self.count_by(|d| {
            matches!(
                d,
                StructLayoutDisposition::PackedMatchesNeitherAuthority { .. }
            )
        })
    }

    /// Rows whose `StructId` is shadowed by an earlier definition of the same
    /// id — a malformed module, counted separately from a layout disagreement.
    pub fn struct_id_collisions(&self) -> usize {
        self.count_by(|d| matches!(d, StructLayoutDisposition::StructIdCollision { .. }))
    }

    /// Every row that must block byte emission.
    pub fn refusals(&self) -> impl Iterator<Item = &StructLayoutRow> {
        self.rows.iter().filter(|r| r.disposition.is_refusal())
    }

    /// `true` when the module carries at least one refusing struct.
    pub fn refuses(&self) -> bool {
        self.rows.iter().any(|r| r.disposition.is_refusal())
    }
}

/// What [`recompute_layout`] found when it asked "who owns this struct's
/// emitted layout?".
///
/// The packed question is NOT "is this struct `#[repr(packed)]`" but "do
/// trust-cg's two packed authorities actually DISAGREE about this struct". The
/// clamp `min(natural_align, N)` is a no-op whenever no field's natural
/// alignment exceeds `N`, and then both authorities compute the identical
/// layout — one authority, and the normal comparison must run.
enum LayoutAuthority {
    /// Exactly one layout is emitted for this struct — either because it is
    /// not packed, or because both packed authorities landed on the same
    /// answer. Compare the producer against it.
    Single(AuthorityLayout),
    /// The two packed authorities disagree AND the producer's claim matches at
    /// least one of them. Scoring would mean picking a winner, which is the one
    /// thing this predicate must not do.
    Split(String),
    /// The two packed authorities disagree and the producer matches
    /// **neither**. A total statement over both, so no choice is needed and the
    /// struct is refused.
    MatchesNeither {
        packed: AuthorityLayout,
        natural: AuthorityLayout,
        reason: String,
    },
}

/// Is every intermediate of the byte path's `u32` layout arithmetic
/// representable for `ty`?
///
/// `Type::bytes()` (`types.rs:106-134`) multiplies `elem.bytes() * count` and
/// accumulates struct offsets in unchecked `u32`; `Type::align()` on an
/// `Enum` reaches `enum_payload_layout`, which computes payload BYTES, so it
/// overflows too. This mirrors that arithmetic in checked `u64` and refuses
/// anything that would not fit, so the subsequent real calls cannot abort
/// (debug) or wrap (release).
fn layout_is_representable(ty: &Type) -> bool {
    ty.checked_bytes().is_some()
}

/// How many of `elems` occupy at least one byte once translated to LIR, or
/// `None` when one of them does not convert at all — in which case the
/// translation step reports the adapter's own reason rather than being shadowed
/// by an interior message.
///
/// An aggregate with at most one non-ZST element has no observable reordering
/// freedom, so the byte path's natural-C lowering and rustc's layout cannot
/// disagree about where the payload sits.
fn non_zst_count(elems: &[Ty], module: &Module) -> Option<usize> {
    let mut non_zst = 0usize;
    for elem in elems {
        let lir = translate_field_type(elem, module).ok()?;
        if lir.checked_bytes().is_none_or(|b| b > 0) {
            non_zst += 1;
        }
    }
    Some(non_zst)
}

/// An interior the producer states no layout for, or `None` when every
/// interior along the `Struct`/`Array`/`Tuple`/`Record`/`Closure`/`Enum` spine
/// is either comparable or reported by the translation step instead.
///
/// `path` names where the interior sits, so the refusal reason can point at it.
///
/// **Termination** rests on `depth` alone. There is deliberately no cycle
/// guard: every edge this scan follows is also an edge
/// `translate_type_with_enum_tables` follows *with the same depth increment*,
/// so a type graph with a cycle blows the adapter's
/// `MAX_TYPE_TRANSLATION_DEPTH` at classification step 3a and never reaches
/// this function. A `seen: Vec<StructId>` guard used to sit on the `Ty::Struct`
/// arm; it was provably unreachable (disabling it left the suite green with no
/// hang) and has been removed rather than left reading as coverage.
///
/// The bound **fails CLOSED**. It used to return `None` — "no interior gap
/// here" — which is the one answer that lets step 7 certify `Agrees`. That the
/// branch is unreachable today is an argument about two constants being equal,
/// and an unreachable branch that silently certifies is the wrong shape for an
/// argument that might stop holding. Depth exhaustion now reports a gap, and
/// [`MAX_INTERIOR_SCAN_DEPTH`] is *defined as* the adapter's bound rather than
/// copied from it, so the two cannot drift apart in the first place.
fn interior_layout_gap(ty: &Ty, path: &str, module: &Module, depth: usize) -> Option<String> {
    if depth >= MAX_INTERIOR_SCAN_DEPTH {
        return Some(format!(
            "{path} sits deeper than the interior scan's own bound \
             ({MAX_INTERIOR_SCAN_DEPTH}); the scan has NOT established that the interior is \
             comparable, and reporting no gap here would certify a layout it never looked at"
        ));
    }
    match ty {
        Ty::Tuple(elems) => {
            let non_zst = non_zst_count(elems, module)?;
            if non_zst > 1 {
                return Some(format!(
                    "{path} is a `Ty::Tuple` with {non_zst} non-zero-sized elements; a tuple \
                     carries no `FieldDef::offset`, so the producer states no interior layout, \
                     and the byte path lowers it declaration-ordered natural-C while rustc is \
                     free to reorder it"
                ));
            }
            elems.iter().enumerate().find_map(|(i, elem)| {
                interior_layout_gap(elem, &format!("{path}.{i}"), module, depth + 1)
            })
        }
        // Same synthesized aggregate as a tuple: the adapter lowers a record to
        // `Type::Struct([field types...])` in declaration order
        // (`adapter.rs:1406-1433`), and `RecordDef`'s fields reuse `FieldDef`
        // with `offset` ALWAYS `None` (`trust-ir/src/ty.rs:596-598`). Resolved
        // exactly as the adapter resolves it — index first, then linear scan.
        Ty::Record(rid) => {
            let rdef = module
                .records
                .get(rid.as_usize())
                .filter(|def| def.id == *rid)
                .or_else(|| module.records.iter().find(|def| def.id == *rid))?;
            let field_tys: Vec<Ty> = rdef.fields.iter().map(|f| f.ty.clone()).collect();
            let non_zst = non_zst_count(&field_tys, module)?;
            if non_zst > 1 {
                return Some(format!(
                    "{path} is a `Ty::Record` (`{}`) with {non_zst} non-zero-sized fields; \
                     `RecordDef` carries no producer offsets (`FieldDef::offset` is always \
                     `None` for records), so the producer states no interior layout, and the \
                     byte path lowers it to the same declaration-ordered natural-C \
                     `Type::Struct` a tuple gets while rustc is free to reorder it",
                    rdef.name
                ));
            }
            rdef.fields.iter().find_map(|f| {
                interior_layout_gap(&f.ty, &format!("{path}.`{}`", f.name), module, depth + 1)
            })
        }
        // Likewise `Type::Struct([capture types...])` in capture-declaration
        // order (`adapter.rs:1443-1467`), and `ClosureTy::captures` is a bare
        // `Vec<Ty>` with no offset carrier at all. rustc reorders closure
        // captures exactly as it reorders `repr(Rust)` struct fields. Resolved
        // by index, exactly as the adapter resolves it.
        Ty::Closure(cid) => {
            let cdef = module.closure_types.get(cid.as_usize())?;
            let non_zst = non_zst_count(&cdef.captures, module)?;
            if non_zst > 1 {
                return Some(format!(
                    "{path} is a `Ty::Closure` with {non_zst} non-zero-sized captures; \
                     `ClosureTy::captures` is a bare `Vec<Ty>` with no offset carrier, so the \
                     producer states no interior layout, and the byte path lowers it to a \
                     capture-ordered natural-C `Type::Struct` while rustc reorders closure \
                     captures"
                ));
            }
            cdef.captures.iter().enumerate().find_map(|(i, capture)| {
                interior_layout_gap(capture, &format!("{path}.capture{i}"), module, depth + 1)
            })
        }
        Ty::Enum(eid) => {
            // An enum that DOES carry a layout descriptor is either refused by
            // the adapter's own translation with a precise message, or admitted
            // only because its emitted image IS the producer's declared one —
            // a Direct encoding that agrees with the canonical tagged union
            // (`enum_layout_matches_canonical`), or a Niche encoding whose
            // payload carrier reproduces the declared size, align and every
            // declared field offset (`niche_enum_carrier`). Both admissions are
            // equalities against the descriptor, so neither leaves an interior
            // whose layout this predicate has nothing to score.
            let edef = module.enums.iter().find(|e| e.id == *eid)?;
            if edef.layout.is_some() {
                return None;
            }
            Some(format!(
                "{path} is `Ty::Enum` (`{}`) whose `EnumDef` carries no producer layout \
                 descriptor; the byte path synthesizes LIR's canonical tagged-union layout, \
                 which is not rustc's, and the enum payload carries no producer offsets to \
                 compare",
                edef.name
            ))
        }
        Ty::Struct(sid) => {
            let sdef = module.structs.iter().find(|s| s.id == *sid)?;
            // A nested `#[repr(packed)]` struct is the one interior trust-cg
            // provably SIZES two ways (see the module docs' packed section).
            // Its own census row says `NotComparable`, but that says nothing
            // about THIS row: certifying the container `Agrees` certifies an
            // interior whose extent the compiler computes two ways.
            //
            // WHICH of the two the container advances by is no longer the
            // question. The nested-packed repair moved
            // `packed_struct_layout`'s own advance onto `packed_struct_size`
            // (it used to advance by the natural `mfty.bytes()`, over-reporting
            // `#[repr(packed)] { u8, P }` as 17 where rustc says 10), so a
            // PACKED container now advances past a packed interior with the
            // packed extent. What survives is the two-authority split itself: a
            // NON-packed container still advances past the same interior with
            // natural-C `Type::offset_of`, and the alloca/heap element stride,
            // the aggregate-constant slot, the aggregate `Load` slot and the C
            // ABI classifier all still measure it with `Type::bytes()`. So the
            // interior's extent is still computed two ways, and certifying a
            // container over it still certifies bytes no single authority owns.
            // Same doctrine as the tuple/record/closure gap.
            if let StructRepr::Packed(n) = sdef.repr {
                return Some(format!(
                    "{path} is `Ty::Struct` (`{}`), a `#[repr(packed({n}))]` INTERIOR, and \
                     trust-cg has NO SINGLE SIZE AUTHORITY for a packed struct: \
                     `packed_struct_layout` / `TrustIrAdapter::packed_struct_size` (the \
                     `Inst::GEP` element stride, a PACKED container's own running offset, and \
                     the aggregate-field `Memmove` length on the packed `InsertField` arm and \
                     the aggregate `Store` arm) and natural-C `Type::bytes()` / \
                     `Type::offset_of` (`TrustIrAdapter::translate_alloc`, \
                     `translate_heap_alloc`, the aggregate-constant slot, the aggregate `Load` \
                     slot, the C ABI classifier, and a NON-packed container's own field \
                     offsets) give it two different extents. This container's own offsets can \
                     only be recomputed by advancing past `{}` with one of them, so agreeing \
                     on them says nothing about where the fields AFTER it sit",
                    sdef.name, sdef.name
                ));
            }
            sdef.fields.iter().find_map(|f| {
                interior_layout_gap(&f.ty, &format!("{path}.`{}`", f.name), module, depth + 1)
            })
        }
        Ty::Array(elem_id, _) => {
            let elem = module.types.get(elem_id.index() as usize)?;
            interior_layout_gap(elem, &format!("{path}[]"), module, depth + 1)
        }
        // `Ty::Refine(base, _)` is REPRESENTATION-PRESERVING by construction
        // (`trust-ir/src/ty.rs:183-190`): the adapter erases it and lowers the
        // base carrier verbatim (`adapter.rs:1512-1522`). So EVERY interior gap
        // the base has is an interior gap the refinement has, and not following
        // this edge let a refinement hide a tuple / record / closure /
        // descriptor-less-enum interior and mint a false `Agrees`. Resolved
        // exactly as the adapter resolves it (`types` table by index) and
        // charged the SAME one level of depth the adapter charges it, so the
        // "scan depth never exceeds translation depth" invariant survives.
        Ty::Refine(base_id, _) => {
            let base = module.types.get(base_id.index() as usize)?;
            interior_layout_gap(base, path, module, depth + 1)
        }
        _ => None,
    }
}

/// The part of a [`StructDef`] that decides **what layout the byte path emits
/// for values of its id** — and therefore the only part step 0 may compare.
///
/// (b) CODE DOES: the byte path resolves `Ty::Struct(sid)` by FIRST MATCH
/// (`adapter.rs:1250`) and then builds `Type::Struct([translate(f.ty) for f in
/// resolved.fields])`, choosing between the packed and the natural-C authority
/// on `resolved.repr` (`adapter.rs:11529` `is_packed_struct_ty`, gating
/// `packed_field_offset` at `:11549` and `packed_struct_size` at `:11586`).
/// `translate_type_*` is a
/// function of the field `Ty` and the module tables alone. So the emitted
/// layout is a function of exactly two things: the field TYPE sequence and the
/// `repr`.
///
/// Everything else in `StructDef` is either identity (`name`, `FieldDef::name`)
/// or the producer CLAIM this predicate exists to score (`FieldDef::offset`,
/// `size`, `align`). When two defs sharing an id agree here, both are addressed
/// with a byte-identical layout, each one's own claim is scoreable against it,
/// and the honest verdicts are the ordinary `Agrees` / `Disagrees` — which is
/// why the projection is used instead of a distinct non-refusing collision
/// disposition: a wrong claim under a harmless shadow is still a wrong claim
/// and must still refuse, naming the field.
///
/// This is also exactly the condition steps 1-7 need. They translate `sdef`'s
/// OWN fields (step 3a) and pick the authority from `sdef.repr` (step 3c); that
/// is the same measurement the byte path makes for `sdef.id` iff the projection
/// matches. Narrowing it further would be unsound; widening it refuses structs
/// nothing misaddresses.
///
/// Not covered, and deliberately so: DWARF debug-info emission
/// (`adapter.rs:16357`) does read `FieldDef::offset` and field names off a
/// resolved def, so a name-only shadow can still mint debug info naming the
/// wrong twin. That is not an ADDRESS defect, this module is scoped to
/// addresses, and it is recorded here rather than folded into a layout refusal.
fn emitted_layout_identity(sdef: &StructDef) -> (StructRepr, Vec<&Ty>) {
    (sdef.repr, sdef.fields.iter().map(|f| &f.ty).collect())
}

/// Translate ONE field type through the adapter's module-aware conversion.
fn translate_field_type(ty: &Ty, module: &Module) -> Result<Type, crate::adapter::AdapterError> {
    translate_type_with_enum_tables(
        ty,
        &module.structs,
        &module.types,
        &module.enums,
        &module.records,
        &module.closure_types,
    )
}

/// Classify one struct's producer layout against the recomputed LIR layout.
///
/// `module` supplies the struct / enum / record / closure / type tables the
/// adapter needs to convert field types.
///
/// The byte path resolves `Ty::Struct(sdef.id)` by FIRST MATCH
/// (`adapter.rs:1250`, `structs.iter().find(|s| s.id == *sid)`), and
/// [`trust_ir::Module::add_struct`] honours declared ids verbatim with no
/// collision check. So the first thing this does is establish that `sdef.id`
/// resolves back to a definition that EMITS THE SAME LAYOUT as `sdef`
/// ([`emitted_layout_identity`]: `repr` plus the field type sequence); if it
/// does not, no layout measured for `sdef` is a layout anything emits and the
/// answer is [`StructLayoutDisposition::StructIdCollision`]. Once that holds,
/// translating `sdef`'s own fields and re-resolving `Ty::Struct(sdef.id)` are
/// provably the same measurement, and the field-wise route is kept only because
/// it can name the offending field in a `NotComparable` reason.
///
/// Note what step 0 does NOT establish, on purpose: it says nothing about the
/// two defs' NAMES or about their producer offsets / size / align. Those are
/// the claim this predicate scores, and under a same-layout shadow each def's
/// claim is scoreable against the one emitted layout — so a wrong claim still
/// lands on `Disagrees` and still refuses, naming the field.
///
/// `sdef` does not have to be reachable by id at all — a standalone def that
/// no id resolves to is measured field-wise, since there is no other definition
/// for the byte path to prefer over it.
pub fn classify_struct_layout(sdef: &StructDef, module: &Module) -> StructLayoutDisposition {
    // 0. ID COLLISION — checked before everything else, because it invalidates
    //    every subsequent measurement: under a collision no value of `sdef`'s
    //    type is addressed with `sdef`'s layout, so `sdef`'s own offsets (and
    //    its own MIXED / absent state) describe nothing that is emitted.
    //
    //    The test is LAYOUT equality, not structural equality. `StructDef:
    //    PartialEq` also compares `name`, every `FieldDef::name` and the
    //    producer `size`/`align`, none of which the byte path reads when it
    //    lays a value out — see [`emitted_layout_identity`]. Two defs sharing
    //    an id but agreeing on the emitted layout "shadow each other
    //    harmlessly", exactly as this comment has always said, and refusing
    //    them was a false refusal.
    if let Some((resolved_index, resolved)) = module
        .structs
        .iter()
        .enumerate()
        .find(|(_, s)| s.id == sdef.id)
        && emitted_layout_identity(resolved) != emitted_layout_identity(sdef)
    {
        return StructLayoutDisposition::StructIdCollision {
            struct_id: sdef.id,
            resolved_name: resolved.name.clone(),
            resolved_index,
        };
    }

    // 1. MIXED — producer data alone decides this, so it is checked before any
    //    conversion and cannot be masked by an unconvertible field type.
    let with_offset: Vec<usize> = sdef
        .fields
        .iter()
        .enumerate()
        .filter(|(_, f)| f.offset.is_some())
        .map(|(i, _)| i)
        .collect();
    let without_offset: Vec<usize> = sdef
        .fields
        .iter()
        .enumerate()
        .filter(|(_, f)| f.offset.is_none())
        .map(|(i, _)| i)
        .collect();
    if !with_offset.is_empty() && !without_offset.is_empty() {
        return StructLayoutDisposition::MixedOffsets {
            with_offset,
            without_offset,
        };
    }

    // 2. LAYOUT ABSENT — NOTHING TO COMPARE AT ALL: no field carries an offset
    //    and the producer recorded neither size nor align. A field-less struct
    //    has no offsets to be absent and falls through to the vacuous `Agrees`
    //    below instead.
    //
    //    An offset-less struct that DOES record a size or an align is NOT
    //    returned here: `StructDef::size` / `align` come from the same layout
    //    query the offsets do, but the offsets carry an extra bounds check
    //    (`trust-thir-lower/src/lib.rs:9328`) that can drop every one of them
    //    while size/align survive. That 9-vs-16 divergence is real and must be
    //    reported, so such a struct falls through to the size comparison in
    //    step 5 — and, if the size agrees, lands back on `LayoutAbsent` at the
    //    end rather than on a false `Agrees`, because the offsets were never
    //    checked.
    let offsets_absent = with_offset.is_empty() && !sdef.fields.is_empty();
    if offsets_absent && sdef.size.is_none() && sdef.align.is_none() {
        return StructLayoutDisposition::LayoutAbsent;
    }

    // 3a. NOT COMPARABLE — route each field type through the SAME conversion
    //     the byte path uses, so this measures the layout that is actually
    //     emitted. Step 0 established that `sdef` IS what `sdef.id` resolves
    //     to, so translating `sdef`'s own fields here and re-resolving
    //     `Ty::Struct(sdef.id)` are the same measurement; the field-wise route
    //     is kept because it can name the offending field in the reason.
    let mut lir_fields: Vec<Type> = Vec::with_capacity(sdef.fields.len());
    for field in &sdef.fields {
        match translate_field_type(&field.ty, module) {
            Ok(ty) => lir_fields.push(ty),
            Err(err) => {
                return StructLayoutDisposition::NotComparable {
                    kind: NotComparableKind::AdapterRejected,
                    reason: format!("`{}`.`{}`: {err}", sdef.name, field.name),
                };
            }
        }
    }
    let lir_ty = Type::Struct(lir_fields);

    // 3b. NOT COMPARABLE — a layout the byte path's u32 arithmetic cannot
    //     represent. Checked BEFORE any `bytes()` / `align()` / `offset_of`
    //     call, which would abort in debug and wrap in release.
    if !layout_is_representable(&lir_ty) {
        return StructLayoutDisposition::NotComparable {
            kind: NotComparableKind::Unrepresentable,
            reason: format!(
                "`{}`: the LIR layout is not representable in the byte path's u32 arithmetic \
                 (`Type::bytes()` would overflow), so no offset it computes is meaningful",
                sdef.name
            ),
        };
    }

    // Field sizes are only safe to ask for AFTER the representability guard.
    let lir_field_is_non_zst: Vec<bool> = match &lir_ty {
        Type::Struct(fields) => fields.iter().map(|f| f.bytes() > 0).collect(),
        _ => Vec::new(),
    };

    // 3c. WHO OWNS this struct's emitted layout? For every non-packed `repr`
    //     that is natural C. For `#[repr(packed(N))]` trust-cg has two
    //     implementations, so both are computed and compared: identical
    //     answers mean one authority and a normal comparison; differing
    //     answers mean either a named non-answer or — when the producer
    //     contradicts BOTH — a refusal that needs no authority choice.
    let recomputed = match recompute_layout(sdef, &lir_ty, module) {
        LayoutAuthority::Single(layout) => layout,
        LayoutAuthority::Split(reason) => {
            return StructLayoutDisposition::NotComparable {
                kind: NotComparableKind::PackedNoSingleAuthority,
                reason,
            };
        }
        LayoutAuthority::MatchesNeither {
            packed,
            natural,
            reason,
        } => {
            return StructLayoutDisposition::PackedMatchesNeitherAuthority {
                packed,
                natural,
                reason,
            };
        }
    };

    // 4. COMPARE — every field, not just the first. Skipped wholesale when the
    //    producer recorded no offsets at all; only size/align are comparable
    //    then (see step 2).
    let mut mismatches = Vec::new();
    for (index, field) in sdef.fields.iter().enumerate() {
        if offsets_absent {
            break;
        }
        let Some(producer_offset) = field.offset else {
            // Unreachable given the MIXED / LAYOUT-ABSENT gates above, but
            // fail closed rather than skipping a field silently.
            return StructLayoutDisposition::MixedOffsets {
                with_offset: (0..sdef.fields.len()).filter(|i| *i != index).collect(),
                without_offset: vec![index],
            };
        };
        let Some(recomputed_offset) = recomputed.offsets.get(index).copied() else {
            return StructLayoutDisposition::NotComparable {
                kind: NotComparableKind::Unrepresentable,
                reason: format!("`{}`: no recomputed offset for field {index}", sdef.name),
            };
        };
        if producer_offset != recomputed_offset {
            let load_bearing = lir_field_is_non_zst.get(index).copied().unwrap_or(false);
            mismatches.push(FieldOffsetMismatch {
                field_index: index,
                field_name: field.name.clone(),
                producer_offset,
                recomputed_offset,
                load_bearing,
            });
        }
    }

    // 5. COMPARE the struct's TOTAL SIZE and ALIGNMENT. `StructDef::size` /
    //    `align` are `Some` exactly when the offsets are (one `layout`
    //    binding mints all three, `trust-thir-lower/src/lib.rs:9269-9271`), so
    //    this data is free — and it is the only thing that catches a
    //    niche-optimised field, where every offset agrees and the size is
    //    wrong by 2x.
    let size_differs = sdef.size.is_some_and(|s| s != recomputed.size);
    let align_differs = sdef.align.is_some_and(|a| a != recomputed.align);
    let size = (size_differs || align_differs).then_some(StructSizeMismatch {
        producer_size: sdef.size,
        recomputed_size: recomputed.size,
        producer_align: sdef.align,
        recomputed_align: recomputed.align,
    });

    if !mismatches.is_empty() || size.is_some() {
        // A MEASURED disagreement outranks an unmeasurable interior: this row
        // must REFUSE, and `NotComparable` does not. The mismatches are real
        // regardless of what the interior does — they are the offsets the byte
        // path emits for the outer struct.
        return StructLayoutDisposition::Disagrees { mismatches, size };
    }

    // 6. LAYOUT ABSENT — the size/align agreed, but no field offset was ever
    //    compared. Certifying `Agrees` here would be exactly the false
    //    certification step 2 exists to avoid.
    if offsets_absent {
        return StructLayoutDisposition::LayoutAbsent;
    }

    // 7. NOT COMPARABLE — everything measurable agrees, so before certifying
    //    the row, refuse to certify an INTERIOR the producer states no layout
    //    for (`Ty::Tuple`, `Ty::Record`, `Ty::Closure`, descriptor-less
    //    `Ty::Enum`). Such an interior converts fine and is laid out by LIR
    //    alone, so agreement on the outer offsets says nothing about it.
    for field in &sdef.fields {
        if let Some(gap) =
            interior_layout_gap(&field.ty, &format!("field `{}`", field.name), module, 0)
        {
            return StructLayoutDisposition::NotComparable {
                kind: NotComparableKind::UnstatedInterior,
                reason: format!("`{}`: {gap}", sdef.name),
            };
        }
    }

    StructLayoutDisposition::Agrees
}

/// Authority C: declaration-ordered natural C, read off the LIR type the byte
/// path builds. `None` only if `Type::offset_of` declines for some index, which
/// `Type::Struct` with `sdef.fields.len()` members never does — kept fail-closed
/// rather than defaulting a missing offset to 0, which would fabricate an
/// authority's answer.
fn natural_authority(field_count: usize, lir_ty: &Type) -> Option<AuthorityLayout> {
    let mut offsets = Vec::with_capacity(field_count);
    for index in 0..field_count {
        offsets.push(u64::from(lir_ty.offset_of(index)?));
    }
    Some(AuthorityLayout {
        offsets,
        size: u64::from(lir_ty.bytes()),
        align: u64::from(lir_ty.align()),
    })
}

/// Authority D: the producer's own declared layout, **when the byte path
/// actually emits it**.
///
/// This asks [`crate::declared_layout::emitted_struct_layout`] — the same
/// function `TrustIrAdapter::explicit_field_offset` and
/// `TrustIrAdapter::aggregate_value_extent` ask — rather than reading
/// `sdef.offset` directly, so the answer is "what is emitted", not "what was
/// declared". `None` whenever that function falls back: an incomplete declared
/// layout, one whose fields do not fit or overlap under the emitted interior
/// extents, or one that exceeds the natural-C recomputation and so would not
/// fit the room the unreached extent consumers reserve.
fn declared_authority(sdef: &StructDef, module: &Module) -> Option<AuthorityLayout> {
    let layout = emitted_struct_layout(
        sdef,
        LayoutTables {
            structs: &module.structs,
            types: &module.types,
            enums: &module.enums,
            records: &module.records,
            closures: &module.closure_types,
        },
    )
    .ok()?;
    (layout.source == LayoutSource::Declared).then_some(AuthorityLayout {
        offsets: layout.offsets,
        size: layout.size,
        align: layout.align,
    })
}

/// Authority P: `packed_struct_layout`, the packed placement walk. `None` when
/// it cannot produce a complete answer (its own field translation failed, or
/// the walk was truncated so `size` is `None`).
fn packed_authority(sdef: &StructDef, module: &Module) -> Option<AuthorityLayout> {
    let layout = packed_struct_layout(
        sdef,
        &module.structs,
        &module.types,
        &module.enums,
        &module.records,
        &module.closure_types,
        None,
    )
    .ok()?;
    Some(AuthorityLayout {
        offsets: layout.offsets,
        size: layout.size?,
        align: layout.align,
    })
}

/// Does the producer's stated layout agree with `authority` on **every
/// component the producer actually stated**?
///
/// Components the producer left `None` are not evidence against it: a struct
/// whose layout query declined has made no claim to contradict. This is
/// deliberately the same "stated components only" rule steps 4 and 5 apply.
fn producer_matches(sdef: &StructDef, authority: &AuthorityLayout) -> bool {
    let offsets_agree = sdef.fields.iter().enumerate().all(|(i, f)| match f.offset {
        None => true,
        Some(stated) => authority.offsets.get(i) == Some(&stated),
    });
    offsets_agree
        && sdef.size.is_none_or(|s| s == authority.size)
        && sdef.align.is_none_or(|a| a == authority.align)
}

/// `[0, ?, 8]`-style rendering of what the producer actually claimed, so a
/// refusal can quote the claim next to both authorities.
fn render_producer_claim(sdef: &StructDef) -> String {
    let offsets: Vec<String> = sdef
        .fields
        .iter()
        .map(|f| f.offset.map_or_else(|| "?".to_string(), |o| o.to_string()))
        .collect();
    let show = |v: Option<u64>| v.map_or_else(|| "?".to_string(), |x| x.to_string());
    format!(
        "offsets [{}], size {}, align {}",
        offsets.join(", "),
        show(sdef.size),
        show(sdef.align)
    )
}

/// Who owns `sdef`'s emitted layout, and what do they say?
///
/// For every non-packed `repr` there is one authority — natural C — and this is
/// a plain recomputation. For `#[repr(packed(N))]` trust-cg has two
/// implementations that can each emit bytes for the same struct, so this
/// computes BOTH and then decides:
///
/// * **they agree** — the clamp `min(natural_align, N)` was a no-op for every
///   field, there is one emitted layout after all, and the producer must be
///   compared against it like any other struct. Gating on `repr` instead of on
///   the actual disagreement is what swallowed load-bearing refusals: an
///   all-`u8` `#[repr(packed)]` struct with a field parked at the wrong offset
///   was reported as a census row while both authorities agreed it moved;
/// * **they disagree and the producer matches exactly one** — scoring means
///   picking a winner. Non-answer, named ([`LayoutAuthority::Split`]);
/// * **they disagree and the producer matches neither** — a total statement
///   over both authorities that needs no choice between them, so it refuses
///   ([`LayoutAuthority::MatchesNeither`]).
fn recompute_layout(sdef: &StructDef, lir_ty: &Type, module: &Module) -> LayoutAuthority {
    let Some(natural) = natural_authority(sdef.fields.len(), lir_ty) else {
        return LayoutAuthority::Split(format!(
            "`{}`: LIR `Type::offset_of` yielded no offset for some field, so even the natural-C \
             authority has no complete answer and there is nothing to score against",
            sdef.name
        ));
    };

    // Authority D — the PRODUCER'S OWN layout, read verbatim. Since the
    // declared-offset repair the byte path emits it whenever
    // `crate::declared_layout` accepts it, so it outranks both authorities
    // below: for such a struct there is exactly one emitted layout and it is
    // the producer's. See the module docs, "What this predicate measures after
    // the declared-offset repair", for why that makes the comparison vacuous
    // for these rows and where the real check moved to.
    if let Some(declared) = declared_authority(sdef, module) {
        return LayoutAuthority::Single(declared);
    }

    let StructRepr::Packed(n) = sdef.repr else {
        return LayoutAuthority::Single(natural);
    };

    // Both authorities in full. See the module docs and
    // `designs/2026-08-03-trustir-to-lir-converter.md` §10.
    let Some(packed) = packed_authority(sdef, module) else {
        return LayoutAuthority::Split(split_reason(
            sdef,
            n,
            "unavailable (its own field translation failed)",
            &natural,
            "so the two cannot even be compared",
        ));
    };

    // C1. The packed clamp is a NO-OP whenever no field's natural alignment
    // exceeds `N`. Then both authorities compute the same offsets, the same
    // size and the same alignment: the compiler lays this struct out ONE way,
    // and refusing to score it hides real disagreements.
    if packed == natural {
        return LayoutAuthority::Single(packed);
    }

    // C2. "The producer agrees with NEITHER authority" is a TOTAL statement
    // over both, so it requires no authority choice and can be refused honestly.
    if !producer_matches(sdef, &packed) && !producer_matches(sdef, &natural) {
        let reason = format!(
            "`{}` is `#[repr(packed({n}))]` and its PRODUCER layout — {} — matches NEITHER of \
             trust-cg's two packed layout authorities. Authority P — `packed_struct_layout` / \
             `TrustIrAdapter::packed_field_offset` (`adapter.rs:11549`, reached from `StructGep` \
             at `:3302`, field insert at `:6934`, field extract at `:11654`, aggregate constant \
             at `:14541`) and `packed_struct_size` (`:11586`, array stride at `:3240` / `:6325`) \
             — says {}. Authority C — natural-C `Type::bytes()`/`align()`, which since the \
             2026-08-08 aggregate-constant repair survives as a SIZE/ALIGN authority only: \
             `TrustIrAdapter::translate_alloc` (`:8958-8963`) and `translate_heap_alloc` \
             (`:9163`) stride an element by `lir_ty.bytes()` where `Inst::GEP` strides by \
             `packed_struct_size`, and the aggregate-constant slot, the aggregate `Load` slot \
             and copy length, and the NON-packed `InsertField` arm's `Memmove` length still \
             measure the natural extent — says {}. (The PACKED `InsertField` arm's `Memmove` \
             length and the aggregate `Store` arm's moved to authority P with the \
             2026-08-08 nested-packed repair; they are no longer members of authority C.) \
             This verdict needs NO choice between the two: whichever authority \
             the byte path reaches for a given value, the producer's stated layout is wrong, so \
             the struct is REFUSED rather than reported.",
            sdef.name,
            render_producer_claim(sdef),
            packed.render(),
            natural.render(),
        );
        return LayoutAuthority::MatchesNeither {
            packed,
            natural,
            reason,
        };
    }

    LayoutAuthority::Split(split_reason(
        sdef,
        n,
        &packed.render(),
        &natural,
        "and the producer's own layout matches one of them, so scoring it would be scoring \
         against whichever authority this predicate happened to pick",
    ))
}

/// The `NotComparable` reason for a packed struct whose two authorities
/// disagree without the producer contradicting both.
fn split_reason(
    sdef: &StructDef,
    n: u32,
    packed_says: &str,
    natural: &AuthorityLayout,
    closing: &str,
) -> String {
    format!(
        "`{}` is `#[repr(packed({n}))]` and trust-cg has NO SINGLE LAYOUT AUTHORITY for it, \
         so the producer's layout cannot be scored against \"the\" emitted layout. \
         Authority P — `packed_struct_layout` / `TrustIrAdapter::packed_field_offset` \
         (`adapter.rs:11549`, reached from `StructGep` at `:3302`, field insert at `:6934`, \
         field extract at `:11654`, aggregate constant at `:14541`) and `packed_struct_size` \
         (`:11586`, array stride at `:3240` / `:6325`) — says {packed_says}. Authority C — \
         natural-C `Type::bytes()`/`align()`, which since the 2026-08-08 aggregate-constant \
         repair survives as a SIZE/ALIGN authority only: `TrustIrAdapter::translate_alloc` \
         (`:8958-8963`) and `translate_heap_alloc` (`:9163`) stride an element by \
         `lir_ty.bytes()` where `Inst::GEP` strides by `packed_struct_size`, and the \
         aggregate-constant slot, the aggregate `Load` slot and copy length, and the \
         NON-packed `InsertField` arm's `Memmove` length still measure the natural extent \
         — says {}. (The PACKED `InsertField` arm's `Memmove` length and the aggregate \
         `Store` arm's moved to authority P with the 2026-08-08 nested-packed repair; they \
         are no longer members of authority C.) Certifying agreement \
         would certify a struct the compiler sizes two ways, {closing}.",
        sdef.name,
        natural.render(),
    )
}

/// Run [`classify_struct_layout`] over every struct in `module`.
pub fn census_module_struct_layouts(module: &Module) -> StructLayoutCensus {
    StructLayoutCensus {
        rows: module
            .structs
            .iter()
            .map(|sdef| StructLayoutRow {
                struct_id: sdef.id,
                name: sdef.name.clone(),
                repr: sdef.repr,
                disposition: classify_struct_layout(sdef, module),
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::pred::Pred;
    use trust_ir::{
        ClosureTy, ClosureTyId, EnumDef, EnumId, EnumVariant, FieldDef, FuncTyId, RecordDef,
        RecordId,
    };

    /// Build a module holding a single struct definition.
    fn module_with(sdef: StructDef) -> Module {
        let mut module = Module::new("layout_refusal_test");
        module.add_struct(sdef);
        module
    }

    fn field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
        FieldDef {
            name: name.to_string(),
            ty,
            offset,
        }
    }

    fn struct_def(name: &str, fields: Vec<FieldDef>) -> StructDef {
        StructDef {
            id: StructId::new(0),
            name: name.to_string(),
            fields,
            size: None,
            align: None,
            repr: StructRepr::Rust,
        }
    }

    fn classify(sdef: StructDef) -> StructLayoutDisposition {
        let module = module_with(sdef);
        let only = module
            .structs
            .first()
            .expect("the fixture module holds exactly one struct");
        classify_struct_layout(only, &module)
    }

    // ---------------------------------------------------------------
    // ACCEPT CONTROL — without this every rejection test below could be
    // passing because the predicate rejects everything.
    // ---------------------------------------------------------------

    /// `{ ptr: *const u8, cap: u64, len: u64 }` with the offsets natural-C
    /// layout produces: 0 / 8 / 16.
    #[test]
    fn test_classify_matching_offsets_agrees() {
        let disposition = classify(struct_def(
            "RawVecInner",
            vec![
                field("ptr", Ty::Ptr, Some(0)),
                field("cap", Ty::U64, Some(8)),
                field("len", Ty::U64, Some(16)),
            ],
        ));
        assert_eq!(
            disposition,
            StructLayoutDisposition::Agrees,
            "matching producer offsets must classify as Agrees"
        );
        assert!(
            !disposition.is_refusal(),
            "an agreeing struct must not refuse"
        );
    }

    /// A second accept control at a shape where padding matters:
    /// `{ tag: u8, value: u32 }` -> 0 / 4, not 0 / 1.
    #[test]
    fn test_classify_padded_matching_offsets_agrees() {
        let disposition = classify(struct_def(
            "Tagged",
            vec![
                field("tag", Ty::U8, Some(0)),
                field("value", Ty::U32, Some(4)),
            ],
        ));
        assert_eq!(disposition, StructLayoutDisposition::Agrees);
    }

    // ---------------------------------------------------------------
    // REJECTION CASES
    // ---------------------------------------------------------------

    /// The canonical measured offender: rustc reorders a `repr(Rust)`
    /// `{ len: u64, cap: u64, ptr: *const u8 }`-shaped value so that a later
    /// declared field lands at byte 0. Natural-C recomputation disagrees.
    #[test]
    fn test_classify_reordered_struct_disagrees_load_bearing_naming_field() {
        let disposition = classify(struct_def(
            "RawTableInner",
            vec![
                // Producer (rustc, reorder-aware) puts `bucket_mask` at 8 and
                // `ctrl` at 0; natural-C would put them at 0 and 8.
                field("bucket_mask", Ty::U64, Some(8)),
                field("ctrl", Ty::Ptr, Some(0)),
            ],
        ));
        let StructLayoutDisposition::Disagrees { ref mismatches, .. } = disposition else {
            panic!("a reordered struct must classify as Disagrees, got {disposition:?}");
        };
        assert_eq!(
            mismatches.len(),
            2,
            "both swapped fields must be reported, got {mismatches:?}"
        );
        assert_eq!(mismatches[0].field_name, "bucket_mask");
        assert_eq!(mismatches[0].producer_offset, 8);
        assert_eq!(mismatches[0].recomputed_offset, 0);
        assert!(mismatches[0].load_bearing);
        assert_eq!(mismatches[1].field_name, "ctrl");
        assert_eq!(mismatches[1].producer_offset, 0);
        assert_eq!(mismatches[1].recomputed_offset, 8);
        assert!(mismatches[1].load_bearing);
        assert!(disposition.is_refusal());
        assert!(disposition.is_load_bearing_disagreement());
    }

    /// A disagreement on a field AFTER the first must still be caught — a
    /// predicate that inspects only field 0 passes this struct.
    #[test]
    fn test_classify_disagreement_on_later_field_is_caught() {
        let disposition = classify(struct_def(
            "LaterFieldMoves",
            vec![
                field("head", Ty::U64, Some(0)),
                field("a", Ty::U32, Some(12)),
                field("b", Ty::U32, Some(8)),
            ],
        ));
        let StructLayoutDisposition::Disagrees { ref mismatches, .. } = disposition else {
            panic!("a later-field disagreement must classify as Disagrees, got {disposition:?}");
        };
        assert_eq!(
            mismatches.iter().map(|m| m.field_index).collect::<Vec<_>>(),
            vec![1, 2],
            "field 0 agrees; fields 1 and 2 are swapped"
        );
        assert!(disposition.is_load_bearing_disagreement());
    }

    /// A disagreement that only relocates a zero-sized field is a
    /// disagreement, but NOT load-bearing — no byte that is ever loaded or
    /// stored changes address.
    #[test]
    fn test_classify_zst_only_disagreement_is_not_load_bearing() {
        let disposition = classify(struct_def(
            "WithMarker",
            vec![
                field("value", Ty::U64, Some(0)),
                // `Ty::Tuple(vec![])` lowers to `Type::Struct(vec![])`: 0
                // bytes, align 1. Natural-C recomputes its offset as 8; the
                // producer parked it at 0 (rustc places ZSTs freely).
                field("marker", Ty::Tuple(vec![]), Some(0)),
            ],
        ));
        let StructLayoutDisposition::Disagrees { ref mismatches, .. } = disposition else {
            panic!("a moved ZST is still a disagreement, got {disposition:?}");
        };
        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].field_name, "marker");
        assert_eq!(mismatches[0].producer_offset, 0);
        assert_eq!(mismatches[0].recomputed_offset, 8);
        assert!(
            !mismatches[0].load_bearing,
            "a zero-sized field moving is not load-bearing"
        );
        assert!(
            !disposition.is_load_bearing_disagreement(),
            "the census must not count a ZST-only move among the load-bearing rows"
        );
        assert!(
            disposition.is_refusal(),
            "it is still a producer/consumer disagreement and still refuses"
        );
    }

    /// The generic / param / opaque case: the producer's layout query declined
    /// and left every offset `None`. Distinct state, not an error.
    #[test]
    fn test_classify_all_none_offsets_is_layout_absent() {
        let disposition = classify(struct_def(
            "GenericPair",
            vec![field("left", Ty::U64, None), field("right", Ty::U64, None)],
        ));
        assert_eq!(disposition, StructLayoutDisposition::LayoutAbsent);
        assert!(
            !disposition.is_refusal(),
            "an absent layout is a census row, not a refusal"
        );
    }

    /// MIXED measured 0 today. Detect it anyway, so the day the producer mints
    /// one it is loud rather than half-checked.
    #[test]
    fn test_classify_half_none_offsets_is_the_mixed_defect() {
        let disposition = classify(struct_def(
            "HalfLaidOut",
            vec![
                field("known", Ty::U64, Some(0)),
                field("unknown", Ty::U64, None),
                field("also_known", Ty::U64, Some(16)),
            ],
        ));
        let StructLayoutDisposition::MixedOffsets {
            ref with_offset,
            ref without_offset,
        } = disposition
        else {
            panic!("a half-laid-out struct must classify as MixedOffsets, got {disposition:?}");
        };
        assert_eq!(with_offset, &vec![0, 2]);
        assert_eq!(without_offset, &vec![1]);
        assert!(
            disposition.is_refusal(),
            "a half-checked struct must refuse, not pass on the half that agrees"
        );
    }

    /// A struct whose field types do not all convert to LIR. `Ty::Rc` is
    /// fail-closed in the adapter (refcount ownership has no modelled ABI), so
    /// the consumer-side layout does not exist.
    #[test]
    fn test_classify_unconvertible_field_type_is_not_comparable() {
        let disposition = classify(struct_def(
            "Shared",
            vec![
                field("count", Ty::U64, Some(0)),
                field("inner", Ty::Rc(Box::new(Ty::U64)), Some(8)),
            ],
        ));
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("an unconvertible field must classify as NotComparable, got {disposition:?}");
        };
        assert!(
            reason.contains("Rc"),
            "the reason must name the adapter's refusal, got {reason:?}"
        );
        assert!(
            !disposition.is_refusal(),
            "NotComparable is a census row; the adapter's own type translation already rejects it"
        );
    }

    /// A field-less struct: vacuous agreement, stated explicitly.
    #[test]
    fn test_classify_fieldless_struct_agrees_vacuously() {
        assert_eq!(
            classify(struct_def("Unit", vec![])),
            StructLayoutDisposition::Agrees
        );
    }

    /// MIXED is checked before convertibility: a struct that is both mixed and
    /// unconvertible must report the producer-data defect, not hide behind the
    /// type failure.
    #[test]
    fn test_mixed_offsets_outrank_not_comparable() {
        let disposition = classify(struct_def(
            "MixedAndUnconvertible",
            vec![
                field("known", Ty::U64, Some(0)),
                field("inner", Ty::Rc(Box::new(Ty::U64)), None),
            ],
        ));
        assert!(
            matches!(disposition, StructLayoutDisposition::MixedOffsets { .. }),
            "expected MixedOffsets, got {disposition:?}"
        );
    }

    // ---------------------------------------------------------------
    // MODULE CENSUS
    // ---------------------------------------------------------------

    #[test]
    fn test_census_counts_every_disposition_and_refuses_on_disagreement() {
        let mut module = Module::new("census");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Agreeing".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U64, Some(8))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::C,
        });
        // A producer offset the byte path CANNOT honour: `b` is a `u64` parked
        // at 4 in a non-packed struct, which `crate::declared_layout`'s
        // coherence gate declines (rustc never mints it, and emitting it would
        // be an undeclared unaligned access). So this row keeps the
        // recomputation — `b` at 8 — and is still a scored, load-bearing
        // disagreement. A *reordered* struct with coherent totals is no longer
        // one; the byte path emits the producer's offsets for it. See
        // `test_a_reordered_struct_with_coherent_totals_is_now_emitted_as_declared`.
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Unaligned".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U64, Some(4))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        module.add_struct(StructDef {
            id: StructId::new(2),
            name: "Generic".to_string(),
            fields: vec![field("t", Ty::U64, None)],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        module.add_struct(StructDef {
            id: StructId::new(3),
            name: "Opaque".to_string(),
            fields: vec![field("rc", Ty::Rc(Box::new(Ty::U64)), Some(0))],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        module.add_struct(StructDef {
            id: StructId::new(4),
            name: "Half".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U64, None)],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });

        let census = census_module_struct_layouts(&module);
        assert_eq!(census.rows.len(), 5);
        assert_eq!(census.agrees(), 1, "Agreeing");
        assert_eq!(census.disagrees(), 1, "Unaligned");
        assert_eq!(census.load_bearing_disagreements(), 1, "Unaligned");
        assert_eq!(census.layout_absent(), 1, "Generic");
        assert_eq!(census.not_comparable(), 1, "Opaque");
        assert_eq!(census.mixed_offsets(), 1, "Half");
        assert!(census.refuses());

        let refused: Vec<&str> = census.refusals().map(|r| r.name.as_str()).collect();
        assert_eq!(refused, vec!["Unaligned", "Half"]);
    }

    /// THE REPAIR, seen by this predicate. `#[repr(Rust)] { small: u8,
    /// big: u64 }` — (c) MEASURED with stock `rustc 1.97.0`, `big@0 small@8`,
    /// size 16, align 8 — used to be the canonical `Disagrees`: the byte path
    /// recomputed `small@0 big@8` and addressed both fields at the wrong place.
    ///
    /// Since the declared-offset repair the byte path READS those offsets, so
    /// there is one emitted layout and it is the producer's. This row agreeing
    /// is not the predicate going soft — `crate::declared_layout` is what the
    /// authority selection asks, so if the adapter stopped honouring the
    /// declared offsets this would go straight back to `Disagrees`.
    #[test]
    fn test_a_reordered_struct_with_coherent_totals_is_now_emitted_as_declared() {
        let sdef = StructDef {
            id: StructId::new(0),
            name: "Reordered".to_string(),
            fields: vec![
                field("small", Ty::U8, Some(8)),
                field("big", Ty::U64, Some(0)),
            ],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        };
        // The recomputation really does disagree — this is the divergence, not
        // a fixture that never had one.
        let lir = Type::Struct(vec![Type::I8, Type::I64]);
        assert_eq!(lir.offset_of(0), Some(0), "natural C puts `small` at 0");
        assert_eq!(lir.offset_of(1), Some(8), "natural C puts `big` at 8");

        assert_eq!(classify(sdef), StructLayoutDisposition::Agrees);
    }

    /// A size-only divergence is a census row of its own and must refuse.
    #[test]
    fn test_census_counts_a_size_only_disagreement_and_refuses() {
        let mut module = Module::new("size_census");
        module.add_struct(sized_struct(
            "TrailPad",
            vec![field("a", Ty::U64, Some(0)), field("b", Ty::U8, Some(8))],
            9,
            1,
        ));
        let census = census_module_struct_layouts(&module);
        assert_eq!(census.agrees(), 0);
        assert_eq!(census.disagrees(), 1);
        assert_eq!(census.size_disagreements(), 1);
        assert_eq!(
            census.load_bearing_disagreements(),
            0,
            "no field moved: the load-bearing FIELD figure must stay comparable"
        );
        assert!(census.refuses());
    }

    /// ACCEPT CONTROL for the census: a module in which every struct agrees
    /// must NOT refuse. Without this the `refuses()` assertion above could be
    /// passing because `refuses()` is unconditionally true.
    #[test]
    fn test_census_all_agreeing_module_does_not_refuse() {
        let mut module = Module::new("census_clean");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "A".to_string(),
            fields: vec![field("x", Ty::U32, Some(0)), field("y", Ty::U32, Some(4))],
            size: Some(8),
            align: Some(4),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "B".to_string(),
            fields: vec![field("only", Ty::Ptr, Some(0))],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
        });

        let census = census_module_struct_layouts(&module);
        assert_eq!(census.agrees(), 2);
        assert_eq!(census.disagrees(), 0);
        assert!(!census.refuses(), "a fully agreeing module must not refuse");
        assert_eq!(census.refusals().count(), 0);
    }

    // ---------------------------------------------------------------
    // D1 — struct SIZE / ALIGN divergence is its own mismatch kind.
    // ---------------------------------------------------------------

    fn sized_struct(name: &str, fields: Vec<FieldDef>, size: u64, align: u64) -> StructDef {
        StructDef {
            id: StructId::new(0),
            name: name.to_string(),
            fields,
            size: Some(size),
            align: Some(align),
            repr: StructRepr::Rust,
        }
    }

    /// `{ a: u64@0, b: u8@8 }` — every field offset agrees, and the producer's
    /// recorded size (9, align 1) still contradicts the byte path (16, align
    /// 8). `StructDef::size` / `align` are `Some` exactly when the offsets are,
    /// so this data is free; without comparing it the row is certified clean.
    #[test]
    fn test_classify_size_divergence_disagrees_without_any_field_moving() {
        let disposition = classify(sized_struct(
            "TrailPad",
            vec![field("a", Ty::U64, Some(0)), field("b", Ty::U8, Some(8))],
            9,
            1,
        ));
        let StructLayoutDisposition::Disagrees {
            ref mismatches,
            ref size,
        } = disposition
        else {
            panic!("a diverging total size must classify as Disagrees, got {disposition:?}");
        };
        assert!(
            mismatches.is_empty(),
            "no FIELD moves; this is not a field-offset mismatch, got {mismatches:?}"
        );
        let size = size
            .as_ref()
            .expect("the size divergence must be reported as its own mismatch kind");
        assert_eq!(size.producer_size, Some(9));
        assert_eq!(size.recomputed_size, 16, "natural-C pads the struct to 16");
        assert_eq!(size.producer_align, Some(1));
        assert_eq!(size.recomputed_align, 8);
        assert!(size.size_differs());
        assert!(size.align_differs());
        assert!(
            disposition.is_size_disagreement(),
            "the census must be able to count this row"
        );
        assert!(
            !disposition.is_load_bearing_disagreement(),
            "no field moved, so this is not a load-bearing FIELD disagreement"
        );
        assert!(
            disposition.is_refusal(),
            "a wrong size is a wrong stride, a wrong allocation and a wrong memcpy length"
        );
    }

    /// ACCEPT CONTROL for D1: the same shape with the size the byte path
    /// actually computes must still agree — the size check must not reject
    /// every struct that records one.
    #[test]
    fn test_classify_matching_size_and_align_still_agrees() {
        assert_eq!(
            classify(sized_struct(
                "TrailPad",
                vec![field("a", Ty::U64, Some(0)), field("b", Ty::U8, Some(8))],
                16,
                8,
            )),
            StructLayoutDisposition::Agrees
        );
    }

    /// ALIGNMENT alone is enough: `{ a: u32@0 }` at align 8 is not the align 4
    /// the byte path computes.
    #[test]
    fn test_classify_align_only_divergence_is_reported() {
        let disposition = classify(sized_struct(
            "OverAligned",
            vec![field("a", Ty::U32, Some(0))],
            4,
            8,
        ));
        let size = disposition
            .size_mismatch()
            .expect("an align-only divergence must still be reported");
        assert!(!size.size_differs(), "the size agrees");
        assert!(size.align_differs());
        assert_eq!(size.recomputed_align, 4);
    }

    // D1 x D5 lived here: it asserted a packed struct's SIZE is scored against
    // `packed_struct_size`. N2 retired that claim — the packed SIZE authority
    // is split exactly as the offset authority is, so there is no single stride
    // to score against. Its successor is
    // `test_classify_packed_size_is_not_comparable_either`, in the D5/N2 block.

    /// The niche-optimised class D1 names: an `Option<&T>`-shaped enum field is
    /// 8 bytes to the producer and 16 on the byte path, while its ONE offset
    /// (0) agrees. The size comparison catches it and REFUSES; the enum
    /// interior gate would only have produced a non-refusing census row, so the
    /// measured disagreement deliberately outranks it.
    #[test]
    fn test_classify_niche_enum_field_is_not_certified_clean() {
        let mut module = Module::new("niche");
        module.add_enum(EnumDef::new(
            EnumId::new(0),
            "OptionRef",
            vec![
                EnumVariant {
                    name: "None".to_string(),
                    fields: vec![],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "Some".to_string(),
                    fields: vec![Ty::Ptr],
                    field_names: vec![],
                },
            ],
        ));
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "HoldsOption".to_string(),
            // rustc niche-optimises this to 8 bytes; LIR synthesizes 16.
            fields: vec![field("opt", Ty::Enum(EnumId::new(0)), Some(0))],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        let disposition = classify_struct_layout(&module.structs[0], &module);
        assert_ne!(
            disposition,
            StructLayoutDisposition::Agrees,
            "a niche-optimised enum field must never be certified clean"
        );
        let size = disposition
            .size_mismatch()
            .expect("the 8-vs-16 size divergence is what catches this class");
        assert_eq!(size.producer_size, Some(8));
        assert_eq!(size.recomputed_size, 16, "LIR synthesizes tag + payload");
        assert!(
            disposition.mismatches().is_empty(),
            "the single field still sits at 0 on both sides"
        );
        assert!(
            disposition.is_refusal(),
            "a 2x size error must refuse, not become a census row"
        );
    }

    /// A struct that BOTH has an unmeasurable interior and a real offset
    /// disagreement must refuse. `NotComparable` does not refuse, so letting
    /// the interior gate outrank the measurement would silently drop it.
    #[test]
    fn test_measured_disagreement_outranks_an_unmeasurable_interior() {
        let disposition = classify(struct_def(
            "TupleAndReordered",
            vec![
                field("t", Ty::Tuple(vec![Ty::U8, Ty::U64]), Some(0)),
                // The byte path puts `after` at 16; the producer says 24.
                field("after", Ty::U64, Some(24)),
            ],
        ));
        let StructLayoutDisposition::Disagrees { ref mismatches, .. } = disposition else {
            panic!("a measured disagreement must outrank the interior gap, got {disposition:?}");
        };
        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].field_name, "after");
        assert_eq!(mismatches[0].recomputed_offset, 16);
        assert!(disposition.is_refusal());
    }

    // ---------------------------------------------------------------
    // D2 — a nested `Ty::Tuple` carries no producer offsets.
    // ---------------------------------------------------------------

    /// `Ty::Tuple` has no [`trust_ir::FieldDef`], so it has no producer
    /// offsets: the byte path lowers `(u8, u64)` natural-C (0 / 8) while rustc
    /// reorders it (8 / 0). The outer offsets agree because the sizes coincide,
    /// so the interior divergence is invisible unless it is named.
    #[test]
    fn test_classify_multi_field_tuple_interior_is_not_comparable() {
        let disposition = classify(struct_def(
            "HasTuple",
            vec![
                field("t", Ty::Tuple(vec![Ty::U8, Ty::U64]), Some(0)),
                field("after", Ty::U64, Some(16)),
            ],
        ));
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("a multi-field tuple interior must be NotComparable, got {disposition:?}");
        };
        assert!(
            reason.contains('t') && reason.to_lowercase().contains("tuple"),
            "the reason must name the field and the tuple, got {reason:?}"
        );
    }

    /// ACCEPT CONTROL for D2: a tuple that cannot be reordered observably (one
    /// non-ZST element) must still be compared, not swallowed by the gate.
    #[test]
    fn test_classify_single_element_tuple_is_still_compared() {
        assert_eq!(
            classify(struct_def(
                "HasTinyTuple",
                vec![
                    field("t", Ty::Tuple(vec![Ty::U64]), Some(0)),
                    field("after", Ty::U64, Some(8)),
                ],
            )),
            StructLayoutDisposition::Agrees,
            "a one-element tuple has no interior reordering freedom"
        );
    }

    // ---------------------------------------------------------------
    // D3 — an enum payload interior, for the COMMON (descriptor-less) enum.
    // ---------------------------------------------------------------

    fn module_with_layoutless_enum_field() -> Module {
        let mut module = Module::new("enum_interior");
        module.add_enum(EnumDef::new(
            EnumId::new(0),
            "E",
            vec![
                EnumVariant {
                    name: "A".to_string(),
                    fields: vec![Ty::U64],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "B".to_string(),
                    fields: vec![],
                    field_names: vec![],
                },
            ],
        ));
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "HasEnum".to_string(),
            fields: vec![
                field("e", Ty::Enum(EnumId::new(0)), Some(0)),
                field("x", Ty::U64, Some(16)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        module
    }

    /// The adapter fail-closes only when `EnumDef.layout` / `discriminants` /
    /// `repr` are PRESENT. The common enum has none of them: it translates to
    /// LIR's *synthesized* tagged-union layout, which is not rustc's, and there
    /// are no producer offsets inside the payload to compare against.
    #[test]
    fn test_classify_layoutless_enum_payload_is_not_comparable() {
        let module = module_with_layoutless_enum_field();
        let disposition = classify_struct_layout(&module.structs[0], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("a descriptor-less enum payload must be NotComparable, got {disposition:?}");
        };
        assert!(
            reason.contains('e') && reason.contains('E'),
            "the reason must name the field and the enum, got {reason:?}"
        );
    }

    // ---------------------------------------------------------------
    // D4 / N1 — a struct-id collision is its OWN disposition, and a refusal.
    //
    // Both of the earlier answers were wrong, and provably so:
    //   * resolving `Ty::Struct(sdef.id)` measures ANOTHER struct's fields and
    //     mints a false `Agrees` for the shadowed def;
    //   * translating `sdef`'s OWN fields measures a layout NOBODY EMITS — the
    //     byte path addresses every `Second` value with `First`'s layout.
    // The truth is that the module is malformed, and it must refuse.
    // ---------------------------------------------------------------

    fn module_with_colliding_struct_ids() -> Module {
        let mut module = Module::new("collision");
        // `Module::add_struct` honours declared ids verbatim with NO collision
        // check (trust-ir/src/lib.rs:1010-1014), so two defs can share an id.
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "First".to_string(),
            fields: vec![field("x", Ty::U64, Some(0)), field("y", Ty::U8, Some(8))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Second".to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U8, Some(1))],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        module
    }

    /// `Second` declares `{ a: u8@0, b: u8@1 }`, which is exactly what
    /// natural-C recomputes for its own fields — so measuring `Second`'s own
    /// fields answers `Agrees`. That is a FALSE certification: the byte path
    /// resolves `Ty::Struct(0)` to `First` (`adapter.rs:1250`, first match), so
    /// every `Second` value is addressed with `First`'s 16-byte layout and `b`
    /// lands at 8, not 1. The disposition must name the collision, and refuse.
    #[test]
    fn test_classify_colliding_struct_id_is_its_own_refusing_disposition() {
        let module = module_with_colliding_struct_ids();
        let disposition = classify_struct_layout(&module.structs[1], &module);
        let StructLayoutDisposition::StructIdCollision {
            struct_id,
            ref resolved_name,
            resolved_index,
        } = disposition
        else {
            panic!("a shadowed struct id must be its own disposition, got {disposition:?}");
        };
        assert_eq!(struct_id, StructId::new(0));
        assert_eq!(
            resolved_name, "First",
            "the reason must name the def the byte path actually resolves the id to"
        );
        assert_eq!(resolved_index, 0);
        assert!(
            disposition.is_refusal(),
            "every value of the shadowed type is addressed with another struct's layout: \
             strictly worse than a field disagreement, so it must block emission"
        );
        assert!(
            !disposition.is_load_bearing_disagreement() && !disposition.is_size_disagreement(),
            "a collision is not a measured field/size disagreement and must not pollute those \
             figures"
        );
        assert!(disposition.mismatches().is_empty());
    }

    /// The other half of N1: with NO collision, the predicate must measure the
    /// layout the byte path emits — i.e. resolving by id and translating
    /// `sdef`'s own fields must be the same measurement. `Shadowed` here is
    /// byte-identical to the def that owns the id, so the byte path's first
    /// match IS this struct and there is nothing malformed to report.
    #[test]
    fn test_classify_byte_identical_duplicate_id_is_not_a_collision() {
        let mut module = Module::new("identical_dup");
        let twin = |name: &str| StructDef {
            id: StructId::new(0),
            name: name.to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U8, Some(1))],
            size: Some(2),
            align: Some(1),
            repr: StructRepr::Rust,
        };
        module.add_struct(twin("Twin"));
        module.add_struct(twin("Twin"));
        assert_eq!(
            classify_struct_layout(&module.structs[1], &module),
            StructLayoutDisposition::Agrees,
            "two byte-identical defs shadow each other harmlessly: the resolved layout IS this \
             struct's layout, so the module is not malformed"
        );
    }

    /// The collision is reported for the SHADOWED def only. The struct that
    /// legitimately owns id 0 is what the byte path resolves to, so its own
    /// layout is the emitted one and it is measured normally.
    #[test]
    fn test_classify_colliding_struct_id_first_owner_still_agrees() {
        let module = module_with_colliding_struct_ids();
        assert_eq!(
            classify_struct_layout(&module.structs[0], &module),
            StructLayoutDisposition::Agrees
        );
    }

    /// The collision gate outranks the classification's own steps 1-7: under a
    /// collision `sdef`'s producer data describes nothing that is emitted, so
    /// even a MIXED-offsets defect in the shadowed def is subordinate to it.
    #[test]
    fn test_struct_id_collision_outranks_the_shadowed_defs_own_defects() {
        let mut module = Module::new("collision_mixed");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Owner".to_string(),
            fields: vec![field("x", Ty::U64, Some(0))],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "ShadowedAndMixed".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U64, None)],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        assert!(
            matches!(
                classify_struct_layout(&module.structs[1], &module),
                StructLayoutDisposition::StructIdCollision { .. }
            ),
            "the collision invalidates the shadowed def's own offsets, mixed or not"
        );
    }

    /// The census counts collisions as their own row kind and refuses on them.
    #[test]
    fn test_census_counts_a_struct_id_collision_and_refuses() {
        let module = module_with_colliding_struct_ids();
        let census = census_module_struct_layouts(&module);
        assert_eq!(census.struct_id_collisions(), 1, "`Second` is shadowed");
        assert_eq!(census.agrees(), 1, "`First` owns the id");
        assert_eq!(census.disagrees(), 0);
        assert!(census.refuses());
        let refused: Vec<&str> = census.refusals().map(|r| r.name.as_str()).collect();
        assert_eq!(refused, vec!["Second"]);
    }

    /// ACCEPT CONTROL for N1: distinct ids are the overwhelmingly normal case
    /// and must not be reported as collisions.
    #[test]
    fn test_distinct_struct_ids_are_never_reported_as_a_collision() {
        let mut module = Module::new("distinct_ids");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "A".to_string(),
            fields: vec![field("x", Ty::U64, Some(0))],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "B".to_string(),
            fields: vec![field("y", Ty::U8, Some(0))],
            size: Some(1),
            align: Some(1),
            repr: StructRepr::C,
        });
        let census = census_module_struct_layouts(&module);
        assert_eq!(census.struct_id_collisions(), 0);
        assert_eq!(census.agrees(), 2);
        assert!(!census.refuses());
    }

    // ---------------------------------------------------------------
    // D5 / N2 — `repr(packed)` has NO SINGLE AUTHORITY in trust-cg.
    //
    // D5 scored packed structs against `packed_struct_layout`. That was right
    // only by accident: `fill_aggregate_at_ptr` was NOT one of
    // `packed_field_offset`'s call sites and laid the SAME struct out
    // natural-C. The 2026-08-08 repair put it on `packed_field_offset`
    // (adapter.rs:14541), closing the OFFSET half of the split; the SIZE half
    // survives (`translate_alloc`'s natural stride at `:8958-8963` vs
    // `Inst::GEP`'s `packed_struct_size` at `:6325`). Certifying `Agrees`
    // still certifies a struct the compiler sizes two ways, so the only honest
    // disposition is `NotComparable` naming both.
    // ---------------------------------------------------------------

    fn packed_struct(name: &str, n: u32, fields: Vec<FieldDef>) -> StructDef {
        StructDef {
            id: StructId::new(0),
            name: name.to_string(),
            fields,
            size: None,
            align: None,
            repr: StructRepr::Packed(n),
        }
    }

    /// THE DOMINANCE LEMMA the aggregate-constant repair rests on.
    ///
    /// The 2026-08-08 repair moved `fill_aggregate_at_ptr`'s field addressing
    /// onto authority P but deliberately left its stack SLOT at authority C's
    /// natural size (see the module docs' **Named gaps**). That is only safe
    /// if the natural-C slot always CONTAINS the packed extent — otherwise
    /// moving the offsets down would push a store past the slot end.
    ///
    /// It always does, and the reason is structural rather than empirical: the
    /// packed clamp is `min(natural_align, N)` with both operands powers of
    /// two, so it only ever LOWERS an alignment; `align_to` is monotone in its
    /// operand and non-increasing as the alignment shrinks; and the final
    /// round-up is to a smaller-or-equal struct alignment. So authority P is
    /// pointwise `<=` authority C on every offset, on the size and on the
    /// align.
    ///
    /// (c) MEASURED here over `8^3 x |{1,2,4,8}| = 2048` shapes: every
    /// three-field combination of `{u8, u16, u32, u64, bool, f32, f64, ptr}`
    /// crossed with `packed(1|2|4|8)`.
    ///
    /// Mutation-pinned: this is the assertion that fails the moment anyone
    /// makes the packed clamp round a field UP.
    #[test]
    fn test_packed_authority_is_dominated_by_natural_c() {
        let tys = [
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::Bool,
            Ty::F32,
            Ty::F64,
            Ty::Ptr,
        ];
        let mut checked = 0usize;
        for a in &tys {
            for b in &tys {
                for c in &tys {
                    for n in [1u32, 2, 4, 8] {
                        let sdef = packed_struct(
                            "Dom",
                            n,
                            vec![
                                field("a", a.clone(), None),
                                field("b", b.clone(), None),
                                field("c", c.clone(), None),
                            ],
                        );
                        let module = module_with(sdef);
                        let only = module.structs.first().expect("one struct");
                        let packed =
                            packed_authority(only, &module).expect("scalar fields always convert");
                        let lir = translate_type_with_enum_tables(
                            &Ty::Struct(only.id),
                            &module.structs,
                            &module.types,
                            &module.enums,
                            &module.records,
                            &module.closure_types,
                        )
                        .expect("scalar fields always convert");
                        let natural = natural_authority(only.fields.len(), &lir)
                            .expect("Type::Struct offsets are total");
                        for (i, (p, cc)) in packed
                            .offsets
                            .iter()
                            .zip(natural.offsets.iter())
                            .enumerate()
                        {
                            assert!(
                                p <= cc,
                                "packed({n}) {a:?}/{b:?}/{c:?}: field {i} packed offset {p} \
                                 exceeds natural {cc}; the natural-C slot would no longer \
                                 contain the packed extent"
                            );
                        }
                        assert!(
                            packed.size <= natural.size,
                            "packed({n}) {a:?}/{b:?}/{c:?}: packed size {} exceeds natural {}",
                            packed.size,
                            natural.size
                        );
                        assert!(
                            packed.align <= natural.align,
                            "packed({n}) {a:?}/{b:?}/{c:?}: packed align {} exceeds natural {}",
                            packed.align,
                            natural.align
                        );
                        checked += 1;
                    }
                }
            }
        }
        assert_eq!(checked, 2048, "the sweep must cover every shape it claims");
    }

    /// Both authorities must be NAMED, and both of their measurements quoted:
    /// for `#[repr(packed)] { a: u8@0, b: u64@1 }` authority P says offset 1 /
    /// size 9 and authority C says offset 8 / size 16.
    #[test]
    fn test_classify_packed_struct_is_not_comparable_naming_both_authorities() {
        let disposition = classify(packed_struct(
            "Packed1",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
        ));
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!(
                "a packed struct has two disagreeing layout authorities and cannot be scored \
                 against either, got {disposition:?}"
            );
        };
        assert!(
            reason.contains("packed_field_offset") && reason.contains("translate_alloc"),
            "the reason must NAME both disagreeing authorities — and authority C by a site \
             that is still natural-C, not by the repaired `fill_aggregate_at_ptr`, \
             got {reason:?}"
        );
        assert!(
            !reason.contains("fill_aggregate_at_ptr (`adapter.rs:14519`)"),
            "the repaired site must not be cited as a live divergence, got {reason:?}"
        );
        assert!(
            reason.contains("[0, 1]") && reason.contains("size 9"),
            "authority P's measurement must be quoted, got {reason:?}"
        );
        assert!(
            reason.contains("[0, 8]") && reason.contains("size 16"),
            "authority C's measurement must be quoted, got {reason:?}"
        );
        assert!(
            !disposition.is_refusal(),
            "the DEFECT is in trust-cg's packed lane, not in this struct: this predicate has \
             nothing to say about it, and saying nothing is not a refusal"
        );
    }

    /// Which of the two authorities the producer agrees with does not change
    /// the answer, and that is the point: under D5 the `packed(4)` shape was
    /// `Disagrees`, which was right only by accident — it scored against ONE of
    /// two authorities. `#[repr(packed(4))]`, the libc `log2phys` shape, and
    /// `#[repr(packed)]` with NATURAL-C producer offsets land on the same
    /// honest non-answer.
    ///
    /// The case that used to sit here and no longer does is
    /// `PackedAgreeingWithNeither` — see
    /// `test_packed_matching_neither_authority_is_refused`. Agreeing with
    /// NEITHER authority is a total statement that needs no authority choice,
    /// so it is a refusal, not a non-answer; asserting `NotComparable` for it
    /// was defect C2 written down as a test.
    #[test]
    fn test_classify_packed_is_not_comparable_whichever_authority_the_producer_matches() {
        for (name, n, fields) in [
            (
                "Packed4",
                4u32,
                vec![
                    field("l2p_flags", Ty::U32, Some(0)),
                    field("l2p_contigbytes", Ty::U64, Some(4)),
                ],
            ),
            (
                "PackedButPadded",
                1,
                vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(8))],
            ),
        ] {
            let disposition = classify(packed_struct(name, n, fields));
            assert!(
                matches!(disposition, StructLayoutDisposition::NotComparable { .. }),
                "{name}: packed has no single authority to score against, got {disposition:?}"
            );
        }
    }

    /// A packed struct that ALSO records a size gets the same answer. Since the
    /// 2026-08-08 repair the SIZE split is the one that survives:
    /// `packed_struct_size` (the `Inst::GEP` element stride,
    /// `adapter.rs:6325`) versus natural-C `Type::bytes()` (the
    /// `translate_alloc` element stride at `:8958-8963` and the
    /// aggregate-constant slot at `:14285-14287`). So there is still no total
    /// to score.
    #[test]
    fn test_classify_packed_size_is_not_comparable_either() {
        let mut sdef = packed_struct(
            "Packed1Sized",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
        );
        sdef.size = Some(9);
        sdef.align = Some(1);
        let disposition = classify(sdef);
        assert!(
            matches!(disposition, StructLayoutDisposition::NotComparable { .. }),
            "got {disposition:?}"
        );
        assert!(
            !disposition.is_size_disagreement(),
            "the 9-vs-16 total is a symptom of the split authority, not a producer/consumer \
             disagreement this predicate can attribute"
        );
    }

    /// ACCEPT CONTROL for N2: the packed gate must key on `repr`, not on
    /// "anything with a u8 next to a u64". The same fields under `repr(C)` have
    /// ONE authority and are still measured — and still refuse when they move.
    #[test]
    fn test_non_packed_reprs_are_unaffected_by_the_packed_gate() {
        for repr in [StructRepr::Rust, StructRepr::C, StructRepr::Transparent] {
            let mut agreeing = struct_def(
                "NotPacked",
                vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(8))],
            );
            agreeing.repr = repr;
            assert_eq!(
                classify(agreeing),
                StructLayoutDisposition::Agrees,
                "{repr:?} has a single authority and natural-C puts `b` at 8"
            );

            let mut moved = struct_def(
                "NotPackedMoved",
                vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
            );
            moved.repr = repr;
            let disposition = classify(moved);
            assert!(
                disposition.is_refusal(),
                "{repr:?}: a moved field must still refuse, got {disposition:?}"
            );
        }
    }

    // ---------------------------------------------------------------
    // D6 — the predicate must be TOTAL.
    // ---------------------------------------------------------------

    /// `Type::Array(elem, count).bytes()` is unchecked `u32` multiplication
    /// (`types.rs:124`): debug aborts, release WRAPS and a wrapped offset can
    /// mint either verdict. The predicate must answer `NotComparable`.
    #[test]
    fn test_classify_overflowing_array_field_is_not_comparable_not_a_panic() {
        let mut module = Module::new("huge");
        let elem = module.add_type(Ty::U64);
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Huge".to_string(),
            fields: vec![
                field("big", Ty::Array(elem, u64::from(u32::MAX)), Some(0)),
                field("tail", Ty::U8, Some(0)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        let disposition = classify_struct_layout(&module.structs[0], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("an unrepresentable layout must be NotComparable, got {disposition:?}");
        };
        assert!(
            reason.contains("Huge"),
            "the reason must name the struct, got {reason:?}"
        );
    }

    /// N3: this test used to claim it pinned the interior scan's
    /// `seen: Vec<StructId>` cycle guard. It never did — and could not: the
    /// fixture is answered at classification step 3a by the ADAPTER's own
    /// `MAX_TYPE_TRANSLATION_DEPTH`, long before `interior_layout_gap` runs.
    /// (Falsifier, measured: neutering the guard to `if false && seen.contains`
    /// left the module's 31 tests passing with no hang.) The guard was removed
    /// as dead rather than left reading as coverage; the scan's termination
    /// rests on `MAX_INTERIOR_SCAN_DEPTH`, and no cycle can reach it because
    /// every edge the scan follows the translation follows first.
    ///
    /// So this now pins what actually happens, and asserts the reason names the
    /// authority that produced it — which is what makes it non-vacuous.
    #[test]
    fn test_a_self_referential_struct_is_answered_by_the_translation_depth_limit() {
        let mut module = Module::new("cyclic");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Node".to_string(),
            fields: vec![
                field("next", Ty::Struct(StructId::new(0)), Some(0)),
                field("t", Ty::Tuple(vec![Ty::U8, Ty::U64]), Some(8)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        let disposition = classify_struct_layout(&module.structs[0], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("a cyclic struct is not comparable, got {disposition:?}");
        };
        assert!(
            reason.contains("recursion limit"),
            "the ADAPTER's translation depth limit is what answers this, not any guard in the \
             interior scan; if this stops holding the scan's own termination needs re-proving. \
             Got {reason:?}"
        );
        assert!(
            reason.contains("`next`"),
            "the offending field must be named, got {reason:?}"
        );
    }

    // A companion test asserting the interior scan's own
    // `MAX_INTERIOR_SCAN_DEPTH` bound was DROPPED rather than shipped: the same
    // falsifier that exposed the `seen` guard exposes it. Neutering the bound
    // to `if false && depth >= MAX_INTERIOR_SCAN_DEPTH` left all 45 tests
    // passing with no hang, including a deliberate 200-deep `Link{i}` chain —
    // because a chain that deep blows the adapter's own
    // `MAX_TYPE_TRANSLATION_DEPTH` at step 3a first, exactly as the cyclic
    // fixture above does. The bound stays in the source as a STRUCTURAL
    // totality guarantee (it makes `interior_layout_gap` total without
    // depending on the adapter's behaviour, which the removed `seen` guard did
    // NOT do — a `Tuple`/`Array` chain repeats no `StructId`), but it is not
    // claimed to be covered.

    // ---------------------------------------------------------------
    // N4 — `Ty::Record` and `Ty::Closure` are the SAME interior gap as
    // `Ty::Tuple`: the adapter lowers all three to an identical synthesized
    // `Type::Struct` with no producer offsets anywhere inside.
    // ---------------------------------------------------------------

    fn module_with_record(field_tys: Vec<Ty>) -> Module {
        let mut module = Module::new("record_interior");
        module.records.push(RecordDef {
            id: RecordId::new(0),
            name: "R".to_string(),
            fields: field_tys
                .into_iter()
                .enumerate()
                .map(|(i, ty)| field(&format!("f{i}"), ty, None))
                .collect(),
        });
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "HasRecord".to_string(),
            fields: vec![
                field("r", Ty::Record(RecordId::new(0)), Some(0)),
                field("after", Ty::U64, Some(16)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        module
    }

    fn module_with_closure(captures: Vec<Ty>) -> Module {
        let mut module = Module::new("closure_interior");
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures,
        });
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "HasClosure".to_string(),
            fields: vec![
                field("c", Ty::Closure(ClosureTyId::new(0)), Some(0)),
                field("after", Ty::U64, Some(16)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        module
    }

    /// `Ty::Record(u8, u64)` lowers to the identical `Type::Struct([I8, I64])`
    /// a `Ty::Tuple(u8, u64)` does (`adapter.rs:1406-1433`), and `RecordDef`'s
    /// fields carry `offset: None` by construction. The containing struct's
    /// offsets agree because the total sizes coincide — exactly the way the
    /// tuple gap hides — so the record interior must be named.
    #[test]
    fn test_classify_multi_field_record_interior_is_not_comparable() {
        let module = module_with_record(vec![Ty::U8, Ty::U64]);
        let disposition = classify_struct_layout(&module.structs[0], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("a multi-field record interior must be NotComparable, got {disposition:?}");
        };
        assert!(
            reason.to_lowercase().contains("record") && reason.contains("`R`"),
            "the reason must name the construct and the record, got {reason:?}"
        );
        assert!(
            reason.contains("`r`"),
            "the reason must name the field, got {reason:?}"
        );
    }

    /// ACCEPT CONTROL for the record half of N4: a record with at most one
    /// non-ZST field has no observable reordering freedom and must still be
    /// compared, not swallowed by the gate.
    #[test]
    fn test_classify_single_field_record_is_still_compared() {
        let mut module = module_with_record(vec![Ty::U64]);
        module.structs[0].fields[1].offset = Some(8);
        assert_eq!(
            classify_struct_layout(&module.structs[0], &module),
            StructLayoutDisposition::Agrees,
            "a one-field record has no interior reordering freedom"
        );
    }

    /// `ClosureTy::captures` is a bare `Vec<Ty>` — not even a `FieldDef` to
    /// hang an offset on — and the adapter lowers it to the same synthesized
    /// aggregate (`adapter.rs:1443-1467`). rustc reorders closure captures.
    #[test]
    fn test_classify_multi_capture_closure_interior_is_not_comparable() {
        let module = module_with_closure(vec![Ty::U8, Ty::U64]);
        let disposition = classify_struct_layout(&module.structs[0], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("a multi-capture closure interior must be NotComparable, got {disposition:?}");
        };
        assert!(
            reason.to_lowercase().contains("closure") && reason.contains("captures"),
            "the reason must name the construct, got {reason:?}"
        );
        assert!(
            reason.contains("`c`"),
            "the reason must name the field, got {reason:?}"
        );
    }

    /// ACCEPT CONTROL for the closure half of N4.
    #[test]
    fn test_classify_single_capture_closure_is_still_compared() {
        let mut module = module_with_closure(vec![Ty::U64]);
        module.structs[0].fields[1].offset = Some(8);
        assert_eq!(
            classify_struct_layout(&module.structs[0], &module),
            StructLayoutDisposition::Agrees,
            "a one-capture closure has no interior reordering freedom"
        );
    }

    /// The gap is followed through nesting, like the tuple one: a record buried
    /// inside an inner struct is still reported, with the path to it.
    #[test]
    fn test_classify_record_nested_inside_an_inner_struct_is_not_comparable() {
        let mut module = module_with_record(vec![Ty::U8, Ty::U64]);
        // `HasRecord` is id 0; wrap it.
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Outer".to_string(),
            fields: vec![
                field("inner", Ty::Struct(StructId::new(0)), Some(0)),
                field("tail", Ty::U64, Some(24)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        let disposition = classify_struct_layout(&module.structs[1], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("a record one struct deep is still a gap, got {disposition:?}");
        };
        assert!(
            reason.contains("`inner`") && reason.contains("`r`"),
            "the reason must name the path to the record, got {reason:?}"
        );
    }

    // ---------------------------------------------------------------
    // N5 — D1's size/align comparison must run whenever the producer recorded
    // a size, INDEPENDENTLY of whether it recorded any offsets.
    // ---------------------------------------------------------------

    /// A struct whose layout query succeeded (so `size`/`align` are `Some`) but
    /// whose per-field offsets were all dropped by the bounds check at
    /// `trust-thir-lower/src/lib.rs:9328`. Returning `LayoutAbsent` before the
    /// size comparison leaves the 9-vs-16 divergence unreported — a wrong
    /// stride, a wrong allocation and a wrong `memcpy` length, silently.
    #[test]
    fn test_classify_size_divergence_is_reported_even_with_no_offsets() {
        let disposition = classify(StructDef {
            id: StructId::new(0),
            name: "SizedButOffsetless".to_string(),
            fields: vec![field("a", Ty::U64, None), field("b", Ty::U8, None)],
            size: Some(9),
            align: Some(1),
            repr: StructRepr::Rust,
        });
        let StructLayoutDisposition::Disagrees {
            ref mismatches,
            ref size,
        } = disposition
        else {
            panic!(
                "a recorded size that contradicts the byte path must be reported whether or not \
                 the offsets survived, got {disposition:?}"
            );
        };
        assert!(
            mismatches.is_empty(),
            "no field offset was recorded, so no FIELD can be reported as moved, got {mismatches:?}"
        );
        let size = size.as_ref().expect("the size divergence is the finding");
        assert_eq!(size.producer_size, Some(9));
        assert_eq!(size.recomputed_size, 16, "natural-C pads the struct to 16");
        assert_eq!(size.producer_align, Some(1));
        assert_eq!(size.recomputed_align, 8);
        assert!(disposition.is_refusal());
    }

    /// The other half of N5: when the size/align AGREE and there are still no
    /// offsets, the answer is `LayoutAbsent` — NOT `Agrees`. The offsets went
    /// unchecked, and certifying them would be a fresh false certification.
    #[test]
    fn test_classify_agreeing_size_with_no_offsets_is_absent_not_agrees() {
        let disposition = classify(StructDef {
            id: StructId::new(0),
            name: "SizedOffsetless".to_string(),
            fields: vec![field("a", Ty::U64, None), field("b", Ty::U8, None)],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        assert_eq!(
            disposition,
            StructLayoutDisposition::LayoutAbsent,
            "agreeing on the TOTAL says nothing about where the fields sit"
        );
        assert!(!disposition.is_refusal());
    }

    /// `LayoutAbsent` still means "nothing to compare at all": no offsets, no
    /// size, no align. This is the 1,039/5,197 corpus class and its handling is
    /// unchanged — including that an unconvertible field type is NOT translated
    /// (and so not reported) when there is nothing to compare it against.
    #[test]
    fn test_layout_absent_still_means_nothing_to_compare_at_all() {
        assert_eq!(
            classify(struct_def(
                "GenericUnconvertible",
                vec![
                    field("t", Ty::U64, None),
                    field("rc", Ty::Rc(Box::new(Ty::U64)), None),
                ],
            )),
            StructLayoutDisposition::LayoutAbsent
        );
    }

    /// An offset-less struct whose ALIGN alone contradicts must refuse too.
    #[test]
    fn test_classify_align_only_divergence_with_no_offsets_is_reported() {
        let disposition = classify(StructDef {
            id: StructId::new(0),
            name: "OverAlignedOffsetless".to_string(),
            fields: vec![field("a", Ty::U32, None)],
            size: Some(4),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        let size = disposition
            .size_mismatch()
            .expect("an align-only divergence must still be reported");
        assert!(!size.size_differs());
        assert!(size.align_differs());
        assert_eq!(size.recomputed_align, 4);
        assert!(disposition.is_refusal());
    }

    /// A tuple nested one struct deep is the same gap: the scan follows the
    /// `Struct` / `Array` / `Tuple` / `Enum` spine.
    #[test]
    fn test_classify_tuple_nested_inside_an_inner_struct_is_not_comparable() {
        let mut module = Module::new("nested_tuple");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Inner".to_string(),
            fields: vec![field("t", Ty::Tuple(vec![Ty::U8, Ty::U64]), Some(0))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Outer".to_string(),
            fields: vec![
                field("inner", Ty::Struct(StructId::new(0)), Some(0)),
                field("tail", Ty::U64, Some(16)),
            ],
            size: Some(24),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        let disposition = classify_struct_layout(&module.structs[1], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!("a tuple one struct deep is still a gap, got {disposition:?}");
        };
        assert!(
            reason.contains("inner") && reason.contains('t'),
            "the reason must name the path to the tuple, got {reason:?}"
        );
    }

    /// The predicate must see through a nested struct field, because the byte
    /// path does: `Type::offset_of` sizes an inner struct by its own natural-C
    /// layout. Producer offset 4 for a field that follows an 8-byte inner
    /// aggregate is a disagreement.
    #[test]
    fn test_classify_nested_struct_field_uses_the_byte_paths_layout() {
        let mut module = Module::new("nested");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Inner".to_string(),
            fields: vec![field("a", Ty::U32, Some(0)), field("b", Ty::U32, Some(4))],
            size: Some(8),
            align: Some(4),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Outer".to_string(),
            fields: vec![
                field("inner", Ty::Struct(StructId::new(0)), Some(0)),
                field("tail", Ty::U32, Some(4)),
            ],
            size: Some(12),
            align: Some(4),
            repr: StructRepr::Rust,
        });

        let outer = &module.structs[1];
        let disposition = classify_struct_layout(outer, &module);
        let StructLayoutDisposition::Disagrees { ref mismatches, .. } = disposition else {
            panic!("expected Disagrees for the nested case, got {disposition:?}");
        };
        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].field_name, "tail");
        assert_eq!(mismatches[0].producer_offset, 4);
        assert_eq!(
            mismatches[0].recomputed_offset, 8,
            "the inner struct occupies 8 bytes on the byte path"
        );
        assert!(mismatches[0].load_bearing);

        // ACCEPT CONTROL for the same nesting: offset 8 agrees.
        let mut fixed = module.structs[1].clone();
        fixed.fields[1].offset = Some(8);
        let mut fixed_module = module.clone();
        fixed_module.structs[1] = fixed;
        assert_eq!(
            classify_struct_layout(&fixed_module.structs[1], &fixed_module),
            StructLayoutDisposition::Agrees
        );
    }
    // ---------------------------------------------------------------
    // R1 — `Ty::Refine` is an edge the interior scan must FOLLOW.
    //
    // `Refine(base, p)` is representation-preserving by construction
    // (`trust-ir/src/ty.rs:183-190`) and the adapter erases it, lowering the
    // base carrier verbatim (`adapter.rs:1512-1522`). The scan's `_ => None`
    // arm did not follow it, so a refinement wrapped around a multi-element
    // tuple presented the byte path with exactly the synthesized natural-C
    // aggregate a bare tuple presents — and the row was certified `Agrees`.
    // ---------------------------------------------------------------

    /// A module holding `Refined { r: Refine(<base>), after: u64 }`, with the
    /// producer offsets natural-C computes so nothing else can catch it.
    fn module_with_refined_field(base: Ty, after_offset: u64) -> Module {
        let mut module = Module::new("refine_interior");
        let base_id = module.add_type(base);
        let pred = module
            .intern_pred(Pred::Top)
            .expect("`Pred::Top` is always internable");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Refined".to_string(),
            fields: vec![
                field("r", Ty::Refine(base_id, pred), Some(0)),
                field("after", Ty::U64, Some(after_offset)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        module
    }

    /// The falsifier: a `Ty::Tuple(u8, u64)` hidden behind a refinement is the
    /// SAME interior gap as a bare one, and must be reported as one.
    #[test]
    fn test_classify_tuple_hidden_behind_a_refinement_is_not_comparable() {
        let module = module_with_refined_field(Ty::Tuple(vec![Ty::U8, Ty::U64]), 16);
        let disposition = classify_struct_layout(&module.structs[0], &module);
        let StructLayoutDisposition::NotComparable { kind, ref reason } = disposition else {
            panic!(
                "a refinement erases to its base carrier, so it cannot hide the base's interior \
                 gap, got {disposition:?}"
            );
        };
        assert_eq!(kind, NotComparableKind::UnstatedInterior);
        assert!(
            reason.to_lowercase().contains("tuple") && reason.contains("`r`"),
            "the reason must name the field and the tuple behind the refinement, got {reason:?}"
        );
    }

    /// The gap is followed through a refinement over a *struct* too, so the
    /// fix is not a one-arm special case.
    #[test]
    fn test_classify_refinement_over_a_struct_still_reaches_the_interior() {
        let mut module = Module::new("refine_over_struct");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Inner".to_string(),
            fields: vec![field("t", Ty::Tuple(vec![Ty::U8, Ty::U64]), Some(0))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        let base_id = module.add_type(Ty::Struct(StructId::new(0)));
        let pred = module.intern_pred(Pred::Top).expect("Top interns");
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Outer".to_string(),
            fields: vec![
                field("inner", Ty::Refine(base_id, pred), Some(0)),
                field("tail", Ty::U64, Some(16)),
            ],
            size: Some(24),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        let disposition = classify_struct_layout(&module.structs[1], &module);
        let StructLayoutDisposition::NotComparable { ref reason, .. } = disposition else {
            panic!(
                "a refinement over a struct with a tuple interior is a gap, got {disposition:?}"
            );
        };
        assert!(
            reason.contains("`inner`") && reason.contains("`t`"),
            "the reason must name the path THROUGH the refinement, got {reason:?}"
        );
    }

    /// ACCEPT CONTROL for R1: a refinement over a base with NO interior gap
    /// must still be compared. Following the edge must not turn every
    /// refinement into a non-answer.
    #[test]
    fn test_classify_refinement_over_a_plain_scalar_is_still_compared() {
        let module = module_with_refined_field(Ty::U64, 8);
        assert_eq!(
            classify_struct_layout(&module.structs[0], &module),
            StructLayoutDisposition::Agrees,
            "a refined `u64` is a `u64`; there is no interior to be unstated"
        );
    }

    // ---------------------------------------------------------------
    // R2 — a nested `#[repr(packed)]` struct is an INTERIOR trust-cg lays out
    // two ways. `recompute_layout` gates the struct's OWN repr; nothing gated
    // a packed struct reached as a field type.
    // ---------------------------------------------------------------

    /// `Container { p: P, x: u64 }` where `P` is `#[repr(packed)] { a: u8, b:
    /// u64 }`. The container's own offsets and size are exactly what natural-C
    /// computes, so every other gate passes it — and the old predicate
    /// certified `Agrees` while the byte path writes `p.b` at offset 1
    /// (authority P) or offset 8 (authority C) depending on which lane emits.
    #[test]
    fn test_classify_container_of_a_packed_struct_is_not_comparable() {
        let mut module = Module::new("packed_interior");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "P".to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
            size: Some(9),
            align: Some(1),
            repr: StructRepr::Packed(1),
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Container".to_string(),
            fields: vec![
                field("p", Ty::Struct(StructId::new(0)), Some(0)),
                field("x", Ty::U64, Some(16)),
            ],
            size: Some(24),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        let disposition = classify_struct_layout(&module.structs[1], &module);
        let StructLayoutDisposition::NotComparable { kind, ref reason } = disposition else {
            panic!(
                "a packed INTERIOR has no single authority either, got {disposition:?} — the \
                 container's own offsets agreeing says nothing about where `p`'s fields sit"
            );
        };
        assert_eq!(kind, NotComparableKind::UnstatedInterior);
        assert!(
            reason.contains("`p`") && reason.contains("packed") && reason.contains("`P`"),
            "the reason must name the field, the repr and the packed struct, got {reason:?}"
        );
        assert!(
            !disposition.is_refusal(),
            "same disposition class as the packed struct's own row: a named non-answer"
        );
    }

    /// ACCEPT CONTROL for R2: the gate must key on the INTERIOR's `repr`, not
    /// on nesting. The same container over a `repr(C)` inner is still measured
    /// — and still agrees.
    #[test]
    fn test_classify_container_of_a_non_packed_struct_is_unaffected() {
        let mut module = Module::new("c_interior");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "P".to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(8))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "Container".to_string(),
            fields: vec![
                field("p", Ty::Struct(StructId::new(0)), Some(0)),
                field("x", Ty::U64, Some(16)),
            ],
            size: Some(24),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        assert_eq!(
            classify_struct_layout(&module.structs[1], &module),
            StructLayoutDisposition::Agrees
        );
    }

    // ---------------------------------------------------------------
    // R3 — `is_refusal`'s old justification ("an unconvertible struct is
    // already rejected by the adapter's own type translation") is FALSE for
    // three of the four `NotComparable` kinds. This pins the falsification
    // itself, by running the byte path's own conversion over each fixture.
    // ---------------------------------------------------------------

    /// Translate `Ty::Struct(id)` through the SAME conversion the byte path
    /// uses — the one the old doc claimed would reject these rows.
    fn adapter_translates(module: &Module, id: StructId) -> bool {
        translate_field_type(&Ty::Struct(id), module).is_ok()
    }

    /// Same conversion, for a bare field type rather than a struct id.
    fn adapter_translates_field(module: &Module, ty: &Ty) -> bool {
        translate_field_type(ty, module).is_ok()
    }

    #[test]
    fn test_two_of_the_four_not_comparable_kinds_are_not_rejected_by_the_adapter() {
        // (1) AdapterRejected — the ONLY kind the old sentence describes.
        let rejected = module_with(struct_def(
            "Shared",
            vec![field("inner", Ty::Rc(Box::new(Ty::U64)), Some(0))],
        ));
        assert_eq!(
            classify_struct_layout(&rejected.structs[0], &rejected).not_comparable_kind(),
            Some(NotComparableKind::AdapterRejected)
        );
        assert!(
            !adapter_translates(&rejected, StructId::new(0)),
            "this kind IS blocked independently; without that the control is meaningless"
        );

        // (2) Unrepresentable — NOW BLOCKED, and reached only by the one shape
        //     the per-type gate cannot see from a field: each field fits the
        //     u32 carrier on its own, and their SUM does not. 3e9 + 3e9 = 6e9.
        let mut overflow = Module::new("overflow");
        let elem = overflow.add_type(Ty::U8);
        overflow.add_struct(StructDef {
            id: StructId::new(0),
            name: "Huge".to_string(),
            fields: vec![
                field("lo", Ty::Array(elem, 3_000_000_000), Some(0)),
                field("hi", Ty::Array(elem, 3_000_000_000), Some(3_000_000_000)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        assert!(
            adapter_translates_field(&overflow, &Ty::Array(elem, 3_000_000_000)),
            "each field alone must still convert; otherwise this fixture is testing kind (1)"
        );
        assert_eq!(
            classify_struct_layout(&overflow.structs[0], &overflow).not_comparable_kind(),
            Some(NotComparableKind::Unrepresentable)
        );
        assert!(
            !adapter_translates(&overflow, StructId::new(0)),
            "the adapter now REFUSES an unrepresentable layout — this used to be live              exposure, emitting a wrapped extent"
        );

        // (3) PackedNoSingleAuthority — converts, and both authorities emit.
        let packed = module_with(packed_struct(
            "Packed1",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
        ));
        assert_eq!(
            classify_struct_layout(&packed.structs[0], &packed).not_comparable_kind(),
            Some(NotComparableKind::PackedNoSingleAuthority)
        );
        assert!(
            adapter_translates(&packed, StructId::new(0)),
            "the adapter does NOT reject a packed struct; it lays it out two ways"
        );

        // (4) UnstatedInterior — converts, and LIR synthesizes the interior.
        let tuple = module_with(struct_def(
            "HasTuple",
            vec![
                field("t", Ty::Tuple(vec![Ty::U8, Ty::U64]), Some(0)),
                field("after", Ty::U64, Some(16)),
            ],
        ));
        assert_eq!(
            classify_struct_layout(&tuple.structs[0], &tuple).not_comparable_kind(),
            Some(NotComparableKind::UnstatedInterior)
        );
        assert!(
            adapter_translates(&tuple, StructId::new(0)),
            "the adapter does NOT reject a tuple interior; it synthesizes a natural-C aggregate"
        );

        // The claim the corrected doc makes, stated as an assertion — in BOTH
        // directions, so a kind cannot silently migrate between the groups.
        for kind in [
            NotComparableKind::PackedNoSingleAuthority,
            NotComparableKind::UnstatedInterior,
        ] {
            assert!(
                kind.is_live_exposure() && !kind.is_rejected_by_the_adapter(),
                "{kind:?} is emitted with nothing blocking it"
            );
        }
        for kind in [
            NotComparableKind::AdapterRejected,
            NotComparableKind::Unrepresentable,
        ] {
            assert!(
                kind.is_rejected_by_the_adapter() && !kind.is_live_exposure(),
                "{kind:?} is blocked before emission, so declining to score it costs nothing"
            );
        }
    }

    /// The census must surface the live-exposure population separately, so it
    /// can never again hide inside a single `NotComparable` total.
    #[test]
    fn test_census_separates_live_exposure_from_adapter_rejected_rows() {
        let mut module = Module::new("exposure");
        module.add_struct(struct_def(
            "Rejected",
            vec![field("inner", Ty::Rc(Box::new(Ty::U64)), Some(0))],
        ));
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "HasTuple".to_string(),
            fields: vec![
                field("t", Ty::Tuple(vec![Ty::U8, Ty::U64]), Some(0)),
                field("after", Ty::U64, Some(16)),
            ],
            size: None,
            align: None,
            repr: StructRepr::Rust,
        });
        module.add_struct(StructDef {
            id: StructId::new(2),
            name: "Packed".to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
            size: None,
            align: None,
            repr: StructRepr::Packed(1),
        });

        let census = census_module_struct_layouts(&module);
        assert_eq!(census.not_comparable(), 3);
        assert_eq!(
            census.not_comparable_of_kind(NotComparableKind::AdapterRejected),
            1
        );
        assert_eq!(
            census.not_comparable_of_kind(NotComparableKind::UnstatedInterior),
            1
        );
        assert_eq!(
            census.not_comparable_of_kind(NotComparableKind::PackedNoSingleAuthority),
            1
        );
        assert_eq!(
            census.unrefused_exposures(),
            2,
            "the tuple and the packed row are emitted with nothing blocking them; only the \
             adapter-rejected row is covered by the old justification"
        );
        assert!(
            !census.refuses(),
            "none of the three refuses — which is exactly why the exposure count must be visible"
        );
    }

    // ---------------------------------------------------------------
    // R4 — the interior scan's depth bound must FAIL CLOSED, and its
    // unreachability must be a CHECKED coupling rather than a prose argument
    // about two constants that happen to be equal.
    // ---------------------------------------------------------------

    /// Reaching the bound means the scan has looked at nothing. Returning
    /// "no interior gap" there is the one answer that lets step 7 certify.
    #[test]
    fn test_the_interior_scan_bound_fails_closed() {
        let module = module_with(struct_def("Any", vec![]));
        let gap = interior_layout_gap(
            &Ty::Tuple(vec![Ty::U8, Ty::U64]),
            "field `t`",
            &module,
            MAX_INTERIOR_SCAN_DEPTH,
        );
        let gap = gap.expect(
            "depth exhaustion must REPORT a gap: the scan established nothing, and `None` is \
             the answer that certifies `Agrees`",
        );
        assert!(
            gap.contains("bound") && gap.contains("field `t`"),
            "the reason must say the scan gave up and where, got {gap:?}"
        );
    }

    /// The unreachability argument for that bound is "every edge the scan
    /// follows, the translation follows first, with the same increment". It
    /// holds only while the two bounds are EQUAL. Pin it: raising the
    /// adapter's limit alone would silently make the scan authoritative for
    /// depths the adapter still accepts, and this is the test that says so.
    #[test]
    fn test_the_interior_scan_bound_is_the_adapter_translation_bound() {
        assert_eq!(
            MAX_INTERIOR_SCAN_DEPTH,
            crate::adapter::MAX_TYPE_TRANSLATION_DEPTH,
            "the interior scan is only unreachable-at-its-bound because step 3a's translation \
             bound fires first; if these diverge, re-prove the scan's termination before \
             changing either"
        );
    }

    // ---------------------------------------------------------------
    // R5 — "not load-bearing" must not read as "harmless". D1/N5 put SIZE and
    // ALIGN divergences into `Disagrees` without any field moving, and
    // `is_load_bearing_disagreement` counts FIELDS, so those rows landed in a
    // bucket whose name says they are the mild ones. They are the opposite.
    // ---------------------------------------------------------------

    /// A wrong total size is a wrong array stride, a wrong allocation and a
    /// wrong `memcpy` length. No field moved, so the FIELD figure is 0 — and
    /// `moves_bytes` must still be true.
    #[test]
    fn test_a_size_only_disagreement_moves_bytes_even_though_no_field_moves() {
        let disposition = classify(sized_struct(
            "TrailPad",
            vec![field("a", Ty::U64, Some(0)), field("b", Ty::U8, Some(8))],
            9,
            1,
        ));
        assert!(
            !disposition.is_load_bearing_disagreement(),
            "no FIELD moved: the field-offset figure must stay comparable"
        );
        assert!(
            disposition.moves_bytes(),
            "a 9-vs-16 total relocates every array element past the first and mints a wrong \
             memcpy length; reading this row as harmless is the defect"
        );
    }

    /// The same for an ALIGN-only divergence: a wrong alignment is a wrong
    /// placement inside every containing aggregate.
    #[test]
    fn test_an_align_only_disagreement_moves_bytes() {
        let disposition = classify(sized_struct(
            "OverAligned",
            vec![field("a", Ty::U32, Some(0))],
            4,
            8,
        ));
        assert!(!disposition.is_load_bearing_disagreement());
        assert!(disposition.moves_bytes());
    }

    /// ACCEPT CONTROL for R5, and the reason `moves_bytes` is not just
    /// `is_refusal`: a disagreement that only relocates a ZERO-SIZED field
    /// really is address-preserving, and must be the one kind that answers
    /// `false`. Without this the new accessor could be `true` everywhere.
    #[test]
    fn test_a_zst_only_disagreement_does_not_move_bytes() {
        let disposition = classify(struct_def(
            "WithMarker",
            vec![
                field("value", Ty::U64, Some(0)),
                field("marker", Ty::Tuple(vec![]), Some(0)),
            ],
        ));
        assert!(
            disposition.is_refusal(),
            "it is still a producer/consumer disagreement",
        );
        assert!(
            !disposition.moves_bytes(),
            "no byte that is ever loaded or stored changes address"
        );
    }

    /// The census must be able to report the severity headline directly.
    #[test]
    fn test_census_counts_byte_moving_disagreements_across_both_kinds() {
        let mut module = Module::new("severity");
        // A moved non-ZST field. The producer parks a `u64` at 4 in a
        // non-packed struct, which the declared-offset authority declines as
        // incoherent, so the recomputation stands and `b` really is addressed
        // at 8 instead of 4.
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Unaligned".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U64, Some(4))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
        });
        // A size-only divergence: no field moves.
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "TrailPad".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U8, Some(8))],
            size: Some(9),
            align: Some(1),
            repr: StructRepr::Rust,
        });
        // A ZST-only move: address-preserving. The marker's declared offset is
        // off the end of the declared size, so the containment gate declines
        // the layout and the recomputation (marker@8) stands.
        module.add_struct(StructDef {
            id: StructId::new(2),
            name: "WithMarker".to_string(),
            fields: vec![
                field("value", Ty::U64, Some(0)),
                field("marker", Ty::Tuple(vec![]), Some(9)),
            ],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::Rust,
        });

        let census = census_module_struct_layouts(&module);
        assert_eq!(census.disagrees(), 3);
        assert_eq!(
            census.load_bearing_disagreements(),
            1,
            "the FIELD figure sees only `Unaligned`"
        );
        assert_eq!(census.size_disagreements(), 1, "only `TrailPad`");
        assert_eq!(
            census.byte_moving_disagreements(),
            2,
            "`Reordered` and `TrailPad`; reporting 1 here is what let a wrong stride read as \
             one of the mild rows"
        );
    }

    // ---------------------------------------------------------------
    // C1 — the packed gate keyed on `repr` rather than on whether the two
    // authorities actually DISAGREE, and so swallowed load-bearing refusals.
    //
    // `#[repr(packed(N))]` clamps each field's alignment to `min(natural, N)`.
    // When no field's natural alignment exceeds N the clamp is a NO-OP and both
    // authorities compute the IDENTICAL layout — there is a single authority for
    // that struct and the normal comparison must run.
    // ---------------------------------------------------------------

    /// The two authorities agree byte-for-byte, so the struct is compared, and
    /// an agreeing producer is certified. Under the `repr`-keyed gate this was
    /// `NotComparable` while quoting two IDENTICAL authorities.
    #[test]
    fn test_packed_whose_clamp_is_a_noop_has_one_authority_and_is_compared() {
        let disposition = classify(packed_struct(
            "Hdr",
            1,
            vec![
                field("a", Ty::U8, Some(0)),
                field("b", Ty::U8, Some(1)),
                field("c", Ty::U8, Some(2)),
            ],
        ));
        assert_eq!(
            disposition,
            StructLayoutDisposition::Agrees,
            "max natural align is 1, so the packed clamp is a no-op: authority P and authority C \
             compute offsets [0, 1, 2] / size 3 / align 1 alike, and a struct the compiler lays \
             out ONE way is comparable"
        );
    }

    /// The swallowed refusal, same shape with a MOVED field: the producer puts
    /// `c` at 7 and BOTH authorities put it at 2. This is a real
    /// producer/consumer disagreement that the `repr`-keyed gate reported as a
    /// non-refusing census row.
    #[test]
    fn test_packed_whose_clamp_is_a_noop_still_refuses_a_moved_field() {
        let disposition = classify(packed_struct(
            "HdrMoved",
            1,
            vec![
                field("a", Ty::U8, Some(0)),
                field("b", Ty::U8, Some(1)),
                field("c", Ty::U8, Some(7)),
            ],
        ));
        let StructLayoutDisposition::Disagrees { ref mismatches, .. } = disposition else {
            panic!(
                "both authorities put `c` at 2 and the producer says 7; there is nothing \
                 unscoreable here, got {disposition:?}"
            );
        };
        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].field_name, "c");
        assert_eq!(mismatches[0].producer_offset, 7);
        assert_eq!(mismatches[0].recomputed_offset, 2);
        assert!(mismatches[0].load_bearing);
        assert!(
            disposition.is_refusal(),
            "a load-bearing disagreement must REFUSE; reporting it as a census row is the defect"
        );
    }

    /// The size/align half of the same swallow: agreeing offsets, a producer
    /// total both authorities contradict.
    #[test]
    fn test_packed_whose_clamp_is_a_noop_still_refuses_a_wrong_total_size() {
        let mut sdef = packed_struct(
            "HdrSized",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U8, Some(1))],
        );
        sdef.size = Some(8);
        sdef.align = Some(1);
        let disposition = classify(sdef);
        assert!(
            disposition.is_size_disagreement(),
            "both authorities say size 2; a producer claim of 8 is a wrong stride, \
             got {disposition:?}"
        );
        assert!(disposition.is_refusal());
        assert!(disposition.moves_bytes());
    }

    /// A field-less packed struct: both authorities say offsets `[]` / size 0 /
    /// align 1, so it agrees vacuously exactly as a field-less `repr(Rust)`
    /// struct does. Under the `repr`-keyed gate it was `NotComparable` while
    /// having no field that could sit anywhere.
    #[test]
    fn test_fieldless_packed_struct_agrees_vacuously() {
        assert_eq!(
            classify(packed_struct("PackedUnit", 1, vec![])),
            StructLayoutDisposition::Agrees
        );
    }

    /// ACCEPT CONTROL for C1: the gate must still fire when the clamp really
    /// BITES. `{ a: u8, b: u64 }` under `packed(1)` is laid out two ways, and
    /// nothing here may certify or refuse it.
    #[test]
    fn test_packed_whose_clamp_bites_is_still_the_two_authority_non_answer() {
        let disposition = classify(packed_struct(
            "ClampBites",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
        ));
        assert_eq!(
            disposition.not_comparable_kind(),
            Some(NotComparableKind::PackedNoSingleAuthority),
            "authority P says [0, 1] and authority C says [0, 8]: still no single authority, \
             got {disposition:?}"
        );
        assert!(!disposition.is_refusal());
    }

    /// The clamp is also a no-op when `N` is at least every field's natural
    /// alignment — `packed(8)` over `{ u8, u64 }` changes nothing.
    #[test]
    fn test_packed_with_a_clamp_above_every_field_alignment_is_compared() {
        assert_eq!(
            classify(packed_struct(
                "PackedButWide",
                8,
                vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(8))],
            )),
            StructLayoutDisposition::Agrees,
            "packed(8) clamps nothing on a struct whose widest field is 8-aligned"
        );
    }

    /// ACCEPT CONTROL for the `packed == natural` equality itself, and the one
    /// that binds its **size/align** components rather than only its offsets.
    ///
    /// `#[repr(packed(4))] { a: u64, b: u32 }` is the shape where the two
    /// authorities land on the SAME offsets and different totals: P clamps both
    /// fields to 4, so `a@0`, `b@8`, struct align 4, size 12; C keeps `u64`
    /// 8-aligned, so `a@0`, `b@8`, struct align 8, size 16. The offsets
    /// COINCIDE at `[0, 8]` and the struct is still laid out two ways.
    ///
    /// Weakening the gate to `packed.offsets == natural.offsets` therefore
    /// certifies a struct with two emitted sizes — a wrong array stride and a
    /// wrong `memcpy` length behind an `Agrees` — and, in the other direction,
    /// reports a producer stating authority C's totals as a `Disagrees` scored
    /// against authority P. (c) MEASURED: with that weakening the whole
    /// pre-existing suite stayed green, so this control is what stops the
    /// equality from silently degrading to its offsets half.
    #[test]
    fn test_packed_authorities_agreeing_only_on_offsets_are_still_two_authorities() {
        let claim = |size: u64, align: u64| {
            let mut sdef = packed_struct(
                "StrideSplit",
                4,
                vec![field("a", Ty::U64, Some(0)), field("b", Ty::U32, Some(8))],
            );
            sdef.size = Some(size);
            sdef.align = Some(align);
            classify(sdef)
        };

        let claiming_p = claim(12, 4);
        assert_eq!(
            claiming_p.not_comparable_kind(),
            Some(NotComparableKind::PackedNoSingleAuthority),
            "both authorities put `b` at 8, but P totals 12/4 and C totals 16/8: certifying \
             `Agrees` here certifies a struct with two emitted SIZES, got {claiming_p:?}"
        );
        assert!(!claiming_p.is_refusal());

        let claiming_c = claim(16, 8);
        assert_eq!(
            claiming_c.not_comparable_kind(),
            Some(NotComparableKind::PackedNoSingleAuthority),
            "the mirror direction: scoring authority C's totals against authority P's would \
             refuse a producer that matches an authority the byte path really uses, \
             got {claiming_c:?}"
        );
        assert!(!claiming_c.is_refusal());
    }

    // ---------------------------------------------------------------
    // C2 — a packed struct agreeing with NEITHER authority is still not
    // refused. "Disagrees with every authority" is a TOTAL statement: it needs
    // no choice of which authority is "the" emitted layout, because it holds
    // against both. So it can be refused honestly.
    // ---------------------------------------------------------------

    /// `#[repr(packed(1))] { a: u8 @0, b: u64 @3 }`, size 999, align 64.
    /// Authority P says `[0, 1]` / 9 / 1; authority C says `[0, 8]` / 16 / 8.
    /// The producer matches neither, on offsets AND size AND align.
    #[test]
    fn test_packed_matching_neither_authority_is_refused() {
        let mut sdef = packed_struct(
            "Nonsense",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(3))],
        );
        sdef.size = Some(999);
        sdef.align = Some(64);
        let disposition = classify(sdef);
        let StructLayoutDisposition::PackedMatchesNeitherAuthority {
            ref packed,
            ref natural,
            ref reason,
        } = disposition
        else {
            panic!(
                "a producer layout that matches NEITHER authority needs no authority choice and \
                 must refuse, got {disposition:?}"
            );
        };
        assert_eq!(packed.offsets, vec![0, 1]);
        assert_eq!(packed.size, 9);
        assert_eq!(packed.align, 1);
        assert_eq!(natural.offsets, vec![0, 8]);
        assert_eq!(natural.size, 16);
        assert_eq!(natural.align, 8);
        assert!(
            reason.contains("packed_field_offset") && reason.contains("translate_alloc"),
            "the refusal must still NAME both authorities, and authority C by a site that is \
             still natural-C after the aggregate-constant repair, got {reason:?}"
        );
        assert!(
            disposition.is_refusal(),
            "whichever authority the byte path reaches, the producer's addresses are wrong"
        );
        assert!(
            disposition.mismatches().is_empty() && !disposition.is_size_disagreement(),
            "this is not a `Disagrees`: there is no single recomputed offset to name, so it must \
             not pollute the field/size disagreement figures"
        );
    }

    /// Matching neither on the OFFSETS alone is enough — the producer need not
    /// also contradict the totals.
    #[test]
    fn test_packed_matching_neither_authority_on_offsets_alone_is_refused() {
        let disposition = classify(packed_struct(
            "OffsetsOnly",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(4))],
        ));
        assert!(
            matches!(
                disposition,
                StructLayoutDisposition::PackedMatchesNeitherAuthority { .. }
            ),
            "authority P says `b` at 1, authority C says 8, the producer says 4: no choice of \
             authority makes 4 right, got {disposition:?}"
        );
        assert!(disposition.is_refusal());
    }

    /// The TOTALS are half of the "matches neither" test and must bind on their
    /// own. Offsets `[0, 1]` match authority P exactly, so an offsets-only
    /// comparison calls this a non-answer — but the producer's total
    /// contradicts P as well, and its offsets contradict C, so no authority
    /// makes the claim right and it must refuse.
    ///
    /// Mutation-pinned: dropping the `size`/`align` conjuncts from
    /// `producer_matches` leaves the rest of this suite entirely green.
    #[test]
    fn test_packed_matching_neither_authority_on_the_totals_alone_is_refused() {
        for (name, size, align) in [
            ("WrongSizeOnly", Some(999), None),
            ("WrongAlignOnly", None, Some(64)),
        ] {
            let mut sdef = packed_struct(
                name,
                1,
                vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
            );
            sdef.size = size;
            sdef.align = align;
            let disposition = classify(sdef);
            assert!(
                matches!(
                    disposition,
                    StructLayoutDisposition::PackedMatchesNeitherAuthority { .. }
                ),
                "{name}: the offsets match authority P but the total does not, and authority C \
                 matches nothing at all — a wrong stride is not rescued by agreeing offsets, \
                 got {disposition:?}"
            );
            assert!(disposition.is_refusal(), "{name}");
        }
    }

    /// A component the producer left `None` is not evidence AGAINST it: the
    /// layout query declined, so there is no claim to contradict. A packed
    /// struct with no offsets at all and a size that matches authority P is
    /// still the honest non-answer — and the same struct with a size that
    /// matches neither is still a refusal. Both directions, so the rule cannot
    /// be inverted into "an absent offset disagrees with everything".
    #[test]
    fn test_a_component_the_producer_left_absent_is_not_evidence_against_it() {
        let unstated = |size: u64| {
            let mut sdef = packed_struct(
                "OffsetlessPacked",
                1,
                vec![field("a", Ty::U8, None), field("b", Ty::U64, None)],
            );
            sdef.size = Some(size);
            classify(sdef)
        };

        let matching = unstated(9);
        assert_eq!(
            matching.not_comparable_kind(),
            Some(NotComparableKind::PackedNoSingleAuthority),
            "the producer stated only a size, and it is authority P's: refusing here would treat \
             two absent offsets as a contradiction, got {matching:?}"
        );
        assert!(!matching.is_refusal());

        let contradicting = unstated(999);
        assert!(
            matches!(
                contradicting,
                StructLayoutDisposition::PackedMatchesNeitherAuthority { .. }
            ),
            "P says 9 and C says 16: a stated 999 contradicts both, got {contradicting:?}"
        );
        assert!(contradicting.is_refusal());
    }

    /// ACCEPT CONTROL for the conjunct just added: a producer that states the
    /// totals and gets them RIGHT for one authority is back to the honest
    /// non-answer. Without this the `size`/`align` terms could be inverted.
    #[test]
    fn test_packed_stating_one_authoritys_totals_is_still_not_comparable() {
        let mut sdef = packed_struct(
            "MatchesPCompletely",
            1,
            vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
        );
        sdef.size = Some(9);
        sdef.align = Some(1);
        let disposition = classify(sdef);
        assert_eq!(
            disposition.not_comparable_kind(),
            Some(NotComparableKind::PackedNoSingleAuthority),
            "offsets, size AND align all match authority P; refusing this would mean declaring \
             authority C the winner, got {disposition:?}"
        );
        assert!(!disposition.is_refusal());
    }

    /// ACCEPT CONTROL for C2, both directions: a producer that matches EXACTLY
    /// ONE authority is the case where scoring really would be right only by
    /// accident, and it must stay a non-refusing census row.
    #[test]
    fn test_packed_matching_exactly_one_authority_is_still_not_comparable() {
        for (name, offsets) in [("MatchesP", [0u64, 1u64]), ("MatchesC", [0, 8])] {
            let disposition = classify(packed_struct(
                name,
                1,
                vec![
                    field("a", Ty::U8, Some(offsets[0])),
                    field("b", Ty::U64, Some(offsets[1])),
                ],
            ));
            assert_eq!(
                disposition.not_comparable_kind(),
                Some(NotComparableKind::PackedNoSingleAuthority),
                "{name}: the producer matches one of two disagreeing authorities; picking a \
                 winner is exactly what this predicate must not do, got {disposition:?}"
            );
            assert!(!disposition.is_refusal(), "{name}");
        }
    }

    /// The census counts the new refusing row on its own, and refuses.
    #[test]
    fn test_census_counts_a_packed_row_that_matches_neither_authority() {
        let mut module = Module::new("packed_neither");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "MatchesP".to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(1))],
            size: None,
            align: None,
            repr: StructRepr::Packed(1),
        });
        module.add_struct(StructDef {
            id: StructId::new(1),
            name: "MatchesNeither".to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(4))],
            size: None,
            align: None,
            repr: StructRepr::Packed(1),
        });
        let census = census_module_struct_layouts(&module);
        assert_eq!(census.packed_matches_neither_authority(), 1);
        assert_eq!(
            census.not_comparable_of_kind(NotComparableKind::PackedNoSingleAuthority),
            1,
            "only the row that matches one authority is the honest non-answer"
        );
        assert_eq!(
            census.disagrees(),
            0,
            "neither row is a scored disagreement"
        );
        let refused: Vec<&str> = census.refusals().map(|r| r.name.as_str()).collect();
        assert_eq!(refused, vec!["MatchesNeither"]);
    }

    // ---------------------------------------------------------------
    // C3 — the collision gate's equality was STRUCTURAL, not LAYOUT.
    //
    // `StructDef: PartialEq` includes `name`, every `FieldDef::name` and the
    // producer `size`/`align`. None of those decides what layout the byte path
    // emits: it resolves `Ty::Struct(sid)` by first match and builds
    // `Type::Struct([translate(f.ty) ...])`, choosing the authority on `repr`.
    // So two defs sharing an id with the same field TYPES and the same `repr`
    // shadow each other with a BYTE-IDENTICAL layout, and refusing them is a
    // false refusal — the step-0 rationale says so in as many words.
    // ---------------------------------------------------------------

    /// Two defs sharing an id whose field TYPES and `repr` agree, differing in
    /// everything the emitted layout does not read.
    fn module_with_shadowing_twins(
        first: (&str, &str, Option<u64>, Option<u64>),
        second: (&str, &str, Option<u64>, Option<u64>),
    ) -> Module {
        let mut module = Module::new("shadow");
        for (name, field_name, size, align) in [first, second] {
            module.add_struct(StructDef {
                id: StructId::new(0),
                name: name.to_string(),
                fields: vec![field(field_name, Ty::U64, Some(0))],
                size,
                align,
                repr: StructRepr::C,
            });
        }
        module
    }

    /// Only the STRUCT NAME differs. Every `Meters` value is addressed with
    /// `Feet`'s layout, which is byte-identical to its own: nothing is
    /// misaddressed.
    #[test]
    fn test_same_id_differing_only_in_struct_name_is_not_a_collision() {
        let module = module_with_shadowing_twins(
            ("Feet", "v", Some(8), Some(8)),
            ("Meters", "v", Some(8), Some(8)),
        );
        assert_eq!(
            classify_struct_layout(&module.structs[1], &module),
            StructLayoutDisposition::Agrees,
            "a struct NAME is not layout: the shadowed def is addressed with a byte-identical \
             layout, so the step-0 rationale's \"shadow each other harmlessly\" applies verbatim"
        );
    }

    /// Only a FIELD NAME differs. Same type, same offset, same everything the
    /// byte path reads.
    #[test]
    fn test_same_id_differing_only_in_a_field_name_is_not_a_collision() {
        let module = module_with_shadowing_twins(
            ("T", "lhs", Some(8), Some(8)),
            ("T", "rhs", Some(8), Some(8)),
        );
        assert_eq!(
            classify_struct_layout(&module.structs[1], &module),
            StructLayoutDisposition::Agrees,
            "a FIELD name is not layout either"
        );
    }

    /// Only the producer `size`/`align` differ. Those are the CLAIM being
    /// scored, not the emitted layout — so the shadowed def must be measured,
    /// and its wrong claim reported as the size disagreement it is.
    #[test]
    fn test_same_id_differing_only_in_producer_size_is_scored_not_called_a_collision() {
        let module = module_with_shadowing_twins(
            ("S", "v", Some(8), Some(8)),
            ("S", "v", Some(64), Some(8)),
        );
        let disposition = classify_struct_layout(&module.structs[1], &module);
        assert!(
            disposition.is_size_disagreement(),
            "the emitted layout is 8/8 for BOTH defs; the shadowed def's claim of 64 is a size \
             disagreement, attributed to the right thing, got {disposition:?}"
        );
        assert!(disposition.is_refusal());
    }

    /// Only the producer OFFSETS differ: same field types, so the same layout
    /// is emitted for both — and the shadowed def's offsets are scoreable
    /// against it. A `Disagrees` naming the field, not a collision.
    #[test]
    fn test_same_id_differing_only_in_producer_offsets_is_a_disagreement() {
        let mut module = Module::new("shadow_offsets");
        for offsets in [[0u64, 8u64], [0, 1]] {
            module.add_struct(StructDef {
                id: StructId::new(0),
                name: "S".to_string(),
                fields: vec![
                    field("a", Ty::U8, Some(offsets[0])),
                    field("b", Ty::U64, Some(offsets[1])),
                ],
                size: Some(16),
                align: Some(8),
                repr: StructRepr::C,
            });
        }
        let disposition = classify_struct_layout(&module.structs[1], &module);
        let StructLayoutDisposition::Disagrees { ref mismatches, .. } = disposition else {
            panic!(
                "both defs emit the same layout, so the shadowed def's offsets ARE scoreable, \
                 got {disposition:?}"
            );
        };
        assert_eq!(mismatches.len(), 1);
        assert_eq!(mismatches[0].field_name, "b");
        assert_eq!(mismatches[0].producer_offset, 1);
        assert_eq!(mismatches[0].recomputed_offset, 8);
    }

    /// ACCEPT CONTROL for C3, part 1: a differing field TYPE really does change
    /// the emitted layout, and must still be a collision.
    #[test]
    fn test_same_id_differing_in_a_field_type_is_still_a_collision() {
        let mut module = Module::new("shadow_ty");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".to_string(),
            fields: vec![field("v", Ty::U8, Some(0))],
            size: Some(1),
            align: Some(1),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".to_string(),
            fields: vec![field("v", Ty::U64, Some(0))],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::C,
        });
        assert!(
            matches!(
                classify_struct_layout(&module.structs[1], &module),
                StructLayoutDisposition::StructIdCollision { .. }
            ),
            "the byte path builds the LIR type from the RESOLVED def's field types: a u64 field \
             is addressed as the shadowing def's u8"
        );
    }

    /// ACCEPT CONTROL for C3, part 2: `repr` selects the layout AUTHORITY, so a
    /// differing `repr` is a differing emitted layout and must still collide.
    #[test]
    fn test_same_id_differing_only_in_repr_is_still_a_collision() {
        let mut module = Module::new("shadow_repr");
        let def = |repr| StructDef {
            id: StructId::new(0),
            name: "S".to_string(),
            fields: vec![field("a", Ty::U8, Some(0)), field("b", Ty::U64, Some(8))],
            size: None,
            align: None,
            repr,
        };
        module.add_struct(def(StructRepr::C));
        module.add_struct(def(StructRepr::Packed(1)));
        assert!(
            matches!(
                classify_struct_layout(&module.structs[1], &module),
                StructLayoutDisposition::StructIdCollision { .. }
            ),
            "`repr` picks between the packed and the natural-C authority, so it is layout"
        );
    }

    /// ACCEPT CONTROL for C3, part 3: a differing field COUNT is a differing
    /// layout.
    #[test]
    fn test_same_id_differing_in_field_count_is_still_a_collision() {
        let mut module = Module::new("shadow_count");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".to_string(),
            fields: vec![field("a", Ty::U64, Some(0))],
            size: Some(8),
            align: Some(8),
            repr: StructRepr::C,
        });
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "S".to_string(),
            fields: vec![field("a", Ty::U64, Some(0)), field("b", Ty::U64, Some(8))],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::C,
        });
        assert!(matches!(
            classify_struct_layout(&module.structs[1], &module),
            StructLayoutDisposition::StructIdCollision { .. }
        ));
    }
}
