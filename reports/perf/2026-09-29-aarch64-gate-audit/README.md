# Audit: every `aarch64` test in the MIR bridge, classified

48 sites in `crates/rustc-codegen-trust-cg/src/lib.rs` match `"aarch64"`. Two of
them accounted for the last three `library/core` roots
(`2026-09-29-core-lowers-completely/`). This is the classification of the rest, so
the remaining ones are worked by class and by evidence rather than one at a time by
guess. **Line numbers are as of trust-cg `65de0d8f2` plus the two fixes in that
report; they drift.**

## Class A — genuinely architecture-specific. Leave alone.

These encode a real property of the target, not a rollout boundary.

| line | what |
| ---: | --- |
| 963 | NEON / `fp-armv8` target features |
| 6960 | `"aarch64" \| "arm64" => Target::Aarch64` — the target enum mapping |
| 10475 | `uses_linux_aapcs64_hfa_scope` — the AAPCS64 HFA rule itself |
| 99734, 99810 | AAPCS64 §6.9 `x8` indirect result register |
| 99962, 10503, 11218 | already admit `x86_64` alongside |
| 60905 | atomic RMW/CAS over a POINTER element. Its doc states the restriction is deliberate and reasoned, not a rollout gate |

## Class B — x86-64 keeps a REFUSAL (fail-closed). Safe direction to widen.

The aarch64 arm adds a capability; x86-64 falls to an `Err` or a `None`. Widening
these can only turn a refusal into a lowering, so the risk is a WRONG lowering, not
a silent regression — which is why each needs its own census plus the 18-program
differential, one at a time.

| line | capability withheld from x86-64 | note |
| ---: | --- | --- |
| 4436 | thread-local static with alignment > 8 | |
| 9807 | `scalar_cell_storage` fallback for a pointer-like type | sibling of the referent-cell work already landed |
| 13180 | one-capture closure keeps its canonical environment slot | |
| 25208, 33577, 37370 | slice/str element access through a non-memory-backed fat local | three sites, one shape |
| 25641 | `Rvalue::RawPtr` over `[Deref, Index]` — the folded reference-to-pointer cast | |
| 29344, 38106 | `scalarized_slice_reborrow_source_data_len` — the data/length pair for a reborrow | 29344's else-branch is a hard `Err` |
| 29484, 29516 | `slice_element_address` instead of the restricted index fallback | |
| 30071 | whole-value same-type aggregate copy | |
| 32396 | `Rvalue::Ref` over `[Deref]` with a thin pointee | a sibling arm for this shape is already ungated; this one is narrower |
| 33240 | `retype_plain_address_to_local` | |
| 51763, 53206, 53340 | unwind CLEANUP edges (`Assert`, indirect call, virtual call) with EH active | this is the ELF-EH blocker; three sites, one feature |
| 56750 | `#[track_caller]` VIRTUAL call boundary | |
| 97197 | Box/Rc/Arc two-word payload image | |
| 102441 | zero-sized argument tuple of a generic `Fn*` call | |
| 113751 | thin-pointer LEAF in a memory projection | |

## Class C — ⚠ TWO THIRDS OF THIS CLASS WAS MISCLASSIFIED. Read the correction below.

### Correction, after reading each fall-through instead of the gate's shape

**`32684` and `32868` are NOT fail-open.** The gate's shape suggested "aarch64 runs a
type-mismatch guard, x86-64 skips it", and that reading was wrong. Each aarch64 block
contains a guard AND a capability — `copy_aggregate_slot_bytes`, a whole-byte-image
copy — and the guard is there because copying raw bytes REQUIRES the source and
destination types to be equal. x86-64 does not skip a check; it takes a different and
arguably more careful path: a field-by-field copy that reads each field from its own
rustc layout offset, with a discriminator (`flattened_leaf_layout_offsets`) that asks
the SLOT which of two addressing models it uses, and whose in-source comment documents
several silent miscompiles that design already fixed. There is no hole to close, and
ungating would REPLACE a per-field copy with a byte-image shortcut. Not done.

**`95607` was a real coupling defect, and it was one this campaign created.**
`lower_promoted_scalar_ref_return_call` returns early — declining to promote a snapshot
referent value — and its doc gives the reason: "With real addresses, preserve pointer
identity through the ordinary call and return path. In particular, an address-taken
result reference must store the returned pointer in its cell, not a selected pointee
value." That early return was gated to aarch64 Linux, because aarch64 Linux was the only
target with the real-address (referent-cell) model. **Earlier the same day this campaign
extended celling to x86-64 Linux and left this gate alone**, so x86-64 had real
addresses AND the promotion — the one combination the doc rules out.

Fixed by factoring the target condition into a single predicate,
`uses_real_address_reference_model`, now the sole authority for both the cell pre-pass
and this early return, including the `no-x86-ref-referent-cell` opt-out, so the pair
stays coherent in both knob positions rather than only the default one.

**Measured effect: none, anywhere.** All 1284 shared `library/core` objects are
BYTE-IDENTICAL before and after, as are all 18 runtime programs. So the promotion was
never firing on x86-64 in this corpus, and the inconsistency was latent rather than
active. **That also means the fix is UNTESTED by anything in the suite** — it is a
latent-hazard removal and a named invariant, not a verified behaviour change, and it is
recorded as such rather than credited with closing a miscompile.

### The original (partly wrong) reading, kept for the record

Here the aarch64 arm is a GUARD that x86-64 does not run: aarch64 refuses a
mismatch, x86-64 proceeds. A census cannot see these, because the census only
reports what fails to compile — a wrong compile counts as a success. This is the
class that hid a real `Box<dyn>` transmute miscompile earlier in this campaign.

| line | guard aarch64 has and x86-64 does not |
| ---: | --- |
| 32684 | whole-value deref store: refuses when `source_ty != destination_ty` |
| 32868 | scalarized aggregate deref store: refuses on type mismatch |
| 95607 | preserves pointer identity through the call/return path instead of promoting a snapshot referent value |

~~These should be ungated FIRST, ahead of Class B.~~ **Superseded**: of the three,
two were not fail-open at all and the third was a coupling bug with no measurable
effect. The transferable lesson is the method, not the class: **a gate's SHAPE does not
tell you what the other target does.** Two of these three were misread by reasoning
from `if aarch64 { check } else { nothing }` without reading the fall-through, which
turned out to be a longer and better-documented code path. Read what the other side
actually does before classifying — and before proposing to widen anything.

## Class D — measured and deliberately KEPT

| line | why |
| ---: | --- |
| 112983 | the over-aligned-pointee arm in `memory_aggregate_ref_pointee`. Tested for removal 2026-09-29: ungating it fires on NOTHING (`core` unchanged, all 18 runtime programs unchanged). Shipping it would be an unexercised lowering; it needs a CONSTRUCTED over-aligned-pointee test first. The in-source comment records this. |
| 3772, 10210 | CGU private-symbol planning and the `UnwindAction::Terminate` EH activation. Both are Linux-aarch64 rollout scopes tied to the EH work in Class B; move them WITH that feature, not separately. |

## Method that this audit assumes

One gate at a time, and for each: the `core` census at O3 compared by SET DIFFERENCE
(not counts), the 18-program execution differential, and the Trust / Clean / TY
suites. A gate that changes nothing measurable is NOT landed — an unexercised
widening on this target is the one class of change worth refusing, per the 112983
precedent.
