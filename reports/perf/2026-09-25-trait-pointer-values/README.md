# Trait-object pointer values and returns

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

On base `275e8973ae8a9b39d442eb45f6c8ffba871a988a`, the bridge now carries
trait-object data and vtable pointers together through Rust argument, return,
and call-result slots. Admission requires rustc's actual 16-byte, 8-aligned
ScalarPair layout. Casts and reference/raw reborrows preserve both lanes;
NonNull transmutes store both into their destination slot. Slot-backed call
arguments and virtual receivers read the pair from memory. An explicit
wide-to-thin raw pointer cast selects only the data pointer.

The expanded native test exposed two further missing operations. Unsize
construction now erases the concrete data pointer's IR pointee type before
joining different implementors, retaining the same address. Dynamic
size_of_val/align_of_val read rustc's named common vtable entries. A repr(C)
single-field scalar struct can be byte-addressed only when its one scalar
field occupies its full layout at offset zero. Different-principal trait
upcasts and nested supertrait vtables remain refused. No ABI validator,
loop-completeness guard, proof gate or dependency pin was weakened.

Final qualification uses genuine immutable Trust `ae9c2c1da` and the matching
private compiler SDK: mandatory bridge all-targets check, five-test discovery,
fresh backend and the maintained trait-pointer regression all pass. Fourteen
operations exercise shared/mutable references, raw-pointer mutability casts,
NonNull identity/conversion/dereference, pointer-based mutation, size/alignment,
loop selection and indirect calls. Two different implementors have distinct
methods and layouts (size/alignment 8/8 and 32/16), preventing a swapped metadata
slot from satisfying the oracle. Inputs include zero, wrapping values and high
bits. Each execution checks values, untouched fields and surrounding sentinels:
201,600 checks across LLVM/CG and O0–O3 = **1,612,800 native checks**. The actual
compiler-supplied Rust runtime is linked; its panic control must raise SIGABRT.
No panic stubs or substituted helper bodies are used.

The existing thin-pointer loop and scalar-union join tests both pass on this
same backend: 70,720 and 31,200 native checks respectively. Root formatting
passes, and private-source comparison retains the 61 preexisting formatter
edits with zero new edits; changed tests and Rust fixture pass full formatting.

The tenth full-core diagnostic repeats the entire original source denominator
and original LLVM control retained by the earlier bridge reports. The failing
root count falls **59 -> 47**, removing twelve trait-object-related roots with
zero new failing roots. Whole-core compilation still fails. Intermediate
measurements (49 then 47), the original six-root minimal failure, expanded
fixture failures, MIR, source snapshots and successful final controls are kept.
Native and core diagnostics explicitly disable frontend verification and
codegen certificates; they are not formal proof or self-host evidence.

The unchanged mandatory proof-required C FnABI test was also rerun against the
final backend. It still fails **TCG-PROOF-465** at aliased_f32_read because its
emitted AArch64 opcode inventory contains uncovered instructions. The complete
failed run and LLVM/runtime control artifacts are retained. No proof-required
ABI pass, current full Linux floor, installed compiler promotion or whole-system
completion is claimed. All G1–G8 and L01–L14 remain open.

manifest.json and inventory.json bind compressed records; assets.json binds
every tar member by hash and size. excluded.json lists rebuildable backend and
runtime archives. Native objects, executables and command transcripts are kept
losslessly. The final source hashes are in trait-pointer-values-repair-second.
