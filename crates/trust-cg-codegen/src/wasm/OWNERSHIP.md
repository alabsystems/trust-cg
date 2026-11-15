# The shared-memory ownership map

Normative contract for a trust-cg wasm **island** that lives beside a host
module in one linear memory.

Status: P2 architecture slice (trust `designs/2026-08-24-one-module-every-target.md`
§4). The lane is **differential-experimental**; nothing here is a verified
claim, and §5 below says exactly what this document does to the claim that
P4 will eventually be allowed to make.

**Citation pin.** Every `file:line` below is pinned to trust-cg `911cc870`,
the P2 baseline — resolve one with
`git show 911cc870:crates/trust-cg-codegen/src/wasm/<file>`. The pin is
load-bearing rather than tidy: `encode.rs` and `lower.rs` are being rewritten
*in this same slice* by the import/index-space work this document specifies, so
working-tree line numbers have already moved. Citations describe the behaviour
this contract is written against; §7 says which of it the in-flight
implementation has since changed. The two working-tree citations in §4.3 are
marked as such.

**Normative language.** MUST / MUST NOT / SHOULD carry their usual force and
bind the **host**, not the module — the module cannot check any of them.
**NOT ENFORCED (host obligation)** marks a property that the emitted wasm
does not test at runtime and the backend does not test at compile time. A
violated NOT-ENFORCED clause does not produce an error, a trap, or an
evidence field. It produces wrong bytes in someone else's memory.

---

## 0. Why this document exists

Until P2 a trust-cg wasm module is *closed*: it imports nothing, defines its
own memory, and its address space contains nothing but itself. The whole
correctness story therefore fits inside the module, and "the boundary is the
module" is literally true.

P2 breaks that. An island that shares a host's linear memory is correct only
*relative to* a division of that memory which no wasm mechanism expresses and
no engine checks. This document is that division, written down. It is the
normative form of the bound host/import/shared-memory/initialization/allocator
contract that §4 P2 says joins the claimed surface.

---

## 1. Memory policies and their region maps

An island is compiled under exactly one **memory policy**. The policy is part
of the island's identity, not a link-time option: it changes which addresses
the emitted code may name.

| Policy | Memory | Island's address space |
| --- | --- | --- |
| **N** — none | no memory declared | none; the island touches linear memory not at all |
| **O** — owned | module *defines* one memory | the whole memory, exclusively |
| **I** — imported | module *imports* the host's memory | only the regions negotiated here |

### 1.1 What the backend emits today (baseline facts)

- `compile_module` declares a memory **only** when some function contains an
  `Alloca` (`lower.rs:1796-1801`, gate `uses_stack_frame` at `lower.rs:1750-1755`).
  Memory-free islands are Policy N and get no memory section at all — the two
  shipped P5 islands (`vt_step`, `wcwidth`) are exactly this.
- When a memory is declared it is always **defined, never imported**, as a
  single memory with a min-only limit (`encode.rs:231-238`), and it is **not
  exported** — `ExportKind` has one variant, `Func` (`encode.rs:92-104`), and
  `compile_module` exports only functions (`lower.rs:1842`). Under Policy O
  the host cannot read the island's memory at all.
- The shadow stack pointer is a module-level mutable `i32` global initialized
  to the compile-time constant `STACK_TOP = 65536` (`lower.rs:522`,
  `lower.rs:1798`), inside a memory of `STACK_PAGES = 1` page
  (`lower.rs:521`) — i.e. the stack region *is* the entire memory.
- There is **no import section** in the baseline encoder at all: `finish`
  emits sections 1, 3, 4, 5, 6, 7, 9, 10 (`encode.rs:191-314`) and no others.
  In particular there is no start section (8) and no data section (11), so
  the module performs **zero self-initialization**.

Verified by compiling two modules and decoding the sections (reference
validator: `wasmparser` 0.240.0, the same gate as
`crates/trust-cg-codegen/tests/wasm_module_validation.rs`):

```
A. ptr param + i32 load, NO alloca      -> 59 bytes, sections [1, 3, 7, 10]
   wasmparser: INVALID -> unknown memory 0 (at offset 0x31)

B. one i32 alloca (frame)               -> 96 bytes, sections [1, 3, 5, 6, 7, 10]
   section 5: 01 00 01                  -> 1 memory, min-only, 1 page
   section 6: 01 7f 01 41 80 80 04 0b   -> 1 global, i32, mutable, i32.const 65536
   wasmparser: VALID
```

Case A is the shape §6 is about — a pure island reading a buffer the host
owns. **It is not merely unspecified today; it is unemittable.** The memory
is provisioned by the presence of an `Alloca`, and a function that only reads
through a pointer parameter has none, so the backend emits `i32.load` against
a memory index that does not exist and the reference validator rejects the
module. Provisioning memory from `Alloca` presence is the bug this policy
split replaces: memory presence MUST follow from the declared policy, not
from an incidental instruction.

### 1.2 Policy O — owned memory

The island owns `[0, 65536 × pages)` and the host owns nothing inside it.

- **May read and write:** the live stack `[SP, 65536)` and, once P3 lands data
  segments, its own static region. Nothing else exists there today.
- **Must never touch:** nothing — there is nothing else in the memory.
- **Host may touch:** nothing. The memory is not exported, so the host has no
  handle to it.
- **Confinement** to `[0, memory_size)` holds for every access. This is a
  property of the **engine's** bounds check, not of trust-cg: `lower.rs`
  emits raw `i32.load`/`i32.store` with no address check (`lower.rs:1324-1343`).
  Under Policy O it coincides with the ownership map because the island owns
  the whole memory. Under Policy I it does not, and that difference is the
  entire subject of §1.3.

Policy O is the correct policy for an island that has no host to share with.
It carries no host obligations beyond "instantiate it".

### 1.3 Policy I — imported (shared) memory

The island imports the host's memory. Its address space is now populated by
someone else, and the island's rights are exactly two regions and nothing
else.

**Region S — the island's stack reserve.** A half-open byte range
`S = [B − R, B)` where `B` is the **stack base** (§1.4) and `R` the **stack
reserve**, both supplied by the host at instantiation (§2).

- The island MAY read and write every byte of `S`, at any time, in any order,
  without announcing it. Bytes in `S` are the island's scratch and their
  contents between calls are unspecified.
- The host MUST NOT read or write `S` while any island call is in flight, and
  MUST NOT interpret its contents at any time.

**Region A — the argument windows.** For each pointer argument of an exported
function, the window `[ptr, ptr + n × sizeof(elem))` where `n` is the length
argument declared alongside it in the island's manifest.

- A window declared **read** may be read by the island and MUST NOT be written
  by it.
- A window declared **write** may be read and written by the island.
- The host MUST keep every window valid, in-bounds, and unmoved for the whole
  duration of the call, and MUST NOT mutate a read window concurrently.

**Everything else in the memory is off-limits.** The island MUST NOT read or
write any address outside `S ∪ A`. That includes address `0`.

**What actually stops it: nothing.**

- **NOT ENFORCED (host obligation)** — no load or store carries a region
  check. `Load`/`Store` lower to a bare `local.get` of the pointer followed by
  `i32.load` / `i32.store` with a memarg offset of `0` (`lower.rs:1324-1343`),
  verified in the case-B bytes as `28 02 00` and `36 02 00`. There is no base,
  no limit, and no comparison. In the working tree the scalar `Load`/`Store`
  still use offset `0`, while struct fields, enum tags and lanes, the high
  half of a 128-bit value, sret slots and parameter / return lanes are
  reached through a NONZERO memarg offset (`lower/value.rs` `emit_load` /
  `emit_store`) — equally unchecked against any region.
- **NOT ENFORCED (host obligation)** — GEP address arithmetic is wrapping
  32-bit arithmetic: `base + index × sizeof(pointee)` via `i32.mul` /
  `i32.add`, plus a constant field offset for a struct GEP
  (`lower.rs:1265-1322`). An index outside the buffer produces an address that
  is still inside the host's memory, and the engine accepts it. The one thing
  that *is* proved about this formula is that the stride equals the element
  size, so distinct in-bounds elements are disjoint
  (`crates/trust-cg-verify/src/wasm_memory_proofs.rs:110-116`) — in-bounds is a
  hypothesis of that proof, not a conclusion.
- **NOT ENFORCED (host obligation)** — **a null pointer does not trap.**
  Address `0` is an ordinary readable, writable address in a wasm linear
  memory. Under Policy O a null dereference silently reads zeros; under Policy
  I it silently reads or overwrites whatever the host put at the bottom of its
  memory.
- The engine's bounds check still fires, but it now only says "inside the
  host's memory", which is precisely the set of addresses the island is
  supposed to stay out of. **Under Policy I the engine's trap stops nothing
  the ownership map cares about.**

### 1.4 The frame, exactly

This is the part a host must get right, so it is stated without abbreviation.

**Stack base `B`.** The value the stack-pointer global holds when no island
frame is live. It is the **exclusive** upper bound of the stack region: the
byte at `B` is *not* the island's. Under Policy O, `B = 65536`
(`lower.rs:522`), which is the top of the island's own single page. Under
Policy I, `B` is host-supplied (§2) and `65536` has no meaning whatsoever —
under a shared memory it is page 1 of the host's data.

**Frames grow DOWN.** For a call with frame size `F` the prologue is
(`lower.rs:705-720`, verified as `23 00 21 03 20 03 41 08 6b 22 04 24 00`):

```
saved      := SP              ; global.get, local.set
frame_base := saved − F       ; i32.const F, i32.sub
SP         := frame_base      ; local.tee, global.set
```

so the frame occupies `[SP_new, SP_old)` — low-inclusive, high-exclusive,
immediately below its caller's frame. The epilogue restores `SP := saved`
(`lower.rs:1480-1487`, verified as `20 03 24 00`).

A function with no `Alloca`, home, staging or call-scratch slot has no frame
at all (`compute_frame` leaves it `None`): it emits no prologue, epilogue,
stack-pointer update or stack guard, touches no stack byte, and the
frame-bounds guard has nothing to check in it. At O1 and above the trust-ir
mid-end's store forwarding, dead-slot removal and scalar replacement
(`crates/trust-cg-irmid`) remove the slots they prove unobservable, so more
functions are frameless; `F = 0` contributes nothing to the bound below.
The mid-end's inliner splices a callee's body, its `Alloca`s included, into
its caller, so the callee's slots become the caller's for the whole
activation; it never splices an allocating callee into a block on a cycle of
the caller, nor one with an `Alloca` on a cycle of its own, so a spliced
`Alloca` runs at most once per activation and gets a fixed offset (never the
per-execution carving below). Because the slot is
held on every path of the activation, it never splices an allocating callee
into a caller on a cycle of direct calls (each recursion level would hold
it), and the slots spliced into one caller total at most 1024 bytes
(`MAX_SPLICED_SLOT_BYTES`, which also bounds the per-level growth of a
recursion through calls the module does not show). A chain that went
through the callee's frame now holds one frame instead of two, and a caller
that inlines several callees holds all their slots at once (the stack
high-water mark can rise, by at most that bound per activation, where a
caller calls deeply while holding them).
The mid-end's argument promotion passes a caller's slot to a clone of the
callee as values and takes the bytes the callee writes back as results; the
clone allocates its own copy of those bytes (at most 64 per promoted
parameter) in its entry block, so the copy runs once per activation of the
clone, gets a fixed offset in the clone's frame, and lives only while the
clone runs; the caller's slot, whose only escape was the call, is usually
removed by scalar replacement, and so is the clone's copy.
The mid-end's full unrolling copies no loop that executes an `Alloca`
(policy: each copy would take its own fixed slot where the loop's one
`Alloca` keeps one), so it adds no frame bytes; the arrays it lets scalar
replacement remove take frame bytes away.

**Frame internals.** Every `Alloca` that runs at most once per activation —
or whose earlier pointers provably cannot be observed after it runs again
(`lower/captures.rs`, asking the capture analysis in
`crates/trust-cg-irmid/src/escape.rs`) — is assigned a byte offset `off` with
`0 ≤ off < F` and `off ≡ 0 (mod 8)`, and `F = align_up(total, 8)`
(`lower.rs:666-701`, specifically `align_up(offset, 8)` at `lower.rs:679` and
`frame_size = align_up(offset, 8)` at `lower.rs:694`). The 8-byte slot
alignment is a cleanliness choice, not a correctness requirement — the code
says so (`lower.rs:676-677`) because wasm's non-atomic accesses do not trap on
misalignment. An alloca's address is `frame_base + off` (`lower.rs:1250-1264`),
computed with `i32.add`. There are **no negative offsets and no red zone**:
the frame is entirely within `[frame_base, frame_base + F)`. Any other
`Alloca` (one in a loop whose earlier pointer may still be read) is carved from
the shadow stack at each execution, `SP := (SP − size) & −align`, and released
by the epilogue's restore; it is still below the caller's `SP`. After the
allocas the frame holds the home slots of memory-carried values, which share
bytes when their live ranges never overlap (`lower/storage.rs`), and one
transient region shared by every edge-staging, call-scratch and 128-bit
division-scratch site.

**The bound that holds.** For a call chain with frame sizes `F₁ … Fₙ` entered
at base `B`, every stack byte the island touches lies in
`[B − ΣFᵢ, B)`. This follows from the prologue/epilogue pair alone and is a
property of the emitted code.

**The bounds that do not hold, and are not checked:**

- **NOT ENFORCED (host obligation)** — `ΣFᵢ ≤ R`. An island's prologue
  contains no comparison against any limit. There is no stack-limit global,
  no guard, and no trap (the Policy O floor check below is against the
  module's own static data, not a reserve). When the chain is deeper than the
  reserve, the frames simply continue downward into whatever is below `B − R`.
- **NOT ENFORCED (host obligation)** — recursion depth. The lowering imposes
  no depth limit, so `ΣFᵢ` is unbounded for any island with a cycle in its
  call graph.
- **NOT ENFORCED (host obligation)** — `B ≡ 0 (mod 8)`. If the host supplies a
  misaligned base, every frame slot is misaligned by the same amount. Under
  the current instruction set this is *not* a wrong answer and *not* a trap:
  the align immediate that `emit_memarg` writes (`encode.rs:508-511`, natural
  alignment from `lower.rs:129-137`) is a **hint**, and wasm engines do not
  trap non-atomic accesses on a misaligned effective address. What it does is
  make the module's declared alignment false, cost performance on engines that
  split unaligned accesses, and pre-break any future atomic or SIMD access,
  which *would* trap. Report it as a violated invariant, not as corruption.
- Under Policy O the module's static data sits at the bottom of the memory
  it owns and the stack grows down toward it. When the module HAS static
  data, every prologue and every per-execution `Alloca` checks the new `SP`
  against the end of that data (and against a wrapped subtraction) and
  executes `unreachable` instead of writing below it. Every `SP` the module
  publishes is therefore at or above that floor or followed immediately by
  `unreachable`, and no frame byte is written below it. A trap leaves behind
  either a lowered `SP` still at or above the floor (later frames run with
  less stack and are still checked) or one below it (every later framed call
  traps). When the module has NO static data there is no check, and overflow
  is caught only *accidentally*: `i32.sub` wraps, so an `SP` driven below
  zero becomes a huge unsigned address and the engine's bounds check traps on
  the first access. **Under Policy I there is no check and no such net** —
  below `B − R` there is more valid host memory, and the island writes into it
  without a trap.

**Recommended host mitigation, stated honestly.** A host MAY place a canary
word at `B − R − 4` and check it after each call. That **detects** overflow
after the fact; it does not prevent it, and by the time it fires the island
has already written outside its region. wasm has no unmapped pages inside a
linear memory, so a true guard page is not available.

### 1.5 The unchecked-property register

| Property | Who guarantees it | Checked at runtime? |
| --- | --- | --- |
| access inside the memory | engine bounds check | yes (traps) |
| access inside `S ∪ A` | **host** | **no** |
| `ΣFᵢ ≤ R` | **host** | **no** |
| `B ≡ 0 (mod 8)` | **host** | **no** |
| `S` disjoint from host allocations | **host** | **no** |
| argument window in-bounds and live | **host** | **no** |
| pointer non-null | **host** | **no** |
| frame internals within `[base, base+F)` | trust-cg (`lower.rs:666-701`); every constant-offset access through the frame base re-checked on the emitted body, refused otherwise (`frame_bounds.rs`, working tree) | n/a — static |
| stride = element size for in-bounds GEP | trust-cg, proved (`wasm_memory_proofs.rs:110-116`) | n/a — static |
| shadow-stack frame offset arithmetic | **nobody yet** | see `wasm_memory_proofs.rs:31-34` |

---

## 2. The initialization contract

**Who performs it: the host, at instantiation.** The module does nothing. It
emits no start section and no data segments (`encode.rs:191-314`), so between
instantiation and the first exported call the island executes not one
instruction.

Under Policy I the following MUST hold before the first exported call.

1. **A memory is supplied**, and `memory.size × 65536 ≥ B`.
2. **The stack base is supplied.** The base MUST be delivered as an
   **imported immutable `i32` global**, from which the module's own mutable
   stack-pointer global is initialized (§4). This is a deliberate structural
   choice: an import is a *required instantiation argument*, so a missing base
   is a `LinkError` at instantiation rather than an island quietly running
   with a base of `65536` in the middle of the host's data. It is the only
   clause in this document that is enforced rather than promised.
3. **`B ≡ 0 (mod 8)`.**
4. **`B − R ≥ 0`**, and `S = [B − R, B)` is **disjoint from every other live
   allocation in the memory** — the host's data segments, its heap, its own
   shadow stack, and every other island's region — for the entire lifetime of
   the instance. `S` MUST NOT be handed to a host allocator.
5. **`R ≥ D`**, where `D` is the island's maximum stack depth (§7).
6. **The region need not be zeroed.** The island never requires initialized
   frame bytes; reading an alloca before writing it is trust-ir UB, not a host
   obligation. **NOT ENFORCED (host obligation)** — no such read is detected.

What a violation does:

| Violated | Effect | Detected |
| --- | --- | --- |
| (2) base not supplied | instantiation fails | **yes** — LinkError |
| (1) memory smaller than `B` | trap on the first frame access | yes — engine trap |
| (3) misaligned base | false alignment declaration; future atomics would trap | no |
| (4) region overlaps host data | island frames overwrite live host bytes | **no — silent corruption** |
| (5) `R < D` | frames descend below `S` into host data | **no — silent corruption** |
| argument window invalid | reads or writes the wrong host bytes | **no — silent corruption** |

Three rows of that table say *silent corruption*, and that is the honest
summary of the initialization contract: it is unchecked, and the failure mode
of getting it wrong is not an error but wrong data in the host's memory,
attributed to the host.

**Memory growth is safe.** The host MAY `memory.grow`; wasm guarantees
existing addresses and contents are preserved, so `S` and `A` survive.
Memories cannot shrink. The island itself never grows memory — no
`memory.grow` or `memory.size` opcode exists in the emitter (`encode.rs:326-492`).

**Allocator contract: there is none.** A trust-cg island has no allocator, no
`malloc` import, no heap, and no data segments. Every buffer it touches is
allocated by the host before the call and described by a (pointer, length)
argument pair. An island MUST NOT import an allocation function, and a host
MUST NOT expect the island to free anything.

---

## 3. Reentrancy and concurrency

The stack pointer is one mutable global per instance, shared by every function
in the island (`lower.rs:1798` — under Policy O the only global the module
has). Everything below follows from that.

**Nested reentrancy is safe by construction.** If the host calls export `A`,
`A` calls a host import, and the host calls export `B` on the *same instance*
before `A` returns, `B`'s prologue carves its frame below `A`'s and `B`'s
epilogue restores. That is an ordinary deeper stack. It is not free: the
nesting consumes the same reserve, so `D` in §2(5) MUST be the deepest total
the host can induce **including reentrant nesting**, not the island's own
static depth. **NOT ENFORCED (host obligation).**

**Abandoned frames poison the instance.** The epilogue runs only on a normal
`Return` (`lower.rs:1480-1487`). Any exit that skips it leaves the stack
pointer at the inner value permanently:

- a trap — `unreachable`, integer division by zero, an out-of-bounds access;
- a host exception thrown through an import call and propagated out of the
  island (a JS `throw`, a wasmtime host-function error).

The next entry then starts from the abandoned, lower value. Over repeated
abandoned calls the stack pointer descends monotonically, leaves `S`, and —
under Policy I, with no wrap-trap net (§1.4) — starts writing into host data.

> **Rule R1.** After any island call that does not return normally, the host
> MUST discard the instance. A trapped island instance is poisoned and MUST
> NOT be called again.

R1 is fail-closed and needs no new module surface. The alternative — exporting
the stack-pointer global so the host can reset it — is possible for Lane A but
widens the host's write surface into island state and is not the default.

**Concurrency.** wasm globals are per-instance and instances are not shareable
across agents; only *memories* are. So N threads sharing one memory means N
instances, each with its own private stack pointer, each initialized from its
own imported base.

> **Rule R2.** Each concurrently live island instance MUST be given a
> **disjoint** stack region. Two instances instantiated with the same base
> carve the same addresses and silently corrupt each other.

**NOT ENFORCED (host obligation)** — nothing in the module can observe another
instance's base. R2 is unobservable from inside and unverifiable from the
bytes.

**One property comes free.** A single instance cannot be entered concurrently,
because the platform does not let two agents share an instance. That is
enforced by the engine, not by us, and it is the only concurrency guarantee in
this section that does not rest on the host.

**The island holds no other mutable state.** No data segments, no globals
besides the stack pointer. Two instances over disjoint regions cannot race
through island state. Any race they have is a race through host buffers, which
is the host's to prevent.

---

## 4. The import surface

An island's imports are a **closed whitelist**. Anything not on it MUST be
refused at lowering rather than passed through.

### 4.1 Permitted imports

| # | Kind | Name | When | Supplied by the host as |
| --- | --- | --- | --- | --- |
| 1 | memory | `<ns> "memory"` | Policy I | the host's `WebAssembly.Memory` |
| 2 | global, **immutable** `i32` | `<ns> "__island_stack_base"` | Policy I **and** the island has a frame | the base `B` (§2) |
| 3 | func | `<ns> "<name>"` | opt-in, declared in the manifest | a host function, C ABI |

`<ns>` is the import namespace fixed in §4.3 — **not** `env`.

**The stack pointer stays a defined global, not an imported one.** The island
imports the immutable base (row 2) and *defines* its mutable stack pointer
with the initializer `global.get $__island_stack_base`. This is deliberate and
has three consequences worth naming:

- it needs no wasm extension — a constant expression reading an imported
  immutable global is core wasm 1.0, whereas importing a *mutable* global
  requires the mutable-globals feature;
- the stack pointer stays **per-instance**, which is exactly what rule R2
  needs — instances get private pointers and only the base differs;
- initialization becomes structural: the base cannot be unset, because
  instantiation supplies it.

Lane A consequence: the encoder's global initializers are `i32.const` /
`i64.const` only (`encode.rs:240-261`), so a `global.get` initializer is new
surface — and **imported globals shift the global index space exactly as
imported functions shift the function index space**. `add_global` returns
`self.globals.len()` (`encode.rs:169-173`) with the same zero-import
assumption as `add_function` (`encode.rs:154-158`).

**Function imports are opt-in and default to none.** The default island shape
is *pure*: zero function imports. Every function import is a door back into
the host, and every such door re-opens the reentrancy hazard of §3 and pulls
the host's own behaviour into the island's claimed surface. An island that
declares function imports MUST list them in its manifest with their exact
signatures. Parameters and results are scalars only — `i32`/`i64`/`f32`/`f64`
— which the type mapping already enforces: non-scalar types are refused at
`valtype_of`, and a by-value aggregate crosses as the `i32` address of its
bytes (or its one scalar member), by the WebAssembly Basic C ABI
(`lower/abi.rs`). A module whose `TargetInfo.struct_passing` is
`Unclassified` is refused once an aggregate crosses a call edge by value, and
`AlwaysMemory` is refused outright (`reject_unconsumed_target_abi_surface`);
`wasm32_target_info` stamps `NativeC`, the classification the lane applies.

### 4.2 Forbidden imports

Table imports, tag/exception imports, any allocation function, any
wasm-bindgen-shaped import, and any import in the `env` namespace. Per §4
ruling 4 of the design, the wasm-bindgen glue is a permanent host-side
contract **of the LLVM module only** and never appears in an island.

### 4.3 Naming and versioning

Import module names are arbitrary UTF-8, so the following string grammar is
legal in every engine and is chosen to be impossible to collide with `env`,
`wasi_snapshot_preview1`, or a wasm-bindgen namespace by accident:

```
trust:island/abi@<major>        the fixed runtime contract (memory, __island_stack_base)
trust:island/<island>@<major>   host functions a named island declares
```

- `<major>` bumps on any **breaking** change to that surface: a name removed,
  a signature changed, a region-contract semantic changed (base becomes
  inclusive, windows change ownership mode). Adding a new optional name does
  not bump it.
- An island MUST NOT import two different majors of the same surface.
- The names `__island_stack_base`, `__island_stack_pointer`, and any name
  beginning `__island_` are reserved.

> **Open discrepancy — the namespace, not the member names.** The P2
> implementation landing alongside this document sets
> `ISLAND_HOST_MODULE = "env"` (`lower.rs:627` in the working tree; the member
> names `"memory"` and `"__island_stack_base"` at `lower.rs:629`/`632` agree
> with the table above). This document's ruling is that `env` is the wrong
> namespace and MUST be replaced, for two reasons that are specific to the case
> §6 describes rather than stylistic:
>
> 1. §4 ruling 4 of the design requires "an **explicit** import namespace".
>    `env` is the *implicit default* namespace of the wasm C toolchain — the
>    one Emscripten, wasi-libc, and wasm-bindgen glue already occupy. Choosing
>    it is choosing not to have a namespace.
> 2. `env.memory` is the conventional name for a **linker-supplied** memory. A
>    host wiring an island into an import object that already serves an
>    LLVM-built module — exactly the aterm arrangement in §6 — can satisfy the
>    island's memory import from the existing `env.memory` entry silently, with
>    no error at instantiation and no way for either side to notice. The whole
>    purpose of the ownership map is that the island's memory is *negotiated*;
>    a namespace that lets it be *defaulted* undoes that at the first link.
>
> Resolution is §7 item 7. Until it lands, the shipped constant and this
> document disagree, and this note is the record of which one is normative.

**Export naming, as it stands.** Every trust-ir function is exported verbatim
under its trust-ir name, one export per function, with no prefix and no
mangling (`lower.rs:1833-1843`, confirmed in the case-A/B section-7 bytes:
`read_host_word`, `spill`). That is the surface the shipped P5 islands already
use and this document does not change it. **NOT ENFORCED** — no export-name
policy runs in the wasm backend: `export_func` appends without inspecting the
name (`encode.rs:182-188`), so reserved-prefix violations and duplicate export
names are caught, if at all, downstream at the reference validator rather than
fail-closed at lowering. An island MUST declare its exported name set in its
manifest.

*Working tree:* the closed lowering now decides its export set
(`closed_function_exports` in `lower.rs`). Two externally visible exports of
one name — two definitions, or a definition and the memory export or a growth
shim — are refused (`[TCG-WASM-EXPORT]`). A module-local (internal/private)
definition is exported under its name unless another definition or export
uses that name, in which case it is left unexported; nothing outside the
module may name it, and calls inside the module name functions by index.
Reserved prefixes are still not checked.

---

## 5. What this does to the claim

This is the section the design doc demands. It is meant to be quoted.

> **"The boundary is the module" is true exactly while the module imports
> nothing.** The moment an island imports a host's memory, the proven object
> stops being the module and becomes the pair *(module, ownership map)*. Every
> clause of this document marked NOT ENFORCED is a hypothesis of the eventual
> theorem, discharged by the host and by nobody else — and a claim quoted
> without the map is a claim quoted without its hypothesis.

**Stays module-local** — properties of the emitted bytes, true for any host:

- module well-formedness and type/validation soundness, gated by an
  independent implementation of the spec
  (`crates/trust-cg-codegen/tests/wasm_module_validation.rs`);
- the fail-closed accepted-input perimeter: wasm32 target pin, calling
  convention, multi-result calls, EH instructions and integer unary ops at a
  non-integer type (`not bool`), all refused by name at both public entries
  (`require_wasm32_target_info`, `reject_unsupported_call_contract`,
  `reject_unwired_eh_instructions`, `reject_non_integer_scalar_unops` in
  `lower.rs`);
- the native admission, applied by every module, object and single-function
  entry before any surface or body is looked at (`admit_for_codegen`):
  trust-ir's codegen admission (`trust_cg_lower::validate_codegen_prerequisites`,
  which no policy widens), then the codegen license under the caller's
  `CodegenLicensePolicy` (the `*_license` entries; the default policy
  elsewhere). The body constructs the native instruction translator refuses
  (`RegionHavocStore`, a marked `Undef`, an `Undef` outside the native
  scalar carrier set, a non-array `ArraySplat`, a pointer op at a non-pointer
  type or with a result arity other than one, and a `PtrMetadata` /
  `PtrFromParts` whose metadata type is not the pointer's metadata at 32-bit
  pointers) are refused by name as well (`reject_unmodeled_body_constructs`). Every module row of trust-ir's
  must-refuse corpus is driven through both lanes by both
  `must_refuse_corpus` targets (trust-cg-codegen in process, trust-cg-cli
  through the binary), with exact known-accepted tables. *Working tree:* irreducible CFGs are no longer refused;
  `Lowering::build` selects a dispatch loop over a label local
  (`Lowering::emit_dispatch`) for them, whose bytes the CFG structural
  checker validates like any other;
- frame layout arithmetic — offsets, slot alignment, frame size, downward
  growth, and epilogue restoration on normal return (`lower.rs:666-720`,
  `lower.rs:1480-1487`);
- GEP stride correctness for in-bounds indices, the one memory obligation
  discharged formally today (`wasm_memory_proofs.rs:110-116`) — noting that
  shadow-stack frame offset arithmetic is explicitly **not yet covered**
  (`wasm_memory_proofs.rs:31-34`);
- purity relative to whatever memory it is handed: with the default zero
  function imports, an island reads no clock, no randomness, and calls nothing
  outside itself.

**Becomes a host obligation** — outside the module, unchecked, and inherited
by anything that quotes the module's result:

- region disjointness (§2.4) and base alignment (§2.3);
- reserve sufficiency against the true maximum depth, reentrant nesting
  included (§2.5, §3);
- validity, liveness, and non-concurrent-mutation of every argument window
  (§1.3);
- one disjoint region per concurrently live instance (R2);
- discarding a trapped instance (R1);
- staying out of `S` for the duration of every call.

**Three consequences stated plainly.**

1. **P2 does not lower today's claim, because there is no claim to lower.**
   Every wasm compile already reports verdict `MissingEvidence` and route
   `NotRun` (`lower.rs:1863-1876`, `lower.rs:1917-1943`). What P2 changes is
   the *shape of the claim P4 will be permitted to make* — and recording that
   shape now, before the proofs exist, is the point of writing this down
   early. A proof family landed against an unwritten host contract would be
   over-read on the day it landed.

2. **After P4, the honest phrase is "verified island under a stated host
   contract", never "verified module".** The six obligation families of §4
   ruling 5 discharge properties of the *module*. None of them can discharge a
   property of the host's memory layout, because the module does not name it.

3. **A host that violates the map does not get a failure.** There is no trap,
   no diagnostic, and no evidence field that records it. The island computes
   on and writes into the host's bytes. Any assurance statement that omits
   this sentence is misleading, however true its module-local half is.

Until the P4 families exist the lane stays labeled
**differential-experimental** — no "verified" wording, no proof links.

---

## 6. Worked example: an island beside the aterm engine

**Setting.** The shipped aterm terminal (alab.systems/terminal) is an
LLVM-built wasm module and stays LLVM-built (§4 ruling 1). It owns the linear
memory: its data segments, its Rust heap, and its own `__stack_pointer`
shadow stack all live there at addresses `wasm-ld` chose. **Nothing in the
artifact declares which of those addresses are free**, which is precisely why
the island's compile-time constant `STACK_TOP = 65536` (`lower.rs:522`) cannot
be trusted under sharing: address 65536 is page 1 of the host's memory, and no
declaration anywhere says it is unoccupied.

**The island.** `run_width(ptr: *const u32, len: u32) -> u32` — the display
width of a run of codepoints the engine already holds in a buffer, summing the
`wcwidth` logic that P5 already ships as a pure island.

### 6a. The shape aterm should actually ship: frame-free

`run_width` needs no `Alloca`. Compiled with no allocas it is **Policy N** and
has **no stack contract at all** — it imports only the memory and declares
`R = 0`. Region `A` is its whole world.

| Obligation | Owner |
| --- | --- |
| supply the memory import | host |
| buffer `[ptr, ptr + 4·len)` in-bounds, live, immutable for the call | host |
| `len` is the true element count | host |
| read only `[ptr, ptr + 4·len)`; write nothing | island |
| return a value that depends on nothing but those bytes | island |

That is the whole map, and it is short because the island has no state. Every
island that *can* be authored frame-free SHOULD be.

Note what has to change for even this to compile: today a memory is
provisioned by the presence of an `Alloca` (`lower.rs:1796-1801`), so this
exact function emits `i32.load` with no memory section and the reference
validator rejects it — measured in §1.1 case A as
`unknown memory 0 (at offset 0x31)`.

### 6b. The general case: the island carries a frame

Give `run_width` a 64-byte scratch buffer, so it allocas and Policy I's full
stack contract applies. Say the host reserves `R = 4096` at a base `B` it
carved out of its own allocator.

**Host obligations** — each with what breaks if it is missed:

1. Import object supplies `"trust:island/abi@1" "memory"` (the engine's own
   memory) and `"trust:island/abi@1" "__island_stack_base" = B`. *Missing →
   LinkError at instantiation. The only obligation here that fails loudly —
   and only because the base is an import rather than a setter; see §4.3 for
   why the namespace must not be `env`, which is the namespace this very import
   object already uses for the engine's own glue.*
2. `B ≡ 0 (mod 8)`. *Missed → false alignment declaration; no trap today.*
3. `[B − 4096, B)` is reserved out of the engine's allocator for the instance's
   lifetime and never handed back. *Missed → island frames overwrite live
   engine data, silently.*
4. `4096 ≥ D`, where `D` is the island's declared maximum depth (§7). *Missed →
   frames descend past `B − 4096` into engine data, silently — and with a
   shared memory there is no wrap-trap net (§1.4).*
5. `[ptr, ptr + 4·len)` is in-bounds, live, and not mutated by any other agent
   for the whole call. *Missed → the island reads engine bytes that are not the
   row, and returns a confident wrong width.*
6. The engine does not read or write `[B − 4096, B)` while the call is in
   flight. *Missed → the island's own frame is corrupted under it.*
7. If the call traps, discard the instance (R1). *Missed → the stack pointer
   stays abandoned and the next call starts lower, walking out of the region.*
8. If the engine ever runs the island on a second thread, that instance gets a
   different `B` with a disjoint region (R2). *Missed → two instances carve the
   same addresses.*

**Island obligations:**

1. Read only `[ptr, ptr + 4·len)`; write only `[B − ΣFᵢ, B)`.
2. Never retain `ptr` across calls — it has no storage to retain it in, which
   is a property of the frame-only design, not a promise.
3. Import nothing beyond rows 1 and 2 of §4.1: no allocator, no host function,
   no table.
4. Restore the stack pointer on every normal return (it does —
   `lower.rs:1480-1487`).

**What neither side gets.** The engine gets no assurance that obligations 2–6
were met — no trap, no diagnostic, no evidence field. The island gets no
assurance that its pointer argument means what the manifest says. The pair is
correct if and only if both columns hold, and only the first row of the host's
column is machine-checked.

**And the collision the design names.** If this island were compiled under
Policy O's default and then handed the engine's memory anyway, its first frame
would land at `[65528, 65536)` — inside page 1 of the engine's address space,
which the engine's linker assigned to something and which no declaration
identifies. That is the collision §4 P2 names, and pinning it is the reason
this document exists.

---

## 7. Open items this map creates for the P2 code

Consequences of the contract above that the P2 code must implement. Listed so
the map is not mistaken for a description of shipped behaviour.

**Status against the in-flight implementation.** The P2 encoder/lowering work
is landing in the working tree alongside this document (uncommitted at the time
of writing) and already carries items 1–3 — `WasmMemoryPolicy::Imported` and
`require_memory`, import-shifted `add_function` / `add_global` with an
`ImportAfterDefinition` refusal and a `func_count`-derived element segment, and
`GlobalInit::ImportedGlobal` feeding `WasmStackPolicy::HostBase`. It
independently reached the same ruling as §4.1 on the load-bearing choice: the
stack base arrives as an **imported immutable global** and the stack pointer
stays a defined per-instance global. Items 4–7 are open. Each item below is
therefore written against the pinned baseline; treat 1–3 as "verify, then
close", not as "build".

1. **Memory presence follows the declared policy, not `Alloca` presence.**
   Replace the `uses_stack_frame` gate (`lower.rs:1750-1755`, `lower.rs:1796-1801`)
   with an explicit policy. §1.1 case A is the standing regression: a
   load-through-a-pointer-parameter island must compile and validate.
2. **Import-shifted index spaces, for functions *and* globals.**
   `add_function` returns `self.func_types.len()` (`encode.rs:154-158`) and
   `add_global` returns `self.globals.len()` (`encode.rs:169-173`), both
   assuming zero imports. Imported functions occupy the low function index
   space and imported globals the low global index space; every defined index,
   every `call` / `call_indirect` target, the element segment
   (`encode.rs:276-291`), and the exports (`encode.rs:263-274`) shift with
   them. Getting this wrong is a silent miscompile.
3. **`global.get` initializers**, so the stack pointer can be initialized from
   the imported base (`encode.rs:240-261` is `i*.const`-only today).
4. **A declared maximum stack depth `D`.** For an island whose call graph is
   acyclic, `D` is the maximum over root-to-leaf paths of `Σ frame_size` and is
   computable at lowering. It SHOULD be emitted in the compile evidence
   alongside the existing fields (`lower.rs:1863-1889`). Where `D` is **not**
   computable, Policy I MUST be refused fail-closed. Note that "acyclic" must
   account for the table: `set_func_table` publishes **every** function in the
   module (`lower.rs:1816`), so any island containing a `call_indirect` has, as
   its worst case, the whole module as a possible target set.
5. **An island manifest** binding the policy, `R`, the import list with exact
   signatures, the export name set, and each pointer argument's window mode
   (read / write) and length parameter — the machine-readable form of this
   document, per island.
6. **Static memory-policy conformance:** under Policy I, an island MUST NOT
   reference address constants at all — its only legal addresses come from
   arguments and from the frame base.
7. **Replace the `env` import namespace** with the explicit, versioned
   namespace of §4.3. This is the one place where the landed implementation and
   this document currently disagree; §4.3 records the reasoning and why the
   collision it prevents is the §6 case rather than a hypothetical. The member
   names need no change.

---

## References

- trust `designs/2026-08-24-one-module-every-target.md` §4 (the P2 ladder step
  and the honesty caveat this document is the normative form of), §6 (the
  non-goal restated as "the boundary is the module **plus its declared host
  contract**").
- WebAssembly Core Specification, "Modules" (index spaces, imports precede
  definitions) and "Instructions" (memarg alignment is a hint; non-atomic
  accesses do not trap on misalignment).
- `crates/trust-cg-codegen/tests/wasm_module_validation.rs` — the reference
  validator gate every emitted module passes.
- `crates/trust-cg-verify/src/wasm_memory_proofs.rs` — the memory obligations
  discharged today, and the header's list of what is not.
