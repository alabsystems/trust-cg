# x86 frame-slot value forwarding: h2 reaches LLVM parity, h4 gains 1.1%, and TWO reasons a sound pass can be completely inert (2026-09-29)

This backend had no way to satisfy a frame-slot load from a register that already
holds that slot's contents. Adding one — `trust_cg_opt::x86_slot_forward` — takes
`h2_vec_grow` from 1.0135x LLVM -O3 to **1.0014x** and `h4_vec_dropper` from
1.0503x to **1.0391x**, leaves the other 16 runtime programs BYTE-IDENTICAL, and
shrinks both programs' `main` by 21%.

The more useful half of this report is the two separate reasons the first version
of the pass was sound, correct, fully tested, and fired on absolutely nothing.

## The transform

```text
  (A) store-to-load forward      (B) load-to-load reuse
      mov [slot+d], v                v1 = mov [slot+d]
      ...                            ...
      v2 = mov [slot+d]              v2 = mov [slot+d]
  =>  v2 = mov v                 =>  v2 = mov v1
```

The emitted copy is then forwarded by `X86CopyPropagation` and deleted by
`X86DeadCodeElimination`, so the net effect is one fewer memory operation. A load
whose value is already in its own destination register is deleted outright.

An entry maps `(slot, displacement, width)` to a vreg. Width and register class
must match EXACTLY (a 4-byte store does not satisfy an 8-byte load), the slot must
be a `Fixed` allocation with the access wholly in bounds, and neither the load nor
the instruction that established the entry may carry `proof_origin`.

Two kill rules are the entire aliasing argument:

* a **precisely resolved** store — an allowlisted plain-store opcode whose
  destination resolves to a constant slot range and whose other operands name no
  frame memory — kills the entries of that slot whose bytes it intersects, and
  nothing else;
* **anything else that could write memory clears the whole map**, as does every
  call, pseudo, terminator, atomic and proof-carrying instruction. A SIB store, a
  store through an unresolved register, a memory-destination RMW and `Push` are
  all in this class.

That second rule is why the pass needs no escape analysis: nothing that might name
a frame slot through a pointer is ever allowed to leave an entry standing.

## Why SROA does not already do this

`x86_sroa` promotes a non-escaped slot to vregs outright, which is strictly better
where it applies. It does not apply to these, and the reason is structural: SROA's
recogniser is ROOTED at a materialized slot address and rewrites the accesses
derived from that root, admitting a slot only when EVERY reference to the root is
on its allowlist. A slot whose address is also stored into another slot, or passed
to a call, or used as a SIB base, is out — and a `Vec`'s `(ptr, cap, len)` triple
in these programs is exactly that. Those slots kept every load and store they were
lowered with, including the provably redundant ones.

## FIRST reason the pass was inert: x86 ISel has no direct slot addressing

The first version matched `MemAddr { base: StackSlot(s), disp }`. It was
byte-identical on all 18 programs.

The census the pass carries (`-Ztrust-ir-cg-args=trace-x86-slot-forward`) said why
in one line:

```
h2_vec_grow::main: 0 rewritten | tracked-load opcodes 22 of which 0 resolve to a slot;
                                store opcodes 14 of which 0 resolve
```

22 candidate loads, **zero** resolving. `crates/trust-cg-lower/src/x86_64_isel.rs`
has exactly one non-test site that produces a `StackSlot`-based memory operand, and
it is `Lea root, [StackSlot(s)+0]`. Every frame access in ISel output goes through
such a root as `[root + d]`. Direct `[StackSlot(s)+d]` addressing enters the stream
from only two places, both of them after this pass: the register allocator's spill
code, and `x86_peephole::sib_base_lea_fold` (SIB forms only).

So the fix is a resolver: `build_frame_addresses` grounds a vreg to
`(slot, offset)` over single-def `Lea`/full-width-`MovRR` chains. Soundness is the
argument `X86SpillRemat::FrameAddr` and `x86_licm::resolve_frame_address` already
use — a frame address is a pure function of a body-invariant frame pointer, so a
vreg with exactly ONE static definition holds that same address wherever it is
live. Multi-def vregs are refused (a path-sensitive carrier is not a value), and
`MovRR32` is refused because a 32-bit copy truncates an address.

With the resolver, 20 of h2's 22 candidate loads resolve.

## SECOND reason it was inert: `HAS_SIDE_EFFECTS` is not a memory barrier on x86

Even with addresses resolving, the pass's `is_barrier` cleared its map at almost
every instruction, because it tested `InstFlags::has_side_effects()`.

On x86 that flag is set on **every plain store** (so DCE cannot elide a store whose
value looks dead) and on **every `Cmp`/`Test`**. It means "not freely deletable or
reorderable", not "unknown memory effect". Using it as the barrier test clears the
map at exactly the store the pass is supposed to forward FROM, and again at every
compare. `x86_cse::is_hard_barrier` has the same shape for its own reasons.

The barrier test now asks `crate::effects::x86_inst_effect` whether the instruction
writes memory and routes that through the kill rules, and reserves the flag test
for control flow, `proof_origin` and the named atomic/fence opcodes.

## Block-local was not enough either

With both fixed, the pass forwarded 2 loads in h2 and 1 in h4. The census again:
h2's `main` has **35 blocks** for ~20 candidate loads, so most candidates are the
only access of their slot in their block — and the pair that matters most, a `Vec`
length stored at the end of one block and reloaded at the start of the next,
straddles the boundary.

Adding the restricted cross-block seeding `x86_cse::single_pred_source` already
implements — a block with exactly ONE predecessor reached by a FORWARD edge is
seeded from that predecessor's exit state, snapshotted immediately before its first
PURE control-flow terminator — took it from **2 to 10** forwards in h2 and **1 to
5** in h4. Merge points and back-edges get nothing.

## Results

Both arms built from ONE dylib, toggled by the tracked knob
`-Ztrust-ir-cg-args=no-x86-slot-forward`, compared byte-for-byte:

```
DIFFERS   h2_vec_grow      exit on=66 off=66 llvm=66  MATCH
DIFFERS   h4_vec_dropper   exit on=68 off=68 llvm=68  MATCH
IDENTICAL b1_mispredict h1_vec_push_sum h3_box_leak m1_call_chain m2_call_heavy
IDENTICAL p1_xorshift p2_collatz p3_gcd p4_matmul p5_struct_acc p6_branch_match
IDENTICAL p7_sieve p8_closure_nest v1_saxpy v2_memfill v3_popcount
```

`taskset -c 2`, 200 INTERLEAVED rounds, minimum of each, with BOTH arms carried
twice as byte-identical copies so each has its own noise floor:

| program | arm | min | copy | vs LLVM -O3 |
| --- | --- | ---: | ---: | ---: |
| h2_vec_grow | LLVM -O3 | 12.308 ms | — | 1.0000 |
| | OFF | 12.475 ms | 12.470 ms | 1.0135 / 1.0131 |
| | **ON** | **12.325 ms** | 12.345 ms | **1.0014** / 1.0030 |
| h4_vec_dropper | LLVM -O3 | 7.831 ms | — | 1.0000 |
| | OFF | 8.241 ms | 8.226 ms | 1.0523 / 1.0503 |
| | **ON** | **8.137 ms** | 8.175 ms | **1.0391** / 1.0438 |

h2 gains **1.2%** against a 0.04% (OFF) / 0.16% (ON) copy-to-copy spread and now
matches LLVM. h4 gains **1.1%** against 0.18% / 0.47% spreads, and is still 3.9%
behind.

Both programs' `main` shrank by 21% — h2 285 → 226 instructions, h4 287 → 227.

The clearest single effect is h2's xorshift step, which stopped touching memory at
all. The forwarding removed the reloads, which made the spill store dead, which DCE
removed, after which the state needed no slot:

```
  OFF (15 instructions, 4 memory ops)        ON (12 instructions, 0 memory ops)
    mov -0x68(%rbp),%r10   ; LOAD              mov %r15,%rcx
    mov %r10,%rcx                              shl $0xd,%rcx
    shl $0xd,%rcx                              xor %rcx,%r15
    mov -0x68(%rbp),%r10   ; LOAD              mov %r15,%rcx
    xor %rcx,%r10                              shr $0x7,%rcx
    mov %r10,%rcx                              mov %r15,%rsi
    shr $0x7,%rcx                              xor %rcx,%rsi
    mov %r10,%rsi                              mov %rsi,%rcx
    xor %rcx,%rsi                              shl $0x11,%rcx
    mov %rsi,%rcx                              mov %rsi,%r15
    shl $0x11,%rcx                             xor %rcx,%r15
    xor %rcx,%rsi                              mov %r15,%r14
    mov %rsi,-0x68(%rbp)   ; STORE
    mov -0x68(%rbp),%r10   ; LOAD
    mov %r10,%r15
```

## What this does NOT reach, and it is most of h4's remaining gap

h4 is still 1.039x, and the reason is visible in the same disassembly: the bulk of
its frame traffic is `%r10`/`%r11`, which are the two reserved GPR spill scratches
(`x86_spill_gpr_scratch_regs`). That traffic is materialized by the register
allocator's spill replay, which emits each instruction's reloads immediately in
front of it with no memory of the previous instruction's — so two consecutive
instructions using one spilled vreg each get their own reload of the same slot into
the same scratch. A PRE-RA pass cannot see any of it.

Removing those needs post-RA reload elision, the x86 counterpart of AArch64's
`elide_redundant_spill_slot_reloads`, placed beside the existing
`x86_try_rename_coalesce_copy` — whose own comment records that TV-5 will not
police it, because its documented v1 misses include spill-slot and memory dataflow.
That is a separate capability with a separate soundness argument, and it is the
next item for h4.

## Verification

* 18-program execution differential: 18/18 MATCH on the default build; the A/B
  above additionally checks both arms' exit codes against LLVM on the two programs
  the pass changes.
* Trust clause: the verification-ON corpus test passes.
* Lean-through-Clean 5/5; TY 9/9.
* `trust-cg-opt` library suite green, including 20 tests for this pass: the two
  transforms, the resolver (Lea chain, `MovRR` copy, multi-def refusal, narrow-copy
  refusal), each kill rule in both directions (a DISJOINT store must NOT kill), the
  cross-block policy in both directions (single forward predecessor seeds; a MERGE
  point does not; a call in the predecessor tail exports nothing), and a default-on
  test whose falsifiability arm uses the BUILDER opt-out rather than the
  process-global installer.
* `trust-cg-codegen` library suite green apart from the two pre-existing
  AArch64-host failures.
