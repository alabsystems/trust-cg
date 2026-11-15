# Every beat-llvm program is SEVEN roots from compiling in the default lane, and the gate is one domain condition (2026-09-28)

After bumping AY (0.26.0 -> 0.27.0) and Clean (1561 commits), the default
proof-required lane still compiles **0 of 18** programs. That headline has not
moved all day, and it hides the fact that the distance has collapsed. This report
measures the distance instead of the outcome.

## Every program is 7 roots short, and it is the SAME seven

| program | refused roots | sampling route | source-bound |
| --- | ---: | ---: | ---: |
| b1_mispredict, h1..h4, p4_matmul, p7_sieve, v1_saxpy, v2_memfill, v3_popcount | 7 | 7 | 0 |
| m1_call_chain, p1_xorshift, p2_collatz, p3_gcd, p5_struct_acc, p6_branch_match, p8_closure_nest | 7 | 6 | 0 |
| m2_call_heavy | 8 | 6 | 1 |

Seventeen of eighteen are refused on exactly 7 roots; one on 8. Across the whole
corpus there is now exactly **ONE** source-bound replay failure — the route that
started the day at 494 refusals in `core`.

The seven are the same functions in every program, modulo the crate hash — the
Rust runtime startup chain plus the program's own two:

```
std::rt::lang_start::<()>
std::rt::lang_start::{closure#0}
<lang_start::{closure#0} as FnOnce<()>>::call_once
<lang_start::{closure#0} as FnOnce<()>>::call_once::vtable shim
<fn() as FnOnce<()>>::call_once
<program>::main
<program>::done
```

## What those seven actually need — NOT one opcode

`MovRR` is the FIRST uncovered opcode in 6 of the 7, which invites the conclusion
that one evidence decision unblocks every program. **That conclusion is wrong and
is recorded here so it is not drawn again.** A root needs EVERY emitted opcode
covered, and across p1_xorshift's seven the union is **17 distinct opcodes**:

```
7 MovRR   5 MovRR32   3 MovMR   3 Lea   2 ShrRI   2 MovRM   2 AddRR
1 each: XorRR SubRR ShlRI Mul Movzx LeaRip Jcc ImulRRI CmpRI AddRI
```

Crediting `Copy_64 -> MovRR` alone would surface `MovRR32`, then `MovMR`, and so
on. So the sampling route cannot be retired opcode-by-opcode at a useful rate.

## The real gate: the source-bound body DOMAIN, and one condition inside it

Most of those 17 are ordinary integer ALU and shifts — precisely what the
source-bound body theorem's allowlist already admits (`Iadd, Isub, Imul, Band,
Bor, Bxor, Ishl, Ushr, Sshr, ...`). They reach the sampling route only because the
theorem refuses the BODIES that contain them. Tracing p1_xorshift:

| bodies | verdict |
| ---: | --- |
| 8 | `bound rows=N replay=Valid` — the AY/Clean bumps working |
| **6** | **outside the domain: requires no stack slot, EH, stack protector or sret** |
| 2 | outside the domain: `Load` |
| 2 | outside the domain: `GuardDivZero` |
| 2 | outside the domain: `CallIndirect` |
| 2 | not a bounded unconditional chain |
| 1 each | one-result rule, `Trap`, `ExternRef` |

**The stack-slot condition is the single largest exclusion for a real program, just
as it is for `core`** — where it is 4632 occurrences and 100% of that gate's
firings (measured separately, after splitting the gate's message so each refusal
names one condition).

So the correctness clause reduces to a domain question, not an opcode question:
admit bodies that carry a stack slot, then `Load`, then `CallIndirect`/`GuardDivZero`.
That boundary is DELIBERATE and pinned by
`out_of_domain_sources_and_abis_are_unsupported`, which carries an explicit
`("stack slot", ...)` case asserting such a body makes no claim — so moving it is
the theorem owner's decision. The argument a widening would rest on, and the one
gap in it, are recorded in the `ay-bump` report and the `proof-replay` report.

## The stack-slot widening is NOT a one-line change — it is gated on BOTH sides

The source-side frame gate (`admitted_source`) is the one whose message was split
to attribute the 4632; it is the obvious place to widen. It is not sufficient.
`machine_skeleton` carries its OWN unconditional gate over the EMITTED function:

```rust
if !machine.stack_slots.is_empty()
    || !machine.const_pool_entries.is_empty()
    || !machine.jump_tables.is_empty()
    || !machine.eh_info.is_empty()
    || !machine.guard_obligations.is_empty()
    || machine.max_outgoing_call_bytes != 0
{
    return Err(function("stack slots, constant pool, jump tables, EH, guard                          obligations or an outgoing call area"));
}
```

So removing the source-side condition alone moves the refusal from one gate to the
other and admits nothing. That is worth stating because an experiment that dropped
only the source condition was run earlier in the day and reverted when it broke
`out_of_domain_sources_and_abis_are_unsupported`; had the test not caught it, the
change would have been INERT rather than wrong.

Admitting slot-carrying bodies therefore requires the machine side to model the
frame — the prologue/epilogue the slot forces, and `[StackSlot + disp]` addressing
in the skeleton and the row allowlist (whose `Lea`/`LeaSib` arms today require a
`gpr64` base precisely so a `StackSlot` operand cannot form). That is a theorem
extension of real size, not a condition to delete, and it is the honest scope of
the 4632-exclusion item.

## UPDATE after the stack-slot widening: priced per condition, and it is not one more slice

The frame gate's stack-slot condition was then removed (both sides; see the commit
"admit a stack-slot TABLE"), which took that exclusion from 4632 census
occurrences to ZERO. Re-tracing `p1_xorshift` shows what its seven roots need now:

| bodies | verdict |
| ---: | --- |
| 8 | `replay=Valid` |
| **4** | `StackAddr { slot: 0 }` — takes a slot's ADDRESS |
| 2 | `B1/I8/I16/I32/I64 (pointer)` parameter types |
| 2 | `Load` |
| 2 | `GuardDivZero` |
| 2 | `CallIndirect` |
| 2 | not a bounded unconditional chain |
| 1 | exactly-one-result rule |
| 1 | `Trap` not following a diverging call |
| 1 | `ExternRef` |

The six former stack-slot refusals became four `StackAddr` refusals — those bodies
really do take a frame address, which the instruction domain refuses correctly.

**That is the honest pricing: EIGHT distinct conditions, spread across seven
bodies, all of which must pass for ONE program to compile.** So the remaining work
is not "the next slice" — it is making the body theorem general enough for the Rust
runtime startup chain: frame addresses, loads, guard carriers, indirect calls,
non-linear control flow, traps and external symbol references. Some are individually
tractable (an `ExternRef` is an unknown-but-fixed address that both sides name
identically, so it models as one free constant); `StackAddr`, `Load` and
`CallIndirect` are not, because they need memory and call semantics in a theorem
that today has neither.

This is why the census root count and the per-program distance did not move when
the largest exclusion was removed: a root promotes only when its body passes EVERY
condition, and clearing one of eight changes no body's verdict from refused to
admitted.

**The alternative route remains the cheaper one by far.** If the register-copy
obligation is credited structurally (XD-01), the reconstructed route covers those
opcodes without the body theorem needing to admit any of these constructs at all.
The body theorem is the only route that can carry a copy today, but it is not the
only route that COULD.

## Why the headline did not move while the distance collapsed

`0/18` is a threshold measurement: a binary needs EVERY root. The day's work took
`core` from 3363 refused roots to 2881 and the source-bound route from 494 to 12,
which is why the per-program distance is now 7 rather than "many" — but 7 > 0, so
coverage stays at 0.0%. Both numbers are true and they answer different questions;
quoting only the coverage hides a 97.6% reduction in one route and an 8.2x increase
in emitted objects.

## Provenance

Bridge rebuilt from this tree after merging origin/main; stage2
`trustc 1.99.0-dev (3a3e781fe 2026-09-14)`; `ay 0.27.0+build.11385`;
Clean `e75141b7b` with `carcara-verify`; `-Ztrust-verify=off`, `--edition 2021`,
`--crate-type bin`, `-Cpanic=abort -Copt-level=3`,
`PATH=/usr/bin:$PATH CC=/usr/bin/gcc`. The 0/18 figure is a
`benchmarks/beat-llvm/run.py` run with no `--bridge-cg-arg`, 18 INCOMPLETE and
**0 MISMATCH**.
