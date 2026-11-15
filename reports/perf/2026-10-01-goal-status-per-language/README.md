# Which of the four language lanes the panic refusal actually blocks

Date: 2026-10-01 · Host: AMD Ryzen 9 9900X3D, Linux

The standing goal names **Trust, Rust, Lean-through-Clean and TY**. Reporting the state
as "10 of 18 benchmark programs" conflates those lanes, because the refusal that blocks
them lives in ONE of the four paths. Measured per lane:

## Rust — BLOCKED

`crates/rustc-codegen-trust-cg/src/lib.rs` fail-closes a canonical `AssertKind::BoundsCheck`
when `panic_is_abort(ctx.tcx)` or the edge does not unwind. With the harness's
`-Cpanic=abort`, **10 of 18** benchmark programs are `INCOMPLETE — bridge fail-closed`
(b1, h1, h2, h3, h4, p4, p7, v1, v2, v3) and `library/core` at O3 reports **119 failed
roots**, all `[TCG-ASSERT-PANIC]` (1165 objects), against 0 failed / 1284 objects earlier
the same day. The 8 that compile are at geomean **0.9517x LLVM** and **0.9204x gcc**
(`../2026-10-01-linux-gcc-parity-compilable-subset/`).

## Lean-through-Clean — GREEN, measured today

`trust-cg-codegen --test clean_fixture_host_lowering`: **5 passed / 0 failed**, including
`clean_fixture_host_lowering_floor_at_o0` and `..._at_o1`. The target's own doc explains
why it exists — it drives each committed `clean_*.tir` fixture through
`Compiler::compile` (lowering, regalloc, encoding, object emission) at O0 and O1 with no
JIT and no proof publication, so a lowering defect cannot hide behind the JIT's
publication gate. `clean_fixture_profile_probe` also passes.

**This lane does not go through the rustc bridge**, so the bounds-check refusal cannot
reach it.

## TY — NOT AFFECTED by the refusal

`ty` (the TLA+ model checker, `github.com/alabsystems/ty`, updated to `6c27623ee2`)
reaches machine code as, from `tla-trust-cg`'s own module doc:

1. bytecode -> `TrustIr` (via `tla-ir`)
2. `TrustIr` -> trust-codegen `ISel` (via `trust-cg-lower`)
3. `ISel` -> machine code (via `trust-cg-codegen`)

It depends on `trust-cg-codegen`, `trust-cg-ir`, `trust-cg-jit`, `trust-cg-lower` and
`trust-cg-opt` — and on **`rustc-codegen-trust-cg` not at all** (grep count: 0 in both
its workspace manifest and `tla-trust-cg`'s). There is no MIR in its path, so the
refusal, which is a MIR `Assert` admission check, cannot apply.

Two qualifications on TY, both load-bearing:

* It pins trust-cg by git rev (`b6d4e0407`, 2026-09-30 20:20), not by path, so its lane
  exercises that revision rather than this checkout. Local trust-cg changes reach TY only
  when TY bumps that pin.
* Its compile path defaults to **`OptLevel::O1`** (`compile.rs:297`; its own policy
  treats "optimize" as O2/O3 only) and is overwhelmingly AArch64 — 75 mentions to x86's
  1 in `compile.rs`, and no x86 mention in any `tla-trust-cg` test. So the x86 O2/O3
  passes this repo has been tuning are NOT on TY's default path, and TY's x86-64 Linux
  coverage is thin.

## Trust

The bridge carries a Trust-verified differential (`trust_clause`, 23 functions matching
LLVM exactly) — the suite's first verification-ON coverage. Not re-run here.

## What this changes about the remaining work

The blocker is **the Rust frontend path specifically**, not trust-cg's codegen. Two of
the four named lanes are unaffected by it, and one of those (Clean) is verified green on
this host today. So "the goal is blocked" is true of the Rust clause and of the
performance clause for the ten programs that clause excludes — and is NOT true of the
Clean or TY clauses, which should not be reported as blocked.
