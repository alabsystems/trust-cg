# `library/core` at O3 and O0, 2026-09-29: the "compiles COMPLETELY" reading is STALE, on three named reasons, and today's x86 work is not why

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`scripts/trust_ir_cg_census.py --crate core --panic abort` from the Trust checkout
(`ceb94fe99`), driven by the tree-built stage2 `trustc`
(`rustc 1.99.0-dev (3a3e781fe 2026-09-14)`) against the bridge dylib built from
this worktree, with `-Ztrust-ir-cg-args=no-proof-certs` so the proof-promotion gate
does not mask the LOWERING question. `PATH=/usr/bin:$PATH CC=/usr/bin/gcc`, which
this host requires. Unverified frontend lane (`-Ztrust-verify=off`); not a proof
claim.

## Result

| lane | objects | failed roots | distinct reasons | exit |
| --- | ---: | ---: | ---: | ---: |
| O0, `no-proof-certs` | 44 | **14** | 1 | 1 |
| O3, `no-proof-certs` | 1268 | **16** | 3 | 1 |

| reason | O0 | O3 |
| --- | ---: | ---: |
| `[TCG-DYN-REF-IDENTITY]` | 14 | 10 |
| `Rvalue::RawPtr` | 0 | 4 |
| `Rvalue::Ref aggregate source is unsupported ADT` | 0 | 2 |

Zero typed refusals, zero skipped internal functions, zero trapping stubs, zero
harness errors in both lanes.

## This SUPERSEDES the 2026-09-28 reading, which said zero

`reports/perf/2026-09-28-linux-x86-64-core-census/` recorded, for the O0
`no-proof-certs` lane: "exit code 0, zero failed roots, zero typed refusals, zero
trapping stubs … `library/core` compiles **completely**". That is no longer true,
and the cause is identified.

`[TCG-DYN-REF-IDENTITY]` did not exist when that census ran. It was introduced by
`1048f47f3` ("Reconcile local ABI work and document source capability boundaries",
2026-09-29), which is a deliberate FAIL-CLOSED soundness rule:

> unsizing a shared reference to `{self_ty}` has no canonical referent address.
> Materializing a snapshot would change pointer identity and lose interior writes;
> failing closed. Pass an existing thin reference whose referent has real storage.

So the 14 are not a capability lost. They are a class that previously compiled to
something the rule now judges wrong, converted into a refusal. Counting them as a
regression against the 09-28 number would be reading a tightened gate as a defect —
but leaving the 09-28 "compiles completely" claim standing would be worse, because
it is the sentence someone would quote for the objective's Rust clause.

## Today's five x86 changes are NOT the cause, established two ways

1. **Measured.** The O3 census was run twice against ONE dylib, the second with
   every lever of today's work opted out
   (`no-licm-pointer-loads`, `no-x86-slot-forward`, `no-x86-reload-elide`,
   `x86-loop-align-seam-pad=0`). The two gap tables are IDENTICAL — same 16 roots,
   same 3 reasons, same 1268 objects. Retained here as `gap_table-o3.md` and
   `gap_table-o3-levers-off.md`.
2. **By construction.** At O0 the x86 pass manager is EMPTY
   (`OptLevel::O0 => X86PassManager::new()`), so none of those levers runs in the
   O0 lane at all, and the O0 lane is where the `[TCG-DYN-REF-IDENTITY]` count is
   highest.

## What this means for the completion objective

The Rust clause's strongest available statement is now narrower than it was
yesterday: **`library/core` does not fully lower at either optimization level** —
14 roots at O0 and 16 at O3 — on three reasons, all of them MIR-construct lowering
or an explicit soundness refusal, none of them an x86 codegen, ABI or layout gap.

The O3 lane is also the first time this corpus has been censused at O3 at all, and
it is NOT simply O0's list: inlining removes 4 of the `DYN-REF-IDENTITY` cases and
introduces 6 new ones under two reasons O0 never reaches (`Rvalue::RawPtr`,
`Rvalue::Ref aggregate source is unsupported ADT`). An O0-only census therefore
does not bound the O3 surface, which is the level every runtime measurement in this
campaign uses.

Retained: `gap_table-o0.md`, `gap_table-o3.md`, `gap_table-o3-levers-off.md`,
`provenance-o3.json`, `stderr-o3.log.gz`.
