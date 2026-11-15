# L06-P16 closure record — Linux AArch64, first closure audit (2026-10-16)

**Claim.** Closure-ledger gap L06-P16 (bridge `Fn`-trait call shims read the
`rust-call` argument tuple as one aggregate: `dyn Fn` over a fn item returned
wrong values and `FnOnce` shims trapped or crashed) is CLOSED at
`fdcd95468`. The first closure audit's auditor and both skeptics each said
CLOSE under the explicit closing standard, so ruling LD-74's first condition
holds with no blocking finding to repair. The row's implementation is the
round-10 placement rule (`rust_call_spread`, OD-RUST-CALL-ONE-RULE-20261008)
and its required rows (LD-26), last changed at `4e5ab2354`.

**Boundary.** Execution evidence on one Linux AArch64 host (Trust
`ae9c2c1d`, the Linux bridge lane, rustc's LLVM backend as the oracle).
Darwin and x86-64 were not run here; the Darwin-only family matrix was
ported to Linux and run (below). Dynamic `FnOnce` dispatch, a `Box<dyn Fn>`
blanket call with a cleanup unwind edge at `-O0`/`-O1` under unwind, and
`static`/`const` `dyn Fn` vtables in bridge libraries stay refused (fail
closed, now stated in LIMITATIONS).

## Evidence record

```text
Task ID / kind / platform: LA-09 / closure audit / Linux AArch64
Parent ledger gaps and acceptance row: L06-P16; L06
Input candidate and implementation commit: fdcd95468 (origin/main); row implementation 4e5ab2354
Compiler, sysroot, dependency pins and backend hash: Trust ae9c2c1d (trustc sha256 b2d4fa4b…); trust-ir dc2b8073; Clean 92bcc897; each reviewer built its own bridge backend (path-embedding builds, hashes differ per worktree)
Required host, prerequisites and dependent task IDs: Linux AArch64; LLD and gold for the bridge lane
Smallest failing input / expected behavior: the row's scalar3 reproducer prints 427 (the row recorded 240 before the repair); FnOnce shim crash shapes are refused with [TCG-DYN-FNONCE]
Completion condition: LD-74 (1) auditor and all skeptics but at most one CLOSE; here all three CLOSE
Exact commands and fixed denominator: scripts/check_linux_aarch64_bridge.py --require-proof-tools (required targets) plus the reviewers' differentials
Before / after matches, refusals, failures, skips and timeouts: LD-26 rows 43 + 120 + 264 runs, none refused; rust_call_shims_linux 3/3; L06-P9 step 3,928 cells, 0 wrong; lane red only on L06-P1 aliased_f32_read
Negative or mutation control: the reviewers' independent differentials (about 17,000 matched cells, 0 wrong); the pre-repair reproducer value
Evidence location and evidence class: this record; logs local provenance only; execution evidence
Remaining limitations and next smallest task: LA-12 (the required rows no longer cross a bridge closure body into an LLVM binary)
Task status / ledger status / acceptance status: DONE / CLOSED fdcd95468 / L06 OPEN
```

## Results

| Reviewer | Lane | Independent differential |
| --- | --- | --- |
| Auditor | LD-26 rows: `closure_body_boundary` 43 runs (plus 35 LLVM controls), `inlined_closure_bodies` 120, `rust_call_pointer_calls` 264, `cross_crate_definitions` 16, none refused; L06-P9 step 3,928 cells, 0 wrong; `rust_call_shims_linux` 3/3 (its first Linux run) | The Darwin-only family matrix ported to Linux: 62 rows, 1,012 cells, 0 failures; an Fn/FnMut/FnOnce differential over fn items, fn pointers and closures (by-reference, pair, scalar, `i128`, dirty-padding bool pairs, register exhaustion) across abort and unwind, mixed levels, 16 codegen units and a Rust dylib: 5,382 cells matching LLVM, 0 wrong |
| Skeptic 1 | Same lane result | About 7,100 mixed bridge/LLVM cells in two- and three-crate setups (share-generics on and off, the MIR inliner on either side, TAIT, statics, Drop and generic parents, `track_caller` closures, the earlier rounds' reproducers): no admitted program ran differently from all-LLVM; 6,032 further cells in canonical-provider mode (`-Ztrust-ir-lower`), 0 wrong |
| Skeptic 2 | Same lane result | 4,467 matched cells, 0 wrong, 0 crashes: by-value `FnOnce` environments of 19 shapes, arguments at register exhaustion and on the stack, `Fn`/`FnMut`/`FnOnce`, fn items, fn pointers, `rust-call` items and `Fn` impls; 481 further cells with rustc's exports kept call the bridge's body by symbol, all matching |

Every refusal the reviewers met was named.

## Non-blocking notes

- **Coverage (low, in scope; LA-12).** Since `cc51dbb5c` the bridge provides
  an empty `exported_generic_symbols` under `-Ztrust-verify=off`
  (`withheld_exported_generic_symbols`, LIMITATIONS), the mode the LD-26
  rows use. Every closure instance is in that list, so the rows'
  bridge-library × LLVM-binary cells now link the binary's own copy of each
  closure body and no longer test the crossing where the old wrong code
  lived (across a skeptic's matrices, 0 of 434 such cells import the body). The
  skeptics measured that direction with rustc's exports kept (6,032 and 481
  cells, 0 wrong); the required rows should test it again.
- **Known open item (medium, outside this row).** Where rustc's export list
  stands (default verification, `-Ztrust-ir-lower`), a bridge library can
  list a generic instance over its closure that it never emits (`<Map<Iter<u32>,
  mk_iter::{closure#0}> as Iterator>::max`), and a downstream LLVM binary
  fails to link (loud). LIMITATIONS already states this class as still open
  in the canonical lanes ("an exported body the bridge DROPS").
- The dynamic `FnOnce` refusals were missing from LIMITATIONS; added.

The closing criteria rest on the in-tree bridge lane targets, which anyone
can re-run; the reviewers' differentials and logs are corroborating local
provenance only (session scratch directory `closure-1017/`).
