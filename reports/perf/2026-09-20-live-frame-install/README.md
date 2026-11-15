# Installed emitted-layout frame repair — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The active local compiler package now uses clean source `47c6c194ec1f62b5b12ed254a1ef8a4a1fad30d5`. Production
frame effects follow the validated emitted layout, so an optimized masked-index
Rust store no longer receives a frame from its removed panic block. The O2/O3
program now passes backend admission. See the
[source and native qualification](../2026-09-20-emitted-frame-effects/README.md).

## Package and checks

- Package: `/home/ayates/.local/lib/trust-cg/47c6c194-ay43f133d3-cleaned2a80d1`.
- CLI SHA-256: `53de4798aba955d6384a98b90d81221a7a12be04b20f37c16f1a8f70bcfa5a84`; stock Rust development build, 51.92 seconds.
- Genuine Trust private backend SHA-256: `eb02cff4d1dfb93ae9827b0d60d278a1625095a4dda853622aa29cd574af8c1c`.
- AY `93fe897aea3b4ad5d2ff50c9729c8aa097bfcf36dcbf581e21c4515bbeaf400b`
  and Clean `680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc`
  are unchanged.
- All **234 preflight commands** pass before activation. At O0–O3 the existing
  checks cover return42, twenty select functions, twenty diamond functions,
  48 arithmetic proof exports and 6,912 native arithmetic calls. Select and
  diamond each execute 15,360 comparisons. Existing arithmetic proof owners
  remain intact.
- The candidate backend freshly compiles and executes the twelve qualified
  fixed-array/writer cases (ten O0/O1 cases and two O2/O3 masked-unwind cases) with exact object equality: 3,084
  arena/ABI calls, sixteen arena words, eight placements and eight invalid-index
  traps before any shared-memory store. The dominated-bound
  cases check that large out-of-range indices neither write nor trap. The
  masked-unwind cases check wrapping masked indices and execute no panic.
  Their compile command retains the original qualified source path so unused
  panic source-location data also match exactly.
- Six O0/O1 aligned-reference, scalar/array-reference and static-data cases
  also compile and execute before activation. Every emitted object matches its
  qualified counterpart. The eighteen address-return variants pass 7,200 ABI
  calls checking values, float bits, Unicode, array contents, source alignment
  and allocation identity. Static oracles check packed pointers, function calls,
  self-cycles and mutable cells. Earlier object-level CFI checks are retained in
  the linked qualification; this installation repeats compilation and native
  execution without claiming a new CFI suite.

The launcher at `~/.local/bin/trust-cg` selects this package and adds its tool
prefix to PATH. AY/Clean links use the same package. No proof-policy environment
override is injected; previous packages remain. The included backend is selected
explicitly with Trust's `-Zcodegen-backend`; the qualified Rust lane uses
`-Ztrust-verify=off` while backend proof enforcement stays enabled.

An activated-launcher smoke checks all tool identities, then performs an O3
proof export, native link and execution through the installed command. Source,
CLI and staged backend/tool identities are checked before activation. The
resource envelope remains anchored at 16 GiB RSS, zero grace, two build jobs and
serial preflight commands. Complete logs, proof packets, objects, oracles and
source/tool identities are retained; large binaries are identified by hash.

Unwinding, general CSet, precise CMP proof binding, reference validity and broader
source/native proof composition remain open. This is a local development
installation, not a signed release, verified frontend or verified self-host.
All L01–L14 remain OPEN. No complete floor or performance result is claimed.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-live-frame-install
```
