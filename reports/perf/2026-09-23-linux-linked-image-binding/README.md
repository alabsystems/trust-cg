# Linked-image byte binding of the arithmetic AOT leaves — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`scripts/check_aarch64_aot_arithmetic.py` (report schema v2) passes its complete
Linux AArch64 denominator with the new linked-image step, on clean source
`f2a53aadff1b95c8e0e03bf6a63c71cae69f5f11` (source fingerprint
`8bc5584d472b6337b2f198a1b65bf02b124eb7067d1f71624364a222ce243707`, identical
before and after). The results are **48/48 cases and 6,912/6,912 native
calls**. **All 48 linked executables are bound to their certified objects**,
and **all 144 linked-image negatives are refused** (three per case). The nine
distinct exported queries are independently re-solved and their original
certificates accepted, and all 27 certificate corruptions are rejected. Status
is `pass`, with no errors and no refusals. The run took 51 seconds
(2026-09-23T00:15:14Z to 00:16:05Z).

This is script- and test-level evidence for audit gap `L11-P3`: after `cc`
links a certified object, the executable still carries its bytes. It is not
a certificate over the linked image. L11-P3 stays PARTIAL, `L02-P5` stays OPEN,
and no L01–L14 row closes.

## What the linked-image step checked

For every case the runner parses the certified object and the linked PIE
itself, using only the Python standard library. It never calls `readelf` or
`objdump`. Every executable is `ET_DYN`, so `calculate` is located by its
`.symtab` symbol, not by a fixed address. The results:

- `calculate` sits at link-time VA `0x958` in all 48 PIEs, inside `.text` and
  one `R-X` `PT_LOAD` whose file offset equals the section-derived offset. It
  is 32 bytes for I32/U32 at O0, 24 bytes for I64/U64 at O0 and 20 bytes at
  O1–O3. Its words equal the object's whole `.text` word for word. In each
  object `calculate` is the one global function filling `.text`, and
  `machine_code_hash` binds that object (the existing sidecar audit).
- Every object carries exactly one relocation, an `R_AARCH64_PREL32` in
  `.rela.eh_frame` against `.text`+0 at the FDE `pc_begin` field. No
  relocation patches `.text`. In each PIE exactly one FDE's `pc_begin`
  resolves to `0x958`, with the object's `pc_range`. Its CIE/FDE bytes equal
  the object's modulo the trailing `DW_CFA_nop` padding GNU ld trims, and the
  `.eh_frame_hdr` search table has exactly one entry for `0x958`, pointing at
  that FDE.
- Each row of `records/report.json.gz` records `image_sha256`, `function_va`,
  `function_file_offset`, `function_size`, the load segment, the object and
  linked function hashes, `object_relocations` (`total` 1, `text` 0) and the
  checked relocation effect.

Each case's three negatives had to be refused as `linked-image-mismatch`.
Each refusal's detail is retained in the row's `linked_image.controls`:

| Negative | Construction | Refusal (all 48 cases) |
| --- | --- | --- |
| `patched-function-word` | the function's last word (`ret`) replaced by `NOP` in a copy of the bound image | `1 of N instruction word(s) … differ …; first at word N-1` |
| `patched-fde-pc-begin` | the linked FDE's `pc_begin` word incremented by 4 | `0 linked FDEs resolve pc_begin to 'calculate' at 0x958` |
| `foreign-object` | the recorded oracle linked with `cc` against `inputs/foreign-calculate.c`, which defines a different `calculate` | `linked 'calculate' is 28 bytes; the certified .text is 20/24/32 bytes` |

The foreign-object negative is refused on its size. The word-by-word
comparison is exercised by the patched-word negative and by the unit tests,
which patch every word position of a minimal ELF fixture.

## Independent cross-check

`harnesses/crosscheck_linked_images.py` asks GNU readelf 2.42
(`/usr/bin/readelf`) and LLVM 18.1.3 `llvm-objdump` the same questions for the
retained run. The answers agree with the runner's records for **48/48 cases**
(`records/readelf-crosscheck.json.gz`):

- `readelf -sW` gives the symbol value and size;
- `readelf -rW` gives the object's one `.rela.eh_frame` `R_AARCH64_PREL32`;
- `readelf --debug-dump=frames` finds the one FDE starting at `0x958`, with
  its `.eh_frame` offset and range;
- `llvm-objdump -d` shows identical instruction words in the object and the
  PIE;
- every foreign PIE's `calculate` has a different size.

This checks the tools' output, not the runner's code.

## Companion test evidence at the same source

- `crates/trust-cg-cli/tests/emit_proofs_flag.rs` passes 13/13
  (`records/cli-emit-proofs-flag-test.log.gz`). The ELF `--emit-proofs`
  identity case now links its certified object with `cc` on aarch64 Linux,
  where a missing `cc` fails it. It locates `_identity` in the PIE by symbol,
  at `0x7d8`. It finds its 4 words equal to the certified `.text`, and runs 6
  calls that return their argument. It compares no `.eh_frame` effect. This
  target is not in the Linux floor, and this record makes no floor claim.
- `scripts/tests/test_aarch64_aot_arithmetic.py` passes 43/43
  (`records/runner-unit-tests.log.gz`). This includes the minimal ELF64
  fixtures and the 48 object/PIE pairs retained by the
  [2026-09-20 run](../2026-09-20-maintained-arithmetic-aot/README.md) at
  `c45c4d3f`. All 48 of those pairs bind. Of the 528 same-level cross-case
  swaps, every swap is refused unless the two certified objects are
  byte-identical, in which case their `machine_code_hash` is identical too.

## Host, tools and identities

- Host: `aarch64-unknown-linux-gnu`, Ubuntu 24.04, Linux `6.17.0-1026-nvidia`,
  NVIDIA Grace (20 cores).
- CLI: `target/release/trust-cg` in the git worktree that produced the commit,
  SHA-256 `b25e467aa61e359f17e77af9613c48e14f26c7610a020a4a1bd8816808d82bfc`,
  `trust-cg` release 0.6.0, stock Rust 1.97.1. It was built cold at `450e714b0` with
  `cargo build --release --locked --offline -j 12 -p trust-cg-cli`
  (`records/release-cli-build.log.gz`) before any file of the increment
  changed. The same command at `f2a53aadf` with a clean tree was a no-op
  (`records/release-cli-rebuild.log.gz`), because the increment changes only
  tests, scripts and documents. As in earlier records, the runner cannot
  itself prove the binary came from the fingerprinted source (owner decision
  OD-13); the worktree HEADs and build logs are the build receipt.
- AY `ec2bf181c384bff0453487b47781fb6d40b959a72c1236bdc760ccc1feee4830` and
  Clean `8d819378eb80696a6a753980bb1722de676f283c4219887f769ac70868f0fff8` come
  from the installed package
  `~/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23`, through the pinned
  `env-override` routes. Executables are not archived.
- Host C compiler `/usr/bin/cc` → `aarch64-linux-gnu-gcc-13` (13.3.0), SHA-256
  `a20520ee21543f243d40636a9181a142c45ecd989de31ab86b99a8ea5ada870d`, with GNU
  ld 2.42.
- Controls: `--require-clean`, `--max-rss-gib 16` (Linux `/proc`), default
  timeouts, solver memory 8,192 MB. `records/launch.json` is the exact
  invocation.

## Boundary

- This is a byte comparison made by the runner and a test, not a certificate
  over the linked image. It is not independently replayed, not signed, and
  not a CG-owned evidence record. It binds one function's words and its one
  unwind entry. It does not check the rest of the image, dynamic relocations,
  symbol resolution by the loader, or run-time memory permissions. CFI bytes
  are compared, not evaluated.
- The binding parses ELF only. A Darwin case that exported and linked would
  fail `linked-image-unsupported`, and no Darwin run exists.
- The runner stays a separate, non-required entry point (OD-12). Its
  denominator, failure-class meanings and nine-query replay are unchanged
  (OD-11).

## Retained files

`records/` is the complete runner output directory. Every retained file whose
name ends in `.gz` is the gzip (mtime 0) of the file the report names without
that suffix. The proof sidecars (`*.cert`, `proofs/**/*.json`) are kept as
they are. Objects are `NAME.o.gz` because the repository ignores `*.o`. Each
case directory holds:

- compile, link, foreign-link and native logs;
- the certified object;
- the bound PIE (`NAME.gz`) and the foreign PIE (`NAME-foreign.gz`);
- the proof sidecars and queries.

`inputs/` also holds the foreign C source and object. `records/launch.json`
records the invocation, pinned environment and build receipt.
`runner-source/` copies the runner and its helpers at `f2a53aadf`. `harnesses/`
holds the cross-check and the script that built this archive.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-linked-image-binding
python3 scripts/check_aarch64_aot_arithmetic.py --trust-cg /path/to/trust-cg --require-clean --max-rss-gib 16 --out /path/outside/source
```

The [2026-09-22 maintained run](../2026-09-22-maintained-arithmetic-aot/README.md)
lists its 48 objects in `inventory.json`, but they were never committed,
because the repository ignores `*.o`. `check_evidence_archive.py` therefore
fails on that directory. This archive stores its objects as `.o.gz` instead.
