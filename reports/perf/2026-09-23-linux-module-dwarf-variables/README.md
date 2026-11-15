# Whole-module AArch64 DWARF parameters and variables on Linux — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

On clean source `d978e4b393fbf4496a3ef8423eb433d5e2338c67`, on the Linux
AArch64 GNU host, three runs passed with recording wrappers in front of `cc`,
gdb and the LLVM readers:

- `aarch64_elf_dwarf`: `test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out`
- `e2e_aarch64_elf_debugger_linux`: `test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out`
- `pipeline::tests::module_debug_*` (filtered library run, exactly these four
  tests required): `test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 4060 filtered out`

This is the qualifying run for the L03-P4 increment of `46ea8d806` and its
review repair `d978e4b39`. It replaces the run first retained here at
`46ea8d806` (commit `b46de4acf`, recoverable from git history). That run
passed the same three targets. The repair adds a
lines-only module shape and corrects the wording below. A `-g`
preparation keeps each function's register-debug provenance in
`PreparationMetrics::debug_provenance`. The new sibling entry
`Pipeline::compile_module_emission_with_debug_provenance` gives whole-module
objects the `DW_TAG_formal_parameter` and `DW_TAG_variable` DIEs a
single-function object carries. They come from the shared per-function builder,
counted over the encoded instruction list and moved to each function's text
offset. The row stays **PARTIAL**.

## What the run shows

The fixture and a two-argument leaf were prepared with `-g` and emitted as one
module at O0–O3. Two layouts were used: fixture first (offset 0) and leaf
first (fixture at `0xc` at O0 and `0x8` at O1–O3).

- **ELF objects, independent readers.** `llvm-dwarfdump --verify` reports no
  errors for all eight ELF module objects, all eight Mach-O module objects
  and all eight lines-only ELF module objects.
  Each module subprogram's parameter and variable DIEs are present.
  The fixture has `x` plus `acc`, `spill_probe`, `reg_probe`, `tail_const`
  and its frame-slot locals. The leaf has `arg0`, `arg1` and two provenance
  locals. The test's location checker accepts every range of both
  subprograms against `llvm-objdump` disassembly. It checks register writes
  inside a register range, X29 validity for frame-base ranges, and a spill
  range starting right after its store with no overwrite inside it.
  `records/results.json` (`module_dies`, `module_verify`) summarizes the DIEs
  from the tests' own dumps.
- **Lines-only module objects** (the legacy `compile_module_emission`
  entry, whose description the `Compiler`/CLI `-g` path shares). The same
  two functions go through it at O0–O3 in both orders, with the second
  function past offset 0 (leaf at `0x2d4`/`0x238`/`0x228`/`0x228` when
  fixture-first, fixture at `0xc`/`0x8` when leaf-first). The objects pass
  the reader, line-row and symbol checks. They carry both subprograms and
  no `DW_TAG_formal_parameter`, `DW_TAG_variable` or `.debug_loc`
  (`lines_only_module_dies` in `results.json`, re-read by the harness). The
  fixture-first lines-only object also passes the field-by-field
  relocation-target check and the relocation-neutralization mutations, and
  it is the second object in the function-sections test's `-g`-only leg.
  At base `3058c0de4` these were the only module objects the tests
  inspected; `46ea8d806` had replaced them with the provenance-bearing ones.
- **gdb over a linked module executable** (leaf first, so every fixture range
  was moved). Values read in the live session (`records/gdb/*`,
  `module_gdb_values` in `results.json`):

  | Level | `x` at entry | `tail_const` | `acc` at line 22 | `spill_probe` at line 22 | `reg_probe` at its range start |
  | --- | --- | --- | --- | --- | --- |
  | O0 | 7 | 65536 | 10 | 4103 | 65621 |
  | O1 | 7 | 65536 | 0 (stale slot) | 4103 | 65621 |
  | O2 | 7 | 65536 | 0 (stale slot) | 4103 | 65621 |
  | O3 | 7 | 65536 | 0 (stale slot) | `<optimized out>` (no range covers the stop) | 65621 |

  The expected source values are `x = 7`, `tail_const = 65536`, `acc = 10`
  before line 22, `spill_probe = 7 + 4096 = 4103` and `reg_probe = 65621`.
  The test first requires gdb's static `info scope` reading to describe `x`
  from the fixture's entry and to give `reg_probe` a range. It then asserts
  exactly these readings. `x` is 7 at the fixture's first instruction. At
  the body-line stop, `tail_const` is 65536. `spill_probe` is 4103 if one of
  gdb's static ranges covers the stop and `<optimized out>` if none does,
  and at O0 a range must cover it. `acc` is 10 at O0; from O1 only its name
  is checked, although gdb's own range covers the stop, because its slot is
  stale. `reg_probe` is 65621 at the start of its first range only. No other
  address inside or outside a range is probed. The O1/O2 `spill_probe` value
  is required only because gdb's ranges happen to cover the stop there. It
  also checks the backtrace from the C callee through the module's CG frame
  to `main`, the body-line stop, the step and normal exit.
  The single-function leg's four gdb sessions pass unchanged.
- **Parity observation (recorded, not asserted by the tests).** At every level
  the leaf-first module's fixture location lists equal the single-function
  object's once the fixture's text offset is subtracted: 20, 21, 20 and 19
  ranges at O0–O3 (`single_vs_module_parity_observation`).

## Negative controls

- The three test-side checker mutations are refused on the module object's
  fixture subprogram in both layouts, as on the single-function object:
  a register range at its definition, a frame base in the prologue and a
  spill range detached from its store (`location_checker_refuses_ranges_the_machine_code_contradicts`).
- Emitter side: `module_debug_emission_refuses_an_unshifted_range_in_the_second_function`
  takes the second function's description as the builder produces it before
  rebasing. It first requires a range starting below that function; its
  entry-range parameter location is one. It then requires
  `DwarfEmitError::AddressOutOfFunction` naming that function. Emission
  refuses only ranges outside their function's `[low_pc, low_pc + size)`,
  so this is not a general refusal of unshifted ranges. In the leaf-first
  O0 object the fixture is at `[0xc, 0x2e0)`. Left unshifted, `acc`
  `[0x1c, 0x2bc)` and `reg_probe` `[0x208, 0x2d4)` would still lie inside
  it and pass emission, each 12 bytes early. Only the location checker and
  the gdb leg would catch them.
- `elf_debug_with_function_sections_is_refused` pins the named refusal of
  `-g` with function sections on the legacy entry, the new entry and the
  single-function path.
- `module_elf_dwarf_without_provenance_keeps_empty_local_locations` pins
  single-function parity when no provenance is passed: parameters stay
  located, and provenance-backed locals keep their DIEs with empty location
  lists. No blanket refusal was added.
- A development-time mutation for the repair (not retained) routed the
  lines-only shape through the provenance entry. The module test then failed
  on "a lines-only module must describe no parameter or variable".
- Development-time source mutations, run before `46ea8d806` (transcripts not
  retained):
  - With the rebasing shifted by 0, 7 of 12 `aarch64_elf_dwarf` tests and
    the gdb module leg fail. Emission fails closed: "DWARF location-list
    range [0x0, 0x4) of `elf_debug_leaf` lies outside its code range
    [0x2d4, +0xc) (fail-closed)". That refusal comes from a range below
    the function, as described above.
  - With variables built over the prepared rather than the encoded
    instruction list, `module_debug_locations_follow_the_rbit_return_copy_cleanup`
    fails: range `(68, 8)` instead of `(68, 4)`, claiming X2 across the
    return.

## Finding carried into LIMITATIONS.md

From O1 the fixture's stack-slot local `acc` is still described in its frame
slot over the whole frame-pointer range. The optimizer keeps the value in
registers, so gdb reads a stale `0` where the source value is `10`. The
single-function object behaves the same way; that leg already checks only the
name above O0. This run makes the misdescription concrete. It is not fixed
here.

A second pre-existing finding is also in LIMITATIONS.md. A module's line
program is one sequence. In a leaf-first object the leaf's last row (line
34 at `0x4`) therefore also covers the fixture's prologue up to its first
row at `0x28`, and gdb reports the fixture's entry at line 34. The tests
check only where rows start.

## Baseline, method and environment

The unmodified targets passed on this host at `b591ce6e9`, whose DWARF path
and these tests equal the base `3058c0de4`: `aarch64_elf_dwarf`
10/10 and `e2e_aarch64_elf_debugger_linux` 1/1
([integrated floor](../2026-09-23-linux-integrated-gates/README.md)).

`harnesses/qualify-module-dwarf-20260923.py` takes these steps:

1. Refuses a dirty tree.
2. Builds the test binaries with the real tools. `prebuild` is a
   `--no-run` build judged by exit status and RSS receipt.
3. Runs each command through the Linux floor's process-group timeout
   (1,200 s) and 16 GiB RSS ceiling, with scrubbed `TCG_*`/`TRUST_CG_*`/`AY_*`
   and Rust flag variables. The sampled peaks were 2,459 MiB for the
   prebuild, which compiled the changed sources, then 162, 95 and 13 MiB.
4. Requires that no wrapped run recompiled.
5. Checks the source fingerprint before and after (unchanged).

`capture-module-dwarf-tools-20260923.py` forwards exact argument vectors
after checking each real executable's SHA-256. It records stdout, stderr,
exit status and snapshots of the test scratch files. All 334 calls exited 0:
`cc` 8, gdb 12, `llvm-dwarfdump` 159, `llvm-objdump` 56 and `llvm-readelf` 99.
They are packed in `records/calls.tar.gz`, and the file snapshots in
`records/blobs.tar.gz`. `archive-module-dwarf-20260923.py` built this
directory from the run output. The exact test sources are under
`test-source/`.

Tools: GNU gdb 15.1 (Ubuntu 15.1-1ubuntu1~24.04.1), cc = GCC 13.3.0
(`/usr/bin/aarch64-linux-gnu-gcc-13`), and Ubuntu LLVM 18.1.3
`llvm-dwarfdump`/`llvm-objdump`/`llvm-readelf`. Hashes are in
`records/tools.json`. Rust 1.97.1 (stock) was used, with the pinned AY/Clean
package prefix on PATH; no proof tool is exercised by these targets.

For the repair the harness also checks every lines-only module object:
`--verify`, both subprograms, no parameter or variable DIE, and the second
function past offset 0. Two earlier harness runs at `46ea8d806` are not
retained. In both, all
three test runs passed. The first stopped in the harness's own post-check,
whose DIE parser also matched `--debug-info -v` dumps. The second labelled the
`--no-run` build with the test-suite classifier's verdict. Both harness
defects are fixed in the retained script.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-23-linux-module-dwarf-variables
PKG=$HOME/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23
PATH="$PKG/bin:$HOME/.local/bin:$HOME/.cargo/bin:$PATH" python3 -B \
  reports/perf/2026-09-23-linux-module-dwarf-variables/harnesses/qualify-module-dwarf-20260923.py \
  "$PWD" /path/outside/the/tree/new-run-dir
```

## Boundary

This is object and debugger evidence for these fixtures and readers. It is
not a proof that a described location holds its source value, and the stale
`acc` slot above is a known counterexample. The following stay open:

- The `Compiler`/CLI `-g` path and the parallel module emitter still
  describe subprograms and line rows only. The lines-only objects here come
  from `compile_module_emission`, not from the `Compiler` itself, whose
  test covers a single defined function.
- The rustc bridge never requests debug information.
- `-g` with function sections or COMDAT function text is refused.
- The certified relocation inventory refuses DWARF objects.
- No debugger reads Mach-O module objects here; they get the structural
  checks only.

L03-P4 stays PARTIAL, and no L01–L14 row closes.
