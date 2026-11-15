# Zero-storage bounds leaves — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The conservative empty-frame policy now admits an exact bounds guard using
X0–X15 for its base/index and an immediate bound in `0..=i32::MAX`. Its late
expansion uses comparison/branch/trap instructions and reserved scratch X16 for
large constants; it touches no SP/FP/LR, preserved register or stack storage.
Malformed shapes, other register classes, reserved scratch inputs, register bounds,
implicit preserved-register dependencies and all prior frame requirements retain
the established frame. The six frame-bound arithmetic forms remain unchanged.
No runtime guard, proof check, red-zone policy or unwinding edge is removed.

## Qualification

All **167 frame tests**, **three frame pipeline tests**, **87 DWARF CFI tests**,
and **979 pipeline tests** pass with zero ignored tests. The canonical bounds
native target again passes all **16 objects / 36 valid calls / 80 invalid calls**
at O0–O3 and now requires the prepared code to contain no frame save/restore pair.
Every invalid call traps with SIGTRAP before its observable store. Frame tests
also check the empty CFI description, actual guard expansion and rejection of
malformed operands, W registers, X16/X17, preserved registers and implicit clobbers.
Root formatting passes. The first pipeline command accidentally selected only
891 tests; all passed, but the harness rejected the incomplete denominator.
The corrected complete 979-test command and the failed attempt are both retained.

The normal genuine Trust backend builds and compiles **eight of twelve** fresh
O0/O1 programs with backend proof enforcement enabled: constant-index writes,
dynamic-index writes, masked-index writes and the five-word writer at both levels.
This advances the preceding canonical-assertion checkpoint's two admitted cases.
All eight actual objects pass **257 native calls each (2,056 total)**, checking
sixteen arena words, eight buffer placements, callee-saved registers and SP.
Both dynamic-index objects additionally trap on four invalid indices each before
modifying shared memory. The backend is uninstrumented; the Rust frontend remains
in its explicit unverified development lane.

The O0 writer's frame-pair proof refusal is resolved. The two dominated cases
still refuse the remaining CSet coverage gap. The two unwinding cases still
refuse frame/CSet coverage and retain the known panic-global type errors. Their
failures are not counted as passing required programs.

## Boundary and reproduction

This changes frame selection for an audited guard shape. It supplies no new
source-to-native theorem, lifetime/reference authority, proof promotion rule or
publication authorization. General framed bodies, broader ABI/runtime semantics
and all L01–L14 requirements remain open. Installation is a separate step.

All heavy commands ran serially under an anchored 16 GiB process-group RSS limit,
zero grace, two build jobs and complete child logs. Source and HEAD stayed fixed
for each qualification. Records include exact commands, source fingerprints,
compiler identities, actual objects, native oracles and their outputs. Large
compiler/test executables are identified by hash instead of copied. The harnesses
retain their original machine-local paths; the source and fixtures are available
in this commit. Verify every retained artifact with:

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-zero-storage-bounds
```
