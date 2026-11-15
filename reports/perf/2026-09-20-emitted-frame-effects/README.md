# Frame effects from the emitted layout — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Production AArch64 frame calculation now uses exactly the instructions linked
from the validated emitted block layout. Optimizers retain dead instruction
arena entries; counting their calls, register effects and arguments previously
forced a frame even after their blocks stopped being emitted. The actual Rust
masked-index unwind fixture consequently failed required proof promotion at
O2/O3 solely on its unnecessary STP/LDP frame.

A borrowed frame view validates entry/order, unique instruction ownership,
symbolic CFG edges, jump tables and EH references before selecting the emitted
domain. The same view supplies outgoing argument size, callee-save/call scans,
dynamic-allocation and FP dependencies, and zero-storage eligibility. Declared
stack storage, required stack guards and EH metadata remain conservative.
Public compatibility queries retain their whole-arena contract. Live calls,
preserved registers, outgoing stores and every existing frame-bound arithmetic
opcode still retain the required frame. No STP/LDP/CSet proof mapping, bounds
certificate or authority override is added.

## Qualification

1,256 distinct Rust tests pass with zero ignored tests: 173 frame tests, 979
pipeline tests, 87 CFI units, two original-source/native regressions, three
independent LLVM CFI checks, eleven ELF link/runtime tests and the direct
comparison native matrix. The original-source check was also run separately.
The Linux gate's 31 applicable Python tests pass, with one non-Linux-host
control skipped. The new native target is registered in the 125-family required
floor; no new complete-floor result is claimed.

The original canonical frontend module is validated before lowering. At O2/O3
its dead call remains in the arena while the emitted body is exactly AND,
indexed STR and RET with a zero-byte frame. O0/O1 keep their emitted call and
frame. Additional controls exercise live/dead call, GPR/W/FPR and implicit
register effects, dynamic allocation, incoming and outgoing arguments, declared
storage, six arithmetic frame owners and eleven malformed CFG/ownership/EH
cases. Rejection is read-only; independently laid-out blocks still contribute
their effects.

The native original-module regression executes 4,100 masked-store calls at
O0–O3 with sixteen-word arenas, eight placements, boundary/random indices and
SP/X19–X29/D8–D15 checks. A panic stub exits with failure if the masked bounds
unexpectedly invoke it. The existing comparison matrix also passes 125,760
calls. Independent LLVM readers compare CFI/prologue/frame models for seven
functions at all four levels (28 function variants), covering GPR/FPR saves,
spills, large-frame probes and dynamic allocation; both corrupted-CFA and
renamed-FPR mutations are rejected. The eleven ELF controls include shared
library memory/import identity and unwinding across generated code.

The normal uninstrumented genuine Trust backend builds. The twenty-case Rust
corpus admits eighteen cases; O0/O1 unwind still fail on missing frame proofs.
The old installed backend rejects the exact same original Rust input at O2/O3
on STP/LDP; the candidate accepts both with backend checks enabled. Twelve
writer/bounds programs execute 3,084 ABI/arena calls plus eight dynamic-bound
trap-before-store controls. Six reference/static programs preserve their value,
bit-pattern, alignment, identity and relocation checks, including 7,200 address
ABI calls. Independent ELF extraction pins both new masked leaves to the same
12 bytes, `23084092027823f8c0035fd6`, and readelf checks their exact FDE extent,
CFA=SP+0 and return-address column 30.

## Evidence and limits

The first diagnostic/test harness attempts had validator/import/timeout-helper
API errors, which are retained as failures. The initial external CFI attempt
failed because llvm-dwarfdump was missing. The Ubuntu arm64 LLVM 18.1.3 package
was downloaded with APT, checked against its package SHA-256, and unpacked into
a user-local directory. Reader executables, shared libraries, version output
and the failed attempt are recorded. The unchanged CFI tests then pass; no
missing-reader result is counted as success. Large binaries and the downloaded
package are hash identified rather than copied into this archive.

Commands, resource envelopes, source snapshots, actual objects and native
oracles are retained. Heavy jobs ran serially under an anchored 16 GiB
process-group RSS ceiling, zero grace, two Cargo jobs and one test thread.
Source and HEAD stayed fixed during qualification. Formatting, documentation
and archive-integrity checks pass.

The Trust frontend is explicitly unverified; backend checks stay enabled.
Eliminating the unreachable panic path does not establish general Rust
unwinding support. O0/O1 unwind frames, general CSet, precise CMP proof binding,
caller validity and source/native proof composition remain open. All L01–L14
closure obligations remain open. Installation has a separate follow-up record.

```sh
cargo test --locked -p trust-cg-codegen --lib frame:: -- --test-threads=1
cargo test --locked -p trust-cg-codegen --test aarch64_live_frame_effects -- --nocapture --test-threads=1
cargo test --locked -p trust-cg-codegen --test aarch64_elf_cfi_differential -- --nocapture --test-threads=1
cargo test --locked -p trust-cg-codegen --test e2e_aarch64_elf_link -- --test-threads=1
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-emitted-frame-effects
```

The private frontend/native harnesses require the sealed toolchain and helper
identities recorded in preflight. The scripts preserve original machine paths;
these results apply to the candidate and host shown in their records.
