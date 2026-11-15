# L02-P6 closure record — Linux AArch64, seventh closure audit (2026-10-16)

**Claim.** Closure-ledger gap L02-P6 (ELF symbol visibility and binding:
hidden, protected and default definitions and references in objects and
shared objects) is CLOSED at `fdcd95468`. The seventh closure audit's auditor
and both skeptics each said CLOSE under the explicit closing standard
(stated fail-closed refusals, trust boundaries and out-of-scope items do not
block; KEEP_PARTIAL needs a new in-scope defect with a reproducer), so
ruling LD-74's first condition holds with no blocking finding to repair.
No repair was needed; the row's last repair is `2942549c5` (sixth audit).

**Boundary.** This is execution evidence on one Linux AArch64 host with GNU
ld 2.42, gold 1.16, LLD 22.1.6 and the glibc 2.39 loader, not a linker or
loader theorem. Darwin and x86-64 hosts were not run. The documented
linker facts that the GCC 13.3 twins reproduce (gold's `LOCAL HIDDEN` TLS
entry when a GCC object refers to a hidden thread-local, gold PIE's load
base for absent weak hidden references, GNU ld's symbolic `R_AARCH64_ABS64`
for data words naming protected symbols, GNU ld and LLD refusing a non-PIE
executable that takes a protected function's address) and the conservative
refusals in LIMITATIONS stay as stated there.

## Evidence record

```text
Task ID / kind / platform: LA-08 / closure audit / Linux AArch64
Parent ledger gaps and acceptance row: L02-P6; L02
Input candidate and implementation commit: fdcd95468 (origin/main); last repair 2942549c5
Compiler, sysroot, dependency pins and backend hash: Trust ae9c2c1d (trustc sha256 b2d4fa4b…, 1.99.0-dev, LLVM 22.1.2); trust-ir dc2b8073; Clean 92bcc897
Required host, prerequisites and dependent task IDs: Linux AArch64 with GNU ld, gold and LLD (TCG_REQUIRE_LLD=1, TCG_REQUIRE_GOLD=1)
Smallest failing input / expected behavior: none failing; hidden names absent from .dynsym, protected data and functions not interposed, hidden references bind PC-relative with no GOT/PLT
Completion condition: LD-74 (1) auditor and all skeptics but at most one CLOSE; here all three CLOSE
Exact commands and fixed denominator: see Commands; floor targets 83 / 21 / 18 at their pinned minimums
Before / after matches, refusals, failures, skips and timeouts: 83/83, 21/21, 18/18, no SKIP line, in each of three independent runs
Negative or mutation control: 32 mutants (auditor 10, coverage skeptic 22), all killed by maintained floor targets
Evidence location and evidence class: this record (committed narrative); logs local provenance only; execution evidence
Remaining limitations and next smallest task: none blocking; see Non-blocking notes
Task status / ledger status / acceptance status: DONE / CLOSED fdcd95468 / L02 OPEN
```

## Commands

Each reviewer worked in its own worktree detached at `fdcd95468`, debug
builds through `scripts/trust_cargo.sh` (Trust `ae9c2c1d`), `-j4`,
`CARGO_INCREMENTAL=0`, through `build-slot`:

```sh
TCG_REQUIRE_LLD=1 TCG_REQUIRE_GOLD=1 bash scripts/trust_cargo.sh test --locked --offline \
  -p trust-cg-codegen --test aarch64_elf_symbol_binding \
  --test e2e_aarch64_elf_relocation_model --test v41_abi_residue_objects -- --show-output
```

## Results

| Reviewer | Floor targets | Further evidence |
| --- | --- | --- |
| Auditor | 83/83, 21/21, 18/18 | An independent probe through the trust-cg CLI (static/pie/pic objects at O0–O3; pic shared objects linked by GNU ld, gold and LLD; `readelf --dyn-syms`/`-r`, PLT checks, LD_PRELOAD interposition): 780 pass; the 12 non-passes are GNU ld's symbolic ABS64 for protected pointer words, which a GCC twin reproduces and which bind locally at run time. The sixth audit's surviving mutants K19 and K20, the admission mutant KA and seven new mutants M1–M7: all killed. |
| Skeptic 1 (coverage) | 83/83, 21/21, 18/18; also `e2e_aarch64_globals_linux` 15/15, `e2e_aarch64_elf_link` 11/11, `e2e_aarch64_elf_tlsie` 13/13 | 22 new mutants (N1–N22) at every visibility and binding decision site: 19 killed by the row's own targets, N11 and N12 by `trust-cg-llvm-import` `symbol_linkage_elf` (29/29 unmutated, including a native LD_PRELOAD row), N22 by `e2e_aarch64_sequences`. None survives the floor. |
| Skeptic 2 (behaviour) | 83/83, 21/21, 18/18 | About 25,000 execution checks of shapes the suite does not hold: dlopen LOCAL/GLOBAL/LAZY/DEEPBIND, LD_PRELOAD and preloaded competitors, threads created before and after dlopen, mixed CG and GCC objects, g++ COMDAT coalescing in both orders, strong replacement of weak and linkonce definitions, merged modules, CG executables importing protected data under -pie and -no-pie, -static, -static-pie, -rdynamic, `-z lazy` with gnu and sysv hash styles, and the CLI's own `--shared` link. No wrong code, fail-open or silent misbehaviour. |

## Identities

- Source `fdcd95468` (origin/main); `Cargo.lock` pins trust-ir
  `dc2b80739ea947557a34b59a10f6c8510e690de7` and Clean
  `92bcc897908b248154ace880a6c518a3d9c09634`.
- trustc `/home/ayates/toolchains/trust-ae9c2c1d/bin/trustc`, 1.99.0-dev
  (`ae9c2c1da`), sha256 `b2d4fa4bb1ce8106539d7c2967f1eb3f3f613293b8c905de586fbb4f5ffa4212`.
- GNU ld 2.42 (`aarch64-linux-gnu-ld.bfd`) sha256 `1e4d3369b76845fa…`;
  gold 1.16 (`aarch64-linux-gnu-ld.gold`) sha256 `91be8ad8ab23070a…`;
  LLD 22.1.6 through the stock Rust 1.97.1 `gcc-ld/ld.lld` wrapper (full
  identities in [the L02-P10 closure record](../2026-10-15-linux-l02p10-closure/README.md),
  same host and binaries); cc (`aarch64-linux-gnu-gcc-13`, 13.3.0) sha256
  `a20520ee21543f24…`.
- Not recorded: the SHA-256 of each reviewer's test executables (each
  worktree's build embeds its own path).

## Non-blocking notes

- The pointer-bearing floor rows point only at hidden targets; data words
  naming default or protected symbols behave correctly by execution but are
  not on the floor (auditor, info).
- Unreferenced hidden or protected declarations (N11, N12) and sequence
  result-length preemption (N22) are killed by other floor targets, not by
  the row's own (skeptic 1, info).
- Two floor targets were red at `fdcd95468` for a test-helper defect outside
  this row: `e2e_aarch64_elf_sections` (25/26) and `e2e_aarch64_sequences`
  (9/14) check admission under the default license policy while the compile
  runs under Permit (the LD-55 class); its repair is a separate task.

The closing criteria rest on the in-tree floor targets above, which anyone
can re-run with the commands given. The reviewers' logs, probes and mutant
diffs are corroborating local provenance only (session scratch directory
`closure-1017/`), not committed evidence.
