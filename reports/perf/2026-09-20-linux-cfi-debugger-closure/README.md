# Linux independent CFI and debugger correspondence — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

On clean source `38a1130d7a0a7304da14db928007e4719c3fa991`, all three independent AArch64 ELF CFI tests
and the Linux debugger correspondence test pass. This satisfies the specific
external-tool and debugger evidence required by gap **L03-P10**. It does not
close L03 or any other L01–L14 completion row.

The CFI differential compiles seven frame fixtures at O0–O3, covering spills,
callee-saved GPRs and D8–D15, unrolled and looped stack probes, large frames and
runtime-sized allocation. It compares independently decoded `llvm-dwarfdump`
CFA/register rules against `llvm-objdump` instruction simulation and the
pipeline's reported layout. Both mutated-object controls reject: a shifted CFA
offset and a D8 save misdescribed as X8. These are synchronous unwind checks;
epilogue windows remain explicitly excluded from asynchronous unwind claims.

At each O0–O3 level, the debugger test links and executes the generated ELF
object, checks its native result, then drives real GDB in batch mode. It verifies
a backtrace from the C callee through the TrustCG frame to `main`, the exact
source call line, a source-line breakpoint and stepping, the constant local,
the stack accumulator at O0, and normal process exit. All four GDB transcripts,
exact arguments, sources, objects and executables are retained.

The tests and their assertions are unchanged. Transparent wrappers forward
the original tool argument vectors, working directories, output and exit
statuses. They retain **33 tool invocations**, including version probes,
with real executable paths/hashes and the input/output file snapshots that the
tests normally delete. File content lives under `records/blobs/<sha256>.gz`;
each call's `result.json` maps its original filenames and modes to those blobs.
The wrappers add no proof authority and do not alter generated objects.
Fixture compilation retains the tests' `DispatchVerifyMode::Off`; this record
qualifies emitted CFI and debugger correspondence, not proof-required admission.

The two targets run serially with locked, offline Cargo, two build jobs, one
test thread, the anchored 16 GiB process-group RSS limit, zero memory grace and
a 1,200-second deadline. `TRUST_CG_LLVM_BIN` selects the recording wrappers
only for this isolated object/debugger qualification. No Core admission or
JIT policy test receives that variable. Source identity is checked before and
after. Tool logs, guard receipts, harnesses and exact test sources are archived.

```sh
python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-linux-cfi-debugger-closure
cargo test --locked --offline -j 2 -p trust-cg-codegen --test aarch64_elf_cfi_differential -- --nocapture --test-threads=1
cargo test --locked --offline -j 2 -p trust-cg-codegen --test e2e_aarch64_elf_debugger_linux -- --nocapture --test-threads=1
```

Reproduction requires a Linux AArch64 GNU host, the pinned stock compiler,
GDB, a C toolchain and the LLVM readers. Both tests are already mandatory in
the 125-family Linux regression inventory; missing tools fail rather than skip.
General exception handling, asynchronous epilogue unwinding, complete debugger
coverage and formally composed source-to-native correctness remain open.
