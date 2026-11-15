# Cross-backend ABI differential on Linux AArch64 — 2026-09-22

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`benchmarks/abi-xback/run.sh` passes its complete requested domain on the
Linux AArch64 host: **320 MATCH, 0 MISMATCH, 0 declined, 0 skipped** for
seeds 1–40 at O0, O1, O2 and O3 in both directions (LLVM caller → trust-cg
callee, and trust-cg caller → LLVM callee), each compared against the
LLVM × LLVM oracle's exit code. The result-contract self-test passed first.
This is the first dated, host- and toolchain-identified retained run of this
gate at its extended type table (integers through `i128`, the `A16`/`A8`
aggregates, floats, and the five return shapes including the indirect `sret`
buffer); earlier figures in the README are undated counts without identities.

## Identities

- Harness: `benchmarks/abi-xback/{run.sh,gen.py}` at `d77867fe3`, copied under
  `runner-source/`. That commit switches the trust-cg halves from the refused
  `TCG_NO_PROOF_CERTS`/`TCG_REFINE_SOLVER` environment variables to the
  backend's tracked knob option (`-Ztrust-ir-cg-args=no-proof-certs`,
  `-Ztrust-ir-cg-args=refine-solver=0`) and retains each decline's diagnostic.
- Compiler: sealed Trust `a62ae50d8bd2b990650db2cf0dd25019c67c6ed8`
  (`rustc 1.99.0-dev`, `trustc 0.1.0`) at `~/toolchains/trust-a62ae50d`, passed
  with `--driver`, in its explicit unverified frontend lane (`-Ztrust-verify=off`).
- Backend: `librustc_codegen_trust_cg.so` SHA-256
  `8ffdb7f5c39031ca4eaecf23c984046dc3cd57671252125c5e84a8eb04a99ef7`, the
  fresh release build of the [same-day bridge checkpoint](../2026-09-22-linux-bridge-checkpoint/README.md)
  from source whose production crates equal origin/main `4ded2b97c`. Hash
  identified, not archived.
- Host `aarch64-unknown-linux-gnu`, Ubuntu 24.04.4; linker through rustup's
  `gcc-ld/ld.lld` shim and the system gcc 13.3 driver.

```sh
benchmarks/abi-xback/run.sh --selftest
ABI_XBACK_DYLIB=<backend.so> ABI_XBACK_OUT=<new dir> \
  benchmarks/abi-xback/run.sh --driver <trust package>/bin/trustc 1 40 0 1 2 3
python3 scripts/check_evidence_archive.py reports/perf/2026-09-22-linux-abi-xback
```

## Negative control

`records/run1-refused-env/` is the same day's first run of the unmodified
harness with an earlier build of the same source's backend. The pinned Trust
driver refuses `TCG_NO_PROOF_CERTS` as an untracked codegen control, so every
trust-cg half failed to compile: **0 MATCH, 0 MISMATCH, 320 declined**, and the
gate failed as designed rather than reporting zero mismatches over zero
executions. Its stdout and the generated sources are retained; the harness at
that time discarded compiler stderr, which the repaired harness now keeps.

## Boundary

This is execution evidence for the generator's current input domain on one
host. The generator emits no HFA/HVA, `f16`, vector, `bool`, variadic or narrow
return shapes, and register-bank exhaustion is frequent across seeds rather
than guaranteed per seed, so ledger gap L01-P3's closure (an extended domain,
retained runs on Linux and Darwin, TrustIR-level C → CG HFA natives in the
required floors) remains open, as do all L01–L14 rows. The trust-cg halves run
with proof certificates off: this is an ABI differential, not proof evidence.

## Retained files

`records/run2/` holds every generated callee/caller source for the 40 seeds
(the run's `fail/` directory stayed empty, so it has no retained files); `records/run2-stdout.log` is the complete
transcript. `records/run1-refused-env/` and `records/run1-stdout.log` are the
negative control.
