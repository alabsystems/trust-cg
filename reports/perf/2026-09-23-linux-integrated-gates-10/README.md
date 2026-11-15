# Integrated Linux gates before the eleventh main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `cbca2283f67827db367c69bfcd420fd1975ddec7`:
origin/main `4d7e2409a` plus two merged branches and a floor registration.
Every product change was checked by an independent verifier.

## AArch64 CEGIS superoptimizer repairs

The superoptimizer is opt-in, via `--cegis-superopt=<SECS>`.

- **Solver-gated budget** (`debabccd9`). The per-function budget used to
  expire during the structural walk after the last proof finished. That
  discarded proven rewrites and failed the compile as `CegisIncomplete`.
  The budget now admits only solver-backed verifications.
- **Linear walk** (`69ce55479`). The Layer B and C matchers were quadratic;
  128k instructions now take 73 ms, down from 49.5 s. Equivalence with the
  old walk was checked on 1,500 random and 98 real functions.
- **Wrong-code fix, pre-existing** (`f8c60b01d`). Read and def counting
  treated operand 0 of `CmpRR` and `StrRI` as a definition, so a `Movz`
  still read by a compare or a store was deleted. Counts now come from the
  shared operand-role model. The native regression row showed a store and
  a compare reading an unwritten `x2` before the fix.
- **Non-vacuous obligations** (`f8c60b01d`). Obligations are now built from
  the original instruction window and the encoded replacement. The Layer B
  and C obligations used to compare an expression with itself. AY refutes
  20 of 20 corrupted replacements. `DecodeBitMasks` matches GNU objdump on
  all 16,384 encodings.
- **Fail-closed cache replay** (`a99183cff`). Replay used to apply a
  tampered cache entry as recorded. It now requires the rebuilt replacement
  to equal the recorded one; otherwise the entry is treated as stale and the
  function is searched again. The cache root must be owned by the user and
  private: directories 0700, files 0600.

## Test health

The `ty_mcl_fused_parent_loop` and `ty_callback_abi_call_clobber` targets
raced on process-wide callback counters under parallel test threads. Those
counters are now serialized. `full_proof_suite` pins the Comparison
category at exactly 434, the six deliberate families from `e152b164d` and
`cea76ae56`. Each family was checked to be non-degenerate.

## Floor registration

`e2e_cegis_superopt` is now required on the Linux floor (149 targets) and
on the Darwin floor (195 rows, minimum 1351).

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **149 required target families
and 906 Rust tests**, with `e2e_cegis_superopt` at 10/10. The source
fingerprint
`4056cdcd01ebb35b4f679a6862764b4be00f68362621a5204577728ba0c3e744` was
identical before and after the run. The run took 682 seconds of target
wall time (14:31:48Z to 14:43:20Z), with a highest sampled resident set of
266 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change.

## Library, CLI and extra suites

On the same checkout:

- **Library tests:** codegen passed 4,113 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`); lower passed 1,879.
- **trust-cg-cli:** the binary's tests passed 29, `link_options` 16,
  `output_paths` 8 and `trust_ir_binary_container` 4.
- **trust-cg-verify:**
  - `full_proof_suite` 9;
  - `cegis_cache_codec` 21;
  - `cegis_layer_a` 3;
  - `cegis_layer_b` 6;
  - `cegis_pass` 5;
  - `cegis_payload` 11;
  - `cegis_shared_cache` 6;
  - `cegis_stats_trace` 8.
- **Formerly racing targets, at `--test-threads=16`:**
  `ty_callback_abi_call_clobber` 3 and `ty_mcl_fused_parent_loop` 10.

The bridge lane was not run. The CEGIS pass is opt-in, and the rustc
backend does not enable it.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.

`records/run14/` holds the floor output. `records/*.log.gz` hold the
library, CLI, verify and race transcripts.
