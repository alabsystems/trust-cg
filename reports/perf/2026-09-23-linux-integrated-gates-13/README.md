# Integrated Linux gates before the fourteenth main push — 2026-09-23

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `fda1c5e5c336bf54d869dcfa6755b38660244fa9`.
That source is origin/main `dbec0925f` plus the aggregate wrong-code branch.
Each of the branch's rounds was checked by an independent verifier; there
were four verifier passes, and every defect they found is fixed in the
branch.

## What the branch fixes

- **`InsertField`/`InsertElement` aliasing (wrong code).** An insert on an
  aggregate used to write into its source's storage. As a result, `swap(s)`
  built from two inserts returned `{s.1, s.1}`. Inserts now get storage of
  their own, and aggregate block parameters own their slots, with a copy on
  each edge. That second change also fixes an aggregate `Load` in a loop
  overwriting the previous iteration's value. Zero-sized values have no
  bytes to copy, and no copy is emitted for them.
- **By-reference composite arguments (wrong code).** AAPCS64 B.4 passes a
  composite over 16 bytes by reference. trust-cg used to pass the address
  of the caller's own storage, so a C callee that wrote its parameter
  changed the caller's value.
  - The adapter now copies each such argument into a caller-owned slot: a
    `Memcpy` inline up to 32 bytes, and a `memcpy` call above that.
  - The copy is skipped only when the source slot is exclusively owned and
    the call is its only use.
  - An invoke with such an argument is split into its own block after the
    copy.
  - An earlier version copied inline and unrolled. It took 47 s and 2 GB to
    compile a 72 KB argument at O2; it now takes 0.02 s and 41 MB.
- **HFA classification (ABI mismatch with GCC).** Members are now counted
  after flattening. An empty-struct member is ignored, and a zero-length
  array member disqualifies the HFA, matching `gcc -O2` shape by shape.
- **Darwin variadic invoke.** It is now refused by name
  (`[TCG-VARARG-ABI]`) instead of passing variadic arguments in registers.

## Linux regression floor

`scripts/check_linux_aarch64.py` passed all **154 required target families
and 954 Rust tests**, including:

- `e2e_aarch64_aggregate_insert_linux` 10/10;
- `e2e_aarch64_large_aggregate_args_linux` 9/9;
- `e2e_aarch64_hfa_zero_sized_linux` 4/4.

The source fingerprint
`e6f76801d309987e3ed13a27b3832eb22a7c54290ca9a61007423d379d27345a` was
identical before and after the run. The run took 707 seconds of target
wall time (20:51:45Z to 21:03:42Z), with a highest sampled resident set of
158 MiB. All four controls were on, and the AY/Clean and dependency
identities did not change.

## Library, CLI and extra suites

- **Library tests:** codegen passed 4,122 with 1 ignored (the pre-existing
  `raw_machir_request_cache_real_exhaustive_campaign`); lower passed 1,889.
- **CLI:** the binary's tests passed 30, `link_options` 20, `output_paths` 8
  and `trust_ir_binary_container` 4.
- **trust-cg-verify:** the CEGIS and proof-suite targets passed.
- **Former race targets:** passed at 16 threads.

## Bridge lane

`scripts/check_linux_aarch64_bridge.py --require-proof-tools` rebuilt the
private backend from this source. Its SHA-256 is
`f698665672c4be549dd6a452374d24c1a5b87a9e3470fe1460a6f472808446b2`.

- `tls_thread_local_linux` passes 2/2.
- `aarch64_c_fnabi_aggregate_linux` fails only at the known
  `aliased_f32_read` O0 `[TCG-PROOF-465]` refusal (L06-P1).

The lane's first failing family is reached before any by-reference copy, so
this lane does not exercise the new copies.

## Recorded, not fixed

- **Compile time with many calls in one block.** It grows faster than
  linearly, which predates this branch: 1,000 scalar calls take 14.2 s at
  O2.
- **Darwin not run.** The Darwin arm is covered only by object and
  classification rows; nothing ran on a Darwin host.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
