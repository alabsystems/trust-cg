# Run the Linux regression floor with genuine Trust

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The maintained Linux floor previously invoked Cargo without a way to select
explicit Trust development compilation. The new `--trust-unverified` option
selects PATH's coherent `trustc`/`trustdoc`/`targo` package, binds `RUSTC` and
`RUSTDOC`, and invokes real `targo --unverified`. It records the selected
compiler's sysroot and compiler/build-tool executable hashes before and after
the run. Missing, mixed, unbranded or mismatched packages and compiler wrappers
are refused. This selection and byte inventory are not package authentication
or a claim of Trust-verified compilation.

An actual preflight exposed a second issue: `TCG_EXTERNAL_CLEAN_CHECKER` is a
test-runtime selection, but Trust correctly rejects it as an untracked
compiler control, including on `--print sysroot`. The runner excludes only the
two known Clean runtime selections from compiler probes and builds, then uses
Cargo's target-runner configuration to pass them to the test executable.
Cargo continues to own complete test discovery/execution and library paths.
Other semantic controls are not removed or bypassed. The pure
`core_jit_planning` target retains its existing no-override environment.
AY resolution uses the selected build compiler; Clean resolution still sees
the original runtime selection. All proof acceptance checks remain intact.

## Qualification

Base source: `48df7ac4f926838fd8eb699754e3cee8d65abbc4`. The exact qualified
runner/test source hashes and genuine Trust `ae9c2c1da` tool identities are
retained in the third qualification record. Both complete integration targets
pass through the new command construction and existing bounded execution path:

- `trust-cg-lower/aarch64_variadic_abi`: 3 passed, none failed/ignored/filtered.
- `trust-cg-verify/aarch64_scalar_cell_link`: 7 passed, none failed/ignored/filtered,
  including 24 original C-driver native executions (408 calls, 5,712 checks).

The per-invocation resident-set ceiling was 16 GiB, with observed peaks of
2,361 MiB and 129 MiB. The compiler/build-tool and AY/Clean hashes matched
before and after. Native generated files are retained losslessly in the third
archive. This is focused runner qualification, **not the complete 168-target
floor**, proof-enabled ABI qualification, or whole-system completion.

The final Python floor/x86-runner/host-matrix suite reports 61 discovered,
60 passed and one existing platform-specific skip. All 35 bridge-runner tests
also pass. Real-process fixture tests require the exact unverified invocation,
compiler binding, runtime-only checker delivery, preserved planning isolation,
and rejection of changed executable bytes; negative cases cover missing tools,
mixed packages, stock drivers, mismatched sysroots and compiler wrappers.
These fixtures are unit-test evidence, not compiler qualification.

Earlier failures remain in the archive: the first external qualification
harness stripped Git's leading status space and failed its own preflight
assertion; the second reached the real Trust compiler and exposed the Clean
override rejection. The first Python command named a nonexistent test module;
the corrected and final commands are retained separately.

## Invocation

With the selected Trust package's `bin` directory on PATH and a pinned Clean
runtime selection, run from a clean source checkout:

```sh
python3 -B scripts/check_linux_aarch64.py --trust-unverified \
  --require-clean --require-offline-deps --require-proof-tools \
  --max-rss-gib 16 --jobs 1
```

The complete target inventory, minimum pass counts, features, source/dependency
checks, resource limits and proof-tool checks are unchanged. The same shared
option is exposed by the Linux x86-64 runner; native execution here qualifies
only this AArch64 host. `--list` remains read-only and performs no tool probes.
`manifest.json`, `inventory.json` and `assets.json` bind all retained records,
including every tar member, by hash and size.
