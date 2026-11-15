# Cross-backend ABI differential on Darwin AArch64 — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

`benchmarks/abi-xback/run.sh` passes its complete requested domain on
`aarch64-apple-darwin`: **320 MATCH, 0 MISMATCH, 0 declined, 0 skipped** for
seeds 1–40 at O0, O1, O2 and O3 in both directions (LLVM caller → trust-cg
callee, and trust-cg caller → LLVM callee), each compared against the
LLVM × LLVM oracle's exit code. The result-contract self-test passed first.
This is the first run of the gate on this host; until `404a84bd2` the harness
hard-coded a Linux `gcc-ld` directory and preferred a `.so` backend. It is
correctness evidence for the generator's domain, not a proof and not a
performance measurement.

## Identities

- Source and harness: branch commit `404a84bd2` (the backend's inputs). The
  branch commits after it up to `b2b1cc596` change only documentation, test
  comments and this record, none of them a backend input. The later merges of
  `main` into the branch (`7b8da9967` onward) do change backend inputs, and
  the run was not repeated on a backend built from them: this record is
  evidence about `404a84bd2`, not about the branch head. The harness
  `benchmarks/abi-xback/{run.sh,gen.py}` is copied under `runner-source/`;
  `gen.py` is byte-identical to the
  [2026-09-22 Linux record's](../2026-09-22-linux-abi-xback/README.md), and so
  are the 80 generated sources, so both hosts ran the same 40 signature pairs.
- Compiler: the managed Trust package `trust/9192` (commit
  `321aaeda75478038420d97830f14724c33c8dc39`, `rustc 1.99.0-dev`, `trustc
  0.1.0`, LLVM 22.1.2, host `aarch64-apple-darwin`), passed with `--driver`,
  in its explicit unverified frontend lane (`-Ztrust-verify=off`); `targo
  1.99.0-dev (targo 0.1.0)` from the same package.
- Backend: `librustc_codegen_trust_cg.dylib` SHA-256
  `c80d43c00ea53695ca4689fff3f1a6047754547bb51e47236dc0bb0f440a8e51`,
  release-built from `404a84bd2` with
  `targo --unverified build --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --release --locked`
  (`RUSTC` set to the package `trustc`), and fresh by
  `scripts/bridge_backend.py`. Hash identified, not archived. The trust-cg
  halves run with proof certificates and the refinement solver off
  (`-Ztrust-ir-cg-args=no-proof-certs`, `refine-solver=0`).
- Host: Apple M4 Max, macOS 26.6.2 (`25G83`, Darwin 25.6.0), Xcode 27.0
  (`27A266a`, SDK 27.0), Apple clang 21.0.0 (`clang-2100.3.34.2`). rustc links
  with `cc` (ld64): `trustc --print link-args` names `cc` and no `lld`, so the
  rustup `stable-aarch64-apple-darwin` `gcc-ld` directory the harness puts on
  PATH is unused. The stock lane that builds the rest of the repository is Rust
  1.97.1 (`rustc 1.97.1 (8bab26f4f 2026-07-14)`), which this run does not use.

```sh
benchmarks/abi-xback/run.sh --selftest
ABI_XBACK_OUT=<new dir> \
  benchmarks/abi-xback/run.sh --driver <trust package>/bin/trustc 1 40 0 1 2 3
python3 scripts/check_evidence_archive.py reports/perf/2026-09-27-darwin-abi-xback
```

Started 2026-09-28T05:50:24Z, finished 05:59:21Z (UTC; 2026-09-27 local).

## Negative control

`records/negative-control.patch` makes `AArch64AbiVariant::from_target_triple`
classify Apple triples as AAPCS64 (8-byte stack slots, even-register pairs),
the inverse of the historical Linux bug. The patched source (commit
`639a645d8` plus that one line) was built into its own backend (SHA-256
`6d46d1d1201b6993061437d0ec05694d099767aa467285cc38977ce92e78eeb7`) and run
through the same harness for seeds 1–40 at O2: **18 MATCH, 62 MISMATCH, 0
declined, 0 skipped**, and the gate failed as designed
(`records/negative-control-stdout.log.gz`).

An earlier same-day run with a backend built before the two DarwinPCS repairs
of this change (Trunc to Bool, composite stack slots) also matched 320/320:
the generator emits neither `bool` nor small, packed or homogeneous
composites, so it cannot see them. Those shapes are checked by the Apple clang
twins `e2e_aarch64_aggregate_stack_darwin`, `e2e_aarch64_variadic_darwin` and
`e2e_aarch64_bool_abi_darwin`.

## Boundary

Execution evidence for the generator's current input domain on one host: integer
types through `i128`, `f32`/`f64`, the `A16`/`A8` aggregates and five return
shapes (including the indirect `sret` buffer), with register-bank exhaustion
frequent across seeds rather than guaranteed per seed. The generator emits no
HFA/HVA, `f16`, vector, `bool`, variadic or narrow-return shapes, so ledger gap
`L01-P3`'s domain extension remains open, and `X-DARWIN-P4` and every D/L row
stay open. The rustc bridge lane here is the explicit unverified Trust lane and
makes no Trust-verified compilation claim.

## Retained files

`records/run/` holds every generated callee/caller source for the 40 seeds
(the run's `fail/` directory stayed empty); `records/run-stdout.log.gz` is the
complete transcript. `records/negative-control.patch` and
`records/negative-control-stdout.log.gz` are the negative control.
`inventory.json` lists every file with its SHA-256 and size.
