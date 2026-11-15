# Linux compiler components with the folded-index proof producer

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Trust-CG source `7d15f0fccae9afea446685d2cafa8d7cee5b5fb0` passes 263 selected component tests, zero failed
or ignored. Its exact Rust sources, manifests and lockfiles stay unchanged.
The candidate includes the shared-prelude pins (TrustIR `d41fa3f8`, Clean library
`61c10a679`), proof-emission-independent dataflow enforcement and sysroot solver
discovery. Builds use stock Rust 1.97.1, two Cargo jobs, one test thread, an
exclusive host resource lease and a 16 GiB zero-grace RSS watchdog.

| Selection | Passed |
| --- | ---: |
| frame-controls | 25 |
| v41-contract-surface | 16 |
| v43-handle-transport | 21 |
| recursive-handle-transport | 1 |
| handle-admission-ownership | 5 |
| wasm-contract-surface | 6 |
| proof-emission-admission | 1 |
| sysroot-solver-discovery | 5 |
| branch-fusion | 68 |
| fcmp-cset-authority-controls | 7 |
| unbound-pair-controls | 7 |
| aarch64_affine_lowering | 39 |
| aarch64_trust_ir_affine_lowering | 38 |
| codegen-affine-bytes | 12 |
| core-constant | 1 |
| request-authority | 7 |
| jit-and-object-refusals | 4 |

The live external driver receives Formal, nondegenerate discharge for all three
source-bound leaf-frame instructions in captured and legacy verification. It
rejects changed-body receipt reuse and changed-body frame credit. A separate
no-cache run has the same formal results and a correctly nonreusable receipt.
The Core constant test emits `CORE_CONSTANT_PROOF_ACCEPTED` with the supported
custom tool prefix. Those are bounded source/body/proof checks, not new production
calling-frame admission. Scalar-cell recognition tests retain their explicit
refusal of production frame authority.

AY release binary SHA-256:
`ffaddeae0d8979a649d74c8a43c8837f62e14004c42673ecc6d7cf25ee7ac3ae`.
Independent Clean binary SHA-256:
`680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc`.
These exact tools are independently qualified in the
[AY release report](https://github.com/alabsystems/ay/blob/ca41f14379a48765cfba494d3662c78457162e13/reports/2026-09-17-folded-index-cli-checkpoint/README.md).
The Clean executable is separately frozen; updating the compiler's Clean library
pin does not replace that external checker.

The first harness passed 63 tests in four selections, then reported 4 passing
and 1 failing opaque-handle test. It had supplied `TCG_BLOCKING_IDENTITY`,
`TCG_EXTERNAL_CLEAN_CHECKER` and `TCG_SOLVE_TRACE` to a Core ownership test that
correctly rejects unkeyed ambient controls before reaching type admission.
The diagnostic uses the unchanged test binary: the original environment
reproduces the failure, while removing those controls passes. An independently
linked probe reports the three unkeyed controls, then an empty list. The first
probe attempt refused ambiguous cached library artifacts before compiling; the
corrected attempt resolves the actual Cargo artifact. No production or test
source was modified, and no assertion or admission guard was weakened.

The corrected harness records each new command's environment. Core and discovery
selections use the qualified tool prefix without unkeyed compiler controls;
proof-discharge selections retain their explicit captured controls. Four earlier
successful selections are explicitly carried forward from identical source and
tool inputs. The failed run and both diagnostic attempts remain in this archive.
The final required selections total 263; diagnostic reruns add no credit.

All 53 artifacts have stored and decoded SHA-256 and length checks.
The backend/native matrix and installation are separate and still pending at
this checkpoint. This does not claim a verified Rust build, complete ABI support,
self-hosting, or closure of Linux L01–L14.
