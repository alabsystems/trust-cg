# Wide scalar-pair arguments — 2026-09-27

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

On Linux AArch64, Rust ABI arguments containing a 128-bit scalar in rustc's
`PassMode::Pair` now travel as two scalar values with their original widths.
The existing target classifier places each 128-bit value in a register pair
or a 16-byte-aligned stack slot. Keeping that value intact preserves the
required even-register start and correct placement when registers run out.
The bridge checks the classes, widths and offsets against rustc's FnAbi.

The declaration, entry stores and call-site loads use the same plan and exact
layout. Returns, other targets, C ABI and closure parameter exclusions retain
their existing decisions. Half-precision and 128-bit floating values still have
no carrier here. No proof switch or required gate was weakened.

Qualification uses base `e985b634b85ef530e1a643c18256116dbf4b9aae`, genuine Trust `ae9c2c1da`, TrustIR
`dcc5b9a3ce02827dca6c3b0ae556d09ca338fdad`, and eight maintained source hashes.
Backend SHA-256: `ce2ae339edaff0938a40e38e534e067f81077bbe1623d44e6d868da53005f45a`. Native diagnostics disable frontend
verification and codegen proof certificates. The required proof test is
measured separately; no installed compiler is promoted.

## Validation

- Genuine Targo all-targets check and backend build pass. The ABI target lists
  exactly 24 tests; the new maintained test executes and passes.
- The original baseline has four CG argument-ABI refusals at O0/O3; both LLVM
  baselines run 2,048 checks. The repaired original corpus passes 16,384 checks
  across LLVM/CG O0–O3.
- The expanded corpus passes 217,088 checks at O0–O3: zero through nine preceding
  integer arguments, register/stack splits, signed optional values, wide and
  mixed-width integer tuples, both LLVM/CG call directions, and an indirect
  Rust function-pointer call. Both maintained corpora total 233,472 checks.
- Twenty-one unchanged regressions pass 5,109,644 native checks, including 320
  LLVM-only checks whose corresponding CG store/cleanup cases remain refused.
  Existing f16-value and over-aligned zero-sized Drop refusal controls pass.
  New and unchanged suites total 5,343,116 native checks.
- Root formatting passes. Private formatting adds zero differences beyond
  59 existing library blocks; changed test
  and fixture files pass in full.
- Prototype and maintained builds each execute the original full-core input.
  The maintained run exits 1 with
  13 failed roots and 44
  emitted objects. Exactly `Option<u128>::unwrap_unchecked` and `exp_u128` leave
  the published 15-root failure list. No new roots or remaining failure-message
  changes are observed.
- The unchanged proof-required ABI test exits 101,
  passed=false, TCG-PROOF-465=true.
  Missing instruction proofs remain separate from the native results.

## Scope and reproduction

The first prototype all-targets check rejected a string comparison against the
compiler's `Os` enum. The corrected check uses `Os::Linux`; both attempts and
the original failing ABI baseline are retained. The maintained
`wide_scalar_pair_arguments::` test uses a support module and four fixtures.
Exact test inventory, markers, compiler/backend/source identities, commands,
logs, objects and executables are archived and hash checked. Rebuildable
backend/runtime archives are excluded with their identities. Full core,
instruction proofs and product completion gates remain open.

## Incoming main integration

Before publication, remote main advanced to `ba27f8da6c0c2460dfc7c566976a77cba22b5cec`.
Its only net change is `scripts/tests/test_linux_aarch64_gate.py`: resolved
fixture paths and Linux-only execution of two Trust-mode fixtures. Every
compiler, dependency, test-corpus and backend input used above is unchanged;
the integration receipt checks the candidate hashes and backend bytes. The
66-test Python suite reports 65 passes and one pre-existing non-Linux-only
skip. The two changed Trust-mode tests also execute independently: two pass,
zero skipped. The initial integration audit rejected the existing platform
skip; both the failure and the explicit follow-up are archived. No second
native or full-core run is claimed for this source-equivalent integration.
