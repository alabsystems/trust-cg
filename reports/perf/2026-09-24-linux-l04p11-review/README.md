# L04-P11 review round — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

An independent verifier reviewed the L04-P11 branch (`ddf6cba83..35ce6a2bd`,
recorded in [2026-09-24-linux-l04p11-switch-calls](../2026-09-24-linux-l04p11-switch-calls/README.md)).
It found no soundness defect and five overclaims, and three findings this
record qualifies the fixes for. The change and its boundary are described in
docs/linux-aarch64-completion.md
(section "L04-P11 … — Review round"). Ledger gap L04-P11 stays OPEN.

| Commit | Content |
| --- | --- |
| `2c600920e` | forms for the emitted zero-source copies (`MOV Wd, WZR`, `MOV Xd, XZR`, typed `MOVWrr`/`MOVXrr` from ZR) and the FEAT_FP16 `FMOV Wd, Hn` / `FMOV Hd, Wn`; refusal of every other unbound copy shape by name; `SubsRI` counted as a deferred row and `AddTprelHi12`/`Lo12` counted and credited |
| `16a023614` | documentation corrections, the review-round section, test comments on the clobber set |

The Linux floor ran on clean `2c600920e`; the harness
(`harnesses/qualify-l04p11-review-20260924.py`, stored verbatim) ran on clean
`16a023614`, which changes only documentation and two comment blocks of
`e2e_aarch64_indirect_call.rs` (the harness re-runs that target).
`records/source.json` has HEAD, tree and an empty
`git status --porcelain --untracked-files=all` before and after.
`harnesses/make-inventory-20260924.py` wrote `inventory.json`. The host,
tools and Cargo environment are those of the first-round record (NVIDIA
Grace, GCC 13.3, binutils 2.42, rustc 1.97.1, AY 0.27.0 and Clean 0.9.0 from
the pinned prefix, `--locked --offline -j 16`, `TCG_*`/`TRUST_CG_*` removed).

## Linux floor

`scripts/check_linux_aarch64.py --jobs 16 --require-clean
--require-offline-deps --require-proof-tools --max-rss-gib 16` on clean
`2c600920e` (2026-09-24 07:46–08:09 UTC): **PASS, 166/166 targets, 1,005
tests**. `e2e_aarch64_switch` 3 (minimum 3), `e2e_aarch64_indirect_call` 2
(minimum 2); the proof-grade targets `jit_fail_closed_proof_policy` 7,
`jit_source_bound_arithmetic` 2, `aarch64_raw_dataflow_boundary` 6 and the
stack-probe target `aarch64_stack_probe_decode` 15. `records/floor/` has the
runner's report and those six transcripts.

## Results (harness at `16a023614`)

| Command | Result |
| --- | --- |
| `cargo test -p trust-cg-verify --lib -- aarch64_value_decode function_verifier::tests coverage_gate proof_database` | `ok. 252 passed; 3989 filtered out` |
| `cargo test -p trust-cg-verify --test aarch64_value_decode_gate --test coverage_gate_tests --test meta_theorems --test proof_gate_strict --test soundness_manifest` | `ok.` 5, 49, 8, 32 and 11 passed |
| `cargo test -p trust-cg-codegen --lib` | `ok. 4147 passed; 0 failed; 1 ignored` |
| `cargo test -p trust-cg-cli --bins --test emit_proofs_flag` | `ok.` 30, 0 and 13 passed |
| `cargo test -p trust-cg-codegen --test e2e_aarch64_switch --test e2e_aarch64_indirect_call` | `ok.` 3 passed (8,685,036 checked calls) and 2 passed (7,008 checks) |
| `scripts/check_fmt.sh` | `check_fmt: OK` |
| `cargo test -p trust-cg-verify --lib -- --skip ay_bridge` | `FAILED. 3947 passed; 3 failed` |

The three library failures (`fsym_summary`'s two AY witness tests and the
x86-64 address-teeth audit report) are among the fourteen that fail at the
unmodified base `f3da1fb17` (first-round record,
`records/baseline/verify_lib_full_f3da1fb17.capture.json`); the first round's
complete library run is not repeated here.

## Mutation controls

Each replaces one exact source span, runs the named tests (which must fail)
and restores the file; the harness refuses to continue unless the tree is
clean again (`records/mutations.json`).

| Mutation | Tests | Result |
| --- | --- | --- |
| `r1` the typed `MOVXrr Xd, ZR` form removed | copy-binding, credit-hook and captured-corpus unit tests | 3 of 3 fail (the captured `MOVXrr X3, XZR` word is filed as `MovXrrFromZr` but binds nothing) |
| `r2` `SubsRI` back to "never selected" | `coverage_gate_tests` ratio and SubsRI rows | 2 of 2 fail |
| `r3` `AddTprelHi12`/`Lo12` back to the exclusion | `coverage_gate_tests` ratio | fails |

## Evidence boundary

These are the repository's own gates and unit tests, the Linux floor and
native controls against GCC on one host. A copy's registered obligation is
proved once, on its form's canonical captured word; only ENC-5 checks each
instruction's own word, and proof certificates do not record that it ran.
The typed zero-source forms are content-identical to the untyped ones. The
TPREL obligations cover the HI12/LO12_NC slice arithmetic of the
linker-patched immediates, not the linker or the ELF TLS ABI. `SubsRI` is
counted, not credited. The W<->H FMOV forms assume FEAT_FP16, whose admission
is the ISA profile's.

## Corrections after the second review — 2026-09-24

A second independent verifier checked the branch at `b8e99d969`. Two
statements above no longer hold:

- `AddTprelHi12`/`AddTprelLo12` are no longer credited (`02b3f18d7`). The
  TLSLE obligations are identities over TP, S and A that name no register,
  word or relocation site, and ENC-5 does not decode the words, so both are
  deferred rows and the function verifier refuses every instance. The `r3`
  result above tested the exclusion, not the credit, and still holds.
- "A copy's registered obligation is proved once, on its form's canonical
  captured word" understates how little that proves: the obligation is an
  identity over that word's transcription (for `MOVXrr`,
  `x7 == 0 | (x7 << 0)`; for the zero-source forms this round added, the
  input-free `0 == 0 | (0 << 0)`). The six forms this round added are names
  that instances bind, not evidence about an instance; the per-instance
  evidence is ENC-5's per-compile decode, which no certificate records.

The same review found ORR (vector) copies credited for the whole opcode.
The repair and its qualification are in
[2026-09-24-linux-l04p11-review2](../2026-09-24-linux-l04p11-review2/README.md).
`inventory.json` was regenerated with the same harness; the runs recorded
here are unchanged.
