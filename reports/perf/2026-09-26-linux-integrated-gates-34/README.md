# Integrated Linux gates in Trust development mode before the thirty-second main push — 2026-09-26

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates cover `a7395e619`, which is origin/main `2a5373470` merged with
L13-P7 after four verifier rounds, plus its ledger entry. L13-P7 adds:

- the Linux fuzz lane `scripts/run_linux_fuzz_lane.py`;
- the floor's fuzz rows, which bring the floor to 203 targets;
- the shared Cargo/Targo config audit;
- fixes for the leak and the Mach-O parser.

They also cover the one-line follow-up `aacc51c7f`. The runner and environment
are the same as in [gates-32](../2026-09-26-linux-integrated-gates-32/README.md).
The baseline is gates-33's `run-i45`, the same code as origin/main
`2a5373470`.

## A failure the gate caught

`records/run-i46/` failed ten `trust-cg-llvm-import` targets without running
any test: `tests/common/mod.rs:187` failed to compile. L13-P7's Mach-O parser
repair made `ParsedSymbol::name` a shared `SymbolName`, and the llvm-import
helper still collected it into a `BTreeSet<String>`. That helper is compiled
only with `--features driver`, and no earlier check built it. `aacc51c7f`
converts the name to an owned string. After the fix, `cargo check --workspace
--all-features --all-targets` is clean. `records/llvm-import-i46b.log` re-runs
all twelve llvm-import floor targets at `aacc51c7f` in the same Trust
environment. Their pass counts equal main's exactly (2, 2, 6, 1, 1, 1, 9, 2, 1,
5, 4, 5). The only failure, `explicit_unknown_aarch64_target_still_fails_closed_for_stack_protector`,
is main's own.

## Result at `a7395e619` plus `aacc51c7f`: no failure beyond origin/main's

- **Floor (`records/run-i46/`):** 203 targets, including the 35 fuzz rows, each
  with its case-count probe line.
  - Apart from the ten llvm-import build failures above, it fails the same 20
    test names as main (`floor-failed-tests.diff` against `run-i45` is empty).
- **Same failures as main:** codegen and lower library 7, CLI 1, native 3, fsym
  1, local-call 1.
- **Green:**
  - symbol binding 67 and relocation model 21, with no `SKIP:`;
  - verifier gates 5/52/8/32/11;
  - opt 3,622;
  - fsym CLI 20;
  - unwrap ratchet.
- **Linux bridge lane (`records/bridge-i46/`):** the known L06-P1 refusal. TLS
  and unwind pass 2/2 each, and the source fingerprint was stable.

This is regression evidence only. It is not complete Linux qualification, proof
or Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
