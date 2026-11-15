# Integrated Linux gates in Trust development mode before the thirty-first main push — 2026-09-26

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates cover `2256c04f9`: origin/main `65db080a2` (the thirtieth push)
merged with L03-P13 after four verifier rounds, plus its ledger entry. L03-P13
makes two changes:

- The AArch64 ELF relocation inventory lists every exception-handling
  relocation exactly.
- Certified promotion refuses objects that carry exception tables
  (`[TCG-EH-UNPROVED]`). One census decides this, shared with the proof-grade
  JIT and with the emitters' own table predicate.

The environment and runner are the same as in
[gates-32](../2026-09-26-linux-integrated-gates-32/README.md): Trust `ae9c2c1da`
with `--trust-unverified`, Clean from that package, and `TCG_*` passed only
through a Cargo target runner. The baseline is that archive's `run-i44` and
`*-i44` lanes, which are the same code as origin/main `65db080a2`.

## Result: no failure beyond origin/main's own

- **Floor (`records/run-i45/`):** 169 targets and 1,085 passing tests, with the
  new `aarch64_elf_eh_relocation_inventory` passing 13 of 13. The same 8 targets
  and 20 test names fail as on main, and `floor-failed-tests.diff` against
  `run-i44` is empty.
- **Codegen and lower library:** 4,303 passed. The same 7 codegen tests fail as
  on main, and the 6 extra passes are L03-P13's.
- **Other lanes:** CLI, native (LLD and gold required), fsym and local-call each
  fail exactly main's tests (`gates-32`).
- **Green lanes:**
  - symbol binding 67 and relocation model 21, with no `SKIP:`;
  - verifier gates 5/52/8/32/11;
  - opt library 3,622;
  - fsym CLI 20;
  - unwrap ratchet.
- **Linux bridge lane (`records/bridge-i45/`):** `tls_thread_local_linux` passed
  2 of 2 and `unwind_cleanup_linux` 2 of 2. `aarch64_c_fnabi_aggregate_linux`
  fails at the known L06-P1 `[TCG-PROOF-465]` refusal, and the source
  fingerprint was the same at every checkpoint.

`records/gates-i45.status.txt` is the lane-by-lane exit record.

This is regression evidence only. It is not complete Linux qualification, proof
or Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
