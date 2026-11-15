# Writer replay for all canonical input words — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Qualified on base `5a2b82d8644fd2e502dceddb4b4ad34afe46f504` plus the retained
candidate. Production compiler admission and dependency pins are unchanged:
TrustIR `25422eb4`, Clean `55a85e99`, AY `849c19fa`.

The [previous checkpoint](../2026-09-19-core-byte-writer/README.md) replayed
all 51 instructions of the captured Rust writer for concrete input words and
arbitrary initial bytes. This increment also checks both complete executions
at addresses 80 and 88 for **every combination of five canonical 64-bit words**,
independently quantified, and **every initial byte map**. Each word is a Nat
with an explicit `Nat.lt word 2^64` premise. No execution result is assumed.

The independently reconstructed specification initializes the exact retained
O1 module and requires its complete terminal world to equal five successive
eight-byte writes at `address + 8*i`. It preserves unrelated bytes, the live
external allocation rows `[80,128)` / `[160,168)`, retired owner 7's row
`[16,32)`, cursor 512 and host 37. Return pops the fresh activation and retains
owner counter 9. Addresses and allocation rows remain concrete. Fixture SHA-256:
`ba3659953f16521ba6fdf241d3fd2414c1330b5bd88f01cc368cd4dfd35d346c`.

The test-only untrusted assembler fetches every actual instruction through
TrustIR's Catalog and composes all 51 steps. Copy uses equality congruence on
its real canonical-carrier guard. An explicit U64 eight-byte codec supplies
the actual context/layout, range, encode/decode and access premises to the
existing checked generic Store rules. Real entry and Return rules preserve
the complete world. There is no evaluator replacement, new axiom, declaration
injection, proof-check bypass or conversion to compiler authority. The kernel
independently checks the closed DAG against the reconstructed proposition.

The maintained gate passes **6 test groups**, containing **4 acceptances and
27 refusals**. Two acceptances have concrete words; two universally quantify
over all five words. The previous 23 negative controls remain. Four new kernel
TypeMismatch controls reject reuse at the other address, a changed final store,
a bound proof for the wrong word, and an extra write at byte 200. Resource
exhaustion is excluded from rejection credit. Positive DAGs and all four
rejected symbolic candidates are retained with checker records. The separate
micro-check coverage flag is reported per proof and supplies no extra credit.

Reproduce from the root with the pinned toolchain on PATH:

```sh
python3 scripts/check_core_byte_writer.py --output /tmp/core-byte-writer-replay
```

The gate uses locked/offline dependencies, a 30-minute deadline and 16-GiB
process-group RSS ceiling with no grace. Kernel settings remain 5,000,000
heartbeats and 100,000 cache entries. The finite assembler discovery allowance
is 128 lookups for the 51-instruction body (node/site lookups plus entry metadata),
not a proof admission setting. Gate runtime: 402.31 seconds. Source,
fixture and dependency identities are held through the run. Root formatting,
documentation and whitespace gates pass.

Retained attempts: first failed Rust compilation because the catalog PC uses
usize. Second was cancelled before completion after inspection found exact
codec-layout endpoint mismatches. Third stopped at the assembler's former 32
lookup budget before kernel replay. Fourth accepted the initial universal-word
claim (164,640-byte DAG). Fifth qualifies the maintained gate and all controls.
No failed or cancelled attempt is counted as a proof.

This is a whole TrustIR invocation theorem for explicit caller worlds. It is
not Rust frontend adequacy, arbitrary address/allocation validity, Rust
reference/lifetime semantics, native private-stack/ABI refinement or compiler
publication. The actual native writer still fails its frame/opcode proof check.
**All L01–L14 remain OPEN.** Stored/decoded artifact hashes and sizes are checked
by `scripts/check_evidence_archive.py` against `inventory.json`.
