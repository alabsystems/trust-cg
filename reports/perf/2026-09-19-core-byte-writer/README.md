# Complete captured writer kernel replay — 2026-09-19

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Qualified on base `e976052fd4b1fb7984bca44da218e25392aa47de` plus the retained
candidate. This adds an opt-in regression and reproducible gate; production
admission and the Store/Return API are unchanged. TrustIR `25422eb4`, Clean
`55a85e99` and AY `849c19fa` remain pinned.

The fixture is the byte-exact O1 writer from the previous
[frontend capture](../2026-09-19-signature-layouts/README.md), SHA-256
`ba3659953f16521ba6fdf241d3fd2414c1330b5bd88f01cc368cd4dfd35d346c`.
It contains one C function, a mutable-reference tuple parameter, five U64
parameters and 51 instructions. Its actual descriptor is TyId5, size40,
alignment8, offsets0/8/16/24/32. No source instructions or proof annotations
are rewritten by this replay.

The private test model uses the public TrustIR translation rechecker and the
real immutable Clean ByteV1 environment. The candidate is a lambda over initial
bytes containing reflexivity of an independent expected endpoint. Acceptance
requires the kernel to reduce actual initialization, all fetched instructions,
five stores, Return and activation retirement. No axiom, native-authority
conversion, evaluator replacement or checking-limit change is introduced.

Two accepted calls use address80/address88, words `[0, 1, 0x0123456789abcdef,
2^63, 2^64-1]`, live external rows `[80,128)` and `[160,168)`, retired owner7's
row `[16,32)`, cursor512 and host37. Each claim quantifies over **all initial
byte maps** and preserves the complete terminal allocation history, remaining
bytes, cursor and host; active owners are empty and the next owner is9.
The DAGs are 1,853 bytes each. Separate micro-check coverage is **false** for
both; this record credits the kernel checks only.

Five distinct test groups pass: **2 acceptances, 23 refusals**. Twenty kernel
TypeMismatch controls cover six changed store operands, eight false complete
terminal states, four invalid caller-memory descriptions and two retained-proof
input mismatches. Two malformed DAGs fail decoding and one wrapping address
fails bounded source reconstruction. The tests exclude resource exhaustion
from semantic rejection credit. Complete reasons are retained.

`python3 scripts/check_core_byte_writer.py --output /tmp/core-byte-writer-replay`
reproduces the gate with locked/offline dependencies, a 30-minute deadline,
16-GiB process-group RSS ceiling, no grace and exact fixture/source/dependency
identity checks. The qualified gate completed in 163.26s.
Root formatting, documentation inventory/link/census and whitespace gates pass.
No native backend rebuild is needed for this test-only change.

The first retained attempt failed correctly: its test fixture assigned live
rows to inactive owners3/4, which canonical entry forbids. Its source is
retained. The second fixed those input rows to external owner0 and passed one
whole-writer claim. The third added all controls and passed; the fourth verifies
the maintained gate. The first harness omitted JSON from its general inventory;
the separately retained fixture hash identifies that input. Later harnesses
include JSON, and the maintained gate verifies the exact capture digest.

This is concrete IR invocation evidence. Universal input words/addresses,
Rust reference/lifetime validity and frontend adequacy, native memory/private
stack/ABI refinement, and composed compiler admission remain open. The actual
native Rust writer still fails `TCG-PROOF-465` for its frame envelope. **All
L01–L14 remain OPEN.**

`inventory.json` records decoded and stored SHA-256/size for every evidence
artifact; `scripts/check_evidence_archive.py` checks those bytes.
