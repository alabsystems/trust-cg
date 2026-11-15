# Canonical caller-store replay — 2026-09-19

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The dedicated CG gate passed **6/6 tests**, with **12 accepted kernel replays**
and **33 expected rejections** (23 semantic kernel rejections, seven profile
rejections, three exact-decoding rejections). There were no ignored, measured
or filtered tests. Ten lossless DAG v2 proof terms are retained here. The
separate micro checker reported `micro_checked=false`; no diversity-check
credit is claimed.

The opt-in public `ByteStoreRechecker` reconstructs a Store/Return invocation
against the real pinned Clean ByteV1 vocabulary, quantifying over **all initial
byte maps**. The equality retains the whole final memory, allocation history,
allocation cursor, host state and owner bookkeeping. The tests use explicit
caller allocation rows, including retired owner 7, so initialization must use
fresh owner 8 and return must preserve counter 9. The allocation cursor is 1,
below existing ranges: it cannot stand in for allocation separation.

Coverage includes zero, one, the high-bit word, all-one bits and a mixed-byte
word at two output offsets; an eight-byte store ending at `u64::MAX`; refusal
of a wrapping allocation; forged fetched evaluations and return PCs; erased
writes, changed unrelated bytes, cursor, host, retired history and owner
counter; dead, short, duplicate, inactive-owner and misaligned allocations;
changed retained inputs/alignment; unsupported Copy/reference/module shapes;
and truncated, trailing or empty proof carriers. Counter and allocation-history
corruptions change those fields independently.

## Reproduce and identify

```sh
python3 scripts/check_core_byte_store.py --output /tmp/core-byte-store-replay
```

The directory must be new and outside the checkout. The gate uses locked,
offline dependencies, all tests of the dedicated target, a 30-minute deadline
and a 16-GiB process-group RSS ceiling. Source and Cargo dependency identities
were unchanged during the successful run. The test run took 183.30 seconds;
build plus execution had sampled peak RSS 6001 MiB. This is a stock Rust
1.97.1 development build, not a Trust-verified self-build.

Qualified base: `7fe9dd456cc9e6c92d7555ea5c1969a9cdf3d31a`.
Qualified index tree: `db36aa12dcade42def307e62bed6c5cc4fea99ee`.
TrustIR: `d41fa3f8b7d8e2dba3f6e5b5a0b6217194e2a9f5`.
Clean: `61c10a6795bc342a7a582adae25962bbb28cfbe2`.
The exact input hashes and test executable hash/size are in
qualified-inputs. The
qualified patch `records/third/qualified-source.patch.gz` (removed from the tree) reconstructs the
checked tree from its base. The test executable is identified, not archived;
rebuild it from these inputs. Every retained artifact has stored and, for gzip,
decoded SHA-256 and length in `inventory.json`.

The default (feature-disabled) `trust-cg-verify` library build, root formatting
gate and documentation gate also passed; their complete receipts are retained
under `records/quality/`.

## Attempts and limits

The first exploratory unit selection passed four groups; its logs and receipts
are retained as history, not the final qualification. The dedicated second
run passed five groups and failed a newly added mutation helper: it used
`world[5]` on a five-field constructor. Its exact failed test source is retained.
The correction changes that index to 4; the complete third run then passed.
The gate did not mistake that helper panic for a successful negative control.

This establishes a bounded model replay API, not Rust/reference semantics,
arbitrary functions, native ABI/private-stack refinement, machine execution,
compiler publication or L08/L09 completion. Invocation words, addresses and
allocation records remain concrete. The original Rust writer still needs
faithful Copy/reference reflection and the composed source/Core/LIR/machine
proof. No installed compiler or proof-tool cohort was changed.
