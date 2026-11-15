# Whole writer replay for arbitrary caller memory — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Qualified on base `78dc630711b8bc0e0a9969e0dfd4841be37f5a5d` plus the retained
candidate. This increment changes integration proof assembly and its maintained
gate. Production compiler code and pins are unchanged: TrustIR `25422eb4`,
Clean `55a85e99`, AY `849c19fa`.

The kernel now checks the complete captured 51-instruction writer for arbitrary
positive addresses, five independent canonical U64 words, allocation histories,
initial byte maps, allocation cursors and host states. The earlier
[universal-word proof](../2026-09-20-core-byte-writer-symbolic/README.md) fixed
addresses and the caller world. The new theorem has explicit premises for the
actual ByteV1 entry ownership check, five canonical address bounds, five word
bounds and five actual eight-byte live/aligned access checks. It does not infer
allocation authority from a Rust reference type.

The reconstructed claim initializes the original module, runs all 51 fetched
instructions and compares the complete terminal state against five successive
eight-byte writes at `address + 8*i`. It retains the original cursor and host,
an empty active-owner list and the successor of the actual fresh root owner.
Root retirement is explicit in the expected allocation state. A generic theorem
that retirement preserves every original allocation row is not claimed here;
the two concrete applications independently require their original row lists.
The byte map contains exactly the five writes, including all untouched bytes.

The unchanged O1 frontend fixture has SHA-256
`ba3659953f16521ba6fdf241d3fd2414c1330b5bd88f01cc368cd4dfd35d346c`.
The untrusted test assembler uses actual reflected instructions, Catalog fetches,
checked initialization, Copy/Cast/Add/Store rules and Return. Canonical pointer
bounds, integer bounds, cast carrier guards, store layout and live access are
supplied to the real existing rules. The independent rechecker reconstructs
its own complete proposition from the retained module and checks the serialized
DAG in the immutable Clean ByteV1 environment. No axioms, environment additions,
evaluator replacements or compiler admission changes are introduced.

The same universal proof is applied to two genuinely different concrete callers:

- Address 80, live output row `[80,128)`, retired owner 7's row `[16,32)`,
  another live row `[160,168)`, cursor 512, host 37 and final owner counter 9.
- Address `18446744073709551576` (`u64::MAX - 39`), a 40-byte output row
  ending at the last 64-bit byte address, a different row order, retired owner
  41, cursor 0, host 123 and final owner counter 43. The five words differ too.

Both applications continue to quantify over every initial byte map. Their
bounds use checked standard Nat arithmetic; the actual entry/access predicates
must reduce successfully in the kernel. A retired or short output allocation
therefore cannot instantiate the theorem.

The maintained gate passes **7 groups, 7 accepted DAGs and 36 refusals**.
Nine new controls reject a bound for the wrong address, a bound for the wrong
word, access evidence for the wrong store, a changed terminal host, an extra
write, a changed fetched Store value, a changed fetched offset, and concrete
retired/short allocations. All nine require kernel TypeMismatch, not a resource
failure. Together with the previous controls, 33 refusals are kernel type
mismatches, two are malformed DAG encodings and one is a wrapping source input.
All accepted terms report `micro_checked: false`; this record claims kernel
acceptance only. All seven positive DAGs and rejected symbolic/caller candidates
are retained with their exact rejection records.

Reproduce with the pinned root toolchain on PATH:

```sh
python3 scripts/check_core_byte_writer.py --output /tmp/core-byte-writer-replay
```

The full maintained gate took 972.47 seconds, with peak process-group RSS
1737 MiB. It retains a 30-minute deadline and 16-GiB ceiling with no
grace. Kernel limits remain 5,000,000 heartbeats and 100,000 cache entries;
assembler discovery is bounded at 128 lookups. Source, HEAD, fixture and
resolved dependency identities remain unchanged through qualification. Root
formatting, documentation and whitespace checks pass.

All attempts are retained. First failed Rust compilation on a live borrow of
an expression argument vector; dropping that temporary before moving the
expression fixed it. Second accepted the initial universal theorem in 234.23
seconds of kernel test execution. Third failed compilation because a test
parameter shadowed a helper function; renaming the helper fixed it. Fourth
accepted all three new proofs and nine controls in 705.19 seconds of test
execution (725.66 seconds including compilation). Fifth is the complete
maintained gate. Failed compilation attempts earn no proof credit.

This is a conditional TrustIR invocation theorem for one actual retained
module. Its five access premises do not establish a single valid Rust array
reference or an arbitrary nested call contract. Rust frontend adequacy,
reference/provenance/lifetime semantics, caller/native ABI ownership,
private-frame separation and the relation between source memory and native
memory remain open. No production backend rebuild or native execution is
claimed for this test-only increment; the preceding
[pointer-cast qualification](../2026-09-20-frontend-pointer-casts/README.md)
still records the native writer's frame/opcode refusal. The installed toolpack
is unchanged. **All L01–L14 remain OPEN.**

`inventory.json` binds every retained artifact's stored and decoded hashes and
lengths; `scripts/check_evidence_archive.py` audits them.
