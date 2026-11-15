# Full Linux floor after the flat GEP repair

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

**FAIL**, at clean source `c29c68640da6604ce37d98e5e2a3a6f0946ffe76`,
on 2026-09-24: all **167 targets** ran, **166 passed**. Rust reported
**1,076 passing tests and one failing test**. The full run took 2,212.76 seconds.
No target was removed to obtain this result.

The sole failure is
`trust-cg-lower/trust_ir_construct_inventory::executed_rows_name_darwin_floor_tests_that_reach_the_construct`.
Its GEP row still points to `g5_packed_struct_gep_matches_clang`, whose repaired
field-projection fixture uses `ExtractField` and was renamed accordingly.
Changing only that name would falsely credit a test that no longer exercises
GEP. Commit `f522ed45be84d8109cd1a8cb3424324148dd5e0f` instead points to the
native byte-gather test and its reachable `.gep(` call. That byte-gather
target passed in this full run. Validation of the inventory repair follows
in a separate run; this archived result remains a failure.

The maintained gate required a clean source tree, offline dependency identity,
and pinned proof tools, with two Cargo jobs, one test thread, a 16 GiB RSS
ceiling and 1,200-second timeout per target. Exact environment, tool and
dependency identities, per-target resource receipts, commands, counts and
failures are retained in the raw report and logs. The outer campaign guard
also records its own process group; use the per-target receipts for child
resource measurements.

The inventory records compressed and uncompressed SHA-256
hashes for every original report, target log and runner. These are regression
results on the named source. The later main frame-entry repair, Rust frontend
qualification, proof closure and all product completion rows remain separate
requirements.
