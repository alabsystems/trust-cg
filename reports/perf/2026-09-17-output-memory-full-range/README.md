# Output buffers may end at the last address

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The conditional AArch64 output-memory obligation admits a buffer whose last
accessed byte is `u64::MAX`. Previously it required the exclusive endpoint to
fit in 64 bits, excluding that legal mathematical range. The exclusive-end
comparison now also requires that endpoint to fit; a wrapped zero endpoint
cannot make an overlapping private frame appear disjoint. The opposite ordering
(output starts at or after entry SP) remains available at the address limit.

The new test independently evaluates all five actual preconditions against
unbounded-end `u128` interval arithmetic over **26,244 output/SP pairs**, including
both address-space boundaries. Explicit controls accept a last-byte-at-MAX range
with separated frames and reject an overlapping frame and a range crossing the
address limit. This proves no real allocation or mapped-address fact.

Qualified source index tree `821b4eddf9c5b2cba1a619ed85beedd9c8fe4bc8`, based on
`b9b2cfe4abaa1a2a0ebfd8edf6da2cb44cead48a`. The **57 selected tests pass** with no
failures or ignored tests: 45 existing/new source-bound controls, six original
TrustIR controls, and six UF traversal controls. Every selected name matches
execution. The unchanged source and final-byte corruption tests and all eight
independent GNU assembler reference programs are rerun. Ordinary library
compilation, repository formatting, and documentation checks also pass.

Raw LIR, final reference bytes, authored typed source, and the previously
captured genuine O1 source export the same updated query: **96,334 bytes**,
SHA256 `31a504fe4c43ff0c2e95e4cf38aa5d09d5a538d45499bd5e5f6d800b7b5aeb81`.
Fresh strict AY produces a certificate; independent Clean accepts it and rejects
hole, missing-empty-clause, and opposite-premise corruptions. Four identical
typed-source exports are checked before the deduplicated independent replay.
The first replay with the previously installed AY returned `unknown` at its
unchanged 30-second deadline and produced no certificate; that attempt is
retained. The checked AY span-selection repair was then qualified at native
library, independent checker and rebuilt CLI boundaries. The fresh successful
replay uses frozen AY SHA256 `c495c107b0b8918ccc98f894d3723de16f63cb32c03b4f518ba71e759b489257` and Clean SHA256
`680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc`. The retained receipts identify the exact producer,
checker, test executable, commands, resource caps and source fingerprints.

This remains a conditional diagnostic obligation. It does not establish caller
allocation, lifetime, permissions, native frame ownership or the implementation
correctness of the Rust checkers. It does not enable production admission,
change the installed development compiler, or turn the earlier refused Rust
compilations into native successes. All full Linux L01–L14 requirements remain
open. The genuine O0 source still requires bounds-probe support.

Every stored and decoded evidence artifact is audited against size and SHA256.
Large binaries remain local and are identified by the recorded hashes.

The subsequent ordinary pull merged upstream `684ebe77`, whose only code change
was the static proof-inventory test. All compiler implementation inputs remain
identical to the qualified index above. Fresh tests at `a29fe3bacc47b074fab967ef8cb29469c109372b`
pass both the 1,979-row corpus/allowlist check and the new exact leaf-frame
registration check; formatting also passes. Their commands, executable identity
and logs are retained in the merge inventory.
