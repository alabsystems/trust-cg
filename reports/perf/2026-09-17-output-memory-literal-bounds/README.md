# Independently checked literal bounds probes in the original O0 writer

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The conditional typed output checker now accepts the unchanged captured O0
TrustIR module through the real adapter and independent reference A64 words.
Its six unconditional blocks contain ten literal comparisons, including five
InBounds probes whose assertions the frontend replaced with guard metadata.
The source interpreter evaluates all comparisons at their actual 64-bit types.
An annotated bounds probe must be unsigned less-than and evaluate true.
Neither an InBounds label nor a ProofRef can authorize a false guard.

A private LIR view independently checks literal operands, definition order,
result types and uses. It removes only unused comparisons and numeric bounds
guards proven not to trap. A removed comparison result cannot be consumed even
by another removed instruction. Malformed guard arities, undefined or redefined
values and instructions following return are rejected. The original module,
function, LIR, annotations and exact target bytes remain retained by reference.
The generic raw-LIR API retains its existing boundary and does not acquire this
typed-source capability.

Qualified index `b75f395121230180083f1acea4eece53cb53d741`, based on `919ce4dd9ff70a48d0a9c486ad0dc161672dada0`.
All **60 selected tests pass**, with exact listing/execution agreement and no
failed or ignored tests: 45 source-bound controls, nine original typed-source
tests and six UF traversal controls. The three added tests exercise 20 false,
wrong-operator, nonliteral and wrong-type source mutations; 25 malformed LIR
guards; six comparison/liveness/terminator corruptions; and ten signed/unsigned
comparison cases spanning zero and the signed/unsigned boundaries. A positive
control removes all ProofRefs and still checks the actual true guard operands.
The genuine O0 fixture passes for both scalar and paired reference store streams.
All prior byte/source mutations and eight GNU assembler reference programs run
again. Ordinary library compilation, formatting and documentation checks pass.

The two authored, two captured O1 and two captured O0 source-to-byte checks all
export the same 96,334-byte conditional theorem, SHA256
`31a504fe4c43ff0c2e95e4cf38aa5d09d5a538d45499bd5e5f6d800b7b5aeb81`.
A fresh replay using AY SHA256 `c495c107b0b8918ccc98f894d3723de16f63cb32c03b4f518ba71e759b489257` produces a strict Alethe
certificate. Independent Clean SHA256 `680069f8d7185a8dbc0cc67e860d57a7df9ca4cf8bd8a4d8951346cbbf594dbc` accepts it and
rejects hole, missing-empty-clause and opposite-premise mutations.

The first run compiled successfully and passed all 45 existing source-bound
controls, but three positive typed-source tests failed because the new view
mistakenly required explicit B1 entries in the adapter's sparse type table.
Icmp defines a boolean result even when that optional entry is absent. The
repair accepts the opcode-defined type and still refuses conflicting explicit
types. The full corrected 60-test run and the first failure/source patch are
retained; no negative control was removed.

These are exact retained frontend modules and independent reference words.
The previously refused genuine Rust compilations remain refused; this does not
claim emitted bytes from those failures. Caller allocation, lifetime, writable
permission, native frame ownership, checker refinement and production admission
still require their own proofs. No installed compiler was changed and all full
Linux L01–L14 requirements remain open. Commands, source and binary identities,
enforced resource ceilings, timings and actual evidence are retained below.
Every stored and decoded artifact is checked against its length and SHA256.
