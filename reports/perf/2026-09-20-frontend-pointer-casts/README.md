# Frontend pointer cast repair — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The Rust bridge emitted a mismatched Copy from `Ref<Tuple>` to `PtrConst<Tuple>`,
then a `PtrToInt` whose source was typed. TrustIR requires exact Copy types and a
bare `Ptr` source for `PtrToInt`. Both original errors are retained in a fixture.

The repair preserves thin reference/raw-pointer types with explicit `PtrToPtr`
transports. Pointer-to-integer conversions extract a bare pointer first;
integer-to-raw-pointer conversions produce a bare pointer before the typed raw
endpoint. Requests to manufacture references, discard fat-pointer metadata, or
reinterpret unrelated carriers are refused by this helper before changing the
block or allocating values. Identity Copies remain identity Copies.

No pointee layout, reference lifetime, aliasing, allocation or dereference
permission is inferred from an address conversion. Nominal Rust structs can
share a structural TrustIR tuple while having different physical layouts. The
aggregate-reference and nominal reinterpretation captures therefore retain
Unclassified ABI metadata and no tuple descriptors. The existing signature
layout guards and native proof gates are unchanged.

## Qualification

Base: `c4b6e33b8feb7dc9fdf781c2b56a2ceb729a1d97` (ordinary pull from remote main).
`source/final-source.json` identifies the exact qualified candidate files and
staged tree. The source patch, harnesses, failed attempt, compile logs, capture
modules, object bytes and command/result records are inventoried below this
folder. Large artifacts use deterministic gzip; the inventory checks both
stored and decoded hashes. Shared libraries remain host-local, with their
identities and build provenance retained in the records.

- Seven Copy/cast regression groups pass, including 16 valid pointer/integer
  combinations, 11 rejected requests, the historical two-error reproducer,
  and all 18 actual O0/O1 thin-pointer captures. Existing writer O0 proof
  refusals and source/output mutation controls remain active.
- Six signature-layout/Core-reflection groups pass. This repair does not expand
  their accepted nominal-layout profile.
- A diagnostic backend built with the genuine installed Trust/Targo pack
  captures 22 O0/O1 programs. Twelve scalar programs compile to objects; six
  aggregate programs and two fat-pointer programs stop at `TCG-PROOF-465`
  (`StpPreIndex`, `LdpPostIndex`). Two integer-to-reference programs stop at the
  explicit pointer/integer transport refusal, before module capture.
- The ordinary uninstrumented backend build and native execution results are
  recorded separately. Twelve scalar cases compile and execute successfully at O0/O1 (60 address comparisons); all twelve objects are byte-identical to their diagnostic captures. Ten corresponding aggregate/fat-pointer/reference refusals and two writer refusals are reproduced with the normal backend. Refusal reasons are checked explicitly; no rejected object is executed.
- Root formatting, documentation/inventory, whitespace and archive checks are
  recorded. Root formatting does not claim that every legacy private-backend
  source file satisfies rustfmt.

All heavy jobs run serially with a 16 GiB process-group RSS ceiling, zero grace,
two build jobs and one test thread. The Rust frontend uses the explicitly
unverified development lane; backend proof enforcement stays enabled. Native
execution is finite regression evidence and supplies no end-to-end Rust proof.

The first static run passed the five cast groups but failed to compile the
signature-layout test: its include of the production Copy canonicalizer lacked
the newly shared pointer helper. The missing test module import was added;
subsequent complete runs pass. The failed source and log are retained as a
failure rather than omitted.

## Remaining work

The full system is not complete. Aggregate-reference address programs and the
writer still lack native frame/opcode proof authority. Pointer validity,
provenance and access adequacy, arbitrary caller worlds, private-stack/ABI
refinement, and composed source-to-native correctness remain separate work.
The private whole-writer ByteV1 replay stays a model-specific theorem and is not
used to bypass compiler admission. No L01–L14 completion row is closed here.

The pulled x86 memory-MOV obligation has independent byte decoding and mutation
controls; that upstream commit explicitly leaves wiring it into the compiler's
credit path and extending other memory opcode families for subsequent work.
