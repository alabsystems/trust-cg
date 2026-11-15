# Actual frameless output bytes — 2026-09-20

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The bounded diagnostic checker now binds the actual O1 writer's complete original
TrustIR, actual adapter LIR and all 84 emitted AArch64 text bytes. It recognizes
frameless bodies separately from the existing exact sixteen-byte FP/LR envelope.
It decodes 64-bit MADD independently of code generation and tracks its constant
address factors, including X1 being reused after its original value is stored.

This is **diagnostic evidence, not new production proof authority**. The Rust
trace checker is not proved; caller lifetime, writable ownership and valid Rust
references remain external requirements. The canonical ByteV1 theorem still
needs a proved Nat/bitvector memory relation and composed source/native semantics.
No instruction, publication, cache or JIT admission is changed. All L01–L14 remain
open; the installed compiler package is unchanged.

## Checks and independent replay

- All **53 source-bound frame tests pass**, zero failed or ignored. They include
  the complete original framed query and its 512 single-bit refusal controls,
  incomplete frames, unsupported registers/effects, 256-word limits, exact
  original-source layout binding, 35 MADD changes and a register-reuse ordering
  mutation. GNU assembler independently matches ten encoding cases, including
  all twenty body words of the actual writer and six multiply-add variants.
- The actual typed and LIR-derived frameless queries are identical: **8,187 bytes**,
  SHA-256 `83a786b5c82edd3226a5baf773935b73652a3f667ff5ff6dd539d7561e6e35d9`.
  They relate the entire arbitrary BV64-to-BV8 byte map after all five ordered
  writes. Output alignment and nonwrapping range are explicit premises; no
  private stack interval is introduced for frameless code.
- AY `c495c107` emits an Alethe certificate; Clean `680069f8` independently accepts
  it and rejects all three corruptions: a proof hole, missing empty clause and
  opposite problem premise. This proves the encoded byte-map equality; equality
  of the interpreted traces still depends on the bounded Rust checker.
- The prior framed query is unchanged: **96,334 bytes**, SHA-256
  `31a504fe4c43ff0c2e95e4cf38aa5d09d5a538d45499bd5e5f6d800b7b5aeb81`.

The focused test command is:

```sh
cargo test --locked -p trust-cg-verify --lib source_bound_frame:: -j2 -- --nocapture --test-threads=1
```

The first attempt's captured stdout reached the guard's 1 MiB capture limit,
so its final result and monitor flags were not retained. It receives no passing
qualification credit. The successful harness redirects complete child output
to a file inside the anchored process group; the monitor result is separate.

## Fresh frontend and native endpoints

A temporary diagnostic backend at parent `20f3d8f8` captures the complete original
module before unchanged backend proof enforcement. The O1 module matches the
retained fixture byte-for-byte: SHA-256
`ba3659953f16521ba6fdf241d3fd2414c1330b5bd88f01cc368cd4dfd35d346c`.
The temporary instrumentation was then removed from the isolated capture tree.

A fresh compile using the **installed, uninstrumented** backend also passes.
Its entire ELF equals both the diagnostic capture's ELF and the previous qualified
native ELF: SHA-256
`03904fb2dc13ef8499baf93d0db092dce099e34c3d46fe682a8e26ede8edf732`.
The extracted 84-byte text equals the new test fixture: SHA-256
`af74f5a2b9ba55d66cb011f8c829490d635683077357697b47f650471d6693bd`.
A fresh linked oracle passes **257 calls**, comparing all sixteen arena words
(five outputs and eleven canaries), eight buffer placements and callee-save/SP
preservation. These are finite execution controls, not a theorem about hardware.
Both compiles use the explicit unverified Trust frontend; backend proof checks
remain enabled. O0 still refuses frame-pair/CSet proof gaps and emits no object;
its original module and refusal are retained.

## Provenance and reproduction

The records retain exact commands, source hashes, complete test/query logs,
original modules, objects, assembly, native oracle, proof/corruption packets and
solver/checker identities. Source and HEAD were held throughout each qualification.
The successful commands use an authenticated process-group RSS guard, at most
16 GiB with zero grace, two Cargo jobs and serial execution. The certificate
replay uses 16 GiB for AY and 8 GiB for Clean. No resource limit was breached.
Large backend and verifier binaries are identified by hash rather than stored.
The local archive harnesses record their original absolute paths; use the
retained fixtures and explicit commands to reproduce in another checkout.

Run `python3 scripts/check_evidence_archive.py reports/perf/2026-09-20-frameless-output-bytes`
to verify every stored and decoded artifact hash. This checks retention integrity,
not the semantic truth of the report.
