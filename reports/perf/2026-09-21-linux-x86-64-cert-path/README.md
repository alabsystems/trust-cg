# Linux x86-64 wave-1 `cert-path` evidence — 2026-09-21

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Measurements behind the x86-64 call-only-body exemption and the corrected
XD-01 diagnosis in the Linux x86-64 completion plan.
Everything here was produced on the branch `wave1/cert-path` (base
`23e081da0`) on the host described in the
[2026-09-20 baseline report](../2026-09-20-linux-x86-64-baseline/README.md):
`x86_64-unknown-linux-gnu`, stock Rust 1.97.1 for the root workspace
(`rust-toolchain.toml`), the tree-built stage2 `trustc 1.99.0-dev (3a3e781fe
2026-09-14)` for the bridge, explicit unverified frontend lane.

## `census/core-x86_64-linux-O0-v45/`

`trust_ir_cg_census.py --crate core --opt-level 0 --panic abort` on the bridge
dylib built from this branch (`targo --unverified build --release --locked`).

| Item | Value |
| --- | --- |
| Backend identity | `backend.sha256`: `861e35c6c4446dcb518903923e60529d883c4c117eec1df5e8d52fcf2e48666e`, built from `3918169bc` (the branch after review fixes) |
| Failed roots | **289** over 27 reasons (HEAD `23e081da0`: 335 over 28) |
| Delta against HEAD | 46 roots fixed, all `[TCG-PROOF-465]`; 0 newly failing; 0 roots with a changed reason |
| Emitted objects | 3,143 (HEAD: 3,097) |
| Wall | 67 s |
| Earlier run | dylib `87c6274c86915928972f6e26a6beb73ab65ece3a9d96920fe2dd23c6d737ec77` from `68933360f` (before the review fixes) gave the identical 289 roots: 0 fixed, 0 newly failing, 0 changed reason between the two runs, so dropping the unreachable frame-envelope arm of the empty-body predicate changed nothing on this corpus |

`provenance.json` is the census script's own record. Its `trust_cg_rev`
(`9da5e2376…`) is the Trust checkout's `first-party/trust-cg` pin, which the
script reads from that checkout; it is not the revision of the worktree that
built the dylib. `backend.sha256` binds the measurement to the built backend.
`failed_roots.jsonl.gz` is the per-root list (`reason`, `message`, `symbol`,
`class`); `gap_table.md` is the reason table.

## `census/fixture/`

Ground truth for the exemption's predicate. `callonly.rs` is a `no_std`
fixture with the four `-Cpanic=abort` panic-helper shapes the census refused
under `[TCG-PROOF-465]` plus one ALU control; `rows.log` is the per-row
verifier disposition of every function in it, printed by a scratch-instrumented
build of the bridge (instrumentation removed before the census dylib was
built). Every helper body is `[Ud2]`, `[Call, Ud2]` or `[Jmp, Call, Ud2]` with
the dispositions `Skipped { "x86-64 trap instruction" }` and `Unverified {
"no proof mapping for x86-64 opcode Call|Jmp" }`; the frame `push rbp; mov
rbp, rsp` is inserted by the encoder and is not a row. The control `shape_alu`
carries a value row and keeps the non-vacuous rule.

## `xd01-residual/`

`TCG_TRACE_STATISTICAL=1 cargo test -p trust-cg-codegen --test <target> --
--nocapture --test-threads=1` over the seven host-JIT floor targets
(`run.log` has each target's exit code; `<target>.log` is that target's full
output with its `TCG_STATISTICAL fn=... inst=... opcode=... proof=...
category=... samples=...` rows, and `lib-native_install_gate-alone.log` is
the six `compile_service::native_install_gate_*` lib tests run alone the same
way). `residual-table.md` tabulates every `TCG_STATISTICAL` row, deduplicated
by (function, instruction index) within a target: 911 statistically credited
instructions over 74 functions, 665 in integer classes and 246 in FP/SSE
classes. These are the rows that
`Compiler::gate_jit_proofs_promotable` refuses through the aggregate
`statistical_validation` certificate; the table is the scope of the re-posed
XD-01 decision, not a repair.
