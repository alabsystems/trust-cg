# trust-ir-cg census: `core`
* emitted objects in `obj/`: 67 (per-function/per-batch objects the backend DID produce; not a success count of mono items)

* compiler: `rustc 1.99.0-dev (3a3e781fe 2026-09-14) (trustc 0.1.0)` at `$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc`
* backend: `/home/ayates/trust-cg-wt-cleanprof/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so`; panic=abort; opt-level=0
* repo rev: `ceb94fe99cbc7db4bbe617b53fd04a61acbd4467`; trust-cg rev: `9da5e2376931cfca79f60e82c0acda9633af01c7`
* exit code: `1`; wall: 90s
* typed refusals (JSON): **0** across **0** functions; distinct codes: 0
* failed roots (externally required, fail-closed): **3363**; distinct reasons: 1
* skipped internal functions (dropped as unreachable — for a LIBRARY every one is a missing symbol downstream): **0**; distinct reasons: 0
* trapping stubs emitted for dynamic-dispatch shims (link, but TRAP if reached): **0**; distinct reasons: 0
* harness errors (non-backend `error:` lines): 0

## Failed roots by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|
| 1 | `[TCG-PROOF-465]` | 3363 | `_RNvYNCNvMs5_NtNtCs5j7F4uy8uKG_4core2io5errorNtBa_11OsFunctions7DEFAULT0INtNtNtB` |

## Skipped internal functions by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Trapping stubs by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Typed diagnostic codes

| rank | code | count | example function | example why |
|---:|---|---:|---|---|
