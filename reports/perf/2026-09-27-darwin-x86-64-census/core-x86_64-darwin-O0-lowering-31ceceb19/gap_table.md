# trust-ir-cg census: `core`
* emitted objects in `obj/`: 44 (per-function/per-batch objects the backend DID produce; not a success count of mono items)

* compiler: `rustc 1.99.0-dev (d7f143f3b 2026-09-21) (trustc 0.1.0)` at `trust/build/x86_64-apple-darwin/stage1/bin/trustc`
* backend: `~/tcg-scratch/runs/a128.dylib`; panic=abort; opt-level=0
* repo rev: `d7f143f3be5ac67de26cc75b52da3f2d87a7b770`; trust-cg rev: `de1f19099ff1c50c475df239e0bed471805897b5`
* exit code: `0`; wall: 328s
* typed refusals (JSON): **0** across **0** functions; distinct codes: 0
* failed roots (externally required, fail-closed): **0**; distinct reasons: 0
* skipped internal functions (dropped as unreachable — for a LIBRARY every one is a missing symbol downstream): **0**; distinct reasons: 0
* trapping stubs emitted for dynamic-dispatch shims (link, but TRAP if reached): **0**; distinct reasons: 0
* harness errors (non-backend `error:` lines): 0

## Failed roots by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Skipped internal functions by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Trapping stubs by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Typed diagnostic codes

| rank | code | count | example function | example why |
|---:|---|---:|---|---|
