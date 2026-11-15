# trust-ir-cg census: `core`
* emitted objects in `obj/`: 557 (per-function/per-batch objects the backend DID produce; not a success count of mono items)

* compiler: `rustc 1.99.0-dev (d7f143f3b 2026-09-21) (trustc 0.1.0)` at `trust/build/x86_64-apple-darwin/stage1/bin/trustc`
* backend: `<scratchpad>/s3-integ/s3c.dylib`; panic=abort; opt-level=0
* repo rev: `d7f143f3be5ac67de26cc75b52da3f2d87a7b770`; trust-cg rev: `de1f19099ff1c50c475df239e0bed471805897b5`
* exit code: `1`; wall: 911s
* typed refusals (JSON): **2891** across **2891** functions; distinct codes: 3
* failed roots (externally required, fail-closed): **2887**; distinct reasons: 2
* skipped internal functions (dropped as unreachable — for a LIBRARY every one is a missing symbol downstream): **0**; distinct reasons: 0
* trapping stubs emitted for dynamic-dispatch shims (link, but TRAP if reached): **0**; distinct reasons: 0
* harness errors (non-backend `error:` lines): 0

## Failed roots by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|
| 1 | `[TCG-PROOF-465]` | 2885 | `_RNvYNCNvMs5_NtNtCs7e1ihmkzmZ8_4core2io5errorNtBa_11OsFunctions7DEFAULT0INtNtNtB` |
| 2 | `[TCG-REGALLOC-063]` | 2 | `_RINvNtNtCs7e1ihmkzmZ8_4core4sync6atomic11atomic_loadnEB6_` |

## Skipped internal functions by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Trapping stubs by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Typed diagnostic codes

| rank | code | count | example function | example why |
|---:|---|---:|---|---|
| 1 | `TCG-PROOF-465` | 2887 | `__trustcg_array_fill_i8` | rustc_codegen_trust_cg: Trust Codegen object emission failed: proof promotion rejected for target X86_64: non_verified p |
| 2 | `TCG-REGALLOC-063` | 3 | `core.542ad821d0dce3d0-cgu.0` | rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: unsupported  |
| 3 | `TCG-MIR-UNSUPPORTED` | 1 | `<crate>` | rustc_codegen_trust_cg: cannot compile required function with unsupported MIR (failing closed rather than miscompiling): |
