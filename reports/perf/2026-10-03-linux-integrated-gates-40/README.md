# Integrated Linux AArch64 gates for the amendment-S corpus classification (2026-10-03)

## What run `i57` integrates

Integration `e3508e8d4` is origin/main `e28c13a23` plus `fix/classify-trust-ir-template-corpus`. That branch was verified, and the verifier's two low findings were fixed on it:

- **Template blobs are not modules.** Amendment S at the trust-ir pin `0f243925` defines `.tmbs` level-S template blobs (magic `TRUST_IS`). A module consumer must refuse them.
  - `trust_ir_corpus_roundtrip` classifies the template family. It walks the new `templates/` directory and lists `refuse_templates/` with its reason. Both directions are exact: an unlisted directory, a listed directory that is gone, or a template file without an extension fails.
  - The in-process reader (`load_module_from_bytes`) and the Auto format detection refuse a `TRUST_IS` blob by name (`TEMPLATE_IS_NOT_A_MODULE`). Before, they refused it only by accident, through the JSON fallback.
  - Both `must_refuse_corpus` targets pin that refusal.

## Environment

Trust development mode (Trust ae9c2c1da), with AY admitted. The bridge lane was not run: the change touches no code the bridge builds differently.

## Results

| Lane | `i56` (origin/main, pin `0f243925`) | `i57` |
| --- | --- | --- |
| Floor (225 targets) | 2 failing tests (`trust_ir_corpus_roundtrip`) | PASS |
| codegen/lower lib | 6,637 passed, 0 failed | the same |
| CLI | 1 failure (`emit_proofs` arithmetic) | the same 1 |
| natives, local-call, fsym, fsym CLI, opt lib, symbol binding, verify gates | green | green |

Logs are kept out of tree (host-local: `/home/ayates/trust-cg-floor-20260922/run-i57`, `*-i57.log`). This is regression evidence on one host, not proof.
