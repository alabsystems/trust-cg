# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, class lists, outcome tables, queries, dumps) out of it.
These payloads were never committed. They are held on the measuring host (the
x86_64 Mac of the README) under `~/tcg-scratch`, at the paths below, and are
bound here by size and SHA-256; a directory's row is its total bytes and the
SHA-256 of its manifest (one line `<sha256>  <name>` per file, sorted by name).
`census/payloads.py` regenerates the table. The README states the numbers each
one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s16-design/size_roots.tsv` (the design's class: 101 size-refused functions, 103 bound-uncertified) | 33587 | `61ce8ae97d11a69855090f7ccb9ca7405e3e2726ba7681eedd4ddaf6827dc056` |
| `runs/census-main-a902/failed_roots.jsonl` (main a902's core census (the census chain's baseline row)) | 414814 | `ba84a905957aafce215f313e8fd544f636e3bfa8fb79f7fa97985fd8653eb7b0` |
| `runs/census-main-a902/stderr.log` (its body trace) | 2586489 | `27e08b71c85bab7f852434e4d46ba8f47d715d7833674a40573b840423cf364a` |
| `s16/payloads/class_main/` (its class (`size_roots.py`): 121 size-refused, 94 bound-uncertified) (1 files) | 34133 | `241aeb46dd64cda51029d6c44386b7c0dfa2a5c897e1d8c597e65d56e3911fb1` (manifest) |
| `runs/core-ir-s9/` (slice 9's core dump (the design's input)) (88 files) | 5977212 | `8776e580c966c9f81c085885fd100f78da7de7dc9643fd78f539315bae0d6a69` (manifest) |
| `runs/core-ir-s16/` (the fresh core dump from main a902's bridge (`census/dump_core_ir.sh`)) (166 files) | 6814351 | `a0469d5e8d83fbbe785fd8b6d21b8d0b99737c5e7fe33854d11f7f0e5fb75221` (manifest) |
| `s16/payloads/probe/` (the probe over slice 9's dump before the replanning commit) (2 files) | 100389 | `49c6e4e9a4fbf44e79fecb6c6dc544be8bd0eceaad37db58771751f4c721d0e7` (manifest) |
| `s16/payloads/measure1/` (`census/measure_s16.py` over it) (1 files) | 44834 | `f40fa7f4afc2605c493b2f9d1f58a588a709ab4e9b957cb5138316197c71de18` (manifest) |
| `s16/payloads/probe2/` (the probe over slice 9's dump at the replanning commit) (2 files) | 74990 | `c325124f2b9a6d1f912972b3f6cdf7da1743a2f7442e8608ec9740d8633f747b` (manifest) |
| `s16/payloads/measure2/` (`census/measure_s16.py` over it) (1 files) | 44640 | `0a4f77fb5859cc8ef8deffd6404dc7d6deed4262857cbe16b3d0f1462c90ff6c` (manifest) |
| `s16/payloads/probe6/` (the probe over the fresh dump, final spelling) (2 files) | 45007 | `8a0ea98a06a8f8e5cb07fb8cabf6b089e57d0393d655333f562df9fdaf7f200d` (manifest) |
| `s16/payloads/measure6/` (`census/measure_s16.py` over it (the 121)) (1 files) | 46634 | `8407ea5d57797208c1bb358614d2659a1377283723d1ebfe36e573699f3fa2a9` (manifest) |
| `s16/probe_run6/smt2/` (its queries: 563 parts of 106 functions, one query each for the 94 controls, index) (658 files) | 3818489 | `74a6b642840de219384caa2fe1a7d66c6ae87c6d1e441d9252aaaf0e9caf7c0c` (manifest) |
| `s16/payloads/replay_parts_core.tsv` (the 563 parts on AY build 12713 with Clean, 30 s each) | 23814 | `585caac573cabdc28a2e0eaf13e660ff6e7db670e95f2e30be9e7490afc41bc3` |
| `s16/payloads/replay_parts_core_unnumbered.tsv` (the 643 parts of the first spelling (no value numbering), same replay) | 30514 | `1c31347e9cb7e67f67d6b241a590622fe164b62151f46b917d817b71dca7ade3` |
| `s16/payloads/qualification/host_qualification.log` (host qualification, final tree) | 8461 | `ae86f3e9c50f232c6fcb94be5f3f98797bc2beb7fd32caa7ad549752f430cd83` |
| `s16/payloads/qualification/verifier_credits.log` (verifier credit, final tree) | 1641 | `bbdd130930bb3b15cb55f2e09c54b108b7c79c5a84f803e8cf8e789f67b6499c` |
| `s16/payloads/qualification/queries/` (every replayed qualification query) (36 files) | 212843 | `08f9af123dbac51e44971710e4e00122693d642522d74a0c8524546e62955a4b` (manifest) |
| `s16/payloads/qualification/longchain_300s.tsv` (LongChain's parts with a 300 s budget) | 183 | `3bf109a71c0c25f5db1392a0dfb45d36eaedb4e98cf80965e181103ffd637c87` |
| `s16/payloads/qualification/inverted_branch_300s.tsv` (the inverted-branch part, one-shot AY) | 59 | `236440ea9d597ba9e30e579addcf1229e99b5ad38ccd0c9813659dc58e3a80bb` |
| `s16/payloads/gate_body.log` (the whole x86 body library gate (solver-free), final tree) | 27125 | `b554794d68beeee050328e734104a34b6ca885ac0600f05daa0624f0e8a15198` |
| `s16/payloads/cli_emit_proofs.log` (the CLI emit_proofs tests with AY and Clean) | 2036 | `6c5ba8f5ca79fc4c68b4c82586bd233f8d323139d1c9c4f9e85d5ee96e744587` |
| `s16/payloads/mutants_final/` (`fails-before/run_mutants.sh` on the final tree, with each run's log) (13 files) | 1300468 | `ae3166a405c07881379c3277ab2ccee7a6e31af2595d7a7545cd494cd646c04a` (manifest) |
| `s16/payloads/mutants.txt` (`fails-before/run_mutants.sh` on `887f24723`) | 9089 | `792f5d879fca4ea8610aae0c0550092908438e3e73850624d6d5aa6bbc6ed32f` |
| `s16/payloads/mutants/` (its per-mutant logs) (12 files) | 1290063 | `a5305608f5092b39ef14df310d458edab1708671c27a3e46813198654e3436f2` (manifest) |
| `runs/main-2854ce.dylib` (the landing baseline bridge, main `2854ce3e3`) | 142475452 | `867e506facf0446802bffa7680348da1f87f1aa83e896fd1c303aa42353b8d16` |
| `runs/census-main-2854ce/failed_roots.jsonl` (the landing baseline census) | 934313 | `1b269fe3ebc9c8029c36d3abc634fab6bf7e82f7734da5991002c5a37278b17e` |
| `runs/census-main-2854ce/stderr.log` (its body trace) | 5172674 | `bfcea9d3461e30bebb1b93546aa2817fa3834c0242ab036632c01c328cecb31d` |
| `runs/census-main-2854ce.out` (its summary) | 1730 | `f794504c56987f70d54ef78ec9713b4a992bc4712d1e7132fa9b8caf1034917c` |
| `runs/s16.dylib` (the slice-16 bridge, `5b5b1d105`) | 142921980 | `94f555ff772e55d29a5bc4f770df0f9ef891bb318197501281a15ed9ab691c57` |
| `runs/census-s16/failed_roots.jsonl` (the slice-16 census) | 875625 | `13d3fd4adaad12efc36659b5411c76cb721c5396be4e9f7cc761479fbbd3ba8b` |
| `runs/census-s16/stderr.log` (its body trace) | 4914777 | `e6f6ba33cdb747e678f36a8f2315a7cd22ad40e902c5890fac4480ff78e15ca1` |
| `runs/census-s16.out` (its summary) | 1690 | `fa21d937a1173eb5f5df26c2d58d7def875f5b6a467e8d27504ca8fccc3b9704` |
| `runs/dump-s16/` (its uncertified bodies' queries) (274 files) | 2644361 | `62e03d9797b5d306fb2476b8e5067a707a11e38c31f5084d3bfba8c5a48114a7` (manifest) |
| `s16/compare/` (`census_compare.py` of the two rows) (4 files) | 6442 | `291781f5616bacea869e9fe2a7247d59380b382557a59f8d77561df672461626` (manifest) |
| `s16/logs/census_chain_kept.log` (the census chain log) | 1175 | `94ba9bf135e14ede6bfa4290dbf73ff8065d493c65a28d69e8f22be3733dc168` |
