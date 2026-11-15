# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, root lists, outcome tables, queries, bridge dylibs) out of
it. These payloads were never committed. They are held on the measuring host
(the x86_64 Mac of the README) under `~/tcg-scratch`, at the paths below,
and are bound here by size and SHA-256; a directory's row is its total bytes
and the SHA-256 of its manifest (one line `<sha256>  <name>` per file, sorted
by name). `census/payloads.py` regenerates the table. The README states the
numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/census-s9b/failed_roots.jsonl` (the slice-9 census the class was measured on) | 1231194 | `3f4dc018f961d5eeee3ed032974aae995fa297dd66646c5a8cad7e18e57e05cd` |
| `runs/census-s9b/stderr.log` (its body trace) | 7325560 | `89f0aecef83f0af463f684717742857690c488db1a84eb49cb51e191068ef7e4` |
| `s12/payloads/roots.txt` (the class roots, `census/loop_roots.py`) | 20695 | `3d4894d890e75a3ed8bcabb356103b88b73b3402168d0ecf5b41a1a579efcb0a` |
| `s12/payloads/all.txt` (the class functions) | 20744 | `dd38a2dab995def4cdadad99a38ba7a598598ccb21563260cbcbacced1e5efab` |
| `s12/payloads/loops_main.tsv` (the probe's `--loops` mode over the slice-9 dump) | 91803 | `93184bcaf982f2d38d331866207e76419f7ed49498e2ebb7e3f81db154e2eea1` |
| `s12/payloads/loop_profile.txt` (`census/loop_profile.py`) | 1492 | `4e9295a721a228a88fcd160e0ecfb1087c4b6266f33461443e981f4829610381` |
| `s12/payloads/cf_main.tsv` (the main owner over the dump (`--cf`)) | 625604 | `1c9448560cacc6a2792542d2a2de262510c61c43a55448162745d96e166fcbbc` |
| `s12/payloads/cf_s12.tsv` (the slice-12 owner over the dump, before the merges) | 621343 | `c004018ae9899e708f22754d8005b3d985773d7cb5cb0dbcb27633c82482cb2c` |
| `s12/payloads/newly_bound.txt` (bound by slice 12 only, `census/newly_bound.py`) | 14905 | `5d44c12329cb1afc7307663fcce67fe5bc1b089291af13858b5a61345d747bbe` |
| `s12/payloads/q2/` (their queries) (81 files) | 736753 | `e94e158f93288f821e423eb79a078b76ca81472a22ee557606e6472cec15f845` (manifest) |
| `s12/payloads/replay_q2.tsv` (their offline outcomes on AY build 10530) | 13461 | `c38a3c8e0969b6adccee9f0ba3903ed317f89e77aaeabe778078fd641e63a612` |
| `s12/payloads/replay_q2_12713.tsv` (their offline outcomes on AY build 12713) | 3767 | `5141b00565a4adc9d29d322cbbd6653cbdfb98047274f791c797aecff57fb0a3` |
| `s12/payloads/final_probe/cf_final.tsv` (the final owner over the dump (`--cf`)) | 609393 | `a1c22186f8396fed1ab3ccec26e2a4ca76280dc1edbea0541c231165ba06a8a9` |
| `s12/payloads/qualification_b10530.log` (host qualification on AY build 10530 (before the merges)) | 9320 | `5b499c6fab6ec7db829215b2277f7da6bdec7b62928c2f8e2d4cb062ed5b9d0f` |
| `s12/payloads/fixture_queries/` (the fixture and refutation queries, build-10530 tree) (38 files) | 54257 | `de28ed5f7818b8d21a998992064811d31fb21e4ba98a14c6e1166ed3e4513eb2` (manifest) |
| `s12/payloads/qualification_12713.log` (host qualification on AY build 12713 (final tree)) | 11237 | `2f344a1b0b08137c84959783db6dba1673a8ad6be9451328194f89b7f4e3e7d4` |
| `s12/payloads/fixture_queries_12713/` (the fixture and refutation queries, final tree) (40 files) | 57602 | `d0b132c287b680d5120ff429abd0859ad8e03fc5fe351ef6a73870706ced9718` (manifest) |
| `s12/payloads/fixture_replay_12713.tsv` (the fixture queries offline on build 12713, before the merges) | 530 | `2d5c3b204670d4e444e4ecea868e32d46121c2000d5f06dec0232c1c2830db20` |
| `s12/payloads/earlyexit_long.tsv` (EarlyExit with a 200 s budget) | 36 | `1d3e0d28edda55903fd5e6706387231907de34813d87ee5a3dc734c117a2e71a` |
| `s12/payloads/mutants_premerge/` (`fails-before/run_mutants.sh` on `2316cdeac`) (18 files) | 360856 | `32590c3e31eadfa6353f838742aed8703ca1066987e362530905e064569b7dcb` (manifest) |
| `s12/payloads/mutants.txt` (`fails-before/run_mutants.sh` on the final tree) | 6021 | `26f954ccd388c3eaf5ee72ba78aef3de4d11fc25ede28748cd5b930f7ca5f6b5` |
| `s12/payloads/robustness_no_replay_first.log` (robustness probe, sampler only, no source retry) | 1490369 | `fd12a6cd511dcdb3625950374a261765317cbea673340074a1537a22fa97094d` |
| `s12/payloads/robustness_no_replay_second.log` (robustness probe, sampler only, a fixed retry pool) | 1490369 | `41cbb939aa1b0b649d3cd9fd0b0e9c6221f34147e0e7ebb1d80e2ba1b210c45f` |
| `s12/payloads/robustness_no_replay_final.log` (robustness probe, sampler only) | 1484773 | `9c40a970108af009d209f6dc76aaa660ed912c4662ea9623f51ccfdb11ab5046` |
| `s12/payloads/robustness_replay.log` (robustness probe with the AY replay) | 924771 | `8ae7e74db1abe145be817b86ecfd55c842e9031a61f644f98c3ebe90203f40a9` |
| `runs/census-s13-12713/failed_roots.jsonl` (the baseline: main `360eecafa` on AY build 12713 (slice 13's row)) | 560559 | `c40628cb9403a31cf72e9621a8f3b48856660afc35239c718d8ce7b173c27253` |
| `runs/census-s13-12713/stderr.log` (its body trace) | 3954616 | `7adc25e8b3a051f631717513debad850c1118ffa0a4a9dedc418529b6da14c07` |
| `runs/s12m.dylib` (the merged tree's first bridge (`9d6308215`)) | 131753080 | `27f77f1028105e20543f5a851591b6709fe0abfdb4e8ef7071fcadfefbea8259` |
| `runs/census-s12m/failed_roots.jsonl` (its census) | 489586 | `21b97f3ca484a22bdeb70f3bb93ecc4d193a2af70824117bd7e1a609ff9d8492` |
| `runs/census-s12m/stderr.log` | 3620985 | `ff0b08fe12300c7f15e403a13bf368e8cb20fba3447071d8c2d6083c8772d862` |
| `s12/payloads/compare/` (`census/census_compare.py` against the baseline) (4 files) | 54989 | `50485b753201ee77e310a3e117f2d83d8b06f671c792e6c0da9e22e5a3e4db3d` (manifest) |
| `s12/payloads/refuted/` (the two refuted bodies' queries and counterexample) (4 files) | 26178 | `2d826e502361995b530ed0a6d7f1e10b2b485c7eb3271b9da7f6c10601148d08` (manifest) |
| `s12/payloads/newly_failing/` (the newly failing bodies' queries) (4 files) | 35823 | `4d23f69e36f8eeece2e2e0cae24a365a66b6cf9395d55520381c03a11879fc8f` (manifest) |
| `s12/payloads/newly_failing.tsv` (their offline outcomes) | 488 | `92985f9a53078b1adf1fb76e3528fde78cea6fdcd85673f4538fe8f1e508b65d` |
| `runs/s12f.dylib` (the second bridge (`55e42a730`)) | 131770224 | `1b395ecead38ca248d5e6b919d6864c7a8dfd8458e1cddbce662dfa3cdf3281b` |
| `runs/census-s12f/failed_roots.jsonl` (its census) | 487647 | `4fdf5b91f924b1f21d3aed75ad85026bdf151861369a2bdd816e3255f72a7017` |
| `runs/census-s12f/stderr.log` | 3606370 | `b64ceda4b514f8aebd9fbf0d4e847b45c993d275537e427c45dffa003e66e8b4` |
| `s12/payloads/compare_final/` (`census/census_compare.py`) (4 files) | 54684 | `8d397e2ea5c03b31dfa1b0bd04e2dff4dc370c7d7db4d3449bfca309e5f10b29` (manifest) |
| `s12/payloads/refuted_final/` (add_small's queries, counterexample and probe, before and after) (12 files) | 782034 | `63cb9813b5c7d9bf89cf7638c15f244f628f6e61b7a7a5d333d6ea5a0aa43552` (manifest) |
| `runs/s12z.dylib` (the final bridge (`5bc8bd533`)) | 131770256 | `2af4a7f18233a4a2dd1a78d12d5944a4232cff9d10771e0b1e534c2fb2092773` |
| `runs/census-s12z/failed_roots.jsonl` (the final census) | 486450 | `9895be2f3ced47904dbdba7ad9e0aa9118b913542c03759b8b49b4639b46dd4f` |
| `runs/census-s12z/stderr.log` (its body trace) | 3600847 | `7083ecdb4ebf9ab4faa0ff3ff565cbe6bd467b4e22463f95299438b9823ed12d` |
| `runs/census-s12z.out` (its summary) | 1695 | `124a59a4675393a8583235abda60b414cd9120d14865d9d6266193915f2a7641` |
| `runs/dump-s12z/` (its uncertified bodies' queries) (118 files) | 1460826 | `21702e28f36f639df9c43564c32045af6501fa7a3a609b065a28223d9501a926` (manifest) |
| `s12/payloads/compare_z/` (`census/census_compare.py` against the baseline) (4 files) | 54638 | `984115140e60fc365fe6eefb20db9e7fbc1042f38c8c6f4013861ef254da7b49` (manifest) |
| `runs/main-f6dc.dylib` (main `f6dcad152`'s bridge, the landing baseline) | 137132412 | `856d82606c4a4fc5aec31182f81e8d2c0f6aae61a12fa8b0084efa4ba13b2028` |
| `runs/census-main-f6dc/failed_roots.jsonl` (its census) | 512078 | `8673fca2806b835c39e880ae135e6e421c71511995c8ab196a034874e90774f7` |
| `runs/census-main-f6dc/stderr.log` (its body trace) | 3693196 | `63f340fc47195ba79b910efc5fb6d8788b471413d972009ce25a45a1cba7bf2e` |
| `runs/census-main-f6dc.out` (its summary) | 1721 | `b552f3cc609fdc3297c1afc84fc5f2f52cd8baefd56dfb89bf11c94f80c90bb7` |
| `runs/s12-land.dylib` (the landing tree's bridge (`fca48f987`)) | 137350220 | `f9d3f9b9f0083e969c369484aed9224eb8e21b698b0e1d9b3bab89cddb2a7e3b` |
| `runs/census-s12-land/failed_roots.jsonl` (its census) | 411522 | `a6cac2d8fa0596486a79327c5b31cb1061de5edea62fb843151341a7d290ceec` |
| `runs/census-s12-land/stderr.log` (its body trace) | 3224829 | `4eeeb272033f2be6c68bc8b239dae5ec00e19ea0df0bfe7afede5452d85f21cc` |
| `runs/census-s12-land.out` (its summary) | 1715 | `9617487e9c12a58c51691ba3eb1fc462995c06aefc9b07ceab362678e6ce605d` |
| `runs/dump-s12-land/` (its uncertified bodies' queries) (103 files) | 1228430 | `ef4aec8eac355dd2dd7cf9d1d9655730a3798dcd798018b8f7c01823da365351` (manifest) |
| `s12/payloads/compare_land/` (`census/census_compare.py` against the landing baseline) (4 files) | 51012 | `65cbee9f357ba0e619c7047fe0d91fcf0e879798e5a866590a8659f7d6a18505` (manifest) |
| `s12/logs/qual_9_11_alone.log` (slice 9/11 host qualification on the landing tree, one process) | 33503 | `0202275be2dea67c0532cc850d6a12955df7c2cc8c0044207654f2b0cb441ec7` |
| `s12/logs/qual_live.log` (slice 9 and 11 host qualification, each alone in its own process) | 4981 | `5e901b56e64b8d5fab3812f34df327722dca148c823e02abd30d0accb7e0bb06` |
| `s12/logs/qual_9_11_ledger.log` (slice 9/11 qualification and verifier credit on the updated ledger) | 2311 | `54f18cd864235cd46356ac5578b1b9160c7b0972d726d0207a214d46af047f6b` |
| `s12/logs/gates_land.log` (`gates_full_stage1.sh` and the rest on the landing tree) | 2609 | `0b8df60b83416220aa4e398859bc363d8b1d5d5e9e1503094109526c0ebc43f9` |
| `s12/payloads/slotu128/` (`SlotU128` right-spine and balanced queries (300 s budget), paired runs on AY 12713, AY main and AY `8d6d17ad1`) (5 files) | 5281 | `3f329a595d862b74eca10f64ae4cec75956c4e6087c3f258ca6129cbd9355fab` (manifest) |
| `s12/logs/gates_stage1_premerge_ay.log` (`gates_stage1.sh` on `2316cdeac` (AY build 10530)) | 446 | `8ccc0ec714105759cc7ab3b4ff6072e155cca8d477e2adde27cd2be39a05179e` |
| `s12/logs/gates_rest_premerge.log` (the IR, lowering, optimizer and codegen libraries there) | 929 | `aca5c9fc379d164c337f46ebc09828dc9a8c19c58f0a8829ad3fea29a908c8cd` |
| `s12/logs/flake_rerun.log` (the envelope JIT replay test rerun alone) | 979 | `664405ea2505c0cdd21733fb38b1fb6301cb75321ec7aeb80281cc806f747a2c` |
| `s12/logs/notest_compile.log` (the `--lib --tests --keep-going` build there) | 7472 | `8bd42a33c92fd5b0ff266eee9e49552c13f6740015f9dfae3ad93adc6aabc43b` |
| `s12/logs/test_soundness_check.log` (`scripts/test_soundness_check.sh`) | 8672 | `5d2ae92a22d1527b47ebd4e2bd345434be824c32bb64c5e1f002889ca0b20a60` |
| `s12/logs/tippy.log` (`scripts/check_tippy.sh` (cannot run here)) | 62554 | `335b30a9aaf7395c3fe59460e8e893975d226be41ec3097b71e98a4d66e9c98f` |
| `s12/logs/gates_full_final.log` (`gates_full_stage1.sh` on the final tree (AY build 12713)) | 91 | `0eed2a634798f6cd20a4824c839d7203d6bfa4294c8b827e9d857e95b7416967` |
