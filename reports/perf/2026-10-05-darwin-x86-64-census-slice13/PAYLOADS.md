# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree,
and its payloads (logs, root lists, outcome tables, dumped queries, the
bridges) out of it. These payloads never entered the tree; they live on the
measurement host under `~/tcg-scratch/` (paths below are relative to it),
and the README states the numbers each one carries. The SHA-256 of each pins
it; a directory's is the SHA-256 of its manifest (`census/payloads.py`
prints every row).

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/main-6b10.dylib` (the baseline bridge, `main` `6b108b81d`) | 130988952 | `abf52e172bf17124063fa2e5dd499cbac63c7e04ebd39805ee3b416825077e68` |
| `runs/census-main-6b10/provenance.json` | 1714 | `67147fcefd6a219e9c53a60e6f1ae3be2a5bc65b2b4a25bd67ea5586334700e0` |
| `runs/census-main-6b10/failed_roots.jsonl` (baseline failed roots) | 1161438 | `f7b27afa63f8643b60879ce2d1b635640c4998ca3dbf5f2fdceefbffbfa97f3e` |
| `runs/census-main-6b10/stderr.log` (baseline body trace) | 6985702 | `fd73b11f04bbe80e066cf6d958ce1e01c780e8b8f484a5c54eb09bbf64ce156d` |
| `runs/census-main-6b10.out` (baseline census summary) | 1708 | `c0a1ba8634b4c14c8c40c1f0acf5382d5da8f31cf0ba8208087a06cc65cec74a` |
| `runs/dump-main-6b10/` (the baseline's uncertified bodies' queries) (618 files) | 4777314 | `28b5710350920e2ce28d7c1c181ac6c270705130f1e68c0e73cf2591a8f6e73d` (manifest) |
| `runs/ay12713.dylib` (the build-12713 baseline bridge (the requalification's)) | 130998792 | `dc0f68b920d2ccb58cd814a6bbdb7b8f5e304d3d09499b50d1c289ca74707285` |
| `runs/census-ay12713/failed_roots.jsonl` (build-12713 baseline failed roots) | 646702 | `ebd84fc8502f3ad2d20c455b8c20500f54d96feadc714d49b2fada56f17886f4` |
| `runs/census-ay12713/stderr.log` (build-12713 baseline body trace) | 4368796 | `514c2f93fc7ffb3bfd20d2c39de7a9c60d6683efb9afc8dd2dc75df929027458` |
| `runs/s13-12713.dylib` (the slice-13 bridge, build 12713, from `90608b684`) | 131543496 | `01fa4c3a40dfc22895ee2f05815b415f379fcb3da6ec8c5041e399ca2eb8a542` |
| `runs/census-s13-12713/provenance.json` | 1718 | `8752f678eed050d4aa6b14716827488e5f39977ac256d12354cea4477256a723` |
| `runs/census-s13-12713/failed_roots.jsonl` (slice-13 failed roots) | 560559 | `c40628cb9403a31cf72e9621a8f3b48856660afc35239c718d8ce7b173c27253` |
| `runs/census-s13-12713/stderr.log` (slice-13 body trace) | 3954616 | `7adc25e8b3a051f631717513debad850c1118ffa0a4a9dedc418529b6da14c07` |
| `runs/census-s13-12713.out` (slice-13 census summary) | 1720 | `04f6d2a5a60ba41f0924ccb7e42bcebd3bca5afcbb475cf5cfa57867f62e2f55` |
| `runs/dump-s13-12713/` (the uncertified bodies' queries, `x86-body-dump`) (109 files) | 1319124 | `8e54b6e712ab475c29557450daf6ec029bc09533b354c105428768b790a0060e` (manifest) |
| `s13/logs/census_main.log` (`census/census_s13.sh` log, `main-6b10`) | 556 | `ac31c186b85abcf830c11a86a8902db8c8d22b6e3184cbc50ca1234b7ed1e7f5` |
| `s13/logs/census_s13_12713.log` (`census/census_s13_ay12713.sh` log, slice 13) | 602 | `5433ef327691876105dd770fae76786a0be3873ca61033696bfe1f93176dcb60` |
| `s13/logs/bridge_main.log` (the `main-6b10` bridge build) | 4576 | `48a7b0cbb48fbf954829d85c70fb0041d036bea18ae6c2b34cfaac7136059516` |
| `s13/logs/bridge_s13_12713.log` (the slice-13 bridge build, build 12713) | 129 | `b3ebe215ddc28120216a997ce701e6d932fef5cd5aea008c04d598a4e5d57bae` |
| `s13/payloads/ay12713_roots.tsv` (build-12713 baseline roots by function and last trace) | 169262 | `1684ec9a718c64b2af8b283d67c32c012cce8abb174578e3f73eea0e64293730` |
| `s13/payloads/classes_ay12713.txt` (its class counts) | 402 | `2f3e085214c00f8a3aa5872f57fb222cd39d776089b4c82c11304f31d626305f` |
| `s13/uncert13/` (the 9 uncertified class queries, from the dump) (9 files) | 130329 | `c704b2c61e369850cfcb3d15f7e58cef20f7dd5db997729c590beb2123571daa` (manifest) |
| `s13/payloads/uncert_replay_12713.tsv` (their offline production-protocol outcomes) | 1273 | `b0c15916d3db0da37655522f37078424a21a6104a520d6b0b423c174eb6e0f07` |
| `s13/payloads/uncert_replay_12713.log` | 39 | `0da61f889befd164bd5654a580c492a29852218894a087b10876a239347f2253` |
| `s13/payloads/main_roots.tsv` (baseline roots by function and last trace, `census/roots_by_class.py`) | 266595 | `47476d7c366b20f288402ab9fe1b69e82c630748eaa5cb1c9c342ddb61ee1eba` |
| `s13/payloads/classes.txt` (the class counts, `census/split13.py`) | 402 | `2f3e085214c00f8a3aa5872f57fb222cd39d776089b4c82c11304f31d626305f` |
| `s13/payloads/classes/` (the class files) (11 files) | 58330 | `9c3c469bbead3e8ce790d742014cfe7ce0d9b8610222daa55d1de3870dc931f9` (manifest) |
| `s13/payloads/compare/` (`census/census_compare.py` output) (4 files) | 39104 | `88fb3e433eee313fe9b1ba3464df6da85578cd54e6876c5f60822b95f95537f1` (manifest) |
| `s13/s11_roots.tsv` (the slice-11 census's roots (the first measurement)) | 273160 | `193b143e46b8642d1e60090d81f467b8ca736dcb394168831d8b4a4bb99d8e3c` |
| `s13/s9b_roots.tsv` (the slice-9 census's roots) | 280320 | `cee7521bcdfbfce927a79ed18da16627189249c3cdd037f97c6aec12eb57c00b` |
| `s13/dump_escape.txt` (the stored-address bodies, `census/dump_class.sh`) | 1021814 | `e971eaf50b1bb9f5138b5b92e734f630d8e1801e4f5974dd88b6cf2f77d5c384` |
| `s13/dump_params.txt` (the stack-parameter bodies) | 622854 | `d85a3191b871a885677f339a3ed00a1dcfbbe3ee0dd8c8305b27a4bf6464b504` |
| `s13/dump_call.txt` (the call bodies) | 795069 | `fc2dff67a50f5651ca3409f46ce4b772cb93e9f5368cff2496e2e4cb894c5a87` |
| `s13/dump_mem.txt` (the memory-routine bodies) | 37461 | `c078858f4e1b8b4512366cbfd64091f97a57d7e998f2cb80440dcfb3d216ced1` |
| `s13/dump_atomic.txt` (the atomic bodies) | 384342 | `f59e55b20bbb934fcf787fecf8af8df67db4b397a9d8f35a657f117dd1e28f91` |
| `s13/dump_boolload.txt` (the bool-read bodies) | 118312 | `365c847883207a0c65aa033d7159e7bbc84adc1b4d8547e85124e85d680c1fe7` |
| `s13/sig_main.tsv` (`main`'s owner over the cleaned `core` module (`--sig`)) | 559099 | `4c745b048d3b5a5b194a855f81e20f672c3bd3481e0d095bf60b39376fc82fd4` |
| `s13/sig_wip.tsv` (the slice-13 owner over the same module) | 546699 | `3443a6cbd4951f05967a819d0a8af4a7875333dc39d97dc6d759ae3a3e1149a1` |
| `s13/payloads/qualification.log` (host qualification, 20 fixtures and 15 refutations) | 48357 | `2325b6a31e8d3796be73be6f9bae4d187617d50dc10b392a3f9c06b7cef34869` |
| `s13/payloads/mutants.txt` (`fails-before/run_mutants.sh` summary, first run) | 7071 | `176c65581b9b2858151bc2aa30eebe69b557647c02107469cac1a88d53dfba19` |
| `s13/payloads/mutants2.txt` (the two sharpened controls) | 657 | `856c2741d09d201b51ce2b417d1cdb2064d72ece5a5007ecf97be89ef4179e38` |
| `s13/payloads/mutant_logs/` (the per-mutant test logs) (23 files) | 260649 | `f00e21a47de288feb8c1eae3f9ad42936a645763d09a45179127a8c7ddf2c1b8` (manifest) |
| `s13/payloads/robustness_no_replay_first.log` (robustness probe, sampler only, first run) | 341142 | `9b56ed30e7ffa63edccf67638bc3de280c73f6ab4321e616c42aa3a3dea29b53` |
| `s13/payloads/robustness_no_replay.log` (robustness probe, sampler only) | 313658 | `76ee8ddb6699d3742ff8f8b8ca821ab2a525e3b6bb69c22427e61beb293e4d2b` |
| `s13/payloads/robustness_replay.log` (robustness probe with AY replay) | 349607 | `0cf2f99b4980f913ef070b461a4b6402e2da98759dbdabcd5d65d5a2d0994506` |
| `s13/payloads/e2e.log` (the codegen end-to-end body test) | 4717 | `bfdd190be0bd9cb4188048a6b36860f327d69d4fbb2f0a7eb2956371dc7e29bd` |
| `s13/payloads/test_soundness_check.log` (`scripts/test_soundness_check.sh`) | 8665 | `6dca9417c74cbc4c383d0ea2b0372befd1ca762239ec1567dbd8c90119af6f0e` |
| `s13/payloads/gates_b10530.log` (the branch gates on AY build 10530) | 1629 | `789b832b803ccb4309e7a4be2a159c35050fe2e9c53c1053890554e92356c11b` |
| `s13/payloads/flake_rerun.log` (the memory credit test rerun alone) | 11033 | `eb413a76af6e576f52fe40d0041b23958c0d5850152adc19e9c69690fcda31ef` |
| `s13/payloads/robustness_replay_19.log` (robustness probe with replay, before `TwoAddrsToOut`) | 314745 | `d195e43527af74803c0d24c8acf27ca73a93e89fc9214ef512aa1963aa51fb0a` |
| `s13/payloads/qualification_ay12713_trial.log` (slice-13 qualification on build 12713, merged tree) | 53666 | `8b0075d63847ffc513829d48c972294ee4db223913a095b889dd787065c326bd` |
| `s13/payloads/e2e_ay12713_trial.log` (the end-to-end test on build 12713, merged tree) | 3040 | `d7ecc1771f815ac3c78ed484daec254185df3cd20161195e8862fc6d13aa1a59` |
| `s13/payloads/robustness_replay_ay12713.log` (robustness probe on build 12713, merged tree) | 349886 | `2ee7933a6375ffde2be8a675390989e547876ded0064e3096cd0915af8cd6d73` |
| `s13/payloads/gates_ay12713_trial.log` (the build-12713 gates, merged tree, beside the requalification census) | 2045 | `9977ef3913f6c36266f94a3e869e34c4e21dabac172c0fb0004499c7991959c6` |
| `s13/payloads/qualification_serial_ay12713_trial.log` (their failed qualification tests rerun serially) | 2258 | `abeb6b0b5cefae4aff093924b0773251fee0ff7018eea71d39af88db7714ec18` |
| `s13/payloads/build_x86_tests_trial.log` (every x86 test target compiled, merged tree) | 1330 | `b23ecd639942d77244752dc6f3e4c459a36d156441c51a2b1946f6d03866a603` |
| `s13/payloads/verify_body_serial_ay12713_trial.log` (the whole verify body library serially, build 12713) | 54379 | `46b2e19f82045b0ae8b9ac560f6bc8c2f342d44c365821dcd7636649172fbd7e` |
| `s13/payloads/requal_tree_memo_envelope.log` (the negative-memo and envelope tests on the requalification tree) | 22264 | `06c1f7b4f5a1299c0bae438f17c69a78756790287cade7b5cadf657326400946` |
| `s13/payloads/merged_verify_ay12713.log` (the verify tests on the merged tree, build 12713) | 10891 | `c8dd030e5e96d13af518354904eddfca5f2f7e4ce005e86aed8a62ac798339d3` |
| `s13/payloads/merged_codegen_ay12713.log` (the codegen tests on the merged tree, build 12713) | 124308 | `47a24399c342be29ed25a79cebd469fbc41e71bbee7f287a13461d109888864c` |
| `s13/payloads/test_soundness_check_merged.log` (`scripts/test_soundness_check.sh` on the merged tree) | 8665 | `6dca9417c74cbc4c383d0ea2b0372befd1ca762239ec1567dbd8c90119af6f0e` |
