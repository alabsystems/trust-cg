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
| `runs/main-5495.dylib` (the baseline bridge, `main` `5495c11b4`) | 128014028 | `6b33db1e1399f1022894cc6efb58807e3c8243d15f8231fa51094ae07f0ff7c5` |
| `runs/census-main-5495/provenance.json` | 1713 | `0d02bc9f2b106fe83577aa57a70ae8fd045ab9ed943b87bde8129cc07ed307ae` |
| `runs/census-main-5495/failed_roots.jsonl` (baseline failed roots) | 1268043 | `63cbaa5f85bccc2e4a59334ab61b246eed62e609202061c4d839556a4f132a0e` |
| `runs/census-main-5495/stderr.log` (baseline body trace) | 7502979 | `be6a85608c5195af5ab297a491fb642c5b6f1c6c614ed7c2ebb4f4fcd8b08d06` |
| `runs/census-main-5495.out` (baseline census summary) | 1707 | `02ca1a6320d70fa61f536a27537db5a885455fd2e2744b282ae3bb7a57023b99` |
| `runs/s11.dylib` (the slice-11 bridge) | 128051644 | `7ec2b0d7ba346d025ac7207f9d970f60f9c84fdd8cb6c7d62a9b2b8061e9796e` |
| `runs/census-s11/provenance.json` | 1695 | `6473d6a11a48dd5c7fc5903ddd09782df4fd25d7ae36faa99fbbabadb06fe4bc` |
| `runs/census-s11/failed_roots.jsonl` (slice-11 failed roots) | 1198669 | `a1f5bca5c995631496d759509a5ce703b6342dc5e5481059f38a02055c967c5b` |
| `runs/census-s11/gap_table.md` | 1842 | `76af0412c644bdea4201222de77d1b1bc942be5d2f23903eda2d527f92026a8e` |
| `runs/census-s11/refusals.jsonl` | 4414294 | `5c5913bff7a8fe61012d9dcd5752f01feafdc46d5c9e202b1419a0741169bc4c` |
| `runs/census-s11/stderr.log` (slice-11 body trace) | 7159317 | `f8a33673a44323dcc50a4f67049a7f4b8b2918d3a873b8776b04453696a76c34` |
| `runs/census-s11.out` (slice-11 census summary) | 1677 | `ea5512df30fc6e84a131ca114446798ddffaf71970c6e0076d8bce428979fc69` |
| `runs/dump-s11/` (the uncertified bodies' queries, `x86-body-dump`) (566 files) | 4174171 | `505e4a7297be8cc4c5260f7db2fb14dbabc537d693c92b425db3e6104ab763e6` (manifest) |
| `s11/logs/census.log` (`census/census_s11.sh` log, both rows) | 1114 | `11d4d9eedb7e61ecb3abe96d6726b747a1fe354cafb43eb5ac2f1273f242900f` |
| `s11/payloads/compare/` (`census/census_compare.py` output) (4 files) | 37139 | `ae8aa4ba87077ba592828b6f93e5205355c4b7793c915caf35cc8548b41e3e01` (manifest) |
| `s11/uncert_q/` (the 21 uncertified class queries, from the dump) (21 files) | 206833 | `1f41ef72ffcb5f9dad7d3a87dc2de82ef1e669cd9ecdbe3b1f944121caa09872` (manifest) |
| `s11/payloads/uncert_replay.tsv` (their offline AY outcomes) | 8962 | `6c8fbd63cdcf51ea79cdf6a28127e8d883fe36cfcca5d61de57ca6608ca09378` |
| `s11/ashr4/` (the four former `bvashr` bodies' slice-11 queries) (4 files) | 47365 | `dc96c4b70d0a2e7217cbbb5c966494c4f4e921bc649415c19db71b339f2e1ed8` (manifest) |
| `s11/payloads/ashr4_replay.tsv` (their offline AY outcomes) | 1544 | `827932bf6ba363ce04724d4c1e025733e3ef29e11faf3b42e8096d49a8fada5c` |
| `s11/cls_i128_param.txt` (the class functions, `census/split_classes.py`) | 11743 | `1b57d3c5071659ce3cea9c392e9c3917e7a48f421f14de6ef99d0c19dd814623` |
| `s11/cls_i128_result.txt` | 3105 | `627dbf03bf08ad90c16f8e996427794b294abee87f9a81dacb0690ac00307d16` |
| `s11/cls_float_param.txt` | 4410 | `85f750bab01acf2a5ee86ae9455158c1cba7c7603db62a7b1276f8648aba4135` |
| `s11/cls_float_result.txt` | 4375 | `caa92fd07501bb3817377a4afead12643ec5eb9e72b31424d0dd77623c8140df` |
| `s11/cls_nonscalar_load.txt` | 6570 | `437e28999f7649dddf5c03184c7a984c366cad0f11c30446beb431b07061648c` |
| `s11/cls_call_result.txt` | 2061 | `e9d8c24081f05264e5673d0ba607ee403da60291754f67d278c938dcf268e754` |
| `s11/dump_i128_param.txt` (their LIR and pre-RA bodies, `census/dump_class.sh`) | 755777 | `97e09ccc80f781181cd9c2458ba2a244a3ea5e6197df074ffdff48e84fb12eb5` |
| `s11/dump_float_param.txt` | 254843 | `3a5bc1e60b09a7fe98b92e15c409e6ee3f8cb7e8a286e89988591b6806a43ce8` |
| `s11/dump_float_result.txt` | 49661 | `b1316ba5e03aba193bd2eaa83e778dd80efd6b8af362549291cf411a07cd8161` |
| `s11/payloads/profile_i128_param.txt` (`census/profile.py`) | 9442 | `f09560ec4f933b21e76ebe15907a6244f29828983781899054230c5b9dfe32d4` |
| `s11/payloads/profile_float_param.txt` | 3888 | `3ee1435d26003203e7a755495fc967b19660ca945f360545ebc745ae7ef48449` |
| `s11/payloads/profile_float_result.txt` | 2896 | `9faa8c0e9e22bc1727bef4f9cfed4a1f9b40a6db531e1f534d42e1a26b89bfec` |
| `s11/sig_s11.tsv` (the slice-11 owner over the cleaned `core` module (`--sig`)) | 565237 | `75c9ca38909b34bd1b3159779b7563af727de54cd99bb7db10bbd0d6708efe66` |
| `s11/payloads/class_verdicts.txt` (`census/class_verdicts.py`) | 3463 | `3ce918ad116834582a1435d07304ed68d5ab19bb738fc04a0933145be100a4d2` |
| `s11/smt_cls/` (the bound class queries, offline) (91 files) | 368028 | `74fd4eb9a986faf95ef566569224351052e8be9dad681f4ad231c267d699714a` (manifest) |
| `s11/replay_cls.tsv` (their offline AY outcomes) | 18234 | `859df881f73dda32ec8f207f993ef4dc1fe6cc00271f8a06d35c6e0163dadabe` |
| `s11/payloads/fp_replay.tsv` (the floating-point probe (`fp/`)) | 1159 | `85ffcaff289610fad2f2e0394bfa2724e6715e8d9c15290b4dfb79d0727f9988` |
| `s11/payloads/qualification_first.log` (qualification with the first spellings) | 16236 | `dd8f9d841065b727dcddbce8e42bc849191c91893f67d089f5f5ad70b62b34aa` |
| `s11/payloads/qualification_second.log` (after the constant CL count) | 16031 | `324ed01342eb53534c2d64e2f60032890b1124b2057244cb2c65b8dd17110a88` |
| `s11/payloads/qualification_slice1_first.log` (slice 1 under the sign-extension spelling, before its records moved) | 10685 | `e918deeca881773b211ae40d50260fd998ee05249f65fe088424946abe0ed2d2` |
| `s11/variants1.tsv` (spelling experiments, `census/variants.py`) | 2382 | `7f60292de61ee40f2a87f6910cce6ac2d31d3ddef4e6c8216687a5f8c779b308` |
| `s11/variants2.tsv` (`census/variants2.py`) | 489 | `879d1ab0f58f856df5d28560240f85cb33b4cb7780cbc6ed68e1a46755e9f9dc` |
| `s11/variants3.tsv` (the census bodies respelled, `census/variants3.py`) | 10136 | `f77645eb3789f9bd7e906ddc521efdcafdbe44b121aeedb14ff760e577c84679` |
| `s11/orig31.tsv` (the same bodies unchanged, control rerun) | 9246 | `5a34ede66ffe1b245fa5cbfc1cf85a60fe988095bc167d6ec263f22bc7adcfc4` |
| `s11/payloads/qualification_merged.log` (`fails-before/qualify.sh` on the merged tree) | 31867 | `0bf3de84a75c822b3205572647934842fc1dceed70f4bbf23ac32329ccd69e67` |
| `s11/payloads/solver_free_body_suite.log` (the solver-free body suite and `smt::`) | 26891 | `1349646b8f35983daf178fdd22b2fbba07c421d2bb96aa00349b355c6e8e4cfe` |
| `s11/payloads/wide_extract_before_fix.log` (the same before the wide-`Extract` fix) | 19273 | `911e9c08f3da62016f8688b8cd547d4a47022e66cffea9e0327181a1dc040f2c` |
| `s11/payloads/mutants.txt` (`fails-before/run_mutants.sh` summary) | 9620 | `81c0c6993f9d7d48d9c1e4a5a107b127f83a90f15921f29f6bdd88ce9010c9f9` |
| `s11/payloads/gate_row.log` (`fails-before/gate_row.sh`) | 20606 | `86b2172d377dfaac8a4b78ab0771f817b46168a2db7b71d1079deced1e4436a3` |
| `s11/payloads/robustness_no_replay.log` (robustness probe, sampler only) | 1847124 | `1bb16ba28d6c7fd4b0024688e8d805178e8020338ef10a0c67d534702f65ccda` |
| `s11/payloads/robustness_replay_first.log` (robustness probe with AY replay, the first ground truth) | 1842565 | `f8dc8f820b64425839a8d529d31fbf2d0c27704cd6350fc2f679dc5ca7c841af` |
| `s11/payloads/robustness_replay.log` (robustness probe with AY replay) | 1839189 | `862a2d67e99d75303bca4c941c62a33aa12d0072236437295d8a43f239a4884c` |
| `s11/logs/gates_stage1.log` (`~/tcg-scratch/gates_stage1.sh` on the merged tree) | 1084 | `e22491b1b1e3577e79f03f006405fd71b0e729b7a4f2194e4ae7662be98526ea` |
| `s11/payloads/flake_rerun.log` (its two failures rerun alone) | 10353 | `6ad7c695191c9f524a7b1952a614fca12330bc5842bd13807340823dead6fde1` |
| `s11/payloads/e2e.log` (the codegen end-to-end body test with output) | 2277 | `44d29295b18e0177bc693dc205fe21093a8330087f5c1f9dc491d24d1b448ff8` |
| `s11/logs/gates_full_rest.log` (lower/opt/IR and codegen libraries and the CLI corpus (first run)) | 2226 | `8ccdcb12d8ea94fa7dd408864dc68ff6ca406b45ca98f31e4afef258daf918c5` |
| `s11/logs/gates_rest_libs.log` | 503974 | `11bb737ecab038a0f1873e7917ad9d360813d7ce0116ce81a3686df84f10d98d` |
| `s11/payloads/codegen_lib_first.log` (the codegen library, first run (six out-of-lane devices in the lane)) | 436859 | `5dd9569a593d36116d7078af464884cec963e8774fbdf834603aaf1efbfe7a00` |
| `s11/payloads/codegen_six.log` (those six (and one neighbour) after the move to a variable shift) | 1523 | `d0b144d2436e71ce23325395367e462138628fd626b3f5d3163ad12b934ca412` |
| `s11/logs/gates_rest_codegen2.log` (the codegen library rerun) | 365007 | `2b13f287cd23858fb383fbd1d3da996bcdba42618b4a5c53608ec879220ee76a` |
| `s11/logs/gates_rest_cli.log` | 2506 | `a3d53aa8f2fee75389b046b50335bb3715c13e78ec2793482016dada56356783` |
| `s11/logs/test_soundness_check.log` (`scripts/test_soundness_check.sh`) | 8450 | `dc99f0558654e523c182f761cece47deff918f19e012777044578b4504d90749` |
| `s11/logs/tippy.log` (`scripts/check_tippy.sh`) | 50065 | `7850133658a73d559eb7302b55dd8f4e797b9ea3bed50c40e3de292ca2767ed2` |
