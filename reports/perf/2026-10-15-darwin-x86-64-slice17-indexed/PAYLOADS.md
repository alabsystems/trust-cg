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
| `s17-design/data/functions.tsv` (the design's class: 51 functions, the group of each) | 8446 | `57e7f5ffdd22387144d7af1233732d32fe98a01bf42613c73d262f8e1e837eb9` |
| `s17-design/data/class51_names.txt` (the 51 names the probe is restricted to) | 3722 | `8a588fe97a8d1f2ede1e36289aadf3ae58e05b4b616ec8b76dd43d726a668dce` |
| `runs/core-ir-s9/` (slice 9's core dump (the design's input)) (88 files) | 5977212 | `8776e580c966c9f81c085885fd100f78da7de7dc9643fd78f539315bae0d6a69` (manifest) |
| `runs/core-ir-s16/` (the core dump of main a902's bridge (the slice-16 record's)) (166 files) | 6814351 | `a0469d5e8d83fbbe785fd8b6d21b8d0b99737c5e7fe33854d11f7f0e5fb75221` (manifest) |
| `runs/core-ir-2854ce/` (the core dump of main 2854ce's bridge (`census/dump_core_ir.sh`)) (128 files) | 6922152 | `d5090a7c92c082be4e8870bdc3aead4a956e67f3bc10bca47ee86d45ff97a6fc` (manifest) |
| `s17/payloads/probe_control_s16/` (the control: slice 16's probe over a902's dump) (2 files) | 14054 | `ef11335f55a4dae76dfdfc0e85514a74c6e7cd73021f7f3db419389932e2fa0d` (manifest) |
| `s17/probe/fin_s16/` (slice 17's probe over a902's dump (final code): verdicts, stderr) (2 files) | 8582 | `6e9a7b240ecabde21732addb34d54d62569744bfe6f5c220cd8cb9eba0430f2f` (manifest) |
| `s17/probe/fin_s16/smt2/` (its 133 queries and index) (134 files) | 839721 | `d092bcff14b4bed02a512901674abe5f5aa54493b38dd0462b85548f1f56626d` (manifest) |
| `s17/probe/fin_2854ce/` (the same over 2854ce's dump) (2 files) | 9283 | `d3a7cf222dd689e217cb1d47e6e81e546c6774bfca150ca6d94aadbd71ba94b8` (manifest) |
| `s17/probe/fin_2854ce/smt2/` (its 116 queries and index) (117 files) | 770677 | `2a7db323337c3344edff337c8e33fb84af144f13a643560ea96d8c08b100aea8` (manifest) |
| `s17/probe/control_2854ce/` (the control over 2854ce's dump) (2 files) | 14068 | `75acce50c91d8987c5d8bff51015094d288ad1b18eb7cf4990e588aea05b4038` (manifest) |
| `s17/probe/fin_s9/` (the same over slice 9's dump) (2 files) | 16606 | `86086af16ea4b343c74ac5620e2c5dc27d4fed9dbadcafd68072e97ecccf093f` (manifest) |
| `s17/payloads/measure_fin_s16.txt` (`census/measure_s17.py` over a902's dump, with the certification) | 16709 | `8988d405d1865d9ebe1eff097f87a77a18684d783560bce87f1e46dfaf9724de` |
| `s17/payloads/measure_fin_2854ce.txt` (the same over 2854ce's dump) | 17148 | `6eac1c87c3a8fdffa11d8c16e6348437bc238345edabf87036ecb483fcb4187b` |
| `s17/payloads/measure_fin_s9.txt` (the same over slice 9's dump (no replay)) | 16223 | `8facae63056954dc7c91c8c8f106db40c08ca824738b3d4574cdeada0723855f` |
| `s17/payloads/probe_control_s9/` (the control over slice 9's dump) (2 files) | 22077 | `b21ed2daef96a9e0ba4d06fd3451d76a086ad103288c4eabe6ac56d2eb286740` (manifest) |
| `s17/probe/agep_2854ce/` (slice 17's probe after the `ArrayGep` merge over 2854ce's dump: verdicts, stderr) (2 files) | 8509 | `662e5bd900104ed46752a27cfd6acf486f86e28a9611a5fa2fe12d32c59b4cc6` (manifest) |
| `s17/probe/agep_2854ce/smt2/` (its 126 queries and index) (127 files) | 831457 | `95ae187e3ecb48c3b822884aee4c8d724c8317762d1c36a2d01b2e522f6d4e84` (manifest) |
| `s17/payloads/measure_agep_2854ce.txt` (`census/measure_s17.py` over it, with the certification) | 16789 | `5e9e5f3e29aecee504a70747f2e65ea402b53b14d4d906040032428afbc9007a` |
| `s17/probe/agep_s16/` (the same over a902's dump (queries byte-identical to before the merge)) (2 files) | 8582 | `6e9a7b240ecabde21732addb34d54d62569744bfe6f5c220cd8cb9eba0430f2f` (manifest) |
| `s17/logs/lir_all_2854ce.txt` (every function of 2854ce's main CGU: its LIR and the owner's verdict (after the merge)) | 73744726 | `02530f0d84b8ce68a53652a75b22f69d4358bfd4002b584e898a13c2019f08e9` |
| `s17/payloads/arms_s16.tsv` (`census/select_arms.py` over the chain-spelling queries (arm counts)) | 3774 | `6f6384db95005bb4e9549aa058bf23c5063fbdf7cd06772c0f3333fa17f0a31a` |
| `s17/payloads/core_control/` (slice 16's probe over every function of a902's dump) (2 files) | 572895 | `97adfa2ed945cc09fdc3f8f52a09d2bcf808b4eef04881700e81a8bb5ddc5253` (manifest) |
| `s17/payloads/core_s17/` (slice 17's probe over every function of a902's dump) (2 files) | 567250 | `6f4ef71e98a9f7c2b8fe618d23a8877771f1159688f0615da8f3dea5efab8421` (manifest) |
| `s17/probe/core_diff_s17/` (the 327 queries the dead-byte rule changes (slice 17)) (327 files) | 1704106 | `99746c7acccac32c9ae8049dd41b34275f965ed49548d9c44bfe31aebedbfaba` (manifest) |
| `s17/probe/core_diff_control/` (the same 327 queries (slice 16)) (327 files) | 1892194 | `20415268a915d0bad3e3822c2cdb6a6c7ad1fc9372e8792dd0ce76cfea44b70b` (manifest) |
| `s17/payloads/replay_class_s16.tsv` (the class's queries, linear-chain select, AY 12713 with Clean, 30 s) | 6046 | `a1041eff7a465af0a8dc67db4fa8fa2b062130f2d6290226810eb2520dda5cc7` |
| `s17/payloads/replay_lowbit_s16.tsv` (the same, low-bit select) | 5454 | `17a353c614b48a76390826fed86bc328a5f43cb5f5a5a1b9c454161f99ce4a77` |
| `s17/payloads/replay_vn_s16.tsv` (the same, low-bit select and value numbering) | 5435 | `8d6ca5aec33579bf3c425691d387040b7e8fde284aff6bd7768ff3fc9a3f4292` |
| `s17/payloads/replay_fin_s16.tsv` (the same, final code) | 5430 | `acc745dca499158b4fbf60157e8024a110a66e0de4f631c9a335d408f05d43b2` |
| `s17/payloads/replay_fin_2854ce.tsv` (the final code's queries over 2854ce's dump) | 4715 | `41db87aaf95eeedd1b6a6fce8b3dd8980859abe13f4bc302bee7b5b10083af9a` |
| `s17/payloads/replay_agep_2854ce.tsv` (the final code's queries over 2854ce's dump after the `ArrayGep` merge) | 5175 | `021480e5e9dda85344e9ea24b00e994130dfe3350caa738337ed2fdd9440c858` |
| `s17/payloads/replay_core_diff_s17.tsv` (the 327 dead-byte queries (slice 17), 30 s) | 15940 | `c69bff19e2a221f0b2064030cd0a16bcaca6db8615541c5898d4c24794c72e37` |
| `s17/payloads/replay_core_diff_control.tsv` (the same queries (slice 16), 30 s) | 15934 | `dcfff5815e83eb19562482cc2d6d45ba4d700520522affdadf988d21ed327641` |
| `s17/selects/` (the 256-arm select, linear chain and low-bit by hand) (5 files) | 11071549 | `2840223e7509cad509a9f9a67722c81f3e42a9edb8e5fc55d8949f9bb6324d59` (manifest) |
| `s17/slow/` (StoreThenIndexedRead plain (73 s) and with its constants substituted (3 s)) (6 files) | 49207615 | `241d6a010602621e5a4b3e481a105e8d70c649e5d4bfac012c3b72e950cda516` (manifest) |
| `s17/payloads/qualification_final/` (slice 17's three tool-gated tests on the final code) (3 files) | 8583 | `40ccc502c11378ae3bbb1c2c008f2ce806f7f53e363d29013e8f5a7ba60e0add` (manifest) |
| `s17/payloads/qualification_agep/` (the tool-gated tests of slices 12, 16 and 17 and of ArrayGep on the ArrayGep merge, one per process) (7 files) | 35580 | `795c03c31fc3d668b00df860e7c3db2154f42ae0124c6a3b65b2bbda900191b9` (manifest) |
| `s17/payloads/qualification_agep/queries/` (every replayed slice-17 qualification query on the merge) (150 files) | 461549 | `ae333d29c07dd4e87922d891b3320ed8bd7915a4c39b56b17e61ba28f9b4e368` (manifest) |
| `s17/payloads/qualification/` (the tool-gated tests of slices 12, 16 and 17 before the ArrayGep merge) (5 files) | 23773 | `c7c7645c9379783203892372ebcd3f3a7f8c102c7c5df167ac37ec8351fe8bc9` (manifest) |
| `s17/payloads/qualification/queries/` (the 16 fixtures' canonical queries then, written without a solver) (16 files) | 62190 | `79d6972a47aba25e068358a408cf90d79860bc79cdde36981b41326a5ffb82cf` (manifest) |
| `s17/payloads/qualification_last_merge/` (the same tests on the merge of 4c6ce87e8) (5 files) | 23750 | `aac563f12a19a27e4b88699ab9ab6099235737e41b898452115227ef680c406e` (manifest) |
| `s17/payloads/qualification_lowbit_unnumbered/` (the slice-17 tests before value numbering) (3 files) | 20752 | `0b0bb0d842e34e09baf91f49a2e04e062d6b3f4426705d5ee574b6d512d27c5a` (manifest) |
| `s17/payloads/qualification_vn/` (the slice-17 tests before the bit-move substitution) (3 files) | 9844 | `e5cd6ed3f14ce1690b9ce982c7847b40b260e1469c7203336f623e8fee364232` (manifest) |
| `s17/payloads/gate_body.log` (the whole x86 body library gate (solver-free), final code) | 30632 | `2fbe52641be35a95026ca5e0a84eda7893e168b68646bcb409bce42948d09c69` |
| `s17/payloads/gate_slice17.log` (the slice-17 library gate, final code) | 1979 | `302ccd90391d2b93a9fb8088d51ab9de9effaeda63d9e4b7d519a871a1a746be` |
| `s17/payloads/mutants/` (`fails-before/run_mutants.sh` on the final code (15 mutants), with each run's log) (17 files) | 104395 | `04466b3822f3acd40c072852d463d1c06c8dc46702214d5408978ce2b8b7f9ca` (manifest) |
| `s17/payloads/mutants_agep_first/` (its first run on the merge, before the byte-bound control was fixed) (17 files) | 103240 | `d6cea020728cbd8b12c6a42cfa422a825b287b47976f8931609715e646ffcd5c` (manifest) |
| `s17/payloads/mutants_chain/` (the 13 on the chain spelling, after the control fix) (15 files) | 80936 | `6478c20e21c2ada543e1ab8d378f28bbb68b8ab9307c67836913317946cdb311` (manifest) |
| `s17/payloads/mutants_first/` (the first run, before the "machine in bounds" control was fixed) (15 files) | 78030 | `37d57a0d4a32603ba1b941c8067f91e5ad11201caae5344826739759864da9f8` (manifest) |
| `s17/payloads/robustness.log` (the robustness probe, no replay) | 108461 | `929c4d652aaeb5a6348a27427290a3f7cad11699e55eaf75adb0373b5df853aa` |
| `s17/payloads/robustness_replay_final.log` (the robustness probe, every theorem replayed, final code) | 109492 | `1eea25418ea747f9c8d33a787662cfe3738907a6b70a72c37fbc6ccc6670a3af` |
| `runs/main-6191f36.dylib` (the landing baseline bridge, main `6191f3621`) | 143109444 | `94e646ddbad8ab60a74fea47749c1096e629e188ce743a25f2cbbc9f978c4a9c` |
| `runs/census-main-6191f36/failed_roots.jsonl` (the landing baseline census) | 250593 | `714866463e4738054ab0addae63961716db4329008141518d8a5cf6392722422` |
| `runs/census-main-6191f36/stderr.log` (its body trace) | 1816377 | `7e71d995e09b032128cb480c76f83bc1153c544cb349ccb09a5fd4ed5854ebaa` |
| `runs/census-main-6191f36.out` (its summary) | 1735 | `df06dfe3f1a5349dcd028cd3c380f2db1055d9c5ccd706cf2e48de5d05835a37` |
| `runs/s17.dylib` (the slice-17 bridge, `ac8424004`) | 143283892 | `11290b17fa1c2fbc7758221a608da9b6f1c2fdee19874fe089c72170306b92c6` |
| `runs/census-s17/failed_roots.jsonl` (the slice-17 census) | 206027 | `d56e4a0864982aa2eba7623edd52b32643c45fb39de8e364a2e20aded5ee565a` |
| `runs/census-s17/stderr.log` (its body trace) | 1605393 | `05d5a980b4e74eb9114946592fdbbb60a3428edcca73e71af3deb536439b6e95` |
| `runs/census-s17.out` (its summary) | 1690 | `3e9cf28b4d60c9b3041a29cc224f820118c5ec8c27558dfa6740048d0c77c6e3` |
| `runs/dump-s17/` (its uncertified bodies' queries) (361 files) | 3294333 | `eef707c76c7199bf1c9de7629d21d46221960194a277105af88c9bbc0fa952e4` (manifest) |
| `s17/compare/` (`census_compare.py` of the two rows) (4 files) | 3808 | `f20ce25c54ff1de3fd568090bd4f1be412674f652bdae400a2edae5b7ab22b4c` (manifest) |
| `s17/logs/census_chain_kept.log` (the census chain log) | 1178 | `f253a2b0ba5568f7c15f63341d3e1e93551d73de40d0f877217fd5393fc85ffd` |
