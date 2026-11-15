# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, JSON, root lists, outcome tables, the bridges) out of it.
These payloads never entered the tree; they live on the measurement host under
`~/tcg-scratch/` (paths below are relative to it), and the README states the
numbers each one carries. The SHA-256 of each pins it; a directory's is the
SHA-256 of its manifest (`census/payloads.py` prints every row). The
baseline failed-root file's hash is the one `main`'s census record
(`../2026-09-27-darwin-x86-64-census/README.md`) states for `90ccb1b0b`.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/core-ir-s7/` (the slice-7 census's dumped `core` module, the bridge's `dump-trust-ir` output) (88 files) | 5955551 | `0ab3e31b3bf45f87d2afb4e806373ef18fab7754349ea5af51c397e6ce11fe27` (manifest) |
| `s8/core-ir-clean/core.trust_irbin` (that module minus the 149 bodies this tree's adapter refuses, by `census/clean_dump.sh`) | 4700635 | `09a5cfe68bf40e50cf40626a141bfee56801c69f46dca80c6f2031b0b025b259` |
| `runs/main-90cc.dylib` (the baseline bridge, `main` `90ccb1b0b`) | 125981580 | `331425bdeb50b4c0ccd29f9640252e001c019d7fa17d982f8c22b7b7fbf6dcef` |
| `runs/census-main-90cc/failed_roots.jsonl` (baseline failed roots) | 1770685 | `4f41fb62e4bebfbb1898233e76a290568ad1374239e3901e6efc4f9be22bd619` |
| `runs/census-main-90cc/stderr.log` (baseline body trace) | 9951037 | `9ebf3ba2e10ea6d07f64d88b17effe271b3067f1a5c588fb25911521c79da96a` |
| `runs/census-main-90cc.out` (baseline census summary) | 1628 | `44e099a5dc355ef7490d10efd52c0ac46d794bebca58edf60b45682078ea0eb4` |
| `runs/s8.dylib` (the slice-8 bridge) | 126032972 | `2ab4611d19ea333fea929464ff36d7840a953f3e02c4e93d71e3352adb239558` |
| `runs/census-s8/provenance.json` | 1614 | `b2c15e8b559f10e4379cec326ff76b2738218f18f323eb770a69c93e50bf9b3d` |
| `runs/census-s8/failed_roots.jsonl` (slice-8 failed roots) | 1362196 | `e7faf323ad9e59d70ab1b3aa599f66738defc69f92de4150f95701e377a7077c` |
| `runs/census-s8/gap_table.md` | 1842 | `36b319c10da0be7e86ce24dbc53397bfcca8cad915301cff7b81568fee50277d` |
| `runs/census-s8/refusals.jsonl` | 5021562 | `129d7324ccc9fd5b051d2464af099bcc14575fd0679d10809348f7a1c3cf7ec5` |
| `runs/census-s8/stderr.log` (slice-8 body trace) | 7974117 | `fdcda8a25ceeac58663b48f6c130ba1bbab552410a096e4c1671a55f02cfe782` |
| `runs/census-s8.out` (slice-8 census summary) | 1601 | `63a5e78fe4426f5c99f97d25b451997294eff7191be9169114d384820131316e` |
| `s8/census_s8.log` (`census/census_s8.sh` log) | 513 | `c370b9b8b6bd9a01c56e81de12b8537a5b383de4198681a84f01ae495fe5e6da` |
| `s8/census-compare/promoted.txt` | 43368 | `2b2fd38599db41bb556be43c984c0f36120ee95fee5cd137ae499c69cb9fd6c2` |
| `s8/census-compare/newly_failing.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s8/census-compare/body_trace_classes.tsv` | 7095 | `87a87894d98e34485b9e3bc075e1f3257e7f0d9a901f50b40aad8777eb01aea4` |
| `s8/census-compare/slice8_transitions.tsv` | 4742 | `67aa44d81b888771491f4e6d4dca90905f8f7d45508da696ab16023b97917643` |
| `s8/census-compare/compare.txt` (`census/census_compare.py` output) | 12488 | `8d6ed0abdb996951e32032746240b7f9ef6031d345073a774f429f915d0a64fc` |
| `s8/census-compare/promotions.txt` (`census/promotions.py` output) | 2098 | `9025343d811912b10703055dbf74d6bae1d30a3d954d47b6ea90fea7cf5c0708` |
| `s8/census-compare/root_classes.md` (`census/root_classes_s8.py` output) | 2569 | `1b7bfedde9ea07ea5b8d19f5bd5b9b7b17c80f650ce6f8e4c2607734cb9b8c48` |
| `s8/sig_s7.tsv` (probe `--sig` with `main`'s owner) | 680936 | `36ae066d7714a6b049d6682a0b31cb0e8864179d411e6107edcd895b686abcee` |
| `s8/sig_s8b.tsv` (probe `--sig` with the development slice-8 owner) | 620833 | `33493d13ce606be604fe2025a1e8ce26528693b12c9e3042a96876278889e8f3` |
| `s8/bucket_s7.txt` (`census/bucket.py` output (the class table)) | 1648 | `c78abb80fb2043c9865d5087cfacaff5e82b05f116b4b9796663ab18fbdf515d` |
| `s8/offline_transitions.txt` (`census/offline_transitions.py` output) | 1752 | `0d9245de2ff76385a70f15d192c7a3f114c3454b339dcb7dc6dfcdfe99aac32c` |
| `s8/qualification.txt` (`fails-before/qualify.sh` output) | 7664 | `1f8cbe7413ff342251b618e75e003b9eaafb1cae3db254345824826045dba0a2` |
| `s8/gate_verify_full.txt` (the verify body gate (158 passed)) | 18064 | `759e554b6d37da29962091fdb60441c36d20d20b8df5f1e3b662008f4c4633be` |
| `s8/gate_row_slice8.txt` (`fails-before/gate_row.sh` output) | 7195 | `8f8925fc9e6883af762894c7914fc808d952bdb376708e97e62540badc7366b8` |
| `s8/mutants.txt` (`fails-before/run_mutants.sh` summary) | 5059 | `1b56b5b0505b4c015ea79b81376b31581f28e864e60256a0bb35a2dcc4e22017` |
| `s8/robustness_no_replay.txt` (robustness probe, sampler only) | 548918 | `8c86aab36516daa343621424316b186c104ceedbff0cce83f08a72097d70232f` |
| `s8/robustness_replay.txt` (robustness probe with AY replay) | 549505 | `7d72b63526f37c5dbaabd00536e0fb1557da99e6938b81e9468c868649d250b7` |
| `s8/e2e_and_must_refuse.txt` (codegen end-to-end and must-refuse corpus) | 61216 | `4f0262251cb76991c1ce4240d2c782f0f164d3334f0800b8095b22354218e2a7` |
| `s8/credited_O0.txt` (cross-backend matrix, credited functions, O0) | 478 | `f68925ea375ff0b6384eb7851ac93ed429af9150e34da7d4d1a2abe89b76b9ff` |
| `s8/credited_O123.txt` (cross-backend matrix, credited functions, O1-O3) | 6131 | `dbfc69203afaf037bb305912835b4bbdff306c3d06d4cc88e432865ab3eeb389` |
| `s8/all_O0123.txt` (cross-backend matrix, all fourteen functions (`S8_ALL=1`), O0-O3) | 1268 | `137ca38af091ba4d7d36dc159f10f41f7ce6c2371b329d8201947c2b84c0674d` |
