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
| `runs/census-s13-12713/failed_roots.jsonl` (the measurement row's failed roots (the slice-13 census)) | 560559 | `c40628cb9403a31cf72e9621a8f3b48856660afc35239c718d8ce7b173c27253` |
| `runs/census-s13-12713/stderr.log` (its body trace) | 3954616 | `7adc25e8b3a051f631717513debad850c1118ffa0a4a9dedc418529b6da14c07` |
| `s15/s13_roots.tsv` (its roots by function and last trace (`census/roots_full.py`)) | 143790 | `d3c7d97c6d2c2b76b7d165a7577c1c9f439b9ddc96c25fbc62e1b5054d2ae4a4` |
| `runs/s15-main-cf98.dylib` (the baseline bridge, `main` `cf982f936`) | 132067888 | `16c09ce3bc3ec1acce5d56c1310e7721bca7287127024ec7715c56b2fc31873b` |
| `runs/census-s15-main-cf98/provenance.json` | 1730 | `7433dec7b61c392f7e6ed454a82fbb223f0d1cf378ada79e187f8951dc517206` |
| `runs/census-s15-main-cf98/failed_roots.jsonl` (baseline failed roots) | 566642 | `e8721450a7f0293deb3681de10f141fd1acf76498e31a38b3e5c345b68b562fc` |
| `runs/census-s15-main-cf98/stderr.log` (baseline body trace) | 3974685 | `205ff15fee812c44ba91559bc57e92df3de00281915d2440c07c33d6b4fd2286` |
| `runs/census-s15-main-cf98.out` (baseline census summary) | 1740 | `84bfdc14091d9814c95e56262712b4951b7cd712defd50a0967fa65f5f17ef6c` |
| `runs/dump-s15-main-cf98/` (the baseline's uncertified bodies' queries) (113 files) | 1348556 | `052a8a307a239f17b9e457b416d295973f3278927e6666145366586c988846b2` (manifest) |
| `runs/s15-cf98.dylib` (the slice-15 bridge, `6770368eb`) | 132104528 | `ebf1e17ebc9ed116bc87e0b7e6905bb152ce5a1b3d9dd6d2798dffb1012d8e35` |
| `runs/census-s15-cf98/provenance.json` | 1715 | `e2852e69f329e543e5a534f0e84db9d11f95f78ef7362de98a50cb9e5ce390ab` |
| `runs/census-s15-cf98/failed_roots.jsonl` (slice-15 failed roots) | 530761 | `55cd27fb2da7837c9f2a6c67b773b6c5b2ab58f6cf837f219bc1582749271a16` |
| `runs/census-s15-cf98/stderr.log` (slice-15 body trace) | 3779503 | `b1afd36468e50e307bd26f628502d436f6c24950f0e51045941591fec94ba945` |
| `runs/census-s15-cf98.out` (slice-15 census summary) | 1715 | `244b62fa6296228a46c1877bef5015b435643fc5b97d296543ed2993de9bbe9b` |
| `runs/dump-s15-cf98/` (the slice-15 uncertified bodies' queries (`x86-body-dump`)) (124 files) | 1445034 | `92643d901732b7e130d91fc4e177e85eff36373bc38d3362eed3c6bfe11be0b3` (manifest) |
| `s15/logs/bridge_main.log` (the baseline bridge build) | 263 | `71e5c820074c8413dde6d1f39a989a9045edbec562a60ed841c648aef8415caf` |
| `s15/logs/bridge_s15.log` (the slice-15 bridge build) | 258 | `2fcd2ba719e5044b9ee23ba9cc021d97278bf020c13b8d2fbff33156ebe06aee` |
| `s15/logs/census_main.log` (`census/census_s15.sh` log, baseline) | 606 | `f221703d490f3f85a02a1a9e9d7046a20a74217ad879a8b5379794512948f371` |
| `s15/logs/census_s15.log` (`census/census_s15.sh` log, slice 15) | 601 | `9280324359a764b3038637d80daaffe0db44bb3471b537f64d48af39ee5d7022` |
| `s15/payloads/compare/` (`census/census_compare.py`, baseline to slice 15) (4 files) | 32086 | `73bc6071d5eb0ac25b87802220f49c9fa664a5089b6a23ba593f2d6359dce386` (manifest) |
| `s15/payloads/compare_main_vs_s13/` (`census/census_compare.py`, slice-13 row to baseline) (4 files) | 37032 | `372f0ad6b784a45b69403d14cf560561ecf66b5a9c78d60f545d7a383410220d` (manifest) |
| `s15/uncert15/` (the 9 uncertified class queries, from the dump) (9 files) | 93804 | `ca2685bb659d7be3ee532b6425272e9176d8a91b2f217e970265418fed73796b` (manifest) |
| `s15/payloads/uncert_replay_12713.tsv` (their offline production-protocol outcomes) | 2099 | `50305b180f068abb90e9fa965f28b195d6e72a009b0e18d32ae846e5722faf34` |
| `s15/payloads/uncert_replay_12713.log` | 39 | `cc908579d41409c36ea5cffe79310c668065e3c31fb37b36678cd541eab992cd` |
| `s15/payloads/qualification.log` (the slice-15 gate row and host qualification, 22 fixtures and 14 refutations) | 13793 | `79b3db1d541d20bcf16ab4f86430c49e2716dbb013148edd469f70952007c7ad` |
| `s15/payloads/mutant_logs/` (the rule mutants: `mutants.txt` (final), `mutants_first.txt` (the first run, a transcript copy of its summary: the file itself was overwritten by the rerun), `mutants_base.txt`, `mutants_alu.txt`, `mutants_lower.txt` and each mutant's test log) (29 files) | 514473 | `c4b681c05f949f43b3965c12275b54fa22d858916bc6554e0dd3b6cea893ef1f` (manifest) |
| `s15/payloads/robustness_no_replay_first.log` (robustness probe, sampler only, first run) | 475881 | `964b869dc2ca13c41619ab394b09168fe14cbd7e9b0bfa9dd9896f0d4504e7da` |
| `s15/payloads/robustness_replay.log` (robustness probe with AY replay) | 482475 | `180a90cc8a8b29149905481059d1b75abbf0cc02a305cf1c673996b0dfc482bb` |
| `s15/payloads/e2e.log` (the codegen end-to-end body test and must-refuse corpus) | 125051 | `dd02234c7ce626c059249aa305fb3cb69178d99930188616f275cf2c7aceeb7d` |
| `s15/payloads/e2e_rerun.log` (the end-to-end body test alone) | 4078 | `c769d75134de961a05ec97b58bb240e7f2178d7eae7a1332ff7f8ac4d351306e` |
| `s15/payloads/e2e_without_slice9.log` (the promotion test with slice 9 left out (diagnostic edit)) | 2425 | `61175c55f5ea3f625109e26ce0556f5e24b369eb3c063cea7fb91e3d19be20a3` |
| `s15/payloads/check_merged.log` (every workspace library and test target type-checked) | 9397 | `0d86aef3f1659042ec3e83f9136c81ab3cee8100f977cbe56c7142a313663dc9` |
| `s15/payloads/check_merged2.log` (the same after the second merge) | 2794 | `5c8441f7d110a1bfe7bb6d6c2aae547c69a8672dbe4d4a0420bbce1e49a29e6b` |
| `s15/payloads/check_verify_after_fix.log` (the verify crate after gating main's unused import) | 2917 | `69310aa89c350d1f7c4189286447c86c745d10cab043002ca918b3f8a7162066` |
| `s15/payloads/qualification_merged.log` (the slice-15 row and qualification on the second merge) | 13791 | `619740c5267bcc0e5141158e78ef4cdfd1962f7f425a104e3f5c9cd1f351f7d1` |
| `s15/payloads/verify_body_serial.log` (the verify body library, serially, with AY and Clean) | 45978 | `789d1219b6a22d7006ff1eb148d1409750875b749082d94446649c1c148f2056` |
| `s15/payloads/rerun_slice9_memo.log` (slice 9's qualification and the memo test rerun) | 24975 | `efe95ae6d9cd3d76792d1b93a74e64f916567279ab19564218802e9edcff329e` |
| `s15/payloads/libs_ilo.log` (IR, lowering and optimizer libraries) | 504061 | `10cc4747ad10acec0c80088a761e76ee5fbfac146d5678ccfe1751e5361aa5d8` |
| `s15/payloads/libs_codegen.log` (codegen library) | 366058 | `81b7d63789973c457b10904b8fc5aae7022c1ddbdddb0972f114e749d419acf7` |
| `s15/payloads/cli_must_refuse.log` (CLI must-refuse corpus) | 2506 | `703b31ba3c3faa8f35869fd127c1bbf1b3af76e3eb5bbeef407e933531186cb7` |
| `s15/payloads/test_soundness_check.log` (`scripts/test_soundness_check.sh`) | 8774 | `9623140b8f2b5637790d6ffe1eaa2060382e00050f73c97dffa99c6c532c8319` |
