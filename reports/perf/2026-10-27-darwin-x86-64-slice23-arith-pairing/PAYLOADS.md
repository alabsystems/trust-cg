# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, binaries) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256; a directory's row is its total bytes over its
top-level files and the SHA-256 of its manifest (one line `<sha256>  <name>`
per file, sorted by name). `census/payloads23.py` regenerates the table. The
README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s23-design/README.md` (the slice-23 design (§1-§7)) | 37840 | `dbc83a46365f05970401c0c45b0d61ab6d5a5599de5ec762d2391ee34c9eb8ed` |
| `s23-design/data/dump_sha256.txt` (census-s22's three dumped root queries (sha256)) | 253 | `b85910166599c8fe5989f4f7a9d14aa07414d26e10d605ac96b5fb756b4e277f` |
| `runs/census-s22/failed_roots.jsonl` (census-s22, the 23 failed roots) | 21510 | `46541325082da3ae6e86e9f281a83d8de6f03a3067f0052307f18357c0311464` |
| `runs/census-s22/stderr.log` (its body trace (the census outcome of every function)) | 1318993 | `bbc7f30b0fe989ddc24c5eb970e9df0729a13595f94cd3e6da78c467bd1f6640` |
| `runs/s23.dylib` (the release bridge built from this branch at `addf2c93f`) | 144907824 | `0f232201c1a61f5c99698c8f37b70a79b3c0778ff1743e1fc1975d1f311904c3` |
| `runs/core-ir-s23/` (the fresh `core` trust-ir dump from it (byte for byte `core-ir-s22`)) (88 files) | 6872172 | `afa61a7e32fe698511ce4fa5922ac2fd5dedf85563ad096c8b9d7740091a4626` (manifest) |
| `runs/core-ir-s22/` (census-s22's dump) (88 files) | 6872172 | `afa61a7e32fe698511ce4fa5922ac2fd5dedf85563ad096c8b9d7740091a4626` (manifest) |
| `s23-run/logs/dump.log` (the dump's log) | 152 | `744f0b8d8860ff27bf6f9b62021a153eb682fb89f97da8240c8223872cc314a9` |
| `s23-run/probe/x86_body_probe_p1` (the probe at p1 (the row-level gate)) | 93619400 | `6b6836abff82fc8828ea9649823f13985a826225e132bc73fa2a3fca61a6fe8a` |
| `s23-run/probe/x86_body_probe_p1t` (p1 with the pairing trace (never committed)) | 93678968 | `d3048087debc45d6a806ab5ecc5847d4f3564f86c96745fc23e22890ad909491` |
| `s23-run/probe/x86_body_probe_p1t2` (p1 with the full-context trace (never committed)) | 93678864 | `e85a55e43f799eb001cabfeb0c1d3af7cd78969033f1c0c78a6c197afae61797` |
| `s23-run/stage_p1t2/roots.err` (the traced run: each candidate row and the row-level gate's answer) | 39423 | `9b398032ccc30d238f8f9e9a934960a464b2abfd6aba1b24a16682c0475ebdc2` |
| `s23-run/probe/x86_body_probe_p2` (the probe at p2 (the theorem-level gate)) | 93641400 | `ff0fbffcf14a541d9171297bdc2965b334b28341dda360eb3c5f1057c8feaa65` |
| `s23-run/probe/x86_body_probe_p3` (the probe at p3 (merged with origin/main `4bf54e061`)) | 93650080 | `12ede996f6f59863dc5886fe5adefe8609915610809be4ae9caf828e3afbd14f` |
| `s23-run/probe/x86_body_probe_p3m` (p3 built with the rule mutants (TCG_S23_MUTANT)) | 93682376 | `2589139c2afb8f5bd21c31afed25f2986285a47a5116e53cfc07f7e1d97d9f88` |
| `s23-run/probe/x86_body_probe_p4` (the probe on the final code (merged with origin/main `c06393ad6`)) | 93651232 | `7112122a885849471d6ac7607c1d1c620dfc1440cf34995d82218d8aa0a99023` |
| `s23-run/stage_p1/q/` (the three roots' queries, claim splits and generalizations at p1) (77 files) | 473452 | `e329cadf7f171b9dbf28a22feed18ffc41635fc410ac24f23fc521378d7e9f60` (manifest) |
| `s23-run/stage_p2/q/` (the same at p2 (= p3 = p4)) (76 files) | 432024 | `59dc992c198bfeb2637cf43fe0f08c709d5dfcd5e7690444d495fdb932f7231d` (manifest) |
| `s23-run/stage_p4/q/` (the same on the final code) (76 files) | 432024 | `59dc992c198bfeb2637cf43fe0f08c709d5dfcd5e7690444d495fdb932f7231d` (manifest) |
| `s23-run/stage_p2/table.md` (the per-root route at p2) | 358 | `6374e0fb5f1c321ccc1020abea1c0cbd02c1701c36ed17948141224f0f4b7180` |
| `s23-run/stage_p2/align_all.tsv` (every align_offset query replayed) | 2654 | `9c03f748de0368f4a8f458727af69c21f3092c9f8595ec65e0119968b8d445fd` |
| `s23-run/stage_p2/pow_all.tsv` (every overflowing_pow query replayed) | 1168 | `6269601836b1a7c5c98a61338c3170cba2fb8f42b0ce0041c2a0818e87d468c9` |
| `s23-run/stage_p2/smul_all.tsv` (every scalar_mul query replayed) | 430 | `7bba1e5c393f5af5cb9791664ce933d19cceae9f8934e0f4d3cb5d1156c59ea5` |
| `s23-run/data/replays.jsonl` (every one-shot replay (AY 13556 + Clean, 30 s), keyed by the bytes' sha256) | 78767 | `adf184715949afbb97a444d617ea017bb175c8d38705fe0a236550f6decefda9` |
| `s22-run/all/c/cf.tsv` (the whole-core probe at slice 22 (22c; census-s22's bytes)) | 549097 | `27bbc0dbf39597b696d3ee2d281212bcb10b8bee49b9b2e607e6706f2307edc0` |
| `s23-run/all/p2/cf.tsv` (the whole-core probe at p2) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-run/all/p3/cf.tsv` (at p3) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-run/all/p3m/cf.tsv` (at p3 with the absorbed-pairing gate off (TCG_S23_MUTANT=pairing-never-absorbed)) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-run/all/p4/cf.tsv` (on the final code) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-run/regress_p2/q/` (the 15 changed census-certified functions' queries) (52 files) | 391347 | `1af4209fad750364e057abc798649cc896480e7237a729cf96d93212584f4949` (manifest) |
| `s23-run/regress_p2/table.md` (their replay) | 1899 | `673db51b7a8376e7aa28c12ae947655a8db349864690e1ad26bdc904876adca4` |
| `s23-run/stage_grisu/table.md` (`format_shortest_opt`'s route with claims and generalizations) | 411 | `1051fb8f4c8632e5e394db255a4fed152e95545e91535b5ae867eef327678445` |
| `s23-run/goldens/pre23/` (every golden before slice 23) (19 files) | 796261 | `a46d765655cce3349c93f551608774fc1a77d9d7ea99042d806461e7e092ab75` (manifest) |
| `s23-run/goldens/new1/` (every golden after) (19 files) | 790240 | `beb5c9e4cbdca98f7542b0ccd6371111f60217d2945aad699c8a69ea3b70a3e0` (manifest) |
| `s23-run/goldens/review1/out/review.jsonl` (the review of the 5 moved theorems) | 733 | `3ceca940c3776903de660e2b210e4952e7c28f18a0a044754d03439c4446f3ad` |
| `s23-run/mutants3/summary.txt` (the mutant run on the final code (one log per mutant beside it)) | 6145 | `1b57fe1706681ab4a3d83817b040ca061c9661739618656f3516dbea7b94a90c` |
| `s23-run/gaps/offline300.jsonl` (the four slice-23 exact gaps replayed offline at 300 s) | 2025 | `1c00059ae409cdf226bdf368890edc1223f2920121a4b1a4a063ee8127958316` |
| `s23-run/qual_final2/summary.txt` (the final qualification, one test per process (53 lanes and the deadline-bound lane)) | 5603 | `c71ab637e38d2dcdffb3dfe1576ad8e02cb73157b01b57048782a815aa09302a` |
| `s23-run/logs/suite_final.log` (the solver-free x86 body suite on the final code) | 47463 | `99d0473048199acac2e0155aa4092ceb1460e3ff7558fe0a8f8057635ee92eff` |
| `s23-run/logs/codegen_final2.log` (the codegen body and must-refuse lanes) | 2407 | `98e54462acc1c1cf504ab78219534def6ee8054edb0f847996a6f2be79400a36` |
| `s23-run/logs/lower_final.log` (trust-cg-lower --lib) | 160686 | `183ded854072444a78f329cf18b6b9d738341330d4114ff008146617f074f904` |
| `s23-review/stale_rdx.py` (the review's z3 script for check (3)) | 904 | `26c950e849844be137eb150897b9767d71c9ef738c9f82ae256d1fdaf6fe7c94` |
| `s23-review/shift_sem.py` (the review's z3 script for the shift keys) | 1032 | `9a86159a44fa8870eb8ca94563afed844cf865bdd239c62e3aacb9187c4853ae` |
| `s23-fix/logs/s23_w2.log` (the slice-23 and negative-memo controls on the fixes (2acc76c22)) | 7393 | `bef020d6a09b7e3c04fe32bfa3369af7549b65c05a337569c419f91039bde9d1` |
| `s23-fix/all/w2/cf.tsv` (the whole-core probe on the fixes, before the merge) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-fix/logs/probe_diff_w2.txt` (its diff against p4 (empty)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s23-fix/mutants/summary.txt` (the 20 mutants' run (one log per mutant beside it)) | 10644 | `224c0f9d29e3da0700892f07f3ceb1b3f5b267be0a363613f97bf2f163827b12` |
| `s23-fix/logs/suite_w3.log` (the solver-free x86 body suite after the merge) | 48944 | `4d9c117780fccd9350e72525a5c6b920b767223ea4a8742395e0159c447b66e4` |
| `s23-fix/logs/codegen_w3.log` (the codegen body and must-refuse lanes after the merge) | 12494 | `8c335114782a830d33a224d3930f545298453353734814f1d14a29348743f62e` |
| `s23-fix/logs/lower_w3.log` (trust-cg-lower --lib after the merge) | 169035 | `3b5ae101bfddc0618e51f5665176ea6fe1cafa8023d54baca022d78c877b91b1` |
| `s23-fix/logs/cli_w3b.log` (trust-cg-cli emit_proofs after the merge) | 13344 | `7f2a06a8fd475e8519254bad8ebac918f5eb8d47f421f28309c1b1f5a7b1a42e` |
| `s23-fix/all/w3/cf.tsv` (the whole-core probe after the merge) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-fix/all/w3/cf.err` (its stderr, with each paired owner's pairing record re-derived) | 1524 | `35f54e33b14cc9dab09f629f648d217491e407745f9a7dfdd6dc702d75c110c0` |
| `s23-fix/logs/probe_diff_w3.txt` (its diff against p4 (empty)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s23-fix/qual_w3/summary.txt` (the touched qualification lanes after the merge) | 827 | `6c71a66e8e9c3df255d9cbf46433390ea8250c22f30024ef8ca501fc871f5790` |
| `s23-fix/qual_tm/summary.txt` (two lanes under the mutant pair-stamp-only) | 271 | `f7f772c8f5f03d0dfda93c0476059b298819bff4e53442401e61af9ed7fc1f4d` |
| `s23-fix/logs/suite_w4.log` (the solver-free x86 body suite after the second merge) | 49060 | `bfce0eacb806709a6070f986af905dfa050db1bb0efa2ea66a5c5c8379f47e7f` |
| `s23-fix/logs/codegen_w4.log` (the codegen lanes after the second merge) | 10874 | `d4e1f27dfbb56a8e814da80e765d27a1ea8918b310fb0ab6df6c1e55131c0d4f` |
| `s23-fix/logs/cli_w4.log` (trust-cg-cli emit_proofs after the second merge) | 11536 | `f57903b2b0766e18dc488d48389207420fb8fd3859d6b61be52481e35e04ad1b` |
| `s23-fix/all/w4/cf.tsv` (the whole-core probe after the second merge) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-fix/all/w4/cf.err` (its stderr, each paired owner's pairing record re-derived) | 1524 | `35f54e33b14cc9dab09f629f648d217491e407745f9a7dfdd6dc702d75c110c0` |
| `s23-fix/logs/probe_diff_w4.txt` (its diff against p4 (empty)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s23-fix/qual_w4/summary.txt` (the touched qualification lanes after the second merge) | 830 | `d226318921f6c8ee00dbcfab50b160d1acd6492e4d5454001f4b2a4931508ccb` |
| `s23-fix/logs/suite_w5.log` (the solver-free x86 body suite on the final head) | 50639 | `207cc45c5b89e728e8b9ff21547b96fe92d3d6a58ddea86b1248fe56d7d8b185` |
| `s23-fix/logs/memo_unit_w5.log` (the negative memo's unit tests on the final head) | 2834 | `e5a4639f86f8379589a4537827b649c5545c8f2badbbeadc2c6672f3b8a1b2b9` |
| `s23-fix/logs/codegen_w5.log` (the codegen lanes on the final head) | 11879 | `cdefc9b57105c1fa95419c267cdb15226a00b34f814e456c97757cb8fb74683c` |
| `s23-fix/logs/cli_w5.log` (trust-cg-cli emit_proofs on the final head) | 12541 | `551461e9dcde874cd38bfe40359cb9dbb1c4174f631344a74f7be0becf6d2211` |
| `s23-fix/all/w5/cf.tsv` (the whole-core probe on the final head) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-fix/all/w5/cf.err` (its stderr, each paired owner's pairing record re-derived) | 1524 | `35f54e33b14cc9dab09f629f648d217491e407745f9a7dfdd6dc702d75c110c0` |
| `s23-fix/logs/probe_diff_w5.txt` (its diff against p4 (empty)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s23-fix/qual_w5/summary.txt` (the touched qualification lanes on the final head) | 825 | `303d4726c55945e570a0cc1b38c12ca82fa840db990299e3cf0baa405a384a37` |
| `runs/main-1fb7.dylib` (the census baseline bridge, main `1fb7620a5`) | 145126560 | `71236c17df079ef7fc3371dd52fcfe6c892fd5b1bf95dc62dbd6d058abf1e994` |
| `runs/census-main-1fb7/failed_roots.jsonl` (the baseline census) | 21510 | `46541325082da3ae6e86e9f281a83d8de6f03a3067f0052307f18357c0311464` |
| `runs/census-main-1fb7/stderr.log` (its body trace) | 1319008 | `081f89500bd1fa89e4d8f1e6c64e27052b49db8358e31cc5304c57f43051769a` |
| `runs/census-main-1fb7.out` (its summary) | 1727 | `d1072b9d5277bbe44a87a448da01ba65a8d5c964287c9f1338a95e547a13c32c` |
| `runs/s23-f2a0.dylib` (the slice-23 bridge, `f2a032c4d`) | 145284056 | `e01bfcec4de07b2ef368bae67aea8cb0a70544c1be34bf51f70198d95d409604` |
| `runs/census-s23-f2a0/failed_roots.jsonl` (the slice-23 census) | 18382 | `c955ebddbeb010528ad9348b830714f1a3a5fb37856b24bffb29cbd06e7e03bd` |
| `runs/census-s23-f2a0/stderr.log` (its body trace) | 1301755 | `94ed789ef68dd6f5c94a1e1d8c2ced046203a9b1a0ac9b83c5f3d3b5ae691c2b` |
| `runs/census-s23-f2a0.out` (its summary) | 1722 | `d52d7f47efb268d6767197464f37ea3b502c54ada2c59c1fcf64a5f61f3184d0` |
| `s23-census/compare/` (`census_compare.py` of the two rows) (4 files) | 644 | `6a95bee2f73adb6665b0bd1235239810e0caee2f1c0fd4e096260f7e985413eb` (manifest) |
| `runs/chain-main-1fb7.log` (the baseline census chain log) | 702 | `67a74e2ab2cc62a1e33cd0a6de72b149e75eddf8ecf9b2b74ce0881bf8f0ef33` |
| `runs/chain-s23-f2a0.log` (the slice-23 census chain log) | 580 | `0ad51df7d1e40a61cf28a48135110a0c0ddf880b91d717f812f2474f3299836e` |
