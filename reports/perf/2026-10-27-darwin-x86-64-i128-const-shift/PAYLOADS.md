# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, binaries) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256; a directory's row is its total bytes over its
top-level files and the SHA-256 of its manifest (one line `<sha256>  <name>`
per file, sorted by name). `merge/payloads_m1.py` regenerates the table. The
README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `i128sh-run/final/summary.txt` (the gates on 3331ee136 (one line per gate)) | 1339 | `cf0347b16f0c9c5d2000aee1fb107af046d360c67285847caede4e577449725f` |
| `i128sh-run/final/lower_lib.log` (trust-cg-lower --lib) | 161605 | `a64f8dbd1d4eb8023c59f55c13fc92b8870e8d9eb61173750b7ea8b1c9c69369` |
| `i128sh-run/final/gate.log.summary` (the x86 body suite) | 119 | `183ae68fc7f134a1c78099ba57bdcad96397a4f19a13aee32629f3f2be316d7c` |
| `i128sh-run/final/x86_source_bound_body.log` (codegen --test x86_source_bound_body) | 447 | `7d494f3428d3a0e9df675931cbfb82399bd98c2e46ec0cca62011de103fd7b84` |
| `i128sh-run/final/e2e_x86_64_i128_const_shift.log` (the native differential (O0-O3)) | 323 | `f13d6bcb24f73c962debc4c43915cef8075e0e39ac8b2c4ebbe81c3c011f3e8c` |
| `i128sh-run/final/census_proxy3.log` (the census proxy over core-ir-s22 (17 functions)) | 4345 | `84d97535102fd3b1de824c97da37b6aea21c722a5b862a62aed49328cb6ee581` |
| `i128sh-run/qual_v2/` (the tool-gated lanes, one test per process (logs)) (8 files) | 53486 | `3120292486445443c2d53643c8c853229fc860ee0495b43875c34a554a871c57` (manifest) |
| `i128sh-run/e2e_v1/const_shift_optout.log` (the native differential with TCG_NO_X86_I128_CONST_SHIFT=1) | 2683 | `15322e5709b785885b5b5b6cdff0469005499e7d08f4862c56004b515bac8706` |
| `i128sh-m1/logs/build_m1.log` (the trust-cg-verify library test build on the merged tree) | 14620 | `416672f07c8acc7afa642fc11c1f0f2627b5869b7ff1357a25f5c4cbeff27aca` |
| `i128sh-m1/testbin_m1` (its test binary) | 490119176 | `1aa544f8767fdd417144da4d20da75dbc50c610a189f4f3879baacbab70ed257` |
| `i128sh-m1/logs/golden_write_m1.log` (every golden re-rendered (TCG_X86_BODY_SNAPSHOT_WRITE=1)) | 15371 | `44f5251e0e42621a171cb4989d38f33a2b676d09ab926aa02be9f68abd6bbeb8` |
| `i128sh-m1/logs/golden_write_m1.out` (the digests it printed (each unchanged)) | 1940 | `041dd263d2cf32d2d4a335ceb195d15cd9e22f35a05110f35e2547298c5c1969` |
| `i128sh-m1/goldens/origin_main/` (every golden on origin/main e74f215c6) (19 files) | 797157 | `a545038400f287d397079c6a9b7a3572aac6f1ca17113d81d9b139236aff7c1e` (manifest) |
| `i128sh-m1/goldens/bd2bbd3b9/` (every golden on the branch before the merge) (19 files) | 786215 | `d2968d097e67a8a4bdc0bd7b822ddebc1fe25faf032612d34ab9e7250a67d87d` (manifest) |
| `i128sh-m1/goldens/merged_m1/` (every golden re-rendered from the merged code) (20 files) | 805255 | `50171da3c84cafda482aa3fcf3ab0bec7bb5bed11ddc13fb36cb399ed77e4181` (manifest) |
| `i128sh-m1/review/out_vs_main.txt` (the review against main (claims, validity, z3)) | 1642 | `31e4727c93a0855fb8b2bbb7d5326c65b5eb15abbdf340dcf36b007c400729f5` |
| `i128sh-m1/review/out_vs_main/review.jsonl` (its records) | 1408 | `a50c03947a4cd7855d03f893012d2a478bfe9348b941e1bcaa38363821e649af` |
| `i128sh-m1/review/out23_vs_main.txt` (slice 23's strict review against main (names)) | 1188 | `ffef9929ee51e6002dcedcb3c8095fc17a3009106a155cedfb4a3b564d3a9218` |
| `i128sh-m1/review/out23_vs_branch.txt` (slice 23's review against the branch) | 1151 | `da1ddcffc784d51fd31e7df376ac49625f1cc52401f4b56bddd5513ee74c36f5` |
| `i128sh-m1/review/out_vs_branch.txt` (the claims review against the branch) | 1605 | `922bff0ac403dafbe7d3b1069bae7a7ba843862e1d608872f3b0482bb9053c74` |
| `i128sh-m1/probe/x86_body_probe.rs` (the probe source (s23-fix/probe's; never committed)) | 73740 | `7e67e3f4e65877a34a9fcf984e96eebef86ca8359ef14f34e6b0536d3e153d71` |
| `i128sh-m1/probe/x86_body_probe_m1` (the probe built from the merged tree) | 94649880 | `d6daa28fc080c8f5f9edf76962e5fdcd8073f076705b3a763a5c639b7f62a019` |
| `i128sh-m1/logs/probe_build_m1.log` (its build) | 9389 | `d836b50d7ad92f8a6c265830c022e24cffe01cbc18e7f41934e6429005655b69` |
| `s23-fix/all/w5/cf.tsv` (main's whole-core probe without the fold (slice 23's final head)) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `s23-fix/all/w5/cf.err` (its stderr (pairing records)) | 1524 | `35f54e33b14cc9dab09f629f648d217491e407745f9a7dfdd6dc702d75c110c0` |
| `i128sh-m1/all/m1/cf.tsv` (the whole-core probe on the merged tree) | 549105 | `298784c29067b910ecbdcd3fa03136e999fd895f06218eea4021157dc1f2b6c5` |
| `i128sh-m1/all/m1/cf.err` (its stderr (pairing records)) | 1524 | `35f54e33b14cc9dab09f629f648d217491e407745f9a7dfdd6dc702d75c110c0` |
| `i128sh-m1/all/m1/smt2/` (its queries) (4011 files) | 8358683 | `ef5c12e3fd41d6cf4739581ebf7408056a0f4fa706b0165c6d3992ece56693f7` (manifest) |
| `i128sh-m1/all/m1off/cf.tsv` (the same with TCG_NO_X86_I128_CONST_SHIFT=1) | 549097 | `dc0fa5d9c56a5f82beed38c7fccfd621309fae6116c096293e760690d5ebb511` |
| `i128sh-m1/all/m1off/smt2/` (its queries) (4013 files) | 8359913 | `06a0762ce29535f43d0586dd7d0759884bfffb88851a7526b6a9cdce6e6a6779` (manifest) |
| `i128sh-m1/logs/probe_diff_w5_m1off.txt` (diff -r of main's queries and the fold-off run's (empty)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `i128sh-m1/all/cmp_w5_m1.txt` (main against the merged tree, function by function) | 1660 | `3ecc1f75586358348cbdc44890995b6451f2dcaca83b94c9143ad0dc37b2b701` |
| `i128sh-m1/all/cmp_w5_m1.changed.tsv` (the 11 functions whose theorem bytes change) | 4111 | `4acc8c005ae0dca434e23f24e59670f38ddc706e3e23dcec9e4c933142c548e5` |
| `i128sh-m1/all/cmp_w5_m1.cf_changed.tsv` (the 17 functions whose selection changes) | 6863 | `bed2713e379a74554b897d71dfd149a5b9b787295b95c64c1c1eb7f55d8f13e1` |
| `i128sh-m1/all/cmp_w5_m1off.txt` (main against the fold-off run) | 138 | `9e49d4be6da907d5f876e3054fddf52928ae191cca4312cfe224019fe1ce1c98` |
| `i128sh-m1/all/pair_w5.txt` (main's 30 paired owners (S23-PAIRING lines)) | 1524 | `d59e6f1cf4948f96d278a998a763e131073a1e85ea7009440127ee753ffd6a9d` |
| `i128sh-m1/all/pair_m1.txt` (the merged tree's) | 1524 | `d59e6f1cf4948f96d278a998a763e131073a1e85ea7009440127ee753ffd6a9d` |
| `i128sh-m1/all/pair_m1off.txt` (the fold-off run's) | 1524 | `d59e6f1cf4948f96d278a998a763e131073a1e85ea7009440127ee753ffd6a9d` |
| `i128sh-m1/logs/chain_probe_m1.txt` (the probe chain's log) | 505 | `52085dc0707f6c6e3ec1daad5c69494a328785f39e8f1622e44a86e4b440dcab` |
| `i128sh-m1/stage/names20.txt` (the 17 and slice 23's three roots) | 2001 | `3209b6cb3ba8055dd9c129c8cc8d0d00c4ec1bdf0beae81ebe891cc3876a1f62` |
| `i128sh-m1/stage/m1/q/` (their units, claims, generalizations and arbiters, merged) (352 files) | 937513 | `c745dfc429a82294f2901aed637987a0d1d1ccec7bc55ca0614903307b86a6ac` (manifest) |
| `i128sh-m1/stage/m1off/q/` (the same with the fold off (= main)) (355 files) | 932114 | `a1618b934b11a2897d19bafc26ba97aab52d2e1a41f56c4a392593641dc0266c` (manifest) |
| `i128sh-m1/replay/data/replays.jsonl` (every one-shot replay (AY 13556, Clean 5f09e36c), keyed by the bytes' sha256) | 228332 | `ffb806be943bd645893554e893336764417b48e7120eb2299214e7793ebc578f` |
| `i128sh-m1/replay/chain_replay.txt` (the replay chain's log) | 2142 | `4392fc06e5c24d29492ea5404d4386fd184102c3c524e488656481c55b3f2949` |
| `i128sh-m1/replay/table_m1.md` (every route per function) | 3320 | `f009f0f5d40c23489222ee1d9203510b75168b7c373689d8f0c6960d990fe7a7` |
| `i128sh-m1/replay/route_m1.md` (the production route, merged) | 1935 | `8563d48160de86695bcf16208b2e0690939531426e904e0cda81ad01bd2f50b5` |
| `i128sh-m1/replay/route_m1off.md` (the production route, main) | 1971 | `4e61f46c4159c482c19d837d58ff4171019f979868a38a447eb8dabaab50ea95` |
| `i128sh-m1/logs/chain_gates_m1.txt` (the gates chain's log) | 2978 | `009b0fb33022281f7363184d225497a8852718fdce4d78989b0f38f8c5a2a610` |
| `i128sh-m1/logs/suite_m1.log` (the solver-free x86 body suite) | 51763 | `9c295f5e1a3e1549ea7a1f1242de467b2c126bab8eafb1fffe9ba14724f222a6` |
| `i128sh-m1/qual_m1/summary.txt` (the tool-gated lanes, one test per process) | 1560 | `0aa40c17ba406a69312bba13977063d9eb7c898783a5cfbedcf8aa76c5dacbf8` |
| `i128sh-m1/logs/lower_m1.log` (trust-cg-lower --lib) | 170017 | `1059ac90498c140a0ebea831ca334d10afb5377356f761aab11c9ac80dec2761` |
| `i128sh-m1/logs/codegen_m1.log` (the codegen targets) | 16210 | `89048b580f78856209ffbce63d8a0ef882f19236a6c19ada78351df4ce1515f0` |
| `i128sh-m1/logs/codegen_body_nocapture_m1.log` (codegen x86_source_bound_body with --nocapture (the replay identity)) | 4423 | `6b7d4cf94c101adc3dee946fe8d29b0162c77309477c8235be86635a3d9e1cc3` |
| `i128sh-m1/logs/census_proxy_m1.log` (the census proxy over core-ir-s23 on the merged code) | 5613 | `48ca321e2f5b64baf5ba6838c164f8c74a79003a86919f7f84ef02b101fb2e84` |
| `i128sh-m1/logs/fmt_m1.log` (check_fmt.sh) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `i128sh-m1/logs/doc_m1.log` (check_documentation.py --check) | 87 | `367a2819b366278854f46d55efa2665fcda90bf59ecc31cdd73cba6f9438e898` |
| `i128sh-m1/logs/matrix_m1.log` (full_test_matrix_hosts.py --check (PATH)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `i128sh-m1/logs/matrix6808_m1.log` (the same with TRUST_TARGO naming the 6808 targo) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/i128sh-6607.dylib` (the census bridge, `6607d0f6b`) | 145298928 | `393bc99d926404bb5965a252cdda281ab7be358d60317fd05a9989bc91236a9a` |
| `runs/census-i128sh-6607/failed_roots.jsonl` (the census) | 18382 | `c955ebddbeb010528ad9348b830714f1a3a5fb37856b24bffb29cbd06e7e03bd` |
| `runs/census-i128sh-6607/stderr.log` (its body trace) | 1301467 | `c86a036f89b13e2da035a3e10cdbbba9a67cb32140fcbb65686550afb332d535` |
| `runs/census-i128sh-6607.out` (its summary) | 1737 | `47052450f13f4c31c97baeeaacb44476b0e4e1e45b6d840a408cfd2e67296606` |
| `i128sh-census/compare/` (`census_compare.py` against slice 23's census) (4 files) | 317 | `7754fd74e30ef336648576fda47d488ff8b8c6ce3bb0d731ca3f0af9eb45cc1c` (manifest) |
| `runs/chain-i128sh-6607.log` (the census chain log) | 583 | `86d6f7ede20e8682eac0a29e971954885dce4469c8633c7cc0a0abcff8f76872` |
