# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, job files) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256. `scripts/payloads24c.py` regenerates the table
(`scripts/write_payloads.sh` this file). The README states the numbers each
one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s24c-design/README.md` (the slice-24c design (§0-§9 and the addendum)) | 67710 | `7c444004c081e28b71e0df22a4b6b61ac09bddeefd04d7a2c2144540ca3bcb17` |
| `s24c-run/logs/job4.log` (the first P6: a pure-test header rotated, nothing if-converted) | 71975 | `dbbc7c2a129c7726197e0e4d3b7fa1ca4dfdb2290e40cc29398fdc0b88745351` |
| `s24c-run/logs/job5.log` (P6 from h(0, 0) refused at the loop entry edge; the cut-pairing and N7 probes) | 113895 | `937d28fe50a927a758f93a4ecc0010d589e929221fefd1dcb78623c39b64359e` |
| `s24c-run/fails-before/copy1_x86_source_bound_body_slice24c_tests.rs` (fails-before, first copy (its recording test did not compile; superseded)) | 42154 | `9300c317ebb8be97515f18a5c6020d1e00ca8f2f08d29480af3f1c900de217c3` |
| `s24c-run/logs/job6.log` (its compile on a617488aa (the borrow error)) | 10597 | `e02de8b1a191361468eccf16aa5a0dcefc41e3eeb3d909d5ea924d003114f329` |
| `s24c-run/logs/job7.log` (the module before the golden digest and the O0 record, and the golden write) | 100008 | `97e5cb0b0680861ed64c2386632c42f1920a3bab449344a730b02e4332699dc7` |
| `s24c-run/fails-before/copy2_x86_source_bound_body_slice24c_tests.rs` (fails-before, second copy (the record)) | 42325 | `5ca8384b776b2b3df807bf027091f8c48429d971ccd0cb54b28a509b20ef70f7` |
| `s24c-run/logs/job8.log` (its run on a617488aa: every outcome and the S24C_O0 lines) | 88534 | `28879cc7bcf0796b8ee5beede19faeca3a0b6a1873c35ed953e4f7d97889d0f2` |
| `s24c-run/logs/job9.log` (the module with two surviving mutants (flags, check-off), and the slice-24a module) | 41598 | `bc37092557076f075f151509895df41b9baeadce9f82c670c44df8d5d7cd9c58` |
| `s24c-run/logs/job10.log` (the printer and the module on the final code (13 passed; the S24C_MUTANT lines)) | 93917 | `0d8622de52219df244befffd89a95b37302d64253f749630f6f97a3d6b474386` |
| `s24c-run/logs/job11.log` (gates 1 to 5 at cdfda5a59 (gate 2: the LongDiamond Timeout, not yet recorded)) | 502515 | `cdb7308cf8b67299424add564346f05f761338524c06747b5544e5cfa424c25d` |
| `s24c-run/logs/job12.log` (the offline 300 s replay of the LongDiamond query) | 1429 | `4ce147cd5ee9fd6ebadda009816a0e282acc39492caeb2e8f72c1c60dcd9faed` |
| `s24c-run/offline` (its query copy and outputs) (1 files) | 6344 | `a46077da804d9652b9fa3fa72ba1a495373f33cf81562c0fced916ecea736d0f` (manifest) |
| `s24c-run/logs/job13.log` (gate 2 on the lane head, the gap recorded) | 61219 | `ea274c62fc46d09f3b2b4c0380d3c7008b4d58299b59cabc48edc54a9fe39653` |
| `s24c-run/qual-dump` (gate 2 and 3: every replayed and refuted query) (211 files) | 358995 | `933e739dbe078fc3759e150adc1b47b9b285a546732756d1425665977437a3c0` (manifest) |
| `s24c-run/queue` (the job files the queue ran) (18 files) | 14920 | `6ba4142f21c783d2c00bba469d3ebf46f04e0127d29558ab9ca502f24d7345e9` (manifest) |
| `s24c-run/logs/server1.log` (the queue run's own log) | 766 | `624e3a4cb667f21ad91de44d1dcd477deed25274956caaac6e0d4b276323101f` |
| `s24c-run/logs/gate6-fmt.log` (gate 6, format) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `s24c-run/logs/gate6-docs.log` (gate 6, documentation) | 87 | `367a2819b366278854f46d55efa2665fcda90bf59ecc31cdd73cba6f9438e898` |
| `s24c-run/logs/gate6-matrix.log` (gate 6, the full-test-matrix hosts check (silent on success)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/o2-s25.dylib` (slice 25's release bridge dylib at d92b944fe, which census-o2-s25 ran (also bound in slice 25's PAYLOADS.md)) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/o0-s25.dylib` (its byte copy, which census-o0-s25 ran) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/o2k-s25-nifc.dylib` (its byte copy, which the ceiling census ran) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/census-o2k-s25-nifc` (census-o2k-s25-nifc: slice 25's bridge at O2 without if-conversion or cmov swap (top-level files; obj/ not bound)) (7 files) | 3479010 | `54df3ef275afc38a962194861d8672dbf389658bc50b5b7184d9bd9ebec7a846` (manifest) |
| `s24c-run/logs/census-o2k-s25-nifc.log` (its log) | 805 | `5cfb12195d588ea11505ef53c16e5792fad216cc986b406ad8ffe820fd413263` |
| `s24c-run/census/nifc` (its comparison with census-o2-s25 (compare, promoted, newly failing, transitions, both root-class tables, ceiling.log, SHA256SIZES.txt)) (8 files) | 30224 | `401d55e95287bb6d081d04af1f39c61f9e5bf3446f02328b044a67a2245c2809` (manifest) |
| `s24c-run/census/nifc/ceiling` (the ceiling attribution: ceiling.txt, candidates.tsv, roots.tsv) (3 files) | 136680 | `4b655dbba230ed579971772767c6a079a87360659e13490509a0bd6e08d58ae2` (manifest) |
| `s24c-run/census/nifc-s24a` (the S24a-base nifc comparison (378 -> 339), moved here byte for byte) (4 files) | 47654 | `bd090c53c254e3c87fb2fc97d7a8bceb8a521c3df985593950e2cf4ad7cbb46b` (manifest) |
| `s24c-run/logs/census-o2k-s24a-nifc.log` (the S24a-base nifc census log) | 1943 | `34504553096b3f803620630fed977f9ddf65634722402d419152f1ad73221056` |
| `s24c-run/logs/server2.log` (review round: the queue run of job14 and job15) | 272 | `a273ee73920d779a90893f1e131e614f22e84b0af4cb25421cad32cd00b2faf6` |
| `s24c-run/logs/job14.log` (review round: the module on the working tree (P12 in one part, N8 refused by the loop admission)) | 21612 | `0f50bf5543412cf31e7ddaed8389fe820a5237865b0089e092f2a6ae797e2e88` |
| `s24c-run/logs/job15.log` (review round: the three qualification lanes on the working tree (two composition Timeouts and SlotJoin, not yet recorded)) | 36372 | `bb9cf97f63ecc41d7e59315e98bc1671ebfc5c567d6d83e5617e0499c1ec6fc1` |
| `s24c-run/qual-dump-r1` (their replayed and refuted queries) (23 files) | 50849 | `a44e2111a1f4eaa33bcb67a34ddad0ec98fd0684371b69555332d4fc1096aaa7` (manifest) |
| `s24c-run/offline/r1` (offline AY replays of SlotJoin (30 s twice, 300 s), Diamonds5 and DiamondChain (300 s)) (10 files) | 73292547 | `96e536d5307d0553d0356530e5dd48b346bcb7db68afbfb1e7d11a5b26330342` (manifest) |
| `s24c-run/offline/r2` (SlotJoin at the 30 s budget, twice alone and three at once) (8 files) | 36639474 | `6bb5935493efe037fea21354db46d7949441cec1f844eb14aa852c0a2f60ba7f` (manifest) |
| `s24c-run/logs/server3.log` (review round: the queue run of job16 to job19) | 428 | `2577b1d2d582ff5e818e41a35f7fff5031d1e899128355b5d2ff6f7a398aacd5` |
| `s24c-run/logs/job16.log` (review round: the module on the working tree, P12 and N8 rebuilt) | 35699 | `fe2d67d7004eca9c5dbfbcfc87b2eb36abd6a40c2303ef1ebf381a238846418e` |
| `s24c-run/logs/job17.log` (review round: the three qualification lanes on the working tree, the gaps recorded) | 40196 | `0b203e7b2d761061ec79b234cf9ca8fb94b38616563690b2faadaf357c855e4a` |
| `s24c-run/qual-dump-r2` (their replayed and refuted queries) (24 files) | 53355 | `ef0ef90768f5dfde648b60c08a26ff9456bf87d710d591eb9146756cd3aa5991` (manifest) |
| `s24c-run/fails-before/copy3_x86_source_bound_body_slice24c_tests.rs` (fails-before, third copy (the review round's fixtures)) | 62000 | `332cd44dd5a2cc1260bb65961439973cc06229463496bc898f208b23e5f11b85` |
| `s24c-run/logs/job18.log` (its run on a617488aa) | 99656 | `ccbbf5b58110fbefd21dd0ff4c20a0cc8422adf6e69abd50cb605ee142fe7bb0` |
| `s24c-run/logs/job19.log` (review round: gates 1 to 4 on the committed head 177d144b1) | 348749 | `4ceddeb9c0260685b7c227cd8d45513946d516b0e7ce311d9497086b8fb61c67` |
| `s24c-run/qual-dump-g2` (its gate 2 and 3 replayed and refuted queries) (219 files) | 396722 | `e67129cd506d292ce9dd7d19918fa8168d617d81a13ae842a11e1c592e5b680b` (manifest) |
| `s24c-run/logs/gate6-fmt-r2.log` (review round: gate 6, format, on 177d144b1) | 182 | `f84345c894e69f192d2a67721c47a5f0399bf47698b7784949ca07a75abc064a` |
| `s24c-run/logs/gate6-docs-r2.log` (review round: gate 6, documentation, on 177d144b1) | 117 | `dce097d8ce922b228ee2dd45cd2d98b97586a93c2d4c5f852e086db1249f4aa8` |
| `s24c-run/logs/gate6-matrix-r2.log` (review round: gate 6, the full-test-matrix hosts check, on 177d144b1) | 32 | `ebb6139623c8b23b3e27544258a1757ceffe19dc80800ba8d7d277af9b51de51` |
| `s24c-run/logs/gate6-fmt-r3.log` (review round: gate 6, format, on the final tree) | 208 | `cd955cb4174194e09886fc4673e0c5fd3088a200db3a36c01730c9018b111f03` |
| `s24c-run/logs/gate6-docs-r3.log` (review round: gate 6, documentation, on the final tree) | 143 | `4cd23c9798f6423e93b351f82620da4681032711a51287285e0ad4a5e66eca61` |
| `s24c-run/logs/gate6-matrix-r3.log` (review round: gate 6, the full-test-matrix hosts check, on the final tree) | 58 | `269458aef5341e0685d8efd6daa58ee42691b7ecdcf5118fac98f33ad042d428` |
| `build_bridge.t011.sh` (the bridge build helper census.sh runs (release, the t011 overlay)) | 2190 | `ed29e39bf5644e74ef7fdd74137a6a20130356801fb30fbdc8158cc870acaac6` |
| `census_t011_dylib.sh` (the census driver census.sh runs on one bridge dylib) | 2167 | `010b9d26fc7c07ad9e0df03c408f178bafb12c86c09f6973e9508a29ae5c2a7a` |
| `check_dylib_tools.sh` (the dylib preflight census_t011_dylib.sh runs) | 671 | `b1d0aedd8c3b5ecf1fbdae4891119c27736cd05f8b6018db1e6cde1b5fdb4a6c` |
| `s24c-run/logs/census-s24c.log` (census.sh: the bridge build at 38feaf386, the O2, O0 and O3 censuses and analyse.sh) | 35520 | `dd6d29700a256084acf6f8b6bde475400d004ab5c8b108c3b7a03d2467ca8d7b` |
| `runs/o2-s24c.dylib` (the slice-24c bridge dylib (o0-s24c.dylib and o3-s24c.dylib are byte-identical copies)) | 145750312 | `ca167574b51ed9f9f5e3bb38b08c1eac40d436ee74d9ab2a28574fe7f4b9300a` |
| `runs/census-o2-s24c.out` (O2: the census driver output) | 1720 | `cf0a2501855af2e2b09ec078c86ecf851d21e6d69c5210972c6ab85f1fb3213e` |
| `runs/census-o2-s24c` (O2: the census outputs (failed roots, refusals, stderr trace; obj/ not bound)) (7 files) | 3549510 | `445984bf7c70826cf0ebb920a1e000bdd18b7ceeb44925248ddf1abc69e6d3f8` (manifest) |
| `runs/dump-o2-s24c` (O2: the dumped queries) (7 files) | 9601 | `abeaee99fcb2968a59b57b3092a21d901adda164de8ede30d63aa51e8aecd3c1` (manifest) |
| `runs/census-o0-s24c.out` (O0: the census driver output) | 1717 | `1e9c60ba8bbcd5f35a253ae890e9bc5d80199ff9bed3b2137d14bac8b3c1ec58` |
| `runs/census-o0-s24c` (O0: the census outputs (obj/ not bound)) (7 files) | 1398551 | `0d3ba8975ade94e6b7b645f31faf23d99a79fbac90e7c4e7cfdd46af699b0d1d` (manifest) |
| `runs/dump-o0-s24c` (O0: the dumped queries (none, the directory is empty)) (0 files) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (manifest) |
| `runs/census-o3-s24c.out` (O3: the census driver output) | 1719 | `0d65f5f308382633ab33274a386d83a2220970f60a840f29833a58ce913125a6` |
| `runs/census-o3-s24c` (O3: the census outputs (obj/ not bound)) (7 files) | 4075714 | `118492d1d08d59f3fafdeba664da64df37392b4151f9429751d72ca778130995` (manifest) |
| `runs/dump-o3-s24c` (O3: the dumped queries) (9 files) | 10922 | `a31f407986125dde3188fe29065854c24a656054c1634edc5f8e21e28dcf65b3` (manifest) |
| `runs/census-o2-s25.out` (the O2 baseline (slice 25 at d92b944fe): its driver output) | 1714 | `d3dea4def568298ee9d161d3d0609e7a894ad843decd0ab69072ba58df8d1ebd` |
| `runs/census-o2-s25` (the O2 baseline: its census outputs (obj/ not bound)) (7 files) | 3932791 | `a555d9dfe13acfe041de411f4d874492f44727086a7bd8994a0f250f5d528ac2` (manifest) |
| `runs/dump-o2-s25` (the O2 baseline: its dumped queries) (7 files) | 9601 | `abeaee99fcb2968a59b57b3092a21d901adda164de8ede30d63aa51e8aecd3c1` (manifest) |
| `runs/census-o0-s25.out` (the O0 baseline: its driver output) | 1712 | `a2b10eab700ddb66e8785e540d0b2e778d769882f194ddee4959c648947a6e0f` |
| `runs/census-o0-s25` (the O0 baseline: its census outputs (obj/ not bound)) (7 files) | 1397335 | `3634b7cc41bf62a7d0abefe31cc6d322a281d0e6ddba202406294dc9e77409f2` (manifest) |
| `s24c-run/census/o2` (O2 comparison: compare, merged, promoted, newly failing, transitions, both root-class tables) (7 files) | 25651 | `3685051199c1527ba3b8984e2918c0cd940fb60cbc51b87934494963ff930112` (manifest) |
| `s24c-run/census/o2/segments` (O2 attribution (census_segments.py): segments.txt, roots.tsv, functions.tsv, segments.json) (4 files) | 479450 | `8300dc2af83ba73e0b233c86c34021a9940ef5755eea646cc39fbef351de409b` (manifest) |
| `s24c-run/census/o0` (O0 comparison: compare, merged, transitions, trace_diff.txt, outcomes.txt) (7 files) | 28516 | `70e5554f3cb8ff405855de3e592db04431058110907b42c9db4d853181fcef49` (manifest) |
| `s24c-run/census/o0/trace_diff` (O0: trace_diff.py's records (anomalies, S records, summary)) (3 files) | 2156 | `eb7327228ffca6de785d69cf9633bb4a408ce84b1d33ff982d98463af99bf4b2` (manifest) |
| `s24c-run/census/o3` (O3: the three counts and the refuted lines (o3_counts.txt)) (1 files) | 788 | `a3c14874c4cd2f05aae73c06c86fddc019c19f0cadb405ca9b21fae677ca37f4` (manifest) |
| `s24c-run/census/stop_rule.txt` (the stop rule over all three censuses (the O3 stop)) | 2110 | `e0fe2016ac5d981f3c197169ce19a9085a37f2bf0b4365e3353f973b08064e65` |
| `s24c-run/diag-o3` (the diagnosis: FILES.txt, diag.sh, repro.sh, base_o3.sh and their logs) (8 files) | 15862 | `71600b2399f16d993d32b205b5643e1884755f3874fff805d1151c6369b6c285` (manifest) |
| `runs/o3-s25.dylib` (the O3 baseline's dylib (a byte copy of runs/o2-s25.dylib)) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/census-o3-s25.out` (the O3 baseline (census-o3-s25): its driver output) | 1714 | `e1ad9646bd7040b60b2b82720d45e1f998825ab1d4cb8e377f33830a180cab3a` |
| `runs/census-o3-s25` (the O3 baseline: its census outputs (obj/ not bound)) (7 files) | 4121699 | `229dbfc4cda3c8b4b45b440c7c8e370d34e8b466ecb3169f9effd9220f8a0f16` (manifest) |
| `runs/dump-o3-s25` (the O3 baseline: its dumped queries) (9 files) | 10922 | `a31f407986125dde3188fe29065854c24a656054c1634edc5f8e21e28dcf65b3` (manifest) |
| `s24c-run/diag-o3/compare` (census-o3-s25 -> census-o3-s24c (census_compare.py) and segments.log) (5 files) | 32658 | `878204395e665cc16009caec3cad5b73a09c871a5199c06eeb0ff9d59057ab79` (manifest) |
| `s24c-run/diag-o3/compare/segments` (its census_segments.py attribution) (4 files) | 509184 | `228cf935e3743db60bc3b573bd34a16e0d2aa6cf4086726e8b598afd70f177c4` (manifest) |
| `s24c-run/diag-o3/ay` (every dumped O3 part of the two functions with (get-model), and AY 13556's answers) (30 files) | 24439 | `b7289540bfd823201e3415f2beb91b9f14d9e9597da13bbc5f983247e8ed3438` (manifest) |
| `s24c-run/diag-o3/strsearcher` (the StrSearcher::new reproducer (lib.rs)) (1 files) | 9481 | `5320766826cb91846326135b4d1e43a82252f50b9be4a1d4f7bda3aec1bf1c82` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3` (its O3 trace through the slice-24c dylib) (1 files) | 19373 | `de36cd2485d12c0b8f4eec73d4560828e7fdd82ad14adb0a4f50aa260f26ca7f` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3/dump` (its two dumped parts) (2 files) | 1321 | `49d17464e8ba2e8c60eddea27fb8eea03bebdcc317d008fcc5a5a7411e37464c` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3/obj` (its emitted objects (StrSearcher::new's not among them)) (2 files) | 994 | `690a897bf7e3baf56e493e96f06d3b62ff888bc134a8c9eff478532079c09807` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3/obj/trust-witness` (their witness) (1 files) | 2887 | `a99ba4d1ec4626c8199b11bf955019074d5c84c0f0449f2b8e64a2c86bd5ac73` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3/tir` (the TrustIR containers it compiled (binary and JSON)) (18 files) | 77959 | `c7b05dcf2c02e8e05616ae1e44617371ff87146a967538d7714c33db9c49b2e2` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o3` (its O3 trace through the slice-25 dylib) (1 files) | 18624 | `b3e4f9ee775dc8512193ea5593f0befe47bfd4f5717746ea0b37a7902a24e66c` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o3/dump` (its two dumped parts) (2 files) | 1321 | `49d17464e8ba2e8c60eddea27fb8eea03bebdcc317d008fcc5a5a7411e37464c` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o3/obj` (its emitted objects (StrSearcher::new's not among them)) (2 files) | 994 | `690a897bf7e3baf56e493e96f06d3b62ff888bc134a8c9eff478532079c09807` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o3/obj/trust-witness` (their witness) (1 files) | 2887 | `fb1d817cc9fc0efd40b4cc89a9fb799a8fd240eb5c1629ea7762d24fbd539199` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o3/tir` (the TrustIR containers it compiled (binary and JSON)) (18 files) | 77959 | `c7b05dcf2c02e8e05616ae1e44617371ff87146a967538d7714c33db9c49b2e2` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o2` (its O2 control through the slice-24c dylib) (1 files) | 16247 | `05ba26ad12cb9b097bd2bcd0c158f4f5cde8d2cbd5acb049c7e993dfc47530a7` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o2/obj` (its emitted objects (StrSearcher::new's among them; dump/ is empty)) (4 files) | 3676 | `e56430f28642433fad4f6ec28c86c8ef6f583c1c5f9983954f00d52c1290c5f4` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o2/obj/trust-witness` (their witness) (1 files) | 2887 | `c6102f496430327cd2f78f842d9f7ce6edae8e76d3459a60412094cf452d37c7` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o2/tir` (the TrustIR containers it compiled (binary and JSON)) (18 files) | 77959 | `c3bf3f986c66e1efdce95af7926807fb72a63bc9a6ffe651527f34210f475160` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o2` (its O2 control through the slice-25 dylib) (1 files) | 16251 | `66d921ea2e9e1d6fb5c23a66151d69a21f07751bcf54461139727f9ff88f1581` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o2/obj` (its emitted objects (StrSearcher::new's among them; dump/ is empty)) (3 files) | 3008 | `c7025343902af371d132bbe22ffaa83a060eb4e8802cbb7b7e364598205b6d01` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o2/obj/trust-witness` (their witness) (1 files) | 2887 | `15369c417344bbc50d69b3687635fb45451ec6f1bec9ff939d530ed9d6a8f61b` (manifest) |
| `s24c-run/diag-o3/strsearcher/s25-o2/tir` (the TrustIR containers it compiled (binary and JSON)) (18 files) | 77959 | `c3bf3f986c66e1efdce95af7926807fb72a63bc9a6ffe651527f34210f475160` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3-peephole` (its pre-RA rows (peephole.log) and the two objects that compile emitted) (3 files) | 1122239 | `921272dd10715f7b2a199da6b0ff77b4bd0114b1bea1fb11091909f1e58c8cad` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3-peephole/trust-witness` (their witness) (1 files) | 2887 | `d80a5914e2abedd54ae7b46e40e3ba7d00a9680602b6cb1cafec010bc0a29a0c` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3-np` (its lowering-only object (no proof claim) and disassembly) (3 files) | 81696 | `18e04f352022c51b720ac51366f623b032d621df64cad59aaa8f3c6b058d97aa` (manifest) |
| `s24c-run/diag-o3/strsearcher/s24c-o3-np/trust-witness` (its witness) (1 files) | 2887 | `f43f1929ee1452fa66d79ab2c05899af8645f4537ad0a258c7496e5c71cd46b7` (manifest) |
| `s24c-run/diag-o3/wtf8` (the slice_error_fail reproducer (lib.rs, a byte copy of s25-run/diag-wtf8/lib.rs)) (1 files) | 1190 | `01ccb7f723c663fc464e9ec5433db4c4c2245d2686404c1da368adbcb2c4d378` (manifest) |
| `s25-run/diag-wtf8/lib.rs` (slice 25's reproducer it copies (also bound, in its directory's manifest, by slice 25's PAYLOADS.md)) | 1190 | `9a40e3aca337fb50aff1cefebcaa06efea4b7aef735860d79d5c64b4f9036b3c` |
| `s24c-run/diag-o3/wtf8/s24c-o3` (its O3 trace through the slice-24c dylib) (1 files) | 4816 | `7a73b4afea26fc5b87815266eed76d7f78fa45aacf54d47a87f87023f2fcd0d3` (manifest) |
| `s24c-run/diag-o3/wtf8/s24c-o3/dump` (its three dumped parts) (3 files) | 3544 | `cbf0bdbb341bcd9159e720cc3841ffe13a2d78c35b8d6478380978fa8abaaeb2` (manifest) |
| `s24c-run/diag-o3/wtf8/s24c-o3/obj/trust-witness` (its witness (obj/ holds no object: slice_error_fail's is not emitted)) (1 files) | 12 | `f529c1c514ce8190ffd809c85c6187409b5eac7c148b82be308ef987a002116e` (manifest) |
| `s24c-run/diag-o3/wtf8/s24c-o3/tir` (the TrustIR container it compiled (binary and JSON)) (2 files) | 14620 | `10c13886a7b1c6841f93f0054ddca9c8417ac65a3de31775500032712a1c743b` (manifest) |
| `s24c-run/diag-o3/wtf8/s25-o3` (its O3 trace through the slice-25 dylib) (1 files) | 4813 | `29cddb799eaad12034a93e5c8f683c9999d6778f2e875d40652fce1ecbef072e` (manifest) |
| `s24c-run/diag-o3/wtf8/s25-o3/dump` (its three dumped parts) (3 files) | 3544 | `cbf0bdbb341bcd9159e720cc3841ffe13a2d78c35b8d6478380978fa8abaaeb2` (manifest) |
| `s24c-run/diag-o3/wtf8/s25-o3/obj/trust-witness` (its witness (obj/ holds no object)) (1 files) | 12 | `f529c1c514ce8190ffd809c85c6187409b5eac7c148b82be308ef987a002116e` (manifest) |
| `s24c-run/diag-o3/wtf8/s25-o3/tir` (the TrustIR container it compiled (binary and JSON)) (2 files) | 14620 | `10c13886a7b1c6841f93f0054ddca9c8417ac65a3de31775500032712a1c743b` (manifest) |
| `s24c-run/logs/gate6-fmt-r5.log` (census record: gate 6, format, on ad02a8f06) | 204 | `566e9f020d20325b4ce15aba790f5664f675f63f57cda3c2cbdf5818e7d77f6d` |
| `s24c-run/logs/gate6-docs-r5.log` (census record: gate 6, documentation, on ad02a8f06) | 139 | `d5168f6d9529de0cd87bdc11f62f3ea42cb2ac058c73f1ce6ca6b0b9fc1afe4c` |
| `s24c-run/logs/gate6-matrix-r5.log` (census record: gate 6, the full-test-matrix hosts check, on ad02a8f06) | 54 | `312cfbf035bbf6b58712321bd96a543d66b4637dfa2dd960035cd8f6c88d98b6` |
| `s24c-run/logs/gate6-fmt-r6.log` (fact-check fixes: gate 6, format, on 87d0107b6) | 204 | `cf8dfb8ac80484621b7c7eb7b972beae8c7166de91fa23766e1979843d338943` |
| `s24c-run/logs/gate6-docs-r6.log` (fact-check fixes: gate 6, documentation, on 87d0107b6) | 139 | `129247a277e032815e7632e29c606606c9045d49647b0c42eee6d44fecbba5a3` |
| `s24c-run/logs/gate6-matrix-r6.log` (fact-check fixes: gate 6, the full-test-matrix hosts check, on 87d0107b6) | 54 | `39876c4061c9ef35b366d566720e38df6c7e53db10de2546e2f9c1e45598b2db` |
