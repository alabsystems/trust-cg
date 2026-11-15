# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, fixture copies, queries) out of it. These payloads were
never committed. They are held on the measuring host (the x86_64 Mac of the
README) under `~/tcg-scratch`, at the paths below, and are bound here by size
and SHA-256 (a directory by the SHA-256 of its manifest, as
`scripts/payloads233.py` defines it). `scripts/payloads233.py` regenerates the
table. The README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `od233-design/README.md` (the OD-233 design (§0-§9)) | 68387 | `eacf7482512812c36328257c0926fe730a7a5d3896439abf6ab2ea527c816400` |
| `s25-run/logs/fails-before5.log` (slice 25's fails-before record on 6c036f1de (its S25_FAILS_BEFORE decomposed lines 1790-1809)) | 381887 | `19bf2b1b0adaf6f8c41cadedf0eac6db62e93ba92407648f0396e7d12d2ef19b` |
| `od233-run/logs/a06-fb-base.log` (fails-before at b30110fcd, first run (OD233_FAILS_BEFORE)) | 19312 | `738fddc37f96ca60137a7a01d6ba6ffaa7aaf98cb46296033a9553b2f20982d7` |
| `od233-run/logs/a07-fb-pre.log` (fails-before at 12ebba653, first run (OD233_FAILS_BEFORE)) | 17276 | `8d4c129c79529c00a2e4f94c773b0ab5354cfddffc63c41ba6d6281f2b7204ec` |
| `od233-run/fails-before/first` (the fixture copies the first fails-before runs ran (before formatting)) (2 files) | 90759 | `518273a2d09a035016d206dba9768d4e14d2fd953b194eb5a648c1c89ddc0be2` (manifest) |
| `od233-run/logs/a11a-fb-base.log` (fails-before at b30110fcd on the committed fixtures (lane a8d1d38c6)) | 18599 | `13009f71d78f94ef5fe7585b9b57cb0858c69736c3ac9d50a8cc3ceb33b91dd6` |
| `od233-run/logs/a11b-fb-pre.log` (fails-before at 12ebba653 on the committed fixtures (lane a8d1d38c6)) | 16570 | `e688a3a5aa4b592bf32ab1df5272d1fb383c76f9829b732816b09979b617db5b` |
| `od233-run/fails-before` (the fixture copies the review round's reruns ran (lane 5896ae541; they replaced the a8d1d38c6 copies)) (2 files) | 109919 | `8658359a19d7c85cd7b9a84701a3242346b7c9cc5aafa7da7cb101d6bdda2a0f` (manifest) |
| `od233-run/logs/a01-print.log` (the module with its printers while the fixtures were settled (9 of 10 failed)) | 104876 | `2356ef46626a033ed3b970771203c363a02fc59006abffb5cbae85cf6e346cee` |
| `od233-run/logs/a03-print.log` (the module and slice 16's every-point test while the fixtures were settled (both exit 101)) | 22283 | `ab1d8c24cb3bba63392fa2b19ae41d45923aaf65b4192a539d7da51acf4f9d2a` |
| `od233-run/logs/a04-print.log` (the module with its printers while the fixtures were settled (5 of 11 failed)) | 93837 | `6a19fef13987e6d689e1dd659b0f7e9382536dba1372d2cd5ef246a83c2fcef8` |
| `od233-run/logs/a02-suite.log` (the first solver-free suite run (the stack overflow in slice 16's every-point test)) | 61428 | `a73aba8790692a352b2cd1b15bd89ecf460f3e7e6c469f794cf78e834b149731` |
| `od233-run/logs/a05-print.log` (the module with its printers, and the per-phase overflow diagnosis with and without the rule) | 327889 | `10ec780177f2873cc100191635520466e88b50e70268249e8a9e47db0a000afd` |
| `od233-run/logs/a08-lldb.log` (the overflow diagnosis with a 512 MiB stack, and under lldb) | 582 | `fb4013d30e251361c14e2b6491c06e1d210ee6545fe42ae923ed42d0903e2072` |
| `od233-run/logs/a08-bt.txt` (lldb's stop at the overflow (SmtExpr::try_eval)) | 50572 | `9d3d32428f3e085d2a7b4771fb03d8c5155046d555e6c96048b89420c87dbff3` |
| `od233-run/logs/a09-depth.log` (the statement depths with and without the rule (DEPTH233), and slice 16's every-point test on the verifier stack) | 152976 | `ff242880825b5f550cd46e31a47fa4c1938e02be36874eda768a8189f5fae963` |
| `od233-run/logs/a10-module.log` (slice 25's in-parts test, and the module with its printers and the parts texts (TCG_OD233_PRINT_TEXT=1), before the commit) | 695913 | `38c815736f1c3213694dfb8ff4762c757e3f14c287a875b9f8dede3b8c90ca79` |
| `od233-run/logs/a11-gates.log` (gates 1-5 on a8d1d38c6, then the printers) | 1164234 | `ab0fe796fa28d3d5d6965cff54254427113d7d8e1fe74d84a66ac40db3741077` |
| `od233-run/qual-dump` (the replayed queries of the qualification lanes) (265 files) | 694215 | `b2e9512d90c8f424e299056b1e8ef0cb03f3f4dec8a6491537750b939a6bc535` (manifest) |
| `od233-run/logs/a12-gate6.log` (gate 6 (fmt, docs, the matrix check) on the records tree) | 522 | `be815fcb58ed433957801d16fe3bacad3b31ff05162d47f7111833c30d14ebda` |
| `od233-run/logs/server-a12.log` (the job server's start and exit lines for every job, through a12) | 1207 | `bca12dceb52db8056d632d9d16731e14adf87a924e946ae8eb03fdb16a0af5b2` |
| `od233-run/logs/b01-iter1.log` (review round: the sweep before the commit (V9 without its reload)) | 342197 | `b9123d2536352d0046830128a0a05f0e0f0b6d927ab535961683e7aa7a8fde4a` |
| `od233-run/logs/b02-quick.log` (review round: the module before the commit (V9 and Q1 failing)) | 68268 | `eb2f16919cf24d2670d40e47a1ef561804b19a0d5d5f1c9e91cbbff1f431cf9e` |
| `od233-run/logs/b03-diag.log` (review round: V9's statement printed, and the positive test (Q1 failing)) | 34124 | `061b8cfda8c8c45b588d233e6cd60feee15160e909f9642da8d81ed6c0ec4acc` |
| `od233-run/logs/b04-quick.log` (review round: the module passing before formatting and the commit) | 79997 | `03ccae64151c9be1fb12b9974ea6f807093d8ad09d260628f155c6edce44880e` |
| `od233-run/logs/b05-fb-base.log` (review round: fails-before at b30110fcd on lane 5896ae541, with the base sweep digests (OD233_BASE_DIGEST)) | 161042 | `5935dcd8e8cf67146b63f300ad398bde022757cfaab947df5de125f1cd1b320b` |
| `od233-run/logs/b06-fb-pre.log` (review round: fails-before at 12ebba653 on lane 5896ae541) | 17869 | `cd340aa476dcd69a14632cc1e42eb6e2a25739f6cbf6b22336a9542ed7c63d15` |
| `od233-run/logs/b07-gates.log` (review round: gates 1-5 on 5896ae541 (the sweep and digest lines digest-compare.txt reads)) | 862649 | `3a398f8624ca4a1818dd17a8cad8a7961e9baee27b6edac9e95d2a7b177ef5ad` |
| `od233-run/logs/b08-recut-time.log` (review round: the re-cut timing lane on 5896ae541, which panicked looking for s20 ManySlots in the wrong fixture list (fixed in 3ef06d6dd)) | 10824 | `debaa4201e52b7e50836e1ef9b5c0a75c52c73a0429e3c6158fad46416e515f6` |
| `od233-run/logs/b08b-printers.log` (review round: the od233 printers on 5896ae541) | 686052 | `2476df264a74e5d4439ee61a8b74bcb6da1538bcf5731affce5e1e6e47804e61` |
| `od233-run/logs/b10-recut-time.log` (review round: the re-cut timing lane on AY on 3ef06d6dd (s20 ManySlots at every point)) | 44436 | `2f889e6ae6b56b4468867c7c49ff0eec74e386f30a41b6e84df05eb41f750283` |
| `od233-run/logs/b11-gates.log` (review round: gates 1-5 on 3ef06d6dd, the code head) | 861910 | `5a76f05ce2928852d7b592ae7fa7a26a986dbe277311a59d57d517a55be7184e` |
| `od233-run/logs/b12-gate6.log` (review round: gate 6's first run on the records tree at 3ef06d6dd (the matrix check failed: the timing lane unlisted)) | 1885 | `99abca67e829862f983f5baa62c5d3de048ace12cf2638c51bf64189f1c322e5` |
| `od233-run/logs/b13-gate6.log` (review round: gate 6 on the records tree at 454963b4c) | 1740 | `2b3410fbf4203066bc422226505b18f6de226dd245b61c553653b4814acfce8e` |
| `od233-run/logs/digest-compare.txt` (review round: scripts/digest_compare.py on b05 and b07 (5896ae541)) | 124 | `874d87b1b944b6ce2e7180b32ef28dabe9d4a14dddf56565dd555e6868dc33b6` |
| `od233-run/logs/digest-compare-b11.txt` (review round: scripts/digest_compare.py on b05 and b11 (3ef06d6dd)) | 124 | `874d87b1b944b6ce2e7180b32ef28dabe9d4a14dddf56565dd555e6868dc33b6` |
| `od233-run/census-parse` (review round: the fixed parts_census.py on census-o2-s25 and on the reviewer's three-line attempt) (5 files) | 1236445 | `552616635a18e29f3dd7e6d84844c0250320f81a0b99551535023edfce44d0c1` (manifest) |
| `od233-run/logs/server-b13.log` (review round: the job server's start and exit lines for every b job, through b13) | 939 | `df718f129ec3aa200a9bef2e106328205d3a51642d770d72ca91b9bcdf7e4a7e` |
| `build_bridge.t011.sh` (the bridge build helper census.sh runs (release, the t011 overlay)) | 2190 | `ed29e39bf5644e74ef7fdd74137a6a20130356801fb30fbdc8158cc870acaac6` |
| `census_t011_dylib.sh` (the census driver census.sh runs on one bridge dylib) | 2167 | `010b9d26fc7c07ad9e0df03c408f178bafb12c86c09f6973e9508a29ae5c2a7a` |
| `check_dylib_tools.sh` (the dylib preflight census_t011_dylib.sh runs) | 671 | `b1d0aedd8c3b5ecf1fbdae4891119c27736cd05f8b6018db1e6cde1b5fdb4a6c` |
| `od233-run/logs/census.log` (the bridge build at c76048fa3, the four censuses and their comparisons (census.sh)) | 54421 | `d296bf33dca562c2400e8cd3d2ac819546f5a2180961524c4bc5311b631b83f9` |
| `runs/o2-od233.dylib` (the OD-233 bridge dylib the O2 census ran) | 145730104 | `1bf4e6285327dedf161563aaac702ac0019a5da65873fbe94e645e49be3fe441` |
| `runs/o0-od233.dylib` (the OD-233 bridge dylib the O0 census ran (the same build)) | 145730104 | `1bf4e6285327dedf161563aaac702ac0019a5da65873fbe94e645e49be3fe441` |
| `runs/census-o2-od233.out` (the OD-233 O2 census driver output) | 1755 | `074769ec6cbad6f2fa8eacb6f6c5a300b5b9309b4ef2453dde84c33d6912215e` |
| `runs/census-o2-od233` (the OD-233 O2 census outputs (failed roots, refusals, stderr trace with solve-trace lines)) (7 files) | 4382606 | `f2a2c04485d6ab6b08f0cb89e256ffb28cc300d45fdf7044adc56774da38c750` (manifest) |
| `runs/census-o2-od233/obj` (the OD-233 O2 census's emitted objects) (1035 files) | 1282083 | `621ed554fdf13dd0baf4d47d8b56679e468cc1c88e09609d7bf9bfc9f79c34f8` (manifest) |
| `runs/dump-o2-od233` (the OD-233 O2 census's dumped queries (bodies that did not replay Valid)) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `runs/census-o0-od233.out` (the OD-233 O0 census driver output) | 1753 | `e64337f3df5d7869b345e2bb3a47bd9a3590b940138c8ad1a79e8a41e3727d06` |
| `runs/census-o0-od233` (the OD-233 O0 census outputs) (7 files) | 3017949 | `79d14cbdd186cb8251e5c3ba083bc06ea3fdea879189a0f00bb92920acc4941e` (manifest) |
| `runs/census-o0-od233/obj` (the OD-233 O0 census's emitted objects) (3426 files) | 4682079 | `a194e6359bd623470f590fd77b47f1d3e6690ea04bcb91123b22627db1f0c334` (manifest) |
| `runs/dump-o0-od233` (the OD-233 O0 census's dumped queries) (0 files) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (manifest) |
| `runs/o2-s25-st.dylib` (the baseline dylib (a copy of o2-s25.dylib, d92b944fe) the O2 timing re-run ran) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/o0-s25-st.dylib` (the baseline dylib (the same copy) the O0 timing re-run ran) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/census-o2-s25-st.out` (the baseline O2 timing re-run's driver output) | 1761 | `b442f5828ef7d9e7610d5805db924caf53d4115f65c9c64b666287ff5dbd9306` |
| `runs/census-o2-s25-st` (the baseline O2 timing re-run's outputs (solve-trace lines)) (7 files) | 4381116 | `75ae7c64ee3a07643230db538a14b54b5b4c09d3bcc618f821b9199773f9f4cf` (manifest) |
| `runs/census-o0-s25-st.out` (the baseline O0 timing re-run's driver output) | 1758 | `07602afb11c21c3cc9af8c4c02c0b5b3ffcca48cfd20642af4fb85aac44c8ca5` |
| `runs/census-o0-s25-st` (the baseline O0 timing re-run's outputs (solve-trace lines)) (7 files) | 2967787 | `e654247fe2495d0138895ece2a98832f03d2ada881f7703863ed1587e93bf843` (manifest) |
| `runs/census-o2-s25` (the O2 baseline (slice 25's census, d92b944fe)) (7 files) | 3932791 | `a555d9dfe13acfe041de411f4d874492f44727086a7bd8994a0f250f5d528ac2` (manifest) |
| `runs/census-o0-s25` (the O0 baseline (slice 25's census, d92b944fe)) (7 files) | 1397335 | `3634b7cc41bf62a7d0abefe31cc6d322a281d0e6ddba202406294dc9e77409f2` (manifest) |
| `od233-run/census/o2` (O2: root classes, parts (parts_census.py), objects, both sides) (7 files) | 2475774 | `baf17599e27a256812b08bdfc6a6d05446135aa48b5ad9ee383fc13f8a17aae7` (manifest) |
| `od233-run/census/o2/compare` (O2: census_compare.py against census-o2-s25) (4 files) | 16934 | `255791cb10f92bef4af0c3ad6e565c7f1090ab2c5d02a59b42fb5f62f2a46189` (manifest) |
| `od233-run/census/o2/followup` (O2: census233.py (the stop rule's items, wtf8's trace, the cut_pairing texts)) (2 files) | 6730 | `7cac3187fb780a9269d98e389e5cbaf8e545feb516f2518be97df8e3ec302820` (manifest) |
| `od233-run/census/o2/times` (O2: part_times.py against the baseline re-run) (3 files) | 440111 | `547eb6795ecdd29b46bed250ea7f329c9310edac1c96a40f9b499966c73f15f0` (manifest) |
| `od233-run/census/o2/rerun-compare` (O2: census_compare.py of the baseline re-run against census-o2-s25) (4 files) | 16972 | `9f22e9d865bd9b28e1677e02f347fdb51ed9b07f25006b96914a8557e5e0f124` (manifest) |
| `od233-run/census/o0` (O0: root classes, parts, objects, trace_diff.txt) (8 files) | 4528370 | `ed111d16cdba4c8546719aebf92465c34af8a94124439fee291c739d686e2e50` (manifest) |
| `od233-run/census/o0/compare` (O0: census_compare.py against census-o0-s25) (4 files) | 20348 | `dd29b55e67535a91936777092771bb3d33b6417ec5df5e96772f9c68523992a3` (manifest) |
| `od233-run/census/o0/followup` (O0: census233.py) (2 files) | 14035 | `273885c71d1176204e6b35c4bdf018442506ad60636b0fad19d9bb50cd779f1e` (manifest) |
| `od233-run/census/o0/trace_diff` (O0: slice 25's trace_diff.py records) (3 files) | 19014 | `53c6c5ff55349a5f91b879d18b8caaa9d7fa61882b072cd62af0f6da21302014` (manifest) |
| `od233-run/census/o0/times` (O0: part_times.py against the baseline re-run) (3 files) | 1431648 | `fac26946300eb3d2aa129d2e4bc9960a31ef75472e74d1a3e5ed79b2b93fd857` (manifest) |
| `od233-run/census/o0/rerun-compare` (O0: census_compare.py of the baseline re-run against census-o0-s25) (4 files) | 20348 | `dd29b55e67535a91936777092771bb3d33b6417ec5df5e96772f9c68523992a3` (manifest) |
| `od233-run/census/wtf8` (O2: the certified-part store entries of core::wtf8::slice_error_fail's parts (copied from the shared store)) (3 files) | 1200787 | `3772e9c984a5f75bdcbc7601f47ce1b0c58971252d03c16d21844b656b558dc1` (manifest) |
| `od233-run/census/o0/stop-diagnosis` (O0 stop: the six functions' timed-out parts on the OD-233 census, the baseline re-run, census-o0-s24c and census-o0-s25 (six_parts.py)) (2 files) | 15049 | `532750289f7d76703ad7e99cb15c5c2527d0398c0f3feac2e60b5a7d831c456b` (manifest) |
| `od233-run/census/o0/stop-diagnosis/base-vs-rerun` (O0 stop: census233.py of census-o0-s25 against the baseline dylib's re-run) (2 files) | 5146 | `25210fe49dddbf644301112c9bfe40150dcda175d017a3d9adf8f7a684600aeb` (manifest) |
| `od233-run/census/o0/stop-diagnosis/rerun-vs-od233` (O0 stop: census233.py of the baseline dylib's re-run against the OD-233 census) (2 files) | 13373 | `72bf018bb4f5a7f37e18a640841e089b5fe5e8a1de7743a4ad48e67da521fa7f` (manifest) |
| `runs/census-o0-s24c` (slice 24c's O0 census (2026-11-07), read for the six functions' timeouts) (7 files) | 1398551 | `0d3ba8975ade94e6b7b645f31faf23d99a79fbac90e7c4e7cfdd46af699b0d1d` (manifest) |
| `runs/census-o0-s24c.out` (slice 24c's O0 census driver output (its dylib o0-s24c.dylib, another build)) | 1717 | `1e9c60ba8bbcd5f35a253ae890e9bc5d80199ff9bed3b2137d14bac8b3c1ec58` |
| `runs/census-o2-s25.out` (the O2 baseline's driver output (wall 909 s)) | 1714 | `d3dea4def568298ee9d161d3d0609e7a894ad843decd0ab69072ba58df8d1ebd` |
| `runs/census-o0-s25.out` (the O0 baseline's driver output (wall 2465 s)) | 1712 | `a2b10eab700ddb66e8785e540d0b2e778d769882f194ddee4959c648947a6e0f` |
| `runs/census-o2-s25/obj` (the O2 baseline's emitted objects (the object comparison's base side)) (1034 files) | 1277402 | `9a0420b7c2b872148f77428351e1efb3790cfafca863d56622d0976831093603` (manifest) |
| `runs/census-o0-s25/obj` (the O0 baseline's emitted objects (the object comparison's base side)) (3426 files) | 4682079 | `a194e6359bd623470f590fd77b47f1d3e6690ea04bcb91123b22627db1f0c334` (manifest) |
| `runs/dump-o2-s25` (the O2 baseline's dumped queries (core::wtf8::slice_error_fail's three parts among them)) (7 files) | 9601 | `abeaee99fcb2968a59b57b3092a21d901adda164de8ede30d63aa51e8aecd3c1` (manifest) |
| `runs/dump-o2-s25-st` (the O2 baseline re-run's dumped queries) (7 files) | 9601 | `abeaee99fcb2968a59b57b3092a21d901adda164de8ede30d63aa51e8aecd3c1` (manifest) |
| `runs/dump-o0-s25-st` (the O0 baseline re-run's dumped queries: none, the directory is empty) (0 files) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (manifest) |
| `runs/census-o2-s25/obj/trust-witness` (the O2 baseline's trust-witness directory) (1 files) | 519850 | `1b3819e176edbdff368188ab8319918be80659a4636799db29844f196ba107a8` (manifest) |
| `runs/census-o2-s25-st/obj/trust-witness` (the O2 baseline re-run's trust-witness directory) (1 files) | 519857 | `1b931d1b9feee82f8e1631e26005f03740cedee95fe81592cd042500c02366ef` (manifest) |
| `runs/census-o2-od233/obj/trust-witness` (the OD-233 O2 census's trust-witness directory) (1 files) | 519857 | `d4f97b81611cca6ee36026b7d8b9fe2574b396382521652bb08aff22e8dec20d` (manifest) |
| `runs/census-o0-s25/obj/trust-witness` (the O0 baseline's trust-witness directory) (1 files) | 519850 | `efaf99624445da8839139a697845d5e766040de6be5773438a243183a22d4165` (manifest) |
| `runs/census-o0-s25-st/obj/trust-witness` (the O0 baseline re-run's trust-witness directory) (1 files) | 519856 | `1bcd26cbeef7cc0021b6207a5f02d6c8927748857685a6c363b16cb81856f52a` (manifest) |
| `runs/census-o0-od233/obj/trust-witness` (the OD-233 O0 census's trust-witness directory) (1 files) | 519856 | `a4a9b317c57f90fea1daaac2020f49ee205fe117963fe8730e27525b887c4a1b` (manifest) |
| `od233-run/fact-checks` (scripts/fact_checks233.py's output (fact_checks.txt, sections A-I) and the host's CPU counts (host.txt, sysctl)) (2 files) | 24168 | `e9126f9358147d0dee898d05049b90fa00de876967c9b855a52f2d1556813ffb` (manifest) |
| `runs/o2-s25.dylib` (the O2 baseline's bridge dylib (d92b944fe; also bound in slice 25's PAYLOADS.md)) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/o0-s25.dylib` (the O0 baseline's bridge dylib (the same build; also bound in slice 25's PAYLOADS.md)) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `od233-run/logs/b14-gate6-head.log` (gate 6 on c76048fa3 with a clean tree) | 410 | `c500ad2efca088d227c40a9e7bd49ded1527e7d73ef41c78bc3a9e751146b3d1` |
| `od233-run/logs/server-b.log` (the job server's start and exit lines for every b job, through b14) | 1008 | `5fa7e68a14fdc8ec310991652d0656b20dfe5ee2bcee81cdb7786aeae2aca6f9` |
| `od233-run/logs/c01-gate6.log` (gate 6 on 78f602091 (the census record with its fact-check corrections) with a clean tree, run by hand) | 397 | `9eeae0a265ae6ef5706f839359f94c46313f1e13c912b7a8532cca57ff165da1` |
