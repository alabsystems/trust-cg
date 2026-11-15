# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, binaries) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256. `scripts/payloads25.py` regenerates the table. The
README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s25-design/README.md` (the slice-25 design (§0-§9)) | 73755 | `f3707a633e72186c709322de8b00a282f84a708f74f34fbc9048bba784ed9618` |
| `s25-run/s25.0-solverfree.log` (slice 25.0: the solver-free x86 body suite) | 58934 | `aac6040c8e95a139790543465debd6638d2815b476ad5a71fd86bee39208766d` |
| `s25-run/s25.0-fmt.log` (slice 25.0: format) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `s25-run/logs/census-diag.log` (slice 25.0: the bridge build at 6c036f1de, the O2 census and its comparison (census_diag.sh)) | 2780 | `e9efe0908c597b7c61a3fc5cf2f282f3c5c64d654adf66b8ee33b7d814616cd6` |
| `runs/o2-s25d.dylib` (slice 25.0: the bridge dylib the diagnostic census ran) | 145571760 | `40719b01447e7172c029e0aa38e5d6817cf06bef0cb1e44514a047eecc067cd8` |
| `runs/census-o2-s25d.out` (slice 25.0: the O2 census driver output) | 1718 | `6078db5c3cea0c10978e829d6078a30f8026f87d784105838c626d797dc08189` |
| `runs/census-o2-s25d` (slice 25.0: the O2 census outputs (failed roots, refusals, stderr trace)) (7 files) | 5670360 | `6abda08443f68a1f262c569097b24d70fe65e76cab990ba65b781c2fb35d3453` (manifest) |
| `runs/dump-o2-s25d` (slice 25.0: the O2 census's dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `s25-run/census/diag/compare` (slice 25.0: census_compare.py against census-o2-s24a-f) (4 files) | 44136 | `fcb74968cfcb02ddea51ae7e8de4624ce2735c43167a761cbe36db9f46e28203` (manifest) |
| `s25-run/logs/diag-analysis.log` (slice 25.0: the analysis run (diag_analysis.sh)) | 838 | `b255d1a8560d4918a28b49f709b138eb8ce03ad9ea15a7cce1faa9a5d863d22f` |
| `s25-run/census/diag/trace_diff.txt` (slice 25.0: the function-by-function no-verdict-change check) | 757 | `8d97da5c1c9a4187931b5ae36230412a7595fd86537ef27d4d93b1dba7befbea` |
| `s25-run/census/diag/trace_diff` (slice 25.0: trace_diff.py's records) (3 files) | 145671 | `c36232890497da63478d8f1a483554c112e680401d674eee75bf3f9c2ea4c78a` (manifest) |
| `s25-run/census/diag/histogram.md` (slice 25.0: the histogram of the scan's named rows) | 5786 | `46b3d81f4398716b0bda1800fed6e5ea35ecad9d003a52fcfbbf3a9e257d5c3e` |
| `s25-run/census/diag/s_rows.tsv` (slice 25.0: the named row of each S function) | 55973 | `7b8f6ac6f9f7dfee849172d33c4705feb6023ab90690bd7081317c13c008bfdb` |
| `s25-run/census/diag/s_roots.jsonl` (slice 25.0: the S roots) | 50084 | `132d206ac814e06a94d8805f11dd85f72b2785701520f1b517ad154f2b91c4df` |
| `s25-run/census/diag/o0_sib_sites.json` (slice 25.0: the O0 cross-reference) | 30592 | `33483e4c2457c6713d445ddb30ae75d508a2e75e80d18b399d416327f03408bd` |
| `s25-run/census/diag/merged.txt` (slice 25.0: the merged-chains attribution (census_merged.py)) | 1082 | `1ea60c7cc302837c618a6867747cb6a492aac3e2cc4fd7a583af85e65940d388` |
| `s25-run/logs/s251-solverfree.log` (slice 25.1: the solver-free x86 body suite and the LeaSib control printer) | 68651 | `e5c54c49cb5bf4190bc76f958fe65e63f43e32bea09dc9a4d82bbd2b35e311f9` |
| `s25-run/fails-before/copy1_x86_source_bound_body_slice25_tests.rs` (fails-before, first copy (an earlier fixture section; superseded)) | 27476 | `1ddf10efacce0498cff878a58ea4430cd93d4c1ed32d0663aa411d3d2c888d3c` |
| `s25-run/logs/fails-before1.log` (its run on 6c036f1de (superseded)) | 35825 | `fbac4e9ec802bb105b4cd2dd5b9d8d899c82aca14a17d8f2425b7ba93fe7dfe4` |
| `s25-run/fails-before/copy2_x86_source_bound_body_slice25_tests.rs` (fails-before, second copy (an earlier fixture section; superseded)) | 28698 | `5e17a32e7db15d61ef6cbecf21f01fd1567dc368803cb80786d9e5c2ec402337` |
| `s25-run/logs/fails-before2.log` (its run on 6c036f1de (superseded)) | 237911 | `79f0f1f1175eeec7ed9e2204cfc9901e91420b45e85aed31b06e337980f54096` |
| `s25-run/fails-before/copy3_x86_source_bound_body_slice25_tests.rs` (fails-before, third copy (the final fixtures before their comments were corrected and formatted)) | 36568 | `2730b6a4baffe2ca51bbfbdd7fc9e5581592b68acc29af0ed89004f95d35a88c` |
| `s25-run/logs/fails-before3.log` (its run on 6c036f1de: every fixture's rows and refusal) | 283715 | `35ded9f4341076031f58f194554b841efde4754da78e2379dfae39c3c273bfad` |
| `s25-run/fails-before/copy4_x86_source_bound_body_slice25_tests.rs` (fails-before, fourth copy (the committed fixture section)) | 37184 | `26840846b563bc382506bbad95aed6de8dcbe93e8d049a6358a61a8fa670cda6` |
| `s25-run/logs/fails-before4.log` (its run on 6c036f1de: every fixture's rows and refusal (the record)) | 283587 | `f3259789b0aa66af32a8aedfb183ec0d4c35098b5688f341bc77df9eafb505ca` |
| `s25-run/logs/s252d.log` (the golden write (TCG_X86_BODY_SNAPSHOT_WRITE=1) and the module before the last control fixes) | 32036 | `5dd582ac62ba87fce0f482f5f5138d8e27d052a7c5166f67189b8c09ec87a8a3` |
| `s25-run/logs/s252e.log` (the solver-free module on the final code (20 passed)) | 21216 | `6ec706e9ac359bcaac8425b27506c13b61b8b5605195d8dcad2be020150f32f8` |
| `s25-run/logs/jobQ.log` (gate 2: the three slice-25 qualification lanes) | 56767 | `089a32cae96adba6c10ce2e6362b93cc4dfd64451152aba5cfa52590f5550547` |
| `s25-run/qual-dump` (gate 2: every replayed and refuted query) (48 files) | 113000 | `b29119e3ef0f90aadc69a9adc826254bfa05528c9e40bc41b630d8821373de64` (manifest) |
| `s25-run/logs/jobG.log` (gates 1, 3, 4 and 5) | 377398 | `3fdbb3459d164685b1899693f69de5d88f06f27cbeb10dc912a758836ff2ce2b` |
| `s25-run/logs/jobF.log` (the module with --nocapture (S25_MUTANT lines) and the printers on the final code) | 139333 | `abef44914ac177b9699d6f8a826cc76d8ceefa657e9c82b0212954ec558bacf8` |
| `s25-run/logs/gate6-fmt.log` (gate 6, format) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `s25-run/logs/gate6-docs.log` (gate 6, documentation) | 87 | `367a2819b366278854f46d55efa2665fcda90bf59ecc31cdd73cba6f9438e898` |
| `s25-run/logs/gate6-matrix.log` (gate 6, the full-test-matrix hosts check (silent on success)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s25-run/fix/logs/m1.log` (review round: the module and the golden write, first iteration) | 19482 | `f3fc78584fbbf2bb61ea77fbc89b8f6d638aa906ebf6e583a5b6bda97a6df086` |
| `s25-run/fix/logs/m2.log` (review round: the module, the replay lane and the e2e target, second iteration) | 73068 | `37a52bedfa5b1b4215c8c5082451efe4d2b3c80f860daa8cd07256443739434b` |
| `s25-run/fix/logs/m3.log` (review round: the module and the qualification lanes, third iteration) | 70081 | `2f9fefca2b5d3b183e8846c13f5e5c80ea33e83ee8a83c9e6a7fb6d59f64907e` |
| `s25-run/fix/logs/m4.log` (review round: the module and gate 4 on the pre-commit tree) | 53663 | `e9d865ad1a31dc9aa7379e33850d9cf881add02829e47cae5d38418998910ebf` |
| `s25-run/fix/logs/fin.log` (review round: fin.sh, stopped in its bridge build (no result)) | 73 | `d17402586394a6520baecf12db852b2b9cc18fefe5d8be49a23681e9dc2084e6` |
| `s25-run/fails-before/copy5_x86_source_bound_body_slice25_tests.rs` (fails-before, fifth copy (the review round's fixture section and the extended recorder)) | 106128 | `5f1144d848108e3246cb2fa758ab5e4de06a324c077334cf27ca160629f58617` |
| `s25-run/logs/fails-before5-unused-import.log` (its first attempt: the copy did not compile (an import only the controls use; the generator now allows unused imports)) | 14992 | `64f4739adc057e436e1d111db100a214e969a61db7af4d297ddef2379398a363` |
| `s25-run/logs/fails-before5.log` (its run on 6c036f1de in the base tree's own target dir (the record)) | 381887 | `19bf2b1b0adaf6f8c41cadedf0eac6db62e93ba92407648f0396e7d12d2ef19b` |
| `s25-run/merged/gates.log` (gates 1 to 4 on the merged head a617488aa) | 516011 | `9b802f6e64badab1d7a6afe3c38fc9f8bd3e6069c979a8ab5736ab675808709c` |
| `s25-run/merged/qual-dump` (the merged head's replayed and refuted queries) (195 files) | 343367 | `455503a7cbbba363e72c1f7100efc19fa35feb41b8c9dcb488e0cd9a0cbab7ff` (manifest) |
| `s25-run/diag-wtf8` (the refuted body: the reproducer, its traces, rows and disassembly (FILES.txt indexes it)) (11 files) | 212174 | `aece779aec9930422175831a2d6baf8297e180b61092bb94db14b060dd086f26` (manifest) |
| `s25-run/diag-wtf8/ay` (the refuted body: the census's three parts with (get-model) and AY 13556's answers) (6 files) | 5097 | `81d2a9ed4c3711e227dd67253e3a33f52429088e61bb86281f6afb8c43608bec` (manifest) |
| `s25-run/diag-wtf8/dump` (the refuted body: the reproducer's dumped parts) (5 files) | 903522 | `e5ba9847e25e8bb90e23c69f697e3683e4c5d6e3cc58165fb6971cc6b1b9b761` (manifest) |
| `s25-run/diag-wtf8/tir` (the refuted body: the reproducer's TrustIR container) (2 files) | 14677 | `fefcea139165f0c9870f43e0be874f5c8d8aaebf9289ed18cc1bd9fae8cc3fda` (manifest) |
| `build_bridge.t011.sh` (the bridge build helper census.sh runs (release, the t011 overlay)) | 2190 | `ed29e39bf5644e74ef7fdd74137a6a20130356801fb30fbdc8158cc870acaac6` |
| `census_t011_dylib.sh` (the census driver census.sh runs on one bridge dylib) | 2167 | `010b9d26fc7c07ad9e0df03c408f178bafb12c86c09f6973e9508a29ae5c2a7a` |
| `check_dylib_tools.sh` (the dylib preflight census_t011_dylib.sh runs) | 671 | `b1d0aedd8c3b5ecf1fbdae4891119c27736cd05f8b6018db1e6cde1b5fdb4a6c` |
| `s25-run/logs/census.log` (the bridge build at d92b944fe and both censuses with their comparisons (census.sh)) | 10501 | `65caec62955686f46c7819c618493997ea2e88bbe4b70fe9fa2f2669dc72467b` |
| `runs/o2-s25.dylib` (the bridge dylib the O2 census ran) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/o0-s25.dylib` (the bridge dylib the O0 census ran (the same build)) | 145592216 | `2e47fae16014d496ab5720d8a5ee3e7d76acd7f1773b377c68901f1e49f456f2` |
| `runs/census-o2-s25.out` (the O2 census driver output) | 1714 | `d3dea4def568298ee9d161d3d0609e7a894ad843decd0ab69072ba58df8d1ebd` |
| `runs/census-o2-s25` (the O2 census outputs (failed roots, refusals, stderr trace)) (7 files) | 3932791 | `a555d9dfe13acfe041de411f4d874492f44727086a7bd8994a0f250f5d528ac2` (manifest) |
| `runs/dump-o2-s25` (the O2 census's dumped queries) (7 files) | 9601 | `abeaee99fcb2968a59b57b3092a21d901adda164de8ede30d63aa51e8aecd3c1` (manifest) |
| `s25-run/census/o2` (census_compare.py against census-o2-s24a-f, census_merged.py, root_classes.py and firsthit.py of both sides) (9 files) | 62817 | `96344ad0cb30e800ad11dfea038df4283595e38712e20ee0ed4c75750ea89f14` (manifest) |
| `s25-run/logs/census-followup.log` (the O2 follow-ups run (census_s25.py)) | 14902 | `65f2b32d8ba6dfcd3eaa4b59763a141929043b6de5d72e34ff41a56cf808785d` |
| `s25-run/census/o2/followup` (census_s25.py's records) (3 files) | 619779 | `77604db2ba9c58faf1985f837ff16e93caceaec54446365b004134761cce7aee` (manifest) |
| `runs/census-o0-s25.out` (the O0 census driver output) | 1712 | `a2b10eab700ddb66e8785e540d0b2e778d769882f194ddee4959c648947a6e0f` |
| `runs/census-o0-s25` (the O0 census outputs (failed roots, refusals, stderr trace)) (7 files) | 1397335 | `3634b7cc41bf62a7d0abefe31cc6d322a281d0e6ddba202406294dc9e77409f2` (manifest) |
| `runs/dump-o0-s25` (the O0 census's dumped queries: none, the directory is empty) (0 files) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (manifest) |
| `s25-run/census/o0` (census_compare.py and census_merged.py against census-o0-s24a, and the trace check) (6 files) | 21375 | `2e30ac3128ed38bfb66449355669a0061146f01e1dba6b64a92c60a4e9dcb389` (manifest) |
| `s25-run/census/o0/trace_diff` (trace_diff.py's records of the O0 census) (3 files) | 1081 | `f7b7569fcb0d606d147f725f3f108e7beab7d813633f662eb3a05870e4d37b94` (manifest) |
