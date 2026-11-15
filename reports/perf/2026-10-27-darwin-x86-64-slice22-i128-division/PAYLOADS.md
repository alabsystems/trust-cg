# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, binaries) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256; a directory's row is its total bytes over its
top-level files and the SHA-256 of its manifest (one line `<sha256>  <name>`
per file, sorted by name). `census/payloads.py` regenerates the table. The
README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s22-design/README.md` (the slice-22 design (§1-§6)) | 41742 | `14b61911f981041d0faa6cd8c68db12d91215612065f391246d7c877bbce769c` |
| `s22-design/data/names14.txt` (the 14 roots) | 1541 | `74dd4aaa38e7920e407e1515b399db3384eb2169ef01d2f626723a20f2453754` |
| `runs/census-s21/failed_roots.jsonl` (census-s21, the 36 failed roots the design read) | 37128 | `c1c5242a5e5bbd756d8cbbabc9e938b8fc78165d28595b1481fb74942f0d3b8a` |
| `runs/census-s21/stderr.log` (its body trace (the census outcome of every function)) | 1393474 | `c8cbb5d770e79c90ac97ea9e0400a54b7d09c56573629044fc3a134b3a8d8b7a` |
| `runs/s21.dylib` (the census-s21 bridge the fresh dump ran) | 144687624 | `87407a8dada79825d322bb636693fbf1978d52238f602c09900c2a62c8a73893` |
| `runs/core-ir-s22/` (the fresh `core` trust-ir dump (`census/dump_core_ir.sh`)) (88 files) | 6872172 | `afa61a7e32fe698511ce4fa5922ac2fd5dedf85563ad096c8b9d7740091a4626` (manifest) |
| `s22-run/logs/dump.log` (its log) | 31 | `1a187bdada1d29ce8c0f117b700c936b1af58b99dfb88b90b02fb25b1b862854` |
| `s22-run/probe/x86_body_probe_a2` (the probe at 22a (OD-202)) | 92668360 | `03a7dc0893b1c533d0422cb289408a3dc5c8f1eb3d928265b412711ec1453d7b` |
| `s22-run/probe/x86_body_probe_b` (the probe at 22b without `guard`) | 92789664 | `672f08132f2c15418adb49c7e4144c7be44916681caa1c5e8eda123f13ca18ef` |
| `s22-run/probe/x86_body_probe_b2` (the probe at 22b (OD-203)) | 92790928 | `f9d40d499e7512e39e58744e8c629d1ebf9e5661f5a0f7175c7da53c6edaabd8` |
| `s22-run/probe/x86_body_probe_m` (the probe on the merged tree without `catnf` (22b, trust-ir pin `73c5a310`)) | 92690680 | `4cb429df66a75b6f6e89b7e3b6a0ce93afe6335257e116414dbe7d30b658fe66` |
| `s22-run/probe/x86_body_probe_c` (the probe at 22c (OD-204)) | 92690680 | `d9634203492a74b38a5abacca410071f0e4405d96aa9c918ece4f724e28ce179` |
| `s22-run/probe/trace_spelling.patch` (the local spelling trace (never committed) that found the folded guard) | 2268 | `b82a0d551d160f692893249e9ce74147d41f424798dc65f27f415c871c593b21` |
| `s22-run/probe/x86_body_probe_trace` (the probe with that trace) | 92839144 | `708475ade1d1e24b273ed9198c11b1c7ae33f9eabb662f636f44d5431447d12c` |
| `s22-run/trace/trace.err` (its trace over the 14 roots) | 3605 | `378c2245c61204acfb7742587e321ec90259584755565d18c8b8014df8dbd2e7` |
| `s22-run/probe/trace2.patch` (the second trace (22b without `guard`; theorems and parts)) | 4188 | `9133597e28f09e649bbbb0e064efd6180640bfb5e6dd52179f3edcce3bb0cd57` |
| `s22-run/probe/x86_body_probe_trace2` (the probe with it) | 92728344 | `81c88c048876838b65d57e7006bcfe492718c382e8b7626172579636a0b551b5` |
| `s22-run/trace/trace32b.err` (its trace over the 32 functions the step changes (each failed the check)) | 23432 | `3b487c57ba679d9d9718be764bedd5b1c80ade1ee829835b7aaecb36202b0048` |
| `s22-run/stage_a2/q/` (the 14 roots' queries and claim splits at 22a) (409 files) | 797265 | `ccf502449acf5dca64b6429b99ef42a89a8bafe4154c162a22113ab5ec961014` (manifest) |
| `s22-run/stage_b/q/` (the same at 22b without `guard`) (405 files) | 780045 | `0eb60cd7f148e81eafbf290cc3fa6d388499b46f8846e67608a7eab36b6cf9a2` (manifest) |
| `s22-run/stage_b2/q/` (the same at 22b) (405 files) | 768691 | `48a61759aa202a810103c355624f97b61dd2de69f987e3e15575934fe692ccde` (manifest) |
| `s22-run/stage_c/q/` (the same at 22c) (374 files) | 612374 | `fd3992f57b7dc0370986d997ee47dec67977c160f923ef13cfb093c7557f8120` (manifest) |
| `s22-run/data/replays.jsonl` (every one-shot replay (AY 13556 + Clean, 30 s), keyed by the bytes' sha256) | 254746 | `2075eb14ac01c2f7252963939bd2c9bb007883f250d3649d1cd38ddc2b41608d` |
| `s22-run/data/roots_a2.tsv` (the per-root outcome at 22a) | 1637 | `1394fb1488520bb5e2664d124aac169a3a8ba8150178f49553a9134323f746da` |
| `s22-run/data/roots_b.tsv` (at 22b without `guard`) | 1558 | `22d9d5aebc356f4c27526da6c0766a6c65e8d452520b54f26c3cdae3af0e0603` |
| `s22-run/data/roots_b2.tsv` (at 22b) | 1532 | `249ee471ebc4bd53cde53384bf51c8ca6713172e1ac17c74267da38ef6879875` |
| `s22-run/data/roots_c.tsv` (at 22c) | 1426 | `c8ffb5757536981d78c6b359708e2c6fd5f05b1653b458eb69d8a3dbcb9a8e77` |
| `s22-run/gaps/offline300.jsonl` (the 300 s offline replays (U128MulConst, the cut fixture's first form, div_rem_1e16 at 22b)) | 1215 | `60d5c82d712a59696beec6b8477f87e0900ea549a466f061d1928d5e6826272a` |
| `s22-run/all/main/cf.tsv` (the whole-core probe, main (s21's probe)) | 551233 | `b101041de05e3da67f0c374fab868125b93a3acc0b0bff577dccd1f5e22589c7` |
| `s22-run/all/a2/cf.tsv` (at 22a) | 549147 | `5aa2016b37cf923c57b8aa1dfcba9f92e8f3d0119e7b503dc9095e62af7be78b` |
| `s22-run/all/b/cf.tsv` (at 22b without `guard`) | 549147 | `18362a69b86e099323f4eadb81674775ce9c30ea003360d43d54b28682629f35` |
| `s22-run/all/b2/cf.tsv` (at 22b) | 549143 | `553005f7b1f9d55d20f242dba93c527331c1eaaa0f9772cf1dbd6f03f6f1ecc4` |
| `s22-run/all/m/cf.tsv` (the merged tree without `catnf`) | 549143 | `553005f7b1f9d55d20f242dba93c527331c1eaaa0f9772cf1dbd6f03f6f1ecc4` |
| `s22-run/all/c/cf.tsv` (at 22c) | 549097 | `27bbc0dbf39597b696d3ee2d281212bcb10b8bee49b9b2e607e6706f2307edc0` |
| `s22-run/logs/regress_ac.txt` (every function whose theorem 22b and 22c change, with its census outcome) | 15294 | `65a0743277aae1fa379629ecec4d134c30be8cc1807b234d2c930548e8febbcc` |
| `s22-run/regress_ac/q/` (the 142 census-certified ones' 22c queries) (304 files) | 1007871 | `5a728191460fe8d000550f6ba1219110619e4c7ab4cc74e48a9f50b81065a33f` (manifest) |
| `s22-run/data/roots_regress_ac.tsv` (their replay (cached from the stage replays)) | 12191 | `d46e2a5ec1ff9899a429c0fa70701ffe9c63bc7f66fea018aa609cb7b8954d5d` |
| `s22-run/data/roots_regress_b2.tsv` (the `guard` step's 32) | 2544 | `e024796540313914298df56cbe52a6c654c217dea95452c26dee481167592987` |
| `s22-run/data/roots_regress_c.tsv` (`catnf`'s 112) | 9736 | `c954243b83fa2ccb1183e3025015e718112cd9f7cc9f2f155f795554ca63584a` |
| `s22-run/data/roots_fmt_m.tsv` (`u128` `__fmt_inner` claim by claim without `catnf`) | 228 | `83abd03be75c458d1d87b440a83f07a14eb3ad78201680b414835fb31414d069` |
| `s22-run/data/roots_fmt_c.tsv` (and with it) | 224 | `a21da9a3c071a77061b51d3bb5e521560fd2853b7c4bf2e3dd81ea103e237288` |
| `s22-run/logs/native_diff.log` (the native differential of both bindings (n = 20000)) | 5619 | `6e5f2277d9659fa62b23a45db32445f583657e6b3e684bf20a4516555e4d16b0` |
| `s22-run/logs/limb_exhaustive.txt` (`limb_exhaustive.c` at limbs of 1 to 8 bits) | 842 | `08e391232c553ae9775bceea0bcf20481b6c7f54513e11dcf72a88cb051a6449` |
| `s22-run/logs/limb_lemmas_z3.txt` (z3 5.1.0 on `limb/*.smt2`) | 156 | `f8d797d8cb498f1daab0c7d6f7e721201d208790c258280bebbf1552e6c3c9fc` |
| `s22-run/ayissue/a3.alethe` (the AY issue note's proof (the rejected step at line 542)) | 301160 | `a9c7d1f4ca86a5af6a7e52d4c682dc067aa025270b9a51a177476feec821f4e8` |
| `s22-run/ayissue/a3.clean.out` (Clean's rejection) | 411 | `106e3f5c9071c11be21bf79bf140a4f227c2c6dcbadb19b2eb32ecb8d26705f0` |
| `s22-run/goldens/pre22b/` (every golden before OD-203) (18 files) | 765241 | `d44b71de8e54603279042a64cadb5ecf95b48b629a64c473486a0e781a7f2ca7` (manifest) |
| `s22-run/goldens/pre22c/` (every golden before OD-204) (18 files) | 775808 | `801e514b3dbf21c7144d8e9004ce3d4eb16f7834473f8ef79a87d0f0271e9ec7` (manifest) |
| `s22-run/goldens/c1/` (every golden at 22c) (18 files) | 778544 | `8a456996b05a7eab0e96e09967bad1121459773ca1f0c9fc978d3bb5f48cb8c5` (manifest) |
| `s22-run/goldens/review_b4/review.jsonl` (the review of OD-203's moves) | 306 | `0d5abf96b1ef9407ab6dc669d2330eb54b6a731c036283c82831526ef260be45` |
| `s22-run/goldens/review_c1/review.jsonl` (the review of OD-204's moves) | 3279 | `6a74b62af2161b15ce0966940f29b2b1662221f696a23146be5bc9e49b397f90` |
| `s22-run/mutants_all/` (the mutant run (16 mutants; summary and each run's log)) (18 files) | 768232 | `6b909c0f3f70ef6a4f371b5ad64bf488f18e1951529be3c63d051e29b81c72c8` (manifest) |
| `s22-run/data/repeats_c.jsonl` (three more replays of the four slowest certified class queries) | 6519 | `eefb125ae4f0d9f4b15dfc212374572a4c82f5e141a5cfbe67e1028b4c811ae0` |
| `s22-run/qual_final/` (the final qualification, one test per process (48 lanes and the deadline-bound lane)) (50 files) | 195691 | `145c46f6b59bfaa2ac795735fd70304b8816c79457f89ccd610d2af2ee3365ca` (manifest) |
| `s22-run/logs/gate_a3.log` (the solver-free x86 body suite at 22a) | 42526 | `978561fb2293f064ffee7305c80b6951189e8323d31e04018b5fc533155e46f6` |
| `s22-run/logs/gate_b5.log` (at 22b) | 43285 | `c1ad89ca20809002567d47cabf8141909739996cec3c4469e47242f8b6404bab` |
| `s22-run/logs/gate_c5.log` (on the final code) | 43383 | `ea3409a8270616bdd7e24d2ad36ab045276e41d19db3062042a01c875d3d67a5` |
| `s22-run/logs/codegen_final.body.log` (the codegen body end-to-end lane) | 447 | `c1f4285ca039772eb305a821e8bdf32d43f71a40d753fd1f4e14556d08c9ac52` |
| `s22-run/logs/codegen_final.identity.log` (its replay identity (AY 13556), run with --nocapture) | 1656 | `5478a6ac2fc61a0cca4495eef83c56de156922e59128a0fa8a1f2a8c265a42ff` |
| `s22-run/logs/codegen_final.mrc.log` (the must-refuse corpus) | 494 | `3caf859ded2a9252e0e3f311684665b2600ab0c0c6796ef043425c30f9324ec8` |
| `s22-run/logs/e2e_i128_div.log` (the native i128 division end-to-end (lowering evidence)) | 301 | `d7605ff7f98d154305986076d168740ba08e5ad9cfd7bd3b511424e8b4ef0076` |
| `s22-run/logs/lower.log` (trust-cg-lower --lib) | 160481 | `6508f62bc3a4ee5c41972f29f0f3f4e35c251e5ff983449f11714e9f294e9e8f` |
| `s22-run/logs/check_fmt.log` (scripts/check_fmt.sh (the 6808 package's targo fmt)) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `runs/main-20649af.dylib` (the landing baseline bridge, main `20649afe9`) | 144762976 | `e12c1dc5259a255ebb6187865d12ef7063a7428518b706fe46353cdd67fd4228` |
| `runs/census-main-20649af/failed_roots.jsonl` (the landing baseline census) | 37128 | `c1c5242a5e5bbd756d8cbbabc9e938b8fc78165d28595b1481fb74942f0d3b8a` |
| `runs/census-main-20649af/stderr.log` (its body trace) | 1393482 | `93d00bc1d3a9af12a395131b6585fa883447fdb910371f3a02ddb46d7dde4853` |
| `runs/census-main-20649af.out` (its summary) | 1732 | `20150ce67b4e8fa6a270471267cbd5deccdce7f43ea7bfa496f78f16de5996da` |
| `runs/s22.dylib` (the slice-22 bridge, `b596e62fe`) | 144781504 | `5673600b69e80a1c7db7566d7a049ae05d331f87887b65285285a153c78cfba7` |
| `runs/census-s22/failed_roots.jsonl` (the slice-22 census) | 21510 | `46541325082da3ae6e86e9f281a83d8de6f03a3067f0052307f18357c0311464` |
| `runs/census-s22/stderr.log` (its body trace) | 1318993 | `bbc7f30b0fe989ddc24c5eb970e9df0729a13595f94cd3e6da78c467bd1f6640` |
| `runs/census-s22.out` (its summary) | 1687 | `3be1e456840874a594a933404744c34917b48885632816254b552d2ac0039cad` |
| `s22/compare/` (`census_compare.py` of the two rows) (4 files) | 1639 | `4148fc8dcfbd28703b35904ffb0869a34626aa0bf8c762afddbddd7c602762b7` (manifest) |
| `s22/logs/census_chain_kept.log` (the census chain log) | 1176 | `a5ba1a0ee25accfc4450adc879b65f0a153c66f23093b31b3d3dca2708b7edbd` |
| `s22h-run/records/mutants_verify.txt` (§8's mutant run: the fixed code and each of the six mutants over the `slice22::` tests) | 1598 | `15a87845aaf9854dbace1e0af79bc1c77d3f6c266ead5d63f39ae2e003314f9d` |
| `s22h-run/records/guard_controls.txt` (§8.3's guard controls with and without `guard128-zero-never-fires`) | 592 | `9225a3ed875c1e5cb86a8e6ad4cfe3469b4f6e1a0c9ca16d700c07ccacb0db44` |
| `s22h-run/records/qualification_od210.txt` (§8.1's OD-210 qualification lane, fixed and mutated) | 1381 | `ee72a5500e7a4204ea2482e070dd6e358192ed727ddce7b1d00c3023b3afae72` |
| `s22h-run/records/codegen_od210.txt` (§8.1's codegen OD-210 tests, fixed and mutated) | 1123 | `61458c3180cb903e876a26ef482aa6429c76d26a708242596c61a012053da5c7` |
| `s22h-run/records/final_gates.txt` (§8.4's gates on the final merged code) | 1271 | `7b3f3070759ca289bb1a3d7dcba255fb131c7c98cc634badac6241ce9946c143` |
