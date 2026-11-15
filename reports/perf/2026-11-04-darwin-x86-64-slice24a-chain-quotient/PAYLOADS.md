# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, binaries) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256. `scripts/payloads24a.py` regenerates the table. The
README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s24a-design/README.md` (the slice-24a design (§1-§9)) | 66779 | `670a3fbef2b237560a22a00d3ee679fb499a3b88e777104813197bb26029b302` |
| `s24a-run/fails-before/copy1_x86_source_bound_body_slice24_tests.rs` (the first fails-before copy `fails-before/make_fails_before.py` wrote into the 7ee0def54 worktree (never committed)) | 62004 | `38bbd4326ad24502e30195b37d7dac767acdc913946b5eb21064fc8df32015ba` |
| `s24a-run/logs/fails-before.log` (its run: every fixture, control, wrong lowering and variant on 7ee0def54) | 30651 | `826d6dac1904f5eb8f06bfc1509555197e521d9f54212a77bd40e38fe4460118` |
| `s24a-run/fails-before/copy4_x86_source_bound_body_slice24_tests.rs` (the review round's fails-before copy (the review's fixtures, variants and the O0 outcomes)) | 74410 | `594ce3e7bb5157f3a20841dcb1427e4c6c41bdb348365708537d58205a5fe5dd` |
| `s24a-run/logs/fails-before4.log` (its run on 7ee0def54: the first run's rows plus the review's pairs and the S24_O0 lines `slice24_o0_owners.txt` records) | 96444 | `b8c3e5e6095359bd8ee18c77af00d1048cc3b53f3288b3e0398877fe61807bfa` |
| `s24a-run/logs/jobC.log` (the golden rewrite, the solver-free module, the fails-before run and the three slice-24a qualification lanes) | 56065 | `02b24c04fea8a20e0a5fc58d22aab09eca372c85d6a5c842621ab7ceb2f84263` |
| `s24a-run/logs/print3.log` (the printer on the final fixtures (LIR, merged machine, chains, theorem, every control)) | 177294 | `594662d37b792d43ac11d549a94913de684f7e77b054e58b9046768ccb0f1da3` |
| `s24a-run/logs/jobD.log` (gates 1, 3 and 4) | 162944 | `de7ae325506734bf7d81e29f0ea5ea072bd98a2782558f39a9c09f8b5e2f2983` |
| `s24a-run/logs/gate5-fmt.log` (gate 5, format) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `s24a-run/logs/gate5-docs.log` (gate 5, documentation) | 87 | `367a2819b366278854f46d55efa2665fcda90bf59ecc31cdd73cba6f9438e898` |
| `s24a-run/logs/fix1.log` (the printer on the review's fixtures (the extra pairs' outcomes)) | 190289 | `1fc121fe6d8e1ea6939e815e83fc120b33d0cfa629523cd49132632c3fb9815e` |
| `s24a-run/logs/jobR1.log` (review round, first run: F12 multiplying the join value (its replay times out at 30 s; superseded)) | 74321 | `b9ae253fe4b759d75eafd32a7e69e4a421642e1d3789255c451d98ed7118420a` |
| `s24a-run/logs/jobR1b.log` (review round, second run: F12 multiplying on its left arm (its replay times out at 30 s; superseded)) | 74320 | `e2a94e41ef2269a0ab9c5001ea411da02aa2c90f1b22269d980f0e750f9931ed` |
| `s24a-run/logs/jobR1c.log` (review round on the final fixtures: the golden rewrite, the solver-free module with --nocapture, the three slice-24a qualification lanes) | 73018 | `de941622967e3dfc23a2f146466bd5be985109359523a2467aaf500def131d7a` |
| `s24a-run/logs/chainR.log` (review round: the fails-before rerun and the gates job at 4c54514eb, in order) | 744 | `1e11e6a447fa61264249983a8e708fc7dd4535eafd8d0596cb0f198cc39a6da1` |
| `s24a-run/logs/jobR2.log` (review head 4c54514eb: gate 1, gate 2's replay lane, gate 4) | 82385 | `180807bab2e98dd9dcb1a02a9ea8e8bfef6db304528048e89e2cc3a1142c8a6a` |
| `s24a-run/logs/jobR4.log` (the census fix (b342de091 before commit): the solver-free module with --nocapture and the three qualification lanes) | 63138 | `f9375d30bcce0488b099402c3d8aed06d43c846cc5056689ca75d16e36f269a7` |
| `s24a-run/logs/chainF.log` (final head: the fails-before rerun, the gates and the O2 census rerun, in order) | 3248 | `d0cee17a80c99e6c033cfb9c59687652f09ea10e2358ce98128c546349a2665a` |
| `s24a-run/logs/jobR2f.log` (final head: gate 1, gate 2's replay lane, gate 4) | 82203 | `e9ed521bc0594a210bf2c37958f082924a785c66684c4257c7a54ddd1ee934ff` |
| `s24a-run/logs/jobR3f.log` (final head: gate 2's refutation and credit lanes) | 21776 | `47b34af4b52009c2a08e5db1606f773738415998e35fdd98c0d6427df64e33a3` |
| `s24a-run/logs/gate5-fmt-r.log` (review head: gate 5, format) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `s24a-run/logs/gate5-docs-r.log` (review head: gate 5, documentation) | 87 | `367a2819b366278854f46d55efa2665fcda90bf59ecc31cdd73cba6f9438e898` |
| `s24a-run/logs/gate5-matrix-r.log` (review head: gate 5, the full-test-matrix hosts check (silent on success)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `build_bridge.t011.sh` (the bridge build helper census.sh runs (release, the t011 overlay)) | 2190 | `ed29e39bf5644e74ef7fdd74137a6a20130356801fb30fbdc8158cc870acaac6` |
| `census_t011_dylib.sh` (the census driver census.sh runs on one bridge dylib) | 2167 | `010b9d26fc7c07ad9e0df03c408f178bafb12c86c09f6973e9508a29ae5c2a7a` |
| `s24a-run/logs/census.log` (the bridge build at the review head and both censuses with their comparisons) | 3064 | `2f7ec3807e41de090cdcd1f13a26f3818fa5f57820ab5a68cefe121cf48ffc6b` |
| `runs/o2-s24a.dylib` (the bridge dylib both censuses ran) | 145549936 | `86ecd9154e0b6977a88c994848daed67389896bf7921a600bb47616101cf78ea` |
| `runs/census-o2-s24a.out` (the O2 census driver output) | 1718 | `557c74e9a7e475951dc8a2efa316d087cfb82a63effbbdc8783541ccbc3c3aa4` |
| `runs/census-o2-s24a` (the O2 census outputs (failed roots, refusals, stderr trace)) (7 files) | 5633203 | `b531d09ecbe8f0e7df1db42469ff57026db63876cfae80d1e9b03bac5de3c9a1` (manifest) |
| `runs/dump-o2-s24a` (the O2 census's dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `s24a-run/census/o2` (census_compare.py against census-o2-7ee0) (4 files) | 64913 | `f8da5ea378cfd73ff4418869eeae17bf702c16e03b3d547cd52d1d74223fd5e2` (manifest) |
| `runs/census-o0-s24a.out` (the O0 census driver output) | 1717 | `4d456d1951e18fb32356848607952c237e709850d13ac34c1a021e89b1bcbc40` |
| `runs/census-o0-s24a` (the O0 census outputs (failed roots, refusals, stderr trace)) (7 files) | 1397334 | `be5cf7d3cf0dbe9ae173f0bcb3dfbb29bfda1f54212d13a7a99654ceab96ac6b` (manifest) |
| `runs/dump-o0-s24a` (the O0 census's dumped queries) (0 files) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (manifest) |
| `s24a-run/census/o0` (census_compare.py against census-o0-7ee0) (4 files) | 20348 | `dd29b55e67535a91936777092771bb3d33b6417ec5df5e96772f9c68523992a3` (manifest) |
| `s24a-run/census/merged.txt` (the merged-chains attribution of both censuses at 4c54514eb (census_merged.py)) | 1593 | `796fec18d3ca395b449131366f4ac43d655da1b43fc118ea8b3eb55d4e49d400` |
| `s24a-run/census/merged-f.txt` (the merged-chains attribution of the O2 census at b342de091 (census_merged.py)) | 1225 | `2d7df01981d5e043a3a66512502ccdcdcafe4cf68631ad6b5ea8bb5190e01c9c` |
| `s24a-run/logs/census-f.log` (the bridge rebuilt at the final head and its O2 census, comparison and attribution) | 3178 | `a2f6f4378ab73a61f873686a4908751a5436b0c1ed410c021be94dbc6e002bbc` |
| `runs/o2-s24a-f.dylib` (the final head's bridge dylib) | 145549576 | `c4f0e0f1620685e3c3eda760e627280686e8f98d9848e25db0d1f6588a51c462` |
| `runs/census-o2-s24a-f.out` (the final head's O2 census driver output) | 1728 | `4c338cd20f5ee6392c07042ec22714cccea918594d322c8a80d973294ffebb90` |
| `runs/census-o2-s24a-f` (the final head's O2 census outputs) (7 files) | 5621132 | `ffaca210cac7c806455f59c92a79c114b35a92d3e5e7f2a8005504ccaa620166` (manifest) |
| `runs/dump-o2-s24a-f` (the final head's O2 dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `s24a-run/census/o2-f` (census_compare.py of the final head's O2 census against census-o2-7ee0) (4 files) | 64988 | `28269bd3f351b1d54daa07c52ab4398e35e0e6896bab7449ef0caed966c4fa40` (manifest) |
| `s24a-run/logs/gate5-fmt-f.log` (docs head: gate 5, format) | 164 | `902ed095283cbdb6c476511f390195cc0ba30b22c2a022bfcf57f0a346e6a80b` |
| `s24a-run/logs/gate5-docs-f.log` (docs head: gate 5, documentation) | 99 | `768cc0c433b211562ebdc365ba095ee2d282b6e6820e92385e5b259be7c3f184` |
| `s24a-run/logs/gate5-matrix-f.log` (docs head: gate 5, the full-test-matrix hosts check (silent on success)) | 14 | `9e1c56c9f77984b35ec5814708327c6847832cff3ce234742a41b2bc31fff60c` |
