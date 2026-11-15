# Payloads — slice 19 (the full canonical spelling), 2026-10-26

Every payload of [README.md](README.md) lives out of tree under
`~/tcg-scratch/`; this table binds each by size and SHA-256
(`census/payloads.py`). A directory's row is its total bytes and the SHA-256
of its manifest: one line `<sha256>  <name>` per file, sorted by name.
`replay/results/fresh.jsonl` and `resident.jsonl` hold every replay of this
lane (each line names its label and query SHA-256).

| payload | bytes | SHA-256 |
| --- | ---: | --- |
| `s19-ay-design/` (the design measurement: README) (2 files) | 55650 | `abbaa5b02aef11cc617858b29790ee3f0c542c570b5c5b77420252d35aa25a16` (manifest) |
| `s19-ay-design/data/` (its data (classes, chains, replays)) (123 files) | 3026034 | `87155cbe32c165d65e6da030c4a5382ea744ec3fb9eff2c1d81c12ec01eef03e` (manifest) |
| `runs/census-ay13556/failed_roots.jsonl` (the census row whose class this is) | 114673 | `ff7b2b9e95bbecb81240e8e02f8b4a8c87369cbdec9a953313f4939e15219caf` |
| `runs/census-s20/failed_roots.jsonl` (main fc03f94f2's census row (slice 20): the 41 still fail) | 95460 | `46c92978b4f5dd169c7b9206c585e69d72417f0859ec6c3b7c1f3c730c4d3d86` |
| `runs/census-s20/stderr.log` (its body trace (the regression check's outcomes)) | 1688987 | `1a241ec439030f4f1eae26d44add0c5ac30ee6df37a010329a099ec8b771406a` |
| `runs/dump-s20/` (its uncertified bodies' queries (the probe control's reference)) (221 files) | 1799201 | `ecd4b38f159ab09d23cd53f9e9edb6ef6c69274fbd7f040990a79149f04fa528` (manifest) |
| `runs/core-ir-s20/` (the trust-ir dump of `core` the probe reads) (88 files) | 6872217 | `a373904eb22245733f232a488c44f3add585031bbd65cdef707f2657af7349c0` (manifest) |
| `s19/names41.txt` (the 41 roots) | 4121 | `f03c4c0eb3fba662eba89b41e6293b77b987bd425b4fe505715e4ad0933cf704` |
| `s19/names_wide.txt` (the seven 128-bit add/sub functions) | 769 | `43e32fbd2fedc376d2c752b9ff004ad5f58c006ea2296310651379cc0f746eeb` |
| `s19/probe/x86_body_probe.rs` (the probe (local only, never committed)) | 71052 | `28fa8db92fd3511b6bafa562f59fe7f997add0d9f6824034321bbc33a8373c04` |
| `s19/redump/base20/smt2/` (the probe on main fc03f94f2 (control): the 41 roots' 208 queries) (209 files) | 1648782 | `95857d3aa64a735e87eb2fa1c903ce2eec0c3f9c5678049970b640a31f11bc92` (manifest) |
| `s19/redump/s1/smt2/` (stage 1 on bf5d4b2c9, before the wide-bits rule) (204 files) | 1061469 | `65c37aad0130a8fa1d2e07a167d535d05264c2ba11ee128e5d64f70a66ff7e6c` (manifest) |
| `s19/redump/s1b/smt2/` (stage 1 as committed) (204 files) | 1061625 | `0bfec36ec921ad580e7a85c5ce9eb513d6890bc3924dee04885623d2df901d7b` (manifest) |
| `s19/redump/s1b_mapped/` (the same under the census file names) (203 files) | 1056755 | `9f7c39171f50f9a40fe75fb28cb2a97622fdf7c3b1ed68f6d2dcbfb1384745ad` (manifest) |
| `s19/redump/s2b/smt2/` (stage 2) (204 files) | 1048742 | `14f6e10968b9b6fbdfd0e9f1b731b7516f025447bb618f39c9ad1052a5cf1408` (manifest) |
| `s19/redump/s2b_mapped/` (the same under the census file names) (203 files) | 1043872 | `ca584aace81849cde0280f8cd2ce054c957f46ce891a1e07a2cccdacdbabe950` (manifest) |
| `s19/redump/s3b/smt2/` (stage 3 as first committed, with every split obligation's claims) (2188 files) | 4977327 | `15c1fad2b796932059051c6a5f4859717d34c4e44c1f10d8888dd72c2b395de3` (manifest) |
| `s19/redump/s3b_mapped_claims/` (the claims under the census file names) (1984 files) | 3928585 | `ff061d6681f106577371e3e18fb60526d213102db5dcd592f7eaa97c1c406dc5` (manifest) |
| `s19/redump/s3c/smt2/` (the final code (the wide-bits rule without products), with claims) (2188 files) | 4975167 | `7249834fe4045f2db22b96f8029a12495fb978c96461f5b5f6bcc9fde233e040` (manifest) |
| `s19/redump/s3c_mapped/` (the same under the census file names) (203 files) | 1041920 | `b2b8d02562ec1c04b402e0c92717a8ea38cb77398662750449474d3e59c9f24d` (manifest) |
| `s19/redump/s3c_mapped_claims/` (its claims under the census file names) (1984 files) | 3928377 | `7ebeae7fe3f9c2adc23234924d35be0184339f69985f09fc4cbce14f49002467` (manifest) |
| `s19/wide/` (the seven wide functions on bf5d4b2c9: main's and stage 1's first bytes) (14 files) | 44869 | `ee8e509171532f5add3b115c12db94fd77075c9c3ca7cb8cf4a394b82d8cc55b` (manifest) |
| `s19/redump/wide_base20_mapped/` (the seven on main fc03f94f2) (7 files) | 26971 | `6b733900cd769e346b16996084fff4c5f245ff23a0b71eb9eded885dc1e98da4` (manifest) |
| `s19/redump/wide_s1b_mapped/` (the seven at stage 1 as committed) (7 files) | 18553 | `11baba3bbc2cf070324fa94c2b8dd3734a89461723dc6e72e55028b7557105cf` (manifest) |
| `s19/redump/wide_s3c_mapped/` (the seven on the final code) (7 files) | 18553 | `11baba3bbc2cf070324fa94c2b8dd3734a89461723dc6e72e55028b7557105cf` (manifest) |
| `s19/sub128/` (SubU128's query in slice 18's spelling, inlined, named, both claims) (4 files) | 2077 | `c28688934e0804b13f0c6ab1b6b2189e1786be34a98e35d1740157bdb5763a20` (manifest) |
| `s19/replay/results/fresh.jsonl` (every one-shot replay, keyed by query SHA-256) | 945579 | `9fc574b803811a517ea4b1bcf81fd8233c78b1476283294a58f505846ccca2f6` |
| `s19/replay/results/resident.jsonl` (every resident replay) | 112039 | `dac9ad2dcadd36d4d23217e53cd60412775b0190519c92e11666a9da4e814796` |
| `s19/replay/results/wide.jsonl` (the seven wide functions on bf5d4b2c9) | 5766 | `2c33bc4b7bc071eea86eec5245c64ea82fc856a59f647d5aa5ab9d5d49cd10e8` |
| `s19/logs/chain_meas2.log` (the stage replays' log) | 9527 | `138b9a170ea28b7378ee3fcd6ec856caa3f3abf9d096589b04071052e864c1a3` |
| `s19/logs/chain_meas4.log` (the claim replays' log) | 40193 | `3d85ab45f959fb4160222081e7f97d1f8d65d9561ef446f2b6893e24c90afd95` |
| `s19/logs/claims_resident.log` (the claims' resident leg) | 19814 | `1b06f882b62ef74693c9710a77f522f0f1c822c08f899f6384c9dbdbf2baefc6` |
| `s19/all/base20/smt2/` (the probe over every function, main fc03f94f2) (3973 files) | 10393049 | `92091fed8d9bb9cdd12183e372f14713b283128e036e77bce82ee4565508174a` (manifest) |
| `s19/all/s3c/smt2/` (the same, the final code) (3955 files) | 8388450 | `160c7f7822effe806a60f76c9a5eb0292494ea8efd7fa8d6178a505dcdfb4576` (manifest) |
| `s19/regress/s3c/changed.jsonl` (every function whose bytes change, with its census-s20 outcome) | 440426 | `f67c19a64c8d5ceabd6e615b9c2aeea16ff6bbe6b646368f17ad6949f290fc28` |
| `s19/regress/s3c/queries/` (the census-certified ones' new queries) (1571 files) | 2823739 | `7a4e40a15d5aa8fd367abb680397469e002fa66e9634fb8ab010bbb357f40cb4` (manifest) |
| `s19/logs/regress_s3c.log` (their one-shot replay and the report) | 296691 | `183bf9ff913ddd4636ad7693f5c413d71fe5a297646bf8b14a4de3783dba8890` |
| `s19/goldens-main20/` (every golden on main fc03f94f2) (16 files) | 772443 | `0d9a3d71caf5496971cf6373ec5bbfa38c1969d81ed11f9f323304dc2738df87` (manifest) |
| `s19/goldens-s1m/` (stage 1's goldens) (16 files) | 704884 | `781ce71e66954159abf76515354d6bdd1c3a70651e38bc524f1cd011c8b5c398` (manifest) |
| `s19/goldens-s3m/` (stage 2's and 3's goldens as first committed) (16 files) | 704988 | `c44edf091453f4060868d9a5d81d7ec9c25c68035717f90e570989b098fcad15` (manifest) |
| `s19/goldens-final2/` (the final goldens) (16 files) | 704939 | `69938334694dca005f5bbf2ae989f81856730f2d752b8108b32030eedf3a4f52` (manifest) |
| `s19/review/stage1/review.jsonl` (stage 1's golden review on bf5d4b2c9 (every file but slices 11 and 20)) | 31802 | `9fde890863f7c61e896e298deac33b5c0482b8aef875768bad53f80f2fcedad2` |
| `s19/review/stage1/z3/` (its z3 queries) (308 files) | 789176 | `6472650c3072695c2eb5956e403162cb05225a21e26338293c0d0b8e7cc926cf` (manifest) |
| `s19/review/stage1m/out/review.jsonl` (stage 1's review of slices 11 and 20 against main) | 7150 | `83602841d0298c7c1511ecdb456cb1bb8910c831a8995ba42875d320c7e76c8a` |
| `s19/review/stage1m/out/z3/` (its z3 queries) (68 files) | 804539 | `584d13f3c3c40bbbf7d759b57360a6250a697139f3dcc455529bc10ff78cee11` (manifest) |
| `s19/review/stage2/review.jsonl` (stage 2's golden review) | 414 | `30d5387af7e8e864f0e190f9dee07197bfde5388671f1e88abe378ec38154f9d` |
| `s19/review/stage2/z3/` (its z3 queries) (4 files) | 2180 | `b063c5655dd0d285832057e7484d0b3e903ddaf930a34f266ba6679d4fb57ae0` (manifest) |
| `s19/logs/slice19_s1m.txt` (the slice-19 library tests on stage 1 (counts)) | 7146 | `995e433adcc466f69fed7eabbdde4ee5cebdba7bf63946629483763488e47094` |
| `s19/logs/slice19_s3m_stage23.txt` (the stage-2 and stage-3 library tests (counts)) | 1628 | `dc13151c93610d4ef10472983eef05c07e1243bce89eb7765e148b9ce1807614` |
| `s19/fails-before/stage1.txt` (stage 1's mutants on bf5d4b2c9) | 24010 | `933709cdbdad3b05714b6ad58d5f16c04721a51493a03cd5da6e84460c19c644` |
| `s19/mutants2/stage2.txt` (stage 2's mutants on bf5d4b2c9) | 5187 | `86e60dbed8b9de3da85a8aa4b1db3885152fc65fa38575da1975f8eddaa90a9a` |
| `s19/mutants3/stage12.txt` (the wide-bits and two stage-2 mutants on fc03f94f2) | 932 | `d692f1f0aeb8462e479bdb06247502154df198930c00739b59f6379299c4d10f` |
| `s19/mutants3/stage3.txt` (stage 3's mutants) | 2519 | `a93bc1ef329a37432f8ad8314998edb36ea9f801c60cce34bd538538b9ff0b7b` |
| `s19/logs/gate_final.log` (the solver-free body gate on stage 3 as first committed) | 40647 | `09bd32ee25458bfbd626c1fc24f7e9071b657e116944caa020ece890f327a9fe` |
| `s19/qual/stage1/summary.txt` (stage 1's qualification on bf5d4b2c9) | 4184 | `31f769a4d6d9f65f6efa07d13227c3d6403326e5242c4cde251965d60f737a66` |
| `s19/qual/final/summary.txt` (the final code's qualification) | 4485 | `95509d4b2e3ae892f6223c35ddba69fa284d54abcc2d39944bc60655df021e1e` |
| `s19/qual/final-rerun/summary.txt` (the three moved lanes re-run with the updated records) | 346 | `9c59082cea52344aec6fbc5860119ba28a280203379140c449411b322662cb2d` |
| `s19/logs/gate_final3.log` (the solver-free body gate on the final code) | 40383 | `6b656e6be0eebf16d625becdd22c1054b2718ef12ababa4c44da2481122649ff` |
| `s19/logs/subset_final3.log` (the slice-19, slice-18, slice-11 and golden tests on the final code) | 21183 | `a5f03ab87c7e2f3302dff443db2e3a214a507f738b39992d6aa0edb084064c9e` |
| `s19/logs/gate_lower.log` (trust-cg-lower --lib) | 160997 | `82f3c3de613162595be6f8635af33c67fb45ab6ce8f4944d60a9465be6667d58` |
| `s19/logs/gate_codegen.log` (the codegen gate) | 1968 | `7c26ae2b3d064583b5ded971d610700fa0bb18c414bf3345a03c6487d8beee8f` |
| `s19/logs/gate_codegen_merged.log` (the codegen gate after merging origin/main 5d732f441) | 1874 | `f75bd41ff64e26118f679622ab8a12fb24013025fd2a6fb19d55b8f6b5a3fbba` |
| `s19/logs/tippy_trust-cg-verify.log` (the lint run the installed package refuses) | 22491 | `362ae5b8cbffda51c66c044bc17f16b93c085d99528f2ed1ed4eda7b65fdaca7` |
| `s19/logs/libtests_final.log` (the fixture-solver library tests on the final code) | 51333 | `3d38c648f9d98b4b9e6583a876d7c1e2ce7853164584cdef123daf319776b74f` |
| `s19/logs/libcheck_main20.log` (their failures run on main fc03f94f2) | 19092 | `eee80a6c7836d11e8186cfd31bcb4a053399df0ef2b8d407ce191cd04406c572` |
| `s19/logs/libcheck_final4.log` (and on the final code rebuilt) | 19092 | `00c0c089dbb193a205ffcaef8b22cb777c0f44fb7e3d868776155ac77722688b` |
| `runs/main-5d732f4.dylib` (the landing baseline bridge, main `5d732f441`) | 144537480 | `ce09ce31c89693941348794448cfbfdd12019214531c172c849f075cc2568a8f` |
| `runs/census-main-5d732f4/failed_roots.jsonl` (the landing baseline census) | 94614 | `69e71fc0ae95c01b13f6f12c811baf0c71df0c3af2a0fd98bf37819a9f0a8884` |
| `runs/census-main-5d732f4/stderr.log` (its body trace) | 1693891 | `c8c366109b5f232e5d034c2f7f46590419c4596784d94d097c95b61eb8e1ca8b` |
| `runs/census-main-5d732f4.out` (its summary) | 1732 | `0bb9fd744956a7bf8990c352d279c97baa1e47d9e2eace8a5e3dac12053fb560` |
| `runs/s19.dylib` (the slice-19 bridge, `427a6f3d6`) | 144662120 | `88feb28fc97262dbd573355c95c1488893eb211ea1af6e554ab9003b7ea46676` |
| `runs/census-s19/failed_roots.jsonl` (the slice-19 census) | 49759 | `3e9dab2076786e118d84334a91fe97509d9b7a6fff30bda070273c0b5681103c` |
| `runs/census-s19/stderr.log` (its body trace) | 1457268 | `6e754859c2f99ae8b9ac5aa2f48f27ed5efc58dc3d146ba76e1f5c610f9361a8` |
| `runs/census-s19.out` (its summary) | 1687 | `89972fe20f72de429c5beeb4a921ef77e93a6c468a1a06f2792353cf83ac6cf4` |
| `runs/dump-s19/` (its uncertified bodies' queries) (2 files) | 67807 | `f3aae11d948fd2a8be37ae77f6710e1889775eb35a8154b2420648b3c66a53b4` (manifest) |
| `s19/compare/` (`census_compare.py` of the two rows) (4 files) | 3227 | `78c1bc8836758fe322b85f15b2f844acc2feb20cb2b89d8c5d773ce81293c0b3` (manifest) |
| `s19/logs/census_chain_kept.log` (the census chain log) | 1176 | `288afb85cba1b2d8e32079c297eafc520be016cbe3be755e1b5ecf1d477d86fd` |
