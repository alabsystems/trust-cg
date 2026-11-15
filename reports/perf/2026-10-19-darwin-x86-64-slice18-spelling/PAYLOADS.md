# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps) out of it. These payloads
were never committed. They are held on the measuring host (the x86_64 Mac of
the README) under `~/tcg-scratch`, at the paths below, and are bound here by
size and SHA-256; a directory's row is its total bytes over its top-level files
and the SHA-256 of its manifest (one line `<sha256>  <name>` per file, sorted by
name). `census/payloads.py` regenerates the table. The README states the
numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s18-design/` (the design: README, DESIGN-DRAFT, RULING-DRAFT) (3 files) | 59552 | `47d2acb685df423f89bfa9158152cb3a11ac50ba8a7e89b8cb224b64cf0ce037` (manifest) |
| `s18-design/data/` (the design's measurement data (classes, respellings, replays)) (71 files) | 2330816 | `61f68b540f2d3979645a06c4f8ab385cbdc6f45c20879b3051d864a0db12b7c5` (manifest) |
| `s18-design/queries/orig/` (census-s17's 361 dumped queries (`runs/dump-s17/`, copied)) (361 files) | 3294333 | `eef707c76c7199bf1c9de7629d21d46221960194a277105af88c9bbc0fa952e4` (manifest) |
| `s18-design/queries/v17/` (the design's Python v17 spelling of the singles) (86 files) | 701090 | `4ddcb2b383363574b7eaae937e6cd35307ec4652c5318e9aace5e9a5469a7842` (manifest) |
| `s18-design/queries/v16/` (the design's Python v16 spelling of the singles) (91 files) | 802184 | `52f1760fe606a3260f80f4ea6c272213eecbca4e7cc342186a413c69b019b9f7` (manifest) |
| `runs/census-s17/failed_roots.jsonl` (the census row whose class this is) | 206027 | `d56e4a0864982aa2eba7623edd52b32643c45fb39de8e364a2e20aded5ee565a` |
| `runs/s17.dylib` (census-s17's bridge (`ac8424004`)) | 143283892 | `11290b17fa1c2fbc7758221a608da9b6f1c2fdee19874fe089c72170306b92c6` |
| `runs/core-ir-s17/` (the trust-ir dump of `core` from census-s17's bridge (`census/dump_core_ir.sh`)) (166 files) | 7014661 | `8438494166990a7b232788287c2f982227630999404dc77de42a0644ade984b2` (manifest) |
| `s18/redump/names125.txt` (the 125 functions the probe is restricted to) | 14799 | `4648067eefaa1d295ee7206ac24e64927e9e4b68858340a944ddd1f03c1d5726` |
| `s18/redump/baseline/smt2/` (the probe on main `190b3e53d` (control): its 361 queries and index) (362 files) | 3311331 | `34f3a78ea05bbe521334435e68f30ef60451cc481e19eefa01e305900916c05c` (manifest) |
| `s18/redump/baseline-ff44/smt2/` (the probe on main `ff44162f3` (control)) (362 files) | 3311331 | `34f3a78ea05bbe521334435e68f30ef60451cc481e19eefa01e305900916c05c` (manifest) |
| `s18/redump/B/smt2/` (the probe with stage 1: its 361 queries and index) (362 files) | 2874772 | `3c6fb82025ed3fc874bca962dbeb18e534d5d330b40821eb15443d4fcd32c55f` (manifest) |
| `s18/redump/B_mapped/` (the same under the census file names (`census/compare_probe.py`)) (361 files) | 2857774 | `ea54f35aaa2c1a9b6c5be4fb883707e80432b778292ac84a44755e5af3274a78` (manifest) |
| `s18/replay/b_12713_fresh.jsonl` (stage 1's singles on AY 12713, one-shot) | 43701 | `1886bc1f0bdb94ce9ad2f6f7330ee2a8a172f7f11c859b6918cd9a3cc345bc3a` |
| `s18/replay/b_12713_resident.jsonl` (the resident leg) | 17594 | `e483c38a84fd95100dbdf54b42e908b2b11dbdcb5b98d8c3c8964449cafe4c92` |
| `s18/replay/chain_B.log` (the chain's log) | 18637 | `219092bd08e1ae897497c8986ac97638250bb1184a7e86f358861688424d09e8` |
| `s18/replay/b_13556_fresh.jsonl` (stage 1's singles on AY build 13556 (`ebde49de3`), one-shot) | 47946 | `04273776bae7791233453cd332a5c722bbac9ccceae3fcd14d65726187107cb6` |
| `s18/replay/b_13556_resident.jsonl` (the resident leg on 13556) | 19090 | `22eca796a6adef6644ee3dd26bf289d26c8987f5e8814fb8f0a04cf7859eb257` |
| `s18/goldens-old/` (the 14 goldens before slice 18 (main `190b3e53d`)) (14 files) | 581433 | `4f6a640b00b5fa791ade613572278ea4e3e21e7aaa1042feeab0d093976c6a32` (manifest) |
| `s18/review/stage1/review.jsonl` (stage 1's golden review: sweep and z3 per changed theorem) | 37713 | `9f3ce67dc1a70787f20918c262715879a4a807b8b5993cd703b646601744a564` |
| `s18/review/stage1/table.md` (its per-file table) | 705 | `d8e06805b043ad675e0a92fce969184f9475a2853deea6a1bc571bf780efe872` |
| `s18/review/stage1/z3/` (the 368 z3 equivalence queries) (368 files) | 1033477 | `eb902f05ed328d323f5ffa0b44c750463d2139f0cfb5894146382a21600c39f3` (manifest) |
| `s18/logs/gate-B3.log` (the solver-free body gate on stage 1) | 34338 | `705ac09175ffbcfb3e224f008caa69a68bb976dbeead9c9dba979cc2836dbb33` |
| `s18/logs/slice18-B3.txt` (the slice-18 tests' custody and sweep counts on stage 1) | 3090 | `4e3b696ac77edc7ccc909847212fab8c11448d435c6dd5eafe8139d31ad39784` |
| `s18/logs/golden-write-B.log` (the golden rewrite run (`TCG_X86_BODY_SNAPSHOT_WRITE=1`)) | 172681 | `c49ba13083772b55b04e4ed98960dddb6eeebfb0d79189648ae7e90e79c2144f` |
| `s18/qual/stage1/` (stage 1's qualification, one test per process: logs and summary) (39 files) | 173704 | `eb99c460e12b8f07d49781246483d340b12edd612890b9a459d5f43b984bb279` (manifest) |
| `s18/qual/stage1-rerun/` (the re-run of the moved lanes with the updated tables) (12 files) | 66117 | `c0b0e19e49c9de3469302658aef72298c2c82c8186173a70c48e472b79e49263` (manifest) |
| `s18/qual/stage1-gaps300/gaps300.jsonl` (the six re-spelled gaps at a 300 s budget) | 2279 | `626591ef95edb2e7cdd664723f2eb6de60167c2e2e4d27999cefd6e80d5a4566` |
| `s18/mutants1/` (stage 1's mutants (`fails-before/run_mutants.sh`): the summary and each run's log) (12 files) | 6674186 | `ec84efcc5df4409d2d003b15b5fa4808829e0174657d146fa7c9ea0ddf2445be` (manifest) |
| `s18-design/queries/v18fs/` (the design's Python fold-and-bvsub-zero spelling of the singles) (84 files) | 654459 | `6f3c7f070253edf523f3f3bfde102351dadc1e8b7b456e9119f85e1b9bdbbfee` (manifest) |
| `s18/redump/C/smt2/` (the probe with stage 2: its 361 queries and index) (362 files) | 2827763 | `42fc3e40eb79203ff554ec84bfc0d411e2a55d8c422df0df68994fb98e58337c` (manifest) |
| `s18/redump/C_mapped/` (the same under the census file names) (361 files) | 2810765 | `77e905217a26d7123d576e0a92b8a53136bdf91681cfceb52a64f7c8cbba3efa` (manifest) |
| `s18/redump/C_diffs.txt` (the 14 singles whose assertion differs from the design's) | 1684 | `12de619a0d4ffd24bb51280ef4d3940427be31964a8c16b6da69bb12050b324d` |
| `s18/replay/c_12713_fresh.jsonl` (stage 2's singles on AY 12713, one-shot) | 46920 | `f68aebfb06cd85fb5cb38f1ddcc2cdbde63a5c98e0501ec23c64007ef221ce4a` |
| `s18/replay/c_12713_resident.jsonl` (the resident leg) | 21314 | `d4dcd3da7490f25551ea01e5cb33b30f1af8f3d6549f9bb76f425416d873f45a` |
| `s18/replay/c_13556_fresh.jsonl` (stage 2's singles on AY build 13556, one-shot) | 54581 | `a2f7e85ad13b54328069d68e708383a31f7a823b342c10788299f0459690e4d7` |
| `s18/replay/c_13556_resident.jsonl` (the resident leg on 13556) | 25286 | `895bee88e1bd1af3f01b56e891a0e6084fd14e10f0b4789d8b01936c9c5c50b8` |
| `s18/replay/cno/cno.jsonl` (can_not_overflow's query three times on a quiet host) | 1466 | `53829bafb0c458b470f6997a81661b66febac1bc2aa4717c308c003dd81ce56d` |
| `s18/goldens-s1/` (the 14 goldens of stage 1) (14 files) | 456021 | `de6043cfd69b7dfaf305478e249f56db55b98547a8338c0457476aca7947b4aa` (manifest) |
| `s18/review/stage2/review.jsonl` (stage 2's golden review: sweep and z3 per changed theorem) | 21303 | `2e4016a538eb3f8f4ab473607372aad49aa4b0feedea229a4c4e391ed5a5562b` |
| `s18/review/stage2/z3/` (the 208 z3 equivalence queries) (208 files) | 551639 | `19d6fdcd27c6ef6fe042953f5c4ddf36b65e94a4cbb0805472ee05e3cb4a1486` (manifest) |
| `s18/logs/gate-C4.log` (the solver-free body gate on stage 2) | 34719 | `676ed4525ec051a97d7c9e9e35a3d939f11962ad7d2a7c103ae61805017b45a2` |
| `s18/logs/slice18-C4.txt` (the slice-18 tests' custody and sweep counts on stage 2) | 3083 | `15df85778c195fb5d5219849f179672cb01e65363aa7b993df700a9f6b4b4959` |
| `s18/qual/stage2/` (stage 2's qualification, one test per process) (39 files) | 170803 | `3f99212e7afa817248172fe1c03932fe2b1c384c6fcb09071815879e929711e3` (manifest) |
| `s18/qual/stage2-rerun/` (slice 12's lanes with the updated table) (3 files) | 8326 | `46a8ff4157aebec0155f5377feaac8147814722f6628a237689a1cba6fefe219` (manifest) |
| `s18/qual/stage2-gaps300/gaps300.jsonl` (the two re-spelled slice-14 gaps at a 300 s budget) | 520 | `76eee463317d9857f46344c6688031d6da03d3baa1b3f5dd6a9bf53721b262ac` |
| `s18/mutants2/` (stage 2's mutants over the spelling controls (`filters.txt`)) (20 files) | 5045385 | `c44ec195f026fd4f189398fb949552f0c2607ad18fb6ccd8d0c2079ae07a0350` (manifest) |
| `s18-design/queries/v17p/` (the design's Python second spelling of the parts) (253 files) | 1668941 | `1a51934ab3765a29103a67317915170a3a80f7e95195463da2667354e0f6d5f8` (manifest) |
| `s18/redump/D/smt2/` (the probe with stage 3: its 344 queries and index) (345 files) | 2351773 | `d8c298b3133f17d746e11df73b31c300e6e86fa00add7e9252747409c2a5404d` (manifest) |
| `s18/redump/D_parts/` (its 253 parts under their region's original part name) (253 files) | 1668688 | `36030d4e43f3286713020065a46b5e4754dd0fefa7faa6bb108926066977ae93` (manifest) |
| `s18/redump/D_aligned.json` (the region alignment of the parts) | 37169 | `e7267365e7b2f3603143fa081f64d63cfef02b446cc1aa9afaa89cadd7854bab` |
| `s18/replay/d_12713_fresh.jsonl` (stage 3's parts on AY 12713, one-shot) | 121501 | `6ba882e770b5677d6c4647a64eb5876d8cc785541f4f057953abca7a472b6a9a` |
| `s18/replay/d_12713_resident.jsonl` (the resident leg) | 52023 | `0c3aee994fae45f136ab1ebcc666bf17315a63841e6bea7da8166f7662b3943c` |
| `s18/review/stage3/out/review.jsonl` (the parts golden's review: sweep and z3 per changed part) | 925 | `bfecf9ad5e6f8dac45bb4ae9cd570d3b217341f5ce235bcb4a356d0b8f8ab231` |
| `s18/qual/stage3/` (the stage-3 code's qualification ledger, one test per process) (39 files) | 171877 | `b32ca10a933a6597c1e8b6ad2b3c19bfec9992f1515ebdd43dcc66c479f66cfe` (manifest) |
| `s18/mutants3/` (stage 3's mutants over the slice-16 and slice-18 library tests) (8 files) | 550329 | `a30b4128ddd624a6b7b36f4c4f067d94e50be461510d05dba5a18bf53bc0a1a2` (manifest) |
| `s18/mutants3b/` (the bit-move unit test unmutated and under `respell-no-bit-moves`) (2 files) | 982 | `cfc14d88517d8e11190d482230856ff73a5d24a8a6d908c294173ac4af545c6c` (manifest) |
| `s18/qual/stage3-rerun/` (slice 16's host lane with the shrunk unrefuted record) (2 files) | 10244 | `4f00287785468e6a69b222bd9e12d7b747fae700aeb756098f2e872fce1f8ec7` (manifest) |
| `s18/logs/gate-D4.log` (the solver-free body gate on stage 3 (the final code)) | 35106 | `ec90102aa7aa9962840eec80964144b61d2aabc06ebef321c17ad136c796ff87` |
| `s18/review/stage3/out/Q/` (the parts golden's changed parts, old and new) (8 files) | 75440 | `7d0c56a0aecd53cae0d4b910e04c0f798a157aa43e453051c0156fcbe0fd617c` (manifest) |
| `s18/review/stage3/out/z3/` (their z3 equivalence queries, both directions) (8 files) | 129440 | `deac369da517b425cacf5a51744f53eb829c34f0220ecd29cd5c99d34d8eb6e7` (manifest) |
| `s18/review/z3folds-test/` (the local test that dumps the fold sweep's folds (never committed)) (1 files) | 2360 | `f1c3972fa6b2ff9cd817963ed97ac1a86813ff10261539a783d1b58a2d785da7` (manifest) |
| `s18/review/z3folds/folds.txt` (its dump: 32651 folds) | 2025735 | `387387e2388a957b101e48a4d995265a96edbd3408dcbc57ff2069b9dc0107af` |
| `s18/review/z3folds/` (the z3 queries (`review/z3_folds.py`), the planted control and `result.log`) (20 files) | 5456115 | `565279d28a03f42559bda60cf2cc1438c43e0a11d133ff747c3ef8034b58bda9` (manifest) |
| `runs/main-4a65bc3.dylib` (the landing baseline bridge, main `4a65bc3cf`) | 143324748 | `560cd0ddca8ed8e40176016f0c622600f83ecfaaedcd58d7ba4f984ef8fe9217` |
| `runs/census-main-4a65bc3/failed_roots.jsonl` (the landing baseline census) | 202004 | `e5db8137bf442b58522af0a1dbffa947995a2877e6a28d9dd6c50288224ffad2` |
| `runs/census-main-4a65bc3/stderr.log` (its body trace) | 2218449 | `7abf6935714e32e6aff7f3de45b0576784c4788c350c77a1496439e506e8d6c9` |
| `runs/census-main-4a65bc3.out` (its summary) | 1735 | `992f1b4084e9e313e35aaed699ddf5b67968b0f854a802a4a0a2f67f3108752b` |
| `runs/s18.dylib` (the slice-18 bridge, `ab1f6051d`) | 143342204 | `f0731fdd274f1d5463fd90d092bcd8d6d18c200e8b2e2aeb9e27add75583a822` |
| `runs/census-s18/failed_roots.jsonl` (the slice-18 census) | 123294 | `49de83e668ed8fab8ed7f5b3d92d64f9120e3511c84443b06173894a75b85285` |
| `runs/census-s18/stderr.log` (its body trace) | 1825352 | `d7b08304220f52ed301400d1908993bff829c0b8f69dff015b8cdda3e9eae768` |
| `runs/census-s18.out` (its summary) | 1690 | `1f80a5fa7215cf740287c18cd9b7149956d36efe724171da2380502d3df6036c` |
| `runs/dump-s18/` (its uncertified bodies' queries) (233 files) | 1837417 | `a6cd3e1005911ba6150b114f47b50dfc6e9d18aea26e604345e6b7a162059e41` (manifest) |
| `s18/compare/` (`census_compare.py` of the two rows) (4 files) | 10299 | `d3a021c2e606a9e593e6bef5c8c6340ebd9ad908a2ee7a84b370f505346e4d99` (manifest) |
| `s18/newly_failing/` (the newly failing queries and their offline replay on AY 12713 and 13556) (5 files) | 19961 | `261854b6cd7f233730ad5be15209f9a323068e3c9e6f8445c3cc3fc7c858e188` (manifest) |
| `s18/logs/census_chain_kept.log` (the census chain log) | 1178 | `8df275a6d795be704b14d72504640ca1f5071b8add6df8958cec831f06b1b7d6` |
