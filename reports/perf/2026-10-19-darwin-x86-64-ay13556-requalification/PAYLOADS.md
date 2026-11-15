# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md).
A dated record keeps its Markdown narrative and its reproducer sources in
tree. Its payloads stay out of the tree: logs, outcome tables, dumped
queries, the overlays' manifests and the test binaries. They live on the
measurement host under `~/tcg-scratch/`, with paths below relative to it,
and the README states the numbers each one carries. The SHA-256 of each pins
it. A directory's SHA-256 is that of its manifest, one line `<sha256>
<relative path>` per file under it, recursively, sorted by path;
`census/payloads.py` prints every row. The overlay toolchains themselves are
not payloads: they are under `~/.local/share/trust-overlays/`, and their
manifests are pinned below. The census payloads are the coordinator's and
are recorded with the census row.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `ay-cert/bin/ay-main-ebde49de3` (the AY 13556 binary the overlays carry as `bin/ay`) | 169544116 | `55d348f454d5e939f32657222fd773b938ed444328400ba58efaa24f01103de8` |
| `ay-cert/bin/ay-main-ebde49de3.banner` (its `--version` banner) | 314 | `3a29b8c28045befb68e6327f5dbd2881705ae0d538bab5bb8b9c35c2f8bdf384` |
| `runs/requal-13556/overlays/x86-stage1-ay13556.overlay.json` (the root overlay's manifest) | 2359 | `cb33f79408ec4c0bd368d0578749c0e9a57df6f225e967a509af7176411bf46e` |
| `runs/requal-13556/overlays/x86-stage0-bridge-ay13556.overlay.json` (the bridge overlay's manifest) | 2936 | `acccbbb924352edf2cc32ac46472b2fb104e9c59d98d5ca3cc27e2a69459a90e` |
| `runs/requal-13556/overlays/x86-stage0-bridge-ay13556.trustc-wrapper` (its rewritten `bin/trustc`) | 667 | `0c61994e3c657e739df7f45b3acd398cacba141cb49d405c57f78e685f0d6019` |
| `runs/requal-13556/build_verify1.log` (trust-cg-verify's lib tests on the overlay, `QUALIFIED_AY` moved) | 2535 | `d1957a47e2381c1eef6bfb855896b804c7dad54962e3d63175487cc2b4803d19` |
| `runs/requal-13556/build_verify2.log` (the same with the new tables) | 1163 | `3317885d9a20379d10f68272544b80340343d178fdae18b94dd2cc4a5c1909a7` |
| `runs/requal-13556/build_gates1.log` (the codegen and trust-cg-lower test targets on the overlay) | 3770 | `25be78446eb539be3e836f563800ab0e2b9525079ef6d0c30c90802b4934e949` |
| `runs/requal-13556/verify-measure1.bin` (`measure1`'s test binary) | 475177144 | `c31515508a6cff6d3c50c1092d16f9f636901b42b19c10c3f95ca5bc971a1b74` |
| `runs/requal-13556/verify-measure2.bin` (`measure2`'s test binary) | 475177144 | `801f8e6e8a7ada6a57478cf07726dc945c8a947d4a6aa4d3244f88fbba79409f` |
| `runs/requal-13556/build_verify3.log` (trust-cg-verify's lib tests on the tree merged with origin/main `f75a45cc1`) | 1351 | `35bcf4a02399d39c0f16f204c8e72beeacbdc1b943cc705b37e1e79deea50bb4` |
| `runs/requal-13556/verify-measure3.bin` (`measure3`'s test binary) | 475192064 | `a972ed6c900aa37ac435d70771daf0f49b7c0b89039bd18bd7ed0b48395180ff` |
| `s18/qual/stage3/` (the baseline: slice 18's final ledger on AY 12713 (logs, summary, dumped queries)) (657 files) | 1018317 | `b065dcd137f35e3a259b9cdf0c248c4dd36dd00e1c745aad100a8f0d557ad4b9` (manifest) |
| `runs/requal-13556/measure1/` (`measure1`: the 40 tool-gated tests, one per process, `QUALIFIED_AY` moved, old tables) (659 files) | 1025320 | `4f54fa7bae45f92b113cca511c5f8ac9f8f7db08f5dbc36e613b06b1e90e3d46` (manifest) |
| `runs/requal-13556/measure2/` (`measure2`: the same with the new tables) (659 files) | 1024461 | `6bda800316317cad135d85403537bfc1d0ec92456d51478b77f5de85552cf01a` (manifest) |
| `runs/requal-13556/measure3/` (`measure3`: the same on the tree merged with origin/main `f75a45cc1`) (659 files) | 1024465 | `f42678e399080d2a9e23b265c8cd7da54e690fa838cc288066f99d6950132049` (manifest) |
| `runs/requal-13556/gaps300.tsv` (every remaining gap and `SubU128` offline at 300 s on AY 13556 (`replay/gaps300.sh`)) | 4602 | `967ce52526cc50e1ce613e63daafd3948ed9616cfd0c5b7445c1336950028ab8` |
| `runs/requal-13556/both_ays.tsv` (slice 9's `StoreJoin` and slice 11's `SubU128` on both routes and both AYs) | 1924 | `38a5bfadd546f43a76b4e38646f8bcbaaa95281af7a675f24856e7f96da4b202` |
| `ay-fix/land2/storejoin/` (the AY agent's export of the `StoreJoin` and `SlotU128` spellings before slice 18) (3 files) | 11136 | `cec866a25a8a32296ce0e23a62f518450d84d970b3413d89b8adf7a761fee158` (manifest) |
| `runs/requal-13556/storejoin_prev_spellings.tsv` (those spellings on both routes and both AYs) | 3002 | `1f0000d7728aac03f313a1f4c6a373a39587ec78cd1e9d7807efeae56957b71d` |
| `runs/requal-13556/matrix_capture.txt` (the qualification matrix capture (`TCG_X86_BODY_QUALIFICATION_MATRIX=1`)) | 1048909 | `603320070ff378547c8070b61910a3d41b778d71a2b13d01690ed2aae80b6545` |
| `runs/requal-13556/cex_check_measure1.tsv` (`replay/check_all_cex.py` on `measure1`) | 27846 | `8f78cc8594afc30ffebe8b65269cd09fe9e9990591929c99f2c5d64bab6cc608` |
| `runs/requal-13556/cex_check_measure2.tsv` (`replay/check_all_cex.py` on `measure2`) | 27846 | `8f78cc8594afc30ffebe8b65269cd09fe9e9990591929c99f2c5d64bab6cc608` |
| `runs/requal-13556/cex_check_measure3.tsv` (`replay/check_all_cex.py` on `measure3`) | 27846 | `8f78cc8594afc30ffebe8b65269cd09fe9e9990591929c99f2c5d64bab6cc608` |
| `runs/requal-13556/e2e/e2e_serial.log` (`replay/gate_e2e.sh`: the codegen body and must-refuse tests, serial, time-stamped trace) | 205914 | `b287df9f23abd315d0555d962a63d5197229f7057a403f4d97734f0e973b7e64` |
| `runs/requal-13556/gates/` (`replay/gates.sh` before the merge: each gate's complete output and the summary) (7 files) | 209597 | `ed3309e00a20a53a493eaeea0602b896a3ffd627f0affff6a22a6c81ef5c0ebd` (manifest) |
| `runs/requal-13556/gates-merged/` (`replay/gates.sh` on the merged tree) (7 files) | 209936 | `146bd2fe59ecc9ca004cb8c7660de2c0ab94c27ff59b24d713dd58d66feb2209` (manifest) |
| `runs/main-d0ecc85.dylib` (the landing baseline bridge, main `d0ecc859f` (build 12713 lane)) | 143403340 | `9b754868f79f50e2b1da537ddc3283bfcd97c486f74a6adbeb4a64bae9dc5567` |
| `runs/census-main-d0ecc85/failed_roots.jsonl` (the landing baseline census) | 123294 | `49de83e668ed8fab8ed7f5b3d92d64f9120e3511c84443b06173894a75b85285` |
| `runs/census-main-d0ecc85/stderr.log` (its body trace) | 1826801 | `cb3afa9342a5862e5c99f72dab9adfbfebd7a3f5f54ca86b8e3d0c118001a831` |
| `runs/census-main-d0ecc85.out` (its summary) | 1735 | `25d69e866979dfacf74f4d1805a6df091ef2da7af42f5c52573512b4ec6d37a4` |
| `runs/ay13556.dylib` (this branch's bridge, `f0113c522` (build 13556 lane)) | 143404180 | `de9f4943d490391f3667feb333445e87dcf964f4fcec094972d4f5c526a39e9b` |
| `runs/census-ay13556/failed_roots.jsonl` (this branch's census) | 114673 | `ff7b2b9e95bbecb81240e8e02f8b4a8c87369cbdec9a953313f4939e15219caf` |
| `runs/census-ay13556/stderr.log` (its body trace) | 1782776 | `23146d95a7bf1f85fe331f20f9306a666ff436989b2af43948327b65b2eec87d` |
| `runs/census-ay13556.out` (its summary) | 1710 | `56fda891280497a84af9f30f31988d90372bff593c415e7bf35699c42e189b2e` |
| `runs/dump-ay13556/` (its uncertified bodies' queries) (208 files) | 1643910 | `e15744dcbdefca868857f292eb59a4c2b90854aa31775dc69c03edc9d16bca09` (manifest) |
| `ay13556/compare/` (`census_compare.py` of the two rows) (4 files) | 1338 | `132e105b82dd0e7e0d54f653a90dffa414b0cf249b70815966286fbaeab32fdb` (manifest) |
| `ay13556/logs/census_chain_kept.log` (the census chain log) | 1182 | `3f5bf8e4f133e9f16029f4b9ac04ea0bb69ec58eee23b6dbfd1d099b82a0bac2` |
