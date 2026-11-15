# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, census outputs, queries, the bridge dylib) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound here
by size and SHA-256 (a directory by the SHA-256 of its manifest over its
top-level files, as `scripts/payloads235.py` defines it).
`scripts/payloads235.py` regenerates the table. The README states the numbers
each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s24c-od233/payload/s26-design-2026-11-08.md` (the slice-26 design as of this record (§1.4 bounds, §4.5 G-SEFRT, §5.1 replicas)) | 162437 | `53f0b8250619429a680b151c9af0d429bd17c7f678d5ae29902c340a1021ccbe` |
| `build_bridge.t011.sh` (the bridge build helper census-combined.sh runs) | 2190 | `ed29e39bf5644e74ef7fdd74137a6a20130356801fb30fbdc8158cc870acaac6` |
| `census_t011_dylib.sh` (the census driver census-combined.sh runs on the bridge dylib) | 2167 | `010b9d26fc7c07ad9e0df03c408f178bafb12c86c09f6973e9508a29ae5c2a7a` |
| `check_dylib_tools.sh` (the dylib preflight census_t011_dylib.sh runs) | 671 | `b1d0aedd8c3b5ecf1fbdae4891119c27736cd05f8b6018db1e6cde1b5fdb4a6c` |
| `s24c-od233/census-combined.sh` (the driver (also in tree as scripts/census-combined.sh)) | 2584 | `964cc9f0c97e718b5c0663469a67679c1e66818c480939196e3c3164ff7fa934` |
| `s24c-od233/logs/gates-71c5eb19e.log` (gates 1-5 on 5a49bb594 (gate 1: 511 passed, the fold test and every golden re-render test among them)) | 942269 | `894675a44a637af0bc95668c5952ac046567d068f3a6ea34461892983a0e1593` |
| `s24c-od233/logs/census-combined-5a49bb594-E0004.log` (the first run on 5a49bb594: the bridge build failed with E0004 (DRIVER-EXIT 8)) | 515 | `cac395446de1b22a55a7129ca63fde9a9357938c23598decd9fb0ec7651beed6` |
| `s24c-od233/logs/census-combined.log` (the run on 49748f126: the build, eight censuses, the comparisons, the G-SEFRT trace lines) | 5317 | `5d9d476ef509aa5cc129ac2335132bb35bad0842ee1adb7732aac00789c37496` |
| `runs/s26base.bridge-commit.txt` (the commit the bridge was built from) | 155 | `1cde0291afd8f8d9e2b6eae828a9bf63fa8d10173eda3ed5d4184551787df009` |
| `runs/s26base-base.dylib` (the bridge dylib (the seven other s26base-*.dylib are hard links of it)) | 154506228 | `e974e53bd84854b5cd06d3bbf00ef805590fed557f095aec72e1c4a361fa4c4d` |
| `runs/census-s26base-base.out` (the O2 census driver output) | 1745 | `354a75f83a4386f572b93aa3acc97d9b2290ed5281f6123f78872c6f4369e2c4` |
| `runs/census-s26base-base` (the O2 census outputs (failed roots, refusals, stderr trace)) (7 files) | 3545111 | `4c3edcdcff859ac372e610814213f480386cc0de02f1884eb6eee17c0a6f1509` (manifest) |
| `runs/census-s26base-base/obj` (the O2 census's emitted objects) (1074 files) | 1382667 | `d44e431db2fce2d819ecbedbf37474bfa29fbbc7d243c46d19fec4bb7afd820b` (manifest) |
| `runs/dump-s26base-base` (the O2 census's dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `runs/census-s26base-o0.out` (the O0 census driver output) | 1732 | `b9ac07855e88c92c17614d6260313515074eddfe66f9e6be05391c41a2826495` |
| `runs/census-s26base-o0` (the O0 census outputs (failed roots, refusals, stderr trace)) (7 files) | 1417787 | `d5842956332caf6555512e23a297a5227f20bc193b0a64489321b82d71563643` (manifest) |
| `runs/census-s26base-o0/obj` (the O0 census's emitted objects) (3426 files) | 4682079 | `9b431bdbb673e56faf4a67c97aa74605269502e5db6c7f09842e1367730a68be` (manifest) |
| `runs/dump-s26base-o0` (the O0 census's dumped queries) (0 files) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (manifest) |
| `runs/census-s26base-o3.out` (the O3 census driver output) | 1734 | `93f788a7af217ba95daeeb1ea73d0c5f53e8a8e7583f24df28b45bb59245fb0c` |
| `runs/census-s26base-o3` (the O3 census outputs (failed roots, refusals, stderr trace)) (7 files) | 4055437 | `b5ddee96ad87fb7cffe34b979c2cc04ac2417af24756f14b2d18f4f9d7df200e` (manifest) |
| `runs/census-s26base-o3/obj` (the O3 census's emitted objects) (1029 files) | 1191191 | `bdc51149266b96012b283f8efaeeef8c7b23584922169409936431453cdf5dfd` (manifest) |
| `runs/dump-s26base-o3` (the O3 census's dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `runs/census-s26base-l.out` (the O2, no-x86-licm census driver output) | 1761 | `80183670845791bf33d6a66ecc3a51b0927c1732342ee84e1e7b3fecaa2ef9a6` |
| `runs/census-s26base-l` (the O2, no-x86-licm census outputs (failed roots, refusals, stderr trace)) (7 files) | 2383407 | `be5a93ae8e8cdfded8588e7255cd581dd692a075c7997d866d7bc414370eff2c` (manifest) |
| `runs/census-s26base-l/obj` (the O2, no-x86-licm census's emitted objects) (1159 files) | 1607581 | `61a4bb012ec0b157161a1b1482235508db146b964580d82b4019dd8ba451b7eb` (manifest) |
| `runs/dump-s26base-l` (the O2, no-x86-licm census's dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `runs/census-s26base-lr.out` (the O2, no-x86-licm no-x86-loop-rotate census driver output) | 1801 | `6326e0b428765c0e49b5d29964649d7e5eb819bc66382d875369525f7c19d5c4` |
| `runs/census-s26base-lr` (the O2, no-x86-licm no-x86-loop-rotate census outputs (failed roots, refusals, stderr trace)) (7 files) | 1870172 | `ffde58006fefae13ed92052dccae1abae4ab9805c7fdc726fedc2c122a8d1a4b` (manifest) |
| `runs/census-s26base-lr/obj` (the O2, no-x86-licm no-x86-loop-rotate census's emitted objects) (1197 files) | 1699938 | `bbf5a619a5e23e9319e1588f834f661a861ff43d36e5f9abe58b2095e73b8fba` (manifest) |
| `runs/dump-s26base-lr` (the O2, no-x86-licm no-x86-loop-rotate census's dumped queries) (6 files) | 28315 | `1a21c0459329e53147af5de532b233c894683e6908b63c0f8883a93e21b8321a` (manifest) |
| `runs/census-s26base-r.out` (the O2, no-x86-loop-rotate census driver output) | 1768 | `b1833a8f9d17a8e6f4422f8cd74fb1c730c20d0956b7d51e82dc528a05a8e981` |
| `runs/census-s26base-r` (the O2, no-x86-loop-rotate census outputs (failed roots, refusals, stderr trace)) (7 files) | 3533071 | `05431a0025f45fda4217b5a9dc84516fa1b3b9181fa13bedcdaefa3b01080ff1` (manifest) |
| `runs/census-s26base-r/obj` (the O2, no-x86-loop-rotate census's emitted objects) (1075 files) | 1385083 | `31d35723c8c96e6bd89a5ba116da8ff3cff2ab1a96a282749694af3d9491d929` (manifest) |
| `runs/dump-s26base-r` (the O2, no-x86-loop-rotate census's dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `runs/census-s26base-all.out` (the O2, LICM, rotation, if-conversion and cmov swap off census driver output) | 1878 | `1e4ce66d27b77d83220bd0f8e747eeb2c9c1eaf8344d51c73f79d291761d85be` |
| `runs/census-s26base-all` (the O2, LICM, rotation, if-conversion and cmov swap off census outputs (failed roots, refusals, stderr trace)) (7 files) | 1829075 | `439f8efb1b8fea4f3a16d462311bf316e753ab45dea527dc2b5c0743ed0ce384` (manifest) |
| `runs/census-s26base-all/obj` (the O2, LICM, rotation, if-conversion and cmov swap off census's emitted objects) (1199 files) | 1706857 | `2b54212a017362a67a6f587c8b5eae3ff190db50ba2538a66d4b9f4b7a7585c7` (manifest) |
| `runs/dump-s26base-all` (the O2, LICM, rotation, if-conversion and cmov swap off census's dumped queries) (6 files) | 28315 | `1a21c0459329e53147af5de532b233c894683e6908b63c0f8883a93e21b8321a` (manifest) |
| `runs/census-s26base-tir.out` (the O2 with dump-trust-ir census driver output) | 1816 | `53c260b0b76a7a262445ea0a1ca4d330168e0d70f904e2be514b86b7fc026569` |
| `runs/census-s26base-tir` (the O2 with dump-trust-ir census outputs (failed roots, refusals, stderr trace)) (7 files) | 3545896 | `fc417ea17f16d6356d0c39db0c5eef156a885e0cdb539920e0c249184ec50188` (manifest) |
| `runs/census-s26base-tir/obj` (the O2 with dump-trust-ir census's emitted objects) (1074 files) | 1382667 | `d44e431db2fce2d819ecbedbf37474bfa29fbbc7d243c46d19fec4bb7afd820b` (manifest) |
| `runs/dump-s26base-tir` (the O2 with dump-trust-ir census's dumped queries) (4 files) | 6057 | `98dc07bac48ccf20db4c6f5fae355350838b7b8a09342d9b4f07c76652660bed` (manifest) |
| `runs/tir-s26base` (the TrustIR containers of the dump run (1,288 .trust_irbin with their .json)) (2576 files) | 11314108 | `16c172ca29da3c671b555dfefb69274fbd4dce0d890bc0218c58722d8430abb8` (manifest) |
| `runs/compare-s26base-base-vs-l` (census_compare.py: base against l) (4 files) | 27323 | `f8cfcf2bb40a6e6652d2c6e3b22fd3e1db863d877fbb5e6440f2205ad8cca63a` (manifest) |
| `runs/compare-s26base-base-vs-r` (census_compare.py: base against r) (4 files) | 17074 | `d5befd82a2c0411b31b0e2993700015a87bb88b586e61435a6c2b6adf119dfca` (manifest) |
| `runs/compare-s26base-base-vs-lr` (census_compare.py: base against lr) (4 files) | 31349 | `a3fa0fede58fb80f6e65b743fe9dd10ae0feb7d925d3ea277cbb5c19439f673d` (manifest) |
| `runs/compare-s26base-base-vs-all` (census_compare.py: base against all) (4 files) | 31716 | `832489a9581e429863a4124e0c6c8fcdd6ee5189895e68b3160ffda581b2df42` (manifest) |
| `runs/cmp-combined` (census_compare.py text outputs against the named censuses) (9 files) | 8922 | `9d0c1781058732abc9c205fc76c20b64ae15d78e8020627301b91b4d3b697f1d` (manifest) |
| `runs/cmp-combined/o2-s24c-vs-base` (census_compare.py output directory o2-s24c-vs-base) (4 files) | 16934 | `a84bc977439e9ba9b8185f0110c2c0843fc8608d21ffe9c3ef748e1f2a80ab1a` (manifest) |
| `runs/cmp-combined/o2-od233-vs-base` (census_compare.py output directory o2-od233-vs-base) (4 files) | 20308 | `87f374a4735c1a116e22388f71230c34b1bef6c7ab1f8b1ed6fbf21c1476e34c` (manifest) |
| `runs/cmp-combined/o0-s24c-vs-o0` (census_compare.py output directory o0-s24c-vs-o0) (4 files) | 20348 | `dd29b55e67535a91936777092771bb3d33b6417ec5df5e96772f9c68523992a3` (manifest) |
| `runs/cmp-combined/o3-s24c-vs-o3` (census_compare.py output directory o3-s24c-vs-o3) (4 files) | 19314 | `e452247f05d31cd855d27a71dd91af3af642bcb9e2ca1f4feeea7a8f3d196342` (manifest) |
| `runs/cmp-combined/o2k-od233-l-vs-l` (census_compare.py output directory o2k-od233-l-vs-l) (4 files) | 21737 | `840f6c6a21a2d43859693e9d20a76eee4ae6d79813deb9888aaca54967f75f6b` (manifest) |
| `runs/cmp-combined/m301-l-vs-l` (census_compare.py output directory m301-l-vs-l) (4 files) | 21706 | `cb654160522b4a94d3473bf233ad18c0ee0116cceb1e4ae9461ab69c68df8eb8` (manifest) |
| `runs/cmp-combined/m301-r-vs-r` (census_compare.py output directory m301-r-vs-r) (4 files) | 20453 | `3138cf76c8088a402a4db04090a8a2dcb152acbb6ef0e9336212902e9dda3d5e` (manifest) |
| `runs/cmp-combined/m301-lr-vs-lr` (census_compare.py output directory m301-lr-vs-lr) (4 files) | 22538 | `2a34a025488c08ad960db939d7526f0e489fbe8133dfddfeeebfb3124df9d7ec` (manifest) |
| `runs/cmp-combined/m301-all-vs-all` (census_compare.py output directory m301-all-vs-all) (4 files) | 19582 | `365e596c4c2b3700a91f851b7045f82a1d7695961fc847c9b8081b698c3ed78b` (manifest) |
| `runs/cmp-combined/s25-vs-s24c` (census_compare.py output directory s25-vs-s24c) (4 files) | 20490 | `541fa6f4a002ab34929ee7d59e18113fe261bea5924a6532c1189b422a34c988` (manifest) |
| `s24c-od233/payload/root_classes.py` (slice 24c's root_classes.py (copied), which classed the 214) | 3128 | `0a2f4d4f797e9161b6661e7d8ab453974f963216b06ed8df3266e373629d3bc8` |
| `g-sefrt/escape` (OD-235's before: EscapeAscii::fmt's seven parts, AY replays and the part-2 variants (nodiv, shift, t600)) (22 files) | 43155 | `4c40cba1f332cef054448d4b88c2c5110bf8fcb049bdac827bb1c0741f39ef9f` (manifest) |
| `g-sefrt/escape/replay.log` (the parts' AY replay times (part 2 unknown at 30 s)) | 301 | `0d05a1fb334400be6372ac7ebfc54353a207c1d88d3c18814df110210f528a9f` |
| `runs/census-o2-s24c` (the named census: slice 24c O2) (7 files) | 3549510 | `445984bf7c70826cf0ebb920a1e000bdd18b7ceeb44925248ddf1abc69e6d3f8` (manifest) |
| `runs/census-o2-s24c.out` (the named census's driver output: slice 24c O2) | 1720 | `cf0a2501855af2e2b09ec078c86ecf851d21e6d69c5210972c6ab85f1fb3213e` |
| `runs/census-o0-s24c` (the named census: slice 24c O0) (7 files) | 1398551 | `0d3ba8975ade94e6b7b645f31faf23d99a79fbac90e7c4e7cfdd46af699b0d1d` (manifest) |
| `runs/census-o0-s24c.out` (the named census's driver output: slice 24c O0) | 1717 | `1e9c60ba8bbcd5f35a253ae890e9bc5d80199ff9bed3b2137d14bac8b3c1ec58` |
| `runs/census-o3-s24c` (the named census: slice 24c O3) (7 files) | 4075714 | `118492d1d08d59f3fafdeba664da64df37392b4151f9429751d72ca778130995` (manifest) |
| `runs/census-o3-s24c.out` (the named census's driver output: slice 24c O3) | 1719 | `0d65f5f308382633ab33274a386d83a2220970f60a840f29833a58ce913125a6` |
| `runs/census-o2-od233` (the named census: OD-233 O2) (7 files) | 4382606 | `f2a2c04485d6ab6b08f0cb89e256ffb28cc300d45fdf7044adc56774da38c750` (manifest) |
| `runs/census-o2-od233.out` (the named census's driver output: OD-233 O2) | 1755 | `074769ec6cbad6f2fa8eacb6f6c5a300b5b9309b4ef2453dde84c33d6912215e` |
| `runs/census-o0-od233` (the named census: OD-233 O0) (7 files) | 3017949 | `79d14cbdd186cb8251e5c3ba083bc06ea3fdea879189a0f00bb92920acc4941e` (manifest) |
| `runs/census-o0-od233.out` (the named census's driver output: OD-233 O0) | 1753 | `e64337f3df5d7869b345e2bb3a47bd9a3590b940138c8ad1a79e8a41e3727d06` |
| `runs/census-o2k-od233-l` (the named census: OD-233 no-x86-licm (OD-235's before)) (7 files) | 2876038 | `259fb4bcdd8ea3025069e1c4aea58944d0e4ef6fba6159b9130975fd895f351b` (manifest) |
| `runs/census-o2k-od233-l.out` (the named census's driver output: OD-233 no-x86-licm (OD-235's before)) | 1771 | `b6356f7364df8082c1d769a73c8f846b4065aaa4300a6b19db43284e5b0b7972` |
| `runs/census-o2k-m301-l` (the named census: main b30110fcd no-x86-licm) (7 files) | 2882383 | `01fa7efb63383b764e5537fd86a90966eaf2c9582b129aa3b2f7e473f80e8595` (manifest) |
| `runs/census-o2k-m301-l.out` (the named census's driver output: main b30110fcd no-x86-licm) | 1766 | `97a90b733905a5a84eab5bc6bd76bb3f212d5957751cb5ab273a0fb8315f237d` |
| `runs/census-o2k-m301-r` (the named census: main b30110fcd no-x86-loop-rotate) (7 files) | 3921049 | `fa8cc35aa5759e53d5ece873c34038d66cfb4c514b433479752ca3b114bbf625` (manifest) |
| `runs/census-o2k-m301-r.out` (the named census's driver output: main b30110fcd no-x86-loop-rotate) | 1772 | `894645f0d78d55ca7cc7205954d991df3f3c0f360529a9a539c5dbc4776aec24` |
| `runs/census-o2k-m301-lr` (the named census: main b30110fcd no-x86-licm no-x86-loop-rotate) (7 files) | 2418408 | `4b4e706d206d88aa0f4d3b98cf9e05be73301fcad9ead5e2d7a4e70207596544` (manifest) |
| `runs/census-o2k-m301-lr.out` (the named census's driver output: main b30110fcd no-x86-licm no-x86-loop-rotate) | 1809 | `0a2a76d395e89a6b0a7391a65e6ddbc9e3d97e7832a5e9f32f4e095374d74bec` |
| `runs/census-o2k-m301-all` (the named census: main b30110fcd, four knobs off) (7 files) | 1842746 | `8610449696d2ff71ef6d13c2173002e1b1d8bf1bf5ea7120809bc69af7560fba` (manifest) |
| `runs/census-o2k-m301-all.out` (the named census's driver output: main b30110fcd, four knobs off) | 1883 | `7054342b256e8abb62cd615bb540a423e69767b56f59c27a9e942f43969829f2` |
