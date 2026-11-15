# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md).
A dated record keeps its Markdown narrative and its reproducer sources in
tree, and its payloads (logs, census outputs, objects, bridges, queries) out
of tree. These payloads were never committed. They are held on the measuring
host (the x86_64 Mac of the knob-ceiling record's Setup) under
`~/tcg-scratch`, at the paths below,
and are bound here by size and SHA-256.

- **A directory's row** gives its total bytes over its top-level files and the
  SHA-256 of its manifest. The manifest has one line `<sha256>  <name>` per
  file, sorted by name. An `obj/` row therefore omits the `trust-witness/`
  subdirectory.
- **Regenerating.** `lane/payloads_split.py` regenerates the table.
- **The numbers.** The README states the numbers each payload carries. The
  plain and `lr` censuses it compares against are bound in the
  [2026-11-06 knob-ceiling record](../2026-11-06-darwin-x86-64-o2-knob-ceilings/PAYLOADS.md).

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s26-design/README-s25.md` (the slice 26 design, revised onto slice 25) | 157351 | `9538cd9a576ba269f4cad95c2a83730014fa09657be10d808d3c5484fc2dc4cf` |
| `s26-rebase/run_censuses.log` (the run log (lane/run_censuses.sh)) | 1566 | `ee46ea6698aa234a57f8d2214d5a1c321a1dceaacd8684b2610521d7dde0341f` |
| `s26-rebase/per_root.tsv` (the 111 roots, one row each) | 152305 | `c6807408985594732ffbb49fcaa1f0f79a6b43599be3ffd183c3341ac64145b1` |
| `s26-rebase/work/` (the per-root attribution scripts and outputs) (8 files) | 338249 | `504cff83ef83832f3b9f526801dd6f7cc1b3b46001bab0b34ceff49f9638e8fa` (manifest) |
| `runs/o2k-m301-l.dylib` (census o2k-m301-l: the bridge copy) | 145593880 | `9f8567d76ce111d557799d4e53cb92615f0c212ef29174c8970df8c60e759461` |
| `runs/census-o2k-m301-l.out` (census o2k-m301-l: summary) | 1766 | `97a90b733905a5a84eab5bc6bd76bb3f212d5957751cb5ab273a0fb8315f237d` |
| `runs/census-o2k-m301-l/failed_roots.jsonl` (census o2k-m301-l: failed roots) | 216052 | `c5e5f36554867b631da2b5b66fe4b44cbf9a9fe9a8bcbd4e0394274152ed2ead` |
| `runs/census-o2k-m301-l/refusals.jsonl` (census o2k-m301-l: typed refusals) | 812318 | `3bee64e9205893d52fe1462a8e1838a2ef036f0fcb4ac0bc26b8b28f822908bd` |
| `runs/census-o2k-m301-l/stderr.log` (census o2k-m301-l: body trace) | 1850277 | `e92c6a05a52e71389e0a9981c815c5c8d09754fb50856b861b49bfdf2310642f` |
| `runs/census-o2k-m301-l/obj/` (census o2k-m301-l: emitted objects) (1110 files) | 1463642 | `8ab80b8d6f18659066b0606bcbb958f7dd0103789ec2f07c1b924bc867be8460` (manifest) |
| `runs/dump-o2k-m301-l/` (census o2k-m301-l: dumped queries) (17 files) | 52259 | `2c60496065bda068a279d471f66471e23db55a1179001d847e7a12d4dfdea2a5` (manifest) |
| `s26-rebase/o2k-m301-l/root_classes.txt` (census o2k-m301-l: first-refusal classes) | 1753 | `5648f070cdef9a9855b53ec66244dcb117ddb75941fbc94c1775b286d14bd781` |
| `s26-rebase/o2k-m301-l/vs-o2-m301/` (census_compare.py: o2k-m301-l against plain) (4 files) | 27069 | `f222c256d7f8424699bb83646f74fb1b9c9695a28ab7795e017f66d5a227577d` (manifest) |
| `s26-rebase/o2k-m301-l/lr-vs-o2k-m301-l/` (census_compare.py: lr against o2k-m301-l) (4 files) | 22211 | `11e2ed90de36adf9bd4e5e3d523c4b3c32e386e4c9c015e882a94cc657d7c5f5` (manifest) |
| `s26-rebase/o2k-m301-l/followup/` (census_s25.py: o2k-m301-l against plain) (3 files) | 359787 | `8d324532376747a5cd13259e634e041889812dc5ddb3f8c716e138b4da7e7533` (manifest) |
| `runs/o2k-m301-r.dylib` (census o2k-m301-r: the bridge copy) | 145593880 | `9f8567d76ce111d557799d4e53cb92615f0c212ef29174c8970df8c60e759461` |
| `runs/census-o2k-m301-r.out` (census o2k-m301-r: summary) | 1772 | `894645f0d78d55ca7cc7205954d991df3f3c0f360529a9a539c5dbc4776aec24` |
| `runs/census-o2k-m301-r/failed_roots.jsonl` (census o2k-m301-r: failed roots) | 315443 | `08458f538b2145312825b41e0cca0e0a455f22ca3e4240bba3ea53c8b6752261` |
| `runs/census-o2k-m301-r/refusals.jsonl` (census o2k-m301-r: typed refusals) | 1182569 | `bef426d6940a15179c7c060d46a1d669c7e51ec04788e735a655f7ade3bed4d0` |
| `runs/census-o2k-m301-r/stderr.log` (census o2k-m301-r: body trace) | 2419296 | `5aa2c058cf6c94a0a818a309debf1984f140d7afc6d41a75edd089edd3e819e3` |
| `runs/census-o2k-m301-r/obj/` (census o2k-m301-r: emitted objects) (1035 files) | 1279818 | `86881d04a8455d9511476c2ed44b84859ed2b6c460935fc6f507a115496a28ea` (manifest) |
| `runs/dump-o2k-m301-r/` (census o2k-m301-r: dumped queries) (7 files) | 9601 | `abeaee99fcb2968a59b57b3092a21d901adda164de8ede30d63aa51e8aecd3c1` (manifest) |
| `s26-rebase/o2k-m301-r/root_classes.txt` (census o2k-m301-r: first-refusal classes) | 1659 | `b43149f1f803a7d2d1e598610a9ca14b136e0ed0666f01b52c9e8e3479e899e6` |
| `s26-rebase/o2k-m301-r/vs-o2-m301/` (census_compare.py: o2k-m301-r against plain) (4 files) | 17256 | `dd7cd0bcf545cd9b062b76a60f40d99cf7fb20bf00dccdfac9e47e8813c3b1b0` (manifest) |
| `s26-rebase/o2k-m301-r/lr-vs-o2k-m301-r/` (census_compare.py: lr against o2k-m301-r) (4 files) | 30781 | `e39b6c51e4122dd317c925bdaf999f8f6ee621c8702af28cd08b337f3327d175` (manifest) |
| `s26-rebase/o2k-m301-r/followup/` (census_s25.py: o2k-m301-r against plain) (3 files) | 418590 | `e6959a609b22f28f4205a4b780f820902c7a2dbd35dc4ada24df5a00e1215640` (manifest) |
| `sefrt-diag/FILES.txt` (the diagnosis tree, file by file) | 3465 | `b89aa80eca20436976feeded17d222dbb29ae9e394930eb5b6f69ed31994363d` |
| `sefrt-diag/ay/SUMMARY.txt` (the census parts replayed on AY 13556) | 1110 | `abf75107d5e4813dd26d044336d9015a3c850baaeaf7848135f476fc18f91132` |
| `sefrt-diag/ay/o2k-m301-lr/` (replays of lr parts, with models) (18 files) | 52525 | `8a19aca0aa5a619baa3f9246f2f0e401fb1e001aa2680225ac6d83a9fbb7b54d` (manifest) |
| `sefrt-diag/ay/o2k-m301-all/` (replays of all parts, with models) (18 files) | 52525 | `5cce0d4b3bc3ca18f6a234dd644bd05c63f5fa7c7672d4b3d56fe15c4c00c0da` (manifest) |
| `sefrt-diag/ay/o2k-m301-allbm/` (replays of allbm parts, with models) (16 files) | 48792 | `02a45f895808c07ac7dc56cf8d88900278e06b17fac1d487b8a16022318cd589` (manifest) |
| `sefrt-diag/ay/corerun-attempt1/` (replays of the first attempt parts, with models) (18 files) | 50882 | `0648faa6fb084ce2d55ce120cf2eccf121bb0406668657ccdbdfa38026d1cd71` (manifest) |
| `sefrt-diag/corerun/run.log` (the census-identical core re-run (lane/corerun.sh)) | 1851 | `a5ce3b112bfc97fc10d65473f2004d90b8bd573e02158cb575099823d34cb9d1` |
| `sefrt-diag/corerun/attempt1/` (the re-run: first attempt parts) (9 files) | 34994 | `7943388551caf501f64f24fbd80138996bf596a37d92b160059860b11e95d8e0` (manifest) |
| `sefrt-diag/corerun/attempt2/` (the re-run: second attempt parts) (8 files) | 34395 | `c1fa96b0c8efcaccfd04451c35350cdc42d7ceb6c554a85ed59c5e418275c300` (manifest) |
| `sefrt-diag/corerun/rows-attempt1.txt` (the function machine rows, first attempt) | 58506 | `f54296a7d9f99e60b36c7aed505386a88139f87e5b5e139b7792a8221c7907d9` |
| `sefrt-diag/corerun/rows-attempt2.txt` (the function machine rows, second attempt) | 58556 | `8fbeafbbabef9a6a032b623e4474b203a00e886ea8a110b23266b564c33ffbbd` |
| `sefrt-diag/coremir/sefrt.core.mir` (the function runtime MIR under the census flags) | 63337 | `68685e04feefa38bc82c61d040495416b164ab62badf342cf5f1a56393496daf` |
| `sefrt-diag/synth/` (the defined queries, controls, AY outputs, certificates and Clean checks) (28 files) | 23701394 | `df941960d1b68564e3c8891d0fd9cf0364e2710cba6a9dab11c4f86267f897fb` (manifest) |
| `sefrt-diag/synth-recheck/` (the fact check: the seven queries regenerated and re-run on AY) (18 files) | 14029237 | `617092cdc254a743c4010ed207a6c559f39da377ed5cbd85f12ab7dd55ad3f9a` (manifest) |
