# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md).
A dated record keeps its Markdown narrative and its reproducer sources in
tree, and its payloads (logs, census outputs, objects, bridges) out of tree.
These payloads were never committed. They are held on the measuring host (the
x86_64 Mac of the README) under `~/tcg-scratch`, at the paths below, and are
bound here by size and SHA-256.

- **A directory's row** gives its total bytes over its top-level files and the
  SHA-256 of its manifest. The manifest has one line `<sha256>  <name>` per
  file, sorted by name. An `obj/` row therefore omits the `trust-witness/`
  subdirectory.
- **Regenerating.** `lane/payloads_knobs.py` regenerates the table.
- **The numbers.** The README states the numbers each payload carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s26-design/README.md` (the slice 26 design) | 76283 | `08df687a2a775b193d961c8bfa95af69a19a8c6442f1a1c7204922a224968ecc` |
| `od233-design/README.md` (the OD-233 design (its section 7 names slice_error_fail_rt)) | 67845 | `f6f7bbca675d0516cfbfa776498aa0f59e5fbf6e28ddfb646d434580d4de8a99` |
| `runs/o2-m301.dylib` (the bridge, main b30110fcd) | 145593880 | `9f8567d76ce111d557799d4e53cb92615f0c212ef29174c8970df8c60e759461` |
| `knobs-m301/census.log` (the run log (lane/census.sh)) | 20914 | `1f8bf836b88d79b1145ca9055ef3be5d8cf8408238c8b3798f8d1eed196b734e` |
| `runs/census-o2-s25.out` (census o2-s25: summary) | 1714 | `d3dea4def568298ee9d161d3d0609e7a894ad843decd0ab69072ba58df8d1ebd` |
| `runs/census-o2-s25/failed_roots.jsonl` (census o2-s25: failed roots) | 316504 | `6c923fd7703c22883c36a67310ce3f935ef02a2506a90399f1daef19718f30f4` |
| `runs/census-o2-s25/refusals.jsonl` (census o2-s25: typed refusals) | 1186480 | `98511129068e808377f6611d5987e76db51f14750cb46ba9f11d4a55de3e9af7` |
| `runs/census-o2-s25/stderr.log` (census o2-s25: body trace) | 2426127 | `7d28e07bef4525eb98f72ca0ec05d95b3d73b4076ec66f0a59de252835dd72aa` |
| `runs/census-o2-s25/obj/` (census o2-s25: emitted objects) (1034 files) | 1277402 | `9a0420b7c2b872148f77428351e1efb3790cfafca863d56622d0976831093603` (manifest) |
| `runs/census-o2-m301.out` (census o2-m301: summary) | 1719 | `c35e59d8841bec4e6ae9dced0007a28eb687f27d8fe6f56994f701610ccf0497` |
| `runs/census-o2-m301/failed_roots.jsonl` (census o2-m301: failed roots) | 316504 | `6c923fd7703c22883c36a67310ce3f935ef02a2506a90399f1daef19718f30f4` |
| `runs/census-o2-m301/refusals.jsonl` (census o2-m301: typed refusals) | 1186480 | `98511129068e808377f6611d5987e76db51f14750cb46ba9f11d4a55de3e9af7` |
| `runs/census-o2-m301/stderr.log` (census o2-m301: body trace) | 2426130 | `beffbff216122159952f92710ac017964cab9154e91f95fd7ca2d2cd3abe1ea6` |
| `runs/census-o2-m301/obj/` (census o2-m301: emitted objects) (1034 files) | 1277402 | `9a0420b7c2b872148f77428351e1efb3790cfafca863d56622d0976831093603` (manifest) |
| `runs/census-o2k-m301-lr.out` (census o2k-m301-lr: summary) | 1809 | `0a2a76d395e89a6b0a7391a65e6ddbc9e3d97e7832a5e9f32f4e095374d74bec` |
| `runs/census-o2k-m301-lr/failed_roots.jsonl` (census o2k-m301-lr: failed roots) | 169687 | `08d88d10fe4c449c6708e88d3ea2a27657ec00390cc059f6cbd29e01e276c0c9` |
| `runs/census-o2k-m301-lr/refusals.jsonl` (census o2k-m301-lr: typed refusals) | 637640 | `082fe2d1d5740c7d297adbef1d0e5208d4b0a65e0b406bd1e4e97d2ca1348a1f` |
| `runs/census-o2k-m301-lr/stderr.log` (census o2k-m301-lr: body trace) | 1607323 | `cfb1f2393b6f92ba37901281783bd340d485fa012023f2f563b62304d46310f9` |
| `runs/census-o2k-m301-lr/obj/` (census o2k-m301-lr: emitted objects) (1145 files) | 1531039 | `8466ba491e5298d76a75da2f2e00562d67e3ca98b3f78889ad5453b83fa15f19` (manifest) |
| `runs/census-o2k-m301-all.out` (census o2k-m301-all: summary) | 1883 | `7054342b256e8abb62cd615bb540a423e69767b56f59c27a9e942f43969829f2` |
| `runs/census-o2k-m301-all/failed_roots.jsonl` (census o2k-m301-all: failed roots) | 110489 | `7e489bb5b71f90e79fe8fac7e0b23d7e0ef4244a297c9eb041c1549974201a5e` |
| `runs/census-o2k-m301-all/refusals.jsonl` (census o2k-m301-all: typed refusals) | 417098 | `7092303ebf9aa835486ef59b685a6a4a24e24a71f9240944a47b8b2e9c58c77b` |
| `runs/census-o2k-m301-all/stderr.log` (census o2k-m301-all: body trace) | 1311319 | `9c80d29af40f9cb1b466e5089034e901b400cd89cdd20e825b48647a6274c364` |
| `runs/census-o2k-m301-all/obj/` (census o2k-m301-all: emitted objects) (1197 files) | 1693211 | `fe47d31bba7718c460fc500d16b8f3b0266a42743de50d2cff14291ddc9f24e2` (manifest) |
| `runs/census-o2k-m301-allbm.out` (census o2k-m301-allbm: summary) | 1931 | `819f881e94b6c9fec0a729ff6da095334e1a0dcd64ba8ad720c67d4b676c3d95` |
| `runs/census-o2k-m301-allbm/failed_roots.jsonl` (census o2k-m301-allbm: failed roots) | 104553 | `a6d5f31a1fc1095b6fa00cb889949cbb09cd6ee0dd246b987e19a04785b5e3b7` |
| `runs/census-o2k-m301-allbm/refusals.jsonl` (census o2k-m301-allbm: typed refusals) | 393438 | `a7bc484ef8ac53cdff02a7ddecb257bbc40265da763954d0595b56e723d56060` |
| `runs/census-o2k-m301-allbm/stderr.log` (census o2k-m301-allbm: body trace) | 1084399 | `8cb83d8d1eab2996372186c474a468c001ad7ca854b5cd7d6c3195aad795e0ee` |
| `runs/census-o2k-m301-allbm/obj/` (census o2k-m301-allbm: emitted objects) (1202 files) | 1699805 | `fc5a209c089c22bc4541369bc831e913def5adc2078e0eb7540893931cf723d9` (manifest) |
| `runs/census-o2lk-k3.out` (census o2lk-k3: summary) | 1787 | `e3775facfe5f6bd51df447ef401300bfc98b27d542f31a35305da6b51edc778c` |
| `runs/census-o2lk-k3/failed_roots.jsonl` (census o2lk-k3: failed roots) | 429175 | `b967dfa99dded3ce362fd0306cfa571dfa703bccfe6bdd502b4619cfbd437f00` |
| `runs/census-o2lk-k3/refusals.jsonl` (census o2lk-k3: typed refusals) | 1604244 | `4c15f11cf480ba5538fba1baf1cdf893cb1333e7389c244201e92681ac1b31a5` |
| `runs/census-o2lk-k3/stderr.log` (census o2lk-k3: body trace) | 3081757 | `df1b58aa1e4e62ed58263e943c9be50dd183ea0c975fe5bfd8680a457b89cb50` |
| `runs/census-o2lk-k3/obj/` (census o2lk-k3: emitted objects) (946 files) | 1145458 | `ee37a7bf1203169e3d28946a382936a416990d59c2b8e5763c3bbef251e93cca` (manifest) |
| `runs/dump-o2-m301/` (census o2-m301: dumped queries) (7 files) | 9601 | `abeaee99fcb2968a59b57b3092a21d901adda164de8ede30d63aa51e8aecd3c1` (manifest) |
| `knobs-m301/out/o2-m301/root_classes.txt` (census o2-m301: first-refusal classes) | 1534 | `57439a5b459b875d6290530628b81780c3410af994f31a04fb42dd0922dd01d7` |
| `runs/dump-o2k-m301-lr/` (census o2k-m301-lr: dumped queries) (18 files) | 68493 | `a06185f4975c130c940b46d57d98f1f436091decda63273c92d044950cedd79c` (manifest) |
| `knobs-m301/out/o2k-m301-lr/root_classes.txt` (census o2k-m301-lr: first-refusal classes) | 1753 | `e4f71a113b1f9422f0b25c322f5c8b6a93c4c930f2dba9392592d168b7a96d07` |
| `runs/dump-o2k-m301-all/` (census o2k-m301-all: dumped queries) (18 files) | 68493 | `a06185f4975c130c940b46d57d98f1f436091decda63273c92d044950cedd79c` (manifest) |
| `knobs-m301/out/o2k-m301-all/root_classes.txt` (census o2k-m301-all: first-refusal classes) | 1721 | `bcdbae853063291c873fdb46be4f325344483faa0dd217fc7075e1b079d8f437` |
| `runs/dump-o2k-m301-allbm/` (census o2k-m301-allbm: dumped queries) (17 files) | 66264 | `e36498dad02d96f18938d3c9cb12dd6cd8bff9e0e9dcf5956b887fedf783121f` (manifest) |
| `knobs-m301/out/o2k-m301-allbm/root_classes.txt` (census o2k-m301-allbm: first-refusal classes) | 1686 | `d18c225811b05417b7a6d9df33f82f61cd153f07f086ce03b32bb28646f8b7a5` |
| `knobs-m301/out/o2-m301/vs-o2-s25/` (census_compare.py: plain against slice 25) (4 files) | 16972 | `9f22e9d865bd9b28e1677e02f347fdb51ed9b07f25006b96914a8557e5e0f124` (manifest) |
| `knobs-m301/out/o2k-m301-lr/vs-o2-m301/` (census_compare.py: lr against plain) (4 files) | 30853 | `332e3c5e8d8f93d4ff4df58ae1d7551175c3df28f2b2571da47fe55af533de37` (manifest) |
| `knobs-m301/out/o2k-m301-all/vs-o2-m301/` (census_compare.py: all against plain) (4 files) | 35127 | `4eef35b1f93a23409da8bfe69b6da6513e2008de9c7a9ed52f6dc0d1711754e0` (manifest) |
| `knobs-m301/out/o2k-m301-allbm/vs-o2-m301/` (census_compare.py: allbm against plain) (4 files) | 35850 | `7058a944fa75c4033225baa72e1a65b2eb10d2a775ae43a081e617ade2212cbf` (manifest) |
| `knobs-m301/out/o2k-m301-lr/followup/` (census_s25.py: lr against plain) (3 files) | 343673 | `6ebf415ac9e7bd736a47c89a44b559932e166f54573f88d9754416561b50e48e` (manifest) |
| `knobs-m301/out/o2k-m301-all/followup/` (census_s25.py: all against plain) (3 files) | 326386 | `fa194e802f51327c558340c84ee2961bb91d1a408b85876cfb97318e562b0594` (manifest) |
| `knobs-m301/out/o2k-m301-allbm/followup/` (census_s25.py: allbm against plain) (3 files) | 310464 | `649aeb568b3a0fbee34e057326a17765dd5bfec58c0038617a0871ccc45c95b3` (manifest) |
