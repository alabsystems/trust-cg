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
  file, sorted by name.
- **Regenerating.** `lane/payloads_loop.py` regenerates the table.
- **The numbers.** The README states the numbers each payload carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s26-design/README.md` (the slice 26 design (its section 7 is this measurement plan)) | 76283 | `08df687a2a775b193d961c8bfa95af69a19a8c6442f1a1c7204922a224968ecc` |
| `runs/lk.dylib` (the bridge, 65f5e6cdb (the OD-232 lane)) | 145553312 | `7adef4356b559ab531850c48f7b1b81c563fff5fe831526d8367ed2489a6563b` |
| `runs/o2-s24a-f.dylib` (the slice 24a baseline bridge, b342de091) | 145549576 | `c4f0e0f1620685e3c3eda760e627280686e8f98d9848e25db0d1f6588a51c462` |
| `lk-run/logs/run.log` (the lane run log (lane/run.sh)) | 3732 | `f2cc30bac30baad33ae48c36929fbee444c74678ce5929b6ca1b6196ded6cb6e` |
| `runs/census-o2-s24a-f.out` (census o2-s24a-f: summary) | 1728 | `4c338cd20f5ee6392c07042ec22714cccea918594d322c8a80d973294ffebb90` |
| `runs/census-o2-s24a-f/failed_roots.jsonl` (census o2-s24a-f: failed roots) | 476199 | `3ec806ba3589411ce3f3b4f4676234e27d6a1a805f04d45f89a7f478016d9400` |
| `runs/census-o2-s24a-f/stderr.log` (census o2-s24a-f: body trace) | 3360860 | `ed973f959fd8b4e190d8efb1d73cc68db3ca01f4bb037668c59cd87b06719d4b` |
| `runs/census-o2-s24a-f/obj/` (census o2-s24a-f: emitted objects) (910 files) | 1072987 | `ac06a04f9185742eb7e31b9cfc27e15074f225ee755e0b9b4835ae2e550a9482` (manifest) |
| `runs/census-o2lk-plain.out` (census o2lk-plain: summary) | 1733 | `6ab47514c6550ba9cf5418cc83dd2ecfc265da697dcd5110b0ea9a187f96b496` |
| `runs/census-o2lk-plain/failed_roots.jsonl` (census o2lk-plain: failed roots) | 476199 | `3ec806ba3589411ce3f3b4f4676234e27d6a1a805f04d45f89a7f478016d9400` |
| `runs/census-o2lk-plain/stderr.log` (census o2lk-plain: body trace) | 3360854 | `d9fd397d20be2d1abc5991896091a9dcab63d7cfa208526abc6faea4558453f5` |
| `runs/census-o2lk-plain/obj/` (census o2lk-plain: emitted objects) (910 files) | 1072987 | `ac06a04f9185742eb7e31b9cfc27e15074f225ee755e0b9b4835ae2e550a9482` (manifest) |
| `runs/census-o2lk-k1.out` (census o2lk-k1: summary) | 1756 | `947d92a93d9ba792705da55fbd054b6b31e5bcf94b9138c560c7f2cc3714cfeb` |
| `runs/census-o2lk-k1/failed_roots.jsonl` (census o2lk-k1: failed roots) | 476198 | `045a564b1cb336808a595a1ddd07d8570a38cd2729db98270f7db3f9a96e61f6` |
| `runs/census-o2lk-k1/stderr.log` (census o2lk-k1: body trace) | 3359828 | `03f355b8eed73aad03027cfe7f522ed280df141dc0abb928530af1649d66b2f0` |
| `runs/census-o2lk-k1/obj/` (census o2lk-k1: emitted objects) (910 files) | 1072987 | `ac06a04f9185742eb7e31b9cfc27e15074f225ee755e0b9b4835ae2e550a9482` (manifest) |
| `runs/census-o2lk-k2.out` (census o2lk-k2: summary) | 1749 | `624b7efcf72a0e289cc9bf487993c04bbf64d51c1e11b338b96e89e1fdb3bf99` |
| `runs/census-o2lk-k2/failed_roots.jsonl` (census o2lk-k2: failed roots) | 450413 | `5a59cd5355c91084fa4f1dd4c281dc9e61494402084c1e1e7af03b49c53e959c` |
| `runs/census-o2lk-k2/stderr.log` (census o2lk-k2: body trace) | 3190824 | `1e1826a9431242e2df82233f53b9ea0fdfb9ff6ebab366a1e6a2625826364bfd` |
| `runs/census-o2lk-k2/obj/` (census o2lk-k2: emitted objects) (931 files) | 1122505 | `a64549d6c51ebfee111eb252ff9cb9652457eef21b0369b704d1835779444edd` (manifest) |
| `runs/census-o2lk-k3.out` (census o2lk-k3: summary) | 1787 | `e3775facfe5f6bd51df447ef401300bfc98b27d542f31a35305da6b51edc778c` |
| `runs/census-o2lk-k3/failed_roots.jsonl` (census o2lk-k3: failed roots) | 429175 | `b967dfa99dded3ce362fd0306cfa571dfa703bccfe6bdd502b4619cfbd437f00` |
| `runs/census-o2lk-k3/stderr.log` (census o2lk-k3: body trace) | 3081757 | `df1b58aa1e4e62ed58263e943c9be50dd183ea0c975fe5bfd8680a457b89cb50` |
| `runs/census-o2lk-k3/obj/` (census o2lk-k3: emitted objects) (946 files) | 1145458 | `ee37a7bf1203169e3d28946a382936a416990d59c2b8e5763c3bbef251e93cca` (manifest) |
| `runs/census-o2lk-k4.out` (census o2lk-k4: summary) | 1867 | `0c6bb6ee0548004638aab3254877d3b8bb39ff512bfb1ad123289cf954939e33` |
| `runs/census-o2lk-k4/failed_roots.jsonl` (census o2lk-k4: failed roots) | 429175 | `b967dfa99dded3ce362fd0306cfa571dfa703bccfe6bdd502b4619cfbd437f00` |
| `runs/census-o2lk-k4/stderr.log` (census o2lk-k4: body trace) | 3082918 | `2bb2a3ba3ae3a24e3207aa4bf8aa239402ec763118d66c429a4695f7b765b66b` |
| `runs/census-o2lk-k4/obj/` (census o2lk-k4: emitted objects) (946 files) | 1145458 | `ee37a7bf1203169e3d28946a382936a416990d59c2b8e5763c3bbef251e93cca` (manifest) |
| `runs/census-o2lk-k5.out` (census o2lk-k5: summary) | 1801 | `effbe351642480c52273c9bebec446fe095b769fe7696e6af175c05ee67f88b5` |
| `runs/census-o2lk-k5/failed_roots.jsonl` (census o2lk-k5: failed roots) | 476199 | `3ec806ba3589411ce3f3b4f4676234e27d6a1a805f04d45f89a7f478016d9400` |
| `runs/census-o2lk-k5/stderr.log` (census o2lk-k5: body trace) | 3361341 | `45984a97ec5e259871551986174be33015bd570ac0127ebaf922979c5c87d5fb` |
| `runs/census-o2lk-k5/obj/` (census o2lk-k5: emitted objects) (910 files) | 1072987 | `ac06a04f9185742eb7e31b9cfc27e15074f225ee755e0b9b4835ae2e550a9482` (manifest) |
| `runs/cmp-o2lk-plain-vs-s24a/` (census_compare.py output (cmp-o2lk-plain-vs-s24a)) (4 files) | 319 | `171a4a2fc5175e2664dcabc48e1c1c1b7bb053651b99923bf28bb8c605738418` (manifest) |
| `runs/cmp-o2lk-k1/` (census_compare.py output (cmp-o2lk-k1)) (4 files) | 319 | `171a4a2fc5175e2664dcabc48e1c1c1b7bb053651b99923bf28bb8c605738418` (manifest) |
| `runs/cmp-o2lk-k2/` (census_compare.py output (cmp-o2lk-k2)) (4 files) | 2575 | `898b42d455666f8c25272f34772ccab67565e2c2bfdb398d1ee4c20d5c0c393c` (manifest) |
| `runs/cmp-o2lk-k3/` (census_compare.py output (cmp-o2lk-k3)) (4 files) | 4880 | `2f70c3bce6b276334873218faf7c07ca7e0ddecca1a1bea26c23a31b66664ecf` (manifest) |
| `runs/cmp-o2lk-k4/` (census_compare.py output (cmp-o2lk-k4)) (4 files) | 4880 | `2f70c3bce6b276334873218faf7c07ca7e0ddecca1a1bea26c23a31b66664ecf` (manifest) |
| `runs/cmp-o2lk-k5/` (census_compare.py output (cmp-o2lk-k5)) (4 files) | 319 | `171a4a2fc5175e2664dcabc48e1c1c1b7bb053651b99923bf28bb8c605738418` (manifest) |
