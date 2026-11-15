# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree,
and its payloads (logs, root lists, outcome tables, dumped queries) out of
it. These payloads never entered the tree; they live on the measurement
host under `~/tcg-scratch/` (paths below are relative to it), and the
README states the numbers each one carries. The SHA-256 of each pins it; a
directory's is the SHA-256 of its manifest (`census/payloads.py` prints
every row).

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/census-s15-cf98/failed_roots.jsonl` (the measurement row's failed roots (the slice-15 census)) | 530761 | `55cd27fb2da7837c9f2a6c67b773b6c5b2ab58f6cf837f219bc1582749271a16` |
| `runs/census-s15-cf98/stderr.log` (its body trace) | 3779503 | `b1afd36468e50e307bd26f628502d436f6c24950f0e51045941591fec94ba945` |
| `runs/core-ir-s9/` (the slice-9 dump of `core`'s trust-ir the probe reads) (88 files) | 5977212 | `8776e580c966c9f81c085885fd100f78da7de7dc9643fd78f539315bae0d6a69` (manifest) |
| `scratch14/class_names.tsv` (the 71 class functions (`census/classes.py`)) | 6929 | `ef2864b59d10fc38fb76d2de18337304b2d7ac052cceaa2014d52d42f42a9945` |
| `scratch14/dump_base/` (the probe over the 71 with the slice-12 owner (`--dump`)) (72 files) | 5579475 | `fa5e5a0d112687fded0216fb498d31911caa3503fc04709afab4250a212e6e75` (manifest) |
| `scratch14/dump_s14/` (the probe over the 71 with the slice-14 owner (`--dump`), with the built queries) (116 files) | 5902137 | `48da3840018f2100b2d5e7abf6fe38bcbc6048b4236cd2e5557bd5342e9cbf30` (manifest) |
| `scratch14/payloads/` (logs: library gates, qualification runs, mutants, the native test, the end-to-end compile, offline replays) (46 files) | 2526316 | `9659b0ef92e6688af1612b40b24daf66f241ccc57f5c9b8ff0745b62b0ec90c6` (manifest) |
| `scratch14/qdump/` (every query the pre-merge slice-14 qualification replayed) (52 files) | 84380 | `43cdfb08c9621a1c0f56b9a30628602b474df7647658b4d0dfb7142a8232832f` (manifest) |
| `scratch14/payloads2/` (logs of the gates after merging main 49b93b2ee) (34 files) | 2423612 | `732f829bcc1b317372a29f1dff4de245d4f06ff04d0785b23fb1e16a0a7133fc` (manifest) |
| `scratch14/qdump2/` (every query the post-merge slice-14 qualification replayed) (52 files) | 84380 | `43cdfb08c9621a1c0f56b9a30628602b474df7647658b4d0dfb7142a8232832f` (manifest) |
| `scratch14/exp/` (the division-encoding experiments (inlined, paired, 300 s replays)) (17 files) | 1381760 | `68dfabde29a67d43e4f9bf6a70863de1425048a5b7582b124c796d6324c86f55` (manifest) |
| `runs/main-a902.dylib` (the baseline bridge, main `a902ea9ef`) | 140943088 | `2c1ef38f0e8c8027c8bac697d881e56d6000eeb4f18eaec0b2b9fed4ba874482` |
| `runs/census-main-a902/failed_roots.jsonl` (the baseline census) | 414814 | `ba84a905957aafce215f313e8fd544f636e3bfa8fb79f7fa97985fd8653eb7b0` |
| `runs/census-main-a902/stderr.log` (its body trace) | 2586489 | `27e08b71c85bab7f852434e4d46ba8f47d715d7833674a40573b840423cf364a` |
| `runs/census-main-a902.out` (its summary) | 1720 | `10886fa47074d620feaeb97324e991737e168b531f46fa09041359477903b84d` |
| `runs/s14.dylib` (the slice-14 bridge, `ffdfb2b23`) | 141059808 | `6a297a1693d4920081ef6b72e63f1775665829a1ce6e57717d158a3717695012` |
| `runs/census-s14/failed_roots.jsonl` (the slice-14 census) | 378522 | `c015c553ebbf21661ca81416961e6d78e88b0f4cf56e75e2d58b4a7cce30ecc0` |
| `runs/census-s14/stderr.log` (its body trace) | 2400759 | `e3352da9a67f119d41315fd5d176fad603b5094f5dbc82191a92c904f83a2527` |
| `runs/census-s14.out` (its summary) | 1690 | `045172b8af303bba77951d3e5e4818a3699cf6b31e8493f484770b6c9de338ed` |
| `runs/dump-s14/` (its uncertified bodies' queries) (102 files) | 1245291 | `4fa59072951dc3994007a7b2a1d52d31c1724fd7c80e9addd5ea08c9632497f9` (manifest) |
| `s14/compare/` (`census_compare.py` of the two rows) (4 files) | 3632 | `d80b102f8a721351e7f1bef244a0f754bb03e485cca45b9ae122c6f21ebe485b` (manifest) |
| `s14/logs/census_redo_kept.log` (the census chain log) | 1173 | `1d1a9bc71f4dc5d11b36d3eab66992c88fb6a1ebfa0b632b20f4a6a7521f13f7` |
