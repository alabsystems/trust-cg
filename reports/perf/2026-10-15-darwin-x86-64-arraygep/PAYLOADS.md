# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, root lists, outcome tables, queries, bridge dylibs) out of
it. These payloads were never committed. They are held on the measuring host
(the x86_64 Mac of the README) under `~/tcg-scratch`, at the paths below,
and are bound here by size and SHA-256; a directory's row is its total bytes
and the SHA-256 of its manifest (one line `<sha256>  <name>` per file, sorted
by name). `census/payloads.py` regenerates the table. The README states the
numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/census-s14/failed_roots.jsonl` (slice 14's row (342), before the regression) | 378522 | `c015c553ebbf21661ca81416961e6d78e88b0f4cf56e75e2d58b4a7cce30ecc0` |
| `runs/census-s14/stderr.log` (its body trace) | 2400759 | `e3352da9a67f119d41315fd5d176fad603b5094f5dbc82191a92c904f83a2527` |
| `runs/census-main-2854ce/failed_roots.jsonl` (main 2854ce3e3 (813), the regression) | 934313 | `1b269fe3ebc9c8029c36d3abc634fab6bf7e82f7734da5991002c5a37278b17e` |
| `runs/census-main-2854ce/stderr.log` (its body trace) | 5172674 | `bfcea9d3461e30bebb1b93546aa2817fa3834c0242ab036632c01c328cecb31d` |
| `runs/core-ir-2854ce/` (the core trust-ir dump the probe reads) (128 files) | 6922152 | `d5090a7c92c082be4e8870bdc3aead4a956e67f3bc10bca47ee86d45ff97a6fc` (manifest) |
| `agep/cf5.tsv` (the probe (`--cf`) over the dump with this owner) | 557321 | `29f550df960856a0fb5d2d9cbd722686cca0e3e2c12b23a49fe55e3146ae9c82` |
| `agep/smt2-5/` (the queries it built) (477 files) | 2253661 | `9d701e0e49b2e8515e2666b631a5cc55adefd3fa1fb0fd9806e34011ff1a4b3a` (manifest) |
| `agep/qual2.log` (host qualification on AY 12713) | 9860 | `852f5d860e48f922638c2f5fd787fc3978179a49917356ec44b270ede7083801` |
| `agep/qdump2/` (every query the qualification replayed) (35 files) | 44911 | `d9dc49cc134593525c5770580b6e7ab24c2a9bd69905bfce33c709d7dd3666d9` (manifest) |
| `runs/main-cb390.dylib` (the baseline bridge, main `cb390e657`) | 143106476 | `e0f2f9a8d64b753e7f5e2e8cb500f1a59f78cf95aed52f45573966eac56da251` |
| `runs/census-main-cb390/failed_roots.jsonl` (the baseline census) | 856597 | `4e41aa6a2f48bde34b75c1102705469a63224c65366fb25a4939017fd6c59297` |
| `runs/census-main-cb390/stderr.log` (its body trace) | 4823661 | `a027b5a901119a65699bee0314d2b351b1dd900639672cf4b862692e553f9ae3` |
| `runs/census-main-cb390.out` (its summary) | 1725 | `86594670391f2169daad531ad51c209d83a43cab05b92df5e2c6c188bc45b355` |
| `runs/agep.dylib` (the ArrayGep bridge, `d12c627fb`) | 143094932 | `8de8c7b808b43a6d01ccd55de006ef970648c0b9f9e20e887fcccc5364c433d2` |
| `runs/census-agep/failed_roots.jsonl` (the ArrayGep census) | 253779 | `2fa9a1141c8a03a2723d46d1ce3eb37890072885c0e4620b138b47e5c7a04682` |
| `runs/census-agep/stderr.log` (its body trace) | 1831632 | `90abcb9adb16b4ac26840d78332126aa0bd235b781638a7db480f78b3031306e` |
| `runs/census-agep.out` (its summary) | 1695 | `f898c6b81022e6d149eec3bd799db561850a5b6d415f03a36f2fcc77f47b87bf` |
| `runs/dump-agep/` (its uncertified bodies' queries) (353 files) | 3086255 | `c4b758729d3e6c93db360bc8b8b10cc41d5b0a33481964a3f73122d3f282dba8` (manifest) |
| `agep/compare/` (`census_compare.py` of the two rows) (4 files) | 66754 | `c90a4605c3c53f235ce9539bac23c578389782104630d9d4461f4827ace46ea0` (manifest) |
| `agep/logs/census_chain_kept.log` (the census chain log) | 1177 | `e393d8d5f8ac6a9acbb87d8cecf2d78169af427ecf962cba8c3ac83d491678d7` |
