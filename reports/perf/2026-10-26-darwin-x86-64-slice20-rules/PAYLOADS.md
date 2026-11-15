# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, objects) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256; a directory's row is its total bytes over its
top-level files and the SHA-256 of its manifest (one line `<sha256>  <name>`
per file, sorted by name). `census/payloads.py` regenerates the table. The
README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s20-design/README.md` (the slice-20 design (§1-§8)) | 55280 | `d7f8a8afdb12e7893b00296c7ed0feec101832f5c58ddb6319c6833d25a87a9e` |
| `s20-design/data/inscope.tsv` (the 33 in-scope roots and their classes) | 3586 | `754e8a7749f04b9c8c19372f23e8667749c73e98d825e71cf24ec6175a5202ae` |
| `s20-design/data/names_roots.txt` (census-ay13556's 106 failed roots) | 10673 | `e689e3842081a82ece8466b8dd3aac7a97e5e83ba804c7f37795994cc830bbc4` |
| `s20-design/data/runs/control.tsv` (the design probe's control run (main `376641c44`)) | 29855 | `608f8fbc579276899e6f6925bd4c41575e8bc8a099d04c815603f95c39359a70` |
| `s20-design/data/estimate_all.txt` (the design's per-root estimate) | 7121 | `ebf8b4699fb8d5a18decb5226a66e087bf8d707b624bec6b8e6426fcc2bf4671` |
| `runs/core-ir-s20/` (the census bridge's `core` trust-ir dump the probe reads) (88 files) | 6872217 | `a373904eb22245733f232a488c44f3add585031bbd65cdef707f2657af7349c0` (manifest) |
| `s20-impl/bin/x86_body_probe_s20impl` (the design's probe built from this branch (`probe/`)) | 91619312 | `5d0362276284027b636959a438ea2fd492915c592b318e9654423abb9a2a9d28` |
| `s20-impl/probe/branch.tsv` (its verdicts over the 106 roots) | 26234 | `ae754da43699f0ced59f6d83136fdc10b0456ea1efab1fe87f35a9bad194375e` |
| `s20-impl/probe/branch.err` (its stderr) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s20-impl/probe/branch.smt2/` (its queries and index) (301 files) | 2070016 | `0396f6e27aeb61f8888c0421e99ebf3461fad1012e559d18e3aaf3941d4db8fb` (manifest) |
| `s20-impl/offline/replay_33.tsv` (the 19 built roots' 92 queries on AY 13556 + Clean, 30 s) | 38616 | `4dbadb3e76150716ee21db16c5a60954619a6f8bf3a10ac7753d1d0090d3239d` |
| `s20-impl/offline/roots33.txt` (`census/roots33.py` of that replay) | 4997 | `60005fc892f19201ab32043ce8b216f63fc35513c90905829bb58b4810815c20` |
| `s20-impl/offline/shifts_30s.tsv` (the three shift fixtures offline at 30 s, twice) | 2267 | `07805b59e30b0793c9c08130f057132e9349de2973f195dcda71bd360faabda2` |
| `s20-impl/offline/shifts_300s.tsv` (the same at 300 s) | 1262 | `522f39a75584bd938dd451ca2d4e1eac44662fe1ccef4580641de251db21937e` |
| `s20-impl/offline/clean/` (the two Clean rejections (AY proof, certificate, Clean output)) (8 files) | 18068709 | `aa6a42376df40bd071ac09ceb97cbe36750496f1e270dc0e6882c524111f9616` (manifest) |
| `s20-impl/libcall/before/` (the 28 objects without the selector fix) (28 files) | 103566 | `536eaf6dc083ca590edbc296a7b1cc2b56d6deb5b5c9dc80b5c51fb5cd1e44a5` (manifest) |
| `s20-impl/libcall/after/` (the 28 objects with it) (28 files) | 103566 | `536eaf6dc083ca590edbc296a7b1cc2b56d6deb5b5c9dc80b5c51fb5cd1e44a5` (manifest) |
| `s20-impl/libcall/after2/` (the same, a second run) (28 files) | 103566 | `536eaf6dc083ca590edbc296a7b1cc2b56d6deb5b5c9dc80b5c51fb5cd1e44a5` (manifest) |
| `s20-impl/libcall/before.sha256` (their digests, before) | 2432 | `536eaf6dc083ca590edbc296a7b1cc2b56d6deb5b5c9dc80b5c51fb5cd1e44a5` |
| `s20-impl/libcall/after.sha256` (their digests, after) | 2432 | `536eaf6dc083ca590edbc296a7b1cc2b56d6deb5b5c9dc80b5c51fb5cd1e44a5` |
| `s20-impl/libcall/e2e-i128-before.log` (the native differential before) | 344 | `43a0b19ebe8793dbca790e2a44f6dac69f0e54abee7e42de24d7ee70b140bfdc` |
| `s20-impl/libcall/e2e-i128-after.log` (the native differential after) | 344 | `87a8ec0d83541ec59061233ae077fe5b9326f2ac38aa47f54ecac310c2af9f60` |
| `s20-impl/mutants/` (the first mutant run (22 mutants; summary and each run's log)) (25 files) | 2547042 | `106f6e98747d7ad163c817ec7527819775b21b553e9bc21ebc9ce2f201e57611` (manifest) |
| `s20-impl/mutants2/` (the mutant run on the final controls) (25 files) | 2149855 | `047100efc966d77a0b4107c0fdf97f9115d3ae06f104c57f399a77b3c80db330` (manifest) |
| `s20-impl/qual1/` (the first qualification run (before two fixtures were resized)) (4 files) | 11391 | `c4bb71d7a81d4d3dcdac38ac4920f4cc376ff15ed5d546abdf76de8ecf2e06ec` (manifest) |
| `s20-impl/qual2/` (the second (the resized fixtures; the shifts' second answers)) (4 files) | 12207 | `8d06e607a92c2f75556eff26b2ec9f4c7eb20b4286279f286181f89cac29d676` (manifest) |
| `s20-impl/qual3/` (the third (the deadline-bound record read)) (4 files) | 12873 | `fb0b1525a5d8317706b218d24ff5851d278b60f269827b1612e715945746678f` (manifest) |
| `s20-impl/qual4/` (the gap lane with the production one-query theorems) (2 files) | 7388 | `9fca21fcd6a712dea14286cdeb721abdf035a844fc3da4075d8018a46f360d24` (manifest) |
| `s20-impl/qual5/` (the final run: all three lanes pass) (4 files) | 18912 | `1d18a9454390b1a33bf5b42259497cf33c7f77660ca26e283221cd554edbcd03` (manifest) |
| `s20-impl/qual5x/` (the explicit 300 s deadline-bound lane) (2 files) | 1664 | `510046135d58075e2b08133175d5b80c03779228434df8301bf72e852e401a8f` (manifest) |
| `s20-impl/logs/gate-1.log` (the solver-free body gate right after the merge (before the golden)) | 41774 | `56b234c67fe3851264551f6b81192ad9af34f3d558ce2b9d4f624ed3735f9c2f` |
| `s20-impl/logs/gate-q5.log` (the solver-free body gate on the final controls) | 37628 | `ce21f03d53bd98f4d840affcffce2b21dae41adb92614f34ebef1e560cb27c6f` |
| `s20-impl/logs/s20-fixtures-2.txt` (the fixture printer (LIR, rows, theorems, variants)) | 414969 | `319f02167663ed9bf3376f6822066e647939eb0756da54bd8c5a481906b560fc` |
| `s20-impl/logs/golden-write-2.log` (the golden rewrite run) | 975 | `29ba6f3a72b9e78bcd7fd529da56b99ebbd48d4cc7c686090b8dc7d43e3d157a` |
| `s20-impl/logs/codegen-gate-final.body.log` (the codegen body end-to-end test, final tree) | 447 | `943efa64d35fa9e9d5f2c2dba28d6f800a5e2196283f75a808a88a815a25d676` |
| `s20-impl/logs/codegen-gate-final.mrc.log` (the codegen must-refuse corpus, final tree) | 494 | `6a8dad03f2756d877ae346500dcc70a67bb72cc3d90b8c124ea1860fa1157aed` |
| `s20-impl/logs/e2e-i128-final.log` (the native i128 division differential, final tree) | 301 | `0d5061923862f9663e92ae388ecbedbc6961e5c42941b1071d9a3097fab13f38` |
| `s20-impl/logs/lower-lib.log` (trust-cg-lower --lib) | 159251 | `ef30430515de613968b070775b3b050bb6f91217a595b83e7a6fa3f4160c8677` |
| `runs/main-bf5d4b2.dylib` (the landing baseline bridge, main `bf5d4b2c9`) | 144485872 | `c2f8144d924f2dea48da3070b1272565b2a156b6a5ee6886069dc23bfbcd10d2` |
| `runs/census-main-bf5d4b2/failed_roots.jsonl` (the landing baseline census) | 116391 | `9a7183ce21f38bafc0ac71fe699581ed8fc4f264f113dc5764b2947be0ae009c` |
| `runs/census-main-bf5d4b2/stderr.log` (its body trace) | 1791858 | `c76d4ed93eefe4c14815f7c8b703eca14b914fa84dac2df8a60709f4d99432e2` |
| `runs/census-main-bf5d4b2.out` (its summary) | 1735 | `858fae6ee6edbf63c251aa42643aa1b15785f39a74433dd01f6db5f4aefaabf2` |
| `runs/s20.dylib` (the slice-20 bridge, `104f7bf39`) | 144539240 | `e4cb5f44fc202cbe762b94fe99eeba0e453090ee82865c07591d5da7f9008a0e` |
| `runs/census-s20/failed_roots.jsonl` (the slice-20 census) | 95460 | `46c92978b4f5dd169c7b9206c585e69d72417f0859ec6c3b7c1f3c730c4d3d86` |
| `runs/census-s20/stderr.log` (its body trace) | 1688987 | `1a241ec439030f4f1eae26d44add0c5ac30ee6df37a010329a099ec8b771406a` |
| `runs/census-s20.out` (its summary) | 1687 | `ef7137870c704f896512e601b75d89d562045f1eb14943f543dad2d994e8dcc3` |
| `runs/dump-s20/` (its uncertified bodies' queries) (221 files) | 1799201 | `ecd4b38f159ab09d23cd53f9e9edb6ef6c69274fbd7f040990a79149f04fa528` (manifest) |
| `s20/compare/` (`census_compare.py` of the two rows) (4 files) | 3783 | `1a6d3b2b6c2ff7998a515bb0036147cf004310cef8fcd3cd159a2aa46ae6c1a1` (manifest) |
| `s20/logs/census_chain_kept.log` (the census chain log) | 1177 | `44e40c4ececb9f04b574a0671958d6dfa20f8e9648686f5d74a3ada413578955` |
