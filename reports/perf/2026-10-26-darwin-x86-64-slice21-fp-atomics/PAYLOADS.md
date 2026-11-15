# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, binaries) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256; a directory's row is its total bytes over its
top-level files and the SHA-256 of its manifest (one line `<sha256>  <name>`
per file, sorted by name). `census/payloads.py` regenerates the table. The
README states the numbers each one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `s21-design/README.md` (the slice-21 design (§1-§7)) | 44184 | `d574029dc345d7c89acfdf1c050c761d3dd0cd5840db5ef6095be459400f22d2` |
| `s21-design/data/tables.md` (the design's AY 13556 table of every fixture and spelling) | 8411 | `122a1cac91d7fa2a8f5264e53930db2ef201465a8d02480b6fac774c850b9de2` |
| `s21-design/data/names12.txt` (the 12 roots) | 1185 | `e1c2f93939ca50e66473c335ed4a25361635c1d0578c1ed5355e9023f436d648` |
| `s21-design/hw/x86_probe.out` (the design's hardware probe (MXCSR, NaN rules, ucomisd, cvttsd2si, ld128, xchg)) | 1801 | `795d6c4e1ef0742d287514e9c90a07f58960a9ced12c2e6042df0a02bd40341e` |
| `runs/core-ir-s20/` (the census-s20 bridge's `core` trust-ir dump the probe reads) (88 files) | 6872217 | `a373904eb22245733f232a488c44f3add585031bbd65cdef707f2657af7349c0` (manifest) |
| `s21-run/bin/x86_body_probe_s21` (the probe built from this branch (`probe/`)) | 92447064 | `4a78170bf65c06b98d4fa38d0c8c8087c1d31d6ab2b63ffb8eb6a5f026a84754` |
| `s21-run/probe/roots12.tsv` (its verdicts over the 12 roots) | 1774 | `a2c219a76e32c751f9cbef8ed6b94623fe0528e4a347b6772ca7fbe29847b414` |
| `s21-run/probe/roots12.err` (its stderr) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s21-run/probe/roots12.smt2/` (the 12 roots' queries and index) (13 files) | 22423 | `ca4049a4c9249fa675e84577e7142e589de238d89dbd739b88554b2992459b69` (manifest) |
| `s21-run/probe/replay12.txt` (their replay on AY 13556 + Clean, 30 s) | 5836 | `0807260f84ab5944e62205d5e3b8413c679dead4b87132e2bc1e3f9f43e42b9f` |
| `s21-run/mutants/` (the mutant run (16 mutants; summary and each run's log)) (18 files) | 907712 | `773aa87c9fa58c013d08c45e72e511e9532be2e636acdc1767e68d0130a4291f` (manifest) |
| `s21-run/qual1/` (the first qualification run (the credit lane stops at a TV-2 failure)) (4 files) | 11585 | `d8fa6b8b86573c9963ac1f2d955cd59a2580d17813bcc7b383b0f28ee7fb5876` (manifest) |
| `s21-run/qual2/` (the credit lane, its control check relaxed to the theorem's verdicts) (2 files) | 1638 | `325a0033528523c229d838f35ac7a95c573ef4a928472981f141e84a6abb21dc` (manifest) |
| `s21-run/qual3/` (the run on the final owner: all three lanes pass) (4 files) | 10001 | `b91260a340cd0ddbafc73fd39f9eb2f0e055cb2a5fc9c2fcdc7ec11ded89fdb7` (manifest) |
| `s21-run/qual4/` (the final run, the region fixtures replayed too: all three lanes pass) (4 files) | 10416 | `f808094e39edcd5bebf5cbb2d5b539fb178c9c8ce351cc6e38380da0c757857e` (manifest) |
| `s21-run/logs/gate1.log` (the solver-free body suite before the golden digest was pinned) | 42005 | `725a0ce200fc159f215fc0434c67878d464d6d77b4c7addaaa35a62594c283b6` |
| `s21-run/logs/gate2.log` (the solver-free body suite on the final owner) | 41412 | `1f11a4fe4a57511d9970807be194dc7d9e400b21cb957b45be3ab9e53974a0a4` |
| `s21-run/logs/gate3.log` (the solver-free body suite on the final code) | 41535 | `1722630ccb3ec0744ffdc3a8d3c5e71606f4aadca3da7c4ac97c60cf7fac9a73` |
| `s21-run/logs/print21.log` (the fixture printer (LIR, rows, theorems, variants, controls)) | 94544 | `e515534cde530be5a75f4ebe8e1cb4aa1c016ae654a9f9eb7b4c8033bd4b9511` |
| `s21-run/logs/codegen1.body.log` (the codegen body end-to-end lane) | 447 | `cbed63a3beef8884ac52d776d64a92fb67c0197a7e72526ec241567fa794e058` |
| `s21-run/logs/codegen1.identity.log` (its replay identity (AY 13556), run with --nocapture) | 697 | `4564115434103c658fb8c72c0dfa8a7062b72ab269bb89a19c3cab56e37b82b7` |
| `s21-run/logs/codegen1.mrc.log` (the must-refuse corpus) | 494 | `51ebdfc26f282c4e40d41ca8681cc149be19bbbe2d8089514faf118996b7f133` |
| `s21-run/logs/e2e_atomics.log` (the native atomics end-to-end (the RBX probe)) | 1094 | `2f7fbd70eb04813645ee156018ea9cb132bce3d70acb46e707b4876487a36f10` |
| `s21-run/logs/lower.log` (trust-cg-lower --lib) | 159251 | `7dad25e393dd8145f6fe94f5ef1b6fc1c4eadd4dcc6fa38b6cac691093c19c4d` |
| `s21-run/logs/tippy.log` (the attempted tippy run (the 6808 package cannot resolve the workspace)) | 22500 | `950a7f81f58c97a916d647819188d550056b2820f1add4f0d6f105569b7bbb65` |
| `runs/main-c4885af.dylib` (the landing baseline bridge, main `c4885af82`) | 144660696 | `fc5b53491013b1a5ba06eb766e82d759f0228457ea2699d9a9b8f1c4591e7867` |
| `runs/census-main-c4885af/failed_roots.jsonl` (the landing baseline census) | 49759 | `3e9dab2076786e118d84334a91fe97509d9b7a6fff30bda070273c0b5681103c` |
| `runs/census-main-c4885af/stderr.log` (its body trace) | 1459754 | `3dbf66cfdffeaf8a111c54a7500c6d756af8cbedd39c8b5f79dab52f48d7f98b` |
| `runs/census-main-c4885af.out` (its summary) | 1732 | `c4eea0dc65d164261a8887ded6535bd9d4a19e18c964424a1afc55888b097aeb` |
| `runs/s21.dylib` (the slice-21 bridge, `401db9e46`) | 144687624 | `87407a8dada79825d322bb636693fbf1978d52238f602c09900c2a62c8a73893` |
| `runs/census-s21/failed_roots.jsonl` (the slice-21 census) | 37128 | `c1c5242a5e5bbd756d8cbbabc9e938b8fc78165d28595b1481fb74942f0d3b8a` |
| `runs/census-s21/stderr.log` (its body trace) | 1393474 | `c8cbb5d770e79c90ac97ea9e0400a54b7d09c56573629044fc3a134b3a8d8b7a` |
| `runs/census-s21.out` (its summary) | 1687 | `c243acb41fef090a2303018988ad6abaaf9d1d7bfa8fe749dad4784fec33ec1a` |
| `s21/compare/` (`census_compare.py` of the two rows) (4 files) | 2621 | `8683a33b13d9dd7315e598b09a00224fcc01c606a1c01293cf9c9fca7a5b447f` (manifest) |
| `s21/logs/census_chain_kept.log` (the census chain log) | 1176 | `6f834ff93da5037b907641eb65bd3b609d064efa49c4f456be54a7d44ab87302` |
