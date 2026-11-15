# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md).
A dated record keeps its Markdown narrative and its reproducer sources in
tree. Its payloads stay out of the tree: logs, outcome tables, dumped
queries, the overlays' manifests and the bridges. They live on the
measurement host under `~/tcg-scratch/`, with paths below relative to it,
and the README states the numbers each one carries. The SHA-256 of each pins
it. A directory's SHA-256 is that of its manifest, and `census/payloads.py`
prints every row. The overlay toolchains themselves are not payloads: they
are under `~/.local/share/trust-overlays/`, and their manifests are pinned
below.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/requal-12713/overlays/x86-stage1-ay12713.overlay.json` (the root overlay's manifest) | 2163 | `c31d083b30613a136d0c416bac63a16bdcf3ef9d2b257d0ed95576306a6ef460` |
| `runs/requal-12713/overlays/x86-stage0-bridge-ay12713.overlay.json` (the bridge overlay's manifest) | 2765 | `bc48d68b9a5f24df14cc06049592ce37bda5b06205c4a1a178a5772c5f1d9423` |
| `runs/requal-12713/overlays/x86-stage0-bridge-ay12713.trustc-wrapper` (its rewritten `bin/trustc`) | 667 | `b7e45c03943f4d70c66bfcf104c99e88d65b4ebc5ec72d10cc42c244001d9299` |
| `runs/requal-12713/build_verify.log` (the first overlay build of trust-cg-verify's lib tests) | 1548 | `e71b0b31dd84fbf6b2fc2e71cc3c8ff301b57f3ca5e46533a4a063b97bd9d5b4` |
| `runs/requal-12713/measure1.log` (qualification under the old identity: every outcome printed) | 107239 | `2247eccc8a0c87248fabd94808b4fce421a077edf6408e55a40d1e9eee661107` |
| `runs/requal-12713/measure2.log` (qualification and credit tests under the new tables) | 121216 | `089c69eaaa708d8cb84e11e5e80e03b33d821b4cb0514472a54e37a519caad20` |
| `runs/requal-12713/matrix_capture.txt` (the qualification matrix capture (`TCG_X86_BODY_QUALIFICATION_MATRIX=1`)) | 1028919 | `de6494cf2f9ee0f70dd69badf3e5e2fee3f2728e8116405a43a1e68fa4f7e5b8` |
| `runs/requal-12713/matrix/` (its export, `scripts/export_x86_qualification_matrix.py`) (592 files) | 1124099 | `8b8f84aa6195a0c9c19f74605e5410fb5f33f0b9c289f19796b5a0c89f462d2b` (manifest) |
| `runs/requal-12713/body_new.tsv` (slice 1's matrix on build 12713, `replay/replay_matrix.py`) | 32198 | `0d41cb7372f453135172733cbf3f74f7ff943dd2f9a972c11f94345bcf56cc93` |
| `runs/requal-12713/qdump/` (the canonical queries the qualification replayed (`TCG_X86_BODY_QUALIFY_DUMP`)) (323 files) | 479513 | `bc830ab0442df7056e1ee3630f04250c197f2aa3fa2b26cc624dc987c2c97702` (manifest) |
| `runs/requal-12713/inv/changed_replay.tsv` (the changed fixtures offline, both AYs (`replay/investigate*.sh`)) | 10748 | `570f5e2b287547597fec1d7a11156e9140d9560d69e3c0b12c087afc01242ddc` |
| `runs/requal-12713/inv/mulcommuted_new.tsv` (`Mul/commuted` offline, 300 s) | 160 | `576f2efe50bfbd93a98bd42ccc46392f902a2b9a0eba4f16d55fda48ae10a36f` |
| `runs/requal-12713/inv/pairjoin_merged.tsv` (`PairJoin` merged offline) | 682 | `fecbb0deae870981774aa5d8ad5c3e76a2de3620edf47a4a263d531bb5b29359` |
| `runs/requal-12713/inv/pairjoin_clean_time.txt` (its AY and Clean times) | 279 | `b4e5ddb1f6785e7fbdcf79a5fbe81e1bf861a094930b838e333ec6cfe983c3e2` |
| `runs/requal-12713/inv/subu128_bisect.tsv` (`SubU128` on builds 10530, 12515, 12519, 12713) | 786 | `3c53a8973de0b99c22920bb98c5502c77046bfb2020832c67a010ce622a8e4a1` |
| `runs/requal-12713/inv/sub_new.err` (`SubU128` `--stats-full`, build 12713) | 3051 | `cf6f9d4ec26335f9bb89a17efc24a3c66e9115b26ee1fd2b498cadb32c96231c` |
| `runs/requal-12713/inv/sub_old.err` (the same, build 10530) | 2870 | `eb3607b6899c661dd02032fec15dc1fbb3704d1c1024f6d70840fb021c38ee6a` |
| `runs/requal-12713/inv/mul32_routes.tsv` (the bridge's `mul32` query on both routes, both AYs) | 748 | `bdb64d0cf48f7b0a5d1c7bebaf298a8865db40a56f67624142ee1e44e80d5405` |
| `runs/requal-12713/smoke-new/stderr.log` (`replay/smoke.sh` through the first overlay bridge) | 5435 | `e02fb1fefc10c7288bcadd5cfbdff8ab31b7559739c637502233128a54dccfaa` |
| `runs/requal-12713/smoke-new/dump/` (its dumped queries) (4 files) | 4142 | `1a637e7b2980561074e906c6040b261337ac1ffe724506107314263ff00c06c0` (manifest) |
| `runs/requal-12713/prod_s11_sample_new.tsv` (the live replay protocol on 40 of the slice-11 census's 381 uncertified texts) | 12855 | `05f9ef99195bc91558a0918c6e2ad20adf0993e662ff754d72fe22a7485cd3d5` |
| `runs/requal-12713/refut_new.tsv` (every counterexample of `measure2`) | 46687 | `3dd15f3aab8166bfd74f4b6c1b042231aabacc2b1f590522f700ee3d89b0e18e` |
| `runs/requal-12713/cex_check.tsv` (their z3 checks, `replay/check_all_cex.py`) | 5724 | `d7c3fea5eacbc2d9694a0515510d7fedbca2f2911d53f8a8d58b74bb2aa441d8` |
| `runs/requal-12713/bridge_build2.log` (the census bridge's build (`build_bridge.sh`, at the requalification commit)) | 71 | `5b4adcb04d081735e01a45918e406ed29099b21a50fd402b8c12861b007f4221` |
| `runs/main-6b10.dylib` (the baseline bridge, `main` `6b108b81d` (built by the slice-13 lane)) | 130988952 | `abf52e172bf17124063fa2e5dd499cbac63c7e04ebd39805ee3b416825077e68` |
| `runs/census-main-6b10/provenance.json` | 1714 | `67147fcefd6a219e9c53a60e6f1ae3be2a5bc65b2b4a25bd67ea5586334700e0` |
| `runs/census-main-6b10/failed_roots.jsonl` (baseline failed roots) | 1161438 | `f7b27afa63f8643b60879ce2d1b635640c4998ca3dbf5f2fdceefbffbfa97f3e` |
| `runs/census-main-6b10/stderr.log` (baseline body trace) | 6985702 | `fd73b11f04bbe80e066cf6d958ce1e01c780e8b8f484a5c54eb09bbf64ce156d` |
| `runs/ay12713.dylib` (the overlay bridge) | 130998792 | `dc0f68b920d2ccb58cd814a6bbdb7b8f5e304d3d09499b50d1c289ca74707285` |
| `runs/census-ay12713/provenance.json` | 1712 | `8547d8e1b688366e5f1d0bd9b931739c38ecf0033ef6c57241b6e4759a452680` |
| `runs/census-ay12713/failed_roots.jsonl` (overlay-bridge failed roots) | 646702 | `ebd84fc8502f3ad2d20c455b8c20500f54d96feadc714d49b2fada56f17886f4` |
| `runs/census-ay12713/stderr.log` (overlay-bridge body trace) | 4368796 | `514c2f93fc7ffb3bfd20d2c39de7a9c60d6683efb9afc8dd2dc75df929027458` |
| `runs/census-ay12713.out` (overlay-bridge census summary) | 1710 | `3d232cdd2eb538cfdceef868eb4c0f4f5e16c3f5cb677488fde6099c254b729b` |
| `runs/dump-ay12713/` (the uncertified bodies' queries, `x86-body-dump`) (98 files) | 1164271 | `ae56b4be521fe003f603f2aa22b5b154264d0d0f3e73f579b866c3e80423f39a` (manifest) |
| `runs/requal-12713/census.log` (`census/census_ay12713.sh` log) | 600 | `e72384ea3e2041b63e910eac6737a96cf8c605531e20795cc33135988f771809` |
| `runs/requal-12713/census_host.log` (free disk, load and reclaimable pages each minute of the census) | 7924 | `2d4e69cd83f59753cc994e41dd5b8fc774f14d5b2d65d4d705d979cb0de1dbb6` |
| `runs/requal-12713/census_discarded_diskfull.log` (the discarded first run's log (disk full 10:45-11:05)) | 380 | `e3c8c74cb8d476f047270e36736b74a8e614fdc158c644cc9cb7eef17204b6bf` |
| `runs/requal-12713/negmemo_discarded/` (the negative-memo entries that run wrote, moved out of the store) (36 files) | 8379 | `4d23ae972f43265605f2ff09d95198e1f262707bd9f9e8c80c260b8704028132` (manifest) |
| `runs/requal-12713/compare/` (`census/census_compare.py` output) (4 files) | 175252 | `102a5cf2d3a010ee3376ad622401a4abfaa95cda0680317b72a31f64cb8a87b7` (manifest) |
| `runs/requal-12713/newly/` (the three newly failing bodies' queries and both AYs' routes on them (`routes.tsv`)) (4 files) | 9122 | `cb275ff3a28fb7ed4bb3fdd60c48cf08be5e8ff6643cfcec89bf739f87962885` (manifest) |
| `runs/requal-12713/prod_census98_new.tsv` (the live replay protocol, offline, on the 76 uncertified texts of the census) | 15704 | `080eb2d3aa74f1e7ba3884c3e81de70b35e8bd33bc4b0a7688c917dff2a4ddc1` |
| `runs/requal-12713/oneshot_resident_deadline.tsv` (the one-shot route on the 34 of them whose resident route ran out) | 6630 | `28e3e6a211c263b5f1106864cf86d5d02f36e2c6d449aa3e270259005b05e561` |
| `runs/requal-12713/classes_base.txt` (`root_classes.py`, baseline) | 2869 | `beec25666b4c3069a54af2bcf8951c6dacf6f68a85a57011202e0495be22cbef` |
| `runs/requal-12713/classes_new.txt` (`root_classes.py`, overlay bridge) | 2869 | `3693ae4727811058d88d1de728eb9e7f7d70f525553a2623ab36eb1ba39e5ead` |
| `runs/requal-12713/gates_full_combined.log` (`~/tcg-scratch/gates_full_stage1.sh` on the overlay (its filtered output)) | 1821 | `f2ba5c73ad4e28470153b9fb564109f1b8c38b02cf96d65a094a6e6e7b226284` |
| `runs/requal-12713/negmemo_overlay.log` (the negative-memo controls on the overlay build, before the fixture record) | 21581 | `9aa1ae101b1ef72d5a34e9134bdd8baac2f091f3018c3298a7d309d715ccc81d` |
| `runs/requal-12713/gate_verify1.log` (the verify step of `gates_stage1.sh`, complete output, after the fixture record) | 29975 | `29eb6ab4040dea221120c46e88da453ab47eb8a3758966d49deb06e87efb8a87` |
| `runs/requal-12713/e2e.log` (the codegen end-to-end body test with output) | 2970 | `36e76d545b22271ee0dac3dfbb087db880476fa3328589c23b18016f7f00d0dc` |
| `runs/requal-12713/gates_alltargets.log` (`build --workspace --lib --tests --keep-going` of every test target) | 7499 | `1715773bd200c7d4aed6a971fc04b7633e99d7801298d290e50b07f967d22020` |
| `runs/requal-12713/tippy.log` (`scripts/check_tippy.sh`) | 62547 | `7fea6238a78bde66ea05ba7dd141fb1a56a5712b9d76a4c4181d923de4ea15ec` |
