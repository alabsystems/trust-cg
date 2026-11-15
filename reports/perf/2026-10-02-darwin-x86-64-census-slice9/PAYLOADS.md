# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md).
The dated record keeps its Markdown narrative and reproducer sources in
tree. Its payloads stay out of tree: logs, root lists, outcome tables,
dumped queries and the bridges. They live on the measurement host under
`~/tcg-scratch/`, and the README states the numbers each one carries. The
SHA-256 of each pins it. A directory's digest is the SHA-256 of its sorted
`<sha256>  <relative path>` listing; `census/payloads.py` prints every row.
The baseline (main `cffb7e876`) is the slice-10 record's census, whose
failed-root file and body trace carry the same hashes there
([slice-10 payloads](../2026-10-02-darwin-x86-64-census-slice10/PAYLOADS.md)).

| Path | SHA-256 | What |
| --- | --- | --- |
| `~/tcg-scratch/runs/census-s9b/stderr.log` | `89f0aecef83f0af463f684717742857690c488db1a84eb49cb51e191068ef7e4` | final census body traces (5f06edfdd bridge) |
| `~/tcg-scratch/runs/census-s9b/failed_roots.jsonl` | `3f4dc018f961d5eeee3ed032974aae995fa297dd66646c5a8cad7e18e57e05cd` | final census failed roots (1166) |
| `~/tcg-scratch/runs/census-s9b.out` | `3f73ad4cdb7ec845ce1f58798270b6f08fdb0e0a312fea4dd35faf6161a1107f` | final census harness summary |
| `~/tcg-scratch/runs/s9b.dylib` | `31899dd2dcac67a3d7cafe3f0c5d714df211b59e84e399d2306df1f602b0fdf8` | final census bridge |
| `~/tcg-scratch/runs/dump-s9b/` (593 files, listing digest) | `19b0fd044dec431b4e20f8a15ddfc8c6551a956a2616d4e258e5cc8b3af41784` | final census uncertified-body queries |
| `~/tcg-scratch/runs/census-s9/stderr.log` | `5e101f0142c9009b7bc05136e2351055a5f2649a564b1dcc3f2c6df5a3efc9d1` | first census body traces (e9488c7fe bridge) |
| `~/tcg-scratch/runs/census-s9/failed_roots.jsonl` | `23107f5ca43686bf9f880971eaadbcbd8f7ebd1bb54896c417d6b6dcc54ac366` | first census failed roots (1187) |
| `~/tcg-scratch/runs/s9.dylib` | `a2c51e758b8af07ac8103c1e4318e803d13292939c6ef4a82ad66452e59315d5` | first census bridge |
| `~/tcg-scratch/runs/dump-s9/` (614 files, listing digest) | `42e924e7b6a937905474dcaad797008249ae0eea6acee9ce0f6158de21954b7a` | first census uncertified-body queries |
| `~/tcg-scratch/runs/census-s10/stderr.log` | `6c6a82786d693781b04aac2fef4f090a07ec41a0715c2e244c3169c00f7981e2` | baseline: main cffb7e876 (slice-10 bridge) body traces |
| `~/tcg-scratch/runs/census-s10/failed_roots.jsonl` | `24da7ef3806a8258b09fe3b63f1ea9e23041f4783ca6b43b71cdeca7c922140f` | baseline failed roots (1198) |
| `~/tcg-scratch/s9/compare-s9b/` (4 files, listing digest) | `c9f81b4eb27a85659bceb785382a8454249f31d455afe235aade259c0c2d2448` | census_compare.py output, final census |
| `~/tcg-scratch/s9/compare-s9/` (4 files, listing digest) | `24254c7b66144e3c0b7ac3b5a53c36f707038a664febb568d0a64ff43ac7c1b0` | census_compare.py output, first census |
| `~/tcg-scratch/s9/newly_bound_census.tsv` | `a76e3eef077d4e60dfea208901bbff12fd1bf062f53b07cc788ff358d35ebe1d` | newly_bound.py, first census |
| `~/tcg-scratch/s9/smt-census-new/` (62 files, listing digest) | `dbec34dd57219df119062a5478fb0045f9191a3d00a24ab7df6ef574d904de7e` | first census: the 62 uncertified newly bound queries as dumped |
| `~/tcg-scratch/s9/smt-census-new-inl/` (62 files, listing digest) | `870cb667813fa606bd65c12225600a548d35739bf1093124814878c3e31fdc7a` | the same, inline.py |
| `~/tcg-scratch/s9/smt-census-new-drop/` (62 files, listing digest) | `ee762c3237f8c46f4e0b044395efdc91d66e882ba531c76d52ba659f122b95fc` | the same, drop_identities.py |
| `~/tcg-scratch/s9/census_new_b10530.tsv` | `750f595eaaaf677ea64b232c41e6a71409e0e17ed3c67eb8918ea3f2227b25a0` | replay_dir.py outcomes, as dumped (0/62) |
| `~/tcg-scratch/s9/census_new_inl_b10530.tsv` | `2c33f5755010b72cedeef1fdef69983389abd0b67788da8c51d42afbbdc61e17` | replay outcomes, inlined (14/62) |
| `~/tcg-scratch/s9/census_new_drop_b10530.tsv` | `86f2f5d97e5f8c114e1ad8f9d92a6e97722a8886501349df065e5fc8ec19f311` | replay outcomes, identities dropped (13/62) |
| `~/tcg-scratch/runs/core-ir-s9/` (88 files, listing digest) | `393da31cd54b37baf66a555d7dc8387b14c8eb7b5c7d3e0d075933a0ace258a4` | the core trust-ir dump (main ac0481810 bridge) the probe read |
| `~/tcg-scratch/s9/cf_s9t.tsv` | `9ccd85a0ae3a3c1d123dbe2319aac825ae407857e4494d7469724e5c0220f341` | probe --cf output (shapes and verdicts) |
| `~/tcg-scratch/s9/offline_t/` (2 files, listing digest) | `3dd0f451e67e6291644ea38805bfa65301fc2a5273ed6878d7f351c25042672a` | offline_classes.py output (class tables) |
| `~/tcg-scratch/s9/smt-new/` (53 files, listing digest) | `58fa47aec900cb9dc8142283a5b8117b8b1005898315e643acaf3fb52346d0db` | offline 52 queries, every copy and definition |
| `~/tcg-scratch/s9/smt-trim/` (53 files, listing digest) | `2fe570df74d6331900e632524138d9172d4f4408fe96ea64979c2144d81ebb6a` | offline, trimmed |
| `~/tcg-scratch/s9/smt-trim-inl1/` (53 files, listing digest) | `e8e01fe5868a0aaca610bc3999457b89cda982d3b2559c332b13b56866186d7c` | offline, trimmed and inlined |
| `~/tcg-scratch/s9/smt-new-inl1/` (53 files, listing digest) | `1a4f38f175944022d59b51c4459f1489c392a80270fb3260189daf60fecf2902` | offline, untrimmed and inlined |
| `~/tcg-scratch/s9/new_b10530.tsv` | `b946b1dd740d6ed089e0eabe81e6b37b0970d4e2a699b776cb2a0de3b3698350` | offline replay, untrimmed (1/52) |
| `~/tcg-scratch/s9/trim_b10530.tsv` | `62031d314abcd4765e60e699aaf295f1f7d33d3a485595e48d648161025f5858` | offline replay, trimmed (6/52) |
| `~/tcg-scratch/s9/trim_inl1_b10530.tsv` | `c46f072749cb3d7e7952109ce2dc229fc203ddb5492f127c1b18f70b23c4cdf1` | offline replay, trimmed and inlined (22/52) |
| `~/tcg-scratch/s9/new_inl1_b10530.tsv` | `67d98c874012b6b783852752786613b3db4aa6d17b18306d47679d5febd7510f` | offline replay, untrimmed and inlined (17/52) |
| `~/tcg-scratch/s9/new_branch9ad05.tsv` | `ac2755754449a35dbbe61e3b8dac234447347193b3df8d484028e0b8a40fd73e` | offline replay on AY branch 9ad05eb80, untrimmed (3/52) |
| `~/tcg-scratch/s9/pad/` (7 files, listing digest) | `9c16b697b78721a5cfad1616d8975a5a814a294e20b7b3327394a41b0fdc50fa` | pad.py outputs (padding reproducer) |
| `~/tcg-scratch/s9/payloads/mutants_pre_merge.txt` | `989874cd214cc353386332497f33dd23f49033c3daac9cac33b3c8bfadfb68e6` | run_mutants.sh, pre-merge tree |
| `~/tcg-scratch/s9/payloads/mutants_merged.txt` | `ab6683e273d81f3139368c7f636fa34f54966aff2255474a0c6b7a95b2ee56e6` | run_mutants.sh, merged tree |
| `~/tcg-scratch/s9/payloads/mutants_final.txt` | `4fe5598e5e82fc4c75b26d97611130df8d22be4d14990be6f748d1a42bd81f97` | run_mutants.sh, final tree |
| `~/tcg-scratch/s9/payloads/robustness_run1.log` | `e62074bee1b94b6aff8625981b06bffe8d409198f079a57b935cd6edde69d7e5` | robustness probe, first run (random ground truth) |
| `~/tcg-scratch/s9/payloads/robustness_run3.log` | `4d34734d3074ba3c84e771378fed78d419fd31b26f25c813fb90663d3b487f60` | robustness probe, final solver-free run |
| `~/tcg-scratch/s9/payloads/qualification_final.log` | `01ac716c67e4606fbf490d4a0035d8c79f8728209a70b367afccc684b1c42b81` | slice9 qualification and spelling records |
| `~/tcg-scratch/s9/payloads/gates_merged_verify.log` | `43bbae352c07f8218cf49c48cc4a4d47a3a41fafeead9e285b7f45de47365a28` | gates, merged tree: verify body lib |
| `~/tcg-scratch/s9/payloads/gates_merged_codegen.log` | `db017956743d392024d23c083192ffe1be0927db9c9af3ef438014946ca061f1` | gates, merged tree: codegen body and must-refuse |
| `~/tcg-scratch/s9/payloads/robustness_replay.log` | `c799d808b7e39b0a06d74934dad529de1aeac2920ef87d429b6b1aadbc3f6bf3` | robustness probe with AY replay (ROB9_CAP=3, merged tree) |
| `~/tcg-scratch/s9/payloads/gates_final_verify.log` | `6169910d4d633fd1e5dc9140f71aa50acbdccbd289b3a98f9f066e3326ec73f5` | final gates: verify body lib (661334dfe) |
| `~/tcg-scratch/s9/payloads/gates_final_codegen.log` | `ad597afd78588056d1aa20d7f7e70b9aad019558c20c3c12b96af310bb359b0c` | final gates: codegen body and must-refuse (661334dfe) |
| `~/tcg-scratch/s9/payloads/memory_flake_rerun.log` | `11726665d10d15ae8403516fd4a475ae2546f06a6c047f53e661afc41743d88f` | the SlotFoldedOffset memory flake, re-run alone |
| `~/tcg-scratch/runs/census-s10.out` | `fe705e61aa364df0544a73b66a7b6e3ad3d481ddbfb7d13fdac8f697a64874ff` | baseline harness summary |
