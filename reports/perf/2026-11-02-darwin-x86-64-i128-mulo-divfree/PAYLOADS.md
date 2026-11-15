# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md).
A dated record keeps its Markdown narrative and its reproducer sources in
tree, and its payloads (logs, outcome tables, queries, dumps, binaries) out
of tree. These payloads were never committed. They are held on the measuring
host (the x86_64 Mac of the README) under `~/tcg-scratch`, at the paths below,
and are bound here by size and SHA-256.

- **A directory's row** gives its total bytes over its top-level files and the
  SHA-256 of its manifest. The manifest has one line `<sha256>  <name>` per
  file, sorted by name.
- **Regenerating.** `lane/payloads_mulo.py` regenerates the table.
- **The numbers.** The README states the numbers each payload carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `i128-mulo-design/README.md` (the design this lane implements) | 26144 | `47976b69035cf66c74ddfbbf26c40902fe0e2a4a497fb1eaa0799eb78f632a88` |
| `mulo-run/logs/main_f2a0_ti3_callers.txt` (main's census objects that call a 128-bit division routine (census-s23-f2a0)) | 1879 | `5bea114e638e7bebaa2222c72792f2b0fc410eb50435fb124905de8aac921db5` |
| `mulo-run/probe/x86_body_probe.rs` (the probe source (OD-215's copy plus the MULO_DIVISION_FORM toggle; never committed)) | 74170 | `9bc602c7fb5b22c759ac9cf2fea0c19f8b6aa145a58cf10e320140097b26dbc6` |
| `mulo-run/probe/x86_body_probe_p4` (the probe built from the lane at c8a802a7c) | 94680304 | `3d4031c068a22bf1bfe6dde2d383cf46843d1702776602deb6e8ac42b8454d84` |
| `mulo-run/logs/probe_build_p4.log` (its build) | 9561 | `cbf8218ff1798ca57b8e881035bffdbf95793cf05cc49af16bff6a60fd508166` |
| `mulo-run/logs/chain_probe_p4.txt` (the probe chain's log) | 637 | `e22949d24bfbb956bf97e3b95b80974d378030cea323dc8998463f7d6294b131` |
| `mulo-run/all/p4_new/cf.tsv` (the whole-core probe, division-free form) | 549105 | `9e4a2c025607737a38cb720efc0983081609dca738389f6f3cf8aad855527527` |
| `mulo-run/all/p4_new/cf.err` (its stderr (pairing records)) | 1809 | `067b56381911f5de1949a72cda7d46c615cd3c3231c56071f1691f9d1a407160` |
| `mulo-run/all/p4_new/smt2/` (its queries) (4012 files) | 8360748 | `372c7cf0a52017012efb8ee773ec55015bf705b27cd4de7ff233fa21c1b62bbf` (manifest) |
| `mulo-run/all/p4_old/cf.tsv` (the whole-core probe, division form (MULO_DIVISION_FORM=1)) | 549105 | `298784c29067b910ecbdcd3fa03136e999fd895f06218eea4021157dc1f2b6c5` |
| `mulo-run/all/p4_old/smt2/` (its queries) (4011 files) | 8358683 | `ef5c12e3fd41d6cf4739581ebf7408056a0f4fa706b0165c6d3992ece56693f7` (manifest) |
| `i128sh-m1/all/m1/cf.tsv` (main's whole-core probe (6607d0f6b with the fold)) | 549105 | `298784c29067b910ecbdcd3fa03136e999fd895f06218eea4021157dc1f2b6c5` |
| `mulo-run/logs/probe_diff_m1_p4_old.txt` (diff -r of main's queries and the division form's (empty)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `mulo-run/all/cmp_old_new_p4.txt` (the division form against the division-free one, function by function) | 1982 | `c49372bf215d980746f987a94722df7d348ca5d7d66810734585a0f0113e4c72` |
| `mulo-run/all/cmp_old_new_p4.changed.tsv` (the 11 functions whose theorem bytes change) | 5409 | `d1d162b955fc7b0e9d79781abfe8a8b9b95b413aa84d5b9293d833a11961fa4c` |
| `mulo-run/stage/names.txt` (the 11 changed functions) | 1254 | `6abc9f8b91120354b37a72efb477fdc262840da5d6f9b710d9350c60fffa6a31` |
| `mulo-run/stage/new/q/` (their units, claims, generalizations and arbiters, division-free) (263 files) | 534481 | `f59db8b929354cd1c6a50c7edd540f957fd77b539f3b21ee6c3f22ddffb9d4d2` (manifest) |
| `mulo-run/stage/old/q/` (the same in the division form (= main)) (218 files) | 391123 | `5696aca4be290fe1ef5191a71fd10f19e2a5ef5bad67f7439d949c65c90d366c` (manifest) |
| `mulo-run/replay/data/replays.jsonl` (every one-shot replay (AY 13556, Clean 5f09e36c), keyed by the bytes' sha256) | 153764 | `c33ccf7fc91bef88a00878d6c678fec07673b60bca8a49a389188f7f8a3f23a4` |
| `mulo-run/replay/chain_replay.txt` (the every-route replay chain's log) | 1233 | `1375f0ac83df41d57f8a6b845afcbfeb023f9194d11da0113b956465ceebbf98` |
| `mulo-run/replay/route_new_p4.md` (the production route, division-free) | 1605 | `63bdb5a486808f3d550a493a1b415d4a9a5be55a211019a426284720e7ab87f6` |
| `mulo-run/replay/route_old_p4.md` (the production route, division form) | 1281 | `03a95ed2a379d6ffabd33787f0a269a3c7002d13ff3877548236570ac81e4c0e` |
| `mulo-run/replay/route_cost.txt` (the AY and Clean seconds the route spent per function) | 1552 | `c8be70e97ea5c389fdd7bc05f806cfba99225f8eda026dee532ebb3b907ef5d8` |
| `mulo-run/replay/table_mulo.md` (the per-function route table) | 2587 | `dc5b5504706a6922a92eae78539a9acbd56ba392ed3f20107836915d0d702709` |
| `mulo-run/replay/route_new.md` (the first form's production route (9 of 11)) | 1710 | `afd2eb0158e7f4129fbb37244ce02389424a353c421c5a38534865bfb6cb67fb` |
| `mulo-run/replay/route_new3.md` (the second form's (10 of 11)) | 1660 | `20b6a639358ef62c7dedece5e530e560d71ada7b88f4aaf35d324e4dcb8e2d51` |
| `mulo-run/exp/exp1.out` (div_rem_1e16's claim 3 offline at 120 s (the first form)) | 178 | `ddaa82b04f01db55b6ac3590bd45aeb83b35ddaa5106dbe4a35daeae0b100e8c` |
| `mulo-run/logs/bridge_build.log` (the release bridge build from the lane) | 192 | `eebb266cb7827471e0575416c23848f755e57f878eca6ad99fdc57e5f8cdf1dc` |
| `mulo-run/mulo.dylib` (the bridge) | 145344344 | `af313e1ab27933d68f75b30dc8425b9903dba5edbf683fac4e10c57dc7e50520` |
| `mulo-run/logs/dump.out` (the fresh core dump) | 31 | `f1c59ded597af243ad3de678ba0325b8bec18072f9148ea6bb792a878eeec082` |
| `mulo-run/core-ir-mulo/` (its trust-ir modules) (88 files) | 6873536 | `c12802b43a6eb6e4a74794295c26472305bfb5df4acd071e422f8014a30c39b4` (manifest) |
| `mulo-run/logs/dump_diff_s23.txt` (its diff against core-ir-s23 (the JSON sidecars' new field only)) | 13872 | `6b0774c35af4b3daaef52d93bff6e97002a025f70264f7b89c66cd7e68467dc3` |
| `mulo-run/logs/chain_bridge.txt` (the bridge chain's log (the fresh probe equals core-ir-s23's)) | 428 | `1ce4b924d759670ee1897691993c2da61da1ac3ab79043398db376e43af708a9` |
| `mulo-run/qual_4/summary.txt` (the tool-gated lanes on the measured code (one test per process)) | 941 | `ebf98916136831330e676f9d580686d183c276a82d80934be79a6454d639e620` |
| `mulo-run/logs/sweep16.log` (the 2^32-pair sweeps at W = 16) | 490 | `1b6ae497cbabac948bcb8efbefaafc2d965eaa111086654c64cb5bbd5c0aa6a0` |
| `mulo-run/logs/e2e_mulo_nocapture.log` (the native differential (O0-O3), with the fold) | 9710 | `297ca6996171f1131bfdc2e8d39d196f93c72a629a8499db8b565fb8f09a20cc` |
| `mulo-run/logs/e2e_mulo_nofold.log` (the same with TCG_NO_X86_I128_CONST_SHIFT=1) | 9827 | `7b491c3ae199783f5dac288a17b1e628c112fd66e6e82cd2e7c5926c3e7d9b3a` |
| `mulo-run/icount/objs_fold/` (the objects of the native module, with the fold) (8 files) | 23355 | `371ee45121ebe21cee3e131e5d91f709815942d683a69f75f0735d01fead561c` (manifest) |
| `mulo-run/icount/objs_nofold/` (the same without it) (8 files) | 29805 | `b641acfc9d0380dc24f9ef6fb9f53afd3a7ed138e124c7634c32a67b43623b7c` (manifest) |
| `mulo-run/icount/counts.tsv` (their per-function instruction counts) | 4438 | `0d890a0036d77399af3f0e47d3acb2825afb0c591ab52385909fc8566dac38ba` |
| `mulo-run/icount/table.md` (the count table) | 2442 | `1606d4c73000bbcc1391c253984d723d6756403633c0f34c05a54d91dac2f3ea` |
| `mulo-run/logs/chain_gates.txt` (the gates chain's log) | 2219 | `d513c33b0698e4c7daf1c677218edbf14b0e34341aa96e2e804816bb2ac172a2` |
| `mulo-run/logs/gate_lower.log` (trust-cg-lower --lib) | 170600 | `6c86895d4b3e2488bed3233dc55b865d6cb29cc6ff32ccb3a7dac26cf23981f4` |
| `mulo-run/testbin_final` (the trust-cg-verify library test binary) | 490774000 | `a216d9b1523c21eb780750e8f3c7d4d8c29411dd85e324442dfad47f0135b8b0` |
| `mulo-run/logs/gate_suite.log` (the solver-free x86 body suite) | 52158 | `70295c882b8845b09965f7363abc13161043e3dbf6c23eeabf1bc742bff6e662` |
| `mulo-run/logs/gate_l04p10.log` (L04-P10's solver-free tests) | 1130 | `f55a59ae122f89903815e415affa6a06c6d15eb471adc8ec8aae683b3489b491` |
| `mulo-run/qual_final/summary.txt` (the tool-gated lanes, one test per process) | 941 | `8c82954e0ffe425be83bf17d304809cbac98e9a30e1654807cd88b7abac6e44b` |
| `mulo-run/qual_final/` (their logs) (10 files) | 20066 | `da16a2ef1ef4fc774fb459eafbdeb16f38021ef6090ba2519374672d16fbc497` (manifest) |
| `mulo-run/logs/gate_verify_int.log` (proof_gate_strict and coverage_gate_tests (the moved pins)) | 9808 | `d8002ce370850a6e7b5c267e2f4e3db18457907fb9812e4dee9d3cd1c76e8927` |
| `mulo-run/logs/gate_pipeline.log` (pipeline backend_expansion_nounwind_callees) | 10442 | `d887ae99828941d250fc381eb39e0e6c752a408392f75a728b1566071903b6c6` |
| `mulo-run/logs/gate_codegen.log` (the codegen targets) | 14112 | `1f548dd0ae02989117dea7d3dccad016b38c690e9ce4349deb7f8e7c0d28f6f9` |
| `mulo-run/logs/gate_codegen_nocapture.log` (the native differential and the body lane with --nocapture) | 14315 | `ca7ff13e7c3941b37272f00bc378b3d6d9eda468cf9127b274b45da19be2cbc7` |
| `mulo-run/logs/gate_fmt.log` (check_fmt.sh) | 153 | `ab347ed7a319d5df637aa47f276fe60c9093029a6c6ad4656ab481e5ee2867c8` |
| `mulo-run/logs/gate_doc.log` (check_documentation.py --check) | 87 | `367a2819b366278854f46d55efa2665fcda90bf59ecc31cdd73cba6f9438e898` |
| `mulo-run/logs/gate_matrix.log` (full_test_matrix_hosts.py --check) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `mulo-run/z3/od224_z3.json` (every lemma, control and cross-check of proofs/od224_z3.py, with its z3 CPU time) | 6234 | `faef7df6beb5770cb853def8e157a5e796e0a143dd05d2863ba4e7dcf0e29fac` |
| `mulo-run/z3/od224_z3.err` (its stderr (empty)) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `mulo-run/probe/x86_body_probe_p5` (the probe built from the merged head 07c38c1a3) | 94696808 | `a7b786f2a23fa5b1fc5b1eadb9ed4c9a4e611b9b6d6ed0b06e4c1643a56daef5` |
| `mulo-run/logs/chain_probe_p5.txt` (its chain's log (both forms as measured, byte for byte)) | 672 | `1e28794b58ae4f1f09d08e34f7be00b476e94c9d93ed1ec6c8a5a0ec336db07a` |
| `mulo-run/all/p5_new/cf.tsv` (its whole-core run, division-free) | 549105 | `9e4a2c025607737a38cb720efc0983081609dca738389f6f3cf8aad855527527` |
| `mulo-run/all/p5_old/cf.tsv` (its whole-core run, division form) | 549105 | `298784c29067b910ecbdcd3fa03136e999fd895f06218eea4021157dc1f2b6c5` |
| `runs/mulo-6828.dylib` (the census bridge, `682862195`) | 145395288 | `f4b4305bfda264106a0546e103bb8c8dd88d36adc06a513ffade0f5431936f70` |
| `runs/census-mulo-6828/failed_roots.jsonl` (the census) | 18382 | `c955ebddbeb010528ad9348b830714f1a3a5fb37856b24bffb29cbd06e7e03bd` |
| `runs/census-mulo-6828/stderr.log` (its body trace) | 1304814 | `302d4d156914245d2ea4727227eb2d4dbf88460a181d3c7cd48ee610ee8bce0a` |
| `runs/census-mulo-6828.out` (its summary) | 1727 | `6cfcac6c286b232464f1738e3f286942c7d6230e1cb29843c6a576268ba0fa29` |
| `runs/chain-mulo-6828.log` (the census chain log) | 581 | `9688698cd0ef187602c2bacba5a9204b774aceca8efa38f4c21713bf6e0a5b81` |
| `mulo-census/compare/` (`census_compare.py` against `6607d0f6b`'s census) (4 files) | 317 | `7754fd74e30ef336648576fda47d488ff8b8c6ce3bb0d731ca3f0af9eb45cc1c` (manifest) |
