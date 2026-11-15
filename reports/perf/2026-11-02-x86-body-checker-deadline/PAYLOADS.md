# Payloads: the Clean proof check's own deadline (OD-223), 2026-11-02

Every payload of [README.md](README.md) lives out of tree under
`~/tcg-scratch/`. This table binds each one by size and SHA-256
(`ckdl/payloads.py`). A directory's row gives its total bytes and the
SHA-256 of its manifest, which has one line `<sha256>  <name>` per file,
sorted by name. A mutant's directory holds one log per control, and its
`ckdl/controls-<mutant>.log` holds the run's summary.

| payload | bytes | SHA-256 |
| --- | ---: | --- |
| `runs/census-s23final/stderr.log` (the census body trace: leading_zeros' two lines (2343, 5456)) | 1318078 | `c15615dbbdcdff64d80c4aa433bd5cedbe79fe8eddab7388c35df90d7fec19be` |
| `runs/dump-s23final/__trust_cg_private-core-542ad821d0dce3d0-cgu-0-1703-_RNvMs7_NtCs7e1ihmkzmZ8_4core3numy13leading_zeros.smt2` (the census query, SHA-256 9eb494ad…) | 10049 | `9eb494ad18054a7eb50a942f45efcd20212f0eaf00b96ae2c63abab016841a68` |
| `ckdl/A2-measure.jsonl` (the tools alone: AY, Clean under 30 s and 180 s) | 1114 | `b70313764cc0a9b0d4fc2b898f178b60e97a78ea32e503a9d6fea9fd940def3a` |
| `ckdl/A3-probe.log` (the funnel probe: three routes, TCG_SOLVE_TRACE) | 11979 | `d823475bf997dbf9875d26b2ad88b8aaba7922dac7453987fa5b987c1893061b` |
| `ckdl/A1-build.log` (the lane's test build) | 9546 | `a02ef09aa8235161d28cebf867550ad0e5c6f3e0dc6f3ee04846a900d9fed5ed` |
| `ckdl/jobA.log` (job A: build, measurement, probe, controls) | 2121 | `ea576403a4f622b6f83f3649eda7a7eecc8a6982c53991b1f7e761b69b2190dc` |
| `ckdl/none/` (the lane's 19 controls, one log each) (19 files) | 176487 | `544f60f55963d69d4cd7a986102fc37f8e128f244c84c78a79f356938abf4739` (manifest) |
| `ckdl/jobB.log` (job B: the gates) | 3264 | `60670e82666f7448956b4f32dc3123ffa79ba8c218cbd0e7765035aac6077de4` |
| `ckdl/B1-x86-suite.log` (the x86 body suite) | 51974 | `744be8524826d2c5b673708ac8210fa38a615c91340cffed0717095e3d28aee9` |
| `ckdl/qual/` (the 13 qualification lanes) (13 files) | 167755 | `ea6a723a65fe4bcab56a48996b203b08fb3b763b9fbe0360ca674123942207e3` (manifest) |
| `ckdl/B4-source_bound_negative_memo.log` (lib group) | 11588 | `269c3bedd773a69604d494fea1c2fa4e736698ad04b332b681f1485964168ed7` |
| `ckdl/B4-obligation_cert_store.log` (lib group) | 15757 | `9afc8439f5589c2784506f27e2d3159971458207fcbfb66538283939c3a8c7db` |
| `ckdl/B4-verdict_db.log` (lib group (1 overlay-build failure, also on main)) | 13293 | `9e11da3af860be8067509ed61a029814d7f1f582d4a153ed20d7d7071c570bad` |
| `ckdl/B4-function_request.log` (lib group (2 overlay-build failures, also on main)) | 13911 | `a621402ba30c262c97845a8a894eb7d3b2e1a29dc185ca09e6a751fbe63ea6e8` |
| `ckdl/B4-proof_certificate.log` (lib group) | 11140 | `41bbbb9a343ad311a557023a5c7936bd9067523e7fca00dfe0f81b55ca5cc1f7` |
| `ckdl/B4-ay_bridgesubprocess_tests.log` (lib group) | 11066 | `9c2746148ae8a40537396f0c0fa33c39d42cff21c2f48fc31dc51b06c6e5273e` |
| `ckdl/B4-subprocess.log` (lib group) | 12108 | `50ae67c2bce6bd5c28ea84620e1371cea4b60def25f2fd841dec2433bb862e95` |
| `ckdl/B4-gap_classify.log` (lib group) | 9630 | `19d6e8903d70f54e8f4da18e3884c3421857fa653a20de507bb2bc3f512a3be4` |
| `ckdl/B4-formal_gap.log` (lib group) | 9492 | `3bda90e0b8f69d3c8e23493bb5618568c5cb06d8a83f0a341377f282f46712ad` |
| `ckdl/B5-codegen.log` (trust-cg-codegen x86_source_bound_body and must_refuse_corpus) | 12651 | `975afa3bd19c86a81870bdead5ba7357daf06a43b44a408c09a2c7c77bbe642a` |
| `ckdl/B6-tippy.log` (tippy: no such command in the t011 targo) | 159 | `ac3f4f4119b25653566958f45d74c6d5b1da8e02f114496792fd73ae47598a21` |
| `ckdl/jobC.log` (job C: OD-197 memo controls, five mutants, main-sources) | 11048 | `b823ba9aef80af08584e9339a7ada82a16c640cd91eb2c02f7749864a41a05d2` |
| `ckdl/memo/` (OD-197's 17 memo controls) (17 files) | 157871 | `bb2a1956fc83da00c2e3cb3eac6fb2971d5b01571c3db79eed266da4f8ccaf55` (manifest) |
| `ckdl/check-deadline-ignored/` (mutant) (13 files) | 128359 | `02b49d1b0b147955583eddf696f0334fda2190bb7e9b1945b3e23e7396e49767` (manifest) |
| `ckdl/check-timeout-as-solver-timeout/` (mutant) (13 files) | 122774 | `a26b66ccc22ece4fad870fcfacad3775aac561b138f5fa7f2967da353128146c` (manifest) |
| `ckdl/memo-key-without-check-deadline/` (mutant) (13 files) | 122770 | `bb528e371f76c2fc0625f58bd66edbfe2c4f0cdaacdda36928aba211a07c73d2` (manifest) |
| `ckdl/memo-reads-v5/` (mutant) (13 files) | 122071 | `340938274fb06a8f3c4c37e4c99d4b429ea076f1d9838d71720b4029b9cf8e54` (manifest) |
| `ckdl/main-sources/` (the three overlay-build lib failures on main's sources) (3 files) | 34052 | `419c85a84e4d2c876cd236bbcb990a80c7d162b3ded484b6d543f23401071ae1` (manifest) |
| `ckdl/jobD.log` (job D: main-route again, two memo mutants) | 5101 | `44cf7855b92e99c2bd3de1f3f8dfcd62ba015dd8350dc8f82fd5f8571e569b6a` |
| `ckdl/main-route/` (mutant: main's route (job D's run)) (13 files) | 128039 | `5820249f74d4e254c701fb9fb810b9b4b6fdebcc89d5174f0cbed0615c4cb4ff` (manifest) |
| `ckdl/memo-records-checker-timeout-as-timeout/` (mutant) (13 files) | 123577 | `e7772058694cd2bdcfbf203399f09ed2bf3fe94f8f630cdb5fb9315aef6bc297` (manifest) |
| `ckdl/memo-judges-check-on-solver-expiries/` (mutant) (13 files) | 122688 | `c8add76774a502013fc8d9ef9ea95bc1cdf74eddc9f96b0143e277c57f2a9c97` (manifest) |
| `ckdl/measure_lz.py` (the measurement script) | 3770 | `40b54408a3492bfd88dc4297ec04b3eb00f9d7462315967e72c701d73e366d99` |
| `ckdl/mutate.py` (the mutant driver) | 4289 | `a0b3b76ab1f57e93d71f86be50d19b587b7466a3eed322e4c740c3dc0fcf00b5` |
| `ckdl/jobA.sh` (job A) | 1479 | `afc7aee94597bf95d0ca33e47672d7256140180c72cfb4a1c38dd247adb24891` |
| `ckdl/jobB.sh` (job B) | 1813 | `36dca1cf5b37d0141e17ddf926afcbe2c0a2a22eae47e8071aed3ce85c9b79a0` |
| `ckdl/jobC.sh` (job C) | 1557 | `02ec18246478b0d7437843b4658708cfbe5945fc5d4efbc09f8ceae41643fcc0` |
| `ckdl/jobD.sh` (job D) | 840 | `3b6e030f47e3525e2054000cc49dd22d1cea8e3509e8751279906f7fee3dd7be` |
| `ckdl/controls.sh` (per-process runner (jobs A, B)) | 891 | `f3b584f782cc9bf17c2773a44e0661e12282c12b6a7690fe13ab6c08db9171f2` |
| `ckdl/controls2.sh` (per-process runner (jobs C, D)) | 1006 | `57d19f3ca79f03d4647a3091ccf270bf4136afd0060ae82f1c754ebcee0deb34` |
| `ckdl/run_job.sh` (build-slot wrapper) | 527 | `ca8215c305a26c19e0430181d63f5b010da56fe034d43834f45bbcd462d5eb1a` |
| `ckdl/run_controls.sh` (mutant run wrapper) | 627 | `3f794aa74112765aca66376d7952e42dcb0976973afe6c42d47d1f5a3b8e84d6` |
| `ckdl/new_controls.txt` (the lane's control names) | 1970 | `9ede35dc38cd554f0aa10b692009cf97c415c4da10dfb31ccd10065254138fc6` |
| `ckdl/memo_od197.txt` (OD-197 control names) | 1725 | `077d669624ca6c97c813299e723b9fafc6ee803949c28340baec764b3e52e773` |
| `ckdl/qual.txt` (qualification lane names) | 1518 | `1a5e7319bf010114685e6077a034e09c82c78f76005c4e6c521029d972e24750` |
| `ckdl/mutant_controls.txt` (the mutant set) | 1436 | `5b0b216e59b5dcb0c608df978591a36838b91b33c2c07f78f9843fd0ced7f995` |
| `ckdl/payloads.py` (this table's generator) | 1169 | `4c1e3ef353d7158039c11c19351f8346338128c8afc55d0f995af980deeaa582` |
| `ckdl/jobE.log` (job E: the merged head d33c37a30) | 3893 | `a6436890404a3a21d5028c6455e37fc546b3b3aecfdf8891375819d9ba8b9148` |
| `ckdl/E0-build.log` (its build) | 10558 | `67bbb0b230d7e4a11edb0807b4bf89dddbad3c51f95a145e297a09d8a0c45e39` |
| `ckdl/E-lane/` (the lane's 19 controls on d33c37a30) (19 files) | 176487 | `53d10a7670fc96958c0cda066076299658945fdaf30cc44eaecce7c3fb7b21ec` (manifest) |
| `ckdl/E-memo/` (OD-197's 17 memo controls on d33c37a30) (17 files) | 157871 | `ab9a87c4f3eb7e69f878eac41e68ca55b793cf6a889a2c1cdd93705398afdcc3` (manifest) |
| `ckdl/E3-x86-suite.log` (the x86 body suite on d33c37a30) | 51974 | `f261851eb3e5931304d9e7c4667860572edf3cc5b712f8a1584a45ae523ae4b3` |
| `ckdl/E4-codegen.log` (the codegen targets on d33c37a30) | 11886 | `7f8dfea621fbf7da2ce6ff657fbc90b4c5c40fa56bc00c23fa8273c876740195` |
| `ckdl/jobE.sh` (job E) | 1285 | `f3922d24efb75cab3c0a726e354888efa3f13e96aab7ce06e4d1630f852b06c4` |
