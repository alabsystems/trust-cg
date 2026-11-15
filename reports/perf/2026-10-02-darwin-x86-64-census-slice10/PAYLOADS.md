# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree,
and its payloads (logs, root lists, outcome tables, dumped queries, the
bridges) out of it. These payloads never entered the tree; they live on the
measurement host under `~/tcg-scratch/` (paths below are relative to it),
and the README states the numbers each one carries. The SHA-256 of each pins
it; a directory's is the SHA-256 of its manifest (`census/payloads.py`
prints every row). The baseline bridge's and failed-root file's hashes are
the ones `main`'s census record
([`ac0481810` section](../2026-09-27-darwin-x86-64-census/README.md)) states.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/main-ac04.dylib` (the baseline bridge, `main` `ac0481810`) | 126852084 | `727e6e3baeb72a6852f5e9115d58a21d25a246e4485d0e3f262c31e38c35edab` |
| `runs/census-main-ac04/provenance.json` | 1713 | `7a8aebd09d1fee86916317e60fec802b21496811b9be841258c9decd85337db0` |
| `runs/census-main-ac04/failed_roots.jsonl` (baseline failed roots) | 1358728 | `6324132b6451dbeb0e811f90f2ed65d291c0e3c180a2ab7aef57d4600a443657` |
| `runs/census-main-ac04/stderr.log` (baseline body trace) | 7996008 | `4514ae17b09261e89d38a86b8d91e05ca4379c725070b9616c9975ae1dd99045` |
| `runs/census-main-ac04.out` (baseline census summary) | 1707 | `a6d1a5a8f7fcc3b5fc8b368d4a55aafc5652817d1c063985a07172bf2b85f43d` |
| `runs/s10.dylib` (the slice-10 bridge, `99c2ca5cf`) | 126899220 | `a9d570c24ce3b2e5c5aaf41b56f730f8194ce71f41f35f0172a98f856e761213` |
| `runs/census-s10/provenance.json` | 1696 | `53f5cf19b0f9453bf04b466d79cc92f6ea7aa2d9ac6eed3b2da7fa2bf7bb8f39` |
| `runs/census-s10/failed_roots.jsonl` (slice-10 failed roots) | 1271926 | `24da7ef3806a8258b09fe3b63f1ea9e23041f4783ca6b43b71cdeca7c922140f` |
| `runs/census-s10/gap_table.md` | 1843 | `58dc56ab8e43d3db9794826c1b6e6feaeb857685a6f6a379789f9419c2ab475f` |
| `runs/census-s10/refusals.jsonl` | 4684239 | `8a0c4c15021c7790d49c0ca87ed6993911539641d1c819ea316e468dfb45f400` |
| `runs/census-s10/stderr.log` (slice-10 body trace) | 7498141 | `6c6a82786d693781b04aac2fef4f090a07ec41a0715c2e244c3169c00f7981e2` |
| `runs/census-s10.out` (slice-10 census summary) | 1678 | `fe705e61aa364df0544a73b66a7b6e3ad3d481ddbfb7d13fdac8f697a64874ff` |
| `runs/dump-s10/` (the uncertified bodies' queries, `x86-body-dump`) (551 files) | 3999284 | `99b5964b8573caa046812957b3709e6111894fb9d54adc9401b76c2f9f1fca69` (manifest) |
| `s10/logs/census_s10.log` (`census/census_s10.sh` log) | 551 | `683186a4dd3beea99c3ba411c54b670958d3be10e0775cdb8b81dc1fcdb64013` |
| `s10/payloads/main_roots.tsv` (baseline roots by first refusal, `census/classes.py`) | 343194 | `3c14e4aa56a6dda137d468681d8d6c642875e63d83c60d491550c08f2afb1b7a` |
| `s10/payloads/s10_roots.tsv` (slice-10 roots by first refusal) | 287827 | `815ee1b7341439e497cc5f04550f99c157359cebaf0dd3eb2ab5c3ab5888a5c6` |
| `s10/payloads/compare.txt` (`census/census_compare.py` output) | 2010 | `b054ecf05d2514dfd2e80804889f009dfabdb6fcc0355c7fbe7228048269c0e5` |
| `s10/payloads/promoted.txt` | 5703 | `634ac2ea27c8585852f813d4ed211e20b01b49e5216d0fd3f02dbea56d86d76d` |
| `s10/payloads/newly_failing.txt` | 1 | `01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b` |
| `s10/payloads/slice10_transitions.tsv` (the 164 class functions) | 24827 | `f236a4f019bf0da6599c5ee08cc7800207f31118c45a08125f3037e6facb61e0` |
| `s10/uncert_q/` (the 83 uncertified queries, replayed offline) (83 files) | 716294 | `9e36a3bc9776093e5ba5e2aff8e36b3e224ea7c160e6bf3fb80e9cfd5235570f` (manifest) |
| `s10/payloads/uncert_replay.tsv` (their offline AY outcomes) | 35356 | `a6e66fab1feeffc032b0b2f40d23b8d18a84546499d51fb8388b7254870ddbd6` |
| `s10/variants4/` (the respelled unsigned add/sub queries, `census/variants4.py`) (42 files) | 383306 | `f0f2808db36aaed29ca86382575555b7202e41a5fae2330839a588d268c3d035` (manifest) |
| `s10/variants4.tsv` (their AY outcomes) | 18239 | `f8af5c0243226d2b3513b70d02d6a581479a874c0966165aacca7b8c190deaaa` |
| `s10/payloads/spellings.tsv` (the fixture spelling experiments, `census/variants*.py`) | 22416 | `e99468508d2e83aa7fa2843b7be5443020a094445126d946895fab751cceb0d3` |
| `s10/payloads/qualification_first.log` (qualification with the first spellings) | 14170 | `088e6830671e7e24425924a0735293aae9696ef2e3b84cc0a7d71e5b48e3abee` |
| `s10/payloads/qualification_first_spellings_and_gate.log` | 19512 | `e28a45f5432b66039a958bebf65fea42b3218ed1acb1eb497ae0ea13fa95b346` |
| `s10/payloads/qualification.log` (`fails-before/qualify.sh`, the chosen spellings) | 13123 | `4949522fac52057c255b25ea4f77d241572ac69f6d583fc02cc690896d0b077b` |
| `s10/payloads/credit.log` (`verifier_credits_every_bound_slice_ten_row_with_the_replayed_body_theorem`) | 2266 | `4d27941cbca360ec6a485e2bd8f95bf8790c748e92905490dcfbb0a95d05a0eb` |
| `s10/payloads/solver_free_body_suite.log` (the solver-free body suite (148 tests)) | 57808 | `57bc95e79f0533432a37c4070773d2aa286df7da4dde65c87db3d62a5c7d0650` |
| `s10/payloads/mutants.txt` (`fails-before/run_mutants.sh` summary) | 5651 | `5f83d3f33c3a885a819b34a2b215196343fd42b971f22d19db6b58076dde9cf6` |
| `s10/payloads/gate_row.log` (`fails-before/gate_row.sh`, the committed sampler) | 9939 | `9c6098e62d9ec4a4b63a438eb0fc4bad819b989e3318ecc667916f96c6ab0964` |
| `s10/payloads/needle_old_sampler.log` (the needle refutation under the sampler of `99c2ca5cf`) | 3170 | `2d9ac593b67ccce33d2254a320d4e084d325ba2c5fe37b281e3dc9a2412a5775` |
| `s10/payloads/robustness_no_replay.log` (robustness probe, sampler only) | 281113 | `87f73ed382fd423bdd4174ba95e488f393dc85893bf74ccbb4b70c450f96af2b` |
| `s10/payloads/robustness_replay.log` (robustness probe with AY replay) | 286571 | `13caae5a6593b6ca0f18ebf5c930928d08db3881e55234cf0e6c1ea237e99273` |
| `s10/logs/gates_stage1_merged.log` (`~/tcg-scratch/gates_stage1.sh` on the merged tree) | 437 | `e97aa3ef8364b105ea754ce261f19a6ab43431d7f527704db53d9a0672b0bd22` |
| `s10/payloads/qualification_merged.log` (`fails-before/qualify.sh` on the merged tree) | 11340 | `55d35b913f30b74f96c1be1574b1186fe9f7405de52c7540ee1f6e92cb4bf1e1` |
| `s10/logs/gates_full_rest.log` (codegen library and CLI must-refuse corpus on the merged tree) | 617 | `57a29ef1de0f12e6660c38107779173156e78f08a8162a30ed9451ddd8cbc7c5` |
| `s10/payloads/codegen_lib_rerun.log` (the codegen library rerun, full log) | 362243 | `7106718256ee9799bd683cc9199d342ac57a2833c1b5a081cdd7537fc7d1d749` |
| `s10/payloads/jit_envelope_alone.log` (the JIT envelope test alone) | 2110 | `f788f26772d3f1517829a33b4161ee1ab3807d8afabbad73fbe32ffb0567c799` |
| `s10/logs/tippy.log` (`scripts/check_tippy.sh` with the managed `targo`) | 50070 | `98c41301fc179d499281276c3d3554a4d845e2aa022284e4a51293debba24340` |
