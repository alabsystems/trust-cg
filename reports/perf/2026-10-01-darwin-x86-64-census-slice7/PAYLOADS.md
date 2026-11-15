# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, JSON, root lists, outcome tables, the bridge) out of it.
These payloads never entered the tree; they live on the measurement host under
`~/tcg-scratch/` (paths below are relative to it), and the README states the
numbers each one carries. The SHA-256 of each pins it.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `runs/s7.dylib` (the slice-7 bridge) | 121903524 | `1ff7bf401bb77c7d27f65c965c2a4909aab5cd631ac656eba938ba9facf53dd5` |
| `runs/census-s7/provenance.json` | 1613 | `db0a83377bb31a8ff43b3d90ac6b6f087c4ca20a805e4112e0161546da8cc673` |
| `runs/census-s7/failed_roots.jsonl` | 1714812 | `58f23ed9961ec49d16c65f6e3333ecd776af6451fd1e8fb8d0bc52e0305be087` |
| `runs/census-s7/gap_table.md` | 1841 | `8137df589055d7b6f34e5eeb172167c4d30cedf3ea4fdd3d0a467333e73c213c` |
| `runs/census-s7/refusals.jsonl` | 6261795 | `efe0a23c263e7d5911fd839c45813a220d4b3bd9fa6da2c730932aacbb7ac976` |
| `runs/census-s7/stderr.log` (the body trace) | 9470816 | `7b3e609f76f484f4dc2dd3d17b4eb3885304251d852587edb298b52f5e7cc1f5` |
| `runs/census-s7.out` | 1600 | `1538d7aff2367a6f6a3c3947d4ebf22b7fab86eda9c3a767b303ae07cfedffa3` |
| `s7native/census_s7.log` | 492 | `2166d82089461fb7288bb0b61db43a4326c53353d7c31ec47f209a703dc9f5a7` |
| `s7native/census-compare/promoted.txt` | 17553 | `349855b79bc886f598fb4902634ff904da8072c7b330f9173272b4f2f01d0ce5` |
| `s7native/census-compare/newly_failing.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `s7native/census-compare/body_trace_classes.tsv` | 6905 | `d529808227e6f2394c35e9e254b2576e2ef50f8910b7a3a0e16f77a9224d8cac` |
| `s7native/offline_probe.tsv` | 601844 | `ebb5e89f218428695895a46e130dbce81641a323e0a57c58819ab700560693e3` |
| `s7native/typehint_check.txt` | 3578 | `b989057100f35b1b1d3c41f45e287624ab92c3762bc1e8bcf10c6e51c19bf592` |
| `s7native/uncertified_names.txt` | 17146 | `eb94359d52c8f94224873037e661b746ff865836890ea26ca659808243db3f32` |
| `s7native/replay_uncertified.tsv` | 60132 | `bbe746dbda260e5bc3c90799fd9eb6915eb402d33a976822e15edfaeb969249c` |
| `s7native/replay_uncertified_serial.tsv` | 58482 | `d379d34538ee3eecabc10a476144e63d603a87eabdb77e0dc64292a9563c03f8` |
| `s7native/replay_words.tsv` | 33014 | `eb3faad19d9c1a42684a3b90d2b05146656cc6f9612c6998c6a5ec2bed9645ae` |
| `s7native/qualification_fresh.txt` | 5205 | `dfd51ef786d1437a458cab573473be824bf328124f4af14bb55934f7fcc18286` |
| `s7native/qualification_and_credit.txt` | 6056 | `1973adecdbe24e696b10301f8bc7554cfed606629d3ee85161b3416d396c517e` |
| `s7native/gate_row_slice7.txt` | 9383 | `ed776a4200fbfd71e9c84e457d0ea40439ed59a7d548127bbf4dd842c1a53e18` |
| `s7native/e2e_and_must_refuse.txt` | 55276 | `7feff0f6c29272391509404cf60420b294977368167166c63e0166b786ca4435` |
| `s7native/mutants.txt` | 2610 | `35dbd17b324be1cf3684295c771655e8edae161999fefa13fd9cf94521572d04` |
| `s7native/probe_trace_main336a.txt` | 4503 | `c06e6efed7787c237122a54e14c3b1aeafd70bacb987fc0fc48727fd8f69fce4` |
| `s7native/probe_trace_s7.txt` | 3230 | `b05b2963b62c617087f19d1173f8a1a86068949d60a527759d8e7bbfbb26eec2` |
| `s7native/credited_O0.txt` | 369 | `96f2141559e924ddcb47941ef09e7348dee881060ca24982f40f9753477b31d5` |
| `s7native/credited_O123.txt` | 3481 | `0688789d082a06e26b50779f705b8638915e53649af02aa06b7640d04ed3a9cd` |
| `s7native/m145_O0_O2.txt` | 1922 | `83146128c84176cbe8402b980096b90172d646dd66ccb44a7aa704c1d37d8804` |

The baseline's payloads (`runs/main-336a.dylib`, sha256
`05a601b609a128ba3cc920fb41da2b81f0413ac89513ff25de9b871bfe215234`, and
`runs/census-main-336a/`) are the
[slice-6 census row's](../2026-09-27-darwin-x86-64-census/README.md) inputs.
