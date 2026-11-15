# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, objects, binaries) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256; a directory's row is its total bytes over every file
beneath it and the SHA-256 of its manifest (one line `<sha256>  <relative
path>` per file, sorted by path). `payloads.py` regenerates the table from
`~/tcg-scratch/od210c-run/payload_list.tsv`. The README states the numbers each
one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `od210c-run/logs/bridge_main-4bf54e0.log` (main's bridge build at `4bf54e061` (E0004, the missing classifier arm)) | 366 | `c905fa3bdf4041cfb83172c19fd5549af9742b1e66a602a1cf9db69dc73a1ffa` |
| `runs/main-4bf54e0-fix.dylib` (the baseline bridge (main `4bf54e061` with that arm only)) | 144842312 | `a52dc3b05e92b3ddfd05631a8ea326516dba036659d2bd8c3f7be7d039e7e28b` |
| `runs/od216-c5e2ae5e0.dylib` (this branch's bridge (`c5e2ae5e0`)) | 144852552 | `c08fd2fe69b382ae9029f88881f9f0ddcc9fbd6839dbca4332ddfde56a6536ee` |
| `od210c-run/crates_before/` (the reproducers through the baseline bridge (`run_crates.sh`)) (40 files) | 54921 | `83ea615f7cdfe30311c5f434ae99658799ecd516cb13feba9a155786a504b4f3` (manifest) |
| `od210c-run/crates_before_extra/` (the one-unit declared controls through it) (9 files) | 13695 | `fa1b642798562c474650b135408cac9595a3c268c2e9dd5900ff1cad53c724b9` (manifest) |
| `od210c-run/crates_after/` (the reproducers through this branch's bridge) (45 files) | 65796 | `7e0ddb862e559e734fa342f37f201226f904ac62cb0d7fa0c2403097a4b0b8ea` (manifest) |
| `od210c-run/crates_after_extra/` (the one-unit declared controls through it) (9 files) | 13684 | `53488456fe6ddfaf51cca61b54bd46a31c012d4dc54db882b1214aecc7b875e9` (manifest) |
| `od210c-run/census/` (census-s22's traced functions and its objects' defined symbols (`nm -U`)) (2 files) | 1305258 | `b7f50e5a4641e6069ed8a4dcf14eaf719c4b3208871eee6f5a22085cdcc973b5` (manifest) |
| `od210c-run/quick_b1/` (the new solver-free tests on the first build) (5 files) | 6501 | `cd8847dba84423d3af3d77cf1f3266541175f2c9b2c3d791ff6cf25fcf567cd3` (manifest) |
| `od210c-run/logs/verify_one_b3.out` (the vectorizer fixture's refusals at O2/O3) | 1521 | `da763b0245c0388ecb32b79d3564027c8ef8e95953cd6808646879da30833099` |
| `od210c-run/mutants/` (the mutant run (`run_od216_mutants.sh`: summary and each run's log)) (13 files) | 22459 | `4d609548e569b3d75bf3b89562ca0eeb888038070b6d569f8d741a0d3c6ab68a` (manifest) |
| `od210c-run/gates_b3/` (the gates at `c5e2ae5e0` (the qualification, codegen and opt lanes, and the 7 owner failures)) (12 files) | 109155 | `37612cbef3b91b732712c671975182d08c76e7ede742f5b16e116bbbde7dfe1b` (manifest) |
| `od210c-run/gates_final/` (the final verify gates at `fa077f93d`) (13 files) | 78232 | `8113b63e23e608dffb0a08b94535051161e1650a3d9bcf3fb7e628022c9ad7f9` (manifest) |
| `od210c-run/check/` (the compile check of the touched targets) (6 files) | 19418 | `73b73d0271be89ddfcce52acff9d9760d6cd038a7f04eb5d00cc8089838117ba` (manifest) |
| `od210c-run/lint/` (the tippy attempts (tooling refusals)) (6 files) | 131964 | `7cff83532bbc0760b637041dd975ad233ab797b30e5bc125a7860f0a92544da2` (manifest) |
| `od210c-run/logs/bridge_lib_tests.log` (the bridge's library tests) | 127033 | `c16a633a96bc4be0edb031d402d4e1b1f35075f2c362cb6736a53dfb24ecf8b8` |
