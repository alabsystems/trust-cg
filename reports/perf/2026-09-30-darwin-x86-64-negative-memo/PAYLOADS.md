# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, JSON, archives, root lists) out of it. The payloads below
were removed from the tree in the commit that adds this file. The last commit
that contains them is `189f527ca862` (full `189f527ca862cc0ef078e7c2158769a84230bd16`); recover one with

    git show 189f527ca862:reports/perf/2026-09-30-darwin-x86-64-negative-memo/<path>

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `ab/cold-newly_failing.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ab/cold-promoted.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ab/warm-newly_failing.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ab/warm-promoted.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `core-x86_64-darwin-O0-proof-base-73e5a69f5/backend.sha256` | 65 | `0d6997788d41425fb47a21d95d207f0c632646ec802a9fec9b70d5a82552e2b0` |
| `core-x86_64-darwin-O0-proof-base-73e5a69f5/body_trace.txt.gz` | 110204 | `f9e4eb3a9ee5735b076f989134069f3a8a3ecbe1340f7324fd64241cd729a3d3` |
| `core-x86_64-darwin-O0-proof-base-73e5a69f5/failed_roots.jsonl.gz` | 87838 | `e0f8802d3c158eab7cfc4f65f57ebaf9b2dbeb491102857e23983c98cea2c8f3` |
| `core-x86_64-darwin-O0-proof-base-73e5a69f5/provenance.json` | 1559 | `b1dd954f65464a5002bf23490981387d24880550b374c31970cf2d79fc9e617d` |
| `core-x86_64-darwin-O0-proof-negmemo-cold/backend.sha256` | 65 | `e931c9fb379dfda699f96d86d3716ba45246160f78ac04a22ca4a35b155efa0a` |
| `core-x86_64-darwin-O0-proof-negmemo-cold/body_trace.txt.gz` | 113089 | `e3e9a007d711adb78148ae1c57a614ddbb8c792d2e11ebfe5cbcd1452338c0a1` |
| `core-x86_64-darwin-O0-proof-negmemo-cold/failed_roots.jsonl.gz` | 87838 | `e0f8802d3c158eab7cfc4f65f57ebaf9b2dbeb491102857e23983c98cea2c8f3` |
| `core-x86_64-darwin-O0-proof-negmemo-cold/provenance.json` | 1565 | `62c272eb3c250588da732cc593b33cd560994ea8514e05de9349f33c5b78ece3` |
| `core-x86_64-darwin-O0-proof-negmemo-warm/backend.sha256` | 65 | `e931c9fb379dfda699f96d86d3716ba45246160f78ac04a22ca4a35b155efa0a` |
| `core-x86_64-darwin-O0-proof-negmemo-warm/body_trace.txt.gz` | 113784 | `daa5cdc0962f1684c71a952d8e603f9528d29bb98d24f9cb0abbe8031910be51` |
| `core-x86_64-darwin-O0-proof-negmemo-warm/failed_roots.jsonl.gz` | 87838 | `e0f8802d3c158eab7cfc4f65f57ebaf9b2dbeb491102857e23983c98cea2c8f3` |
| `core-x86_64-darwin-O0-proof-negmemo-warm/provenance.json` | 1565 | `2620389fd297c52d8d8f3a7135e9afc03cb49ef468aa2e966d042db063878db8` |
| `probe-after-review/nm2-before-1.stderr.log` | 5011 | `36405d586a900499bd917b874211bf214a9efcb2019c409c9f2e0b78b78a28ea` |
| `probe-after-review/nm2-before-2.stderr.log` | 5011 | `792d7d5f06776a1a3ac732754add36c79cd597626c18425f567352d6bf418eaf` |
| `probe-after-review/nm2-bypass-1.stderr.log` | 5011 | `691af9f0e2604585978b4b7f2da3c62f44bef3b9fc6cb9d37d4c2ea6d4446e28` |
| `probe-after-review/nm2-cold-1.stderr.log` | 5974 | `f51721a3b9718f93d6c1c8932e32652acadba2f1788c87aa890673e3bcfbcb90` |
| `probe-after-review/nm2-cold-2.stderr.log` | 5974 | `4d88461935d1d5847d53ed962548924ad46714a8b56e93eddc1aa6f4955db610` |
| `probe-after-review/nm2-warm-1.stderr.log` | 6297 | `9f6fef5dab7d574fd1d7db31cf9034a546d0694eb1f6d58f29dfd295191f2d41` |
| `probe-after-review/nm2-warm-2.stderr.log` | 6297 | `9a51875439ef8fa5e3ca494410d633c1db411a50b631141935467dab393ce552` |
| `probe-after-review/summary.txt` | 483 | `81307f66c2045f0120309e51008951efde2e1e0eba8ca8f9a7c2b0872feae663` |
| `probe/nm-before-1.stderr.log` | 5011 | `dd61ffd260f1b9036f8e977db1548ef2fe4d6369dec18240a4e04f317041935d` |
| `probe/nm-before-2.stderr.log` | 5011 | `2ad2ac24636639429eee2d6f299986a72818ba679f0d89e7c46e70b3ed962c32` |
| `probe/nm-bypass-1.stderr.log` | 5011 | `d3504be7468471942b7b03dc6b669837c741da785b9086725323249dfe920fe0` |
| `probe/nm-cold-1.stderr.log` | 5860 | `7c978c741dbf83cb1847a626060c5afc6e7c8b2cd6beb6f936def4c6b32a2903` |
| `probe/nm-cold-2.stderr.log` | 5860 | `f7e7580170633192b91fbd1b834b95915217bea3540ee8b5bc12c8786f5635d4` |
| `probe/nm-warm-1.stderr.log` | 6145 | `125a9924314fc548380cc6307cbf37ce6e27cf55332ce5b9641763424dcc5c36` |
| `probe/nm-warm-2.stderr.log` | 6145 | `b4f4f17b815b73cd5b65cf492e38f49d94bfbe51cd79f3fe5b8a1661a5fc0237` |
| `probe/summary.txt` | 816 | `7b42360ad064a889d4c3ab87f5a5a75cafe4f504ae136d6249859b4276e1d045` |
