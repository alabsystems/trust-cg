# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, JSON, archives, root lists, outcome tables) out of it. The
payloads below were removed from the tree in the commit that adds this file.
The last commit that contains them is `872a379cbe2b` (full `872a379cbe2b46e5137a97c785629be024f8fec0`); recover one with

    git show 872a379cbe2b:reports/perf/2026-09-30-darwin-x86-64-census-slice6/<path>

The README states the numbers each one carries.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `core-x86_64-darwin-O0-proof-slice6/backend.sha256` | 98 | `8e842425d7437e07f07135cb6b891ca803a53e571d95f691e3a743b77d67d50b` |
| `core-x86_64-darwin-O0-proof-slice6/body_trace_gaps.tsv` | 84225 | `ff50b7aafc6e18177e12c747f1cfe56ba3ed2c394d3108f09ddf7bdf8b6b40c4` |
| `core-x86_64-darwin-O0-proof-slice6/failed_roots.jsonl.gz` | 78508 | `49508815a79a5156bfbe493b4f1f0b812f25ee6ffe9408f7d1251f83eb1f7fd2` |
| `core-x86_64-darwin-O0-proof-slice6/newly_failing.txt` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `core-x86_64-darwin-O0-proof-slice6/promoted.txt` | 25826 | `c84a249a7296bc31b2d665653e4a8f40718cb605005c47689e5cabb93503ab40` |
| `core-x86_64-darwin-O0-proof-slice6/provenance.json` | 1545 | `701003ba5d53f89d38f617a016011fee9da35ddc735f8deb9e81d25546b5a0b1` |
| `cross-backend/native/credited.txt` | 1624 | `0c2d8d94e2de0d54e3d132ecd855263251faf521cf7faaad6f51f51ee8136d16` |
| `cross-backend/native/credited_o1.txt` | 238 | `275cc91cf918190ba01d6a610e60feb5be6df6823179be898aae5e51b17493ca` |
| `cross-backend/s6_xback_O0.txt` | 919 | `ddd0142a0c02f876a135f0269dc9093da895db91c7194a9522c087b161391a33` |
| `cross-backend/s6_xback_O0_O1_O2_after_fix.txt` | 9001 | `0c682425d6ebcb8e501fc90bccd548d0dbfedcf6bafec4bafae0e00cdb2bbf50` |
| `cross-backend/s6_xback_O1_O2_before_fix.txt` | 9382 | `51f81559898d87047a978eecd14b51fca3de4988a8a49ae9fb8631ca4401899d` |
| `encoding/canonical.tsv` | 52509 | `484b87a6368407f54055dcba0209d2a0f5975a4b1e5c29d973db3a53d5f6e11d` |
| `encoding/case_split_and_per_path.tsv` | 140755 | `b5fd32ec640b5801c68d4f11f5b78b48e193cef0730aec2d60602e2f81cb2a0d` |
| `encoding/cone_only_first244.tsv` | 56293 | `7f29ee03a6c1827c2da3f1fc870c52c8cfe04b6971b20f83a988e1e23fbf28c4` |
| `encoding/copies_defined.tsv` | 88353 | `e92f22d12a58ad6e79a6c5bb4a463026c6f02e941268e587977590d9e3d8eec3` |
| `encoding/every_definition_first244.tsv` | 64891 | `8c5ed593445aac2c86bda7e2a75d135a25176d3a09291d0ab49255fa2902bf66` |
| `encoding/provenance_pairing_vs_id_pairing_O0.txt` | 236 | `8c5711870d204af6ab5af83fcdf0b85ad17f0104ea1afa7621bcc8f9a8adde25` |
| `fails-before/fails_before_branch.tsv` | 9317 | `7c706f223657509f9fb8560fc09018d136b0e2ae22f0e501077ca04457d9cd65` |
| `fails-before/fails_before_main_915fff712.tsv` | 10113 | `d4bcb29eea140d46da546f436bff721a79421240cf0cc78bfc7bf8092554a895` |
| `fails-before/gate_row_slice6.txt` | 883 | `d88e31c3c1755fb1a93e0828e16e1d8bf3ab0a425d86e706cbe3c1fee5775eee` |
| `fails-before/mutants.txt` | 5718 | `9c7b2b60dff63a9baf0e981a73d7d823a66b7438300253294d6bb60e6075bd51` |
| `fails-before/review_fixes_before_5c5389e2c.txt` | 3322 | `23658282f60f7c4867495f59ad2b0a0ab5a5423a86e06a9c175a739e6b88ba01` |
| `fails-before/successor_order_before_fix.txt` | 2035 | `ebb3cd2da468218638d74a61108d8294177ae0bd211756d5c0ac604b638713a5` |
