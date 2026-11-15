# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, JSON, archives, root lists) out of it. The payloads below
were removed from the tree in the commit that adds this file. The last commit
that contains them is `189f527ca862` (full `189f527ca862cc0ef078e7c2158769a84230bd16`); recover one with

    git show 189f527ca862:reports/perf/2026-09-27-darwin-x86-64-census/<path>

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `core-x86_64-darwin-O0-lowering-31ceceb19/backend.sha256` | 98 | `973083c052ce6798b940e493d09ec12195d390a263224317a1487c7df86395e3` |
| `core-x86_64-darwin-O0-lowering-31ceceb19/provenance.json` | 1519 | `b2f2f09498d7d37fd2937bfeca1342b85ce93c5c6c4501dc048721357a46ca42` |
| `core-x86_64-darwin-O0-lowering-35c463d81/backend.sha256` | 98 | `ee6b9fe5218f78179c6e276e1c95a30abdc96c13518499546ad992789906ddfb` |
| `core-x86_64-darwin-O0-lowering-35c463d81/provenance.json` | 1517 | `03acf765ca771fd8420ee6e415fe2f61288c201c4c83b453835723cef37a72bc` |
| `core-x86_64-darwin-O0-proof-31ceceb19/backend.sha256` | 98 | `973083c052ce6798b940e493d09ec12195d390a263224317a1487c7df86395e3` |
| `core-x86_64-darwin-O0-proof-31ceceb19/provenance.json` | 1488 | `8570df5e4951e3d8f8f79ffd82283515af5771c4c69ff8ad125b2f8456e344a2` |
| `core-x86_64-darwin-O0-proof-73e5a69f5/backend.sha256` | 133 | `ed6f4f810a6d5aa833f69ab76109095ed9de2452f0019113f4490dbfecdd3206` |
| `core-x86_64-darwin-O0-proof-73e5a69f5/failed_roots.jsonl.gz` | 87857 | `5b77a9844fc442595788693556296b54255437f38254bede8d07e04d2f3f623d` |
| `core-x86_64-darwin-O0-proof-73e5a69f5/provenance.json` | 1559 | `b1dd954f65464a5002bf23490981387d24880550b374c31970cf2d79fc9e617d` |
| `core-x86_64-darwin-O0-proof-db6c150ee/backend.sha256` | 133 | `a62a4e87863f90a45c8c606a49bf220398f219a645a13f29ac263108c4913cb7` |
| `core-x86_64-darwin-O0-proof-db6c150ee/failed_roots.jsonl.gz` | 104592 | `d934eae701d11092a83640a7ef75136fe70307e0269ac1e906fb500ed3cb2b98` |
| `core-x86_64-darwin-O0-proof-db6c150ee/provenance.json` | 1558 | `f716fd28978f94cab4216eb2d9b80dc6cb06a5bea727dfd7bc61c2d65d278eb3` |
| `core-x86_64-darwin-O0-proof-slice1-bc8624b4d/backend.sha256` | 98 | `8a071b3b0a95efa677e1260ace35110a1085a8e0f41aa2fe9c00c1c4eb86bc75` |
| `core-x86_64-darwin-O0-proof-slice1-bc8624b4d/provenance.json` | 1486 | `dc4a5d0f8f00d4c5421dc25b3d20add4e0def0d56fce19d25e4c1ff78c43018c` |
| `core-x86_64-darwin-O0-proof-slice2-d0278d3b9/backend.sha256` | 98 | `6dd1c2d78db108b765053028bb246af9605a61a0512bfe6dc0c590d6adbe0501` |
| `core-x86_64-darwin-O0-proof-slice2-d0278d3b9/provenance.json` | 1486 | `bbc6a07f3beaa1a6ce7b7681c2748ce587aa891c82246fa1a4394853c0dedb3f` |
| `core-x86_64-darwin-O0-proof-slice3-94652175d/backend.sha256` | 98 | `0a54f4cac0e98ad31437fa7e6db3750c26b0f47253f6c166cf896ab2c1794452` |
| `core-x86_64-darwin-O0-proof-slice3-94652175d/provenance.json` | 1488 | `b7cd9abccd106d97904dbbd2237dee17324ded0678cf9fd71dcf90e9ce4e5cc6` |
