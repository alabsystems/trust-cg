# Vendored release sources

The public trust-cg snapshot does not carry Git submodule entries. Build-time
sources are flattened here at their pinned upstream revisions so a fresh source
archive and an anonymous clone contain the same auditable bytes.

| Path | Upstream revision | SHA-256 |
| --- | --- | --- |
| `drat-trim/drat-trim.c` | `2e3b2dc0ecf938addbd779d42877b6ed69d9a985` | `d834b649f437e091597f5347f259b9f681087f89ca0844d0cee250a1a1a0c2ee` |
| `microsat/microsat.c` | `26985d9b6b9aa5375d345051bd98afd63213043d` | `f7308ebdd23d6bf01bcb8f0be51a5d2915370c148ac45d4c85b84facf9731b71` |

The files are copied without source edits. trust-cg's build scripts make any
required symbol rewrites in Cargo's output directory and leave these snapshots
unchanged. Each directory contains its upstream MIT license.

Kissat is not needed to build trust-cg. Its source is fetched at the exact
revision recorded in [`THIRD_PARTY.md`](../../THIRD_PARTY.md) only when running
the relevant external benchmarks; its license is retained here.
