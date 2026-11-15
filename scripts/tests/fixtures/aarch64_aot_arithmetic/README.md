# AArch64 arithmetic AOT export fixtures

Real trust-cg CLI exports that `scripts/tests/test_aarch64_aot_arithmetic.py`
uses as regression fixtures: the ported sidecar audit must accept them, reject
named mutations, reproduce the three corruption controls byte for byte, and the
linked-image binder must refuse patched or swapped PIEs. Every file was moved
byte for byte (`git mv`) from the qualification record named below; the test
reads exactly this set (derived with an `open` audit hook over both test
modules, plus every file under each `*-proofs/` tree, which the test rglobs).

| Fixture path | Original path | Recorded in |
| --- | --- | --- |
| `export/harness/`, `export/aot-arithmetic-native-first/`, `export/aot-arithmetic-independent-first/` | `reports/perf/2026-09-17-arithmetic-aot-export/records/` (same subpaths) | `aac298255` |
| `linked-cases/<case>/` | `reports/perf/2026-09-20-maintained-arithmetic-aot/records/gate/cases/<case>/` | `cc2d64164` (run source `c45c4d3f`) |

The records' claims and boundaries stay in their README.md files under
`reports/perf/`; the rest of those payloads was removed from the tree and is
in git history at `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
