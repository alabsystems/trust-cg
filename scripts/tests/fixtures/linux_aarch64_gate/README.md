# Linux AArch64 gate fixtures

`source-bound-alu-boundary-regressions-second/coverage_gate_tests.{stdout,stderr}.log.gz`
is the retained transcript of a complete 40-pass `coverage_gate_tests` run that
an external wrapper once misclassified as a runtime skip because of its 28
pseudo/trap inventory rows. `scripts/tests/test_linux_aarch64_gate.py` classifies
it with the maintained gate. Both files were moved byte for byte (`git mv`) from
`reports/perf/2026-09-17-source-bound-arithmetic/records/source-bound-alu-boundary-regressions-second/`,
recorded in `c611a263f`; the record's README stays under `reports/perf/`.
