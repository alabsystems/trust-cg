# Compiler JIT sealed link, same binary: sealed (default) / unsealed (`TCG_NO_SEALED_JIT_LINK=1`), lane `jit-compiler`

**Identity: PASS** — 149 entries (146 compiled, 3 refused identically): same verdicts, error texts and emitted code on both sides and in every repetition; the unsealed side runs the frame net twice per function except where listed.

Entries whose frame-net runs are not doubled on the unsealed side (sealed / unsealed): trust-cg-fixture/large_aggregate_args--invoke (8 / 8).

| origin | sealed instr | unsealed instr | sealed/unsealed | per-entry median | sealed cycles | unsealed cycles |
|---|--:|--:|--:|--:|--:|--:|
| ay-jit-matrix | 431 M | 455 M | 0.946 | 0.951 | 119 M | 147 M |
| trust-cg-fixture | 942 M | 992 M | 0.950 | 0.951 | 332 M | 287 M |
| ty-prod | 3,908 M | 4,189 M | 0.933 | 0.939 | 1,127 M | 1,129 M |
| ty-semantic | 120,083 M | 127,469 M | 0.942 | 0.943 | 35,141 M | 32,888 M |
| ALL | 125,364 M | 133,105 M | 0.942 | 0.943 | 36,719 M | 34,450 M |
