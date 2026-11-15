# Compiler JIT sealed link, same binary: sealed (default) / unsealed (`TCG_NO_SEALED_JIT_LINK=1`), lane `jit-compiler`

**Identity: PASS** — 149 entries (146 compiled, 3 refused identically): same verdicts, error texts and emitted code on both sides and in every repetition; the unsealed side runs the frame net twice per function except where listed.

Entries whose frame-net runs are not doubled on the unsealed side (sealed / unsealed): trust-cg-fixture/large_aggregate_args--invoke (8 / 8).

| origin | sealed instr | unsealed instr | sealed/unsealed | per-entry median | sealed cycles | unsealed cycles |
|---|--:|--:|--:|--:|--:|--:|
| ay-jit-matrix | 432 M | 455 M | 0.950 | 0.947 | 116 M | 124 M |
| trust-cg-fixture | 1,071 M | 1,124 M | 0.953 | 0.951 | 253 M | 264 M |
| ty-prod | 3,908 M | 4,190 M | 0.933 | 0.940 | 939 M | 1,002 M |
| ty-semantic | 120,728 M | 128,214 M | 0.942 | 0.942 | 28,676 M | 30,455 M |
| ALL | 126,140 M | 133,984 M | 0.941 | 0.943 | 29,984 M | 31,844 M |
