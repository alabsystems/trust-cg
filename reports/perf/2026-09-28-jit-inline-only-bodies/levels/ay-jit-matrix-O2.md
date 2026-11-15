# compile-corpus compare

A: `cc-base` (2026-09-29T00:16:15Z)  
B: `cc-lane` (2026-09-29T00:16:16Z)

**Identity: PASS** — 15 (entry, lane) pairs: same verdicts, error texts, emitted-code digests and frame-net counters on both sides, every repetition.

## Totals (steady-state instructions retired / cycles elapsed)

| origin | lane | A instr | B instr | B/A | A cycles | B cycles | B/A |
|---|---|--:|--:|--:|--:|--:|--:|
| ALL | aot-object | 409.8 M | 409.9 M | 1.0002 | 115.2 M | 116.9 M | 1.0145 |
| ALL | jit-raw | 426.7 M | 426.3 M | 0.9992 | 117.0 M | 123.6 M | 1.0572 |
| ALL | jit-raw-checked | 394.3 M | 394.5 M | 1.0004 | 108.1 M | 110.4 M | 1.0211 |
| ay-jit-matrix | aot-object | 409.8 M | 409.9 M | 1.0002 | 115.2 M | 116.9 M | 1.0145 |
| ay-jit-matrix | jit-raw | 426.7 M | 426.3 M | 0.9992 | 117.0 M | 123.6 M | 1.0572 |
| ay-jit-matrix | jit-raw-checked | 394.3 M | 394.5 M | 1.0004 | 108.1 M | 110.4 M | 1.0211 |

## Per phase bracket (all entries)

| lane | phase | A instr | B instr | B/A |
|---|---|--:|--:|--:|
| aot-object | compile | 409.4 M | 409.5 M | 1.0003 |
| jit-raw | adapter | 34.8 M | 34.2 M | 0.9820 |
| jit-raw | link | 38.4 M | 38.1 M | 0.9928 |
| jit-raw | lir_prepare | 0.0 M | 0.2 M | 0.0000 |
| jit-raw | prepare | 350.6 M | 350.9 M | 1.0010 |
| jit-raw-checked | adapter | 33.9 M | 33.6 M | 0.9910 |
| jit-raw-checked | link | 14.6 M | 14.6 M | 1.0016 |
| jit-raw-checked | lir_prepare | 0.0 M | 0.2 M | 0.0000 |
| jit-raw-checked | prepare | 343.1 M | 343.2 M | 1.0005 |

## Per entry

| origin | entry | lane | verdict | A instr | B instr | B/A |
|---|---|---|---|--:|--:|--:|
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | aot-object | ok | 48.24 M | 48.10 M | 0.9972 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw | ok | 47.83 M | 47.93 M | 1.0020 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw-checked | ok | 43.62 M | 44.25 M | 1.0144 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | aot-object | ok | 59.34 M | 59.64 M | 1.0051 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw | ok | 60.96 M | 60.84 M | 0.9980 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw-checked | ok | 55.73 M | 55.46 M | 0.9953 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | aot-object | ok | 138.10 M | 138.15 M | 1.0003 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw | ok | 147.19 M | 146.63 M | 0.9962 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw-checked | ok | 136.69 M | 136.65 M | 0.9997 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | aot-object | ok | 126.78 M | 126.77 M | 0.9999 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw | ok | 132.40 M | 132.67 M | 1.0020 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw-checked | ok | 122.95 M | 122.74 M | 0.9983 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | aot-object | ok | 37.35 M | 37.21 M | 0.9962 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw | ok | 38.28 M | 38.26 M | 0.9995 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw-checked | ok | 35.31 M | 35.35 M | 1.0013 |
