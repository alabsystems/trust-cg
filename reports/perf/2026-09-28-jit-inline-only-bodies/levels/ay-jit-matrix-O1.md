# compile-corpus compare

A: `cc-base` (2026-09-29T00:16:14Z)  
B: `cc-lane` (2026-09-29T00:16:15Z)

**Identity: PASS** — 15 (entry, lane) pairs: same verdicts, error texts, emitted-code digests and frame-net counters on both sides, every repetition.

## Totals (steady-state instructions retired / cycles elapsed)

| origin | lane | A instr | B instr | B/A | A cycles | B cycles | B/A |
|---|---|--:|--:|--:|--:|--:|--:|
| ALL | aot-object | 340.1 M | 339.9 M | 0.9994 | 93.1 M | 91.6 M | 0.9837 |
| ALL | jit-raw | 399.8 M | 400.0 M | 1.0005 | 102.7 M | 101.5 M | 0.9877 |
| ALL | jit-raw-checked | 361.2 M | 361.8 M | 1.0016 | 93.4 M | 92.4 M | 0.9893 |
| ay-jit-matrix | aot-object | 340.1 M | 339.9 M | 0.9994 | 93.1 M | 91.6 M | 0.9837 |
| ay-jit-matrix | jit-raw | 399.8 M | 400.0 M | 1.0005 | 102.7 M | 101.5 M | 0.9877 |
| ay-jit-matrix | jit-raw-checked | 361.2 M | 361.8 M | 1.0016 | 93.4 M | 92.4 M | 0.9893 |

## Per phase bracket (all entries)

| lane | phase | A instr | B instr | B/A |
|---|---|--:|--:|--:|
| aot-object | compile | 339.7 M | 339.5 M | 0.9995 |
| jit-raw | adapter | 34.5 M | 34.4 M | 0.9953 |
| jit-raw | link | 54.0 M | 53.9 M | 0.9968 |
| jit-raw | lir_prepare | 0.0 M | 0.2 M | 0.0000 |
| jit-raw | prepare | 308.3 M | 308.6 M | 1.0010 |
| jit-raw-checked | adapter | 33.8 M | 33.6 M | 0.9932 |
| jit-raw-checked | link | 22.1 M | 22.1 M | 0.9992 |
| jit-raw-checked | lir_prepare | 0.0 M | 0.2 M | 0.0000 |
| jit-raw-checked | prepare | 302.5 M | 303.0 M | 1.0019 |

## Per entry

| origin | entry | lane | verdict | A instr | B instr | B/A |
|---|---|---|---|--:|--:|--:|
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | aot-object | ok | 40.38 M | 40.22 M | 0.9960 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw | ok | 45.77 M | 45.83 M | 1.0014 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw-checked | ok | 41.11 M | 41.14 M | 1.0009 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | aot-object | ok | 48.88 M | 48.64 M | 0.9952 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw | ok | 55.99 M | 55.60 M | 0.9930 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw-checked | ok | 49.78 M | 50.19 M | 1.0083 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | aot-object | ok | 112.59 M | 112.61 M | 1.0002 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw | ok | 137.17 M | 137.52 M | 1.0026 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw-checked | ok | 124.45 M | 124.52 M | 1.0006 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | aot-object | ok | 103.80 M | 103.85 M | 1.0005 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw | ok | 122.25 M | 122.22 M | 0.9997 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw-checked | ok | 110.87 M | 110.70 M | 0.9985 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | aot-object | ok | 34.46 M | 34.57 M | 1.0034 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw | ok | 38.58 M | 38.80 M | 1.0059 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw-checked | ok | 34.97 M | 35.21 M | 1.0068 |
