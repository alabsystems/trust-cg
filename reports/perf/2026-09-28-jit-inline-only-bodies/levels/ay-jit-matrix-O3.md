# compile-corpus compare

A: `cc-base` (2026-09-29T00:16:16Z)  
B: `cc-lane` (2026-09-29T00:16:16Z)

**Identity: PASS** — 15 (entry, lane) pairs: same verdicts, error texts, emitted-code digests and frame-net counters on both sides, every repetition.

## Totals (steady-state instructions retired / cycles elapsed)

| origin | lane | A instr | B instr | B/A | A cycles | B cycles | B/A |
|---|---|--:|--:|--:|--:|--:|--:|
| ALL | aot-object | 498.7 M | 498.9 M | 1.0005 | 138.8 M | 139.4 M | 1.0039 |
| ALL | jit-raw | 506.3 M | 504.8 M | 0.9971 | 139.1 M | 139.5 M | 1.0025 |
| ALL | jit-raw-checked | 472.8 M | 472.5 M | 0.9994 | 130.6 M | 131.1 M | 1.0037 |
| ay-jit-matrix | aot-object | 498.7 M | 498.9 M | 1.0005 | 138.8 M | 139.4 M | 1.0039 |
| ay-jit-matrix | jit-raw | 506.3 M | 504.8 M | 0.9971 | 139.1 M | 139.5 M | 1.0025 |
| ay-jit-matrix | jit-raw-checked | 472.8 M | 472.5 M | 0.9994 | 130.6 M | 131.1 M | 1.0037 |

## Per phase bracket (all entries)

| lane | phase | A instr | B instr | B/A |
|---|---|--:|--:|--:|
| aot-object | compile | 498.3 M | 498.6 M | 1.0005 |
| jit-raw | adapter | 34.7 M | 34.1 M | 0.9817 |
| jit-raw | link | 33.8 M | 33.4 M | 0.9903 |
| jit-raw | lir_prepare | 0.0 M | 0.2 M | 0.0000 |
| jit-raw | prepare | 435.0 M | 434.2 M | 0.9983 |
| jit-raw-checked | adapter | 33.5 M | 33.3 M | 0.9959 |
| jit-raw-checked | link | 12.6 M | 12.5 M | 0.9898 |
| jit-raw-checked | lir_prepare | 0.0 M | 0.2 M | 0.0000 |
| jit-raw-checked | prepare | 424.0 M | 423.7 M | 0.9992 |

## Per entry

| origin | entry | lane | verdict | A instr | B instr | B/A |
|---|---|---|---|--:|--:|--:|
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | aot-object | ok | 57.76 M | 57.53 M | 0.9960 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw | ok | 58.01 M | 57.45 M | 0.9904 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw-checked | ok | 53.47 M | 53.26 M | 0.9962 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | aot-object | ok | 74.67 M | 74.40 M | 0.9965 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw | ok | 75.90 M | 75.72 M | 0.9976 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw-checked | ok | 70.02 M | 70.13 M | 1.0016 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | aot-object | ok | 168.32 M | 168.87 M | 1.0032 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw | ok | 171.50 M | 171.50 M | 1.0000 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw-checked | ok | 161.03 M | 160.88 M | 0.9991 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | aot-object | ok | 152.12 M | 152.38 M | 1.0017 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw | ok | 154.13 M | 153.38 M | 0.9952 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw-checked | ok | 144.67 M | 144.50 M | 0.9988 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | aot-object | ok | 45.83 M | 45.76 M | 0.9983 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw | ok | 46.74 M | 46.74 M | 1.0001 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw-checked | ok | 43.59 M | 43.72 M | 1.0030 |
