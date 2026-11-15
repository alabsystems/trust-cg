# compile-corpus compare

A: `cc-base` (2026-09-29T00:16:24Z)  
B: `cc-lane` (2026-09-29T00:16:25Z)

**Identity: PASS** — 105 (entry, lane) pairs: same verdicts, error texts, emitted-code digests and frame-net counters on both sides, every repetition.

## Totals (steady-state instructions retired / cycles elapsed)

| origin | lane | A instr | B instr | B/A | A cycles | B cycles | B/A |
|---|---|--:|--:|--:|--:|--:|--:|
| ALL | aot-object | 1,109.0 M | 1,109.9 M | 1.0008 | 254.8 M | 260.8 M | 1.0233 |
| ALL | jit-raw | 1,077.3 M | 1,079.0 M | 1.0016 | 255.7 M | 261.1 M | 1.0212 |
| ALL | jit-raw-checked | 1,005.8 M | 1,008.8 M | 1.0030 | 230.3 M | 235.4 M | 1.0222 |
| trust-cg-fixture | aot-object | 1,109.0 M | 1,109.9 M | 1.0008 | 254.8 M | 260.8 M | 1.0233 |
| trust-cg-fixture | jit-raw | 1,077.3 M | 1,079.0 M | 1.0016 | 255.7 M | 261.1 M | 1.0212 |
| trust-cg-fixture | jit-raw-checked | 1,005.8 M | 1,008.8 M | 1.0030 | 230.3 M | 235.4 M | 1.0222 |

## Per phase bracket (all entries)

| lane | phase | A instr | B instr | B/A |
|---|---|--:|--:|--:|
| aot-object | compile | 1,106.2 M | 1,107.1 M | 1.0008 |
| jit-raw | adapter | 51.7 M | 51.4 M | 0.9945 |
| jit-raw | link | 109.9 M | 109.6 M | 0.9967 |
| jit-raw | lir_prepare | 0.0 M | 2.1 M | 0.0000 |
| jit-raw | prepare | 905.3 M | 905.1 M | 0.9997 |
| jit-raw-checked | adapter | 50.8 M | 50.6 M | 0.9962 |
| jit-raw-checked | link | 54.7 M | 54.7 M | 1.0002 |
| jit-raw-checked | lir_prepare | 0.0 M | 2.0 M | 0.0000 |
| jit-raw-checked | prepare | 890.3 M | 890.8 M | 1.0006 |

## Per entry

| origin | entry | lane | verdict | A instr | B instr | B/A |
|---|---|---|---|--:|--:|--:|
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | aot-object | ok | 198.33 M | 198.42 M | 1.0004 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | jit-raw | error | 185.49 M | 185.15 M | 0.9982 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | jit-raw-checked | error | 172.46 M | 172.92 M | 1.0027 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | aot-object | ok | 28.36 M | 28.18 M | 0.9938 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw | ok | 27.83 M | 27.86 M | 1.0010 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw-checked | ok | 25.23 M | 25.52 M | 1.0114 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | aot-object | ok | 7.24 M | 7.24 M | 1.0002 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw | ok | 6.51 M | 6.58 M | 1.0095 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw-checked | ok | 6.35 M | 6.40 M | 1.0079 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | aot-object | ok | 8.21 M | 8.20 M | 0.9984 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | jit-raw | error | 7.91 M | 7.90 M | 0.9986 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | jit-raw-checked | error | 7.44 M | 7.48 M | 1.0047 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | aot-object | ok | 6.63 M | 6.64 M | 1.0014 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | jit-raw | error | 6.43 M | 6.45 M | 1.0034 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | jit-raw-checked | error | 6.03 M | 6.09 M | 1.0086 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | aot-object | ok | 14.66 M | 15.16 M | 1.0342 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw | ok | 13.97 M | 14.10 M | 1.0096 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw-checked | ok | 13.29 M | 13.40 M | 1.0083 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | aot-object | ok | 2.39 M | 2.39 M | 0.9993 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | jit-raw | error | 2.22 M | 2.29 M | 1.0331 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | jit-raw-checked | error | 2.04 M | 2.11 M | 1.0343 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | aot-object | ok | 2.08 M | 2.07 M | 0.9954 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw | ok | 2.02 M | 2.04 M | 1.0103 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw-checked | ok | 1.87 M | 1.91 M | 1.0243 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | aot-object | ok | 3.73 M | 3.72 M | 0.9981 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | jit-raw | error | 3.64 M | 3.55 M | 0.9777 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | jit-raw-checked | error | 3.33 M | 3.34 M | 1.0038 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | aot-object | ok | 4.17 M | 4.15 M | 0.9974 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw | ok | 3.95 M | 4.01 M | 1.0142 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw-checked | ok | 3.72 M | 3.77 M | 1.0120 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | aot-object | ok | 11.46 M | 11.48 M | 1.0021 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw | ok | 10.61 M | 10.76 M | 1.0136 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw-checked | ok | 10.09 M | 10.26 M | 1.0171 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | aot-object | ok | 23.13 M | 23.36 M | 1.0097 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | jit-raw | error | 23.25 M | 23.32 M | 1.0029 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | jit-raw-checked | error | 21.64 M | 21.51 M | 0.9937 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | aot-object | ok | 28.84 M | 29.08 M | 1.0084 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | jit-raw | error | 28.50 M | 28.57 M | 1.0023 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | jit-raw-checked | error | 26.01 M | 26.39 M | 1.0147 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | aot-object | ok | 9.74 M | 9.74 M | 1.0004 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw | ok | 8.76 M | 8.86 M | 1.0112 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw-checked | ok | 8.16 M | 8.25 M | 1.0107 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | aot-object | ok | 9.63 M | 9.63 M | 1.0002 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw | ok | 9.17 M | 9.27 M | 1.0115 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw-checked | ok | 8.55 M | 8.65 M | 1.0114 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | aot-object | ok | 10.09 M | 10.08 M | 0.9991 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw | ok | 9.08 M | 9.18 M | 1.0114 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw-checked | ok | 8.45 M | 8.55 M | 1.0121 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | aot-object | ok | 9.60 M | 9.59 M | 0.9998 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw | ok | 8.65 M | 8.75 M | 1.0112 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw-checked | ok | 8.10 M | 8.19 M | 1.0114 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | aot-object | ok | 9.42 M | 9.41 M | 0.9997 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw | ok | 8.41 M | 8.51 M | 1.0127 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw-checked | ok | 7.87 M | 7.97 M | 1.0132 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | aot-object | ok | 7.12 M | 7.11 M | 0.9985 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw | ok | 6.29 M | 6.38 M | 1.0140 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw-checked | ok | 5.88 M | 5.96 M | 1.0140 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | aot-object | ok | 7.62 M | 7.61 M | 0.9994 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw | ok | 6.80 M | 6.90 M | 1.0153 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw-checked | ok | 6.37 M | 6.45 M | 1.0137 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | aot-object | ok | 7.65 M | 7.66 M | 1.0012 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw | ok | 6.83 M | 6.94 M | 1.0157 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw-checked | ok | 6.40 M | 6.49 M | 1.0145 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | aot-object | ok | 16.65 M | 16.68 M | 1.0017 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw | ok | 15.29 M | 15.31 M | 1.0010 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw-checked | ok | 14.24 M | 14.29 M | 1.0031 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | aot-object | ok | 16.31 M | 16.10 M | 0.9873 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw | ok | 15.07 M | 15.13 M | 1.0041 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw-checked | ok | 14.10 M | 14.15 M | 1.0035 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | aot-object | ok | 11.40 M | 11.40 M | 1.0001 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw | ok | 10.44 M | 10.53 M | 1.0080 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw-checked | ok | 9.74 M | 9.84 M | 1.0104 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | aot-object | ok | 10.31 M | 10.32 M | 1.0004 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw | ok | 9.36 M | 9.45 M | 1.0096 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw-checked | ok | 8.70 M | 8.79 M | 1.0106 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | aot-object | ok | 8.42 M | 8.42 M | 1.0003 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw | ok | 7.64 M | 7.73 M | 1.0121 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw-checked | ok | 7.12 M | 7.22 M | 1.0131 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | aot-object | ok | 6.64 M | 6.64 M | 0.9994 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw | ok | 5.84 M | 5.98 M | 1.0237 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw-checked | ok | 5.55 M | 5.67 M | 1.0210 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | aot-object | ok | 8.90 M | 8.89 M | 0.9994 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw | ok | 7.64 M | 7.73 M | 1.0122 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw-checked | ok | 7.16 M | 7.25 M | 1.0131 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | aot-object | ok | 130.96 M | 131.20 M | 1.0018 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw | ok | 133.51 M | 133.07 M | 0.9968 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw-checked | ok | 123.20 M | 123.86 M | 1.0054 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | aot-object | ok | 163.43 M | 163.58 M | 1.0009 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw | ok | 163.57 M | 163.89 M | 1.0019 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw-checked | ok | 150.19 M | 149.96 M | 0.9984 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | aot-object | ok | 39.16 M | 39.23 M | 1.0016 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | jit-raw | error | 34.68 M | 34.72 M | 1.0012 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | jit-raw-checked | error | 33.17 M | 33.51 M | 1.0101 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | aot-object | error | 0.84 M | 0.87 M | 1.0375 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | jit-raw | error | 0.85 M | 0.84 M | 0.9909 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | jit-raw-checked | error | 0.80 M | 0.79 M | 0.9886 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | aot-object | ok | 269.27 M | 268.98 M | 0.9989 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw | ok | 270.85 M | 270.87 M | 1.0001 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw-checked | ok | 257.05 M | 256.26 M | 0.9970 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | aot-object | ok | 15.08 M | 15.06 M | 0.9990 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw | ok | 14.73 M | 14.76 M | 1.0014 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw-checked | ok | 13.97 M | 14.00 M | 1.0022 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | aot-object | error | 1.55 M | 1.55 M | 0.9944 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | jit-raw | error | 1.51 M | 1.62 M | 1.0714 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | jit-raw-checked | error | 1.50 M | 1.56 M | 1.0402 |
