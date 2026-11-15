# compile-corpus compare

A: `cc-base` (2026-09-29T00:16:26Z)  
B: `cc-lane` (2026-09-29T00:16:27Z)

**Identity: PASS** — 105 (entry, lane) pairs: same verdicts, error texts, emitted-code digests and frame-net counters on both sides, every repetition.

## Totals (steady-state instructions retired / cycles elapsed)

| origin | lane | A instr | B instr | B/A | A cycles | B cycles | B/A |
|---|---|--:|--:|--:|--:|--:|--:|
| ALL | aot-object | 1,237.3 M | 1,237.6 M | 1.0002 | 285.0 M | 289.1 M | 1.0145 |
| ALL | jit-raw | 1,212.0 M | 1,214.5 M | 1.0021 | 288.1 M | 294.8 M | 1.0235 |
| ALL | jit-raw-checked | 1,137.1 M | 1,142.6 M | 1.0048 | 259.2 M | 264.6 M | 1.0207 |
| trust-cg-fixture | aot-object | 1,237.3 M | 1,237.6 M | 1.0002 | 285.0 M | 289.1 M | 1.0145 |
| trust-cg-fixture | jit-raw | 1,212.0 M | 1,214.5 M | 1.0021 | 288.1 M | 294.8 M | 1.0235 |
| trust-cg-fixture | jit-raw-checked | 1,137.1 M | 1,142.6 M | 1.0048 | 259.2 M | 264.6 M | 1.0207 |

## Per phase bracket (all entries)

| lane | phase | A instr | B instr | B/A |
|---|---|--:|--:|--:|
| aot-object | compile | 1,234.5 M | 1,234.9 M | 1.0003 |
| jit-raw | adapter | 51.5 M | 51.3 M | 0.9958 |
| jit-raw | link | 108.7 M | 108.3 M | 0.9961 |
| jit-raw | lir_prepare | 0.0 M | 2.0 M | 0.0000 |
| jit-raw | prepare | 1,041.4 M | 1,041.9 M | 1.0004 |
| jit-raw-checked | adapter | 50.6 M | 50.5 M | 0.9972 |
| jit-raw-checked | link | 54.2 M | 54.1 M | 0.9980 |
| jit-raw-checked | lir_prepare | 0.0 M | 2.0 M | 0.0000 |
| jit-raw-checked | prepare | 1,022.3 M | 1,025.2 M | 1.0029 |

## Per entry

| origin | entry | lane | verdict | A instr | B instr | B/A |
|---|---|---|---|--:|--:|--:|
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | aot-object | ok | 242.14 M | 241.95 M | 0.9992 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | jit-raw | error | 230.14 M | 229.86 M | 0.9988 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | jit-raw-checked | error | 216.74 M | 216.95 M | 1.0010 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | aot-object | ok | 31.04 M | 30.79 M | 0.9919 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw | ok | 30.87 M | 30.90 M | 1.0009 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw-checked | ok | 28.14 M | 28.31 M | 1.0061 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | aot-object | ok | 7.70 M | 7.67 M | 0.9965 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw | ok | 7.05 M | 7.03 M | 0.9977 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw-checked | ok | 6.83 M | 6.84 M | 1.0021 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | aot-object | ok | 9.63 M | 9.63 M | 1.0001 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | jit-raw | error | 9.24 M | 9.27 M | 1.0035 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | jit-raw-checked | error | 8.82 M | 8.84 M | 1.0022 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | aot-object | ok | 7.48 M | 7.48 M | 0.9998 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | jit-raw | error | 7.18 M | 7.25 M | 1.0087 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | jit-raw-checked | error | 6.87 M | 6.90 M | 1.0044 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | aot-object | ok | 14.78 M | 15.29 M | 1.0344 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw | ok | 14.17 M | 14.27 M | 1.0074 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw-checked | ok | 13.28 M | 13.57 M | 1.0213 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | aot-object | ok | 2.83 M | 2.83 M | 1.0009 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | jit-raw | error | 2.65 M | 2.71 M | 1.0219 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | jit-raw-checked | error | 2.48 M | 2.54 M | 1.0266 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | aot-object | ok | 2.17 M | 2.17 M | 1.0027 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw | ok | 2.15 M | 2.13 M | 0.9897 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw-checked | ok | 1.98 M | 2.00 M | 1.0146 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | aot-object | ok | 3.86 M | 3.87 M | 1.0002 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | jit-raw | error | 3.75 M | 3.72 M | 0.9931 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | jit-raw-checked | error | 3.50 M | 3.53 M | 1.0073 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | aot-object | ok | 4.50 M | 4.51 M | 1.0015 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw | ok | 4.30 M | 4.36 M | 1.0139 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw-checked | ok | 4.06 M | 4.12 M | 1.0162 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | aot-object | ok | 11.47 M | 11.48 M | 1.0013 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw | ok | 10.58 M | 10.75 M | 1.0161 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw-checked | ok | 10.11 M | 10.27 M | 1.0154 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | aot-object | ok | 26.68 M | 26.99 M | 1.0118 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | jit-raw | error | 26.98 M | 27.04 M | 1.0022 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | jit-raw-checked | error | 25.00 M | 25.43 M | 1.0170 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | aot-object | ok | 32.30 M | 32.19 M | 0.9964 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | jit-raw | error | 31.76 M | 31.81 M | 1.0014 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | jit-raw-checked | error | 29.08 M | 29.28 M | 1.0068 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | aot-object | ok | 12.86 M | 12.89 M | 1.0029 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw | ok | 12.28 M | 12.33 M | 1.0034 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw-checked | ok | 11.69 M | 11.74 M | 1.0041 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | aot-object | ok | 12.26 M | 12.34 M | 1.0068 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw | ok | 12.15 M | 12.21 M | 1.0049 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw-checked | ok | 11.55 M | 11.64 M | 1.0077 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | aot-object | ok | 13.25 M | 13.31 M | 1.0045 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw | ok | 12.59 M | 12.70 M | 1.0087 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw-checked | ok | 12.03 M | 12.13 M | 1.0084 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | aot-object | ok | 12.63 M | 12.68 M | 1.0040 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw | ok | 12.08 M | 12.15 M | 1.0059 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw-checked | ok | 11.50 M | 11.61 M | 1.0098 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | aot-object | ok | 12.20 M | 12.26 M | 1.0044 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw | ok | 11.51 M | 11.56 M | 1.0044 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw-checked | ok | 10.98 M | 11.10 M | 1.0105 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | aot-object | ok | 9.36 M | 9.36 M | 1.0005 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw | ok | 8.80 M | 9.00 M | 1.0232 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw-checked | ok | 8.39 M | 8.47 M | 1.0104 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | aot-object | ok | 10.00 M | 10.02 M | 1.0014 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw | ok | 9.22 M | 9.36 M | 1.0152 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw-checked | ok | 8.80 M | 8.90 M | 1.0107 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | aot-object | ok | 10.10 M | 10.09 M | 0.9992 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw | ok | 9.32 M | 9.40 M | 1.0084 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw-checked | ok | 8.89 M | 8.98 M | 1.0099 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | aot-object | ok | 21.65 M | 21.82 M | 1.0076 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw | ok | 20.86 M | 20.88 M | 1.0011 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw-checked | ok | 19.40 M | 19.54 M | 1.0068 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | aot-object | ok | 20.76 M | 20.80 M | 1.0018 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw | ok | 20.05 M | 20.12 M | 1.0032 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw-checked | ok | 18.86 M | 18.91 M | 1.0028 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | aot-object | ok | 15.23 M | 15.04 M | 0.9874 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw | ok | 14.70 M | 14.81 M | 1.0077 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw-checked | ok | 13.89 M | 14.15 M | 1.0184 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | aot-object | ok | 13.70 M | 13.56 M | 0.9899 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw | ok | 13.03 M | 13.14 M | 1.0080 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw-checked | ok | 12.42 M | 12.53 M | 1.0093 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | aot-object | ok | 11.31 M | 11.45 M | 1.0127 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw | ok | 10.71 M | 10.84 M | 1.0118 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw-checked | ok | 10.25 M | 10.34 M | 1.0091 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | aot-object | ok | 8.30 M | 8.29 M | 0.9991 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw | ok | 7.57 M | 7.63 M | 1.0078 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw-checked | ok | 7.26 M | 7.37 M | 1.0143 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | aot-object | ok | 11.42 M | 11.44 M | 1.0020 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw | ok | 10.65 M | 10.75 M | 1.0100 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw-checked | ok | 10.17 M | 10.27 M | 1.0098 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | aot-object | ok | 131.08 M | 131.13 M | 1.0004 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw | ok | 133.61 M | 134.09 M | 1.0036 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw-checked | ok | 123.11 M | 123.89 M | 1.0063 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | aot-object | ok | 180.75 M | 180.27 M | 0.9973 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw | ok | 181.12 M | 181.03 M | 0.9995 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw-checked | ok | 166.24 M | 167.42 M | 1.0071 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | aot-object | ok | 42.08 M | 42.40 M | 1.0075 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | jit-raw | error | 37.79 M | 37.75 M | 0.9989 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | jit-raw-checked | error | 36.24 M | 36.48 M | 1.0067 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | aot-object | error | 0.85 M | 0.83 M | 0.9856 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | jit-raw | error | 0.89 M | 0.85 M | 0.9499 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | jit-raw-checked | error | 0.80 M | 0.80 M | 1.0011 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | aot-object | ok | 272.94 M | 272.67 M | 0.9990 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw | ok | 274.40 M | 274.85 M | 1.0016 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw-checked | ok | 260.81 M | 260.59 M | 0.9991 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | aot-object | ok | 16.41 M | 16.51 M | 1.0060 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw | ok | 16.29 M | 16.32 M | 1.0015 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw-checked | ok | 15.44 M | 15.57 M | 1.0084 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | aot-object | error | 1.55 M | 1.56 M | 1.0052 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | jit-raw | error | 1.53 M | 1.62 M | 1.0588 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | jit-raw-checked | error | 1.51 M | 1.56 M | 1.0301 |
