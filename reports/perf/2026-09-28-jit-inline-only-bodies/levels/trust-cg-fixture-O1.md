# compile-corpus compare

A: `cc-base` (2026-09-29T00:16:23Z)  
B: `cc-lane` (2026-09-29T00:16:24Z)

**Identity: PASS** — 105 (entry, lane) pairs: same verdicts, error texts, emitted-code digests and frame-net counters on both sides, every repetition.

## Totals (steady-state instructions retired / cycles elapsed)

| origin | lane | A instr | B instr | B/A | A cycles | B cycles | B/A |
|---|---|--:|--:|--:|--:|--:|--:|
| ALL | aot-object | 949.2 M | 949.2 M | 1.0000 | 214.5 M | 218.8 M | 1.0201 |
| ALL | jit-raw | 921.8 M | 923.7 M | 1.0020 | 214.1 M | 220.0 M | 1.0274 |
| ALL | jit-raw-checked | 855.6 M | 859.0 M | 1.0040 | 192.9 M | 197.2 M | 1.0223 |
| trust-cg-fixture | aot-object | 949.2 M | 949.2 M | 1.0000 | 214.5 M | 218.8 M | 1.0201 |
| trust-cg-fixture | jit-raw | 921.8 M | 923.7 M | 1.0020 | 214.1 M | 220.0 M | 1.0274 |
| trust-cg-fixture | jit-raw-checked | 855.6 M | 859.0 M | 1.0040 | 192.9 M | 197.2 M | 1.0223 |

## Per phase bracket (all entries)

| lane | phase | A instr | B instr | B/A |
|---|---|--:|--:|--:|
| aot-object | compile | 946.4 M | 946.4 M | 1.0001 |
| jit-raw | adapter | 51.7 M | 51.7 M | 0.9984 |
| jit-raw | link | 104.3 M | 103.8 M | 0.9944 |
| jit-raw | lir_prepare | 0.0 M | 2.1 M | 0.0000 |
| jit-raw | prepare | 755.5 M | 755.4 M | 0.9999 |
| jit-raw-checked | adapter | 50.9 M | 50.8 M | 0.9982 |
| jit-raw-checked | link | 51.8 M | 51.7 M | 0.9980 |
| jit-raw-checked | lir_prepare | 0.0 M | 2.0 M | 0.0000 |
| jit-raw-checked | prepare | 743.0 M | 743.9 M | 1.0012 |

## Per entry

| origin | entry | lane | verdict | A instr | B instr | B/A |
|---|---|---|---|--:|--:|--:|
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | aot-object | ok | 174.47 M | 174.13 M | 0.9980 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | jit-raw | error | 163.72 M | 162.70 M | 0.9937 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--corpus | jit-raw-checked | error | 149.20 M | 149.46 M | 1.0017 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | aot-object | ok | 23.09 M | 23.45 M | 1.0156 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw | ok | 22.49 M | 22.53 M | 1.0017 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw-checked | ok | 21.08 M | 20.71 M | 0.9827 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | aot-object | ok | 6.75 M | 6.72 M | 0.9957 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw | ok | 6.08 M | 6.15 M | 1.0112 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw-checked | ok | 5.90 M | 5.92 M | 1.0046 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | aot-object | ok | 7.28 M | 7.28 M | 1.0000 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | jit-raw | error | 6.92 M | 6.96 M | 1.0059 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest3 | jit-raw-checked | error | 6.44 M | 6.50 M | 1.0080 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | aot-object | ok | 5.65 M | 5.66 M | 1.0017 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | jit-raw | error | 5.38 M | 5.41 M | 1.0054 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--casttest_trunc_i8 | jit-raw-checked | error | 5.03 M | 5.06 M | 1.0064 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | aot-object | ok | 11.46 M | 11.55 M | 1.0073 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw | ok | 10.40 M | 10.49 M | 1.0093 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw-checked | ok | 9.68 M | 9.79 M | 1.0121 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | aot-object | ok | 1.88 M | 1.87 M | 0.9968 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | jit-raw | error | 1.74 M | 1.83 M | 1.0539 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--mutable_byte_globals | jit-raw-checked | error | 1.55 M | 1.63 M | 1.0482 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | aot-object | ok | 1.65 M | 1.55 M | 0.9424 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw | ok | 1.61 M | 1.67 M | 1.0387 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw-checked | ok | 1.48 M | 1.50 M | 1.0173 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | aot-object | ok | 3.25 M | 3.23 M | 0.9953 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | jit-raw | error | 3.18 M | 3.16 M | 0.9939 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--printf_string_global | jit-raw-checked | error | 2.88 M | 2.91 M | 1.0111 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | aot-object | ok | 3.40 M | 3.38 M | 0.9958 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw | ok | 3.16 M | 3.26 M | 1.0301 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw-checked | ok | 2.91 M | 2.98 M | 1.0243 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | aot-object | ok | 8.93 M | 8.94 M | 1.0010 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw | ok | 8.10 M | 8.23 M | 1.0155 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw-checked | ok | 7.58 M | 7.73 M | 1.0200 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | aot-object | ok | 20.31 M | 20.38 M | 1.0038 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | jit-raw | error | 20.30 M | 20.36 M | 1.0030 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_divtest | jit-raw-checked | error | 18.76 M | 18.88 M | 1.0064 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | aot-object | ok | 25.00 M | 25.19 M | 1.0076 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | jit-raw | error | 24.94 M | 24.97 M | 1.0012 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--ws2_nottest | jit-raw-checked | error | 23.07 M | 23.06 M | 0.9994 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | aot-object | ok | 4.23 M | 4.22 M | 0.9982 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw | ok | 3.65 M | 3.74 M | 1.0239 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw-checked | ok | 3.40 M | 3.46 M | 1.0166 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | aot-object | ok | 3.97 M | 3.98 M | 1.0022 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw | ok | 3.31 M | 3.43 M | 1.0369 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw-checked | ok | 3.05 M | 3.15 M | 1.0330 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | aot-object | ok | 4.30 M | 4.30 M | 1.0001 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw | ok | 3.63 M | 3.79 M | 1.0421 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw-checked | ok | 3.40 M | 3.48 M | 1.0233 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | aot-object | ok | 4.36 M | 4.35 M | 0.9972 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw | ok | 3.81 M | 3.96 M | 1.0398 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw-checked | ok | 3.54 M | 3.64 M | 1.0270 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | aot-object | ok | 4.67 M | 4.66 M | 0.9994 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw | ok | 3.93 M | 4.05 M | 1.0297 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw-checked | ok | 3.66 M | 3.76 M | 1.0261 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | aot-object | ok | 3.75 M | 3.74 M | 0.9972 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw | ok | 3.36 M | 3.48 M | 1.0369 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw-checked | ok | 3.11 M | 3.17 M | 1.0183 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | aot-object | ok | 3.92 M | 3.93 M | 1.0018 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw | ok | 3.37 M | 3.47 M | 1.0298 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw-checked | ok | 3.10 M | 3.19 M | 1.0298 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | aot-object | ok | 3.91 M | 3.92 M | 1.0026 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw | ok | 3.36 M | 3.47 M | 1.0327 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw-checked | ok | 3.12 M | 3.19 M | 1.0226 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | aot-object | ok | 9.14 M | 9.15 M | 1.0006 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw | ok | 7.73 M | 7.79 M | 1.0073 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw-checked | ok | 6.95 M | 7.03 M | 1.0107 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | aot-object | ok | 9.01 M | 9.01 M | 1.0001 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw | ok | 7.53 M | 7.58 M | 1.0074 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw-checked | ok | 6.78 M | 6.82 M | 1.0069 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | aot-object | ok | 5.03 M | 5.02 M | 0.9988 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw | ok | 4.50 M | 4.62 M | 1.0259 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw-checked | ok | 4.15 M | 4.22 M | 1.0148 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | aot-object | ok | 4.26 M | 4.26 M | 0.9994 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw | ok | 3.60 M | 3.74 M | 1.0394 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw-checked | ok | 3.39 M | 3.44 M | 1.0153 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | aot-object | ok | 3.85 M | 3.86 M | 1.0005 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw | ok | 3.48 M | 3.58 M | 1.0308 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw-checked | ok | 3.20 M | 3.28 M | 1.0237 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | aot-object | ok | 5.51 M | 5.51 M | 0.9991 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw | ok | 4.79 M | 4.93 M | 1.0285 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw-checked | ok | 4.38 M | 4.48 M | 1.0230 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | aot-object | ok | 4.45 M | 4.44 M | 0.9971 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw | ok | 3.90 M | 3.99 M | 1.0217 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw-checked | ok | 3.62 M | 3.71 M | 1.0246 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | aot-object | ok | 115.89 M | 115.72 M | 0.9985 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw | ok | 117.96 M | 117.81 M | 0.9987 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw-checked | ok | 107.92 M | 108.85 M | 1.0086 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | aot-object | ok | 147.49 M | 147.53 M | 1.0002 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw | ok | 147.02 M | 147.12 M | 1.0007 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw-checked | ok | 133.73 M | 134.57 M | 1.0063 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | aot-object | ok | 35.73 M | 35.61 M | 0.9968 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | jit-raw | error | 31.12 M | 31.13 M | 1.0003 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke | jit-raw-checked | error | 29.84 M | 30.19 M | 1.0115 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | aot-object | error | 0.84 M | 0.84 M | 1.0087 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | jit-raw | error | 0.86 M | 0.83 M | 0.9611 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--invoke_variadic | jit-raw-checked | error | 0.80 M | 0.79 M | 0.9874 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | aot-object | ok | 266.57 M | 266.44 M | 0.9995 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw | ok | 268.14 M | 268.57 M | 1.0016 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw-checked | ok | 255.23 M | 254.48 M | 0.9971 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | aot-object | ok | 13.61 M | 13.79 M | 1.0129 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw | ok | 13.21 M | 13.29 M | 1.0058 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw-checked | ok | 12.18 M | 12.48 M | 1.0243 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | aot-object | error | 1.57 M | 1.56 M | 0.9918 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | jit-raw | error | 1.53 M | 1.59 M | 1.0397 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--variadic | jit-raw-checked | error | 1.51 M | 1.56 M | 1.0330 |
