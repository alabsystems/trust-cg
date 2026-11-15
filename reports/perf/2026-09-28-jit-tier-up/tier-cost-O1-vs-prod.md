# compile-corpus tier cost

LOW: `compile_corpus_tier` at `O1` (2026-09-28T20:22:31Z)  
TOP: `compile_corpus_tier` at `each module's own level` (2026-09-28T20:22:03Z)

**Consistency: PASS** — 139 (entry, lane) pairs compiled on both sides; every repetition of each side agrees with itself; both sides reach the same verdicts.

## Totals (steady-state instructions retired)

| origin | lane | entries | LOW instr | TOP instr | LOW/TOP |
|---|---|--:|--:|--:|--:|
| ALL | jit-raw | 139 | 122,990.3 M | 127,021.9 M | 0.9683 |
| ay-jit-matrix | jit-raw | 5 | 400.5 M | 425.7 M | 0.9407 |
| trust-cg-fixture | jit-raw | 25 | 663.8 M | 781.1 M | 0.8498 |
| ty-prod | jit-raw | 22 | 3,972.4 M | 3,850.0 M | 1.0318 |
| ty-semantic | jit-raw | 87 | 117,953.6 M | 121,965.0 M | 0.9671 |

## Per entry

| origin | entry | lane | LOW level | TOP level | LOW instr | TOP instr | LOW/TOP |
|---|---|---|---|---|--:|--:|--:|
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw | O1 | O2 | 45.87 M | 47.96 M | 0.9564 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw | O1 | O2 | 55.64 M | 60.29 M | 0.9229 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw | O1 | O2 | 137.34 M | 146.72 M | 0.9361 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw | O1 | O2 | 122.57 M | 132.68 M | 0.9238 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw | O1 | O2 | 39.04 M | 38.06 M | 1.0259 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw | O1 | O2 | 22.31 M | 27.68 M | 0.8059 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw | O1 | O2 | 5.94 M | 6.41 M | 0.9274 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw | O1 | O2 | 10.30 M | 13.86 M | 0.7427 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw | O1 | O2 | 1.64 M | 1.88 M | 0.8724 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw | O1 | O2 | 3.13 M | 3.97 M | 0.7899 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw | O1 | O2 | 8.15 M | 10.46 M | 0.7788 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw | O1 | O2 | 3.66 M | 8.81 M | 0.4159 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw | O1 | O2 | 3.35 M | 9.14 M | 0.3662 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw | O1 | O2 | 3.71 M | 9.08 M | 0.4086 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw | O1 | O2 | 3.88 M | 8.66 M | 0.4478 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw | O1 | O2 | 3.97 M | 8.41 M | 0.4718 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw | O1 | O2 | 3.42 M | 6.27 M | 0.5451 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw | O1 | O2 | 3.39 M | 6.83 M | 0.4964 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw | O1 | O2 | 3.56 M | 6.81 M | 0.5224 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw | O1 | O2 | 7.87 M | 15.27 M | 0.5153 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw | O1 | O2 | 7.60 M | 15.02 M | 0.5061 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw | O1 | O2 | 4.55 M | 10.46 M | 0.4347 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw | O1 | O2 | 3.64 M | 9.34 M | 0.3898 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw | O1 | O2 | 3.52 M | 7.62 M | 0.4623 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw | O1 | O2 | 4.79 M | 5.85 M | 0.8179 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw | O1 | O2 | 3.95 M | 7.65 M | 0.5158 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw | O1 | O2 | 118.32 M | 133.14 M | 0.8887 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw | O1 | O2 | 146.56 M | 163.38 M | 0.8970 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw | O1 | O2 | 269.57 M | 270.52 M | 0.9965 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw | O1 | O2 | 13.04 M | 14.58 M | 0.8940 |
| ty-prod | ty-prod/Barrier/0 | jit-raw | O1 | O1 | 130.74 M | 130.72 M | 1.0002 |
| ty-prod | ty-prod/Barriers/0 | jit-raw | O1 | O0 | 337.70 M | 310.38 M | 1.0880 |
| ty-prod | ty-prod/Barriers/1 | jit-raw | O1 | O0 | 341.19 M | 313.09 M | 1.0897 |
| ty-prod | ty-prod/Barriers/10 | jit-raw | O1 | O1 | 128.57 M | 129.24 M | 0.9948 |
| ty-prod | ty-prod/Barriers/2 | jit-raw | O1 | O0 | 343.14 M | 314.90 M | 1.0897 |
| ty-prod | ty-prod/Barriers/3 | jit-raw | O1 | O0 | 318.44 M | 296.58 M | 1.0737 |
| ty-prod | ty-prod/Barriers/4 | jit-raw | O1 | O0 | 292.22 M | 270.15 M | 1.0817 |
| ty-prod | ty-prod/Barriers/5 | jit-raw | O1 | O1 | 38.54 M | 38.20 M | 1.0088 |
| ty-prod | ty-prod/Barriers/6 | jit-raw | O1 | O1 | 55.19 M | 55.40 M | 0.9963 |
| ty-prod | ty-prod/Barriers/7 | jit-raw | O1 | O1 | 439.81 M | 439.70 M | 1.0003 |
| ty-prod | ty-prod/Barriers/8 | jit-raw | O1 | O1 | 92.43 M | 92.85 M | 0.9955 |
| ty-prod | ty-prod/Barriers/9 | jit-raw | O1 | O1 | 335.71 M | 335.63 M | 1.0003 |
| ty-prod | ty-prod/HourClock/0 | jit-raw | O1 | O1 | 107.69 M | 108.51 M | 0.9924 |
| ty-prod | ty-prod/HourClock2/0 | jit-raw | O1 | O1 | 130.76 M | 131.74 M | 0.9926 |
| ty-prod | ty-prod/Lock/0 | jit-raw | O1 | O1 | 109.74 M | 110.99 M | 0.9887 |
| ty-prod | ty-prod/MCConsensus/0 | jit-raw | O1 | O1 | 106.84 M | 107.83 M | 0.9909 |
| ty-prod | ty-prod/MCConsensus_2/0 | jit-raw | O1 | O1 | 107.56 M | 106.89 M | 1.0063 |
| ty-prod | ty-prod/Simple/0 | jit-raw | O1 | O1 | 108.27 M | 108.25 M | 1.0002 |
| ty-prod | ty-prod/SimpleRegular/0 | jit-raw | O1 | O1 | 108.13 M | 108.39 M | 0.9976 |
| ty-prod | ty-prod/clean/0 | jit-raw | O1 | O1 | 83.21 M | 83.88 M | 0.9920 |
| ty-prod | ty-prod/clean/1 | jit-raw | O1 | O1 | 11.09 M | 11.10 M | 0.9997 |
| ty-prod | ty-prod/clean/2 | jit-raw | O1 | O1 | 245.39 M | 245.60 M | 0.9992 |
| ty-semantic | ty-semantic/ABCorrectness/0 | jit-raw | O1 | O2 | 1,825.74 M | 1,909.78 M | 0.9560 |
| ty-semantic | ty-semantic/ABCorrectness/1 | jit-raw | O1 | O1 | 44.87 M | 45.19 M | 0.9931 |
| ty-semantic | ty-semantic/ABCorrectness/2 | jit-raw | O1 | O1 | 31.23 M | 31.27 M | 0.9986 |
| ty-semantic | ty-semantic/ACP_NB_TLC/0 | jit-raw | O1 | O2 | 10,662.93 M | 11,141.83 M | 0.9570 |
| ty-semantic | ty-semantic/ACP_SB_TLC/0 | jit-raw | O1 | O2 | 7,474.00 M | 7,823.19 M | 0.9554 |
| ty-semantic | ty-semantic/AsyncTerminationDetection/0 | jit-raw | O1 | O2 | 3,034.77 M | 3,117.06 M | 0.9736 |
| ty-semantic | ty-semantic/AsynchInterface/0 | jit-raw | O1 | O2 | 1,121.37 M | 1,161.51 M | 0.9654 |
| ty-semantic | ty-semantic/AsynchInterface/1 | jit-raw | O1 | O1 | 37.72 M | 37.86 M | 0.9962 |
| ty-semantic | ty-semantic/AsynchInterface/2 | jit-raw | O1 | O1 | 20.52 M | 20.51 M | 1.0005 |
| ty-semantic | ty-semantic/Barrier/0 | jit-raw | O1 | O2 | 1,012.34 M | 1,014.70 M | 0.9977 |
| ty-semantic | ty-semantic/Barrier/1 | jit-raw | O1 | O1 | 105.21 M | 104.93 M | 1.0027 |
| ty-semantic | ty-semantic/Barrier/2 | jit-raw | O1 | O1 | 17.74 M | 17.75 M | 0.9994 |
| ty-semantic | ty-semantic/Barrier/3 | jit-raw | O1 | O1 | 42.56 M | 41.88 M | 1.0163 |
| ty-semantic | ty-semantic/Barriers/0 | jit-raw | O1 | O2 | 11,152.50 M | 11,186.08 M | 0.9970 |
| ty-semantic | ty-semantic/Barriers/1 | jit-raw | O1 | O0 | 360.30 M | 325.56 M | 1.1067 |
| ty-semantic | ty-semantic/Barriers/10 | jit-raw | O1 | O1 | 336.48 M | 335.46 M | 1.0030 |
| ty-semantic | ty-semantic/Barriers/2 | jit-raw | O1 | O0 | 328.14 M | 304.77 M | 1.0767 |
| ty-semantic | ty-semantic/Barriers/3 | jit-raw | O1 | O0 | 345.44 M | 316.37 M | 1.0919 |
| ty-semantic | ty-semantic/Barriers/4 | jit-raw | O1 | O0 | 310.39 M | 290.70 M | 1.0677 |
| ty-semantic | ty-semantic/Barriers/5 | jit-raw | O1 | O1 | 290.14 M | 289.47 M | 1.0023 |
| ty-semantic | ty-semantic/Barriers/6 | jit-raw | O1 | O1 | 38.60 M | 38.46 M | 1.0037 |
| ty-semantic | ty-semantic/Barriers/7 | jit-raw | O1 | O1 | 55.42 M | 55.67 M | 0.9955 |
| ty-semantic | ty-semantic/Barriers/8 | jit-raw | O1 | O1 | 439.65 M | 439.62 M | 1.0001 |
| ty-semantic | ty-semantic/Barriers/9 | jit-raw | O1 | O1 | 92.57 M | 93.33 M | 0.9918 |
| ty-semantic | ty-semantic/CatEvenBoxes/0 | jit-raw | O1 | O2 | 1,436.60 M | 1,484.89 M | 0.9675 |
| ty-semantic | ty-semantic/Chameneos/0 | jit-raw | O1 | O2 | 2,495.54 M | 2,574.60 M | 0.9693 |
| ty-semantic | ty-semantic/Channel/0 | jit-raw | O1 | O2 | 1,116.04 M | 1,152.23 M | 0.9686 |
| ty-semantic | ty-semantic/Channel/1 | jit-raw | O1 | O1 | 55.44 M | 56.83 M | 0.9755 |
| ty-semantic | ty-semantic/Channel/2 | jit-raw | O1 | O1 | 22.52 M | 22.99 M | 0.9797 |
| ty-semantic | ty-semantic/Consensus/0 | jit-raw | O1 | O2 | 371.68 M | 395.67 M | 0.9394 |
| ty-semantic | ty-semantic/DiningPhilosophers/0 | jit-raw | O1 | O2 | 3,844.70 M | 3,976.82 M | 0.9668 |
| ty-semantic | ty-semantic/HourClock/0 | jit-raw | O1 | O2 | 305.40 M | 303.95 M | 1.0048 |
| ty-semantic | ty-semantic/HourClock/1 | jit-raw | O1 | O1 | 7.32 M | 7.29 M | 1.0034 |
| ty-semantic | ty-semantic/HourClock/2 | jit-raw | O1 | O1 | 10.36 M | 10.41 M | 0.9948 |
| ty-semantic | ty-semantic/HourClock2/0 | jit-raw | O1 | O2 | 267.93 M | 264.19 M | 1.0142 |
| ty-semantic | ty-semantic/HourClock2/1 | jit-raw | O1 | O1 | 16.74 M | 16.76 M | 0.9988 |
| ty-semantic | ty-semantic/LiveHourClock/0 | jit-raw | O1 | O2 | 266.82 M | 264.02 M | 1.0106 |
| ty-semantic | ty-semantic/Lock/0 | jit-raw | O1 | O2 | 2,147.07 M | 2,237.23 M | 0.9597 |
| ty-semantic | ty-semantic/Lock/1 | jit-raw | O1 | O1 | 65.17 M | 65.17 M | 1.0000 |
| ty-semantic | ty-semantic/Lock/2 | jit-raw | O1 | O1 | 25.20 M | 25.20 M | 0.9998 |
| ty-semantic | ty-semantic/Lock/3 | jit-raw | O1 | O1 | 48.94 M | 48.56 M | 1.0077 |
| ty-semantic | ty-semantic/MCConsensus/0 | jit-raw | O1 | O2 | 555.37 M | 574.91 M | 0.9660 |
| ty-semantic | ty-semantic/MCConsensus/1 | jit-raw | O1 | O1 | 12.48 M | 12.48 M | 0.9997 |
| ty-semantic | ty-semantic/MCConsensus/2 | jit-raw | O1 | O1 | 15.96 M | 15.77 M | 1.0118 |
| ty-semantic | ty-semantic/MCConsensus_2/0 | jit-raw | O1 | O2 | 380.73 M | 404.01 M | 0.9424 |
| ty-semantic | ty-semantic/MCConsensus_2/1 | jit-raw | O1 | O1 | 12.47 M | 12.58 M | 0.9914 |
| ty-semantic | ty-semantic/MCConsensus_2/2 | jit-raw | O1 | O1 | 15.78 M | 15.90 M | 0.9925 |
| ty-semantic | ty-semantic/MCInnerFIFO/0 | jit-raw | O1 | O2 | 2,921.57 M | 3,036.52 M | 0.9621 |
| ty-semantic | ty-semantic/MCInternalMemory/0 | jit-raw | O1 | O2 | 3,276.41 M | 3,397.26 M | 0.9644 |
| ty-semantic | ty-semantic/MCLiveInternalMemory/0 | jit-raw | O1 | O2 | 3,062.71 M | 3,172.71 M | 0.9653 |
| ty-semantic | ty-semantic/Peterson/0 | jit-raw | O1 | O2 | 3,902.84 M | 4,060.08 M | 0.9613 |
| ty-semantic | ty-semantic/Peterson/1 | jit-raw | O1 | O1 | 187.92 M | 187.72 M | 1.0011 |
| ty-semantic | ty-semantic/Peterson/2 | jit-raw | O1 | O1 | 35.77 M | 36.22 M | 0.9874 |
| ty-semantic | ty-semantic/Peterson/3 | jit-raw | O1 | O1 | 94.09 M | 94.38 M | 0.9969 |
| ty-semantic | ty-semantic/Prisoner/0 | jit-raw | O1 | O2 | 2,547.78 M | 2,675.38 M | 0.9523 |
| ty-semantic | ty-semantic/Simple/0 | jit-raw | O1 | O2 | 2,911.88 M | 2,957.10 M | 0.9847 |
| ty-semantic | ty-semantic/Simple/1 | jit-raw | O1 | O0 | 329.81 M | 305.99 M | 1.0778 |
| ty-semantic | ty-semantic/Simple/2 | jit-raw | O1 | O1 | 43.04 M | 43.24 M | 0.9954 |
| ty-semantic | ty-semantic/Simple/3 | jit-raw | O1 | O1 | 74.11 M | 74.23 M | 0.9983 |
| ty-semantic | ty-semantic/Simple/4 | jit-raw | O1 | O1 | 155.19 M | 154.68 M | 1.0033 |
| ty-semantic | ty-semantic/SimpleRegular/0 | jit-raw | O1 | O2 | 3,485.60 M | 3,541.79 M | 0.9841 |
| ty-semantic | ty-semantic/SimpleRegular/1 | jit-raw | O1 | O0 | 721.10 M | 639.36 M | 1.1279 |
| ty-semantic | ty-semantic/SimpleRegular/2 | jit-raw | O1 | O0 | 615.41 M | 562.10 M | 1.0948 |
| ty-semantic | ty-semantic/SimpleRegular/3 | jit-raw | O1 | O1 | 35.36 M | 35.27 M | 1.0026 |
| ty-semantic | ty-semantic/SimpleRegular/4 | jit-raw | O1 | O1 | 43.33 M | 43.18 M | 1.0035 |
| ty-semantic | ty-semantic/SpanTree/0 | jit-raw | O1 | O2 | 1,311.51 M | 1,323.27 M | 0.9911 |
| ty-semantic | ty-semantic/SyncTerminationDetection/0 | jit-raw | O1 | O2 | 1,924.04 M | 1,979.16 M | 0.9721 |
| ty-semantic | ty-semantic/TCommit/0 | jit-raw | O1 | O2 | 1,611.64 M | 1,671.90 M | 0.9640 |
| ty-semantic | ty-semantic/TCommit/1 | jit-raw | O1 | O1 | 189.82 M | 190.10 M | 0.9985 |
| ty-semantic | ty-semantic/TCommit/2 | jit-raw | O1 | O1 | 17.21 M | 17.25 M | 0.9972 |
| ty-semantic | ty-semantic/TCommit/3 | jit-raw | O1 | O1 | 31.85 M | 31.92 M | 0.9979 |
| ty-semantic | ty-semantic/TwoPhase/0 | jit-raw | O1 | O2 | 3,405.16 M | 3,632.21 M | 0.9375 |
| ty-semantic | ty-semantic/VoucherLifeCycle/0 | jit-raw | O1 | O2 | 2,588.55 M | 2,683.34 M | 0.9647 |
| ty-semantic | ty-semantic/VoucherLifeCycle/1 | jit-raw | O1 | O1 | 140.42 M | 139.33 M | 1.0078 |
| ty-semantic | ty-semantic/VoucherLifeCycle/2 | jit-raw | O1 | O1 | 33.87 M | 33.94 M | 0.9979 |
| ty-semantic | ty-semantic/VoucherLifeCycle/3 | jit-raw | O1 | O1 | 70.01 M | 69.98 M | 1.0004 |
| ty-semantic | ty-semantic/clean/0 | jit-raw | O1 | O2 | 2,032.35 M | 2,188.40 M | 0.9287 |
| ty-semantic | ty-semantic/clean/1 | jit-raw | O1 | O1 | 83.71 M | 83.39 M | 1.0038 |
| ty-semantic | ty-semantic/clean/2 | jit-raw | O1 | O1 | 11.09 M | 11.14 M | 0.9953 |
| ty-semantic | ty-semantic/clean/3 | jit-raw | O1 | O1 | 2.73 M | 2.76 M | 0.9897 |
| ty-semantic | ty-semantic/clean/4 | jit-raw | O1 | O1 | 14.85 M | 14.84 M | 1.0004 |
| ty-semantic | ty-semantic/clean/5 | jit-raw | O1 | O1 | 34.96 M | 34.60 M | 1.0104 |
| ty-semantic | ty-semantic/dijkstra-mutex_LSpec-model/0 | jit-raw | O1 | O2 | 8,286.69 M | 8,641.92 M | 0.9589 |
| ty-semantic | ty-semantic/kvstore/0 | jit-raw | O1 | O2 | 4,801.28 M | 5,099.59 M | 0.9415 |
| ty-semantic | ty-semantic/nbacc_ray97/0 | jit-raw | O1 | O2 | 4,077.24 M | 4,207.92 M | 0.9689 |
| ty-semantic | ty-semantic/nbacg_guer01/0 | jit-raw | O1 | O2 | 7,418.50 M | 7,839.28 M | 0.9463 |
| ty-semantic | ty-semantic/stages/0 | jit-raw | O1 | O2 | 2,745.33 M | 2,966.11 M | 0.9256 |
