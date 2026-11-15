# compile-corpus tier cost

LOW: `compile_corpus_tier` at `O0` (2026-09-28T20:21:36Z)  
TOP: `compile_corpus_tier` at `each module's own level` (2026-09-28T20:22:03Z)

**Consistency: PASS** — 139 (entry, lane) pairs compiled on both sides; every repetition of each side agrees with itself; both sides reach the same verdicts.

## Totals (steady-state instructions retired)

| origin | lane | entries | LOW instr | TOP instr | LOW/TOP |
|---|---|--:|--:|--:|--:|
| ALL | jit-raw | 139 | 122,680.7 M | 127,021.9 M | 0.9658 |
| ay-jit-matrix | jit-raw | 5 | 384.0 M | 425.7 M | 0.9021 |
| trust-cg-fixture | jit-raw | 25 | 475.1 M | 781.1 M | 0.6082 |
| ty-prod | jit-raw | 22 | 3,975.5 M | 3,850.0 M | 1.0326 |
| ty-semantic | jit-raw | 87 | 117,846.2 M | 121,965.0 M | 0.9662 |

## Per entry

| origin | entry | lane | LOW level | TOP level | LOW instr | TOP instr | LOW/TOP |
|---|---|---|---|---|--:|--:|--:|
| ay-jit-matrix | ay-jit-matrix/bcp-propagate | jit-raw | O0 | O2 | 43.52 M | 47.96 M | 0.9074 |
| ay-jit-matrix | ay-jit-matrix/bcp-propagate-with-decisions | jit-raw | O0 | O2 | 53.41 M | 60.29 M | 0.8859 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal | jit-raw | O0 | O2 | 133.36 M | 146.72 M | 0.9090 |
| ay-jit-matrix | ay-jit-matrix/bcp-watched-literal-chunked | jit-raw | O0 | O2 | 115.90 M | 132.68 M | 0.8735 |
| ay-jit-matrix | ay-jit-matrix/parent-loop | jit-raw | O0 | O2 | 37.81 M | 38.06 M | 0.9936 |
| trust-cg-fixture | trust-cg-fixture/aggregate_insert--zero_sized | jit-raw | O0 | O2 | 23.47 M | 27.68 M | 0.8479 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--bitreverse_intrinsics | jit-raw | O0 | O2 | 5.69 M | 6.41 M | 0.8877 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--fp_core_binops | jit-raw | O0 | O2 | 9.01 M | 13.86 M | 0.6501 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--objectsize_intrinsic | jit-raw | O0 | O2 | 1.63 M | 1.88 M | 0.8668 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_dispatch | jit-raw | O0 | O2 | 2.71 M | 3.97 M | 0.6831 |
| trust-cg-fixture | trust-cg-fixture/fsym_real_function_corpus--switch_narrow_widths | jit-raw | O0 | O2 | 6.77 M | 10.46 M | 0.6470 |
| trust-cg-fixture | trust-cg-fixture/fuzz--abs | jit-raw | O0 | O2 | 3.49 M | 8.81 M | 0.3964 |
| trust-cg-fixture | trust-cg-fixture/fuzz--axpy | jit-raw | O0 | O2 | 2.98 M | 9.14 M | 0.3256 |
| trust-cg-fixture | trust-cg-fixture/fuzz--ceq | jit-raw | O0 | O2 | 3.57 M | 9.08 M | 0.3928 |
| trust-cg-fixture | trust-cg-fixture/fuzz--crcx | jit-raw | O0 | O2 | 3.70 M | 8.66 M | 0.4269 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fdot | jit-raw | O0 | O2 | 3.96 M | 8.41 M | 0.4711 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fib | jit-raw | O0 | O2 | 3.23 M | 6.27 M | 0.5153 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum | jit-raw | O0 | O2 | 3.45 M | 6.83 M | 0.5048 |
| trust-cg-fixture | trust-cg-fixture/fuzz--fsum64 | jit-raw | O0 | O2 | 3.44 M | 6.81 M | 0.5058 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ijk | jit-raw | O0 | O2 | 6.98 M | 15.27 M | 0.4569 |
| trust-cg-fixture | trust-cg-fixture/fuzz--mm_ikj | jit-raw | O0 | O2 | 6.83 M | 15.02 M | 0.4550 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pc | jit-raw | O0 | O2 | 4.34 M | 10.46 M | 0.4147 |
| trust-cg-fixture | trust-cg-fixture/fuzz--pm | jit-raw | O0 | O2 | 3.54 M | 9.34 M | 0.3790 |
| trust-cg-fixture | trust-cg-fixture/fuzz--prodi64 | jit-raw | O0 | O2 | 3.32 M | 7.62 M | 0.4365 |
| trust-cg-fixture | trust-cg-fixture/fuzz--st | jit-raw | O0 | O2 | 4.41 M | 5.85 M | 0.7534 |
| trust-cg-fixture | trust-cg-fixture/fuzz--trib | jit-raw | O0 | O2 | 3.72 M | 7.65 M | 0.4863 |
| trust-cg-fixture | trust-cg-fixture/hfa_zero_sized--corpus | jit-raw | O0 | O2 | 102.73 M | 133.14 M | 0.7717 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--corpus | jit-raw | O0 | O2 | 123.22 M | 163.38 M | 0.7542 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--scaling | jit-raw | O0 | O2 | 127.39 M | 270.52 M | 0.4709 |
| trust-cg-fixture | trust-cg-fixture/large_aggregate_args--tail | jit-raw | O0 | O2 | 11.49 M | 14.58 M | 0.7880 |
| ty-prod | ty-prod/Barrier/0 | jit-raw | O0 | O1 | 116.55 M | 130.72 M | 0.8916 |
| ty-prod | ty-prod/Barriers/0 | jit-raw | O0 | O0 | 311.13 M | 310.38 M | 1.0024 |
| ty-prod | ty-prod/Barriers/1 | jit-raw | O0 | O0 | 313.52 M | 313.09 M | 1.0014 |
| ty-prod | ty-prod/Barriers/10 | jit-raw | O0 | O1 | 117.11 M | 129.24 M | 0.9062 |
| ty-prod | ty-prod/Barriers/2 | jit-raw | O0 | O0 | 315.36 M | 314.90 M | 1.0014 |
| ty-prod | ty-prod/Barriers/3 | jit-raw | O0 | O0 | 298.03 M | 296.58 M | 1.0049 |
| ty-prod | ty-prod/Barriers/4 | jit-raw | O0 | O0 | 269.27 M | 270.15 M | 0.9968 |
| ty-prod | ty-prod/Barriers/5 | jit-raw | O0 | O1 | 35.18 M | 38.20 M | 0.9209 |
| ty-prod | ty-prod/Barriers/6 | jit-raw | O0 | O1 | 64.34 M | 55.40 M | 1.1615 |
| ty-prod | ty-prod/Barriers/7 | jit-raw | O0 | O1 | 659.25 M | 439.70 M | 1.4993 |
| ty-prod | ty-prod/Barriers/8 | jit-raw | O0 | O1 | 90.27 M | 92.85 M | 0.9722 |
| ty-prod | ty-prod/Barriers/9 | jit-raw | O0 | O1 | 368.11 M | 335.63 M | 1.0968 |
| ty-prod | ty-prod/HourClock/0 | jit-raw | O0 | O1 | 96.49 M | 108.51 M | 0.8892 |
| ty-prod | ty-prod/HourClock2/0 | jit-raw | O0 | O1 | 116.68 M | 131.74 M | 0.8857 |
| ty-prod | ty-prod/Lock/0 | jit-raw | O0 | O1 | 98.87 M | 110.99 M | 0.8908 |
| ty-prod | ty-prod/MCConsensus/0 | jit-raw | O0 | O1 | 96.56 M | 107.83 M | 0.8955 |
| ty-prod | ty-prod/MCConsensus_2/0 | jit-raw | O0 | O1 | 96.36 M | 106.89 M | 0.9015 |
| ty-prod | ty-prod/Simple/0 | jit-raw | O0 | O1 | 97.12 M | 108.25 M | 0.8972 |
| ty-prod | ty-prod/SimpleRegular/0 | jit-raw | O0 | O1 | 97.25 M | 108.39 M | 0.8972 |
| ty-prod | ty-prod/clean/0 | jit-raw | O0 | O1 | 80.57 M | 83.88 M | 0.9605 |
| ty-prod | ty-prod/clean/1 | jit-raw | O0 | O1 | 12.24 M | 11.10 M | 1.1034 |
| ty-prod | ty-prod/clean/2 | jit-raw | O0 | O1 | 225.20 M | 245.60 M | 0.9169 |
| ty-semantic | ty-semantic/ABCorrectness/0 | jit-raw | O0 | O2 | 1,760.71 M | 1,909.78 M | 0.9219 |
| ty-semantic | ty-semantic/ABCorrectness/1 | jit-raw | O0 | O1 | 42.96 M | 45.19 M | 0.9508 |
| ty-semantic | ty-semantic/ABCorrectness/2 | jit-raw | O0 | O1 | 29.79 M | 31.27 M | 0.9526 |
| ty-semantic | ty-semantic/ACP_NB_TLC/0 | jit-raw | O0 | O2 | 10,690.36 M | 11,141.83 M | 0.9595 |
| ty-semantic | ty-semantic/ACP_SB_TLC/0 | jit-raw | O0 | O2 | 7,434.72 M | 7,823.19 M | 0.9503 |
| ty-semantic | ty-semantic/AsyncTerminationDetection/0 | jit-raw | O0 | O2 | 2,976.06 M | 3,117.06 M | 0.9548 |
| ty-semantic | ty-semantic/AsynchInterface/0 | jit-raw | O0 | O2 | 1,084.87 M | 1,161.51 M | 0.9340 |
| ty-semantic | ty-semantic/AsynchInterface/1 | jit-raw | O0 | O1 | 35.88 M | 37.86 M | 0.9476 |
| ty-semantic | ty-semantic/AsynchInterface/2 | jit-raw | O0 | O1 | 19.35 M | 20.51 M | 0.9436 |
| ty-semantic | ty-semantic/Barrier/0 | jit-raw | O0 | O2 | 996.63 M | 1,014.70 M | 0.9822 |
| ty-semantic | ty-semantic/Barrier/1 | jit-raw | O0 | O1 | 101.54 M | 104.93 M | 0.9678 |
| ty-semantic | ty-semantic/Barrier/2 | jit-raw | O0 | O1 | 16.34 M | 17.75 M | 0.9205 |
| ty-semantic | ty-semantic/Barrier/3 | jit-raw | O0 | O1 | 51.78 M | 41.88 M | 1.2364 |
| ty-semantic | ty-semantic/Barriers/0 | jit-raw | O0 | O2 | 12,212.13 M | 11,186.08 M | 1.0917 |
| ty-semantic | ty-semantic/Barriers/1 | jit-raw | O0 | O0 | 326.16 M | 325.56 M | 1.0018 |
| ty-semantic | ty-semantic/Barriers/10 | jit-raw | O0 | O1 | 368.18 M | 335.46 M | 1.0975 |
| ty-semantic | ty-semantic/Barriers/2 | jit-raw | O0 | O0 | 303.06 M | 304.77 M | 0.9944 |
| ty-semantic | ty-semantic/Barriers/3 | jit-raw | O0 | O0 | 316.14 M | 316.37 M | 0.9993 |
| ty-semantic | ty-semantic/Barriers/4 | jit-raw | O0 | O0 | 291.35 M | 290.70 M | 1.0022 |
| ty-semantic | ty-semantic/Barriers/5 | jit-raw | O0 | O1 | 266.63 M | 289.47 M | 0.9211 |
| ty-semantic | ty-semantic/Barriers/6 | jit-raw | O0 | O1 | 35.51 M | 38.46 M | 0.9233 |
| ty-semantic | ty-semantic/Barriers/7 | jit-raw | O0 | O1 | 64.67 M | 55.67 M | 1.1617 |
| ty-semantic | ty-semantic/Barriers/8 | jit-raw | O0 | O1 | 661.02 M | 439.62 M | 1.5036 |
| ty-semantic | ty-semantic/Barriers/9 | jit-raw | O0 | O1 | 90.50 M | 93.33 M | 0.9697 |
| ty-semantic | ty-semantic/CatEvenBoxes/0 | jit-raw | O0 | O2 | 1,387.89 M | 1,484.89 M | 0.9347 |
| ty-semantic | ty-semantic/Chameneos/0 | jit-raw | O0 | O2 | 2,485.16 M | 2,574.60 M | 0.9653 |
| ty-semantic | ty-semantic/Channel/0 | jit-raw | O0 | O2 | 1,110.14 M | 1,152.23 M | 0.9635 |
| ty-semantic | ty-semantic/Channel/1 | jit-raw | O0 | O1 | 50.63 M | 56.83 M | 0.8910 |
| ty-semantic | ty-semantic/Channel/2 | jit-raw | O0 | O1 | 20.49 M | 22.99 M | 0.8915 |
| ty-semantic | ty-semantic/Consensus/0 | jit-raw | O0 | O2 | 355.72 M | 395.67 M | 0.8990 |
| ty-semantic | ty-semantic/DiningPhilosophers/0 | jit-raw | O0 | O2 | 3,814.98 M | 3,976.82 M | 0.9593 |
| ty-semantic | ty-semantic/HourClock/0 | jit-raw | O0 | O2 | 297.50 M | 303.95 M | 0.9788 |
| ty-semantic | ty-semantic/HourClock/1 | jit-raw | O0 | O1 | 6.36 M | 7.29 M | 0.8723 |
| ty-semantic | ty-semantic/HourClock/2 | jit-raw | O0 | O1 | 9.67 M | 10.41 M | 0.9284 |
| ty-semantic | ty-semantic/HourClock2/0 | jit-raw | O0 | O2 | 260.20 M | 264.19 M | 0.9849 |
| ty-semantic | ty-semantic/HourClock2/1 | jit-raw | O0 | O1 | 15.95 M | 16.76 M | 0.9519 |
| ty-semantic | ty-semantic/LiveHourClock/0 | jit-raw | O0 | O2 | 260.08 M | 264.02 M | 0.9851 |
| ty-semantic | ty-semantic/Lock/0 | jit-raw | O0 | O2 | 2,105.93 M | 2,237.23 M | 0.9413 |
| ty-semantic | ty-semantic/Lock/1 | jit-raw | O0 | O1 | 66.69 M | 65.17 M | 1.0233 |
| ty-semantic | ty-semantic/Lock/2 | jit-raw | O0 | O1 | 23.09 M | 25.20 M | 0.9162 |
| ty-semantic | ty-semantic/Lock/3 | jit-raw | O0 | O1 | 58.03 M | 48.56 M | 1.1950 |
| ty-semantic | ty-semantic/MCConsensus/0 | jit-raw | O0 | O2 | 534.26 M | 574.91 M | 0.9293 |
| ty-semantic | ty-semantic/MCConsensus/1 | jit-raw | O0 | O1 | 14.19 M | 12.48 M | 1.1367 |
| ty-semantic | ty-semantic/MCConsensus/2 | jit-raw | O0 | O1 | 16.50 M | 15.77 M | 1.0463 |
| ty-semantic | ty-semantic/MCConsensus_2/0 | jit-raw | O0 | O2 | 366.07 M | 404.01 M | 0.9061 |
| ty-semantic | ty-semantic/MCConsensus_2/1 | jit-raw | O0 | O1 | 14.18 M | 12.58 M | 1.1269 |
| ty-semantic | ty-semantic/MCConsensus_2/2 | jit-raw | O0 | O1 | 16.54 M | 15.90 M | 1.0399 |
| ty-semantic | ty-semantic/MCInnerFIFO/0 | jit-raw | O0 | O2 | 2,874.68 M | 3,036.52 M | 0.9467 |
| ty-semantic | ty-semantic/MCInternalMemory/0 | jit-raw | O0 | O2 | 3,271.42 M | 3,397.26 M | 0.9630 |
| ty-semantic | ty-semantic/MCLiveInternalMemory/0 | jit-raw | O0 | O2 | 3,056.18 M | 3,172.71 M | 0.9633 |
| ty-semantic | ty-semantic/Peterson/0 | jit-raw | O0 | O2 | 3,868.71 M | 4,060.08 M | 0.9529 |
| ty-semantic | ty-semantic/Peterson/1 | jit-raw | O0 | O1 | 186.84 M | 187.72 M | 0.9953 |
| ty-semantic | ty-semantic/Peterson/2 | jit-raw | O0 | O1 | 34.12 M | 36.22 M | 0.9419 |
| ty-semantic | ty-semantic/Peterson/3 | jit-raw | O0 | O1 | 113.28 M | 94.38 M | 1.2003 |
| ty-semantic | ty-semantic/Prisoner/0 | jit-raw | O0 | O2 | 2,496.82 M | 2,675.38 M | 0.9333 |
| ty-semantic | ty-semantic/Simple/0 | jit-raw | O0 | O2 | 2,941.14 M | 2,957.10 M | 0.9946 |
| ty-semantic | ty-semantic/Simple/1 | jit-raw | O0 | O0 | 306.87 M | 305.99 M | 1.0029 |
| ty-semantic | ty-semantic/Simple/2 | jit-raw | O0 | O1 | 48.17 M | 43.24 M | 1.1139 |
| ty-semantic | ty-semantic/Simple/3 | jit-raw | O0 | O1 | 69.43 M | 74.23 M | 0.9352 |
| ty-semantic | ty-semantic/Simple/4 | jit-raw | O0 | O1 | 166.24 M | 154.68 M | 1.0748 |
| ty-semantic | ty-semantic/SimpleRegular/0 | jit-raw | O0 | O2 | 3,511.69 M | 3,541.79 M | 0.9915 |
| ty-semantic | ty-semantic/SimpleRegular/1 | jit-raw | O0 | O0 | 638.64 M | 639.36 M | 0.9989 |
| ty-semantic | ty-semantic/SimpleRegular/2 | jit-raw | O0 | O0 | 561.60 M | 562.10 M | 0.9991 |
| ty-semantic | ty-semantic/SimpleRegular/3 | jit-raw | O0 | O1 | 32.79 M | 35.27 M | 0.9295 |
| ty-semantic | ty-semantic/SimpleRegular/4 | jit-raw | O0 | O1 | 48.33 M | 43.18 M | 1.1193 |
| ty-semantic | ty-semantic/SpanTree/0 | jit-raw | O0 | O2 | 1,292.83 M | 1,323.27 M | 0.9770 |
| ty-semantic | ty-semantic/SyncTerminationDetection/0 | jit-raw | O0 | O2 | 1,878.09 M | 1,979.16 M | 0.9489 |
| ty-semantic | ty-semantic/TCommit/0 | jit-raw | O0 | O2 | 1,587.61 M | 1,671.90 M | 0.9496 |
| ty-semantic | ty-semantic/TCommit/1 | jit-raw | O0 | O1 | 183.66 M | 190.10 M | 0.9661 |
| ty-semantic | ty-semantic/TCommit/2 | jit-raw | O0 | O1 | 15.76 M | 17.25 M | 0.9132 |
| ty-semantic | ty-semantic/TCommit/3 | jit-raw | O0 | O1 | 35.31 M | 31.92 M | 1.1062 |
| ty-semantic | ty-semantic/TwoPhase/0 | jit-raw | O0 | O2 | 3,314.22 M | 3,632.21 M | 0.9125 |
| ty-semantic | ty-semantic/VoucherLifeCycle/0 | jit-raw | O0 | O2 | 2,638.41 M | 2,683.34 M | 0.9833 |
| ty-semantic | ty-semantic/VoucherLifeCycle/1 | jit-raw | O0 | O1 | 142.72 M | 139.33 M | 1.0243 |
| ty-semantic | ty-semantic/VoucherLifeCycle/2 | jit-raw | O0 | O1 | 31.29 M | 33.94 M | 0.9219 |
| ty-semantic | ty-semantic/VoucherLifeCycle/3 | jit-raw | O0 | O1 | 81.22 M | 69.98 M | 1.1606 |
| ty-semantic | ty-semantic/clean/0 | jit-raw | O0 | O2 | 1,949.75 M | 2,188.40 M | 0.8909 |
| ty-semantic | ty-semantic/clean/1 | jit-raw | O0 | O1 | 80.98 M | 83.39 M | 0.9711 |
| ty-semantic | ty-semantic/clean/2 | jit-raw | O0 | O1 | 12.23 M | 11.14 M | 1.0976 |
| ty-semantic | ty-semantic/clean/3 | jit-raw | O0 | O1 | 2.58 M | 2.76 M | 0.9331 |
| ty-semantic | ty-semantic/clean/4 | jit-raw | O0 | O1 | 13.61 M | 14.84 M | 0.9169 |
| ty-semantic | ty-semantic/clean/5 | jit-raw | O0 | O1 | 31.60 M | 34.60 M | 0.9131 |
| ty-semantic | ty-semantic/dijkstra-mutex_LSpec-model/0 | jit-raw | O0 | O2 | 8,103.24 M | 8,641.92 M | 0.9377 |
| ty-semantic | ty-semantic/kvstore/0 | jit-raw | O0 | O2 | 4,786.04 M | 5,099.59 M | 0.9385 |
| ty-semantic | ty-semantic/nbacc_ray97/0 | jit-raw | O0 | O2 | 4,026.14 M | 4,207.92 M | 0.9568 |
| ty-semantic | ty-semantic/nbacg_guer01/0 | jit-raw | O0 | O2 | 7,308.28 M | 7,839.28 M | 0.9323 |
| ty-semantic | ty-semantic/stages/0 | jit-raw | O0 | O2 | 2,637.07 M | 2,966.11 M | 0.8891 |
