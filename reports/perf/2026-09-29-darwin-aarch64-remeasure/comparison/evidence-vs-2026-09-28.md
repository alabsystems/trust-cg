previous: 2026-09-28-darwin-aarch64-campaign/2026-09-28-01fc13b13608/01fc13b13608-20260928T134336Z.json
current:  2026-09-29-darwin-aarch64-remeasure/2026-09-29-80b0e03aa609-141117Z/80b0e03aa609-20260929T141257Z.json

| aggregate | previous | current |
| --- | ---: | ---: |
| MATCH | 0 | 0 |
| INCOMPLETE | 18 | 18 |
| MISMATCH | 0 | 0 |
| coverage % | 0.0000 | 0.0000 |
| runtime geomean x -O3 | null | null |
| runtime, resolvable rows x -O3 | null | null |
| resolvable rows | 0 | 0 |
| scalar runtime x -O3 | null | null |
| worst runtime x -O3 | null | null |
| warm compile x -O2 | null | null |
| warm compile x -O3 | null | null |
| cold compile x -O2 | null | null |
| linked size x -O3 | null | null |
| worst linked size x -O3 | null | null |
| program peak RSS x -O3 | null | null |
| floor-bound programs | null | null |
| compiler peak RSS x -O2 | null | null |
| compiler peak RSS x -O3 | null | null |

| category | previous x -O3 | current x -O3 |
| --- | ---: | ---: |
| branch | null | null |
| heap | null | null |
| multifn | null | null |
| scalar | null | null |
| vectorizable | null | null |

| program | verdict prev/cur | LLVM -O3 run s prev/cur | bridge run s prev/cur | runtime x prev -> cur | bridge rel_spread prev/cur | warm x -O2 prev -> cur | cold x -O2 prev -> cur | size x prev -> cur | compiler RSS x -O2 prev -> cur |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| b1_mispredict | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| h1_vec_push_sum | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| h2_vec_grow | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| h3_box_leak | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| h4_vec_dropper | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| m1_call_chain | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| m2_call_heavy | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p1_xorshift | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p2_collatz | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p3_gcd | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p4_matmul | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p5_struct_acc | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p6_branch_match | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p7_sieve | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| p8_closure_nest | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| v1_saxpy | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| v2_memfill | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
| v3_popcount | INCOMPLETE/INCOMPLETE | null/null | null/null | null -> null | -/- | null -> null | null -> null | null -> null | null -> null |
