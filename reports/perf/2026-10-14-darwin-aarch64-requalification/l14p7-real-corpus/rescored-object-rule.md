# Re-scored under the round-1 library rules: `7fe6e3c25532-20261014T180158Z.json`

Computed from the retained samples by `commands/rescore_object_rule.py`; nothing was re-measured. The run stays not evidence: 27 of 62 rows started or ended LOADED (1-min load above 8.0).

| row | lane | as run | re-scored | why |
| --- | --- | --- | --- | --- |
| crate/either-1.18.0 | bridge | COMPILED | ERROR | the compile exited 0 without a readable object |
| crate/either-1.18.0 | diagnostic | COMPILED | ERROR | the compile exited 0 without a readable object |
| crate/fnv-1.0.7 | bridge | COMPILED | ERROR | the compile exited 0 without a readable object |
| crate/fnv-1.0.7 | diagnostic | COMPILED | ERROR | the compile exited 0 without a readable object |
| crate/rustc-hash-2.1.2 | bridge | COMPILED | ERROR | the compile exited 0 without a readable object |
| crate/rustc-hash-2.1.2 | diagnostic | COMPILED | ERROR | the compile exited 0 without a readable object |
| crate/scopeguard-1.2.0 | bridge | COMPILED | ERROR | the compile exited 0 without a readable object |
| crate/scopeguard-1.2.0 | diagnostic | COMPILED | ERROR | the compile exited 0 without a readable object |

Vacuous rows (LLVM's `-O3` object holds no code): `crate/either-1.18.0`, `crate/fnv-1.0.7`, `crate/rustc-hash-2.1.2`, `crate/scopeguard-1.2.0`, `crate/unicode-ident-1.0.24`

## bridge lane: 1 of 62 rows completed (1.6%), 0 with code (0.0%)

| outcome | rows |
| --- | ---: |
| COMPILED | 1 |
| INCOMPLETE | 56 |
| TIMEOUT | 1 |
| ERROR | 4 |

| kind | rows | completed | % |
| --- | ---: | ---: | ---: |
| real-program | 13 | 0 | 0.0 |
| real-crate | 27 | 1 | 3.7 |
| trust-sysroot | 2 | 0 | 0.0 |
| scale-ladder | 20 | 0 | 0.0 |

| ratio vs LLVM (completed rows) | geomean | worst | rows |
| --- | ---: | ---: | ---: |
| compile_cpu_s | 1.556 | 1.556 | 1 |
| compile_instructions | 1.172 | 1.172 | 1 |
| compile_maxrss_bytes | 1.208 | 1.208 | 1 |
| compile_wall_s | 1.051 | 1.051 | 1 |

## diagnostic lane: 42 of 62 rows completed (67.7%), 41 with code (66.1%)

| outcome | rows |
| --- | ---: |
| MATCH | 33 |
| COMPILED | 9 |
| INCOMPLETE | 16 |
| ERROR | 4 |

| kind | rows | completed | % |
| --- | ---: | ---: | ---: |
| real-program | 13 | 13 | 100.0 |
| real-crate | 27 | 8 | 29.6 |
| trust-sysroot | 2 | 1 | 50.0 |
| scale-ladder | 20 | 20 | 100.0 |

| ratio vs LLVM (completed rows) | geomean | worst | rows |
| --- | ---: | ---: | ---: |
| code_bytes | 4.902 | 75.765 | 8 |
| compile_cpu_s | 1.961 | 26.387 | 42 |
| compile_instructions | 1.449 | 8.847 | 42 |
| compile_maxrss_bytes | 1.208 | 1.293 | 42 |
| compile_wall_s | 1.352 | 30.142 | 42 |
| runtime_cycles | 1.011 | 1.348 | 33 |
| runtime_instructions | 1.008 | 1.177 | 33 |
| runtime_maxrss_bytes | 1.013 | 1.281 | 33 |
| runtime_wall_s | 1.000 | 1.113 | 33 |
