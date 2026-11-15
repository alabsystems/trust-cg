revision `7fe6e3c25532` dirty=False load [4.21, 5.57, 7.15] -> [7.92, 6.7, 5.89] (threshold 8.0); eligible=False
  not evidence: 27 of 62 rows started or ended LOADED (1-min load above 8.0)

### bridge: 5 of 62 completed (8.1%)

| outcome | rows |
| --- | ---: |
| COMPILED | 5 |
| INCOMPLETE | 56 |
| TIMEOUT | 1 |

| kind | rows | completed | % |
| --- | ---: | ---: | ---: |
| real-crate | 27 | 5 | 18.5 |
| real-program | 13 | 0 | 0.0 |
| scale-ladder | 20 | 0 | 0.0 |
| trust-sysroot | 2 | 0 | 0.0 |

refused rows by code: `[TCG-ARG-ABI]` 2, `[TCG-BOX-PAYLOAD-DROP]` 1, `[TCG-COLLECTION-IMAGE]` 6, `[TCG-FAT-POINTEE-LANE]` 1, `[TCG-FMT-DECLINED]` 2, `[TCG-IR-LOWER]` 2, `[TCG-ITER-UNMODELED]` 2, `[TCG-MIR-UNSUPPORTED]` 56, `[TCG-OWNING-ITER-METHOD]` 3, `[TCG-POINTEE-LANES]` 5, `[TCG-PROOF-465]` 56, `[TCG-PROVENANCE-XCHECK-FAIL]` 2, `[TCG-REGALLOC-063]` 4, `[TCG-RET-ABI]` 2, `[TCG-RET-UNBOUND]` 1, `[TCG-SRET-ABI]` 2, `[TCG-STEPBY-OPT-LEVEL]` 1

| ratio vs LLVM over completed rows | geomean | worst | rows | missing |
| --- | ---: | ---: | ---: | --- |
| code_bytes | - | - | 5 | crate/either-1.18.0, crate/fnv-1.0.7, crate/rustc-hash-2.1.2, crate/scopeguard-1.2.0, crate/unicode-ident-1.0.24 |
| compile_cpu_s | 1.519 | 1.556 | 5 | - |
| compile_instructions | 1.164 | 1.172 | 5 | - |
| compile_maxrss_bytes | 1.126 | 1.208 | 5 | - |
| compile_wall_s | 0.993 | 1.051 | 5 | - |

### diagnostic: 46 of 62 completed (74.2%)

| outcome | rows |
| --- | ---: |
| COMPILED | 13 |
| INCOMPLETE | 16 |
| MATCH | 33 |

| kind | rows | completed | % |
| --- | ---: | ---: | ---: |
| real-crate | 27 | 12 | 44.4 |
| real-program | 13 | 13 | 100.0 |
| scale-ladder | 20 | 20 | 100.0 |
| trust-sysroot | 2 | 1 | 50.0 |

refused rows by code: `[TCG-ARG-ABI]` 2, `[TCG-BOX-PAYLOAD-DROP]` 1, `[TCG-COLLECTION-IMAGE]` 6, `[TCG-FAT-POINTEE-LANE]` 1, `[TCG-FMT-DECLINED]` 2, `[TCG-IR-LOWER]` 2, `[TCG-ITER-UNMODELED]` 2, `[TCG-MIR-UNSUPPORTED]` 16, `[TCG-OWNING-ITER-METHOD]` 3, `[TCG-POINTEE-LANES]` 5, `[TCG-RET-ABI]` 2, `[TCG-SRET-ABI]` 2, `[TCG-STEPBY-OPT-LEVEL]` 1

| ratio vs LLVM over completed rows | geomean | worst | rows | missing |
| --- | ---: | ---: | ---: | --- |
| code_bytes | - | - | 13 | crate/either-1.18.0, crate/fnv-1.0.7, crate/rustc-hash-2.1.2, crate/scopeguard-1.2.0, crate/unicode-ident-1.0.24 |
| compile_cpu_s | 1.914 | 26.387 | 46 | - |
| compile_instructions | 1.419 | 8.847 | 46 | - |
| compile_maxrss_bytes | 1.190 | 1.293 | 46 | - |
| compile_wall_s | 1.314 | 30.142 | 46 | - |
| runtime_cycles | 1.011 | 1.348 | 33 | - |
| runtime_instructions | 1.008 | 1.177 | 33 | - |
| runtime_maxrss_bytes | 1.013 | 1.281 | 33 | - |
| runtime_wall_s | 1.000 | 1.113 | 33 | - |

| row | lines | LLVM compile s | production outcome | production s (refusal, or median) | codes | diagnostic | diag compile x | diag instr x | diag runtime cycles x | code bytes LLVM / production / diagnostic |
| --- | ---: | ---: | --- | ---: | --- | --- | ---: | ---: | ---: | --- |
| real-program/p01_interp | 26 | 0.337 | INCOMPLETE | 1.459 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.029 | 1.204 | 0.916 |  |
| real-program/p02_sort_vec | 31 | 0.352 | INCOMPLETE | 8.391 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.024 | 1.189 | 1.016 |  |
| real-program/p03_tokenizer | 36 | 0.350 | INCOMPLETE | 1.493 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.025 | 1.210 | 1.069 |  |
| real-program/p04_matmul | 43 | 0.359 | INCOMPLETE | 1.478 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 TCG-REGALLOC-063 | MATCH | 0.984 | 1.169 | 1.044 |  |
| real-program/p05_state_machine | 43 | 0.344 | INCOMPLETE | 5.423 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.004 | 1.208 | 0.971 |  |
| real-program/p06_rdp | 54 | 0.353 | INCOMPLETE | 9.375 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.004 | 1.189 | 1.011 |  |
| real-program/p07_wordcount | 32 | 0.334 | INCOMPLETE | 5.379 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.039 | 1.200 | 0.960 |  |
| real-program/p08_fnv_hash | 21 | 0.332 | INCOMPLETE | 1.640 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.006 | 1.193 | 1.008 |  |
| real-program/p09_sieve | 27 | 0.327 | INCOMPLETE | 1.622 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.262 | 1.500 | 0.999 |  |
| real-program/p10_struct_logic | 44 | 0.337 | INCOMPLETE | 4.200 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.051 | 1.224 | 0.995 |  |
| real-program/p11_vec_stack | 32 | 0.327 | INCOMPLETE | 5.286 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.054 | 1.204 | 1.011 |  |
| real-program/p12_box_tree | 35 | 0.329 | INCOMPLETE | 9.315 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.032 | 1.205 | 0.934 |  |
| real-program/p13_sort_std | 21 | 0.385 | INCOMPLETE | 14.349 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 2.682 | 1.841 | 0.943 |  |
| crate/adler2-2.0.1 | 551 | 0.307 | INCOMPLETE | 16.902 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 TCG-REGALLOC-063 | COMPILED | 10.710 | 1.673 | - | 724 / - / 3,756 |
| crate/aho-corasick-1.1.5 | 20,937 | 1.684 | INCOMPLETE | 161.620 | TCG-ARG-ABI TCG-COLLECTION-IMAGE TCG-FMT-DECLINED TCG-MIR-UNSUPPORTED TCG-POINTEE-LANES TCG-PROOF-465 TCG-RET-ABI TCG-SRET-ABI | INCOMPLETE | - | - | - | 94,632 / - / - |
| crate/arrayvec-0.7.8 | 3,535 | 0.353 | INCOMPLETE | 0.512 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | COMPILED | 1.023 | 1.133 | - | 28 / - / 40 |
| crate/bitflags-2.13.1 | 6,351 | 0.387 | INCOMPLETE | 19.234 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | COMPILED | 2.530 | 1.909 | - | 4,236 / - / 18,844 |
| crate/either-1.18.0 | 2,423 | 0.329 | COMPILED | 0.334 |  | COMPILED | 1.010 | 1.123 | - | 0 / - / - |
| crate/fastrand-2.5.0 | 1,512 | 0.348 | INCOMPLETE | 27.402 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | INCOMPLETE | - | - | - | 1,448 / - / - |
| crate/fnv-1.0.7 | 367 | 0.347 | COMPILED | 0.306 |  | COMPILED | 0.866 | 1.143 | - | 0 / - / - |
| crate/foldhash-0.2.0 | 1,128 | 0.373 | INCOMPLETE | 24.341 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | INCOMPLETE | - | - | - | 1,364 / - / - |
| crate/glob-0.3.4 | 1,993 | 0.614 | INCOMPLETE | 74.535 | TCG-COLLECTION-IMAGE TCG-IR-LOWER TCG-MIR-UNSUPPORTED TCG-OWNING-ITER-METHOD TCG-POINTEE-LANES TCG-PROOF-465 | INCOMPLETE | - | - | - | 18,884 / - / - |
| crate/hashbrown-0.15.5 | 23,476 | 0.504 | INCOMPLETE | 80.260 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | INCOMPLETE | - | - | - | 340 / - / - |
| crate/heck-0.5.0 | 864 | 0.652 | INCOMPLETE | 18.937 | TCG-IR-LOWER TCG-MIR-UNSUPPORTED TCG-OWNING-ITER-METHOD TCG-PROOF-465 | INCOMPLETE | - | - | - | 19,748 / - / - |
| crate/hex-0.4.3 | 817 | 0.342 | INCOMPLETE | 16.453 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | COMPILED | 1.095 | 1.217 | - | 248 / - / 1,556 |
| crate/itoa-1.0.18 | 574 | 0.334 | INCOMPLETE | 17.278 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | COMPILED | 1.820 | 1.467 | - | 2,256 / - / 5,972 |
| crate/memchr-2.8.3 | 15,824 | 0.542 | INCOMPLETE | 72.759 | TCG-ARG-ABI TCG-MIR-UNSUPPORTED TCG-PROOF-465 TCG-PROVENANCE-XCHECK-FAIL | INCOMPLETE | - | - | - | 8,672 / - / - |
| crate/minimal-lexical-0.2.1 | 7,718 | 0.366 | INCOMPLETE | 115.574 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | INCOMPLETE | - | - | - | 1,916 / - / - |
| crate/percent-encoding-2.3.2 | 694 | 0.336 | INCOMPLETE | 20.242 | TCG-COLLECTION-IMAGE TCG-MIR-UNSUPPORTED TCG-PROOF-465 TCG-PROVENANCE-XCHECK-FAIL | INCOMPLETE | - | - | - | 2,892 / - / - |
| crate/regex-syntax-0.8.11 | 58,528 | 2.823 | INCOMPLETE | 548.731 | TCG-BOX-PAYLOAD-DROP TCG-COLLECTION-IMAGE TCG-FAT-POINTEE-LANE TCG-FMT-DECLINED TCG-ITER-UNMODELED TCG-MIR-UNSUPPORTED TCG-OWNING-ITER-METHOD TCG-POINTEE-LANES TCG-PROOF-465 TCG-REGALLOC-063 TCG-RET-ABI TCG-SRET-ABI | INCOMPLETE | - | - | - | 182,352 / - / - |
| crate/rustc-hash-2.1.2 | 675 | 0.294 | COMPILED | 0.298 |  | COMPILED | 1.010 | 1.141 | - | 0 / - / - |
| crate/same-file-1.0.6 | 950 | 0.304 | INCOMPLETE | 16.492 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | INCOMPLETE | - | - | - | 824 / - / - |
| crate/scopeguard-1.2.0 | 624 | 0.286 | COMPILED | 0.290 |  | COMPILED | 1.004 | 1.142 | - | 0 / - / - |
| crate/siphasher-1.0.3 | 1,794 | 0.321 | INCOMPLETE | 22.852 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | COMPILED | 30.142 | 8.847 | - | 136 / - / 10,304 |
| crate/smallvec-1.15.2 | 3,822 | 0.348 | INCOMPLETE | 12.558 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | COMPILED | 1.035 | 1.176 | - | 316 / - / 872 |
| crate/strsim-0.11.1 | 1,473 | 0.543 | INCOMPLETE | 157.240 | TCG-COLLECTION-IMAGE TCG-ITER-UNMODELED TCG-MIR-UNSUPPORTED TCG-POINTEE-LANES TCG-PROOF-465 TCG-RET-UNBOUND TCG-STEPBY-OPT-LEVEL | INCOMPLETE | - | - | - | 14,856 / - / - |
| crate/termcolor-1.4.1 | 2,572 | 0.453 | INCOMPLETE | 123.445 | TCG-COLLECTION-IMAGE TCG-MIR-UNSUPPORTED TCG-POINTEE-LANES TCG-PROOF-465 | INCOMPLETE | - | - | - | 5,676 / - / - |
| crate/unicode-ident-1.0.24 | 2,085 | 0.275 | COMPILED | 0.289 |  | COMPILED | 1.025 | 1.141 | - | 0 / 16 / 16 |
| crate/unicode-segmentation-1.13.3 | 8,961 | 0.467 | INCOMPLETE | 20.386 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | INCOMPLETE | - | - | - | 8,292 / - / - |
| crate/unicode-width-0.2.2 | 23,920 | 0.347 | INCOMPLETE | 12.884 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | INCOMPLETE | - | - | - | 868 / - / - |
| trust-sysroot/core-O0 | 702,865 | 5.139 | TIMEOUT | 3600.013 |  | COMPILED | 8.377 | 4.784 | - | 391,720 / - / 1,141,352 |
| trust-sysroot/core-O3 | 702,865 | 6.571 | INCOMPLETE | 219.823 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 TCG-REGALLOC-063 | INCOMPLETE | - | - | - | 129,808 / - / - |
| ladder/scale_gate/small | 355 | 0.349 | INCOMPLETE | 1.630 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.053 | 1.261 | 0.973 |  |
| ladder/scale_gate/medium | 2,805 | 0.459 | INCOMPLETE | 2.268 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.082 | 1.619 | 1.058 |  |
| ladder/scale_gate/large | 11,205 | 0.866 | INCOMPLETE | 4.455 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.101 | 2.021 | 1.111 |  |
| ladder/scale_gate/xlarge | 33,605 | 2.005 | INCOMPLETE | 10.358 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.091 | 2.234 | 1.348 |  |
| ladder/compile-scaling/blocks-100 | 104 | 0.341 | INCOMPLETE | 1.530 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.039 | 1.187 | 0.980 |  |
| ladder/compile-scaling/blocks-200 | 204 | 0.351 | INCOMPLETE | 1.587 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.047 | 1.207 | 1.061 |  |
| ladder/compile-scaling/blocks-400 | 404 | 0.384 | INCOMPLETE | 1.612 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.054 | 1.278 | 0.980 |  |
| ladder/compile-scaling/blocks-800 | 804 | 0.474 | INCOMPLETE | 1.744 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.116 | 1.592 | 1.016 |  |
| ladder/compile-scaling/loops-15 | 64 | 0.342 | INCOMPLETE | 1.897 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.093 | 1.255 | 1.011 |  |
| ladder/compile-scaling/loops-30 | 124 | 0.363 | INCOMPLETE | 2.021 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.141 | 1.343 | 0.989 |  |
| ladder/compile-scaling/loops-60 | 244 | 0.404 | INCOMPLETE | 2.154 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.253 | 1.572 | 1.014 |  |
| ladder/compile-scaling/loops-120 | 484 | 0.480 | INCOMPLETE | 2.641 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.687 | 2.161 | 0.997 |  |
| ladder/compile-scaling/funcs-50 | 52 | 0.356 | INCOMPLETE | 1.465 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 0.988 | 1.203 | 0.955 |  |
| ladder/compile-scaling/funcs-100 | 102 | 0.360 | INCOMPLETE | 1.517 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.002 | 1.225 | 1.025 |  |
| ladder/compile-scaling/funcs-200 | 202 | 0.403 | INCOMPLETE | 1.701 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 0.992 | 1.257 | 1.001 |  |
| ladder/compile-scaling/funcs-400 | 402 | 0.470 | INCOMPLETE | 1.903 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 0.931 | 1.302 | 0.971 |  |
| ladder/compile-scaling/arraysize-4096 | 15 | 0.322 | INCOMPLETE | 1.652 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.062 | 1.202 | 0.943 |  |
| ladder/compile-scaling/arraysize-16384 | 15 | 0.332 | INCOMPLETE | 1.659 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.049 | 1.201 | 1.093 |  |
| ladder/compile-scaling/arraysize-65536 | 15 | 0.334 | INCOMPLETE | 1.673 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.028 | 1.202 | 0.990 |  |
| ladder/compile-scaling/arraysize-262144 | 15 | 0.332 | INCOMPLETE | 1.662 | TCG-MIR-UNSUPPORTED TCG-PROOF-465 | MATCH | 1.024 | 1.202 | 1.052 |  |

production COMPILED rows whose LLVM object holds no code (vacuous): ['crate/either-1.18.0', 'crate/fnv-1.0.7', 'crate/rustc-hash-2.1.2', 'crate/scopeguard-1.2.0', 'crate/unicode-ident-1.0.24']
