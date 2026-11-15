# L02-P13 closure record — Linux AArch64, third closure audit and LD-74 re-check (2026-10-23)

**Claim.** Closure-ledger gap L02-P13 (the LLVM text importer dropped
function visibility and link-once linkage: a hidden LLVM function was
exported and preemptible, a `linkonce_odr` one became a strong definition) is
CLOSED at `d4181873f` under ruling LD-74:

1. the third closure audit at `e0474f6ce` (2026-10-16): the auditor and
   skeptic 2 said CLOSE; skeptic 1 (coverage lens) said KEEP_PARTIAL on one
   finding, the visibility of non-scalar global definitions pinned by no test
   (mutant S13 survived every importer floor target);
2. that finding was repaired with floor rows only, no product change (LD-85:
   `symbol_linkage_elf` grows from 29 to 31 tests, a host-neutral row over
   520 global definitions of ten initializer shapes and a native
   GNU ld/gold/LLD interposition row), and an independent verifier CONFIRMED
   it (31 mutants killed); it landed in `d4181873f` through the landing train
   (attested 134/134, portable scope);
3. a re-check that takes the blocking skeptic's coverage lens said CLOSE at
   `d4181873f`.

**Boundary.** Execution evidence on one Linux AArch64 host against llc 22
from the Trust sysroot and gcc twins, through GNU ld 2.42, gold 1.16 and LLD
22.1.6. Darwin and x86-64 were not run here. The stated conservative refusals
and documented differences in LIMITATIONS (LD-20 to LD-25, LD-31, llc's
mergeable `.rodata.str1.1` sections) remain as stated.

## Evidence record

```text
Task ID / kind / platform: LA-125 / closure / Linux AArch64
Parent ledger gaps and acceptance row: L02-P13; L02
Input candidate and implementation commit: d4181873f (origin/main); repair LD-85
Compiler, sysroot, dependency pins and backend hash: Trust ae9c2c1d overlay trust-ae9c2c1d-ay13556 (LD-94); trust-ir 89c68b72; Clean d0bf4d54
Required host, prerequisites and dependent task IDs: Linux AArch64; GNU ld, gold, LLD and llc (TCG_REQUIRE_LLD/GOLD/LLC=1)
Smallest failing input / expected behavior: mutant S13 (image globals written with default visibility) must fail a floor target; it does
Completion condition: LD-74 (1)-(3)
Exact commands and fixed denominator: scripts/trust_cargo.sh test -p trust-cg-llvm-import --features driver --test symbol_linkage_elf (31 tests)
Before / after matches, refusals, failures, skips and timeouts: 31/31, no SKIP; importer lib 287/287
Negative or mutation control: the re-check's 75 mutants at every importer visibility, linkage, COMDAT, dso_local, retention and naming site; every behaviour-changing one killed by a floor target
Evidence location and evidence class: this record; logs local provenance only; execution evidence
Remaining limitations and next smallest task: two low, non-blocking coverage notes (below)
Task status / ledger status / acceptance status: DONE / CLOSED d4181873f / L02 OPEN
```

## Re-check (coverage lens) at `d4181873f`

- `symbol_linkage_elf` 31/31 with LLD, gold and llc required and no `SKIP`
  line; the importer library 287/287; the other importer floor targets green
  apart from the three NEON reds origin carries (`ary3_init_o2_e2e`,
  `ary3_reverse_accum_proof_facts`), outside this row.
- 75 mutants: S13 re-derived at `push_image_global` and its three
  visibility variants, one per initializer-shape caller (string, integer
  array, pointer array, serialized aggregate, zero array, named struct zero,
  named struct with fields, `ptr null`), the scalar and declaration sites,
  the function-fact, ODR, COMDAT, dso_local (D01–D16), retention (R01–R07)
  and naming rules. Every one that changes behaviour on LLVM-valid input is
  killed by `symbol_linkage_elf`.
- A probe with shapes outside the floor's table (nested arrays and structs,
  `i1`, float arrays, hidden and protected arrays in named sections, weak
  hidden pointer arrays) gave the same binding, visibility and defined state
  as llc for every symbol.

## Non-blocking notes

- The refusal of a symbol prefix carrying two linkage keywords is pinned only
  by library unit tests (mutant V06); it changes behaviour only on text that
  llc itself rejects.
- Mutant G16 (a provisional linkage passed to `push_image_global`) is
  equivalent: the caller overwrites the field before any read.

The closing criteria rest on the in-tree floor targets, which anyone can
re-run; the reviewers' probes and logs are corroborating local provenance
only (session scratch directory `closure-1023/`).
