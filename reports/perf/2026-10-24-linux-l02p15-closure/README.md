# L02-P15 closure record — Linux AArch64, third closure audit and seven LD-74 re-checks (2026-10-24)

**Claim.** Closure-ledger gap L02-P15 (the LLVM text importer admits LLVM
text whose meaning it does not read) is CLOSED at `99943e348` under ruling
LD-74:

1. the third closure audit at `9a237122b` (2026-10-23): the auditor and
   skeptic 2 said CLOSE; skeptic 1 (differential lens) said KEEP_PARTIAL on
   one finding, `nobuiltin` and the `no-builtin*` attributes admitted while
   the backend expanded `memcpy`/`memset` inline;
2. that finding was repaired (LD-97, with LD-98) and independently verified;
3. re-checks taking skeptic 1's lens then found six further defects of one
   family, a call lowered with a signature or ABI llc would not use, each
   repaired by name and independently verified before the next re-check
   (LD-100 rules 1–12, below), and the seventh re-check said CLOSE at
   `99943e348`.

**Boundary.** Differential testing against llc 22.1.2 on one Linux AArch64
host (O0–O3; GNU ld, gold and LLD; static and PIE), not a proof. Darwin and
x86-64 objects were not run. The stated over-refusals and the differences
LLVM's LangRef permits (a plain C99-prototype call of `memcpy`, `memmove` or
`memset` expanded where llc keeps the call, LD-16 as corrected; the
`available_externally` body inlined at O1–O3; `llvm.objectsize` answering
-1; unresolved weak symbols called without a null test, which is undefined
behaviour) remain as stated in LD-16, LD-100 and LIMITATIONS.

## The re-check sequence

| Re-check | Head | Finding (all high, wrong code, measured 0 of 24 equal to llc) | Repair |
| --- | --- | --- | --- |
| 1 | `ff895a9be` | the adapter lowered any call named `memcpy`, `memmove` or `memset` as the routine by name alone | LD-100 rules 1–7: C-prototype gate in one decision (`classify_direct_call`), with the fsym and SROA readers |
| 2 | `f95ca7609` | an unprototyped `(...)` declaration took its calls' C type (OD-56) and passed the gate | rule 8: headers of routine names refused unless the module's own and modelled |
| 3 | `f37c48df9` | a call stating another type than its header (a call through a cast) was expanded | rule 9: every direct call's stated type must equal its callee's signature |
| 4 | `469ad7904` (verifier) | a libm intrinsic renamed to its C symbol was typed by the module's header of that symbol | rule 10: the renamed call is recorded at the intrinsic's type and compared |
| 5 | `848a8638d` | a hidden-buffer declaration of a runtime name gave the backend's own `memcpy` call its convention | rule 11: AArch64 selection refuses an `sret` callee named like a backend runtime routine |
| 6 | `f8e524bc9` | the weak-call rewrite dropped an `extern_weak` callee's hidden buffer (and weak intrinsics) | rule 12: such weak calls refused by name; a sweep of every importer rewrite against every ABI fact |
| 7 | `99943e348` | none in scope | CLOSE |

## Evidence record

```text
Task ID / kind / platform: LA-173 / closure / Linux AArch64
Parent ledger gaps and acceptance row: L02-P15; L02
Input candidate and implementation commit: 99943e348 (rule 12 on top of land/linux-20261024b)
Compiler, sysroot, dependency pins and backend hash: Trust ae9c2c1d overlay trust-ae9c2c1d-ay13556 (LD-94); llc 22.1.2 from the Trust sysroot
Required host, prerequisites and dependent task IDs: Linux AArch64; GNU ld, gold, LLD and llc (TCG_REQUIRE_LLD/GOLD/LLC=1)
Smallest failing input / expected behavior: each row's reproducers above are refused by name or run equal to llc
Completion condition: LD-74 (1)-(3), with the blocking lens re-checked until CLOSE
Exact commands and fixed denominator: scripts/trust_cargo.sh test -p trust-cg-llvm-import --features driver (460 tests) and -p trust-cg-lower --lib --test '*' (2,900)
Before / after matches, refusals, failures, skips and timeouts: importer 460/0, lower 2,900/0 at 99943e348
Negative or mutation control: each rule's single-site mutants killed by named tests (9 for rule 12); each rule's new tests fail on its base
Evidence location and evidence class: this record and LD-100's Measured sections; probes and logs local provenance only; differential testing
Remaining limitations and next smallest task: stated over-refusals and LangRef-permitted differences above
Task status / ledger status / acceptance status: DONE / CLOSED 99943e348 / L02 OPEN
```

## The seventh re-check at `99943e348`

- All 15 reported weak-`sret` reproducers refused by name at every
  optimisation level; the base ran each wrong in 0 of 24 configurations.
- A census of 1,295 `extern_weak` modules, base against head: 93 newly
  refused (54 distinct), all by rule 12; none newly admitted; of the 54, 31
  ran wrong at the base, 4 ran alike (the stated over-refusals).
- 318 new differential probes: 302 equal to llc in 24 of 24 and 5 refused by
  name; the other 11 behave the same at base and head and are differences
  of llc (a speculated weak call or libcall ahead of its null test, an `i32`
  count passed with dirty upper bits) or undefined behaviour.
- 887 earlier reproducers re-run: each equal, refused, or a recorded
  difference.

The closing criteria rest on the in-tree importer and lowering tests, which
anyone can re-run; the reviewers' probe corpora and logs are corroborating
local provenance only (session scratch directories `w1023*`, `rc1023*`,
`proto1023*`, `libm1024`, `rt1024`, `r12`).
