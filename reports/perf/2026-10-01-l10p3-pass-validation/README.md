# L10-P3 per-pass validation: cost and calibration on the compile corpus

Date: 2026-10-01 · Host: Apple M4 Max, macOS, shared with other work · Branch:
`w14/aarch64-per-pass-validation-L10-P3` · Corpus:
[benchmarks/compile-corpus](../../../benchmarks/compile-corpus/README.md), 247
modules, 534 (entry, lane) pairs.

Commands: [commands/measure.sh](commands/measure.sh) runs every arm with one
release `compile_corpus` binary, and
[commands/aggregate.py](commands/aggregate.py) aggregates the calibration log
by pass, validator and verdict. The payloads stay out of tree (`.gitignore`,
durable evidence policy). Identities at `ec6c90504`: the calibration log
(89,939,009 bytes) has SHA-256
`21a681c4d57f456a7e709be5f2c8b36d0eb4752b42144f67cff53dce41220628`, and its
aggregate `verdicts-all.tsv` has SHA-256
`425729e2ec67be43c2298eeb4999165b04f1b90ad593be43d574ae780faead94`. The
tables below come from that aggregate. Instructions retired are the
steady-state repetition that `run.py compare` reports. They hold up under the
shared host's load; cycles do not.

## Cost (instructions retired, validation on against off, same binary)

`run.py compare` reported **Identity: PASS** for every arm against `off`: the
same verdicts, error texts, emitted-code digests and frame-net counters on
all 534 pairs, every repetition. So validation changed no emitted byte.

The script ran twice. At `bc4be093d` the load average was 8.4 to 13.2. At
`ec6c90504` (adds the exception-edge and dominating-move checks) it was 39
to 64, with a Darwin floor running alongside.

| lane | default tier (schedulers, diagnostic) | dedicated tier |
|---|--:|--:|
| `aot-object` | +0.80% / +0.62% | +8.03% / +8.02% |
| `jit-raw` | +0.48% / +0.47% | +5.03% / +5.12% |
| `jit-raw-checked` | +0.52% / +0.49% | +5.39% / +5.45% |
| `aot-proofs` (rustc bridge, proof grade) | +8.56% as shipped (`bc4be093d`) | +8.56% |

Each cell gives `bc4be093d` / `ec6c90504`.

The `aot-proofs` lane is the rustc bridge's default route. The bridge emits
proof certificates unless told not to, so `Compiler` makes the pipeline proof
grade, and `Pipeline::pass_validation_config` raises every proof-grade
pipeline to the dedicated tier with `enforce`. The control cannot lower that,
so `TRUST_CG_PASS_VALIDATION=off` is not "no validation" on this lane, and the
main arms show no difference there (0.9985 to 0.9995). Its cost was measured
with a probe build: `bc4be093d` plus a temporary environment check that
skipped only the proof-grade raise, never committed. The probe compared the
raise skipped with validation off against the same binary as shipped, and
went from 19,590.9 M to 21,267.4 M instructions (+8.56%). The probe binary
was used only for this row.

## Calibration (`TRUST_CG_PASS_VALIDATION_SCOPE=all`, reps 1, every lane, `ec6c90504`)

Every pass is validated: the dedicated validator where there is one,
otherwise the generic symbolic region check, plus an unchanged-claim check on
every run that reported no change. This is not a cost arm, because the log
writes dominate it.

| group | validated | unproved | refuted | uncovered |
|---|--:|--:|--:|--:|
| dedicated validators (changed runs) | 10,183 | 0 | 0 | — |
| generic region check (changed runs of the other passes) | 46,405 | 34,664 | 0 | — |
| unchanged-claim checks | 954,646 | — | 3 | — |
| no validator at all | — | — | — | 9,533 |

- Dedicated: `pressure-aware-scheduler` 5,513, `mem-pair-formation` 2,968,
  `licm` 1,523, `instruction-scheduler` 176 and `if-convert` 3. None was
  refuted or unproved. `late-boolean-diamond` and `tiny-loop-diamond`
  changed nothing on this corpus.
- Generic: 57.2% of the other passes' changed runs validated. That is nearly
  all of `dce`, `cfg-simplify`, `declarative-rewrite`, `addr-mode`,
  `cmp-branch-fusion`, `shift-alu-fuse` and `const-fold`, and a minority of
  `copy-prop`, `cse`, `gvn` and `sroa`, whose cross-block value equalities
  are not modeled. No loop restructuring, vectorizer, `rotate-idiom` or
  `tail-call` run validated. Their unproved verdicts are expected from this
  check and are not findings. Modeling exception edges added 15 validated
  `copy-prop` and `dce` runs over `bc4be093d`.
- The three unchanged-claim refutations are `scalar-unroll` runs that
  normalize constant trip guards and then report no change. The CHANGELOG
  documents them; they are recorded, not changed.
- No validator: `branch-layout` 8,640 (post-allocation layout) and
  `extended-loop-rotation` 893 (outside the pass manager).

Strength: translation validation of each run under the validators' machine
model. It is not a proof of any pass.

## Re-check after merging main (`c48a01e49`, 2026-10-06)

The branch merged `origin/main` at `2ac5b7620` (main's OD-127 LICM and
pairing changes included), and the hoist validator gained the exception-edge,
bounded-slot and repeating-preheader conditions. One release `compile_corpus`
binary at `c48a01e49` (SHA-256
`9b5a094b6300410b03453ff7bcbd96d730da85146184c93cad56206d276a79c9`) ran the
arms of [commands/measure.sh](commands/measure.sh). The load average was 48
to 85, with other work and a Darwin floor running.

| lane | default tier | dedicated tier |
|---|--:|--:|
| `aot-object` | +0.47% | +7.84% |
| `jit-raw` | +0.59% | +5.17% |
| `jit-raw-checked` | +0.66% | +5.56% |
| `aot-proofs` (proof grade, always dedicated) | 0.9973 | 0.9970 |

Steady-state instructions retired, reps 3, validation on against off, same
binary. `run.py compare` reported **Identity: PASS** for both arms on all 534
pairs.

Calibration of the dedicated scope (`TRUST_CG_PASS_VALIDATION_SCOPE=dedicated`
with the log, reps 1, every lane): 10,505 changed dedicated runs validated,
none refuted or unproved. By pass: `pressure-aware-scheduler` 5,577,
`mem-pair-formation` 2,975, `licm` 1,773, `instruction-scheduler` 176,
`if-convert` 4. There were 92,074 unchanged-claim checks, all validated. The
log (14,029,214 bytes) has SHA-256
`52c53ffe494454748e2921b866cba2c89c3f2d6cf6be548a7f752fa10e393467`, and its
aggregate has SHA-256
`1a44de31f1233a6bc891255ef0141b139ec2be8d3fcfdcd518fa83e5360f13eb`. The
logging arm is not a cost arm.

Against validation off it also reported **Identity: PASS**. The corpus's
failing compiles are therefore the same with validation off; most are
`aot-proofs` proof-promotion refusals. None names a pass validation.

