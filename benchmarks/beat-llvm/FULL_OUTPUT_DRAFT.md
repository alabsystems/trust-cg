# Complete output checks for three original kernels

This bounded diagnostic originated on
`c84d39e930b1030794a61a6e37abefc95fcf1532` and has been merged with the current
harness. The original manifest and all six supported fixture bytes still match.
The pure Python controls have been executed; they launch no compiler or kernel.
A native attempt now records
three repeated LLVM/Clang baseline agreements for each kernel. TrustCG refuses
proof promotion, so all three rows remain incomplete and three-lane native
qualification remains open.
Production proof gates, the original fixtures, `run.py`, and its timing and
coverage rules are unchanged. This draft grants no formal or superiority credit.

## Why another output check is needed

The actual original fixtures compute unsigned checksums and call
`process::exit((code % 126) as i32)`. In `run.py`, `run_bin` discards stdout and
stderr (line 664); `runtime_lane` checks repeated exit codes (line 669), and the
manifest check compares the LLVM O3 exit with the expected residue (line 840).
`bench_program` compares those residues across lanes (line 917). A result changed
by 126 can pass this comparison. Equal XOR checksums can also conceal different
struct fields. These paths establish residue agreement, not full functional
correctness.

The existing `progs_c/` directory contains 14 C ports of the 18 manifest rows.
Their termination statements also fold the result modulo 126. The separate
`run_gcc_baseline.sh` uses an x86_64 macOS target and native ISA flags, has no
backend freshness check, and explicitly disables proof certificates. Its plain
benchmark invocation follows `set -e`, so an expected nonzero benchmark exit can
terminate the script before the following `$?` assignment. That harness supplies
source material; its historical claims do not qualify this draft.

## Bounded source and output scope

| Original row | Unchanged iteration count | Complete final kernel state |
| --- | ---: | --- |
| `p1_xorshift` | 400,000,000 | RNG `x` and accumulator `acc` |
| `p3_gcd` | 4,000,000 | LCG `s` and accumulator `acc` |
| `p5_struct_acc` | 300,000,000 | Each of `st.a`, `st.b`, `st.c` |

`full_output.py` binds the exact manifest and the six actual Rust/C fixture
bytes by SHA-256. It replaces only their output functions and final termination
statements when writing separate validation clones. The existing kernels,
initial values, iteration bounds, and intermediate operations remain unchanged.
The source controls compare the original main body before the final output
statement with the generated body. They also reject any fixture or manifest
drift rather than creating a different benchmark denominator.

The actual C source uses `uint64_t` throughout these three kernels. Addition
and multiplication wrap modulo 2^64, matching the explicit Rust wrapping
operations. The xorshift shifts are 13, 7, and 17, and every GCD division tests
its divisor for zero first. The struct rotation is fixed at 9, so its C shifts
of 9 and 55 are both defined. The loop counters stay below their fixed bounds.
This source review provides the rationale for reusing the existing C ports;
finite native baseline observations are recorded in the report; source-semantics
and three-lane qualification remain open.

The output is exactly one ASCII line with named, lowercase, 16-digit hexadecimal
fields. Seven known unsigned transport values include zero, both sides of the
32-bit boundary, the signed 64-bit boundary, and all ones. The complete final
state follows them. The reader requires empty stderr, exact field order, normal
exit, the original manifest residue, and a residue matching the full decoded
state. LLVM, Trust-CG, and Clang must agree on every field in at least three
repeats. State arrays and struct fields are never reduced to a comparison
checksum.

All 18 original manifest rows remain in every report. The other 15 carry
`UNSUPPORTED` and a specific missing output/semantic scope. They do not enter
the supported count. Each row retains all three named lanes. Compiler refusal,
missing execution, signal, and timeout retain raw outcomes and remain
`INCOMPLETE`; observed malformed output or differing complete state is
`MISMATCH`. The runner reports no compile time, runtime, RSS, speed ratio, or
performance gate result.

## Tool and artifact custody

`run_full_output.py` reuses the repository's actual Trust package resolver and
backend freshness resolver. Rust compilation names the resolved `trustc` and
uses the existing explicit unverified frontend lane (`-Ztrust-verify=off`).
Backend proof checking retains its default policy. No backend proof bypass,
stale override, stock compiler, or injected `TCG_*`/`TRUST_CG_*` control is
admitted. Clang must be an explicit absolute executable identifying itself as
Clang. All lanes use the same declared native target. Rust uses the resolved compiler's
native default without an explicit `--target`; the optional target argument only
checks that identity. Only little-endian
64-bit x86_64 or AArch64 Linux/macOS hosts are in this draft's scope.

The report retains compiler, backend, helper, fixture, validation source, binary,
command, and raw output hashes. Before and after compilation/execution it checks
the selected compiler/backend, validation source, and exact binary bytes.
These are file snapshots, not proof of loaded-library or runtime environment
immutability. Default CPU/ISA parity, frontend/source adequacy, linked standard
libraries, effective target features, native ABI transport, and actual host
qualification remain required. The report explicitly sets
`isa_parity_qualified`, `formal_credit`, `superiority_eligible`,
`full_original_corpus_qualified`, and `original_timed_binary_qualified` to false.

Run the pure control suite with `python3 -B -m unittest -v test_full_output.py`
from this directory; it mocks subprocess operations and launches no compiler or benchmark. Before
the first build in the selected project, run `aterm help rust` as required by
the user's AGENTS instructions. Then invoke the diagnostic runner with explicit
Trust and Clang identities and a new capture directory. That execution will
create three compilation lanes for each supported kernel. Refusal is a retained
outcome. Success means finite agreement for those exact generated artifacts;
it does not prove all inputs, all 18 programs, or a compiler theorem.

## Exact binary boundary for future timing

The generated validation clones and original timed programs have different
source and binary identities. A passing clone must never qualify an original
`run.py` binary. The original timing artifacts remain exit-only and unqualified
for complete output correctness.

A future timing integration must satisfy all of these requirements before a
performance row counts:

1. Retain the full source, compiler and backend hashes, flags, declared/effective
   target, linked runtime, relevant environment, and output binary identity.
2. Qualify the **same binary bytes** that will be timed. Run complete output
   checks on those artifacts outside the measured compile interval. Reuse those
   bytes for runtime measurements; recheck identity before and after each run.
3. If compile-time measurements build several artifacts, qualify each measured
   compilation's actual output. A separately rebuilt artifact, a last successful
   build, or a validation clone cannot stand in for other measured outputs.
4. If complete-state output is added to the timed corpus, version that source
   and measurement contract explicitly. Keep the original kernel work and
   iteration counts. Account for its output and runtime overhead; the present
   original timings cannot be relabeled as measurements of the changed program.
5. Keep all 18 rows and all refusal/timeout/mismatch outcomes. Complete the 15
   unsupported output scopes before claiming full original-corpus correctness.
6. Qualify LLVM/CG/Clang target and ISA parity, actual frontend and native ABI
   transport, production certificates, and machine/environment suitability.
   Source or executable hashes alone do not discharge those obligations.

This draft does not change the timing contract or implement that future admission
transaction. Original goal H remains open until exact-artifact correctness,
production proof qualification, complete corpus accounting, and actual
performance measurements all pass.

## Pure controls and remaining qualification

Thirteen control groups cover the original denominator, fixture/manifest drift,
kernel preservation, unsigned high bits, strict parsing and exit status,
same-residue wrong results, XOR collisions, nonreturned final state, incomplete
lanes/repeats, nondeterminism, timeouts/launch failures, unchanged proof policy,
retained CG refusal, and binary/source mutation. Mocked positive tuples are test
data. They are not observed benchmark results. No golden full-state tuples have
been fabricated.

Observed disagreement remains `MISMATCH` even when a different lane refuses or
a repeat later times out. Missing evidence alone remains `INCOMPLETE`. Neither
case can earn complete-state agreement or performance credit.
