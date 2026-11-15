# x86 if-conversion, measured for the first time: worth 44% on b1 and 47% on p2

Host AMD Ryzen 9 9900X3D, x86-64 Linux, `-Copt-level=3`, 90 interleaved rounds,
`taskset -c 2`, min statistic, the default arm carried twice as its own floor.

## Why it had never been measured

`X86IfConvert` (OPT-11) and `X86CmovSwap` are both DEFAULT-ON passes that rewrite
hot-loop control flow into `Cmovcc`. Their only kill switches were
`std::env::var_os("TCG_NO_IFCONVERT")` and `std::env::var_os("TCG_NO_X86_CMOV_SWAP")` —
raw environment reads with no tracked twin in `knobs.rs`. `trustc` refuses every `TCG_*`
variable before the backend loads, so through the real driver both passes were
unconditionally on and unmeasurable. That is the same defect this backend has now found
sixteen times.

Both now have tracked opt-outs, `no-x86-ifconvert` and `no-x86-cmov-swap`.

## The reason to suspect a LOSS rather than a win

Read out of LLVM 22.1.2, trust-cg's x86 lane is the mirror image of LLVM's design with
the cost model removed:

* trust-cg: **two** default-on branch->cmov passes, **zero** cmov->branch passes, and no
  profitability term in either. Its x86 ISel lowers every `Select` to `mov` + `Cmovcc`
  unconditionally, with nothing downstream able to reverse it.
* LLVM: a generous converter PAIRED with `X86CmovConversion` to undo it, which carries a
  real depth/latency/mispredict-penalty model, and one UNCONDITIONAL rule —
  `ForceMemOperand` (`cl::init(true)`): any cmov group containing a memory-operand cmov
  becomes a branch again regardless of cost, because "On x86, a CMOV will dramatically
  amplify any memory latency by blocking speculative execution".

So the live hypothesis was that an unmeasured, cost-model-free branch->cmov pass could be
costing one of the trailing programs — particularly `b1_mispredict`, whose arms are
memory read-modify-writes (`t[j] += acc` / `t[j] ^= acc`), exactly the shape LLVM's
unconditional rule exists to undo.

## Measured: refuted, decisively, in the other direction

| program | if-convert ON (default) | ON, 2nd copy | OFF | verdict |
| --- | ---: | ---: | ---: | --- |
| `b1_mispredict` | 1.0949 | 1.0950 | **1.4429** | removing it costs **44%** |
| `p2_collatz` | 1.0106 | 1.0107 | **1.4700** | removing it costs **47%** |
| `p7_sieve` | 0.7220 | 0.7214 | 0.7326 | removing it costs ~1.5% |

It changes exactly 3 of 18 binaries and all three exit-match trust-cg/LLVM. Both floors
are 0.0001-0.0006, so these are not marginal.

**`X86CmovSwap` changes 0 of 18 binaries** — inert on this corpus, so its default costs
and buys nothing here.

## What this settles

1. **If-conversion is correctly default-ON and is one of the largest single levers in the
   backend** — larger than anything measured this campaign. b1 at 1.0949 is a program
   that if-conversion already rescued from 1.44.
2. **The "trust-cg converts to cmov with no cost model, so it may be over-converting"
   concern is refuted for this corpus.** It is not over-converting on the three programs
   where it fires. A cmov->branch veto pass — which LLVM has and this backend lacks —
   would have nothing to undo here.
3. It reframes b1's remaining 9.5%: the branch-vs-cmov decision on b1's diamond has
   already been made, correctly and profitably. Whatever remains is not that decision.

This does NOT establish that if-conversion is right everywhere — it fires on 3 programs
and this measures those 3. But the direction of the risk was wrong, and the size of the
effect means the pass should not be touched without re-running this.
