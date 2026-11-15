# The m142 closure-argument refusal, reproduced in seconds

Round 3 recorded the `m142_x86_scalar_pair_arg_xback` red and said naming its
cause needed "one instrumented bridge build". It did not. These three files are
the two failing shapes cut out of that 1,236-second differential; each refusal
reproduces from a release bridge dylib in about a second.

```sh
export PATH="$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin:/usr/bin:$PATH"
T=$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc
DY=<worktree>/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so

# the callee rlib, LLVM side (the oracle half of the differential)
$T --edition=2021 -Ztrust-verify=off --crate-type rlib --crate-name calleearg \
   --target x86_64-unknown-linux-gnu -Cpanic=abort -Coverflow-checks=off \
   -Ccodegen-units=1 -Copt-level=0 --out-dir out calleearg.rs

# the caller bin, trust-cg side — this is the compile that refuses
$T --edition=2021 -Ztrust-verify=off --crate-type bin -Zcodegen-backend=$DY \
   --target x86_64-unknown-linux-gnu -Cpanic=abort -Coverflow-checks=off \
   -Ccodegen-units=1 -Copt-level=0 \
   --extern calleearg=out/libcalleearg.rlib -L out -o out/caller caller_apply_once.rs
```

`before-fix.txt` and `after-fix.txt` are the `[TCG-ARG-ABI]` lines that came
back, on the merge commit and after the argument-index fix. They are the whole
finding:

* Both shapes are refused because `scalar_pair_param_plan` declines a
  `ty::Closure` instance BY NAME, so the CLOSURE BODY's own `Option<u8>`
  parameter keeps the whole-slot declaration and `check_param_abi` refuses it.
  The symbol the error is attributed to is the caller being compiled, which is
  why `<&{closure} as Fn<..>>::call` looked like the cause.
* `apply_once` additionally hit a real bridge defect — the `FnAbi::args` index
  of a closure body whose zero-sized env the declaration drops — and reported
  "Report this — it is a bridge bug". After the fix it reports the same honest
  lane refusal as `apply_fn`, which is what bounds the blast radius to one gate,
  one code, two shapes.

Nothing here weakens `m142`; it stays RED on those 16 combinations.
