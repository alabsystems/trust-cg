# The closure `FnAbi` argument-index defect, reproduced in seconds

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Measured 2026-09-24, Linux x86-64, stage2 `trustc` `3a3e781fe`, release bridge
dylib, `-Copt-level=0`. Each refusal comes back in about a second; no
instrumented bridge build is needed.

## The defect

`func_ty_for_instance` does not prepend the env input for a closure body whose
by-value environment is ZERO-SIZED (a non-capturing `FnOnce` — the body's entry
block drops it too, `closure_body_takes_env`). rustc's `fn_sig_for_fn_abi` does
NOT drop it: the receiver stays `FnAbi::args[0]` with `PassMode::Ignore`.

The bridge then used its own `inputs` index as the `FnAbi::args` index at the
argument gates in `classify_func_ty`, and `param_input_index_for_mir_arg`
subtracted a SECOND 1 on the body side. For such a body both ends therefore
asked rustc about the argument one position too early, and the gate compared the
closure ENV against the first real parameter.

**No miscompile was possible.** The gate type-checks the `ArgAbi` against the
type it is classifying before reading any placement, so a misaligned index
always REFUSED. What it cost is capability and honesty: an ordinary program
shape was refused with "Report this — it is a bridge bug".

## The fix

The mapping is stated ONCE at each end, and both name rustc's own index:

* `closure_env_abi_index_offset` (declaration) — 1 exactly for a dropped-env
  closure body, threaded into `classify_func_ty` as `abi_arg_index_offset` and
  added to `input_index` at every gate that indexes `FnAbi::args`. The
  coroutine-resume lane and the `fn(..)`-pointer lane pass 0 and say why.
* `rustc_fn_abi_arg_index_for_mir_arg` (body) — `local - 1`, with no closure
  adjustment, because rustc keeps one `args` entry per MIR argument local.

The unit test `the_declaration_and_the_body_name_the_same_rustc_fn_abi_argument`
pins that the two halves name the same argument.

## Reproducing

```sh
export PATH="$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin:/usr/bin:$PATH"
cd crates/rustc-codegen-trust-cg
env RUSTC="$(command -v trustc)" targo --unverified build --release --locked
cd -
./drive.sh "my label" \
  crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so
```

`before-fix.txt` and `after-fix.txt` are that driver's output on `origin/main`
(`43affd4a9`) and on this branch. They are the whole finding:

* BOTH shapes are refused, before and after, because `scalar_pair_param_plan`
  declines a `ty::Closure` instance BY NAME — closure call sites hand-build one
  value per argument — so the closure body's own `Option<u8>` `PassMode::Pair`
  parameter keeps the whole-slot declaration and `check_param_abi` refuses it.
  That decline is a separate, still-open scope question (owed under XD-05:
  teaching the pair lane to the six hand-built closure-call argument builders).
  Nothing here weakens it.
* `apply_once` additionally hit the index defect and reported "Report this — it
  is a bridge bug". After the fix it reports the SAME honest lane refusal as
  `apply_fn`, which is what bounds the blast radius to one gate, one code, two
  shapes.

The symbol each error is attributed to is the caller being compiled, which is
why `<&{closure} as Fn<..>>::call` looked like the cause in the round-3 log.

## This defect is upstream's, not a merge artifact

`before-fix.txt` was measured on `origin/main` `43affd4a9` itself (this branch
was subsequently rebased onto `777ab22cd`, whose single commit adds archive
records only and does not touch the bridge). Upstream
reimplemented the two-value `PassMode::Pair` argument lane independently and
carried the same off-by-one into it, so this fix applies to upstream's lane
directly — it is not a repair of a local divergence.

## Regression evidence for the lane the index feeds

Measured on this branch, same host and stage2 driver:

| Gate | Result |
| --- | --- |
| `tests::the_declaration_and_the_body_name_the_same_rustc_fn_abi_argument` | 1 passed |
| bridge `--lib` (295 tests) | 282 passed, 13 failed — all `mem_refine::` solver-certificate, the known pre-existing set |
| `m141_x86_scalar_pair_arg_xback` (upstream's own pair-argument differential, 12 shapes x 4 opt levels x 2 backends) | 1 passed, 976s |
| `closures_x86` | 1 passed, 56s |
| `closure_capture_x86` | 3 passed, 89s |
| root `cargo test -p trust-cg-codegen --lib` | 4159 passed, 19 failed — the known XD-01 proof-promotion set |
