# x86-64 split-copy replay fixtures

Inputs of `tests/e2e_x86_64_split_copy_replay.rs`. Two trust-ir modules dumped
by the rustc bridge for the `#[no_mangle]` kernels of `split_copy_kernels.rs`,
with the bridge's sidecar records, checked in byte for byte as the bridge wrote
them (the `k.` prefix comes from `-o k.o`). At x86-64 `-Copt-level=3` each
kernel's greedy allocation splits a value whose child is read only by an
original ISel copy; the register-allocation replay used to drop that split
copy (see the rule on `replay_x86_regalloc_stream_mutations`).

## Why the kernels read through a raw pointer

Each array read is `*(&raw const a as *const u64).add(i)` with `i < 8`:

* `a[i]` carries a bounds check, a source Assert. Since the TrustIR v52 panic
  cohort this backend refuses every native source Assert at codegen admission
  (`require_assert_panic_kinds`), and the bridge refuses a `panic=abort` bounds
  check outright (`[TCG-ASSERT-PANIC]`), both before register allocation. The
  earlier fixtures of this directory were the `a[i]` spelling; on that cohort
  both were refused at admission and tested nothing here.
* `a.as_ptr().add(i)` goes through an unsized `&[u64]`, and the bridge lowers
  that into a module `trust-ir validate` rejects (`FieldAccessInvalid` on an
  `insertfield`/`extractfield` of a pointer).

The raw-pointer spelling has no Assert, no unsizing and no UB-check branch in
its optimized MIR, and both dumps validate. The kernels compute what the `a[i]`
spelling computed, and reach the same defect: before the fix `k_xsh_8` printed
the same wrong value and `k_mul_8` was refused at the same spill slot (below).

## Command

```sh
trustc --edition=2021 -Ztrust-verify=off --crate-type lib -Cpanic=abort \
  -Ccodegen-units=1 -Copt-level=3 --target x86_64-apple-darwin \
  --extern core=$CORE/libcore.rlib --extern compiler_builtins=$CORE/libcompiler_builtins.rlib -L $CORE \
  -Zcodegen-backend=$BRIDGE \
  "-Ztrust-ir-cg-args=no-proof-certs batch-cgu=0 dump-trust-ir=$OUT" --emit obj -o k.o split_copy_kernels.rs
```

The fixtures are `$OUT/k.trustcg_split_copy_k_{xsh,mul}_8.rcgu.{trust_irbin,json}`,
unchanged. `batch-cgu=0` selects the bridge's one-module-per-function compile,
which writes one dump per function before compiling it, whether or not the
backend then refuses it.

## Provenance (2026-10-01)

* Compiler: `trustc` 1.99.0-dev, commit `321aaeda75478038420d97830f14724c33c8dc39`
  (atpkg Trust package), aarch64-apple-darwin host.
* `$BRIDGE`: `librustc_codegen_trust_cg.dylib` built from trust-cg
  `a40ece1064c9e946dbac3fc13d7bfd461df65cbd` (the replay fix merged with main
  `ddb6e4964`) with `RUSTC=$(command -v trustc) scripts/trust_cargo.sh build
  --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --release --locked`;
  sha256 `2635f26188bf9f5aeb57f5ae9fc54deea2cdad5491075374027bf043dbe24202`.
  Its trust-ir pin is `ebb5ff734d62aff3d416b312524d7c9e902463fb`. With it the
  command exits 0.
* `$CORE`: x86_64-apple-darwin `core` and `compiler_builtins`, LLVM code
  generation by the same `trustc` at `-Copt-level=3`, from that commit's
  `library/` (`git archive 321aaeda7 library/core library/compiler-builtins
  library/stdarch library/portable-simd` in the Trust repository), with
  `RUSTC_BOOTSTRAP=1`:

  ```sh
  trustc --edition 2024 --crate-type lib --crate-name core -Zforce-unstable-if-unmarked \
    -Ztrust-verify=off -Cpanic=abort --target x86_64-apple-darwin -Copt-level=3 \
    --out-dir $CORE library/core/src/lib.rs
  trustc --edition 2024 --crate-type lib --crate-name compiler_builtins -Zforce-unstable-if-unmarked \
    -Ztrust-verify=off -Cpanic=abort --target x86_64-apple-darwin \
    --cfg 'feature="compiler-builtins"' --cfg 'feature="mem"' -Copt-level=3 \
    --extern core=$CORE/libcore.rlib -L $CORE --out-dir $CORE \
    library/compiler-builtins/compiler-builtins/src/lib.rs
  ```

  sha256 `15f0b28761044ac7287f76145606ab82165482d52a3b4f5eb4cfd1d3410ec858`
  (`libcore.rlib`) and
  `cbda938dc927d93929b5c0c5b3b7ce8e0329c11b53e685d8b525f54a15b2cee3`
  (`libcompiler_builtins.rlib`).
* A bridge built the same way from trust-cg
  `a2a7da739b40b00d161ec7cd5f8d1007c223c3b1` (main before the replay fix and
  before the v52 cohort; sha256
  `8f1969bbf03841b29d55e58ef2bcec1edbe4b202d161b07ff8d0516d3ee9e59b`) writes
  byte-identical dumps and exits 1:
  `trustcg_split_copy_k_mul_8: [TCG-REGALLOC-063] ... x86-64 regalloc failed:
  [TCG-POST-RA-SPILL-INIT] fn trustcg_split_copy_k_mul_8 reads spill slot
  [rbp-128] with no store anywhere in the final stream`; its `k_xsh_8` object
  compiles.
* Both dumps are wire v38. `trust-ir validate --format bin` (atpkg trust-ir
  0.14.0) reports each well-formed; at v38 an absent `body_gate` is the
  grandfathered state.

## Contents

`fixtures_match_their_recorded_provenance` requires each row below to match
the file's bytes.

| file | sha256 |
| --- | --- |
| `split_copy_kernels.rs` | `886a46373c2a7c82961e03bdf95dd0f9c7e70d2da290ff11a4f4b962e8f1458d` |
| `k.trustcg_split_copy_k_xsh_8.rcgu.trust_irbin` | `5fb35eb5c376b997b65394e64598e7e577b18c08e494fb9cafeed76a8dfada5a` |
| `k.trustcg_split_copy_k_xsh_8.rcgu.json` | `a4771c632ca7327d72d6e553ec160915f17ad914ec5f72131a6af505e1168a05` |
| `k.trustcg_split_copy_k_mul_8.rcgu.trust_irbin` | `bc6ca089dee6e7b1694b8394e896489fa5d95b9c9215ae72faa59032053ab860` |
| `k.trustcg_split_copy_k_mul_8.rcgu.json` | `530877d3b5f0d4703700cdae2899949eca22a050f6b0f6817306a5f71b12ad28` |

## Expected values

The C driver passes `s[i] = i * 0x9E3779B97F4A7C15` (wrapping), `i < 8`. The
test's Rust oracle gives `8275365051531202673` for `k_xsh_8` and
`8577365346607315621` for `k_mul_8`. Linked with that driver
(`cc -arch x86_64`) and run under Rosetta 2, the `k_xsh_8` object of the
`a2a7da739` bridge printed `5374597959403525797`; the objects of the
`a40ece106` bridge printed the two oracle values.
