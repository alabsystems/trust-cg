# fmt-selfhost — the `core::fmt` interception, from BOTH sides

**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · **License:** Apache-2.0

## Why this corpus exists

`core::fmt::rt::Argument`, `core::fmt::Arguments` and `core::fmt::rt::ArgumentType`
are recognised BY NAME (`is_fmt_internal_ty`) and the `format!` / `write!` /
`println!` / `panic!` interception decodes them at COMPILE TIME: a local of one of
those types is treated as dead, its assignments are skipped, and a call returning
one is dropped to a no-op.

That is right when the types are FOREIGN — a downstream crate building a
`format_args!` the bridge is about to synthesise into bytes. It is **wrong when
the types are LOCAL**, i.e. when `core` itself is the crate being compiled:
`rt::Argument::new_display` really does construct an `Argument`,
`PanicInfo::message` really does return an `Arguments`, and skipping those
assignments is a silent miscompile rather than a refusal. Measured on
2026-09-10, the pre-fix backend compiled `core::panic::PanicInfo::message` to

```
sub  sp, sp, #0x10
sub  x1, x29, #0x8      ; an UNINITIALISED stack slot
ldr  x0, [x1]           ; ... returned as `self.message`
```

`is_local_fmt_internal_ty` now splits the two cases, and the deadness seeding is
re-rooted at the calls an interception actually consumes.

Both halves need a differential net, and they observe DIFFERENT things, so this
corpus compares **stdout AND exit code** (the existing `shape-coverage` corpus
compares exit status only, and formatted bytes are the whole point here). Panic
MESSAGE TEXT is a long-standing accepted deviation, so a panicking program is
compared on its exit status and its pre-panic stdout only.

| program | side | what it pins |
| --- | --- | --- |
| `fmt_println` | foreign | `println!`/`print!`/`eprintln!` with integer and `&str` placeholders — the `std::io::_print` consumer |
| `fmt_format` | foreign | `format!` into a `String`, observed through a byte checksum — the `alloc::fmt::format` (O0) and `map_or_else` (O2/O3-inlined) consumers |
| `fmt_write` | foreign | `write!` into a `String` twice — the `<String as fmt::Write>::write_fmt` consumer and its append semantics |
| `fmt_panic` | foreign | a FORMATTED `panic!` — the diverging-panic consumer, whose whole block is replaced |
| `argtype_shape` | self-host | the `ArgumentType` LAYOUT: a niche-encoded two-variant enum carrying a non-null data pointer plus a function pointer, rebuilt in a user crate so it can actually be RUN |
| `selfhost_live_reader` | self-host | the DEADNESS SEEDING, on the real self-host path: compiled `--crate-name core`, so its own `fmt::rt::ArgumentType` is CRATE-LOCAL to the recognizer. One local is read by a non-intercepted function AND flows into a `panic!` root (must be lowered); one is consumed only by the `panic!` (must stay dead) |
| `abi_aggregate_return` | ABI | the RETURN CONVENTION of an `rt::Argument`-shaped 16-byte niche enum — rustc returns it through the hidden caller-allocated buffer. A pinned `[TCG-RET-ABI]` REFUSAL until 2026-09-11; a running row since the convention was lowered |

`argtype_shape` is the runnable stand-in for the self-host LAYOUT: the `core`
bodies that now lower (`Argument::new_display`, `Arguments::new`, …) cannot be
executed from a user program, because a user program links the prebuilt `core`.
What CAN be executed is the memory layout they now depend on, so that is what
this program exercises.

`selfhost_live_reader` goes one step further and runs the self-host CODE PATH
itself. The recognizer identifies a crate-local `core::fmt::rt::ArgumentType` by
its crate-qualified def path plus `DefId::is_local`, so a program compiled with
`--crate-name core` that declares its own `fmt::rt::ArgumentType` IS on the
self-host branch — `run.sh`'s `extra_flags` passes that flag to both sides. It is
the only program in the repo that reaches the self-host deadness seeding from a
user crate, and unlike the five below it does NOT pass on the pre-fix backend:
with the seeding rooted on reachability alone, `live_reader`'s local was marked
dead, its `let a = …` skipped, and the function refused with `Place projection
field 0 before aggregate binding` at both opt levels.

**Be honest about what each half proves.** The five original programs pass on the
backend BEFORE the self-host change as well as after (measured 2026-09-10) — the
four foreign-side ones because that lane is deliberately untouched, and
`argtype_shape` because its enum lives in a user crate and was never name-gated.
For those five this corpus is a REGRESSION net for the layout and interception
machinery, not a witness for the `PanicInfo::message` fix; that fix is witnessed
by the `core` census (438 -> 316 fail-closed roots) and by the emitted object for
`PanicInfo::message`, which stops loading from an uninitialised stack slot and
now reads `ldr x1, [x0]; mov x0, x1; ret`.

The two added programs DO discriminate: `selfhost_live_reader` fails on the
pre-fix seeding (see above), and `abi_aggregate_return` exercises the return
convention the mixed-link table below is about — it declined on the backend that
had the gate and no lowering, and compiled to a WRONG object on the backend that
had neither.

Why no user program can witness the FOREIGN half of the same hazard: a genuine
non-intercepted reader of a foreign `fmt::Arguments` forces the value to be
materialized, and a foreign `core::fmt` plumbing type has no memory layout by
construction, so the bridge fails closed — measured 2026-09-10, `let lit =
format_args!("literal"); observe(&lit)` refuses with `Ty::core::fmt::rt::-`
`ArgumentType` at `-O0` and `-O2`. Inside `core` the layout EXISTS, which is
precisely why the self-host branch needs the reader proof and the foreign branch
does not.

## The aggregate-return ABI seam — MEASURED, then CLOSED by refusal

Like every whole-program differential in this repo, `argtype_shape` compiles both
the caller and the callee with the same backend, so a calling-convention
disagreement is invisible to it (this is the whole argument for
`../abi-xback`). It was invisible here in a way that mattered, because the type
this program models is returned BY VALUE across real calls inside `core`.

Measured 2026-09-10 with `probe_make(&i32) -> ArgTy<'_>` (`#[inline(never)]`)
in a separately compiled rlib, so the call really crosses a codegen boundary:

| caller | callee | result |
| --- | --- | --- |
| LLVM | LLVM | exits 42 (the oracle) |
| trust-cg | trust-cg | exits 42 (self-consistent — which is why every whole-program row passed) |
| trust-cg | LLVM | **exits 138** (a crash) |
| LLVM | trust-cg | **exits 0** — a SILENT WRONG VALUE |

The cause, read from rustc's own `FnAbi` rather than guessed: under the RUST ABI
`FnAbi::adjust_for_rust_abi` casts a `BackendRepr::Memory` aggregate into an
integer register only when it fits in ONE pointer, so every larger Memory
aggregate keeps `PassMode::Indirect` — the callee writes through the `x8` return
buffer. trust-cg's aggregate-return classifier is the C one (AAPCS64 §6.9:
register pair up to 16 bytes, `x8` above it), so it returned the same 16-byte
value in `x0`/`x1`. Disassembled at `-Copt-level=0`:

```
LLVM      str x8, [sp, #0x8] ... str x0, [x9] ; str x8, [x9, #0x8]   ; writes THROUGH x8
trust-cg  ldr x0, [x19] ; ldr x1, [x19, #0x8] ; ret                  ; returns in x0/x1
```

This was never introduced by the self-host change — it is a general property of
the aggregate-return classifier — but this lane is the first to EMIT `core`
functions that return `fmt::rt::Argument` by value, which makes it reachable in
exactly the mixed-link self-host scenario.

**It was a refusal first.** `check_aggregate_return_abi_matches_rustc` compares
trust-cg's placement against rustc's `PassMode` and fails the function closed
with `[TCG-RET-ABI]`, naming the mode and listing the fixes. That was the only
honest option while the hidden return-buffer pointer had no lowering, and its
cost was recorded rather than hidden: the `core` census went **316 -> 516**
fail-closed roots, 221 of them `[TCG-RET-ABI]` — 50 returning an
`rt::Argument`-family type (33 of those are `fmt::rt` constructors), the rest
ordinary 9-16 byte Memory-repr returns such as `Option<ascii::EscapeDefault>`,
`char::EscapeDebug` and `[char; 3]`. Those objects had previously been emitted
with the wrong return convention.

**It is now LOWERED (2026-09-11), and the gate proves the agreement.** When
rustc's `FnAbi` says `PassMode::Indirect`, the lowered function takes a hidden
LEADING return-buffer pointer parameter and returns nothing — the shape trust-ir
already had a word for (`ParamAttrs::sret`, which it validates: pointer-typed,
unique, empty return list). The callee writes its result through that pointer;
the caller allocates the buffer (it uses the destination slot, exactly as rustc's
own `make_return_dest` does) and passes its address. Per target, from each ABI's
own rule and never from a size heuristic: **AAPCS64 §6.9 `x8`**, a register
outside the X0-X7 argument bank, which is why the AArch64 selector needs the
marker at all; **System V x86-64 `rdi`**, an ordinary hidden leading INTEGER
argument, which a leading pointer parameter already lands in, plus the psABI
§3.2.3 requirement that the callee return that address in `%rax`. Any other
target REFUSES.

`[TCG-RET-ABI]` is UNCHANGED and still runs on every by-value aggregate return.
It is told which placement the bridge is about to emit, so it now compares
`CallerBuffer` against rustc's `CallerBuffer` and agrees. That agreement is the
only evidence the two classifiers match, so the gate is not excused from the
lane — it is the lane's witness. Indirect calls (a `fn(..)` pointer, a vtable
slot) do NOT lower the convention and keep refusing: the selector marker is keyed
by callee SYMBOL, and neither has one.

Measured after the change: the `core` census returns to **316** fail-closed roots
with `[TCG-RET-ABI]` at **0** and 200 more emitted objects (2933 -> 3133), and NO
symbol that compiled before now fails. All four mixed-link directions exit 42 at
`-Copt-level=0` and `-Copt-level=2` — see `../sret-xback/`, which measures that
table directly and carries the negative control for it.

## Running

```sh
./run.sh [path-to-backend.dylib] [path-to-trustc]
```

Every program is compiled twice — once through the bridge, once through the
stock LLVM backend of the SAME compiler, which is the oracle — at `-Copt-level=0`
and `-Copt-level=2`, and both binaries are run twice so a read of uninitialised
memory shows up as run-to-run variation.

## The decline ratchet

One row is listed explicitly, with a substring of the DIAGNOSTIC it is allowed
to decline with. A NEW decline fails the gate; a listed decline that starts
compiling also fails it until the line is consciously removed; and a listed row
that starts declining for a DIFFERENT reason fails too, so an allowance can
never quietly cover whatever appears next.

* `fmt_write O2` — `memory-backed aggregate assignment Rvalue::Cast`, an
  unrelated gap in the `String` slot path.

`abi_aggregate_return O0` / `O2` were listed here while the indirect-return
convention had no lowering. They are deliberately NOT listed any more, and the
selftest asserts their absence: the convention is implemented, so the program
compiles and is compared like every other row. If either starts declining again,
the gate fails — which is the point of removing the line rather than leaving it.
