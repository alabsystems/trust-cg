// Integration test: GENERAL `&dyn Trait` METHOD DISPATCH (dynamic dispatch) —
// compiled for x86_64 via the rustc_codegen_trust_cg bridge, COMPILED, LINKED,
// and RUN, with exit codes checked against the default LLVM backend at the SAME
// optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The keystone covered here is a VIRTUAL CALL: `d.method(args)` where
// `d: &dyn Trait`. The bridge emits a vtable for each concrete `impl` (a
// `{ drop_in_place, size, align, methods... }` read-only global, one
// `SymbolAddr` reloc per `tcx.vtable_entries` method), builds the `&T as &dyn
// Trait` unsize fat pointer `{ data, vtable }`, and lowers the call by LOADING
// the method pointer from `vtable + idx*ptr_size` (the rustc vtable index) and
// `CallIndirect`-ing it with the fat pointer's DATA half as the thin `&self`.
//
// Each program below is a `trait Shape { fn val(&self) -> i64; ... }` with 2+
// impls (`Square`, `Circle`). The cases exercise:
//   * a direct `&dyn Shape` constructed and dispatched (`.val()`) — the right
//     impl must run;
//   * a RUNTIME-selected `&dyn Shape` (`if cond { &a } else { &b }`) — the
//     vtable must be carried correctly through the branch merge so each branch
//     dispatches its own impl;
//   * a method TAKING ARGS (`fn scale(&self, k: i64) -> i64`) — args pass
//     normally after the thin `&self`;
//   * a SUM over an array/loop of `&dyn Shape` (`&[&dyn Shape]`) — each 16-byte
//     fat-pointer element is loaded and dispatched in turn.
//
// A wrong vtable slot, a wrong `&self` data pointer, or a dropped argument shows
// up as a mismatched exit code against LLVM.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const OPT_LEVEL: &str = "-Copt-level=3";

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run dyn-dispatch test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn x86_64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_dyn_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", OPT_LEVEL])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    match try_compile(dir, name, src, backend) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend). stderr: <<<{stderr}>>>",
            if backend.is_some() { "trust-cg" } else { "llvm" },
        ),
    }
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The full differential: each `&dyn Trait` dispatch program is compiled by
/// trust-cg AND LLVM, run, and the exit codes must match each other and the
/// expected value. The trait + 2 impls are shared; each case constructs and
/// dispatches a trait object differently.
#[test]
fn dyn_dispatch_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("cases");

    // The shared trait + impls, prepended to every case's `fn main`.
    const PRELUDE: &str = "\
        trait Shape { fn val(&self) -> i64; fn scale(&self, k: i64) -> i64; } \
        struct Square { s: i64 } \
        struct Circle { r: i64 } \
        impl Shape for Square { \
            fn val(&self) -> i64 { self.s * self.s } \
            fn scale(&self, k: i64) -> i64 { self.s * k } } \
        impl Shape for Circle { \
            fn val(&self) -> i64 { self.r * 3 } \
            fn scale(&self, k: i64) -> i64 { self.r + k } } ";

    // (name, `fn main` body + any helpers, expected exit code). All values 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // 1. A direct `&dyn Shape` constructed from a `Square` and dispatched.
        //    `Square{7}.val()` = 49. Confirms the right impl's method runs.
        (
            "direct_square",
            "fn main(){ let sq = Square { s: 7 }; \
                 let d: &dyn Shape = &sq; \
                 std::process::exit(d.val() as i32); }",
            49,
        ),
        // 2. A direct `&dyn Shape` from a `Circle` — the OTHER impl. `Circle{8}.val()`
        //    = 24. Together with case 1 this proves the vtable selects per-type.
        (
            "direct_circle",
            "fn main(){ let c = Circle { r: 8 }; \
                 let d: &dyn Shape = &c; \
                 std::process::exit(d.val() as i32); }",
            24,
        ),
        // 3. The `&dyn Shape` flows through a real (non-inlined) function boundary:
        //    a `fn dispatch(d: &dyn Shape) -> i64` whose `&dyn` PARAMETER is a
        //    two-word { data, vtable } value received in a register pair, then
        //    dispatched. `Square{6}.val()` = 36.
        (
            "boundary_param",
            "#[inline(never)] fn dispatch(d: &dyn Shape) -> i64 { d.val() } \
             fn main(){ let sq = Square { s: 6 }; \
                 let d: &dyn Shape = &sq; \
                 std::process::exit(dispatch(d) as i32); }",
            36,
        ),
        // 4. A RUNTIME-selected `&dyn Shape` taking the `true` branch (Square): the
        //    vtable chosen on the live branch must reach the call. `Square{5}.val()`
        //    = 25.
        (
            "runtime_select_true",
            "fn main(){ let a = Square { s: 5 }; let b = Circle { r: 9 }; \
                 let cond = std::hint::black_box(true); \
                 let d: &dyn Shape = if cond { &a } else { &b }; \
                 std::process::exit(d.val() as i32); }",
            25,
        ),
        // 5. The SAME runtime-select shape taking the `false` branch (Circle):
        //    proves the merge carries the OTHER vtable. `Circle{9}.val()` = 27.
        (
            "runtime_select_false",
            "fn main(){ let a = Square { s: 5 }; let b = Circle { r: 9 }; \
                 let cond = std::hint::black_box(false); \
                 let d: &dyn Shape = if cond { &a } else { &b }; \
                 std::process::exit(d.val() as i32); }",
            27,
        ),
        // 6. A method TAKING AN ARGUMENT: `scale(&self, k)` passes `k` after the
        //    thin `&self`. `Circle{10}.scale(5)` = 10 + 5 = 15.
        (
            "method_with_arg",
            "#[inline(never)] fn go(d: &dyn Shape, k: i64) -> i64 { d.scale(k) } \
             fn main(){ let c = Circle { r: 10 }; \
                 let d: &dyn Shape = &c; \
                 std::process::exit(go(d, 5) as i32); }",
            15,
        ),
        // 7. A SUM over an array/loop of `&dyn Shape`: a `&[&dyn Shape]` of mixed
        //    impls, each 16-byte fat-pointer element loaded and dispatched.
        //    Square{4}=16, Circle{7}=21, Square{3}=9 -> 46.
        (
            "array_loop_sum",
            "#[inline(never)] fn sum(shapes: &[&dyn Shape]) -> i64 { \
                 let mut total = 0i64; let mut i = 0usize; \
                 while i < shapes.len() { total += shapes[i].val(); i += 1; } total } \
             fn main(){ let a = Square { s: 4 }; let b = Circle { r: 7 }; \
                 let c = Square { s: 3 }; \
                 let arr: [&dyn Shape; 3] = [&a, &b, &c]; \
                 std::process::exit(sum(&arr) as i32); }",
            46,
        ),
        // 8. A longer mixed array, Circle-first, to catch any per-element offset
        //    bug. Circle{2}=6, Square{10}=100, Circle{5}=15, Square{1}=1 -> 122.
        (
            "array_loop_sum_mixed",
            "#[inline(never)] fn sum(shapes: &[&dyn Shape]) -> i64 { \
                 let mut total = 0i64; let mut i = 0usize; \
                 while i < shapes.len() { total += shapes[i].val(); i += 1; } total } \
             fn main(){ let a = Circle { r: 2 }; let b = Square { s: 10 }; \
                 let c = Circle { r: 5 }; let d = Square { s: 1 }; \
                 let arr: [&dyn Shape; 4] = [&a, &b, &c, &d]; \
                 std::process::exit(sum(&arr) as i32); }",
            122,
        ),
        // 9. `Box<dyn Trait>` UNSIZE + dispatch: `Box::new(Square{7}) as Box<dyn
        //    Shape>` then `.val()`. The owning fat pointer reuses the box's heap
        //    data pointer (no alloca/copy) paired with the vtable; the receiver
        //    recovery (`Box`'s `Unique`/`NonNull` transmute to `*const dyn`) must
        //    yield the same { data, vtable }. `Square{7}.val()` = 49.
        //    (`std::process::exit` so `Box<dyn>` Drop does not run.)
        (
            "box_dyn_square",
            "fn main(){ let b: Box<dyn Shape> = Box::new(Square { s: 7 }); \
                 std::process::exit(b.val() as i32); }",
            49,
        ),
        // 10. The OTHER impl through a `Box<dyn Shape>`: `Box::new(Circle{8})`,
        //     `.val()` = 24. With case 9 this proves the vtable is keyed per
        //     concrete boxed type.
        (
            "box_dyn_circle",
            "fn main(){ let b: Box<dyn Shape> = Box::new(Circle { r: 8 }); \
                 std::process::exit(b.val() as i32); }",
            24,
        ),
        // 11. TWO methods dispatched through the SAME `Box<dyn Shape>`: `.val()`
        //     and `.scale(k)`. Both vtable slots must resolve off the recovered
        //     receiver. `Square{6}`: val=36, scale(2)=12 -> 48.
        (
            "box_dyn_two_methods",
            "fn main(){ let b: Box<dyn Shape> = Box::new(Square { s: 6 }); \
                 std::process::exit((b.val() + b.scale(2)) as i32); }",
            48,
        ),
        // 12. A MULTI-FIELD boxed concrete type through `Box<dyn>` (self-contained
        //     trait): `B{x,y}` -> `x+y`. The box's heap pointer addresses the whole
        //     two-field struct; the recovered `&self` must read both fields.
        //     `B{x:5,y:7}.v()` = 12.
        (
            "box_dyn_multifield",
            "trait Two { fn v(&self) -> u64; } \
             struct B { x: u64, y: u64 } \
             impl Two for B { fn v(&self) -> u64 { self.x + self.y } } \
             fn main(){ let b: Box<dyn Two> = Box::new(B { x: 5, y: 7 }); \
                 std::process::exit(b.v() as i32); }",
            12,
        ),
    ];

    for (name, body, expected) in shapes {
        let src = format!("{PRELUDE}{body}");
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), &src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), &src, Some(&dylib));
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM backend exit code for `{name}` is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
