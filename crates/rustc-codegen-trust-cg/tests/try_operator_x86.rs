#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: the `?` operator (Try / error-propagation) std `fn main`
// programs compiled for x86_64 via the rustc_codegen_trust_cg bridge — COMPILED,
// LINKED, and RUN, with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: `?`-operator (Try::branch / FromResidual::from_residual / ControlFlow)
// support for the two std `Try` types `Result<T, E>` and `Option<T>`.
//
// The `?` desugaring rustc emits is:
//
//     let cf = <Ty as Try>::branch(expr);   // Some(v)/Ok(v) -> Continue(v)
//                                            // None/Err(e)   -> Break(residual)
//     match discriminant(cf) {
//         Continue => bind the value, fall through,
//         Break    => return FromResidual::from_residual(residual),
//     }
//
// The bridge lowers the real `Try::branch` body (constructing the `ControlFlow`
// in a memory slot) and INTERCEPTS `from_residual` (its real body is
// `#[track_caller]` and descends into a `caller_location` intrinsic this backend
// does not lower), synthesizing the fixed std semantics directly:
//   * `Result<T,F>::from_residual(Err(e)) = Err(From::from(e))` — applying ONLY an
//     IDENTITY `From` (E == F). A value-transforming `From` impl FAILS CLOSED with
//     a precise diagnostic rather than guessing the conversion (never miscompile).
//     A ZERO-SIZED error type (`E = ()`, i.e. `?` on `Result<T, ()>`) copies NO
//     payload — the residual `Result<Infallible, ()>` is itself a ZST and reaches
//     `from_residual` as a ZST *constant* operand (no place); `Err(())` is fully
//     constructed by the Err-discriminant write, so the empty payload copy is skipped.
//   * `Option<T>::from_residual(None) = None`.
//
// Each program is compiled by BOTH backends and run; the trust-cg exit code must
// equal the LLVM exit code (and the expected value). `run_exit_code` asserts the
// process exited via a normal exit code (not a signal), so a regressed `?` that
// faulted (SIGBUS/SIGSEGV) would fail the test loudly rather than pass silently.
//
// Regression context: a chained `?` (`let a = f(x)?; let b = f(a)?; ...`) drove
// enough register pressure that the x86-64 greedy live-range *splitter* placed a
// join-block split copy unsoundly for the diamond CFG — the memory-aggregate
// return-slot pointer was left un-rematerialized on the taken path, so the
// post-call reload read a stale stack slot and the program faulted. The fix
// disables x86-64 live-range splitting (a pure code-quality optimization;
// falling back to the plain greedy allocator is always sound). These chained-`?`
// cases lock that fix in.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";

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
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run try-operator test");
    let built = target_dir
        .join("release")
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
    let dir = std::env::temp_dir().join(format!("rcl2_try_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the given backend (None = default LLVM). On success returns
/// `Ok(binary_path)`; on a compile/link failure returns `Err(stderr)` so callers
/// can assert a fail-closed diagnostic.
fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
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
        .expect("process exited via signal, not exit code (a `?` fault/miscompile)")
}

/// The full differential: each `?`-operator `fn main` is compiled by trust-cg AND
/// LLVM, run, and the exit codes must match each other and the expected value.
/// All values are in 0..=255 (process exit truncates to a byte).
#[test]
fn try_operator_shapes_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("shapes");

    let shapes: &[(&str, &str, i32)] = &[
        // --- Result<T, E> ? : Ok-propagation. compute(5): helper(5)=Ok(10) so
        //     a=10; helper(10)=Ok(20) so b=20; Ok(10+20)=Ok(30). -> 30.
        (
            "result_ok_prop",
            "fn helper(x:i32)->Result<i32,i32>{ if x<0 {return Err(7);} Ok(x*2) }\n\
             fn compute(x:i32)->Result<i32,i32>{ let a=helper(x)?; let b=helper(a)?; Ok(a+b) }\n\
             fn main(){ std::process::exit(match compute(5){Ok(v)=>v,Err(e)=>100+e}); }",
            30,
        ),
        // --- Result<T, E> ? : Err early-return. compute(-1): helper(-1)=Err(7),
        //     so the FIRST `?` breaks early -> `Err(7)`; main maps Err(7)->107.
        (
            "result_err_early",
            "fn helper(x:i32)->Result<i32,i32>{ if x<0 {return Err(7);} Ok(x*2) }\n\
             fn compute(x:i32)->Result<i32,i32>{ let a=helper(x)?; let b=helper(a)?; Ok(a+b) }\n\
             fn main(){ std::process::exit(match compute(-1){Ok(v)=>v,Err(e)=>100+e}); }",
            107,
        ),
        // --- Option<T> ? : Some-propagation. chain(4): first(4)=Some(5) so a=5;
        //     first(5)=Some(6) so b=6; Some(5+6)=Some(11). -> 11.
        (
            "option_some_prop",
            "fn first(x:i32)->Option<i32>{ if x==0 {None} else {Some(x+1)} }\n\
             fn chain(x:i32)->Option<i32>{ let a=first(x)?; let b=first(a)?; Some(a+b) }\n\
             fn main(){ let r=match chain(4){Some(v)=>v,None=>99}; std::process::exit(r); }",
            11,
        ),
        // --- Option<T> ? : None early-return. chain(0): first(0)=None, so the
        //     FIRST `?` breaks early -> `None`; main maps None->99.
        (
            "option_none_early",
            "fn first(x:i32)->Option<i32>{ if x==0 {None} else {Some(x+1)} }\n\
             fn chain(x:i32)->Option<i32>{ let a=first(x)?; let b=first(a)?; Some(a+b) }\n\
             fn main(){ let r=match chain(0){Some(v)=>v,None=>99}; std::process::exit(r); }",
            99,
        ),
        // --- A chain of >= 3 `?` (Result). The high register pressure of three
        //     consecutive `?` plus the live `a`/`b`/`c` across each call+diamond is
        //     exactly the shape that previously faulted. compute(5): helper(5)=6
        //     (a=5? no: a=helper(5)=6); a=6,b=7,c=8; Ok(6+7+8)=Ok(21). -> 21.
        (
            "result_three_q_chain",
            "fn helper(x:i32)->Result<i32,i32>{ if x<0 {return Err(7);} Ok(x+1) }\n\
             fn compute(x:i32)->Result<i32,i32>{ let a=helper(x)?; let b=helper(a)?; \
             let c=helper(b)?; Ok(a+b+c) }\n\
             fn main(){ std::process::exit(match compute(5){Ok(v)=>v,Err(e)=>100+e}); }",
            21,
        ),
        // --- A chain of 5 `?` (Result), even higher pressure. c(1): each helper
        //     adds 1: a=2,b=3,d=4,e=5,f=6; Ok(2+3+4+5+6)=Ok(20). -> 20.
        (
            "result_five_q_chain",
            "fn h(x:i32)->Result<i32,i32>{ if x>100 {return Err(7);} Ok(x+1) }\n\
             fn c(x:i32)->Result<i32,i32>{ let a=h(x)?; let b=h(a)?; let d=h(b)?; \
             let e=h(d)?; let f=h(e)?; Ok(a+b+d+e+f) }\n\
             fn main(){ std::process::exit(match c(1){Ok(v)=>v,Err(e)=>100+e}); }",
            20,
        ),
        // --- `?` calling a helper that returns Result (inside a Result fn).
        //     use_it(2): parse(2)=Ok(12) so v=12; Ok(12*3)=Ok(36). -> 36.
        (
            "q_helper_returns_result",
            "fn parse(s:i32)->Result<i32,i32>{ if s==0 {Err(5)} else {Ok(s+10)} }\n\
             fn use_it(x:i32)->Result<i32,i32>{ let v=parse(x)?; Ok(v*3) }\n\
             fn main(){ std::process::exit(match use_it(2){Ok(v)=>v,Err(e)=>100+e}); }",
            36,
        ),
        // --- `?` with a DISTINCT (custom) error type `i64` (E != T width; identity
        //     `From<i64> for i64`). run(5): check(5)=Ok(10) a=10; check(10)=Ok(20)
        //     b=20; Ok(30). -> 30.
        (
            "q_custom_err_i64_ok",
            "fn check(x:i32)->Result<i32,i64>{ if x<0 {Err(7)} else {Ok(x*2)} }\n\
             fn run(x:i32)->Result<i32,i64>{ let a=check(x)?; let b=check(a)?; Ok(a+b) }\n\
             fn main(){ std::process::exit(match run(5){Ok(v)=>v,Err(e)=>100+(e as i32)}); }",
            30,
        ),
        // --- Same custom `i64` error type, the Err early-return path. run(-1):
        //     check(-1)=Err(7) -> early return Err(7); main maps to 107.
        (
            "q_custom_err_i64_err",
            "fn check(x:i32)->Result<i32,i64>{ if x<0 {Err(7)} else {Ok(x*2)} }\n\
             fn run(x:i32)->Result<i32,i64>{ let a=check(x)?; let b=check(a)?; Ok(a+b) }\n\
             fn main(){ std::process::exit(match run(-1){Ok(v)=>v,Err(e)=>100+(e as i32)}); }",
            107,
        ),
        // --- `?` with a custom error type of a DIFFERENT width (`u8`), Err path.
        //     run(-1): check(-1)=Err(9u8) -> early return; main maps to 109.
        (
            "q_custom_err_u8",
            "fn check(x:i32)->Result<i32,u8>{ if x<0 {Err(9u8)} else {Ok(x*2)} }\n\
             fn run(x:i32)->Result<i32,u8>{ let a=check(x)?; Ok(a) }\n\
             fn main(){ std::process::exit(match run(-1){Ok(v)=>v,Err(e)=>100+(e as i32)}); }",
            109,
        ),
        // --- `?` on a UNIT-error `Result<i32, ()>`, Ok path. The residual
        //     `Result<Infallible, ()>` is a ZST and reaches `from_residual` as a ZST
        //     constant (no place); the payload-copy path once fail-closed ("residual
        //     operand is not a place"). Nothing to copy — `Err(())` is the Err tag alone.
        //     f(Ok(10)) = Ok(11) -> 11.
        (
            "q_unit_err_ok",
            "fn f(r:Result<i32,()>)->Result<i32,()>{ Ok(r?+1) }\n\
             fn main(){ std::process::exit(match f(Ok(10)){Ok(v)=>v,Err(())=>99}); }",
            11,
        ),
        // --- Same unit-error `?`, the Err early-return path. f(Err(())) breaks at the
        //     first `?` and returns `Err(())` via the ZST-residual `from_residual`; main
        //     maps Err(()) -> 99.
        (
            "q_unit_err_early",
            "fn f(r:Result<i32,()>)->Result<i32,()>{ Ok(r?+1) }\n\
             fn main(){ std::process::exit(match f(Err(())){Ok(v)=>v,Err(())=>99}); }",
            99,
        ),
        // --- `?` INSIDE A LOOP (Option), all iterations succeed. step adds 1
        //     while x<=5. run(0): v=1 (acc=1,x=1), v=2 (acc=3,x=2), v=3 (acc=6,x=3).
        //     Some(6). -> 6.
        (
            "q_in_loop_complete",
            "fn step(x:i32)->Option<i32>{ if x>5 {None} else {Some(x+1)} }\n\
             fn run(start:i32)->Option<i32>{ let mut acc=0; let mut x=start; let mut i=0; \
             while i<3 { let v=step(x)?; acc+=v; x=v; i+=1; } Some(acc) }\n\
             fn main(){ let r=match run(0){Some(v)=>v,None=>200}; std::process::exit(r); }",
            6,
        ),
        // --- `?` INSIDE A LOOP (Option) that breaks early via None. run(0) with 10
        //     iterations: x grows 0->1->...; once x>5 step returns None and the `?`
        //     inside the loop returns `None` from `run`; main maps None->200.
        (
            "q_in_loop_breaks_none",
            "fn step(x:i32)->Option<i32>{ if x>5 {None} else {Some(x+1)} }\n\
             fn run(start:i32)->Option<i32>{ let mut acc=0; let mut x=start; let mut i=0; \
             while i<10 { let v=step(x)?; acc+=v; x=v; i+=1; } Some(acc) }\n\
             fn main(){ let r=match run(0){Some(v)=>v,None=>200}; std::process::exit(r); }",
            200,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
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

/// A `?` whose error path requires a NON-IDENTITY `From` conversion (here
/// `From<i32> for Big`, a value transform `|x| Big(x + 1)`) cannot be modeled
/// without running the user `From` body, which the bridge does not lower. It must
/// FAIL CLOSED with a precise diagnostic naming the non-identity conversion —
/// never silently guess the conversion (which would miscompile the error value).
/// LLVM compiles + runs the (valid) program, confirming the program itself is
/// fine and that only the trust-cg modeling gap forces the fail-closed.
#[test]
fn non_identity_from_residual_fails_closed_not_miscompile() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("failclosed");

    let prog = "struct Big(i64);\n\
        impl From<i32> for Big { fn from(x:i32)->Big{ Big(x as i64 + 1) } }\n\
        fn inner(x:i32)->Result<i32,i32>{ if x<0 {Err(3)} else {Ok(x)} }\n\
        fn outer(x:i32)->Result<i32,Big>{ let v=inner(x)?; Ok(v) }\n\
        fn main(){ std::process::exit(match outer(5){Ok(v)=>v,Err(Big(e))=>(e%128) as i32}); }";

    // LLVM compiles + runs the (valid) program: outer(5) = Ok(5) -> exit 5.
    let llvm_bin = compile(&dir, "fc_llvm", prog, None);
    assert_eq!(
        run_exit_code(&llvm_bin),
        5,
        "LLVM must compile+run the non-identity-From program"
    );

    // trust-cg must FAIL CLOSED (compile or link error), never produce a binary
    // that miscompiles the conversion.
    match try_compile(&dir, "fc_tcg", prog, Some(&dylib)) {
        Ok(bin) => {
            // If a binary was somehow produced it must NOT silently miscompile;
            // surface this loudly. (We expect this arm to be unreachable.)
            let exit = run_exit_code(&bin);
            panic!(
                "trust-cg unexpectedly produced a binary for a non-identity `From` `?` \
                 (exit {exit}); a value-transforming From must fail closed, not compile"
            );
        }
        Err(stderr) => {
            assert!(
                stderr.contains("from_residual")
                    && (stderr.contains("not the identity")
                        || stderr.contains("identity")
                        || stderr.contains("value-transforming")),
                "non-identity `From` `?` must fail closed with a precise diagnostic naming the \
                 non-identity conversion. stderr: <<<{stderr}>>>"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
