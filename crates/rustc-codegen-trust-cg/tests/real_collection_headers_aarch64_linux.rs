//! Native Linux AArch64 collection representation qualification. Covers an
//! actual rlib boundary in all four LLVM/CG combinations at O0 through O3.
//! This is an unverified codegen differential, with Trust frontend verification
//! and lowering proof certificates off equally for the relevant compilations.
#![cfg(all(target_os = "linux", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/real_collection_header_cases.rs"]
mod fixture_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::io::Write;
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

fn run(command: &mut Command, log: &Path, limit: Duration) -> ExitStatus {
    let mut output = std::fs::File::create(log).expect("create fixture diagnostics");
    writeln!(output, "{command:?}").expect("record fixture command");
    command
        .stdout(Stdio::from(output.try_clone().expect("clone fixture log")))
        .stderr(Stdio::from(output.try_clone().expect("clone fixture log")));
    let mut child = command.spawn().expect("execute native fixture command");
    let started = Instant::now();
    loop {
        match child.try_wait().expect("poll native fixture command") {
            Some(status) => {
                writeln!(output, "status={status:?}").expect("record fixture status");
                return status;
            }
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                writeln!(output, "timed out after {limit:?}").expect("record timeout");
                panic!("fixture timed out; diagnostics {}", log.display());
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    }
}

fn compile(
    dir: &Path,
    source: &Path,
    output: &Path,
    backend: Option<&Path>,
    opt: u8,
    library: Option<&Path>,
) {
    compile_with_panic(dir, source, output, backend, opt, library, "abort");
}

fn compile_with_panic(
    dir: &Path,
    source: &Path,
    output: &Path,
    backend: Option<&Path>,
    opt: u8,
    library: Option<&Path>,
    panic_strategy: &str,
) {
    let mut command = toolchain_support::rustc_command_with_edition("2024");
    command
        .arg(format!("-Cpanic={panic_strategy}"))
        .args(["-Coverflow-checks=off", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"));
    if let Some(backend) = backend {
        command.arg(format!("-Zcodegen-backend={}", backend.display()));
        command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    if let Some(library) = library {
        command
            .arg("--crate-name=caller")
            .arg("--extern")
            .arg(format!("c={}", library.display()));
    } else {
        command.args(["--crate-type=rlib", "--crate-name=c"]);
    }
    command.arg(source).arg("-o").arg(output).current_dir(dir);
    let log = output.with_extension("compile.log");
    let status = run(&mut command, &log, Duration::from_secs(300));
    assert!(
        status.success(),
        "compile failed: {status:?}; {}",
        log.display()
    );
}

#[test]
fn real_collection_headers_cross_backend() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    assert_eq!(
        fixture_support::CASES.len(),
        40,
        "review the collection matrix denominator"
    );
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-real-collection-header.XXXXXX"])
        .output()
        .expect("create native fixture directory");
    assert!(temp.status.success());
    let root = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("real collection header artifacts: {}", root.display());
    let mut cells = 0;
    for case in fixture_support::CASES {
        let dir = root.join(case.name);
        std::fs::create_dir(&dir).expect("create case directory");
        let callee = dir.join("callee.rs");
        let caller = dir.join("caller.rs");
        std::fs::write(&callee, format!("#[inline(never)]\n{}\n", case.callee))
            .expect("write callee");
        std::fs::write(&caller, format!("extern crate c;\nfn main(){{let answer={{{}}};std::process::exit(answer as i32);}}\n", case.caller_body)).expect("write caller");
        for opt in 0..=3 {
            for callee_cg in [false, true] {
                let rlib = dir.join(format!("libc_{callee_cg}_{opt}.rlib"));
                compile(
                    &dir,
                    &callee,
                    &rlib,
                    callee_cg.then_some(backend.as_path()),
                    opt,
                    None,
                );
                for caller_cg in [false, true] {
                    let bin = dir.join(format!("caller_{callee_cg}_{caller_cg}_{opt}"));
                    compile(
                        &dir,
                        &caller,
                        &bin,
                        caller_cg.then_some(backend.as_path()),
                        opt,
                        Some(&rlib),
                    );
                    let log = bin.with_extension("run.log");
                    let status = run(&mut Command::new(&bin), &log, Duration::from_secs(30));
                    assert_eq!(
                        status.code(),
                        Some(case.expected),
                        "{} O{opt} callee_cg={callee_cg} caller_cg={caller_cg}: {:?}; {}",
                        case.name,
                        status,
                        log.display()
                    );
                    cells += 1;
                }
            }
        }
    }
    assert_eq!(cells, 640, "every declared collection cell must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during collection execution"
    );
    eprintln!(
        "TCG_REAL_COLLECTION_HEADER_XBACK cells={cells} shapes={} optimization_levels=4 combinations=4 lexical_drops=on frontend=off certs=off",
        fixture_support::CASES.len()
    );
    if std::env::var_os("TRUST_COLLECTION_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained collection artifacts: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).expect("remove successful fixture directory");
    }
}

/// LLVM constructs and owns the real custom allocator. The bridge previously
/// skipped its deallocation callback even though a ZST allocator is observable.
#[test]
fn custom_zst_box_allocator_preserves_deallocation_callback() {
    custom_zst_allocator_preserves_deallocation_callback(
        "box",
        "Box<Vec<u64>,custombox::Counting>",
    );
}

#[test]
fn custom_zst_vec_allocator_preserves_deallocation_callback() {
    custom_zst_allocator_preserves_deallocation_callback("vec", "Vec<u64,custombox::Counting>");
}

fn custom_zst_allocator_preserves_deallocation_callback(shape: &str, consumer_ty: &str) {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-custom-box-allocator.XXXXXX"])
        .output()
        .expect("create custom allocator fixture directory");
    assert!(temp.status.success());
    let root = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    let provider_source = root.join("provider.rs");
    let consumer_source = root.join("consumer.rs");
    let caller_source = root.join("caller.rs");
    std::fs::write(&provider_source, r#"#![feature(allocator_api)]
use std::alloc::{Allocator,AllocError,Global,Layout};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize,Ordering};
static DEALLOCS:AtomicUsize=AtomicUsize::new(0);
#[derive(Clone,Copy)] pub struct Counting;
unsafe impl Allocator for Counting {
 fn allocate(&self,layout:Layout)->Result<NonNull<[u8]>,AllocError>{Global.allocate(layout)}
 unsafe fn deallocate(&self,ptr:NonNull<u8>,layout:Layout){DEALLOCS.fetch_add(1,Ordering::SeqCst);unsafe {Global.deallocate(ptr,layout)}}
}
pub fn make_box()->Box<Vec<u64>,Counting>{Box::new_in(vec![7u64,11,19],Counting)}
pub fn make_vec()->Vec<u64,Counting>{let mut v=Vec::with_capacity_in(3,Counting);v.extend([7,11,19]);v}
pub fn reset(){DEALLOCS.store(0,Ordering::SeqCst)}
pub fn count()->usize{DEALLOCS.load(Ordering::SeqCst)}
"#).unwrap();
    std::fs::write(
        &consumer_source,
        r#"#![feature(allocator_api)]
extern crate custombox;
#[inline(never)] pub fn consume(_v:VALUE_TY)->usize {7}
"#
        .replace("VALUE_TY", consumer_ty),
    )
    .unwrap();
    std::fs::write(&caller_source, r#"extern crate custombox;
extern crate boxconsumer;
fn main(){let v=custombox::make();custombox::reset();let r=boxconsumer::consume(v);if r!=7{std::process::exit(1)} if custombox::count()!=1{std::process::exit(2)}}
"#.replace("custombox::make()", &format!("custombox::make_{shape}()"))).unwrap();
    for opt in [0, 2] {
        let base = || {
            let mut command = toolchain_support::rustc_command_with_edition("2024");
            command
                .arg("-Cpanic=abort")
                .arg(format!("-Copt-level={opt}"));
            command.current_dir(&root);
            command
        };
        let provider = root.join(format!("libcustombox_O{opt}.rlib"));
        let mut command = base();
        command
            .args(["--crate-type=rlib", "--crate-name=custombox"])
            .arg(&provider_source)
            .arg("-o")
            .arg(&provider);
        let log = root.join(format!("provider_O{opt}.log"));
        assert!(
            run(&mut command, &log, Duration::from_secs(300)).success(),
            "LLVM allocation provider failed: {}",
            log.display()
        );
        let llvm_consumer = root.join(format!("libboxconsumer_llvm_O{opt}.rlib"));
        let mut command = base();
        command
            .args(["--crate-type=rlib", "--crate-name=boxconsumer"])
            .arg(&consumer_source)
            .arg("--extern")
            .arg(format!("custombox={}", provider.display()))
            .arg("-o")
            .arg(&llvm_consumer);
        let log = root.join(format!("consumer_llvm_O{opt}.log"));
        assert!(
            run(&mut command, &log, Duration::from_secs(300)).success(),
            "LLVM consumer control failed: {}",
            log.display()
        );
        let control = root.join(format!("llvm_control_O{opt}"));
        let mut command = base();
        command
            .arg(&caller_source)
            .arg("--extern")
            .arg(format!("custombox={}", provider.display()))
            .arg("--extern")
            .arg(format!("boxconsumer={}", llvm_consumer.display()))
            .arg("-L")
            .arg(format!("dependency={}", root.display()))
            .arg("-o")
            .arg(&control);
        let log = root.join(format!("control_compile_O{opt}.log"));
        assert!(run(&mut command, &log, Duration::from_secs(300)).success());
        let log = root.join(format!("control_run_O{opt}.log"));
        assert_eq!(
            run(&mut Command::new(&control), &log, Duration::from_secs(30)).code(),
            Some(0),
            "LLVM must invoke the custom deallocator exactly once"
        );
        let output = root.join(format!("libboxconsumer_cg_O{opt}.rlib"));
        let mut command = base();
        command
            .args(["--crate-type=rlib", "--crate-name=boxconsumer"])
            .arg(&consumer_source)
            .arg("--extern")
            .arg(format!("custombox={}", provider.display()))
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
            .arg("-o")
            .arg(&output);
        let log = root.join(format!("consumer_cg_O{opt}.log"));
        assert!(
            run(&mut command, &log, Duration::from_secs(300)).success(),
            "CG custom {shape} consumer failed: {}",
            log.display()
        );
        let control = root.join(format!("cg_control_O{opt}"));
        let mut command = base();
        command
            .arg(&caller_source)
            .arg("--extern")
            .arg(format!("custombox={}", provider.display()))
            .arg("--extern")
            .arg(format!("boxconsumer={}", output.display()))
            .arg("-L")
            .arg(format!("dependency={}", root.display()))
            .arg("-o")
            .arg(&control);
        let log = root.join(format!("cg_control_compile_O{opt}.log"));
        assert!(run(&mut command, &log, Duration::from_secs(300)).success());
        let log = root.join(format!("cg_control_run_O{opt}.log"));
        assert_eq!(
            run(&mut Command::new(&control), &log, Duration::from_secs(30)).code(),
            Some(0),
            "CG consumer must invoke custom {shape} deallocator exactly once"
        );
    }
    assert_eq!(
        std::fs::read(&backend).unwrap(),
        backend_before,
        "backend changed during custom allocator controls"
    );
    if std::env::var_os("TRUST_COLLECTION_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained custom allocator controls: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).unwrap();
    }
}

/// Returning the actual header across a non-inlined rlib boundary prevents
/// LLVM from eliding an allocation whose only use is a constant capacity.
#[test]
fn collection_constructor_overflow_and_null_abort() {
    use std::os::unix::process::ExitStatusExt;
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-constructor-errors.XXXXXX"])
        .output()
        .expect("create allocation-error fixture directory");
    assert!(temp.status.success());
    let root = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    let callee = root.join("lib.rs");
    std::fs::write(
        &callee,
        "#[inline(never)]\npub fn f(n:usize)->Vec<u64> {Vec::<u64>::with_capacity(n)}\n",
    )
    .unwrap();
    let overflow = root.join("overflow.rs");
    std::fs::write(&overflow, "extern crate c;fn main(){let n=std::hint::black_box(usize::MAX/8+1);let v=c::f(n);std::hint::black_box(v.as_ptr());std::process::exit(0)}\n").unwrap();
    let isize_overflow = root.join("isize_overflow.rs");
    std::fs::write(&isize_overflow, "extern crate c;fn main(){let n=std::hint::black_box(isize::MAX as usize/8+1);let v=c::f(n);std::hint::black_box(v.as_ptr());std::process::exit(0)}\n").unwrap();
    let null = root.join("null.rs");
    std::fs::write(&null, r#"extern crate c;
use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicBool,Ordering};
struct NullWhenArmed;
static ARMED:AtomicBool=AtomicBool::new(false);
unsafe impl GlobalAlloc for NullWhenArmed {
 unsafe fn alloc(&self,layout:Layout)->*mut u8 {if ARMED.load(Ordering::SeqCst)&&layout.size()==24&&layout.align()==8 {std::ptr::null_mut()} else {unsafe {System.alloc(layout)}}}
 unsafe fn dealloc(&self,p:*mut u8,layout:Layout){unsafe {System.dealloc(p,layout)}}
}
#[global_allocator] static ALLOC:NullWhenArmed=NullWhenArmed;
fn main(){ARMED.store(true,Ordering::SeqCst);let v=c::f(std::hint::black_box(3));std::hint::black_box(v.as_ptr());std::process::exit(0)}
"#).unwrap();
    let mut cells = 0;
    for opt in [0, 1, 2, 3] {
        for (name, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
            let library = root.join(format!("libc_{name}_{opt}.rlib"));
            compile(&root, &callee, &library, selected, opt, None);
            for (shape, source) in [
                ("overflow", &overflow),
                ("isize_overflow", &isize_overflow),
                ("null", &null),
            ] {
                let binary = root.join(format!("{shape}_{name}_{opt}"));
                // The allocation-provider caller is always independently built
                // with LLVM, so only the callee constructor backend varies.
                compile(&root, source, &binary, None, opt, Some(&library));
                let log = binary.with_extension("run.log");
                let status = run(&mut Command::new(&binary), &log, Duration::from_secs(30));
                assert_eq!(
                    status.signal(),
                    Some(6),
                    "{shape} constructor must SIGABRT before returning an invalid header; backend={name}, O{opt}, status={status:?}; {}",
                    log.display()
                );
                cells += 1;
            }
        }
    }
    assert_eq!(cells, 24, "every allocator error control must execute");
    assert_eq!(
        std::fs::read(&backend).unwrap(),
        backend_before,
        "backend changed during allocator error controls"
    );
    if std::env::var_os("TRUST_COLLECTION_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained constructor errors: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).unwrap();
    }
}

/// A real panic must cross the returned-header ABI, run the callee's Guard,
/// drop an already-owned Vec buffer, and be caught by the LLVM-built caller.
#[test]
fn collection_capacity_unwind_cleanup_and_zero_allocations() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-capacity-unwind.XXXXXX"])
        .output()
        .expect("create unwind fixture directory");
    assert!(temp.status.success());
    let root = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    let mut cells = 0;
    for (shape, callee_source, caller_source) in [
        (
            "unwind",
            include_str!("support/collection_allocation_unwind_callee.rs"),
            include_str!("support/collection_allocation_unwind_caller.rs"),
        ),
        (
            "zero",
            include_str!("support/collection_allocation_zero_callee.rs"),
            include_str!("support/collection_allocation_zero_caller.rs"),
        ),
    ] {
        let callee = root.join(format!("{shape}-callee.rs"));
        let caller = root.join(format!("{shape}-caller.rs"));
        std::fs::write(&callee, callee_source).unwrap();
        std::fs::write(&caller, caller_source).unwrap();
        for opt in 0..=3 {
            for (name, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                let library = root.join(format!("libc_{shape}_{name}_{opt}.rlib"));
                compile_with_panic(&root, &callee, &library, selected, opt, None, "unwind");
                let binary = root.join(format!("{shape}_{name}_{opt}"));
                compile_with_panic(&root, &caller, &binary, None, opt, Some(&library), "unwind");
                let log = binary.with_extension("run.log");
                let status = run(&mut Command::new(&binary), &log, Duration::from_secs(30));
                assert_eq!(
                    status.code(),
                    Some(0),
                    "{shape} O{opt} backend={name} must preserve caught capacity panic, lexical drops and zero-allocation headers; {status:?}; {}",
                    log.display()
                );
                cells += 1;
            }
        }
    }
    assert_eq!(cells, 16, "every unwind/zero control must execute");
    assert_eq!(
        std::fs::read(&backend).unwrap(),
        backend_before,
        "backend changed during unwind controls"
    );
    if std::env::var_os("TRUST_COLLECTION_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained capacity unwind controls: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).unwrap();
    }
}

/// Reserve guards the byte bound after addition succeeds and invokes the
/// actual OOM policy before committing a null resized pointer to the header.
#[test]
fn collection_growth_byte_bounds_and_null_default_handler() {
    use std::os::unix::process::ExitStatusExt;
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-growth-errors.XXXXXX"])
        .output()
        .expect("create growth fixture directory");
    assert!(temp.status.success());
    let root = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    let mut callers = Vec::new();
    for (shape, request) in [
        ("usize_bytes", "usize::MAX/8"),
        ("isize_bytes", "isize::MAX as usize/8"),
    ] {
        let source = root.join(format!("{shape}-caller.rs"));
        std::fs::write(&source, format!("extern crate c;fn main(){{let v=c::f(std::hint::black_box({request}));std::hint::black_box(v.as_ptr());std::hint::black_box(v.len());std::process::exit(0)}}\n")).unwrap();
        callers.push((shape, source));
    }
    let null_source = root.join("null-caller.rs");
    std::fs::write(&null_source, r#"extern crate c;
use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicBool,Ordering};
struct NullReallocWhenArmed;
static ARMED:AtomicBool=AtomicBool::new(false);
unsafe impl GlobalAlloc for NullReallocWhenArmed {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {unsafe {System.alloc(l)}}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){unsafe {System.dealloc(p,l)}}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {if ARMED.load(Ordering::SeqCst)&&l.size()==32&&l.align()==8&&n==64 {std::ptr::null_mut()} else {unsafe {System.realloc(p,l,n)}}}
}
#[global_allocator] static ALLOC:NullReallocWhenArmed=NullReallocWhenArmed;
fn main(){ARMED.store(true,Ordering::SeqCst);let v=c::f(std::hint::black_box(7));std::hint::black_box(v.as_ptr());std::hint::black_box(v.len());std::process::exit(0)}
"#).unwrap();
    callers.push(("null", null_source));
    let mut cells = 0;
    for method in ["reserve", "reserve_exact"] {
        let callee = root.join(format!("{method}-callee.rs"));
        std::fs::write(&callee, format!("#[inline(never)]\npub fn f(n:usize)->Vec<u64>{{let mut v=Vec::with_capacity(4);v.push(7);v.{method}(n);v}}\n")).unwrap();
        for opt in 0..=3 {
            for (name, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                let library = root.join(format!("libc_{method}_{name}_{opt}.rlib"));
                compile(&root, &callee, &library, selected, opt, None);
                for (shape, caller) in &callers {
                    let binary = root.join(format!("{method}_{shape}_{name}_{opt}"));
                    compile(&root, caller, &binary, None, opt, Some(&library));
                    let log = binary.with_extension("run.log");
                    let status = run(&mut Command::new(&binary), &log, Duration::from_secs(30));
                    assert_eq!(
                        status.signal(),
                        Some(6),
                        "{method}/{shape} O{opt} backend={name} must SIGABRT through the source capacity/OOM policy; {status:?}; {}",
                        log.display()
                    );
                    cells += 1;
                }
            }
        }
    }
    assert_eq!(cells, 48, "every growth error control must execute");
    assert_eq!(
        std::fs::read(&backend).unwrap(),
        backend_before,
        "backend changed during growth error controls"
    );
    if std::env::var_os("TRUST_COLLECTION_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained growth error controls: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).unwrap();
    }
}

/// Real std OOM hooks receive the requested Layout across an independent rlib boundary.
#[test]
fn collection_allocation_error_preserves_std_hook_and_layout() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-oom-hook.XXXXXX"])
        .output()
        .expect("create OOM hook fixture directory");
    assert!(temp.status.success());
    let root = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    let constructor = root.join("constructor.rs");
    let realloc = root.join("realloc.rs");
    let caller = root.join("caller.rs");
    std::fs::write(
        &constructor,
        r#"#[inline(never)] pub fn f(n:usize)->Vec<u64>{Vec::with_capacity(n)}
"#,
    )
    .unwrap();
    std::fs::write(&realloc, r#"#[inline(never)] pub fn f(n:usize)->Vec<u64>{let mut v=Vec::with_capacity(4);v.push(7);v.reserve_exact(n);v}
"#).unwrap();
    std::fs::write(&caller, r#"#![feature(alloc_error_hook)]
extern crate c;
use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicBool,Ordering};
struct ArmedNull;
static ARMED:AtomicBool=AtomicBool::new(false);
unsafe impl GlobalAlloc for ArmedNull {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {
  if cfg!(constructor)&&ARMED.load(Ordering::SeqCst)&&l.size()==24&&l.align()==8 {std::ptr::null_mut()} else {unsafe{System.alloc(l)}}
 }
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){unsafe{System.dealloc(p,l)}}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {
  if cfg!(realloc_case)&&ARMED.load(Ordering::SeqCst)&&l.size()==32&&l.align()==8&&n==64 {std::ptr::null_mut()} else {unsafe{System.realloc(p,l,n)}}
 }
}
#[global_allocator] static ALLOC:ArmedNull=ArmedNull;
fn main(){
 std::alloc::set_alloc_error_hook(|l| {
  let expected=if cfg!(constructor){24}else{64};
  std::process::exit(if l.size()==expected&&l.align()==8 {73}else{74});
 });
 ARMED.store(true,Ordering::SeqCst);
 let n=if cfg!(constructor){3}else{7};
 let v=c::f(std::hint::black_box(n));
 std::hint::black_box(v.as_ptr());std::hint::black_box(v.len());
 std::process::exit(2);
}
"#).unwrap();
    let mut cells = 0;
    for panic in ["abort", "unwind"] {
        for opt in [0, 1, 2, 3] {
            for (shape, source, cfg) in [
                ("constructor", &constructor, "constructor"),
                ("realloc", &realloc, "realloc_case"),
            ] {
                for (name, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                    let stem = format!("{panic}_{shape}_{name}_O{opt}");
                    let library = root.join(format!("libc_{stem}.rlib"));
                    let binary = root.join(&stem);
                    let base = || {
                        let mut command = toolchain_support::rustc_command_with_edition("2024");
                        command
                            .arg(format!("-Cpanic={panic}"))
                            .arg(format!("-Copt-level={opt}"))
                            .args(["-Coverflow-checks=off", "-Ccodegen-units=1"])
                            .current_dir(&root);
                        command
                    };
                    let mut command = base();
                    command.args(["--crate-type=rlib", "--crate-name=c"]);
                    if let Some(selected) = selected {
                        command
                            .arg(format!("-Zcodegen-backend={}", selected.display()))
                            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
                    }
                    command.arg(source).arg("-o").arg(&library);
                    let log = root.join(format!("{stem}_callee.log"));
                    assert!(
                        run(&mut command, &log, Duration::from_secs(300)).success(),
                        "callee compile failed: {}",
                        log.display()
                    );
                    // Only the callee varies; the hook and GlobalAlloc provider are LLVM-built.
                    let mut command = base();
                    command
                        .args([
                            "--crate-name=caller",
                            "--cfg",
                            cfg,
                            "--check-cfg=cfg(constructor,realloc_case)",
                        ])
                        .arg(&caller)
                        .arg("--extern")
                        .arg(format!("c={}", library.display()))
                        .arg("-o")
                        .arg(&binary);
                    let log = root.join(format!("{stem}_caller.log"));
                    assert!(
                        run(&mut command, &log, Duration::from_secs(300)).success(),
                        "LLVM provider compile failed: {}",
                        log.display()
                    );
                    let log = root.join(format!("{stem}_run.log"));
                    let status = run(&mut Command::new(&binary), &log, Duration::from_secs(30));
                    assert_eq!(
                        status.code(),
                        Some(73),
                        "OOM must call the actual std hook with exact bytes/align; {stem}; status={status:?}; {}",
                        log.display()
                    );
                    cells += 1;
                }
            }
        }
    }
    assert_eq!(
        cells, 32,
        "all hook, panic strategy and backend controls execute"
    );
    assert_eq!(
        std::fs::read(&backend).unwrap(),
        backend_before,
        "backend changed during OOM hook controls"
    );
    if std::env::var_os("TRUST_COLLECTION_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained OOM hook controls: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).unwrap();
    }
}

/// CapacityOverflow remains a real panic under panic=abort: the configured
/// std hook must run before termination across an independently LLVM-called rlib.
/// Constructor/exact reserve exercise the byte bound; reserve exercises addition
/// wrap. Complete payload/file/line/column records must equal the LLVM observation.
#[test]
fn collection_capacity_abort_preserves_panic_hook() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-capacity-panic-hook.XXXXXX"])
        .output()
        .expect("create panic-hook fixture directory");
    assert!(temp.status.success());
    let root = std::path::PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    let mut cells = 0;
    for (shape, body, request) in [
        (
            "constructor",
            "Vec::<u64>::with_capacity(n)",
            "isize::MAX as usize/8+1",
        ),
        (
            "reserve",
            "{let mut v=Vec::<u64>::with_capacity(4);v.push(7);v.reserve(n);v}",
            "usize::MAX",
        ),
        (
            "reserve_exact",
            "{let mut v=Vec::<u64>::with_capacity(4);v.push(7);v.reserve_exact(n);v}",
            "isize::MAX as usize/8",
        ),
    ] {
        let callee = root.join(format!("{shape}-callee.rs"));
        let caller = root.join(format!("{shape}-caller.rs"));
        std::fs::write(
            &callee,
            format!("#[inline(never)]\npub fn f(n:usize)->Vec<u64>{{{body}}}\n"),
        )
        .unwrap();
        let caller_template = r#"extern crate c;
fn main() {
    std::panic::set_hook(Box::new(|info| {
        let text = if let Some(s) = info.payload().downcast_ref::<&str>() { *s }
            else if let Some(s) = info.payload().downcast_ref::<String>() { s.as_str() }
            else { "<other>" };
        let location = info.location().expect("capacity panic location");
        eprintln!("CAPACITY_HOOK|{}|{}|{}|{}", text, location.file(), location.line(), location.column());
        std::process::exit(73);
    }));
    let v = c::f(std::hint::black_box(REQUEST));
    std::hint::black_box(v.as_ptr());
    std::process::exit(2);
}
"#;
        std::fs::write(&caller, caller_template.replace("REQUEST", request)).unwrap();
        for opt in 0..=3 {
            let mut llvm_observation = None;
            for (name, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                let library = root.join(format!("libc_{shape}_{name}_{opt}.rlib"));
                compile(&root, &callee, &library, selected, opt, None);
                let binary = root.join(format!("{shape}_{name}_{opt}"));
                compile(&root, &caller, &binary, None, opt, Some(&library));
                let log = binary.with_extension("run.log");
                let status = run(&mut Command::new(&binary), &log, Duration::from_secs(30));
                assert_eq!(
                    status.code(),
                    Some(73),
                    "{shape} O{opt} backend={name} must invoke the configured panic hook before abort; {status:?}; {}",
                    log.display()
                );
                let raw = std::fs::read(&log).expect("read hook observation");
                let text = std::str::from_utf8(&raw).expect("hook output is UTF8");
                // The harness keeps its command/status alongside child output.
                // Compare the entire unique child marker, retaining the full log.
                let records: Vec<_> = text
                    .lines()
                    .filter(|line| line.starts_with("CAPACITY_HOOK|"))
                    .collect();
                assert_eq!(records.len(), 1, "one complete child hook observation");
                let observation = records[0].to_owned();
                let fields: Vec<_> = observation.split('|').collect();
                assert_eq!(
                    fields.len(),
                    5,
                    "payload and full source location must be recorded"
                );
                assert_eq!(fields[0], "CAPACITY_HOOK");
                assert_eq!(fields[1], "capacity overflow");
                assert!(
                    !fields[2].is_empty()
                        && fields[3].parse::<u32>().unwrap() > 0
                        && fields[4].parse::<u32>().unwrap() > 0,
                    "real source location"
                );
                if name == "llvm" {
                    llvm_observation = Some(observation);
                } else {
                    assert_eq!(
                        Some(&observation),
                        llvm_observation.as_ref(),
                        "{shape} O{opt} must preserve LLVM's exact capacity-panic payload/file/line/column"
                    );
                }
                cells += 1;
            }
        }
    }
    assert_eq!(cells, 24, "all capacity panic-hook controls must execute");
    assert_eq!(
        std::fs::read(&backend).unwrap(),
        backend_before,
        "backend changed during capacity panic-hook controls"
    );
    if std::env::var_os("TRUST_COLLECTION_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained capacity panic-hook controls: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).unwrap();
    }
}
