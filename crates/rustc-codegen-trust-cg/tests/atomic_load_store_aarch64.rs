// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Native diagnostic only: Trust verification and proof certificates are off.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const PREFIX: &str = "#![feature(core_intrinsics,adt_const_params)]\n#![allow(internal_features,incomplete_features)]\nuse core::intrinsics::{self as i,AtomicOrdering as O};\n";
struct Temporary(PathBuf);
impl Temporary {
    fn new(name: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-atomic-{name}-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Temporary {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("failed atomic fixtures retained at {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).expect("remove successful atomic fixtures");
        }
    }
}
struct Run {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}
fn bounded(command: &mut Command, root: &Path, label: &str, seconds: u64) -> Run {
    let stdout = root.join(format!("{label}.stdout"));
    let stderr = root.join(format!("{label}.stderr"));
    let description = format!("{command:?}");
    command
        .stdin(Stdio::null())
        .stdout(File::create(&stdout).unwrap())
        .stderr(File::create(&stderr).unwrap());
    let mut child = command.spawn().expect("spawn atomic fixture step");
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            fs::write(
                root.join(format!("{label}.command")),
                format!("{description}\nstatus: {status}\n"),
            )
            .unwrap();
            return Run {
                status,
                stdout: fs::read(stdout).unwrap(),
                stderr: fs::read(stderr).unwrap(),
            };
        }
        if started.elapsed() >= Duration::from_secs(seconds) {
            child.kill().expect("kill timed-out atomic fixture child");
            child.wait().expect("reap timed-out atomic fixture child");
            panic!("atomic fixture timed out: {description}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}
fn compile(
    root: &Path,
    backend: Option<&Path>,
    name: &str,
    body: &str,
    opt: u32,
    panic: &str,
) -> (Run, PathBuf) {
    let lane = if backend.is_some() { "cg" } else { "llvm" };
    let label = format!("{name}-O{opt}-{panic}-{lane}");
    let source = root.join(format!("{label}.rs"));
    fs::write(&source, format!("{PREFIX}{body}\n")).unwrap();
    let exe = root.join(&label);
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    for (key, _) in std::env::vars_os() {
        if key
            .to_str()
            .is_some_and(|k| k.starts_with("TRUST_CG_") || k.starts_with("TCG_"))
        {
            command.env_remove(key);
        }
    }
    command
        .args([
            "--target",
            "aarch64-apple-darwin",
            "--crate-name",
            "atomic_guest",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Cpanic={panic}"));
    if let Some(backend) = backend {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command.arg(&source).arg("-o").arg(&exe);
    (
        bounded(&mut command, root, &format!("{label}-compile"), 300),
        exe,
    )
}
fn execute(root: &Path, exe: &Path) -> Run {
    let mut command = Command::new("/bin/sh");
    command
        .args(["-c", "ulimit -c 0 && exec \"$@\"", "atomic-fixture"])
        .arg(exe);
    bounded(
        &mut command,
        root,
        &format!("{}-run", exe.file_name().unwrap().to_str().unwrap()),
        30,
    )
}
fn assert_compiled(run: &Run) {
    assert!(
        run.status.success(),
        "compile failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
}
fn assert_refused(run: &Run, reason: &str) {
    assert!(!run.status.success(), "negative atomic case was admitted");
    assert!(
        String::from_utf8_lossy(&run.stderr).contains(reason),
        "wrong refusal (wanted {reason}): {}",
        String::from_utf8_lossy(&run.stderr)
    );
}

#[test]
fn atomic_nonvolatile_accesses_match_llvm_aarch64() {
    darwin_native::require("atomic_nonvolatile_accesses_match_llvm_aarch64", &[]);
    let root = Temporary::new("ordinary");
    let backend = backend_artifact_support::current_test_backend();
    let cases = [
        // Keep the original inlined atomic regressions: introducing a call
        // boundary can change scalar-cell selection and hide their old refusal.
        // Separate runtime-input controls read before and after non-inlined
        // updates, covering stale snapshots and valid bool/char layouts.
        (
            "local_relaxed",
            r#"use std::sync::atomic::{AtomicU32,Ordering}; fn main() {let a=AtomicU32::new(19); a.store(73,Ordering::Relaxed); println!("{}",a.load(Ordering::Relaxed));}"#,
            "73\n",
        ),
        (
            "local_release_acquire",
            r#"use std::sync::atomic::{AtomicU32,Ordering}; fn main() {let a=AtomicU32::new(19); a.store(73,Ordering::Release); println!("{}",a.load(Ordering::Acquire));}"#,
            "73\n",
        ),
        (
            "local_seqcst",
            r#"use std::sync::atomic::{AtomicU32,Ordering}; fn main() {let a=AtomicU32::new(19); a.store(73,Ordering::SeqCst); println!("{}",a.load(Ordering::SeqCst));}"#,
            "73\n",
        ),
        (
            "local_relaxed_cross_call",
            r#"use std::sync::atomic::{AtomicU32,Ordering}; use std::hint::black_box as bb; #[inline(never)] fn update(a:&AtomicU32,v:u32){a.store(v,Ordering::Relaxed);} #[inline(never)] fn read(a:&AtomicU32)->u32{a.load(Ordering::Relaxed)} fn main(){let a=AtomicU32::new(bb(19));let before=read(&a);update(&a,bb(73));let after=read(&a);println!("{before} {after}");}"#,
            "19 73\n",
        ),
        (
            "local_release_acquire_cross_call",
            r#"use std::sync::atomic::{AtomicU32,Ordering}; use std::hint::black_box as bb; #[inline(never)] fn update(a:&AtomicU32,v:u32){a.store(v,Ordering::Release);} #[inline(never)] fn read(a:&AtomicU32)->u32{a.load(Ordering::Acquire)} fn main(){let a=AtomicU32::new(bb(19));let before=read(&a);update(&a,bb(73));let after=read(&a);println!("{before} {after}");}"#,
            "19 73\n",
        ),
        (
            "local_seqcst_cross_call",
            r#"use std::sync::atomic::{AtomicU32,Ordering}; use std::hint::black_box as bb; #[inline(never)] fn update(a:&AtomicU32,v:u32){a.store(v,Ordering::SeqCst);} #[inline(never)] fn read(a:&AtomicU32)->u32{a.load(Ordering::SeqCst)} fn main(){let a=AtomicU32::new(bb(19));let before=read(&a);update(&a,bb(73));let after=read(&a);println!("{before} {after}");}"#,
            "19 73\n",
        ),
        (
            "memory_u32",
            r#"use std::hint::black_box as bb; #[repr(C,align(4))] struct Aligned(u32); #[repr(C)] struct Atom(std::cell::UnsafeCell<Aligned>); impl Atom{#[inline(always)] fn new(v:u32)->Self{unsafe{std::mem::transmute(v)}} #[inline(always)] fn ptr(&self)->*mut u32{self.0.get().cast::<u32>()}} #[inline(never)] fn update(p:*mut u32,v:u32){unsafe{*p=v;}} #[inline(never)] fn read(p:*const u32)->u32{unsafe{*p}} fn main(){let a=Atom::new(bb(19u32));let p=a.ptr();let before=read(bb(p));update(bb(p),bb(73u32));let after=read(bb(p));println!("{before} {after}");}"#,
            "19 73\n",
        ),
        (
            "memory_i16",
            r#"use std::hint::black_box as bb; #[repr(C,align(2))] struct Aligned(i16); #[repr(C)] struct Atom(std::cell::UnsafeCell<Aligned>); impl Atom{#[inline(always)] fn new(v:i16)->Self{unsafe{std::mem::transmute(v)}} #[inline(always)] fn ptr(&self)->*mut i16{self.0.get().cast::<i16>()}} #[inline(never)] fn update(p:*mut i16,v:i16){unsafe{*p=v;}} #[inline(never)] fn read(p:*const i16)->i16{unsafe{*p}} fn main(){let a=Atom::new(bb(19i16));let p=a.ptr();let before=read(bb(p));update(bb(p),bb(-73i16));let after=read(bb(p));println!("{before} {after}");}"#,
            "19 -73\n",
        ),
        (
            "memory_f32",
            r#"use std::hint::black_box as bb; #[repr(C,align(4))] struct Aligned(f32); #[repr(C)] struct Atom(std::cell::UnsafeCell<Aligned>); impl Atom{ #[inline(always)] fn ptr(&self)->*mut f32{self.0.get().cast::<f32>()}} #[inline(never)] fn update(p:*mut f32,v:f32){unsafe{*p=v;}} #[inline(never)] fn read(p:*const f32)->f32{unsafe{*p}} fn main(){let a:Atom=unsafe{std::mem::transmute(bb(19f32))};let p=a.ptr();let before=read(bb(p));update(bb(p),bb(73.5f32));let after=read(bb(p));println!("{} {}",before.to_bits(),after.to_bits());}"#,
            "1100480512 1116930048\n",
        ),
        (
            "memory_zst",
            r#"use std::hint::black_box as bb; #[repr(C,align(4))] struct Aligned((),u32); #[repr(C)] struct Atom(std::cell::UnsafeCell<Aligned>); impl Atom{#[inline(always)] fn new(v:u32)->Self{unsafe{std::mem::transmute(v)}} #[inline(always)] fn ptr(&self)->*mut u32{self.0.get().cast::<u32>()}} #[inline(never)] fn update(p:*mut u32,v:u32){unsafe{*p=v;}} #[inline(never)] fn read(p:*const u32)->u32{unsafe{*p}} fn main(){let a=Atom::new(bb(19u32));let p=a.ptr();let before=read(bb(p));update(bb(p),bb(73u32));let after=read(bb(p));println!("{before} {after}");}"#,
            "19 73\n",
        ),
        (
            "memory_bool",
            r#"use std::hint::black_box as bb; #[repr(C,align(1))] struct Aligned(bool); #[repr(C)] struct Atom(std::cell::UnsafeCell<Aligned>); impl Atom{ #[inline(always)] fn ptr(&self)->*mut bool{self.0.get().cast::<bool>()}} #[inline(never)] fn update(p:*mut bool,v:bool){unsafe{*p=v;}} #[inline(never)] fn read(p:*const bool)->bool{unsafe{*p}} fn main(){let a:Atom=unsafe{std::mem::transmute(bb(false))};let p=a.ptr();let before=read(bb(p));update(bb(p),bb(true));let after=read(bb(p));println!("{before} {after}");}"#,
            "false true\n",
        ),
        (
            "memory_char",
            r#"use std::hint::black_box as bb; #[repr(C,align(4))] struct Aligned(char); #[repr(C)] struct Atom(std::cell::UnsafeCell<Aligned>); impl Atom{ #[inline(always)] fn ptr(&self)->*mut char{self.0.get().cast::<char>()}} #[inline(never)] fn update(p:*mut char,v:char){unsafe{*p=v;}} #[inline(never)] fn read(p:*const char)->char{unsafe{*p}} fn main(){let a:Atom=unsafe{std::mem::transmute(bb('λ'))};let p=a.ptr();let before=read(bb(p));update(bb(p),bb('界'));let after=read(bb(p));println!("{before} {after}");}"#,
            "λ 界\n",
        ),
        (
            "relaxed",
            "fn main() { let mut x=19u32; unsafe { i::atomic_store::<u32,{O::Relaxed},false>(&mut x,73); } let y=unsafe { i::atomic_load::<u32,{O::Relaxed},false>(&x) }; println!(\"{y}\"); }",
            "73\n",
        ),
        (
            "release_acquire",
            "fn main() { let mut x=19u32; unsafe { i::atomic_store::<u32,{O::Release},false>(&mut x,73); } let y=unsafe { i::atomic_load::<u32,{O::Acquire},false>(&x) }; println!(\"{y}\"); }",
            "73\n",
        ),
        (
            "seqcst",
            "fn main() { let mut x=19u32; unsafe { i::atomic_store::<u32,{O::SeqCst},false>(&mut x,73); } let y=unsafe { i::atomic_load::<u32,{O::SeqCst},false>(&x) }; println!(\"{y}\"); }",
            "73\n",
        ),
        (
            "static",
            "use std::sync::atomic::{AtomicU32,Ordering}; static X:AtomicU32=AtomicU32::new(19); fn main() { X.store(73,Ordering::SeqCst); println!(\"{}\",X.load(Ordering::SeqCst)); }",
            "73\n",
        ),
        (
            "rmw",
            "fn main() { let mut x=19u32; let old=unsafe { i::atomic_xadd::<u32,u32,{O::AcqRel}>(&mut x,54) }; println!(\"{old} {x}\"); }",
            "19 73\n",
        ),
        (
            "pointer",
            "fn main() { let a=19u32; let b=73u32; let mut p=&a as *const u32; unsafe { i::atomic_store::<*const u32,{O::Release},false>(&mut p,&b); } let y=unsafe { i::atomic_load::<*const u32,{O::Acquire},false>(&p) }; println!(\"{}\",unsafe { *y }); }",
            "73\n",
        ),
        (
            "signed_narrow",
            "fn main() { let mut x=19i8; unsafe { i::atomic_store::<i8,{O::SeqCst},false>(&mut x,-73); } let y=unsafe { i::atomic_load::<i8,{O::SeqCst},false>(&x) }; println!(\"{y}\"); }",
            "-73\n",
        ),
        (
            "unsigned_narrow",
            "fn main() { let mut x=19u8; unsafe { i::atomic_store::<u8,{O::SeqCst},false>(&mut x,233); } let y=unsafe { i::atomic_load::<u8,{O::SeqCst},false>(&x) }; println!(\"{y}\"); }",
            "233\n",
        ),
    ];
    let mut cells = 0;
    let mut executions = 0;
    for (name, body, expected) in cases {
        for panic in ["abort", "unwind"] {
            for opt in 0..=3 {
                let mut oracle = None;
                for lane in [None, Some(backend.as_path())] {
                    let (compilation, exe) = compile(&root.0, lane, name, body, opt, panic);
                    assert_compiled(&compilation);
                    let run = execute(&root.0, &exe);
                    assert_eq!(
                        run.status.code(),
                        Some(0),
                        "{name} O{opt} {panic}: {:?}",
                        run.status
                    );
                    assert_eq!(run.stdout, expected.as_bytes(), "{name} O{opt} {panic}");
                    assert!(
                        run.stderr.is_empty(),
                        "{}",
                        String::from_utf8_lossy(&run.stderr)
                    );
                    let outcome = (run.status.code(), run.stdout, run.stderr);
                    if lane.is_none() {
                        oracle = Some(outcome);
                    } else {
                        assert_eq!(Some(outcome), oracle);
                    }
                    executions += 1;
                }
                cells += 1;
            }
        }
    }
    assert_eq!((cells, executions), (160, 320));
    println!(
        "TCG_ATOMIC_NONVOLATILE fixtures=20 cells=160 executions=320 opts=0,1,2,3 panic=abort,unwind"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn volatile_atomics_are_explicitly_refused_aarch64() {
    darwin_native::require("volatile_atomics_are_explicitly_refused_aarch64", &[]);
    let root = Temporary::new("volatile");
    let backend = backend_artifact_support::current_test_backend();
    let cases = [
        (
            "volatile_load",
            "fn main() { let x=73u32; let y=unsafe { i::atomic_load::<u32,{O::Acquire},true>(&x) }; println!(\"{y}\"); }",
        ),
        (
            "volatile_store",
            "fn main() { let mut x=19u32; unsafe { i::atomic_store::<u32,{O::Release},true>(&mut x,73); } println!(\"{x}\"); }",
        ),
    ];
    let mut cells = 0;
    for (name, body) in cases {
        for panic in ["abort", "unwind"] {
            for opt in 0..=3 {
                let (oracle, exe) = compile(&root.0, None, name, body, opt, panic);
                assert_compiled(&oracle);
                let run = execute(&root.0, &exe);
                assert_eq!(run.status.code(), Some(0));
                assert_eq!(run.stdout, b"73\n");
                assert!(run.stderr.is_empty());
                let (cg, _) = compile(&root.0, Some(&backend), name, body, opt, panic);
                assert_refused(&cg, "[TCG-ATOMIC-VOLATILE]");
                cells += 1;
            }
        }
    }
    assert_eq!(cells, 16);
    println!(
        "TCG_ATOMIC_VOLATILE fixtures=2 cells=16 refused=16 llvm_runs=16 opts=0,1,2,3 panic=abort,unwind"
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn atomic_type_and_ordering_contracts_fail_closed_aarch64() {
    darwin_native::require(
        "atomic_type_and_ordering_contracts_fail_closed_aarch64",
        &[],
    );
    let root = Temporary::new("policy");
    let backend = backend_artifact_support::current_test_backend();
    // LLVM compiling an illegal ordering is not authority to weaken the shared
    // trust-ir legality table. These four cases are never executed on either lane.
    let orders = [
        (
            "load_release",
            "fn main() { let x=73u32; let y=unsafe { i::atomic_load::<u32,{O::Release},false>(&x) }; println!(\"{y}\"); }",
            "atomic_load with Release ordering is invalid",
        ),
        (
            "load_acqrel",
            "fn main() { let x=73u32; let y=unsafe { i::atomic_load::<u32,{O::AcqRel},false>(&x) }; println!(\"{y}\"); }",
            "atomic_load with AcqRel ordering is invalid",
        ),
        (
            "store_acquire",
            "fn main() { let mut x=19u32; unsafe { i::atomic_store::<u32,{O::Acquire},false>(&mut x,73); } println!(\"{x}\"); }",
            "atomic_store with Acquire ordering is invalid",
        ),
        (
            "store_acqrel",
            "fn main() { let mut x=19u32; unsafe { i::atomic_store::<u32,{O::AcqRel},false>(&mut x,73); } println!(\"{x}\"); }",
            "atomic_store with AcqRel ordering is invalid",
        ),
    ];
    let types = [
        (
            "bool",
            "fn main() { let x=true; let y=unsafe { i::atomic_load::<bool,{O::Relaxed},false>(&x) }; println!(\"{y}\"); }",
        ),
        (
            "char",
            "fn main() { let x='A'; let y=unsafe { i::atomic_load::<char,{O::Relaxed},false>(&x) }; println!(\"{y}\"); }",
        ),
        (
            "reference",
            "static N:u32=73; static R:&u32=&N; fn main() { let y=unsafe { i::atomic_load::<&u32,{O::Relaxed},false>(&R) }; println!(\"{}\",*y); }",
        ),
        (
            "float",
            "fn main() { let x=73f32; let y=unsafe { i::atomic_load::<f32,{O::Relaxed},false>(&x) }; println!(\"{y}\"); }",
        ),
        (
            "aggregate",
            "#[derive(Clone,Copy)] struct Pair { a:u32,b:u32 } fn main() { let x=Pair{a:19,b:54}; let y=unsafe { i::atomic_load::<Pair,{O::Relaxed},false>(&x) }; println!(\"{}\",y.a+y.b); }",
        ),
    ];
    // Proving a local scalar memory image grants no calling-ABI authority.
    // Keep padded integer arguments and memory-represented float returns
    // rejected when an independently compiled caller uses different registers.
    let layout_abi_cases = [
        (
            "padded_abi",
            r#"#[repr(C,align(8))] struct W(u32); #[inline(never)] fn f(w:W)->u32{std::hint::black_box(w.0)}fn main(){println!("{}",f(W(73)));}"#,
            "73\n",
            "[TCG-ARG-ABI]",
        ),
        (
            "float_return_abi",
            r#"#[repr(C,align(4))]struct W(f32); #[inline(never)]fn f()->W{W(std::hint::black_box(73.5))}fn main(){println!("{}",f().0.to_bits());}"#,
            "1116930048\n",
            "[TCG-RET-ABI]",
        ),
    ];
    let mut layout_abi_refusals = 0;
    let mut llvm_abi_runs = 0;
    let mut order_refusals = 0;
    let mut type_refusals = 0;
    for panic in ["abort", "unwind"] {
        for opt in 0..=3 {
            for (name, body, reason) in orders {
                let (cg, _) = compile(&root.0, Some(&backend), name, body, opt, panic);
                assert_refused(&cg, reason);
                order_refusals += 1;
            }
            for (name, body) in types {
                let (llvm, _) = compile(&root.0, None, name, body, opt, panic);
                assert_refused(&llvm, "expected basic integer or pointer type");
                let (cg, _) = compile(&root.0, Some(&backend), name, body, opt, panic);
                assert_refused(&cg, "[TCG-ATOMIC-TYPE]");
                type_refusals += 1;
            }
            for (name, body, expected, reason) in layout_abi_cases {
                let (llvm, exe) = compile(&root.0, None, name, body, opt, panic);
                assert_compiled(&llvm);
                let run = execute(&root.0, &exe);
                assert_eq!(run.status.code(), Some(0));
                assert_eq!(run.stdout, expected.as_bytes());
                assert!(run.stderr.is_empty());
                llvm_abi_runs += 1;
                let (cg, _) = compile(&root.0, Some(&backend), name, body, opt, panic);
                assert_refused(&cg, reason);
                layout_abi_refusals += 1;
            }
        }
    }
    assert_eq!((order_refusals, type_refusals), (32, 40));
    assert_eq!((layout_abi_refusals, llvm_abi_runs), (16, 16));
    println!(
        "TCG_ATOMIC_POLICY order_fixtures=4 type_fixtures=5 cells=72 refused=72 llvm_type_refusals=40 opts=0,1,2,3 panic=abort,unwind layout_abi_fixtures=2 layout_abi_refusals=16 llvm_abi_runs=16"
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}
