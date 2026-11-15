//! Execute every shared real-program guest with LLVM and CG at O0–O3.
//! This diagnostic differential disables frontend verification and machine
//! certificates explicitly; successful compilation alone is never a match.
#![cfg(all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

include!("real_program_corpus/corpus_guests.rs");

fn backend_arg(backend: &Path) -> OsString {
    let mut arg = OsString::from("-Zcodegen-backend=");
    arg.push(backend);
    arg
}

fn execute(program: &Path) -> Result<i32, String> {
    let mut child = Command::new(program)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|error| format!("cannot execute {}: {error}", program.display()))?;
    let started = Instant::now();
    loop {
        match child.try_wait().map_err(|error| error.to_string())? {
            Some(status) => {
                return status
                    .code()
                    .ok_or_else(|| format!("signal termination: {status}"));
            }
            None if started.elapsed() >= Duration::from_secs(30) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err("native execution timed out".to_owned());
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    }
}

fn compile(dir: &Path, guest: &Guest, opt: u8, backend: Option<&Path>) -> Result<PathBuf, String> {
    compile_with_panic(dir, guest, opt, backend, "abort")
}

/// `compile` with the panic strategy `panic` (`abort` or `unwind`).
fn compile_with_panic(
    dir: &Path,
    guest: &Guest,
    opt: u8,
    backend: Option<&Path>,
    panic: &str,
) -> Result<PathBuf, String> {
    let lane = if backend.is_some() { "cg" } else { "llvm" };
    let src = dir.join(format!("{}.rs", guest.name));
    std::fs::write(&src, guest.src).expect("write shared corpus guest");
    let program = dir.join(format!("{}_{}_O{opt}", guest.name, lane));
    let mut command = toolchain_support::rustc_command();
    command.args([
        "--target",
        host_target_support::AARCH64_TARGET,
        &format!("-Cpanic={panic}"),
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ]);
    command.arg(format!("-Copt-level={opt}"));
    if let Some(backend) = backend {
        command.arg(backend_arg(backend));
        command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let output = command
        .arg("-o")
        .arg(&program)
        .arg(&src)
        .output()
        .expect("invoke the exact backend build compiler");
    std::fs::write(
        dir.join(format!("{}_{}_O{opt}.log", guest.name, lane)),
        &output.stderr,
    )
    .expect("retain compiler diagnostics");
    if !output.status.success() {
        return Err(format!(
            "{lane} compile {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(program)
}

#[test]
fn shared_real_programs_execute_and_match_llvm_at_every_level() {
    assert!(
        toolchain_support::target_std_available(host_target_support::AARCH64_TARGET),
        "native Trust std is required; this runtime matrix cannot skip"
    );
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!(
        "trustcg_real_program_runtime_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create native runtime matrix directory");
    let guests = corpus();
    assert_eq!(
        guests.len(),
        13,
        "shared corpus denominator changed; review the matrix"
    );
    let mut failures = Vec::new();
    let mut executions = 0;
    for opt in 0..=3 {
        for guest in &guests {
            let oracle = compile(&dir, guest, opt, None).and_then(|program| execute(&program));
            let candidate =
                compile(&dir, guest, opt, Some(&backend)).and_then(|program| execute(&program));
            match (oracle, candidate) {
                (Ok(expected), Ok(actual)) => {
                    executions += 2;
                    println!(
                        "TCG_REAL_PROGRAM_RUNTIME guest={} opt={opt} llvm={expected} cg={actual}",
                        guest.name
                    );
                    if actual != expected {
                        failures.push(format!(
                            "{} O{opt} ({}): LLVM {expected}, CG {actual}",
                            guest.name, guest.what
                        ));
                    }
                    if guest.name == "p09_sieve" && expected != 198 {
                        failures.push(format!(
                            "independent fixed sieve oracle changed at O{opt}: {expected} != 198"
                        ));
                    }
                }
                (oracle, candidate) => failures.push(format!(
                    "{} O{opt} ({}): LLVM {oracle:?}, CG {candidate:?}",
                    guest.name, guest.what
                )),
            }
        }
    }
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during native execution"
    );
    assert!(
        failures.is_empty(),
        "runtime corpus failures (artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(executions, guests.len() * 4 * 2);
}

#[test]
fn nested_scalar_raw_borrow_uses_live_stable_storage() {
    let guest = Guest {
        name: "nested_scalar_raw_borrow",
        what: "raw address through scalar wrappers observes whole-local replacement",
        src: r#"
use std::mem::ManuallyDrop;
#[repr(transparent)]
struct Wrap<T>(T);
#[inline(never)]
fn check() -> u64 {
    let mut value = ManuallyDrop::new(Wrap(7u64));
    let pointer = std::hint::black_box(&raw mut (*value).0);
    unsafe { *pointer = 41; }
    let first = value.0;
    value = ManuallyDrop::new(Wrap(47));
    let second = unsafe { *pointer };
    let identity = pointer.cast::<u8>() == (&raw mut value).cast::<u8>();
    first + second + identity as u64
}
fn main() { std::process::exit(check() as i32); }
"#,
    };
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("trustcg_nested_raw_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create raw-borrow runtime directory");
    for opt in 0..=3 {
        for lane in [None, Some(backend.as_path())] {
            let program = compile(&dir, &guest, opt, lane).unwrap();
            assert_eq!(
                execute(&program).unwrap(),
                89,
                "nested raw borrow O{opt}, backend {lane:?}"
            );
        }
    }
}

/// Direct byte formals and address-taken wrapper fields preserve the same
/// initialized byte. Niche/padded neighbors keep their own representations.
#[test]
fn full_range_u8_wrapper_projections_preserve_values_and_aliases() {
    let guest = Guest {
        name: "full_range_u8_wrappers",
        what: "real ExitCode and exact byte wrappers preserve values and aliased writes",
        src: r#"
#![feature(process_exitcode_internals)]
#[repr(transparent)] struct Inner(u8);
#[repr(transparent)] struct Outer(Inner);
#[repr(transparent)] struct NicheInner(std::num::NonZeroU8);
#[repr(transparent)] struct NicheOuter(NicheInner);
#[repr(C)] struct Padded(Inner,u8);
#[inline(never)] fn actual_exitcode(n:u8)->u32 {
    std::hint::black_box(std::process::ExitCode::from(n)).to_i32() as u32
}
#[inline(never)] fn direct(v:Outer)->u32 {v.0.0 as u32}
#[inline(never)] fn as_i32(v:&Inner)->i32 {v.0 as i32}
#[inline(never)] fn to_i32(v:Outer)->i32 {as_i32(&v.0)}
#[inline(never)] fn rewrite(v:&mut Inner,n:u8) {v.0=n;}
#[inline(never)] fn aliased(n:u8)->u32 {
    let mut v=Outer(Inner(n));rewrite(&mut v.0,n^0xa5);v.0.0 as u32
}
#[inline(never)] fn niche(n:u8)->u32 {
    let x=std::num::NonZeroU8::new(n|1).unwrap();
    let v=std::hint::black_box(NicheOuter(NicheInner(x)));v.0.0.get() as u32
}
#[inline(never)] fn padded(n:u8)->u32 {
    let v=std::hint::black_box(Padded(Inner(n),n^0xa5));
    v.0.0 as u32+((v.1 as u32)<<8)
}
fn main() {
    for n in 0u8..=255 {
        let n=std::hint::black_box(n);
        assert_eq!(actual_exitcode(n), n as u32);
        assert_eq!(direct(Outer(Inner(n))), n as u32);
        assert_eq!(to_i32(Outer(Inner(n))), n as i32);
        assert_eq!(aliased(n), (n^0xa5) as u32);
        assert_eq!(niche(n), (n|1) as u32);
        assert_eq!(padded(n), n as u32+(((n^0xa5) as u32)<<8));
    }
}
"#,
    };
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!("trustcg_u8_wrappers_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create u8 wrapper fixture directory");
    let mut cells = 0;
    for opt in 0..=3 {
        for selected in [None, Some(backend.as_path())] {
            let program = compile(&dir, &guest, opt, selected).expect("compile u8 wrapper fixture");
            assert_eq!(
                execute(&program).expect("execute u8 wrapper fixture"),
                0,
                "u8 wrapper oracle failed at O{opt}, CG={}",
                selected.is_some()
            );
            cells += 1;
        }
    }
    assert_eq!(cells, 8, "every wrapper control must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during wrapper controls"
    );
    eprintln!("TCG_U8_WRAPPER_RUNTIME cells=8 checks_per_cell=1536 frontend=off certs=off");
}

/// A counting global allocator for the empty-Vec guests. A free of a zero-byte
/// layout or of a zero-page pointer (an empty Vec's dangling sentinel is its
/// alignment) is counted as `FOREIGN` and never reaches the system allocator,
/// so the defect is an exit-code bit rather than a malloc abort. `check`
/// returns `1 << case` unless the case returned `expected`, freed nothing
/// foreign, freed exactly what it allocated, and freed a buffer iff it owns one.
macro_rules! counting_allocator_prelude {
    () => {
        r#"
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
static FOREIGN: AtomicUsize = AtomicUsize::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        DEALLOCS.fetch_add(1, Ordering::SeqCst);
        if layout.size() == 0 || (pointer as usize) < 4096 {
            FOREIGN.fetch_add(1, Ordering::SeqCst);
            return;
        }
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOC: Counting = Counting;
fn reset() {
    ALLOCS.store(0, Ordering::SeqCst);
    DEALLOCS.store(0, Ordering::SeqCst);
    FOREIGN.store(0, Ordering::SeqCst);
}
#[inline(never)]
fn check(case: u32, result: u64, expected: u64, owns_buffer: bool) -> i32 {
    let allocs = ALLOCS.swap(0, Ordering::SeqCst);
    let deallocs = DEALLOCS.swap(0, Ordering::SeqCst);
    let foreign = FOREIGN.swap(0, Ordering::SeqCst);
    let freed = if owns_buffer { deallocs >= 1 } else { deallocs == 0 };
    if result == expected && foreign == 0 && allocs == deallocs && freed { 0 } else { 1 << case }
}
struct Noisy(u64);
impl Drop for Noisy {
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}
"#
    };
}

/// Empty Vecs own no allocation: `Vec::new()` and `Vec::with_capacity(0)` hold
/// the alignment's dangling sentinel at capacity zero, and rustc's `RawVec`
/// frees only a nonzero capacity. Each bridge path that frees a Vec buffer must
/// skip the zero-byte free: the by-value `vec::IntoIter` drop, the
/// `Vec<Box<T>>` drop and the needs-drop-element drop. Each `filled` case is
/// the same path over an owned buffer, the control that the counting allocator
/// still observes that path's free. The first guest is the reported program
/// verbatim.
///
/// The `vec::IntoIter` guests also pin the iterator's state layout. At O2 and O3
/// rustc's MIR inliner builds the iterator itself (`IntoIter { buf, phantom,
/// cap, alloc, ptr, end }`, stored at rustc's offsets `buf@0, ptr@8, cap@16,
/// end@24`) and the bridge's `next`/drop must read those same offsets. Before
/// the state followed rustc's layout they read a private `ptr@0, end@8, buf@16,
/// cap@24` cursor: `filled_into_iter` returned 0 (LLVM 42) and freed `0x4`, its
/// capacity, and the standalone filled program aborted. The chain-terminal
/// guest reads the same state through the iterator-chain source; it runs at O0
/// and O1 only, because at O2 and O3 the bridge refuses those terminals
/// (`iterator fold self argument is not memory-backed`) before this layout
/// matters. In the `Vec::with_capacity(0)` guest the O2/O3 inlined `into_iter`
/// builds the iterator from the `RawVecInner` that `try_allocate_in` returned,
/// which the bridge's with-capacity chain elides: the chain must give that
/// `Result` its real `Ok` value (before, the iterator read an unwritten slot
/// and its drop freed a garbage pointer).
#[test]
fn empty_vec_drops_free_no_dangling_buffer() {
    let reported = Guest {
        name: "empty_vec_into_iter_reported",
        what: "the reported program: iterate an empty Vec by value",
        src: r#"
fn main(){ let v: Vec<u64> = Vec::new(); let mut s = 0u64; for x in v { s += x; } std::process::exit(s as i32) }
"#,
    };
    let filled_reported = Guest {
        name: "filled_vec_into_iter_reported",
        what: "the reported program: iterate a filled Vec by value",
        src: r#"
fn main() {
    let mut v = Vec::new();
    v.push(20u64);
    v.push(22);
    let mut s = 0;
    for x in v { s += x; }
    std::process::exit(s as i32)
}
"#,
    };
    let into_iter = Guest {
        name: "empty_vec_into_iter_drop",
        what: "vec::IntoIter next and drop over empty and filled Vecs",
        src: concat!(
            counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn empty_into_iter() -> u64 {
    let v: Vec<u64> = Vec::new();
    let mut s = 0u64;
    for x in v { s += x; }
    s
}
#[inline(never)]
fn filled_into_iter() -> u64 {
    let mut v: Vec<u64> = Vec::new();
    v.push(20);
    v.push(22);
    let mut s = 0u64;
    for x in v { s += x; }
    s
}
#[inline(never)]
fn explicit_into_iter() -> u64 {
    let mut v: Vec<u64> = Vec::new();
    v.push(20);
    v.push(22);
    let mut s = 0u64;
    for x in v.into_iter() { s = s * 3 + x; }
    s
}
#[inline(never)]
fn partially_consumed_into_iter() -> u64 {
    let mut v: Vec<u64> = Vec::new();
    v.push(20);
    v.push(22);
    v.push(24);
    let mut s = 0u64;
    for x in v { if x > 20 { break; } s += x; }
    s
}
#[inline(never)]
fn byte_into_iter() -> u64 {
    let mut v: Vec<u8> = Vec::new();
    v.push(20);
    v.push(22);
    let mut s = 0u64;
    for x in v { s = s * 5 + x as u64; }
    s
}
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, empty_into_iter(), 0, false);
    failed |= check(1, filled_into_iter(), 42, true);
    failed |= check(2, explicit_into_iter(), 82, true);
    failed |= check(3, partially_consumed_into_iter(), 20, true);
    failed |= check(4, byte_into_iter(), 122, true);
    std::process::exit(failed);
}
"#
        ),
    };
    let with_capacity = Guest {
        name: "zero_capacity_vec_into_iter_drop",
        what: "vec::IntoIter over Vec::with_capacity(0) and (3), with a filled control",
        src: concat!(
            counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn empty_with_capacity_into_iter() -> u64 {
    let v: Vec<u64> = Vec::with_capacity(0);
    let mut s = 0u64;
    for x in v { s += x; }
    s
}
#[inline(never)]
fn reserved_into_iter() -> u64 {
    let mut v: Vec<u64> = Vec::with_capacity(3);
    v.push(20);
    v.push(22);
    let mut s = 0u64;
    for x in v { s = s * 3 + x; }
    s
}
#[inline(never)]
fn filled_into_iter() -> u64 {
    let mut v: Vec<u64> = Vec::new();
    v.push(20);
    v.push(22);
    let mut s = 0u64;
    for x in v { s += x; }
    s
}
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, empty_with_capacity_into_iter(), 0, false);
    failed |= check(1, reserved_into_iter(), 82, true);
    failed |= check(2, filled_into_iter(), 42, true);
    std::process::exit(failed);
}
"#
        ),
    };
    let chain = Guest {
        name: "vec_into_iter_chain_terminals",
        what: "vec::IntoIter as an iterator-chain source: sum, map, rev, filter",
        src: r#"
#[inline(never)]
fn filled() -> Vec<u64> {
    let mut v = Vec::new();
    v.push(20u64);
    v.push(22);
    v.push(25);
    v
}
#[inline(never)]
fn sum() -> u64 { filled().into_iter().sum() }
#[inline(never)]
fn map_sum() -> u64 { filled().into_iter().map(|x| x * 2).sum() }
#[inline(never)]
fn rev_fold() -> u64 { filled().into_iter().rev().fold(0, |a, x| a * 3 + x) }
#[inline(never)]
fn filter_count() -> u64 { filled().into_iter().filter(|x| x % 2 == 0).count() as u64 }
fn main() {
    let mut failed = 0;
    if sum() != 67 { failed |= 1; }
    if map_sum() != 134 { failed |= 2; }
    if rev_fold() != 311 { failed |= 4; }
    if filter_count() != 2 { failed |= 8; }
    std::process::exit(failed);
}
"#,
    };
    let owned = Guest {
        name: "empty_vec_owned_drop",
        what: "Vec<Box<T>> and needs-drop-element Vec drops, empty and filled",
        src: concat!(
            counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn empty_boxed_drop() -> u64 {
    let v: Vec<Box<u64>> = Vec::new();
    v.len() as u64
}
#[inline(never)]
fn empty_needs_drop_drop() -> u64 {
    let v: Vec<Noisy> = Vec::new();
    v.len() as u64
}
#[inline(never)]
fn filled_boxed_drop() -> u64 {
    let mut v: Vec<Box<u64>> = Vec::new();
    v.push(Box::new(7));
    v.len() as u64 + 41
}
#[inline(never)]
fn filled_needs_drop_drop() -> u64 {
    let mut v: Vec<Noisy> = Vec::new();
    v.push(Noisy(7));
    v.len() as u64 + 41
}
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, empty_boxed_drop(), 0, false);
    failed |= check(1, empty_needs_drop_drop(), 0, false);
    failed |= check(2, filled_boxed_drop(), 42, true);
    failed |= check(3, filled_needs_drop_drop(), 42, true);
    std::process::exit(failed);
}
"#
        ),
    };
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!("trustcg_empty_vec_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create empty-Vec runtime directory");
    let mut cells = 0;
    let mut failures = Vec::new();
    for (guest, levels, expected) in [
        (&reported, 0..=3, 0),
        (&filled_reported, 0..=3, 42),
        (&into_iter, 0..=3, 0),
        (&with_capacity, 0..=3, 0),
        (&chain, 0..=1, 0),
        (&owned, 0..=3, 0),
    ] {
        for opt in levels {
            for (lane, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                match compile(&dir, guest, opt, selected).and_then(|program| execute(&program)) {
                    Ok(code) if code == expected => cells += 1,
                    other => failures.push(format!(
                        "{} O{opt} {lane}: {other:?} (expected Ok({expected}))",
                        guest.name
                    )),
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "empty-Vec drops (exit code bit i = case i of the guest freed memory it does not \
         own, leaked, or returned a wrong value; artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(cells, 44, "every empty-Vec cell must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during empty-Vec controls"
    );
    eprintln!("TCG_EMPTY_VEC_DROP cells={cells} frontend=off certs=off");
}

/// A raw-pointer constant whose CTFE image carries no provenance (null, the
/// dangling sentinel `NonNull::dangling()` and an empty `Vec` hold, an integer
/// cast to a pointer, `ptr::without_provenance`) is TrustIR's no-provenance
/// pointer value, built by the pointer-width integer and `IntToPtr`. Each check
/// observes the exact address LLVM gives it, so a constant spelled at the wrong
/// value, or refused, fails a cell. Bare raw pointers, `NonNull` operands, a
/// user newtype over `NonNull` and a raw-pointer field of a constant aggregate
/// are each covered, at O0-O3 under both panic strategies. The exit status
/// holds eight bits, so a failing check above bit 7 exits 255.
#[test]
fn address_only_raw_pointer_constants_match_llvm() {
    let guest = Guest {
        name: "address_only_raw_pointer_constants",
        what: "provenance-free raw-pointer constants keep their exact addresses",
        src: r#"
use std::ptr::NonNull;
#[derive(Clone, Copy)]
struct Window { start: *const u64, len: usize, end: *mut u8 }
#[derive(Clone, Copy)]
struct Handle(NonNull<u16>);
#[derive(Clone, Copy)]
struct Slot { handle: Handle, tag: u32 }
const SENTINEL: *const u8 = usize::MAX as *const u8;
const WINDOW: Window = Window { start: 16 as *const u64, len: 3, end: 0x40 as *mut u8 };
const DANGLING: NonNull<u32> = NonNull::dangling();
const HANDLE: Handle = Handle(NonNull::dangling());
#[inline(never)]
fn addr<T>(p: *const T) -> usize { p as usize }
#[inline(never)]
fn non_null(p: NonNull<u32>) -> usize { p.as_ptr() as usize }
#[inline(never)]
fn window(w: Window) -> usize { addr(w.start) + w.len + addr(w.end) }
#[inline(never)]
fn slot(tag: u32) -> Slot { Slot { handle: HANDLE, tag } }
#[inline(never)]
fn slot_sum(tag: u32) -> usize {
    let local = Slot { handle: HANDLE, tag };
    addr(local.handle.0.as_ptr()) + local.tag as usize
}
fn main() {
    let mut failed = 0;
    if addr(Vec::<u64>::new().as_ptr()) != 8 { failed |= 1; }
    if addr(Vec::<u16>::new().as_ptr()) != 2 { failed |= 2; }
    if addr(SENTINEL) != usize::MAX { failed |= 4; }
    if window(std::hint::black_box(WINDOW)) != 16 + 3 + 0x40 { failed |= 8; }
    if non_null(DANGLING) != 4 || non_null(NonNull::dangling()) != 4 { failed |= 16; }
    if addr(std::ptr::without_provenance::<u8>(0x1234)) != 0x1234 { failed |= 32; }
    if NonNull::<u64>::dangling() != NonNull::dangling() { failed |= 64; }
    let mut empty = Vec::<u32>::new().into_iter();
    if empty.next().is_some() || addr(std::ptr::null::<u8>()) != 0 { failed |= 128; }
    let returned = slot(std::hint::black_box(5));
    if addr(returned.handle.0.as_ptr()) + returned.tag as usize != 2 + 5 { failed |= 256; }
    if slot_sum(std::hint::black_box(6)) != 2 + 6 { failed |= 512; }
    std::process::exit(if failed > 0xff { 0xff } else { failed });
}
"#,
    };
    let backend = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("trustcg_address_only_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create address-only pointer runtime directory");
    let mut failures = Vec::new();
    let mut cells = 0;
    for panic in ["abort", "unwind"] {
        for opt in 0..=3 {
            for (lane, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                match compile_with_panic(&dir, &guest, opt, selected, panic)
                    .and_then(|program| execute(&program))
                {
                    Ok(0) => cells += 1,
                    other => failures.push(format!(
                        "{} -Cpanic={panic} O{opt} {lane}: {other:?} (expected Ok(0))",
                        guest.name
                    )),
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "address-only raw-pointer constants (exit code bit i = check i read a wrong \
         address, 255 = a check above bit 7 did; artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(cells, 16, "every address-only pointer cell must execute");
    eprintln!("TCG_ADDRESS_ONLY_RAW_POINTER cells={cells} frontend=off certs=off");
}

/// A counting global allocator that also balances each freed layout against the
/// allocated ones (bytes and alignment), for the consumed-`vec::IntoIter` guests.
/// `check` returns `1 << case` unless the case returned `expected`, freed
/// nothing foreign, freed exactly as many blocks, bytes and alignment units as
/// it allocated, and freed a buffer iff it owns one. `filled!` builds a
/// three-element `Vec<u64>` from opaque values, so LLVM keeps the allocation.
macro_rules! layout_counting_allocator_prelude {
    () => {
        r#"
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
static FOREIGN: AtomicUsize = AtomicUsize::new(0);
static BYTES_IN: AtomicUsize = AtomicUsize::new(0);
static BYTES_OUT: AtomicUsize = AtomicUsize::new(0);
static ALIGN_IN: AtomicUsize = AtomicUsize::new(0);
static ALIGN_OUT: AtomicUsize = AtomicUsize::new(0);
static SINK: AtomicU64 = AtomicU64::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::SeqCst);
        BYTES_IN.fetch_add(layout.size(), Ordering::SeqCst);
        ALIGN_IN.fetch_add(layout.align(), Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::SeqCst);
        BYTES_IN.fetch_add(layout.size(), Ordering::SeqCst);
        ALIGN_IN.fetch_add(layout.align(), Ordering::SeqCst);
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        DEALLOCS.fetch_add(1, Ordering::SeqCst);
        if layout.size() == 0 || (pointer as usize) < 4096 {
            FOREIGN.fetch_add(1, Ordering::SeqCst);
            return;
        }
        BYTES_OUT.fetch_add(layout.size(), Ordering::SeqCst);
        ALIGN_OUT.fetch_add(layout.align(), Ordering::SeqCst);
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOC: Counting = Counting;
fn reset() {
    ALLOCS.store(0, Ordering::SeqCst);
    DEALLOCS.store(0, Ordering::SeqCst);
    FOREIGN.store(0, Ordering::SeqCst);
    BYTES_IN.store(0, Ordering::SeqCst);
    BYTES_OUT.store(0, Ordering::SeqCst);
    ALIGN_IN.store(0, Ordering::SeqCst);
    ALIGN_OUT.store(0, Ordering::SeqCst);
}
#[inline(never)]
fn check(case: u32, result: u64, expected: u64, owns_buffer: bool) -> i32 {
    let allocs = ALLOCS.swap(0, Ordering::SeqCst);
    let deallocs = DEALLOCS.swap(0, Ordering::SeqCst);
    let foreign = FOREIGN.swap(0, Ordering::SeqCst);
    let bytes_in = BYTES_IN.swap(0, Ordering::SeqCst);
    let bytes_out = BYTES_OUT.swap(0, Ordering::SeqCst);
    let align_in = ALIGN_IN.swap(0, Ordering::SeqCst);
    let align_out = ALIGN_OUT.swap(0, Ordering::SeqCst);
    let balanced = allocs == deallocs && bytes_in == bytes_out && align_in == align_out;
    let freed = if owns_buffer { deallocs >= 1 } else { deallocs == 0 };
    if result == expected && foreign == 0 && balanced && freed { 0 } else { 1 << case }
}
macro_rules! filled {
    () => {{
        let mut v: Vec<u64> = Vec::new();
        v.push(std::hint::black_box(20));
        v.push(std::hint::black_box(22));
        v.push(std::hint::black_box(25));
        v
    }};
}
"#
    };
}

/// A terminal that takes an iterator chain BY VALUE consumes the `vec::IntoIter`
/// at its source, so it drops that iterator: std's `collect` / `extend` /
/// `for_each` / `sum` / `fold` / `count` / `max` / `last` / ... free the buffer
/// when their `self` goes out of scope, and the caller never drops a moved
/// argument. The bridge drives these terminals itself, so the drive must free
/// the buffer exactly once with its allocation layout (`cap * size_of::<T>()`,
/// `align_of::<T>()`), whether the iterator was fully drained, cut short by
/// `take`, or advanced by `next` before the terminal, and must skip a
/// zero-capacity buffer. A `&mut self` terminal (`find` / `position` / `any` /
/// `all` / `nth`) leaves the iterator to the caller's own `vec::IntoIter` drop;
/// those cases are the double-free controls. Each guest's exit code is the
/// bitmask of failing cases; the expected code is 0 in both lanes.
///
/// Levels: the last two guests' terminals compile at every level. The others run
/// at O0 and O1 only, because at O2 and O3 the bridge refuses them before the
/// drop matters (`iterator <name> self argument is not memory-backed`,
/// `Vec::collect iterator argument is not memory-backed`, `[TCG-SRET-ABI]`,
/// `[TCG-OWNING-ITER-METHOD]`, and the unintercepted `extend_trusted` /
/// `spec_extend`).
#[test]
fn consumed_vec_into_iter_frees_its_buffer() {
    let collect = Guest {
        name: "vec_into_iter_collect_extend_free",
        what: "collect / extend consume a vec::IntoIter source; nth borrows one",
        src: concat!(
            layout_counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn collect_map() -> u64 {
    let out: Vec<u64> = filled!().into_iter().map(|x| x * 2).collect();
    out[0] + out[1] + out[2] + out.len() as u64
}
#[inline(never)]
fn collect_bare() -> u64 {
    let out: Vec<u64> = filled!().into_iter().collect();
    out[0] + out[1] + out[2] + out.len() as u64
}
#[inline(never)]
fn collect_empty() -> u64 {
    let v: Vec<u64> = Vec::new();
    let out: Vec<u64> = v.into_iter().map(|x| x * 2).collect();
    out.len() as u64
}
#[inline(never)]
fn extend_map() -> u64 {
    let mut out: Vec<u64> = Vec::new();
    out.push(1);
    out.extend(filled!().into_iter().map(|x| x + 1));
    out.iter().sum::<u64>() + out.len() as u64
}
#[inline(never)]
fn extend_bare() -> u64 {
    let mut out: Vec<u64> = Vec::new();
    out.push(1);
    out.extend(filled!().into_iter());
    out.iter().sum::<u64>() + out.len() as u64
}
#[inline(never)]
fn nth() -> u64 { filled!().into_iter().nth(1).unwrap_or(0) }
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, collect_map(), 137, true);
    failed |= check(1, collect_bare(), 70, true);
    failed |= check(2, collect_empty(), 0, false);
    failed |= check(3, extend_map(), 75, true);
    failed |= check(4, extend_bare(), 72, true);
    failed |= check(5, nth(), 22, true);
    std::process::exit(failed);
}
"#
        ),
    };
    let reduce = Guest {
        name: "vec_into_iter_reduce_free",
        what: "sum / fold / count / for_each / rfold consume a vec::IntoIter source",
        src: concat!(
            layout_counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn sum() -> u64 { filled!().into_iter().sum() }
#[inline(never)]
fn map_sum() -> u64 { filled!().into_iter().map(|x| x * 2).sum() }
#[inline(never)]
fn fold() -> u64 { filled!().into_iter().fold(0, |a, x| a * 3 + x) }
#[inline(never)]
fn count() -> u64 { filled!().into_iter().count() as u64 }
#[inline(never)]
fn for_each() -> u64 {
    SINK.store(0, Ordering::SeqCst);
    filled!().into_iter().for_each(|x| { SINK.fetch_add(x, Ordering::SeqCst); });
    SINK.load(Ordering::SeqCst)
}
#[inline(never)]
fn rev_fold() -> u64 { filled!().into_iter().rev().fold(0, |a, x| a * 3 + x) }
#[inline(never)]
fn enumerate_sum() -> u64 {
    filled!().into_iter().enumerate().map(|(i, x)| i as u64 * x).sum()
}
#[inline(never)]
fn empty_sum() -> u64 {
    let v: Vec<u64> = Vec::new();
    v.into_iter().sum()
}
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, sum(), 67, true);
    failed |= check(1, map_sum(), 134, true);
    failed |= check(2, fold(), 271, true);
    failed |= check(3, count(), 3, true);
    failed |= check(4, for_each(), 67, true);
    failed |= check(5, rev_fold(), 311, true);
    failed |= check(6, enumerate_sum(), 72, true);
    failed |= check(7, empty_sum(), 0, false);
    std::process::exit(failed);
}
"#
        ),
    };
    let terminal = Guest {
        name: "vec_into_iter_terminal_free",
        what: "max / min_by_key / max_by / product / last consume a vec::IntoIter source",
        src: concat!(
            layout_counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn max() -> u64 { filled!().into_iter().max().unwrap_or(0) }
#[inline(never)]
fn min_by_key() -> u64 { filled!().into_iter().min_by_key(|x| x % 7).unwrap_or(0) }
#[inline(never)]
fn max_by() -> u64 {
    filled!().into_iter().max_by(|a, b| (a % 7).cmp(&(b % 7))).unwrap_or(0)
}
#[inline(never)]
fn product() -> u64 { filled!().into_iter().product() }
#[inline(never)]
fn last() -> u64 { filled!().into_iter().map(|x| x + 1).last().unwrap_or(0) }
#[inline(never)]
fn rev_map_sum() -> u64 { filled!().into_iter().rev().map(|x| x * 2).sum() }
#[inline(never)]
fn byte_sum() -> u64 {
    let mut v: Vec<u8> = Vec::new();
    v.push(std::hint::black_box(20));
    v.push(std::hint::black_box(22));
    v.push(std::hint::black_box(25));
    v.into_iter().map(|x| x as u64).sum()
}
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, max(), 25, true);
    failed |= check(1, min_by_key(), 22, true);
    failed |= check(2, max_by(), 20, true);
    failed |= check(3, product(), 11000, true);
    failed |= check(4, last(), 26, true);
    failed |= check(5, rev_map_sum(), 134, true);
    failed |= check(6, byte_sum(), 67, true);
    std::process::exit(failed);
}
"#
        ),
    };
    let partial = Guest {
        name: "vec_into_iter_partial_free",
        what: "partially consumed and short-cut vec::IntoIter sources",
        src: concat!(
            layout_counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn next_then_sum() -> u64 {
    let mut it = filled!().into_iter();
    let first = it.next().unwrap_or(0);
    first * 100 + it.map(|x| x * 2).sum::<u64>()
}
#[inline(never)]
fn take_sum() -> u64 { filled!().into_iter().take(2).sum() }
#[inline(never)]
fn take_count() -> u64 { filled!().into_iter().take(2).count() as u64 }
#[inline(never)]
fn skip_sum() -> u64 { filled!().into_iter().skip(1).sum() }
#[inline(never)]
fn filter_count() -> u64 { filled!().into_iter().filter(|x| x % 2 == 0).count() as u64 }
#[inline(never)]
fn byte_filter_count() -> u64 {
    let mut v: Vec<u8> = Vec::new();
    v.push(std::hint::black_box(20));
    v.push(std::hint::black_box(22));
    v.push(std::hint::black_box(25));
    v.into_iter().filter(|x| x % 2 == 0).count() as u64
}
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, next_then_sum(), 2094, true);
    failed |= check(1, take_sum(), 42, true);
    failed |= check(2, take_count(), 2, true);
    failed |= check(3, skip_sum(), 47, true);
    failed |= check(4, filter_count(), 2, true);
    failed |= check(5, byte_filter_count(), 2, true);
    std::process::exit(failed);
}
"#
        ),
    };
    let borrowed = Guest {
        name: "vec_into_iter_borrowed_free",
        what: "short-circuiting &mut self terminals leave the vec::IntoIter to the caller's drop",
        src: concat!(
            layout_counting_allocator_prelude!(),
            r#"
#[inline(never)]
fn find() -> u64 { filled!().into_iter().find(|&x| x > 20).unwrap_or(0) }
#[inline(never)]
fn position() -> u64 { filled!().into_iter().position(|x| x == 22).unwrap_or(9) as u64 }
#[inline(never)]
fn any() -> u64 { filled!().into_iter().any(|x| x == 22) as u64 }
#[inline(never)]
fn all() -> u64 { filled!().into_iter().all(|x| x > 10) as u64 }
fn main() {
    reset();
    let mut failed = 0;
    failed |= check(0, find(), 22, true);
    failed |= check(1, position(), 1, true);
    failed |= check(2, any(), 1, true);
    failed |= check(3, all(), 1, true);
    std::process::exit(failed);
}
"#
        ),
    };
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir =
        std::env::temp_dir().join(format!("trustcg_consumed_into_iter_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create consumed-IntoIter runtime directory");
    let mut cells = 0;
    let mut failures = Vec::new();
    for (guest, levels) in [
        (&collect, 0..=1),
        (&reduce, 0..=1),
        (&terminal, 0..=1),
        (&partial, 0..=3),
        (&borrowed, 0..=3),
    ] {
        for opt in levels {
            for (lane, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                match compile(&dir, guest, opt, selected).and_then(|program| execute(&program)) {
                    Ok(0) => cells += 1,
                    other => failures.push(format!(
                        "{} O{opt} {lane}: {other:?} (expected Ok(0))",
                        guest.name
                    )),
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "consumed vec::IntoIter drops (exit code bit i = case i of the guest leaked, freed \
         memory it does not own, freed with a layout it did not allocate, or returned a \
         wrong value; artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(cells, 28, "every consumed-IntoIter cell must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during consumed-IntoIter cells"
    );
    eprintln!("TCG_CONSUMED_INTO_ITER_DROP cells={cells} frontend=off certs=off");
}

/// The guests of the drop-order differentials (`vec_into_iter_drops_each_element_once`
/// and `drop_element_iterators_drop_or_refuse`). `D` has a user `Drop` and its
/// trust-ir type is its single `u64` leaf, so the bridge's iterator chains admit
/// `vec::IntoIter<D>` while every element owes a destructor call.
/// `mk()` builds `[D(20), D(22), D(25)]` from opaque values. `D::drop` counts
/// each call, folds the dropped value into `ORDER` (`order * 64 + value`), and
/// panics when the value is the guest's `PANIC_AT` (`0`: never). A guard in
/// `main` reports on either exit, normal or unwinding: the code is `100` when
/// `RESULT` (what `run()` returned, `u64::MAX` if it unwound) is `EXPECTED`,
/// plus `10` per destructor call, plus the blocks the global allocator still
/// holds, plus `50` when the destructor order is not `EXPECTED_ORDER`.
macro_rules! drop_order_prelude {
    () => {
        r#"
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
static DROPS: AtomicUsize = AtomicUsize::new(0);
static ORDER: AtomicU64 = AtomicU64::new(0);
static RESULT: AtomicU64 = AtomicU64::new(u64::MAX);
#[allow(dead_code)]
static SINK: AtomicU64 = AtomicU64::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        DEALLOCS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOC: Counting = Counting;
struct D(u64);
impl Drop for D {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
        let order = ORDER.load(Ordering::SeqCst);
        ORDER.store(order.wrapping_mul(64).wrapping_add(self.0), Ordering::SeqCst);
        if self.0 == PANIC_AT {
            panic!("element drop panics");
        }
    }
}
#[inline(never)]
fn mk() -> Vec<D> {
    let mut v = Vec::new();
    v.push(D(std::hint::black_box(20)));
    v.push(D(std::hint::black_box(22)));
    v.push(D(std::hint::black_box(25)));
    v
}
struct Report;
impl Drop for Report {
    fn drop(&mut self) {
        let allocs = ALLOCS.load(Ordering::SeqCst) as i32;
        let deallocs = DEALLOCS.load(Ordering::SeqCst) as i32;
        let drops = DROPS.load(Ordering::SeqCst) as i32;
        let expected_order = EXPECTED_ORDER.iter().fold(0u64, |a, &x| a * 64 + x);
        let value = if RESULT.load(Ordering::SeqCst) == EXPECTED { 100 } else { 0 };
        let misordered = if ORDER.load(Ordering::SeqCst) == expected_order { 0 } else { 50 };
        std::process::exit(value + 10 * drops + (allocs - deallocs) + misordered);
    }
}
fn main() {
    ALLOCS.store(0, Ordering::SeqCst);
    DEALLOCS.store(0, Ordering::SeqCst);
    let _report = Report;
    RESULT.store(run(), Ordering::SeqCst);
}
"#
    };
}

/// A `drop_order_prelude!` guest whose `run()` body is `$body` (which may begin
/// with items: a `Clone` impl, a helper type or function). The short forms
/// default `EXPECTED_ORDER` to ascending `[20, 22, 25]` and `PANIC_AT` to `0`;
/// the `unwind` form expects `run()` to unwind (`EXPECTED` is `u64::MAX`). An
/// order of other than three destructor calls names its length (`len "6"`).
macro_rules! drop_order_guest {
    (unwind $name:literal, $panic_at:literal, $body:literal) => {
        drop_order_guest!($name, $panic_at, $body, "u64::MAX", "[20, 22, 25]")
    };
    ($name:literal, $body:literal, $expected:literal) => {
        drop_order_guest!($name, 0, $body, $expected, "[20, 22, 25]")
    };
    ($name:literal, $body:literal, $expected:literal, $order:literal) => {
        drop_order_guest!($name, 0, $body, $expected, $order)
    };
    ($name:literal, $body:literal, $expected:literal, $order:literal, len $len:literal) => {
        drop_order_guest!($name, 0, $body, $expected, $order, $len)
    };
    ($name:literal, $panic_at:literal, $body:literal, $expected:literal, $order:literal) => {
        drop_order_guest!($name, $panic_at, $body, $expected, $order, "3")
    };
    (
        $name:literal,
        $panic_at:literal,
        $body:literal,
        $expected:literal,
        $order:literal,
        $len:literal
    ) => {
        Guest {
            name: $name,
            what: $body,
            src: concat!(
                drop_order_prelude!(),
                "const PANIC_AT: u64 = ",
                $panic_at,
                ";\nconst EXPECTED: u64 = ",
                $expected,
                ";\nconst EXPECTED_ORDER: [u64; ",
                $len,
                "] = ",
                $order,
                ";\n#[inline(never)]\nfn run() -> u64 { ",
                $body,
                " }\n"
            ),
        }
    };
}

/// What a drop-order guest must do in each lane at one of its levels.
enum DropOrderExpect {
    /// `panic=abort`: LLVM exits 130 (the value, three destructor calls in
    /// `EXPECTED_ORDER`, nothing leaked) and CG exits the same code.
    Abort130,
    /// `panic=unwind`, `run()` unwinds out of a panicking `D::drop`: LLVM exits
    /// `13x` (unwound, three destructor calls in order, `x` blocks the
    /// in-flight panic still holds) and CG exits the same code.
    UnwindMatchesLlvm,
    /// LLVM runs; CG refuses to compile, naming this marker.
    Refused(&'static str),
}

/// The refusal CG must name at each level a drop-order guest's own
/// `DropOrderExpect` leaves out, as `(level, marker)` pairs.
type DropOrderElsewhere = &'static [(u8, &'static str)];

/// One drop-order guest: its source, the levels its `DropOrderExpect` holds
/// at, and the named refusal at each other level.
type DropOrderCase = (Guest, &'static [u8], DropOrderExpect, DropOrderElsewhere);

/// `refuses!([2, 3], MARKER)`: a `DropOrderElsewhere` naming `MARKER` at
/// each listed level.
macro_rules! refuses {
    ([$($opt:literal),*], $marker:expr) => {
        &[$(($opt, $marker)),*]
    };
}

/// Run every drop-order case at O0-O3 and assert each cell. At a level the
/// case lists, both lanes run and its `DropOrderExpect` must hold; at every
/// other level CG must refuse with that level's marker (only CG runs there:
/// the listed levels are the guest's LLVM oracle). A case must say what
/// happens at each of the four levels exactly once. `tag` names the artifact
/// directory (removed when every cell passes, kept otherwise) and the summary
/// line.
fn run_drop_order_cases(tag: &str, cases: &[DropOrderCase]) {
    for (guest, levels, _, elsewhere) in cases {
        let mut covered: Vec<u8> = levels
            .iter()
            .copied()
            .chain(elsewhere.iter().map(|&(opt, _)| opt))
            .collect();
        covered.sort_unstable();
        assert_eq!(
            covered,
            [0, 1, 2, 3],
            "drop-order guest {} must name what happens at each level exactly once",
            guest.name
        );
    }
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!("trustcg_{tag}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create drop-order runtime directory");
    // One worker per guest at a time: a guest's lanes and levels share its
    // source file, so they run in sequence.
    let next = std::sync::atomic::AtomicUsize::new(0);
    let outcomes = std::sync::Mutex::new((0usize, Vec::new()));
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    // A refusal's code and reason lines, or the start of the error (a timeout,
    // a signal, a compiler crash) when it has none.
    let cg_summary = |cg: &Result<i32, String>| match cg {
        Ok(code) => format!("Ok({code})"),
        Err(error) => {
            let named: Vec<&str> = error
                .lines()
                .filter(|line| line.contains("[TCG-") || line.contains(" - "))
                .collect();
            if named.is_empty() {
                format!("Err({:?})", error.chars().take(400).collect::<String>())
            } else {
                named.join(" | ")
            }
        }
    };
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    let Some((guest, levels, expect, elsewhere)) = cases.get(index) else {
                        break;
                    };
                    let panic = if guest.name.starts_with("u_") {
                        "unwind"
                    } else {
                        "abort"
                    };
                    let run = |opt: u8, selected: Option<&Path>| {
                        compile_with_panic(&dir, guest, opt, selected, panic)
                            .and_then(|program| execute(&program))
                    };
                    let mut verdicts = Vec::new();
                    for &opt in *levels {
                        let llvm = run(opt, None);
                        let cg = run(opt, Some(backend.as_path()));
                        verdicts.push(match (expect, &llvm, &cg) {
                            (DropOrderExpect::Abort130, Ok(130), Ok(130)) => Ok(2),
                            (DropOrderExpect::UnwindMatchesLlvm, Ok(oracle), Ok(code))
                                if oracle / 10 == 13 && code == oracle =>
                            {
                                Ok(2)
                            }
                            (DropOrderExpect::Refused(marker), Ok(_), Err(error))
                                if error.contains(marker) =>
                            {
                                Ok(2)
                            }
                            _ => Err(format!(
                                "{} O{opt} panic={panic} ({}): LLVM {llvm:?}, CG {}",
                                guest.name,
                                guest.what,
                                cg_summary(&cg)
                            )),
                        });
                    }
                    for &(opt, marker) in *elsewhere {
                        let cg = run(opt, Some(backend.as_path()));
                        verdicts.push(match &cg {
                            Err(error) if error.contains(marker) => Ok(1),
                            _ => Err(format!(
                                "{} O{opt} panic={panic} ({}): CG must refuse with {marker:?}, CG {}",
                                guest.name,
                                guest.what,
                                cg_summary(&cg)
                            )),
                        });
                    }
                    let mut outcomes = outcomes.lock().expect("drop-order outcomes");
                    for verdict in verdicts {
                        match verdict {
                            Ok(cells) => outcomes.0 += cells,
                            Err(failure) => outcomes.1.push(failure),
                        }
                    }
                }
            });
        }
    });
    let (cells, mut failures) = outcomes.into_inner().expect("drop-order outcomes");
    failures.sort();
    assert!(
        failures.is_empty(),
        "drop-order cells (exit code: 100 for the expected result or unwind, +10 per \
         destructor call, +1 per block still allocated, +50 out of order; artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    let expected_cells: usize = cases
        .iter()
        .map(|(_, levels, _, elsewhere)| 2 * levels.len() + elsewhere.len())
        .sum();
    assert_eq!(cells, expected_cells, "every drop-order cell must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during drop-order cells"
    );
    std::fs::remove_dir_all(&dir).expect("remove passing drop-order artifacts");
    eprintln!(
        "TCG_{} cells={cells} frontend=off certs=off",
        tag.to_uppercase()
    );
}

/// `vec::IntoIter<D>` for an element `D` with a user `Drop`
/// (`drop_order_prelude!`): every element is dropped exactly once, in rustc's
/// order, whoever consumes it. A by-value terminal the bridge drives owns the
/// iterator: it drops each item it discards (every item `count` counts, the
/// result `last` replaces, a `filter` / `skip` / `step_by` / `take_while` /
/// `skip_while` reject) and, after the drive, the elements no pull yielded
/// (`take`, `rev().take`), then frees the buffer. A by-value closure (`map` /
/// `fold` / `for_each` / `position` / `any` / `all`) or `collect` moves the item
/// on, so the drive never drops it again. A `collect` std runs in place adopts
/// the source buffer and drops only the elements a `take` left. A
/// `vec::IntoIter` the caller drops (after a `for` loop's `break`, a `next()`,
/// a `&mut self` `find` / `nth`) drops its unyielded elements before the free.
/// The `v.iter()` and mapped `Range` guests are controls: their items are
/// references, or owned values the drive drops at a discard while no buffer is
/// involved.
///
/// Levels: each guest runs at the levels where the bridge compiles its shape,
/// and at each other level the cell asserts the refusal it names there before
/// any drop is emitted. By-value count, scalar fold, last, mapped sum and
/// mapped collect require exact native matches at every level, including the
/// original buffer free and all element drops. Residual refusals include the
/// unit-accumulator fold reached by `for_each` at O2/O3,
/// `[TCG-OWNING-ITER-METHOD]` (`take_while` / `skip_while` at O0/O1,
/// `advance_by` at O2/O3) and `[TCG-STEPBY-OPT-LEVEL]` (O1-O3). A collect
/// into `Vec<D>` is no cell: the bridge
/// refuses it at every level (`Vec::collect of a non-integer/non-float-scalar
/// element`). A comparing reduction (`min_by_key`) drops each comparison's
/// loser mid-reduction, which the drive does not model, so it refuses
/// (`[TCG-ITER-DISCARD-DROP]`).
///
/// `panic=unwind` with a panicking `D::drop`: the dropped `vec::IntoIter` runs
/// `drop_in_place::<[D]>`'s nested cleanup (the remaining elements, then the
/// buffer, then the unwind) and matches LLVM, a `next()` then drop included
/// (O0-O3). Any drive over an owning source of
/// such elements refuses (`[TCG-INTOITER-UNWIND-DROP]`), the by-value and the
/// `&mut self` terminals alike: an unwinding payload call or element drop
/// leaves the drive without the drops std's unwind runs.
#[test]
fn vec_into_iter_drops_each_element_once() {
    const ALL: &[u8] = &[0, 1, 2, 3];
    const LOW: &[u8] = &[0, 1];
    const HIGH: &[u8] = &[2, 3];
    use DropOrderExpect::{Abort130, Refused, UnwindMatchesLlvm};
    const UNWIND_REFUSAL: &str = "[TCG-INTOITER-UNWIND-DROP]";
    const NOWHERE: DropOrderElsewhere = &[];
    const UNIT_FOLD: &str = "iterator fold over a non-scalar accumulator";
    let guests: Vec<DropOrderCase> = vec![
        // The reported shapes.
        (
            drop_order_guest!("d_count", "mk().into_iter().count() as u64", 3),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!("d_fold", "mk().into_iter().fold(0, |a, d| a + d.0)", 67),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_for_break",
                "let mut n = 0; for d in mk() { n += 1; if d.0 == 20 { break } } n",
                1
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_for_full",
                "let mut n = 0; for _d in mk() { n += 1; } n",
                3
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_last",
                "mk().into_iter().last().map(|d| d.0).unwrap_or(0)",
                25
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!("d_map_sum", "mk().into_iter().map(|d| d.0).sum()", 67),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_next_then_drop",
                "let mut it = mk().into_iter(); let x = it.next().map(|d| d.0).unwrap_or(0); x",
                20
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_take_map_sum",
                "mk().into_iter().take(1).map(|d| d.0).sum()",
                20
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!("d_vec_drop", "let v = mk(); v.len() as u64", 3),
            ALL,
            Abort130,
            NOWHERE,
        ),
        // Every discard site, terminal and moving closure.
        (
            drop_order_guest!(
                "d_next_then_sum",
                "let mut it = mk().into_iter(); let f = it.next().map(|d| d.0).unwrap_or(0); f * 100 + it.map(|d| d.0).sum::<u64>()",
                2047
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_skip_sum",
                "mk().into_iter().skip(1).map(|d| d.0).sum()",
                47
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_filter_count",
                "mk().into_iter().filter(|d| d.0 != 22).count() as u64",
                2
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_filter_map_sum",
                "mk().into_iter().filter(|d| d.0 > 20).map(|d| d.0).sum()",
                47
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_step_by",
                "mk().into_iter().step_by(2).map(|d| d.0).sum()",
                45
            ),
            &[0],
            Abort130,
            refuses!([1, 2, 3], "[TCG-STEPBY-OPT-LEVEL]"),
        ),
        (
            drop_order_guest!(
                "d_take_while",
                "mk().into_iter().take_while(|d| d.0 < 22).map(|d| d.0).sum()",
                20
            ),
            HIGH,
            Abort130,
            refuses!([0, 1], "[TCG-OWNING-ITER-METHOD] `take_while`"),
        ),
        (
            drop_order_guest!(
                "d_skip_while",
                "mk().into_iter().skip_while(|d| d.0 < 22).map(|d| d.0).sum()",
                47
            ),
            HIGH,
            Abort130,
            refuses!([0, 1], "[TCG-OWNING-ITER-METHOD] `skip_while`"),
        ),
        (
            drop_order_guest!("d_take_count", "mk().into_iter().take(2).count() as u64", 2),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!("d_skip_count", "mk().into_iter().skip(1).count() as u64", 2),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_skip_last",
                "mk().into_iter().skip(1).last().map(|d| d.0).unwrap_or(0)",
                25
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_rev_take",
                "mk().into_iter().rev().map(|d| d.0).take(1).sum()",
                25,
                "[25, 20, 22]"
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_nth",
                "mk().into_iter().nth(1).map(|d| d.0).unwrap_or(0)",
                22
            ),
            LOW,
            Abort130,
            refuses!([2, 3], "[TCG-OWNING-ITER-METHOD] `advance_by`"),
        ),
        (
            drop_order_guest!(
                "d_find",
                "mk().into_iter().find(|d| d.0 > 20).map(|d| d.0).unwrap_or(0)",
                22
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_position",
                "mk().into_iter().position(|d| d.0 == 22).unwrap_or(9) as u64",
                1
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!("d_any", "mk().into_iter().any(|d| d.0 == 22) as u64", 1),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!("d_all", "mk().into_iter().all(|d| d.0 > 10) as u64", 1),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_for_each",
                "mk().into_iter().for_each(|d| { SINK.fetch_add(d.0, Ordering::SeqCst); }); SINK.load(Ordering::SeqCst)",
                67
            ),
            LOW,
            Abort130,
            refuses!([2, 3], UNIT_FOLD),
        ),
        (
            drop_order_guest!(
                "d_map_collect",
                "let o: Vec<u64> = mk().into_iter().map(|d| d.0).collect(); o.iter().sum()",
                67
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        // An in-place collect adopts the source buffer and drops the elements
        // the `take` left in place.
        (
            drop_order_guest!(
                "d_map_take_collect",
                "let o: Vec<u64> = mk().into_iter().map(|d| d.0).take(1).collect(); o.iter().sum()",
                20
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_take_map_collect",
                "let o: Vec<u64> = mk().into_iter().take(2).map(|d| d.0).collect(); o.iter().sum()",
                42
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "d_min_by_key",
                "mk().into_iter().min_by_key(|d| d.0 % 7).map(|d| d.0).unwrap_or(0)",
                22,
                "[20, 25, 22]"
            ),
            ALL,
            Refused("[TCG-ITER-DISCARD-DROP]"),
            NOWHERE,
        ),
        // Controls: borrowed elements, and owned items without an owning source.
        (
            drop_order_guest!(
                "r_iter_filter_count",
                "let v = mk(); v.iter().filter(|d| d.0 > 20).count() as u64",
                2
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "r_iter_skip_sum",
                "let v = mk(); v.iter().skip(1).map(|d| d.0).sum()",
                47
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "r_iter_enumerate_skip",
                "let v = mk(); v.iter().enumerate().skip(1).map(|(i, d)| i as u64 * d.0).sum()",
                72
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "r_iter_min_by_key",
                "let v = mk(); v.iter().min_by_key(|d| d.0 % 7).map(|d| d.0).unwrap_or(0)",
                22
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "r_range_map_filter_count",
                "(0..3u64).map(|x| D(std::hint::black_box(x) + 20)).filter(|d| d.0 != 21).count() as u64",
                2,
                "[20, 21, 22]"
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        // panic=unwind: the iterator's own drop unwinds like rustc's glue.
        (
            drop_order_guest!(unwind "u_vec_drop", 22, "let v = mk(); v.len() as u64"),
            ALL,
            UnwindMatchesLlvm,
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_for_break", 22, "let mut n = 0; for d in mk() { n += 1; if d.0 == 20 { break } } n"),
            ALL,
            UnwindMatchesLlvm,
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_for_full", 22, "let mut n = 0; for _d in mk() { n += 1; } n"),
            ALL,
            UnwindMatchesLlvm,
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_next_then_drop", 22, "let mut it = mk().into_iter(); let x = it.next().map(|d| d.0).unwrap_or(0); x"),
            ALL,
            UnwindMatchesLlvm,
            NOWHERE,
        ),
        // panic=unwind: a drive over the owning source refuses.
        (
            drop_order_guest!(unwind "u_count", 22, "mk().into_iter().count() as u64"),
            ALL,
            Refused(UNWIND_REFUSAL),
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_map_sum", 22, "mk().into_iter().map(|d| d.0).sum()"),
            ALL,
            Refused(UNWIND_REFUSAL),
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_take_map_sum", 22, "mk().into_iter().take(1).map(|d| d.0).sum()"),
            ALL,
            Refused(UNWIND_REFUSAL),
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_skip_sum", 20, "mk().into_iter().skip(1).map(|d| d.0).sum()"),
            ALL,
            Refused(UNWIND_REFUSAL),
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_last", 20, "mk().into_iter().last().map(|d| d.0).unwrap_or(0)"),
            ALL,
            Refused(UNWIND_REFUSAL),
            NOWHERE,
        ),
        (
            drop_order_guest!(unwind "u_position", 22, "mk().into_iter().position(|d| d.0 == 25).unwrap_or(9) as u64"),
            ALL,
            Refused(UNWIND_REFUSAL),
            NOWHERE,
        ),
    ];
    run_drop_order_cases("into_iter_drop_order", &guests);
}

/// The other iterators that produce or own a `Drop` element (`drop_order_prelude!`),
/// LLVM vs CG at O0-O3: every cell asserts the value and the exact destructor
/// calls and order, or the refusal CG names.
///
/// * `.cloned()`: the bridge drives `Cloned` by loading the element out of its
///   reference and calls no `Clone::clone`, only where the clone is a bitwise
///   copy (`clone_is_bitwise_copy`: builtin, the builtin derive, or core's own
///   impl for a `Copy` type, over fields that qualify). Any other clone (a
///   hand-written one, also on a `Copy` type or marked
///   `#[automatically_derived]`, and one core's `Reverse::clone` or a non-`Copy`
///   `Cell` reaches) is left to core's real `Cloned` bodies, whose `sum` /
///   `count` here refuse (`[TCG-ITER-UNMODELED]`, as a `fold` at O2/O3 where
///   `sum` inlines into it). A bitwise clone of an element
///   that needs drop refuses (`[TCG-ITER-CLONED-CLONE]`): each clone is an owned
///   value the drive would have to drop where it discards it.
/// * `array::IntoIter<D>`: the bridge's array model owns no element drop, so it
///   no longer admits `D`. std's own bodies run where this backend lowers them
///   (`for`, `next()`, `nth`, an unused iterator, `count` at O2/O3) and drop every
///   element; the other shapes refuse by name. Before, the unyielded elements
///   leaked. Under `panic=unwind` the real std bodies for these array shapes
///   must match LLVM's three drops, their order and allocation count, including
///   the remaining elements after a destructor panics. This does not admit a
///   droppable element to the bridge's synthetic array-iterator model.
/// * `vec::Drain<D>`: the bridge's Drain drops none of the drained elements no
///   pull yielded, so it refuses (`[TCG-DRAIN-ELEMENT-DROP]`) at the
///   `Vec::drain` that would build one, a fully consumed drain included.
/// * A `vec::IntoIter<u64>` mapped to `D`: under `panic=abort` the drive drops
///   each item where it discards it; under `panic=unwind` it refuses
///   (`[TCG-INTOITER-UNWIND-DROP]`), since a predicate that unwinds would leave
///   the item in flight and the iterator's buffer behind.
///
/// Controls: a `u64` array iterator and `u64` drain, and `.cloned()` over a
/// derived or core bitwise clone, still compile and match.
#[test]
fn drop_element_iterators_drop_or_refuse() {
    const ALL: &[u8] = &[0, 1, 2, 3];
    const LOW: &[u8] = &[0, 1];
    const HIGH: &[u8] = &[2, 3];
    use DropOrderExpect::{Abort130, Refused, UnwindMatchesLlvm};
    const NOWHERE: DropOrderElsewhere = &[];
    const CLONED: &str = "[TCG-ITER-CLONED-CLONE]";
    const DRAIN: &str = "[TCG-DRAIN-ELEMENT-DROP]";
    const UNMODELED_COUNT: &str = "[TCG-ITER-UNMODELED] iterator `count` terminal";
    const UNMODELED_SUM: &str = "[TCG-ITER-UNMODELED] iterator `sum` terminal";
    const UNMODELED_FOLD: &str = "[TCG-ITER-UNMODELED] iterator `fold` terminal";
    const UNMODELED_TRY_FOLD: &str = "iterator try_fold over an unmodeled iterator chain";
    const UNWIND_REFUSAL: &str = "[TCG-INTOITER-UNWIND-DROP]";
    let guests: Vec<DropOrderCase> = vec![
        // `.cloned()` over a hand-written clone is left to core's real
        // `Cloned` bodies, whose `sum` / `count` terminals refuse here.
        (
            drop_order_guest!(
                "c_user_clone_map_sum",
                "impl Clone for D { fn clone(&self) -> D { D(self.0 + 1) } } let v = mk(); v.iter().cloned().map(|d| d.0).sum()",
                70,
                "[21, 23, 26, 20, 22, 25]",
                len "6"
            ),
            LOW,
            Refused(UNMODELED_SUM),
            refuses!([2, 3], UNMODELED_FOLD),
        ),
        (
            drop_order_guest!(
                "c_user_clone_count",
                "impl Clone for D { fn clone(&self) -> D { D(self.0 + 1) } } let v = mk(); v.iter().cloned().count() as u64",
                3,
                "[21, 23, 26, 20, 22, 25]",
                len "6"
            ),
            LOW,
            Refused(UNMODELED_COUNT),
            refuses!([2, 3], UNMODELED_FOLD),
        ),
        (
            drop_order_guest!(
                "c_bitwise_clone_filter_count",
                "impl Clone for D { fn clone(&self) -> D { D(self.0) } } let v = mk(); v.iter().cloned().filter(|d| d.0 != 22).count() as u64",
                2,
                "[20, 22, 25, 20, 22, 25]",
                len "6"
            ),
            ALL,
            Refused(UNMODELED_COUNT),
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "c_copy_user_clone_sum",
                "#[derive(Copy)] struct C(u64); impl Clone for C { fn clone(&self) -> C { C(self.0 + 1) } } let _v = mk(); let mut w = Vec::new(); w.push(C(std::hint::black_box(3))); w.push(C(std::hint::black_box(5))); w.iter().cloned().map(|c| c.0).sum()",
                10
            ),
            LOW,
            Refused(UNMODELED_SUM),
            refuses!([2, 3], UNMODELED_FOLD),
        ),
        (
            drop_order_guest!(
                "c_marked_user_clone_sum",
                "#[derive(Copy)] struct C(u64); #[automatically_derived] impl Clone for C { fn clone(&self) -> C { C(self.0 + 1) } } let _v = mk(); let mut w = Vec::new(); w.push(C(std::hint::black_box(3))); w.push(C(std::hint::black_box(5))); w.iter().cloned().map(|c| c.0).sum()",
                10
            ),
            LOW,
            Refused(UNMODELED_SUM),
            refuses!([2, 3], UNMODELED_FOLD),
        ),
        // A derived (bitwise) clone of an element that needs drop refuses: each
        // clone is an owned value the drive would have to drop at its discards.
        (
            drop_order_guest!(
                "c_derived_drop_clone_filter_count",
                "#[derive(Clone)] struct E(u64); impl Drop for E { fn drop(&mut self) { let _ = D(self.0); } } let mut v = Vec::new(); v.push(E(std::hint::black_box(20))); v.push(E(std::hint::black_box(22))); v.push(E(std::hint::black_box(25))); v.iter().cloned().filter(|e| e.0 != 22).count() as u64",
                2,
                "[20, 22, 25, 20, 22, 25]",
                len "6"
            ),
            ALL,
            Refused(CLONED),
            NOWHERE,
        ),
        // Controls: a derived bitwise clone of an element that needs no drop.
        (
            drop_order_guest!(
                "c_derived_copy_sum",
                "#[derive(Clone, Copy)] struct C(u64); let _v = mk(); let mut w = Vec::new(); w.push(C(std::hint::black_box(3))); w.push(C(std::hint::black_box(5))); w.iter().cloned().map(|c| c.0).sum()",
                8
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "c_derived_filter_sum",
                "#[derive(Clone)] struct C(u64); let _v = mk(); let mut w = Vec::new(); w.push(C(std::hint::black_box(3))); w.push(C(std::hint::black_box(5))); w.push(C(std::hint::black_box(9))); w.iter().cloned().filter(|c| c.0 != 5).map(|c| c.0).sum()",
                12
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        // Controls: core's own bitwise clones, and a derive over their fields.
        (
            drop_order_guest!(
                "c_nonzero_sum",
                "let _v = mk(); let mut w = Vec::new(); w.push(std::num::NonZeroU32::new(std::hint::black_box(3)).unwrap()); w.push(std::num::NonZeroU32::new(5).unwrap()); w.iter().cloned().map(|n| n.get() as u64).sum()",
                8
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "c_reverse_sum",
                "let _v = mk(); let mut w = Vec::new(); w.push(std::cmp::Reverse(std::hint::black_box(3u64))); w.push(std::cmp::Reverse(5)); w.iter().cloned().map(|r| r.0).sum()",
                8
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "c_derived_core_fields_sum",
                "#[derive(Clone, Copy)] struct Id(std::num::NonZeroU32, std::marker::PhantomData<u8>); let _v = mk(); let mut w = Vec::new(); w.push(Id(std::num::NonZeroU32::new(std::hint::black_box(3)).unwrap(), std::marker::PhantomData)); w.push(Id(std::num::NonZeroU32::new(5).unwrap(), std::marker::PhantomData)); w.iter().cloned().map(|i| i.0.get() as u64).sum()",
                8
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        // `Cell<C>` (not `Copy`) and `Reverse<C>` over a hand-written
        // `C::clone` are not bitwise clones here (`clone_is_bitwise_copy`):
        // core's real bodies, which refuse at these terminals.
        (
            drop_order_guest!(
                "c_cell_user_clone_sum",
                "#[derive(Copy)] struct C(u64); impl Clone for C { fn clone(&self) -> C { C(self.0 + 1) } } let _v = mk(); let mut w = Vec::new(); w.push(std::cell::Cell::new(C(std::hint::black_box(3)))); w.push(std::cell::Cell::new(C(5))); w.iter().cloned().map(|c| c.get().0).sum()",
                8
            ),
            LOW,
            Refused(UNMODELED_SUM),
            refuses!([2, 3], UNMODELED_FOLD),
        ),
        (
            drop_order_guest!(
                "c_reverse_user_clone_sum",
                "#[derive(Copy)] struct C(u64); impl Clone for C { fn clone(&self) -> C { C(self.0 + 1) } } let _v = mk(); let mut w = Vec::new(); w.push(std::cmp::Reverse(C(std::hint::black_box(3)))); w.push(std::cmp::Reverse(C(5))); w.iter().cloned().map(|r| r.0 .0).sum()",
                10
            ),
            LOW,
            Refused(UNMODELED_SUM),
            refuses!([2, 3], UNMODELED_FOLD),
        ),
        // `array::IntoIter<D>`: std's bodies, or a refusal.
        (
            drop_order_guest!(
                "a_for_break",
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } let mut n = 0; for d in ma() { n += d.0; break; } n",
                20
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "a_next_then_drop",
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } let mut it = ma().into_iter(); it.next().map(|d| d.0).unwrap_or(0)",
                20
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "a_unused",
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } let it = ma().into_iter(); let _k = &it; 7",
                7
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "a_nth",
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } ma().into_iter().nth(1).map(|d| d.0).unwrap_or(0)",
                22
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "a_count",
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } ma().into_iter().count() as u64",
                3
            ),
            HIGH,
            Abort130,
            refuses!([0, 1], UNMODELED_COUNT),
        ),
        (
            drop_order_guest!(
                "a_take_count",
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } ma().into_iter().take(2).count() as u64",
                2
            ),
            LOW,
            Refused(UNMODELED_COUNT),
            refuses!([2, 3], UNMODELED_TRY_FOLD),
        ),
        (
            drop_order_guest!(
                unwind "u_a_skip_sum",
                22,
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } ma().into_iter().skip(1).map(|d| d.0).sum()"
            ),
            ALL,
            Refused("[TCG-ITER-UNMODELED]"),
            NOWHERE,
        ),
        (
            drop_order_guest!(
                unwind "u_a_for_break",
                22,
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } let mut n = 0; for d in ma() { n += d.0; break; } n"
            ),
            ALL,
            UnwindMatchesLlvm,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                unwind "u_a_unused",
                22,
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } let it = ma().into_iter(); let _k = &it; 7"
            ),
            ALL,
            UnwindMatchesLlvm,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                unwind "u_a_count",
                22,
                "#[inline(never)] fn ma() -> [D; 3] { [D(std::hint::black_box(20)), D(std::hint::black_box(22)), D(std::hint::black_box(25))] } ma().into_iter().count() as u64"
            ),
            HIGH,
            UnwindMatchesLlvm,
            refuses!([0, 1], UNMODELED_COUNT),
        ),
        (
            drop_order_guest!(
                "a_u64_take_sum",
                "let _v = mk(); let a = [std::hint::black_box(3u64), 5, 9]; a.into_iter().take(2).map(|x| x * 2).sum()",
                16
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        // `vec::Drain<D>` refuses at the `Vec::drain` that builds it.
        (
            drop_order_guest!(
                "dr_for_break",
                "let mut v = mk(); let mut n = 0; for d in v.drain(..) { n += d.0; break; } n * 10 + v.len() as u64",
                200
            ),
            ALL,
            Refused(DRAIN),
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "dr_next_then_drop",
                "let mut v = mk(); let n = { let mut it = v.drain(..); it.next().map(|d| d.0).unwrap_or(0) }; n * 10 + v.len() as u64",
                200
            ),
            ALL,
            Refused(DRAIN),
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "dr_unused",
                "let mut v = mk(); { let _it = v.drain(..); } v.len() as u64",
                0
            ),
            ALL,
            Refused(DRAIN),
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "dr_for_full",
                "let mut v = mk(); let mut n = 0; for d in v.drain(..) { n += d.0; } n * 10 + v.len() as u64",
                670
            ),
            ALL,
            Refused(DRAIN),
            NOWHERE,
        ),
        (
            drop_order_guest!(
                unwind "u_dr_unused",
                22,
                "let mut v = mk(); { let _it = v.drain(..); } v.len() as u64"
            ),
            ALL,
            Refused(DRAIN),
            NOWHERE,
        ),
        // A `vec::IntoIter<u64>` mapped to a `Drop` item: dropped at each discard
        // under abort; under unwind the drive refuses.
        (
            drop_order_guest!(
                "v_u64_map_d_filter_count",
                "let mut w = Vec::new(); w.push(std::hint::black_box(20u64)); w.push(22); w.push(25); w.into_iter().map(|x| D(x)).filter(|d| d.0 != 22).count() as u64",
                2
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
        (
            drop_order_guest!(
                unwind "u_v_u64_map_d_pred_panic",
                0,
                "let mut w = Vec::new(); w.push(std::hint::black_box(20u64)); w.push(22); w.push(25); w.into_iter().map(|x| D(x)).filter(|d| { if d.0 == 22 { panic!(\"p\") } true }).count() as u64"
            ),
            ALL,
            Refused(UNWIND_REFUSAL),
            NOWHERE,
        ),
        (
            drop_order_guest!(
                "dr_u64_for_break",
                "let _v = mk(); let mut w = Vec::new(); w.push(std::hint::black_box(3u64)); w.push(5); w.push(9); let mut n = 0; for x in w.drain(..) { n += x; break; } n * 10 + w.len() as u64",
                30
            ),
            ALL,
            Abort130,
            NOWHERE,
        ),
    ];
    run_drop_order_cases("drop_element_iterators", &guests);
}

/// A program with its own `#[global_allocator]` must link and run whatever its
/// emitted code calls. rustc expands the attribute into this crate's
/// `__rust_alloc`, `__rust_dealloc`, `__rust_realloc` and `__rust_alloc_zeroed`
/// (`#[rustc_std_internal_symbol]` items), and the precompiled std calls all
/// four, so each is a link root even when no lowered body references it. The
/// first guest's own code allocates and frees through the allocator; the second
/// guest's own code never allocates (only std does, behind the program's back).
/// The allocator counts its calls so the exit code also shows that it, not the
/// default allocator, served the program.
#[test]
fn user_global_allocator_entry_points_link() {
    let boxed = Guest {
        name: "global_allocator_box",
        what: "a counting #[global_allocator] serving a Box",
        src: r#"
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        DEALLOCS.fetch_add(1, Ordering::SeqCst);
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOC: Counting = Counting;
fn main() {
    let before = (ALLOCS.load(Ordering::SeqCst), DEALLOCS.load(Ordering::SeqCst));
    let b = Box::new(std::hint::black_box(40u64));
    let r = *b;
    drop(b);
    let allocated = ALLOCS.load(Ordering::SeqCst) > before.0;
    let freed = DEALLOCS.load(Ordering::SeqCst) > before.1;
    std::process::exit(r as i32 + allocated as i32 + freed as i32)
}
"#,
    };
    let silent = Guest {
        name: "global_allocator_unreferenced",
        what: "a #[global_allocator] that no lowered body calls",
        src: r#"
use std::alloc::{GlobalAlloc, Layout, System};
struct Passthrough;
unsafe impl GlobalAlloc for Passthrough {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { unsafe { System.alloc(layout) } }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOC: Passthrough = Passthrough;
fn main() { std::process::exit(std::hint::black_box(42)) }
"#,
    };
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!("trustcg_global_alloc_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create global-allocator runtime directory");
    let mut cells = 0;
    let mut failures = Vec::new();
    for guest in [&boxed, &silent] {
        for opt in 0..=3 {
            for (lane, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                match compile(&dir, guest, opt, selected).and_then(|program| execute(&program)) {
                    Ok(42) => cells += 1,
                    Ok(code) => failures.push(format!("{} O{opt} {lane}: exit {code}", guest.name)),
                    // A link failure lists every undefined symbol once per
                    // referencing object; keep the symbol names.
                    Err(error) => {
                        let undefined: Vec<&str> = error
                            .lines()
                            .filter(|line| line.trim_end().ends_with("referenced from:"))
                            .map(str::trim)
                            .collect();
                        let summary = if undefined.is_empty() {
                            error.chars().take(400).collect::<String>()
                        } else {
                            format!("undefined {}", undefined.join(" "))
                        };
                        failures.push(format!("{} O{opt} {lane}: {summary}", guest.name));
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "user #[global_allocator] programs (artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(cells, 16, "every global-allocator cell must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during global-allocator controls"
    );
    eprintln!("TCG_USER_GLOBAL_ALLOCATOR cells={cells} frontend=off certs=off");
}

/// `core::array::IntoIter<T, N>` is `{ alive: IndexRange { start, end }, data:
/// [MaybeUninit<T>; N] }` behind single-field wrappers. At `-O2`/`-O3` rustc's
/// MIR inliner builds that value itself (and may advance `alive.start` with its
/// own inlined `next`) before calling the intercepted chain terminal, so the
/// terminal must read rustc's index range over the inline buffer, whoever built
/// or advanced the state. Each guest sets exit bit i when case i returns a wrong
/// value. The terminals guest covers bare and adapted terminals (`sum`, `map`,
/// `filter` + `count`, `fold`, `max`, `min`, `take`, `skip`, `enumerate`, a `u8`
/// element); the advanced guest consumes some elements with `next` first; the
/// returned guest moves the iterator out of the frame whose array built it and
/// overwrites that stack before iterating.
#[test]
fn array_into_iter_terminals_read_rustcs_state() {
    let terminals = Guest {
        name: "array_into_iter_terminals",
        what: "chain terminals over a fresh array::IntoIter",
        src: r#"
use std::hint::black_box;
#[inline(never)]
fn sum(k: u64) -> u64 { [k, k + 1, k + 2].into_iter().sum() }
#[inline(never)]
fn map_sum(k: u64) -> u64 { [k, k + 1, k + 2].into_iter().map(|x| x * 10).sum() }
#[inline(never)]
fn filter_count(k: u64) -> u64 {
    [k, k + 1, k + 2, k + 3].into_iter().filter(|x| x % 2 == 0).count() as u64
}
#[inline(never)]
fn fold(k: u64) -> u64 { [k, k + 1, k + 2].into_iter().fold(100, |a, x| a * 2 - x) }
#[inline(never)]
fn max(k: u64) -> u64 { [k + 5, k, k + 2].into_iter().max().unwrap_or(0) }
#[inline(never)]
fn min(k: i32) -> i32 { [k + 7, k - 5, k].into_iter().min().unwrap_or(0) }
#[inline(never)]
fn take_sum(k: u64) -> u64 { [k, k + 1, k + 2, k + 3].into_iter().take(2).sum() }
#[inline(never)]
fn skip_sum(k: u64) -> u64 { [k, k + 1, k + 2, k + 3].into_iter().skip(1).sum() }
#[inline(never)]
fn enumerate_sum(k: u64) -> u64 {
    [k, k + 1, k + 2].into_iter().enumerate().map(|(i, x)| i as u64 * x).sum()
}
#[inline(never)]
fn byte_sum(k: u8) -> u64 { [k, k + 1, k + 2, k + 3, k + 4].into_iter().map(|x| x as u64).sum() }
fn main() {
    let k = black_box(1u64);
    let mut bits = 0;
    if sum(k) != 6 { bits |= 1 << 0; }
    if map_sum(k) != 60 { bits |= 1 << 1; }
    if filter_count(k) != 2 { bits |= 1 << 2; }
    if fold(k) != 789 { bits |= 1 << 3; }
    if max(k) != 6 { bits |= 1 << 4; }
    if min(black_box(1)) != -4 { bits |= 1 << 5; }
    if take_sum(k) != 3 { bits |= 1 << 6; }
    if skip_sum(k) != 9 { bits |= 1 << 7; }
    if enumerate_sum(k) != 8 { bits |= 1 << 8; }
    if byte_sum(black_box(1)) != 15 { bits |= 1 << 9; }
    std::process::exit(bits);
}
"#,
    };
    let advanced = Guest {
        name: "array_into_iter_advanced",
        what: "chain terminals after `next` consumed part of an array::IntoIter",
        src: r#"
use std::hint::black_box;
#[inline(never)]
fn next_then_sum(k: u64) -> u64 {
    let mut it = [k, k + 1, k + 2, k + 3].into_iter();
    let first = it.next().unwrap_or(0);
    first * 100 + it.sum::<u64>()
}
#[inline(never)]
fn next_then_count(k: u64) -> u64 {
    let mut it = [k, k + 1, k + 2, k + 3, k + 4].into_iter();
    let _ = it.next();
    let _ = it.next();
    it.filter(|x| x % 2 == 1).count() as u64
}
#[inline(never)]
fn drained_then_sum(k: u64) -> u64 {
    let mut it = [k, k + 1].into_iter();
    while it.next().is_some() {}
    it.sum::<u64>() + 7
}
fn main() {
    let k = black_box(1u64);
    let mut bits = 0;
    if next_then_sum(k) != 109 { bits |= 1 << 0; }
    if next_then_count(k) != 2 { bits |= 1 << 1; }
    if drained_then_sum(k) != 7 { bits |= 1 << 2; }
    std::process::exit(bits);
}
"#,
    };
    let returned = Guest {
        name: "array_into_iter_returned",
        what: "an array::IntoIter returned out of the frame that built it",
        src: r#"
use std::hint::black_box;
#[inline(never)]
fn make(k: u64) -> std::array::IntoIter<u64, 4> { [k, k + 1, k + 2, k + 3].into_iter() }
#[inline(never)]
fn clobber(k: u64) -> u64 { black_box([k ^ 0x5a5a; 64]).len() as u64 }
#[inline(never)]
fn returned_sum(k: u64) -> u64 {
    let it = make(k);
    let c = clobber(k);
    it.sum::<u64>() + (c & 0)
}
#[inline(never)]
fn returned_loop(k: u64) -> u64 {
    let mut it = make(k);
    let c = clobber(k);
    let mut s = c & 0;
    while let Some(x) = it.next() { s = s * 10 + x; }
    s
}
fn main() {
    let k = black_box(1u64);
    let mut bits = 0;
    if returned_sum(k) != 10 { bits |= 1 << 0; }
    if returned_loop(k) != 1234 { bits |= 1 << 1; }
    std::process::exit(bits);
}
"#,
    };
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!("trustcg_array_into_iter_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create array::IntoIter runtime directory");
    let mut cells = 0;
    let mut failures = Vec::new();
    for guest in [&terminals, &advanced, &returned] {
        for opt in 0..=3 {
            for (lane, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
                match compile(&dir, guest, opt, selected).and_then(|program| execute(&program)) {
                    Ok(0) => cells += 1,
                    other => failures.push(format!(
                        "{} O{opt} {lane}: {} (expected Ok(0))",
                        guest.name,
                        match other {
                            Ok(code) => format!("Ok({code})"),
                            Err(error) =>
                                format!("Err({})", error.chars().take(400).collect::<String>()),
                        }
                    )),
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "array::IntoIter terminals (exit bit i = case i of the guest returned a wrong value; \
         artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(cells, 24, "every array::IntoIter cell must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during array::IntoIter cells"
    );
    eprintln!("TCG_ARRAY_INTO_ITER cells={cells} frontend=off certs=off");
}

/// Run `program` to completion: its exit code or terminating signal, and its
/// stderr with the thread id dropped from each `thread '..' (id) panicked at`
/// line, so two processes' panic reports compare by payload and location.
fn execute_outcome(program: &Path) -> Result<(String, String), String> {
    execute_outcome_within(program, Duration::from_secs(30))
}

/// [`execute_outcome`] with an explicit wall-clock bound: a process still
/// running at `limit` is killed and reported as timed out.
fn execute_outcome_within(program: &Path, limit: Duration) -> Result<(String, String), String> {
    use std::io::Read;
    use std::os::unix::process::ExitStatusExt;
    let mut child = Command::new(program)
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("cannot execute {}: {error}", program.display()))?;
    let started = Instant::now();
    let status = loop {
        match child.try_wait().map_err(|error| error.to_string())? {
            Some(status) => break status,
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                return Err("native execution timed out".to_owned());
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    };
    let mut raw = Vec::new();
    child
        .stderr
        .take()
        .expect("piped stderr")
        .read_to_end(&mut raw)
        .map_err(|error| error.to_string())?;
    let status = match (status.code(), status.signal()) {
        (Some(code), _) => format!("exit={code}"),
        (None, Some(signal)) => format!("signal={signal}"),
        (None, None) => format!("unknown status {status:?}"),
    };
    let stderr = String::from_utf8_lossy(&raw)
        .lines()
        .map(|line| match line.split_once(" panicked at ") {
            Some((thread, location)) if thread.starts_with("thread '") => {
                format!("panicked at {location}")
            }
            _ => line.to_owned(),
        })
        .collect::<Vec<_>>()
        .join("\n");
    Ok((status, stderr))
}

/// `vec![x; n]` (the scalar and the struct-image `from_elem` lowerings) and
/// `<[T]>::repeat(n)` reserve `n` (`len * n`) elements. An element extent past
/// `isize::MAX` bytes must take alloc's genuine `capacity_overflow` panic, and
/// an allocation the allocator refuses must reach the allocation-error handler,
/// exactly as LLVM's code does, never store through a null or short buffer.
/// The `fits` guest is the control that the guarded constructors still build
/// and fill. A `len * n` that wraps `usize` in `repeat` (or `str::repeat`) is
/// std's own `checked_mul(n).expect("capacity overflow")`, a panic at its
/// `alloc/src/slice.rs` call site, whether the wrapped product is zero or a
/// large extent the capacity guard would report from `raw_vec` instead.
#[test]
fn collection_constructor_capacity_errors_match_llvm() {
    let guest =
        |name: &'static str, what: &'static str, src: &'static str| Guest { name, what, src };
    let guests = [
        guest(
            "capacity_fits",
            "from_elem scalar and image and repeat that fit build and fill",
            r#"
#[derive(Clone, Copy)]
struct P { a: u32, b: u64 }
#[inline(never)]
fn scalar(n: usize) -> u64 {
    let v = vec![7u64; n];
    let mut s = 0;
    for x in v.iter() { s += *x; }
    s + v.len() as u64
}
#[inline(never)]
fn image(n: usize) -> u64 {
    let v = vec![P { a: 1, b: 2 }; n];
    let mut s = 0;
    for p in v.iter() { s += p.a as u64 + p.b; }
    s + v.len() as u64
}
#[inline(never)]
fn repeat(n: usize) -> u64 {
    let v = [1u64, 2].repeat(n);
    let mut s = 0;
    for x in v.iter() { s += *x; }
    s + v.len() as u64
}
fn main() {
    let n = std::hint::black_box(3usize);
    std::process::exit((scalar(n) + image(n) + repeat(n)) as i32);
}
"#,
        ),
        guest(
            "from_elem_capacity_overflow",
            "vec![u64; usize::MAX / 4] exceeds isize::MAX bytes",
            r#"
#[inline(never)]
fn make(n: usize) -> usize { vec![7u64; n].len() }
fn main() { std::process::exit(make(std::hint::black_box(usize::MAX / 4)) as i32) }
"#,
        ),
        guest(
            "from_elem_byte_wrap",
            "vec![u64; 1 << 61]: cap * size wraps to zero bytes",
            r#"
#[inline(never)]
fn make(n: usize) -> usize { vec![7u64; n].len() }
fn main() { std::process::exit(make(std::hint::black_box(1usize << 61)) as i32) }
"#,
        ),
        guest(
            "from_elem_image_capacity_overflow",
            "vec![struct; usize::MAX / 4] exceeds isize::MAX bytes",
            r#"
#[derive(Clone, Copy)]
struct P { a: u32, b: u64 }
#[inline(never)]
fn make(n: usize) -> usize { vec![P { a: 1, b: 2 }; n].len() }
fn main() { std::process::exit(make(std::hint::black_box(usize::MAX / 4)) as i32) }
"#,
        ),
        guest(
            "repeat_capacity_overflow",
            "[u64; 2].repeat(usize::MAX / 8) exceeds isize::MAX bytes",
            r#"
#[inline(never)]
fn make(s: &[u64], n: usize) -> usize { s.repeat(n).len() }
fn main() { std::process::exit(make(&[1, 2], std::hint::black_box(usize::MAX / 8)) as i32) }
"#,
        ),
        guest(
            "from_elem_allocation_failure",
            "vec![u64; 1 << 59] is a valid layout the allocator refuses",
            r#"
#[inline(never)]
fn make(n: usize) -> usize { vec![7u64; n].len() }
fn main() { std::process::exit(make(std::hint::black_box(1usize << 59)) as i32) }
"#,
        ),
        guest(
            "repeat_allocation_failure",
            "[u64; 2].repeat(1 << 58) is a valid layout the allocator refuses",
            r#"
#[inline(never)]
fn make(s: &[u64], n: usize) -> usize { s.repeat(n).len() }
fn main() { std::process::exit(make(&[1, 2], std::hint::black_box(1usize << 58)) as i32) }
"#,
        ),
        guest(
            "repeat_len_times_n_wraps_to_zero",
            "[u64; 2].repeat(1 << 63): len * n wraps usize to zero",
            r#"
#[inline(never)]
fn make(s: &[u64], n: usize) -> usize { s.repeat(n).len() }
fn main() { std::process::exit(make(&[1, 2], std::hint::black_box(1usize << 63)) as i32) }
"#,
        ),
        guest(
            "repeat_len_times_n_wraps_nonzero",
            "[u64; 3].repeat(1 << 63): len * n wraps usize to 1 << 63",
            r#"
#[inline(never)]
fn make(s: &[u64], n: usize) -> usize { s.repeat(n).len() }
fn main() { std::process::exit(make(&[1, 2, 3], std::hint::black_box(1usize << 63)) as i32) }
"#,
        ),
        guest(
            "str_repeat_len_times_n_wraps",
            "\"ab\".repeat(1 << 63): str::repeat's byte count wraps usize",
            r#"
#[inline(never)]
fn make(s: &str, n: usize) -> usize { s.repeat(n).len() }
fn main() { std::process::exit(make("ab", std::hint::black_box(1usize << 63)) as i32) }
"#,
        ),
    ];
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!("trustcg_capacity_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create capacity runtime directory");
    let mut cells = 0;
    let mut failures = Vec::new();
    for guest in &guests {
        for opt in 0..=3 {
            let oracle =
                compile(&dir, guest, opt, None).and_then(|program| execute_outcome(&program));
            let candidate = compile(&dir, guest, opt, Some(&backend))
                .and_then(|program| execute_outcome(&program));
            match (oracle, candidate) {
                (Ok(expected), Ok(actual)) if expected == actual => cells += 1,
                (oracle, candidate) => failures.push(format!(
                    "{} O{opt} ({}):\n  LLVM {oracle:?}\n  CG   {candidate:?}",
                    guest.name, guest.what
                )),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "collection constructor capacity errors (artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(cells, guests.len() * 4, "every capacity cell must match");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during capacity controls"
    );
    eprintln!("TCG_COLLECTION_CAPACITY_ERRORS cells={cells} frontend=off certs=off");
}

/// `<[T]>::repeat(n)` and `str::repeat(n)` write `len * n` elements, so a zero
/// product is no work at all: std returns at once for `n == 0` and, for an
/// empty source, doubles a zero-length buffer `log2(n)` times. An empty source
/// with an `n` near `usize::MAX` is therefore an immediate empty result, never
/// `n` passes over an empty copy. The narrow-width guest covers the 1-, 2- and
/// 4-byte fill variants; `repeat_zero_n` is the `n == 0` edge over non-empty
/// sources; `repeat_large_fill` checks every fill variant still writes all
/// `len * n` elements in order when the product is large but allocates. Each
/// guest checks its own results and exits with bit `i` set when its case `i`
/// returned a wrong value, never with a length (the OS keeps only the low 8
/// bits of an exit status, so a wrong length such as `1 << 40` would read as
/// exit 0). Each execution is bounded, so a fill that does not stop is a
/// reported timeout instead of a stalled suite. Every CG binary must link a
/// `__trustcg_slice_repeat_*` fill, so a cell is evidence about the bridge's
/// own `repeat` lowering, not a compiled std body.
#[test]
fn slice_repeat_zero_total_and_large_fill_match_llvm() {
    let guest =
        |name: &'static str, what: &'static str, src: &'static str| Guest { name, what, src };
    let guests = [
        guest(
            "repeat_empty_u64_huge_n",
            "[0u64; 0].repeat(usize::MAX / 2) is an empty Vec",
            r#"
#[inline(never)]
fn make(s: &[u64], n: usize) -> usize { s.repeat(n).len() }
fn main() {
    let mut bad = 0;
    if make(&[0u64; 0], std::hint::black_box(usize::MAX / 2)) != 0 { bad |= 1; }
    std::process::exit(bad)
}
"#,
        ),
        guest(
            "str_repeat_empty_huge_n",
            "\"\".repeat(1 << 40) is an empty String",
            r#"
#[inline(never)]
fn make(s: &str, n: usize) -> usize { s.repeat(n).len() }
fn main() {
    let mut bad = 0;
    if make("", std::hint::black_box(1usize << 40)) != 0 { bad |= 1; }
    std::process::exit(bad)
}
"#,
        ),
        guest(
            "repeat_empty_narrow_widths_max_n",
            "empty u8/u16/f32 sources repeated usize::MAX times are empty",
            r#"
#[inline(never)]
fn r8(s: &[u8], n: usize) -> usize { s.repeat(n).len() }
#[inline(never)]
fn r16(s: &[u16], n: usize) -> usize { s.repeat(n).len() }
#[inline(never)]
fn r32(s: &[f32], n: usize) -> usize { s.repeat(n).len() }
fn main() {
    let n = std::hint::black_box(usize::MAX);
    let mut bad = 0;
    if r8(&[], n) != 0 { bad |= 1; }
    if r16(&[], n) != 0 { bad |= 2; }
    if r32(&[], n) != 0 { bad |= 4; }
    std::process::exit(bad)
}
"#,
        ),
        guest(
            "repeat_zero_n",
            "non-empty sources repeated zero times are empty",
            r#"
#[inline(never)]
fn r64(s: &[u64], n: usize) -> usize { s.repeat(n).len() }
#[inline(never)]
fn r8(s: &[u8], n: usize) -> usize { s.repeat(n).len() }
#[inline(never)]
fn rs(s: &str, n: usize) -> usize { s.repeat(n).len() }
fn main() {
    let n = std::hint::black_box(0usize);
    let mut bad = 0;
    if r64(&[1, 2, 3], n) != 0 { bad |= 1; }
    if r8(&[9], n) != 0 { bad |= 2; }
    if rs("abc", n) != 0 { bad |= 4; }
    std::process::exit(bad)
}
"#,
        ),
        guest(
            "repeat_large_fill",
            "non-empty sources repeated 10^5..2^20 times fill every element in order",
            r#"
#[inline(never)]
fn r8(s: &[u8], n: usize) -> bool {
    let v = s.repeat(n);
    let (mut ok, mut i) = (v.len() == s.len() * n, 0);
    for x in v.iter() { ok &= *x == s[i % s.len()]; i += 1; }
    ok && i == s.len() * n
}
#[inline(never)]
fn r16(s: &[i16], n: usize) -> bool {
    let v = s.repeat(n);
    let (mut ok, mut i) = (v.len() == s.len() * n, 0);
    for x in v.iter() { ok &= *x == s[i % s.len()]; i += 1; }
    ok && i == s.len() * n
}
#[inline(never)]
fn r32(s: &[u32], n: usize) -> bool {
    let v = s.repeat(n);
    let (mut ok, mut i) = (v.len() == s.len() * n, 0);
    for x in v.iter() { ok &= *x == s[i % s.len()]; i += 1; }
    ok && i == s.len() * n
}
#[inline(never)]
fn r64(s: &[f64], n: usize) -> bool {
    let v = s.repeat(n);
    let (mut ok, mut i) = (v.len() == s.len() * n, 0);
    for x in v.iter() { ok &= *x == s[i % s.len()]; i += 1; }
    ok && i == s.len() * n
}
#[inline(never)]
fn rs(s: &str, n: usize) -> bool {
    let v = s.repeat(n);
    let (mut ok, mut i) = (v.len() == s.len() * n, 0);
    for x in v.as_bytes().iter() { ok &= *x == s.as_bytes()[i % s.len()]; i += 1; }
    ok && i == s.len() * n
}
fn main() {
    let mut bad = 0;
    if !r8(&[1, 2, 3], std::hint::black_box(1 << 20)) { bad |= 1; }
    if !r16(&[-4, 5, 6, -7], std::hint::black_box(100_000)) { bad |= 2; }
    if !r32(&[7, 9], std::hint::black_box(300_000)) { bad |= 4; }
    if !r64(&[1.5, -0.25], std::hint::black_box(70_000)) { bad |= 8; }
    if !rs("xyz", std::hint::black_box(100_000)) { bad |= 16; }
    std::process::exit(bad)
}
"#,
        ),
    ];
    let limit = Duration::from_secs(10);
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact test-build backend");
    let dir = std::env::temp_dir().join(format!("trustcg_repeat_fill_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create repeat fill runtime directory");
    let mut cells = 0;
    let mut failures = Vec::new();
    for guest in &guests {
        for opt in 0..=3 {
            let oracle = compile(&dir, guest, opt, None)
                .and_then(|program| execute_outcome_within(&program, limit));
            let candidate = compile(&dir, guest, opt, Some(&backend)).and_then(|program| {
                let symbols = Command::new("nm")
                    .arg(&program)
                    .output()
                    .map_err(|error| format!("nm {}: {error}", program.display()))?;
                if !String::from_utf8_lossy(&symbols.stdout).contains("__trustcg_slice_repeat_") {
                    return Err(
                        "CG binary does not link a __trustcg_slice_repeat_* fill".to_owned()
                    );
                }
                execute_outcome_within(&program, limit)
            });
            match (oracle, candidate) {
                (Ok(expected), Ok(actual))
                    if expected == actual && expected == ("exit=0".to_owned(), String::new()) =>
                {
                    cells += 1
                }
                (oracle, candidate) => failures.push(format!(
                    "{} O{opt} ({}):\n  LLVM {oracle:?}\n  CG   {candidate:?}",
                    guest.name, guest.what
                )),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "slice/str repeat fills (expected exit 0 with no stderr; artifacts {}):\n{}",
        dir.display(),
        failures.join("\n")
    );
    assert_eq!(cells, guests.len() * 4, "every repeat cell must match");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during repeat cells"
    );
    eprintln!("TCG_SLICE_REPEAT_FILL cells={cells} frontend=off certs=off");
}

/// A genuine `IntoIter<T, Custom<Global>>` is not a Global iterator. The LLVM
/// provider constructs its real state; LLVM's consumer must invoke the custom
/// deallocation exactly once. CG must decline the named consumer, rather than
/// peeling arbitrary generic allocator arguments to a false Global witness.
#[test]
fn custom_generic_into_iter_allocator_is_not_global() {
    use std::fs::File;
    use std::process::ExitStatus;
    const PROVIDER: &str = r##"#![feature(allocator_api)]
use std::alloc::{Allocator, AllocError, Global, Layout};
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicUsize, Ordering};
pub struct Custom<A>(pub PhantomData<A>);
static FREES: AtomicUsize = AtomicUsize::new(0);
unsafe impl Allocator for Custom<Global> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        FREES.fetch_add(1, Ordering::SeqCst);
        unsafe { Global.deallocate(ptr, layout) }
    }
}
#[inline(never)]
pub fn make_iter() -> std::vec::IntoIter<u64, Custom<Global>> {
    let mut v = Vec::new_in(Custom::<Global>(PhantomData));
    v.push(17); v.push(29); v.into_iter()
}
#[inline(never)] pub fn reset() { FREES.store(0, Ordering::SeqCst); }
#[inline(never)] pub fn frees() -> usize { FREES.load(Ordering::SeqCst) }
"##;
    const CALLEE: &str = r##"#![feature(allocator_api)]
extern crate provider;
use provider::Custom;
use std::alloc::Global;
#[unsafe(no_mangle)]
#[inline(never)]
pub fn consume(mut it: std::vec::IntoIter<u64, Custom<Global>>) -> u64 {
    let value = it.next().unwrap_or(0);
    drop(it);
    value
}
"##;
    const CALLER: &str = r##"#![feature(allocator_api)]
extern crate provider;
extern crate callee;
fn main() {
    let it = provider::make_iter();
    provider::reset();
    let value = callee::consume(it);
    let frees = provider::frees();
    assert_eq!((value, frees), (17, 1));
}
"##;
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read exact backend");
    let compiler = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let compiler_before = std::fs::read(&compiler).expect("read exact build compiler");
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock after epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trustcg_custom_intoiter_{}_{}",
        std::process::id(),
        nonce
    ));
    std::fs::create_dir(&dir).expect("fresh custom iterator directory");
    let mut llvm_native = 0;
    let mut cg_refused = 0;
    for opt in [0u8, 2] {
        let cell = dir.join(format!("O{opt}"));
        std::fs::create_dir(&cell).expect("fresh optimization cell");
        for (name, text) in [
            ("provider.rs", PROVIDER),
            ("callee.rs", CALLEE),
            ("caller.rs", CALLER),
        ] {
            std::fs::write(cell.join(name), text).expect("write exact fixture");
        }
        let compile_part = |label: &str,
                            source: &str,
                            output: &Path,
                            args: &[OsString],
                            selected: Option<&Path>|
         -> Result<(ExitStatus, String), String> {
            let log = cell.join(format!("{label}.log"));
            let mut command = toolchain_support::rustc_command();
            command.args([
                "--target",
                host_target_support::AARCH64_TARGET,
                "-Cpanic=abort",
                "-Coverflow-checks=off",
                "-Ccodegen-units=1",
            ]);
            command.arg(format!("-Copt-level={opt}"));
            command
                .arg("-L")
                .arg(format!("dependency={}", cell.display()));
            command.args(args);
            if let Some(selected) = selected {
                command.arg(backend_arg(selected));
                command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
            }
            command.arg(cell.join(source)).arg("-o").arg(output);
            command.stdout(Stdio::null());
            command.stderr(Stdio::from(File::create(&log).map_err(|e| e.to_string())?));
            let mut child = command.spawn().map_err(|e| e.to_string())?;
            let started = Instant::now();
            let status = loop {
                match child.try_wait().map_err(|e| e.to_string())? {
                    Some(status) => break status,
                    None if started.elapsed() >= Duration::from_secs(240) => {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(format!("{label} compiler timed out"));
                    }
                    None => std::thread::sleep(Duration::from_millis(5)),
                }
            };
            Ok((
                status,
                std::fs::read_to_string(log).map_err(|e| e.to_string())?,
            ))
        };
        let provider = cell.join("libprovider.rlib");
        let provider_args: Vec<OsString> = ["--crate-name", "provider", "--crate-type", "rlib"]
            .into_iter()
            .map(OsString::from)
            .collect();
        let (status, stderr) = compile_part(
            "provider-llvm",
            "provider.rs",
            &provider,
            &provider_args,
            None,
        )
        .expect("LLVM provider compile completion");
        assert!(status.success(), "O{opt} LLVM provider: {stderr}");
        let provider_extern = OsString::from(format!("provider={}", provider.display()));
        let mut callee_args: Vec<OsString> =
            ["--crate-name", "callee", "--crate-type", "rlib", "--extern"]
                .into_iter()
                .map(OsString::from)
                .collect();
        callee_args.push(provider_extern.clone());
        let library = cell.join("libcallee.rlib");
        let (status, stderr) =
            compile_part("callee-llvm", "callee.rs", &library, &callee_args, None)
                .expect("LLVM consumer compile completion");
        assert!(status.success(), "O{opt} LLVM consumer: {stderr}");
        let caller_args = vec![
            OsString::from("--crate-name"),
            OsString::from("caller"),
            OsString::from("--extern"),
            provider_extern,
            OsString::from("--extern"),
            OsString::from(format!("callee={}", library.display())),
        ];
        let program = cell.join("oracle");
        let (status, stderr) =
            compile_part("caller-llvm", "caller.rs", &program, &caller_args, None)
                .expect("LLVM caller compile completion");
        assert!(status.success(), "O{opt} LLVM caller: {stderr}");
        assert_eq!(
            execute(&program),
            Ok(0),
            "O{opt} LLVM must return17/custom frees1"
        );
        llvm_native += 1;
        let candidate = cell.join("libcallee-cg.rlib");
        let (status, stderr) = compile_part(
            "callee-cg",
            "callee.rs",
            &candidate,
            &callee_args,
            Some(&backend),
        )
        .expect("CG consumer compile completion");
        assert!(
            !status.success(),
            "O{opt}: custom iterator consumer must be refused"
        );
        assert!(
            stderr.lines().any(|line| {
                line.trim_start().starts_with("- consume:")
                    && line.contains("[TCG-VEC-INTOITER-LAYOUT]")
                    && line.contains("custom allocator")
            }),
            "O{opt}: expected named consume custom-allocator refusal, got {stderr}"
        );
        cg_refused += 1;
        assert_eq!(
            std::fs::read(&backend).expect("reread backend"),
            backend_before
        );
        assert_eq!(
            std::fs::read(&compiler).expect("reread compiler"),
            compiler_before
        );
        for (name, text) in [
            ("provider.rs", PROVIDER),
            ("callee.rs", CALLEE),
            ("caller.rs", CALLER),
        ] {
            assert_eq!(
                std::fs::read_to_string(cell.join(name)).expect("reread fixture"),
                text
            );
        }
    }
    assert_eq!((llvm_native, cg_refused), (2, 2));
    eprintln!("TCG_CUSTOM_INTOITER_ALLOCATOR llvm_native=2 cg_refused=2 frontend=off certs=off");
}
