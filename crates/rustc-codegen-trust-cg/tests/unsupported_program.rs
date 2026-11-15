#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use positive_evidence::{Certs, Evidence};

// Regression test for the rustc_codegen_trust_cg M0 load/fail invariant.
//
// The hello-loop path has moved beyond pure M0, so this test uses an
// intentionally unsupported program to keep proving the original M0
// acceptance criterion: rustc loads our dylib, reaches the backend
// entrypoint, and then fails with our diagnostic rather than a dlopen
// or codegen-backend load error.

use std::path::{Path, PathBuf};
use std::process::ExitStatus;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn write_temp_source(stem: &str, contents: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("rcl2_{}_{}.rs", stem, std::process::id()));
    std::fs::write(&path, contents).expect("failed to write temp source file");
    path
}

struct BackendRun {
    status: ExitStatus,
    stderr: String,
}

fn run_backend_on_source(stem: &str, src: &str) -> BackendRun {
    run_backend_on_source_with(stem, src, &[], &[])
}

/// `run_backend_on_source` with `extra_args` passed straight to trustc (for
/// example `-Copt-level=2`).
fn run_backend_on_source_with_args(stem: &str, src: &str, extra_args: &[&str]) -> BackendRun {
    run_backend_on_source_with(stem, src, extra_args, &[])
}

/// `run_backend_on_source` with backend `knobs` passed as
/// `-Ztrust-ir-cg-args` on the (bridge-only) compile. An empty `knobs` is the
/// default proof lane, which is what `run_backend_on_source` — and so every
/// fail-closed test in this file — keeps using.
fn run_backend_on_source_with_knobs(stem: &str, src: &str, knobs: &[&str]) -> BackendRun {
    run_backend_on_source_with(stem, src, &[], knobs)
}

fn run_backend_on_source_with(
    stem: &str,
    src: &str,
    extra_args: &[&str],
    knobs: &[&str],
) -> BackendRun {
    let src_path = write_temp_source(stem, src);
    let out_bin = std::env::temp_dir().join(format!("rcl2_{stem}_out_{}", std::process::id()));
    let dylib = ensure_dylib_built();

    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let mut cmd = toolchain_support::rustc_command();
    cmd.arg(&backend_arg).args(extra_args);
    if !knobs.is_empty() {
        cmd.arg(toolchain_support::backend_knobs_arg(knobs));
    }
    let output = cmd
        .arg("-o")
        .arg(&out_bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");

    let _ = std::fs::remove_file(&src_path);
    let _ = std::fs::remove_file(&out_bin);

    BackendRun {
        status: output.status,
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

fn assert_no_backend_load_failure(stderr: &str) {
    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
}

// The capability tests below compile in the default (certificates-on) lane,
// and a refusal of any kind fails them. On aarch64-apple-darwin a
// proof-promotion refusal (`[TCG-PROOF-465]`) used to be an accepted early
// return, which passed a capability test without its capability assertions
// (ledger L06-P10).

/// Whether a test that passes a backend knob can run on this host.
///
/// On aarch64-apple-darwin, where `scripts/check_darwin_aarch64_bridge.py`
/// requires this target and its preflight refuses a compiler without the knob
/// option, a missing option FAILS the test instead of letting it pass without
/// running (ledger L06-P10). Other hosts keep the shared rule and skip with a
/// named reason (`toolchain_support::skip_without_backend_knobs`).
fn knob_test_can_run(test: &str) -> bool {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        assert!(
            toolchain_support::backend_knobs_supported(),
            "{test}: the build compiler does not list the backend knob option in `-Z help`, \
             so this test's `no-proof-certs` knob cannot be expressed; on \
             aarch64-apple-darwin a missing prerequisite fails"
        );
        true
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    {
        !toolchain_support::skip_without_backend_knobs(test)
    }
}

/// MISCOMPILE #72 (now SUPPORTED): a branch-varying mutable scalar reference
/// (`selected` is `&mut left` on one path and `&mut right` on another) used to
/// fail closed because the "borrowed scalar" SNAPSHOT model could not represent a
/// reference that names different locals across control flow. The fix cells every
/// such referent (a stack slot), so `&mut left`/`&mut right` become real cell
/// pointers, the join is an ordinary pointer phi, and the reference can be stored,
/// escaped, and dereferenced correctly. This program must now COMPILE (runtime
/// correctness — including escaping the reference into a tuple and writing through
/// it — is locked in by the differential test m72_branch_ref_join_x86.rs).
#[test]
fn branch_variant_mutable_scalar_reference_tuple_escape_now_compiles_after_backend_load() {
    let src = r#"
#![no_main]

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let mut left = 11u64;
    let mut right = 29u64;
    let mut selected = &mut left;

    if argc != 0 {
        selected = &mut right;
    }

    *selected = 7;
    let escaped = (selected,);
    let _ = escaped;
    (left.wrapping_add(right) & 0xFF) as i32
}
"#;
    let output = run_backend_on_source("branch_mutable_scalar_reference_escape", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        output.status.success(),
        "branch-varying mutable scalar reference (now supported via cells) failed to compile. \
         stderr was: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("cannot compile required function with unsupported MIR"),
        "branch-varying mutable scalar reference unexpectedly still fails closed. stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
    positive_evidence::record(Evidence::Compiled, Certs::On);
}

#[test]
fn promoted_scalar_reference_return_tuple_escape_fails_closed_after_backend_load() {
    let src = r#"
#![no_main]

#[inline(never)]
fn pick_ref<'a>(flag: bool, left: &'a u64, right: &'a u64) -> &'a u64 {
    if flag { right } else { left }
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let left = 11u64;
    let right = 29u64;
    let selected = pick_ref(argc != 0, &left, &right);
    let escaped = (selected,);
    let _ = escaped;
    0
}
"#;
    let output = run_backend_on_source("scalar_reference_return_tuple_escape", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    // Still FAILS CLOSED (the escaping borrowed scalar reference is not materialized
    // through a stable home). The guard MESSAGE was refreshed to the current
    // wording; the fail-closed behavior (and the soundness it protects — a LIVE
    // `*escaped.0` deref of the same shape also fails closed, verified
    // differentially) is unchanged.
    assert!(
        !output.status.success(),
        "escaping promoted scalar reference return unexpectedly compiled successfully"
    );
    assert!(
        stderr.contains(
            "rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"
        ),
        "rustc did not reach the rustc_codegen_trust_cg unsupported-MIR diagnostic. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains(
            "promoted scalar reference return then arg requires scalar borrow materialization"
        ) || stderr.contains("borrowed scalar reference used without deref"),
        "promoted scalar reference return escape guard did not fail on the intended tuple move. stderr was: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

#[test]
fn mutable_scalar_reference_return_compiles_via_general_lowering() {
    // A `&mut T`-returning fn (`pick_mut` selects one of two `&mut u64` params)
    // used to be HARD-DECLINED by `direct_scalar_ref_select_return` ("promoted
    // mutable scalar reference return is unsupported") BEFORE it even checked the
    // body shape, failing the whole compile. That recognizer only models the
    // IMMUTABLE select and threads a value; a `&mut` return is not that shape, so
    // it now falls through (`Ok(None)`) to general call lowering, which owns the
    // pointer + write-back.
    //
    // Validated sound by: a RUN differential over 30 mutable-ref-return shapes
    // (0 wrong, proofs-ON and proofs-OFF, the refinement oracle accepts all), a
    // CROSS-BACKEND pointer-return ABI check (llvm-caller x tcg-callee and
    // tcg-caller x llvm-callee, 8/8 MATCH -- the `&mut` return lands in x0 exactly
    // where LLVM expects), corpus .text 18/18 identity, and abi-xback 320/0. See
    // benchmarks/shape-coverage/progs/s72_mut_ref_return.rs for the run regression.
    let src = r#"
#![no_main]

#[inline(never)]
fn pick_mut<'a>(flag: bool, left: &'a mut u64, right: &'a mut u64) -> &'a mut u64 {
    if flag { right } else { left }
}

#[no_mangle]
pub extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let mut left = 11u64;
    let mut right = 29u64;
    let selected = pick_mut(argc != 0, &mut left, &mut right);
    *selected = *selected + 1;
    (left.wrapping_add(right) & 0xFF) as i32
}
"#;
    let output = run_backend_on_source("mutable_scalar_reference_return", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        output.status.success(),
        "mutable scalar reference return (now supported via general call lowering) \
         failed to compile. stderr was: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("promoted mutable scalar reference return is unsupported"),
        "mutable scalar reference return still hit the REMOVED hard-decline guard. \
         stderr was: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
    positive_evidence::record(Evidence::Compiled, Certs::On);
}

/// CONTROL for the reference-escaping scalar-cell widening.
///
/// `compute_scalar_cell_locals`' reference-RETURNING-callee arm used to cell only
/// `Int/Uint/Float/Bool/Char` referents, which made `direct_scalar_ref_select_return`
/// refuse every other one ("promoted mutable scalar reference return is
/// unsupported" — 6 `library/core` roots, plus 2 for the shared-aggregate twin).
/// The cure is the ADDRESS: cell every referent the memory model can represent.
///
/// An INTERCEPTED collection is the one thing that must stay OUT. A `Vec` models
/// as a single `Ptr` whose value IS the address of a synthesized `{ptr,cap,len}`
/// slot produced by the interception, not by a cell slot; celling the local puts a
/// second slot in front of it and the intercept's value is never defined at its
/// use. `cellable_reference_referent_ty` excludes it by the interception PREDICATE
/// (`vec_element_ty`/`is_string_ty`/…) rather than by a typed heuristic — a typed
/// guard is defeatable (`&mut *(p as *mut NonNull<u8> as *mut u8)` walks through
/// one), which is why the widening is on the CELL and not on the refusal.
///
/// This program must therefore still FAIL CLOSED, with the same message.
/// A run that COMPILES is a regression, not a win. The positive half of the pair
/// (a non-primitive referent that now compiles AND prints the right value) is
/// `bridge_corpus/fix_refret_cell_nonprimitive.rs`.
#[test]
fn intercepted_collection_reference_return_still_fails_closed() {
    let src = r#"#![crate_type = "lib"]
#[inline(never)]
fn first_mut(v: &mut Vec<u64>) -> &mut u64 {
    &mut v[0]
}

#[no_mangle]
pub fn drive() -> u64 {
    let mut v: Vec<u64> = Vec::new();
    v.push(3);
    let r = first_mut(&mut v);
    *r = 8;
    v[0]
}
"#;
    let output = run_backend_on_source("refret_vec_intercepted_control", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert_no_backend_load_failure(stderr);
    assert!(
        !output.status.success(),
        "an INTERCEPTED `Vec` referent reaching a reference-returning callee compiled; \
         celling it breaks the Vec interception, so this must stay fail-closed. \
         stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("promoted mutable scalar reference return is unsupported"),
        "the `Vec` control failed closed, but not with the reference-return refusal — the \
         exclusion may have moved. stderr was: <<<{stderr}>>>"
    );
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

/// CONTROL for the WRAPPED twin of the reference-return refusal: `[TCG-REFRET-WRAP]`.
///
/// The same intercepted `Vec` referent the control above keeps uncelled reaches a
/// local callee whose return WRAPS the `&mut u64` in a struct (`W { p: &mut v[0] }`).
/// The bare-`&mut` refusal in `direct_scalar_ref_select_return` cannot see a wrapped
/// return; `[TCG-REFRET-WRAP]` is the guard that does, and nothing else in `tests/`
/// asserted that it fires.
///
/// This pins the guard's PRESENCE, by its tag: with the guard deleted this program
/// compiles when proof certificates are off, and with them on (as here) it is
/// refused by something else; on aarch64-apple-darwin that is `[TCG-PROOF-465]`,
/// the whole-lane opcode-inventory refusal, so the fail-closed assertion alone
/// would pass vacuously and it is the `[TCG-REFRET-WRAP]` assertion that fails
/// (measured on `5828b4ce6`). (Measured on `ad7ee9c4e`: the deleted-guard build
/// happens to print the right `v0=10` for THIS program, because the store goes
/// through the Vec's heap pointer; the shape it silently miscompiles is a projected
/// field borrow, `make(&mut s.a) -> W { p: &mut u64 }`, `a=1` against LLVM's `a=10`.
/// See the header of the corpus file.) The source is the corpus file itself, so the
/// pin and the fixture cannot drift apart.
#[test]
fn wrapped_mut_scalar_ref_return_still_fails_closed() {
    let src = include_str!("bridge_corpus/fix_o_refret_wrap_control.rs");
    let output = run_backend_on_source("refret_wrap_control", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert_no_backend_load_failure(stderr);
    assert!(
        !output.status.success(),
        "an INTERCEPTED `Vec` referent reaching a callee that returns a WRAPPED `&mut u64` \
         compiled; the referent has no address the returned reference can alias, so this \
         must stay fail-closed. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains(
            "[TCG-REFRET-WRAP] call passes a `&mut`/`&` to a scalarized local and returns a \
             `&mut` scalar reference wrapped in an aggregate/enum (&mut u64)"
        ),
        "the wrapped-return control failed closed, but not with `[TCG-REFRET-WRAP]` — the \
         guard may have moved or been bypassed. stderr was: <<<{stderr}>>>"
    );
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

/// The CELLED RETURN LOCAL, positive half.
///
/// `&res` taken on the tail-returned local (NRVO makes `res` BE `_0`) cells `_0`
/// through the widened reference-escaping arm of `compute_scalar_cell_locals`, so
/// every whole-local write to `_0` STORES into the cell instead of binding an SSA
/// scalar. `TerminatorKind::Return` then asked `value_for_scalar_binding` for
/// `_0`, found nothing in `scalar_values`, and FABRICATED the synthetic
/// `ValueId(0)` — a never-defined SSA use, so the whole function failed closed at
/// `[TCG-SSA-071] value ValueId(0) used in bbN is never defined`. That was
/// `core::io::error::repr::Repr::new_custom`, the one genuine capability LOSS of
/// the reference-return cell widening.
///
/// CAPABILITY, not soundness: the definition was in the cell and the return was
/// not looking there, so the return LOADS it. The runtime-value half of this pin
/// is `bridge_corpus/fix_return_celled_local.rs` (differential vs LLVM at
/// -O0/-O2/-O3).
///
/// WHY THIS TEST PASSES `no-proof-certs`. With proof certificates ON (the
/// default) the bridge currently refuses AArch64 objects at proof promotion
/// (`[TCG-PROOF-465] … emitted opcode inventory found N uncovered non-pseudo
/// opcode(s)`) — a whole-lane fact about the AArch64 opcode inventory, raised
/// after lowering, that says nothing about the celled return. Left on, the
/// success assertion below fails on that refusal on an AArch64 host, red for a
/// reason unrelated to this pin.
/// What the knob changes (the bridge sets `emit_proofs = false`): no proof
/// certificate is generated or promoted and the bridge re-checks no proof bundle;
/// exception tables are not refused as unproved; the verifier is not pre-warmed;
/// the non-vacuity post-check on the raw TV-3 dataflow observation is skipped (the
/// gate itself still enforces); an `artifact-cache-dir` cache, if set, uses the
/// unchecked partition; and AArch64 publication runs at the compatibility policy
/// instead of proof grade (`with_proof_grade_aarch64_publication_if`), so
/// decode-allowlisted words are counted rather than refused, the final-layout
/// cross-check does not bind encoded edges to the recorded CFG, and `TCG_*`
/// downgrades of the post-RA and decode nets and late-layout controls are honored
/// rather than refused (with none set, those nets enforce). The -O1+ inliner
/// may also splice inline-only (`AvailableExternally`) bodies that no
/// authenticated import defines, which a proof compile withholds
/// (`InlineOnlyAdmission::for_proof_claim`); the bridge emits no such body, so
/// that changes nothing here. MIR lowering is unchanged.
/// `[TCG-SSA-071]` and `[TCG-RET-UNBOUND]` are MIR-lowering refusals, so the
/// assertions that they are absent are as strong as with certificates on; the
/// success assertion holds against the compatibility publication checks listed.
/// It is scoped to this test: the fail-closed tests above and below keep the
/// default lane.
#[test]
fn celled_return_local_loads_from_its_cell() {
    if !knob_test_can_run("celled_return_local_loads_from_its_cell") {
        return;
    }
    let src = r#"#![crate_type = "lib"]
#[repr(transparent)]
pub struct Repr(*mut u8);

impl Repr {
    // A `&self` method whose RETURN TYPE CARRIES A REFERENCE: the trigger for the
    // reference-escaping cell arm (`Repr::data(&self) -> ErrorData<&Custom>` in
    // `library/core`).
    #[inline(never)]
    pub unsafe fn peek(&self) -> &u64 {
        unsafe { &*(self.0 as *const u64) }
    }

    #[inline(never)]
    pub fn make(base: *mut u8) -> Self {
        let res = Repr(base);
        // `&res` == `&_0` after NRVO: this is what cells `_0`.
        assert!(unsafe { *res.peek() } != 0);
        res
    }
}

#[no_mangle]
pub fn drive(p: *mut u8) -> *mut u8 {
    Repr::make(p).0
}
"#;
    let output = run_backend_on_source_with_knobs("celled_return_local", src, &["no-proof-certs"]);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert_no_backend_load_failure(stderr);
    assert!(
        !stderr.contains("[TCG-SSA-071]"),
        "the celled return local fabricated a never-defined ValueId again. \
         stderr was: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("[TCG-RET-UNBOUND]"),
        "the celled return local reached the unbound-`_0` refusal, so the cell arm \
         did not fire. stderr was: <<<{stderr}>>>"
    );
    assert!(
        output.status.success(),
        "the celled return local failed closed. stderr was: <<<{stderr}>>>"
    );
    positive_evidence::record(Evidence::Compiled, Certs::Off);
}

/// The NON-zero-sized loop carrier — `core::fmt::write`'s `NonNull<u8>` cursor,
/// the twin of the ZST exemption's control — is ADMITTED as a loop-header phi
/// and its in-loop update is THREADED: the compiled program must agree with
/// LLVM on every value it prints.
///
/// HISTORY, because this test asserted the OPPOSITE for a week. It was written
/// (1e94902d3, 2026-09-14) to pin that this shape FAILS CLOSED, on the located
/// blocker that `local_is_scalar` keys on `trust_ir::Ty::bit_width()`, which is
/// `None` for every pointer-like type, so a pointer carrier could never become
/// a header phi and `loop_carried_completeness_error` refused it. One day later
/// da9885c03 admitted a ONE-LANE pointer-width carrier as a header phi (the
/// authority being `fmt` interception liveness, not the type), closed
/// `core::fmt::write` as a census root, and flipped the corpus row
/// `fix_q_pointer_loop_carrier` from REFUSED to AGREE at both opt levels — but
/// this file, which nothing ran, kept asserting the refusal. The 2026-09-21
/// first run of this crate's own suite found it red, and the program it
/// compiles was checked against LLVM before this rewrite: identical stdout and
/// exit code at `-O0` and `-O2`.
///
/// So the contract this test pins is the CURRENT one, and it pins the property
/// the old refusal existed to protect: "admitting it without a real header phi
/// DROPS the in-loop update". A dropped update here would read the same byte on
/// every iteration and the hashes would diverge from LLVM's; the test compares
/// every printed value. A REFUSAL is now a regression too — a failure to
/// compile fails the test rather than being read as fail-closed — because a
/// backend that stops admitting this shape re-opens `core::fmt::write`.
#[test]
fn nonzst_pointer_loop_carrier_compiles_and_threads_its_update() {
    // PROOFS-OFF DIAGNOSTIC on the bridge side (see the comment at the knob
    // below); see `knob_test_can_run` for a compiler without the knob option.
    if !knob_test_can_run("nonzst_pointer_loop_carrier_compiles_and_threads_its_update") {
        return;
    }
    // `#![no_std]`/`#![no_main]` so the program links against nothing but
    // libSystem and the bridge's own output is what runs — the same fixture
    // convention as the host-native `*_differential.rs` harnesses.
    let src = r#"#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}
use core::hint::black_box as bb;
use core::ptr::NonNull;

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, n: usize) -> isize;
}

fn put(v: u64) {
    let mut b = [0u8; 24];
    let mut i = 23usize;
    b[23] = b'\n';
    let mut x = v;
    loop {
        i -= 1;
        b[i] = b'0' + (x % 10) as u8;
        x /= 10;
        if x == 0 {
            break;
        }
    }
    unsafe {
        write(1, b.as_ptr().wrapping_add(i), 24 - i);
    }
}

/// The exact shape of `core::fmt::write`'s cursor loop: a `NonNull<u8>`
/// carrier advanced every iteration and read through on the next.
#[inline(never)]
pub fn hash(buf: &[u8]) -> u64 {
    let mut p = NonNull::from(&buf[0]);
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < buf.len() {
        acc = acc
            .wrapping_mul(31)
            .wrapping_add(unsafe { *p.as_ptr() } as u64);
        p = unsafe { NonNull::new_unchecked(p.as_ptr().add(1)) };
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = hash(bb(b"carrier"));
    let b = hash(bb(b"z"));
    let c = hash(bb(b"the quick brown fox jumps over the lazy dog"));
    put(a);
    put(b);
    put(c);
    ((a ^ b ^ c) % 100) as i32
}
"#;
    let dylib = ensure_dylib_built();
    let dir = std::env::temp_dir().join(format!(
        "rcl2_nonzst_pointer_loop_carrier_{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    // Compile (with the bridge when `backend` is `Some`), run, and return
    // (exit code, stdout). A compile failure is a hard failure on EITHER side.
    let compile_and_run = |backend: Option<&Path>, opt: &str| -> (i32, String) {
        let tag = if backend.is_some() { "tcg" } else { "llvm" };
        let bin = dir.join(format!("{tag}_{}", opt.trim_start_matches("-Copt-level=")));
        let mut cmd = toolchain_support::rustc_command();
        cmd.args(["--crate-type", "bin", "-Cpanic=abort", "-Ccodegen-units=1"]);
        cmd.arg("-Clink-arg=-lSystem");
        cmd.arg(opt);
        if let Some(dylib) = backend {
            let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
            backend_arg.push(dylib);
            cmd.arg(backend_arg);
            // Bridge side only, for the reason given in
            // impostor_std_crate_name_differential.rs ("WHY THE BRIDGE SIDE PASSES
            // `no-proof-certs`"): default-on proof certificates currently refuse
            // every AArch64 object at promotion ([TCG-PROOF-465], uncovered opcode
            // inventory), a whole-lane fact orthogonal to the loop carrier this
            // differential measures. The LLVM oracle has no such lane. A LOWERING
            // refusal of the carrier still fails the compile, and so this test.
            cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        }
        cmd.arg("-o").arg(&bin).arg(&src_path);
        let output = cmd.output().expect("spawn the compiler");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        if backend.is_some() {
            assert_no_backend_load_failure(&stderr);
        }
        assert!(
            output.status.success(),
            "{tag} ({opt}): the NON-zero-sized pointer loop carrier did not compile. \
             Since da9885c03 a one-lane pointer-width carrier IS a loop-header phi \
             (this is `core::fmt::write`'s cursor); a refusal here re-opens that \
             root. stderr was: <<<{stderr}>>>"
        );
        let run = std::process::Command::new(&bin)
            .output()
            .expect("run compiled binary");
        let code = run
            .status
            .code()
            .unwrap_or_else(|| panic!("{tag} ({opt}): the program died by signal"));
        (code, String::from_utf8_lossy(&run.stdout).into_owned())
    };

    for opt in ["-Copt-level=0", "-Copt-level=2"] {
        let (llvm_code, llvm_out) = compile_and_run(None, opt);
        assert_eq!(
            llvm_out.lines().count(),
            3,
            "({opt}) the LLVM oracle must print the three hashes; got <<<{llvm_out}>>>"
        );
        let (tcg_code, tcg_out) = compile_and_run(Some(&dylib), opt);
        assert_eq!(
            tcg_out, llvm_out,
            "({opt}) STDOUT differs from LLVM: the loop-carried `NonNull<u8>` update \
             was not threaded through the header phi (a dropped update re-reads the \
             first byte on every iteration)"
        );
        assert_eq!(tcg_code, llvm_code, "({opt}) exit code differs from LLVM");
    }
    let _ = std::fs::remove_dir_all(&dir);
    positive_evidence::record(Evidence::NativeRun, Certs::Off);
}

/// ADDRESS IDENTITY: a reference joined from two raw-pointer locals
/// (`if c { &a } else { &b }`) and a direct `&a` are both passed to a callee
/// that compares them. Neither referent has a real home (a pointer-valued local
/// is neither celled nor slot-backed), so each borrow would be materialized
/// into its own slot and `ptr::eq(r, &a)` would be false where Rust says true.
/// The bridge refuses the pair by name rather than hand out unrelated addresses.
#[test]
fn joined_reference_and_direct_borrow_without_home_fail_closed() {
    let src = r#"#![crate_type = "lib"]
#[inline(never)]
fn same<T>(a: &T, b: &T) -> u32 {
    core::ptr::eq(a, b) as u32
}

#[no_mangle]
pub fn joined(v: u32) -> u32 {
    let x = v;
    let y = v ^ 1;
    let a: *const u32 = &x;
    let b: *const u32 = &y;
    let r = if v & 1 == 0 { &a } else { &b };
    same(r, &a) + 2 * same(r, &b)
}
"#;
    let output = run_backend_on_source("addr_identity_joined_raw", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    assert_no_backend_load_failure(stderr);
    assert!(
        !output.status.success(),
        "a joined reference and a direct borrow of one of its home-less referents \
         compiled; their addresses would be unrelated. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("[TCG-ADDR-IDENTITY]"),
        "the address-identity pair failed closed, but not by name. stderr was: <<<{stderr}>>>"
    );
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

/// ADDRESS IDENTITY: two references joined from overlapping sets of
/// raw-pointer locals (`r1` selects `a` or `b`, `r2` selects `b` or `c`) are
/// passed to a callee that compares them. Both select `b` on some inputs, where
/// Rust says `ptr::eq(r1, r2)`; without a home for the referents each joined
/// reference would be materialized into its own slot and compare unequal. The
/// bridge refuses the pair by name.
#[test]
fn overlapping_joined_references_without_home_fail_closed() {
    let src = r#"#![crate_type = "lib"]
#[inline(never)]
fn same<T>(a: &T, b: &T) -> u32 {
    core::ptr::eq(a, b) as u32
}

#[no_mangle]
pub fn overlapping(v: u32) -> u32 {
    let x = v;
    let y = v ^ 1;
    let z = v ^ 2;
    let a: *const u32 = &x;
    let b: *const u32 = &y;
    let c: *const u32 = &z;
    let r1 = if v & 1 == 0 { &a } else { &b };
    let r2 = if v & 2 == 0 { &b } else { &c };
    same(r1, r2)
}
"#;
    let output = run_backend_on_source("addr_identity_overlapping_joins", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    assert_no_backend_load_failure(stderr);
    assert!(
        !output.status.success(),
        "two joined references sharing a home-less referent compiled; their addresses \
         would be unrelated. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("[TCG-ADDR-IDENTITY]"),
        "the overlapping joins failed closed, but not by name. stderr was: <<<{stderr}>>>"
    );
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

#[test]
fn nested_array_reference_unit_leaf_whole_store_fails_after_backend_load() {
    let src = r#"#![crate_type = "lib"]
#[no_mangle]
pub fn write_nested_array(value: &mut [(u64, ()); 2]) {
    *value = [(1, ()), (4, ())];
}
"#;
    let output = run_backend_on_source("nested_array_reference_abi", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "unsupported unit-leaf nested array whole-store unexpectedly compiled successfully"
    );
    assert!(
        stderr.contains(
            "rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"
        ),
        "rustc did not reach the rustc_codegen_trust_cg unsupported-MIR diagnostic. stderr was: <<<{stderr}>>>"
    );
    // The bridge now SKIPS zero-sized fields (the `()` leaf) when flattening an
    // aggregate — `PhantomData`/`Global`/`()` contribute no bytes and no scalar
    // leaf, which is what lets `Vec`/`RawVec` flatten. So `(u64, ())` flattens to
    // a single `u64`, and this whole-array store no longer trips the unit-leaf
    // guard; instead it fails closed one step later on the *by-value aggregate*
    // store (a whole scalarized aggregate has no single-scalar representation).
    // Either precise fail-closed diagnostic is acceptable — the invariant this
    // test pins is that the program fails closed (never miscompiles, never via a
    // backend load failure), not the exact message.
    assert!(
        stderr.contains("aggregate reference nested field is not memory-scalar")
            || stderr.contains("Unit")
            || stderr.contains("whole scalarized aggregate")
            || stderr.contains("by-value aggregate"),
        "unsupported-program guard did not fail closed on the intended unit-leaf nested array whole-store. stderr was: <<<{stderr}>>>"
    );

    assert_no_backend_load_failure(stderr);
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

#[test]
fn multi_variant_enum_reference_parameter_abi_fails_after_backend_load() {
    let src = r#"#![crate_type = "lib"]
pub enum Choice {
    Left(u64),
    Right(u64),
}

#[no_mangle]
pub fn write_choice(value: &mut Choice, flag: bool) {
    if flag {
        *value = Choice::Left(3);
    } else {
        *value = Choice::Right(5);
    }
}
"#;
    let output = run_backend_on_source("multi_variant_enum_reference_abi", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    // Now SUPPORTED: writing a multi-variant enum through a `&mut` reference
    // compiles. Runtime correctness (the written variant/payload reads back
    // exactly) was verified differentially (LLVM oracle vs trust-cg, O0/O2/O3) —
    // `write_choice(&mut c, flag)` then matching on `c` agrees. (Stale guard
    // assertion refreshed: this used to fail closed before the enum-reference ABI
    // was implemented.)
    assert!(
        output.status.success(),
        "multi-variant enum reference ABI must now COMPILE. stderr was: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
    positive_evidence::record(Evidence::Compiled, Certs::On);
}

/// The defined external symbols of every object in `dir` (`nm -g`, any
/// platform spelling: a Mach-O `_` prefix is removed).
fn defined_external_symbols(dir: &Path) -> std::collections::BTreeSet<String> {
    let mut defined = std::collections::BTreeSet::new();
    for entry in std::fs::read_dir(dir).expect("read the object output directory") {
        let path = entry.expect("object directory entry").path();
        if path.extension().is_none_or(|extension| extension != "o") {
            continue;
        }
        let nm = std::process::Command::new("nm")
            .arg("-g")
            .arg(&path)
            .output()
            .expect("spawn nm");
        assert!(nm.status.success(), "nm -g {path:?} failed: {nm:?}");
        for line in String::from_utf8_lossy(&nm.stdout).lines() {
            let fields: Vec<&str> = line.split_whitespace().collect();
            if let [.., kind, name] = fields.as_slice() {
                if !kind.eq_ignore_ascii_case("u") {
                    let name = if cfg!(target_os = "macos") {
                        name.strip_prefix('_').unwrap_or(name)
                    } else {
                        name
                    };
                    defined.insert(name.to_string());
                }
            }
        }
    }
    defined
}

/// A `#[no_mangle]` export is a required root, and so is its failure route.
///
/// The object compile runs in `join_codegen`, after rustc has dropped the type
/// context, so each pending function's `FailureRoute` is decided in
/// `codegen_crate` and carried to it (`DeferredFn::route`, [MEM-DEFER]). A
/// root whose object compile fails there must be a named failed root, never
/// the drop-with-a-record route of a `#[rustc_std_internal_symbol]` shim: a
/// dropped export compiles the library without the symbol its callers link
/// against. So every export is either named by the failed compile's
/// `[TCG-MIR-UNSUPPORTED]` refusal or defined by an emitted object, and never
/// recorded as a skipped Rust-internal function. On aarch64-apple-darwin in
/// the default proof lane both roots currently fail object emission
/// (`[TCG-PROOF-465]`), which is the path this pins, and the test's positive
/// evidence is an expected refusal. Wherever they compile, the definition
/// check holds instead and the evidence is a compile; `write_choice` is the
/// function `multi_variant_enum_reference_parameter_abi_fails_after_backend_load`
/// requires to compile, so a complete pass of this target credits a compile
/// here (scripts/check_darwin_aarch64_bridge.py), and the deferred failure
/// route then needs another refused root to stay exercised on this host.
#[test]
fn no_mangle_roots_are_never_dropped_when_their_object_compile_fails() {
    let src = r#"#![crate_type = "lib"]
pub enum Choice {
    Left(u64),
    Right(u64),
}

#[no_mangle]
pub fn write_choice(value: &mut Choice, flag: bool) {
    if flag {
        *value = Choice::Left(3);
    } else {
        *value = Choice::Right(5);
    }
}

#[no_mangle]
pub extern "C" fn add_two(x: u64) -> u64 {
    x.wrapping_add(2)
}
"#;
    let roots = ["write_choice", "add_two"];
    let stem = "no_mangle_roots_route";
    let src_path = write_temp_source(stem, src);
    let out_dir = std::env::temp_dir().join(format!("rcl2_{stem}_out_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&out_dir);
    std::fs::create_dir_all(&out_dir).expect("create the object output directory");
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(ensure_dylib_built());
    let output = toolchain_support::rustc_command()
        .arg(&backend_arg)
        .args(["--emit=obj", "-Ccodegen-units=1", "--out-dir"])
        .arg(&out_dir)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");
    let _ = std::fs::remove_file(&src_path);
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert_no_backend_load_failure(&stderr);

    for root in roots {
        assert!(
            !stderr
                .lines()
                .any(|line| line.contains("skipped Rust-internal function")
                    && line.contains(&format!("): {root}: "))),
            "required root `{root}` took the std-internal drop route. stderr: <<<{stderr}>>>"
        );
    }
    if output.status.success() {
        let defined = defined_external_symbols(&out_dir);
        for root in roots {
            assert!(
                defined.contains(root),
                "the compile succeeded but no object defines required root `{root}` \
                 (defined: {defined:?}). stderr: <<<{stderr}>>>"
            );
        }
        let _ = std::fs::remove_dir_all(&out_dir);
        positive_evidence::record(Evidence::Compiled, Certs::On);
    } else {
        assert!(
            stderr.contains(
                "rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"
            ),
            "a failed compile must name its failed required roots. stderr: <<<{stderr}>>>"
        );
        assert!(
            roots.iter().any(|root| stderr
                .lines()
                .any(|line| line.trim_start().starts_with(&format!("- {root}: ")))),
            "the failed compile names none of the required roots. stderr: <<<{stderr}>>>"
        );
        let _ = std::fs::remove_dir_all(&out_dir);
        positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
    }
}

#[test]
// Linux AArch64 has a native positive/rounding regression in
// support/wide_int_float.rs. Other bridge targets retain this boundary.
#[cfg(not(all(target_arch = "aarch64", target_os = "linux")))]
fn unsupported_int_to_float_u128_source_fails_after_backend_load() {
    let src = "fn main() { let _x = 1u128 as f64; }\n";
    let output = run_backend_on_source("bad_int_to_float_u128", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        !output.status.success(),
        "unsupported u128 int-to-float pair unexpectedly compiled successfully"
    );
    assert!(
        stderr.contains(
            "rustc_codegen_trust_cg: cannot compile required function with unsupported MIR"
        ),
        "rustc did not reach the rustc_codegen_trust_cg unsupported-MIR diagnostic. stderr was: <<<{stderr}>>>"
    );
    assert!(
        stderr.contains("CastKind::IntToFloat U128 -> F64"),
        "unsupported-program guard did not fail on the intended u128 int-to-float pair. stderr was: <<<{stderr}>>>"
    );

    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

#[test]
fn float_remainder_is_now_supported_after_backend_load() {
    // Float remainder (`%` on f32/f64) WAS an unsupported-MIR fail-closed case.
    // The f32/f64 arithmetic lowering on this branch now SUPPORTS it (frem,
    // fmod/fmodf semantics), differentially verified against LLVM at O0/O3 in
    // float_semantics.rs (`5.5f32 % 2.0f32 == 1.5`, `-5.5f64 % 2.0f64`). This
    // test, formerly asserting the fail-closed path, now guards that float
    // remainder keeps compiling cleanly THROUGH the backend (not via a
    // dylib-load failure).
    let src = "fn main() { let _x = 5.0f64 % 2.0f64; }\n";
    let output = run_backend_on_source("float_remainder", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);

    assert!(
        output.status.success(),
        "float remainder should now compile (frem is supported). stderr: <<<{stderr}>>>"
    );

    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
    positive_evidence::record(Evidence::Compiled, Certs::On);
}

/// MISCOMPILE #71, now SUPPORTED: a loop that mutates a SCALARIZED aggregate
/// (struct/array/tuple) FIELD used to have no loop-header phi for that field, so
/// the in-loop store was silently dropped and the post-loop read saw the INITIAL
/// value. The bridge now MEMORY-BACKS a loop-carried mutated aggregate local
/// (`compute_memory_backed_locals`), so the in-loop store round-trips through its
/// stable stack slot and survives the back-edge — `let mut q=Q{a,..}; while .. {
/// q.a += 1 }` now compiles and accumulates correctly. Runtime CORRECTNESS (no
/// store-drop) is verified differentially by
/// `m71_loop_carried_aggregate_field_accumulates_matches_llvm` in
/// `m80_loop_refmut_writeback_x86.rs`; here we only assert it COMPILES.
#[test]
fn loop_carried_aggregate_field_mutation_now_compiles_after_backend_load() {
    let src = r#"
#![no_main]
use core::hint::black_box as bb;
#[derive(Clone, Copy)] struct Q { a: i32, b: i32 }
#[no_mangle] pub extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let mut q = Q { a: bb(7i32), b: bb(0i32) };
    let mut i = 0i32;
    while i < bb(1i32) {
        q.a = q.a.wrapping_add(1);
        i = i.wrapping_add(1);
    }
    q.a & 0xFF
}
"#;
    let output = run_backend_on_source("m71_loop_aggregate_field", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    assert!(
        output.status.success(),
        "loop-carried aggregate-field mutation must now COMPILE (memory-backed), not fail closed. \
         stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
    positive_evidence::record(Evidence::Compiled, Certs::On);
}

/// A whole-value store `*d = t` whose scalarized source `t` has a zero-sized
/// field BEFORE a sized one. The flat construction binds `t` by MIR field index
/// (the ZST included) while the rustc-layout writer walks ZST-skipping leaves;
/// reading leaf `i` under key `i` once put the `()` in `b`'s bytes, so the shape
/// was refused `[TCG-ZST-LANE-INDEX]`. The same writer serves a store into a
/// field of an address-taken aggregate (`h.z = t`). The writer now reads each
/// leaf under the key `scalarized_leaf_binding_keys` states, so both COMPILE at
/// every optimization level; `zst_leaf_key_differential` and the wasm32 corpus
/// crate `r7-bridge-zst-leaf-keys.rs` check the stored values against LLVM.
/// `no-proof-certs` isolates MIR lowering from the host's opcode-proof inventory.
#[test]
fn zst_before_sized_field_whole_store_from_scalarized_source_compiles() {
    if !knob_test_can_run("zst_before_sized_field_whole_store_from_scalarized_source_compiles") {
        return;
    }
    let cases = [
        (
            "zst_lane_index_deref_store",
            r#"#![crate_type = "lib"]
#[derive(Clone, Copy)]
pub struct Z1 { a: u32, z: (), b: u32 }
#[inline(never)]
#[no_mangle]
pub fn store_z1(d: &mut Z1, x: u32) { *d = Z1 { a: x, z: (), b: !x }; }
"#,
        ),
        (
            "zst_lane_index_field_store",
            r#"#![crate_type = "lib"]
use core::marker::PhantomData;
#[derive(Clone, Copy)]
pub struct Z3 { a: u8, b: u64, p: PhantomData<u32>, c: u16 }
#[derive(Clone, Copy)]
pub struct Hold { h: u16, z: Z3, t: u8 }
#[inline(never)]
fn look(h: &Hold) -> u64 { h.h as u64 ^ h.z.b ^ (h.z.c as u64) << 30 ^ h.z.a as u64 }
#[no_mangle]
pub fn field_store(x: u64) -> u64 {
    let mut h = Hold { h: 1, z: Z3 { a: 2, b: 3, p: PhantomData, c: 4 }, t: 5 };
    let r = look(&h);
    let mut t = Z3 { a: x as u8, b: x.rotate_left(11), p: PhantomData, c: (x >> 3) as u16 };
    t.b ^= 5;
    h.z = t;
    r ^ look(&h) ^ h.t as u64
}
"#,
        ),
    ];
    for (stem, src) in cases {
        for opt in ["-Copt-level=0", "-Copt-level=2"] {
            let output = run_backend_on_source_with(stem, src, &[opt], &["no-proof-certs"]);
            let stderr = output.stderr.as_str();
            eprintln!("rustc {stem} {opt} stderr:\n{stderr}");
            assert!(
                output.status.success(),
                "{stem}: a whole store from a scalarized source with an interior ZST must \
                 compile at {opt}. stderr: <<<{stderr}>>>"
            );
            assert!(
                !stderr.contains("[TCG-ZST-LANE-INDEX]"),
                "{stem}: the interior-ZST whole store still reports \
                 [TCG-ZST-LANE-INDEX] at {opt}. stderr: <<<{stderr}>>>"
            );
            assert_no_backend_load_failure(stderr);
        }
    }
    positive_evidence::record(Evidence::Compiled, Certs::Off);
}

/// A CONSTANT pointer to a zero-sized `T` coerced to `*const dyn Tr` / `&dyn Tr`
/// is not always rustc's dangling address: a null pointer stays null and a
/// `&STATIC` of a ZST static has the static's address. Only a promoted pointer
/// into a zero-length allocation takes the `align as *const T` value, so these
/// two constants (which rustc produces at -O1+) must still be refused.
#[test]
fn non_promoted_zst_constant_trait_object_data_pointer_fails_closed() {
    let cases = [
        (
            "zst_null_dyn",
            r#"#![crate_type = "lib"]
pub trait Tr { fn f(&self, x: u32) -> u32; }
pub struct Z;
impl Tr for Z { fn f(&self, x: u32) -> u32 { x ^ 3 } }
#[inline(never)]
fn is_null_dyn(p: *const dyn Tr) -> u32 { p.is_null() as u32 }
#[no_mangle]
pub fn null_dyn(x: u32) -> u32 {
    let p: *const dyn Tr = core::ptr::null::<Z>();
    is_null_dyn(p) | (x & 0)
}
"#,
        ),
        (
            "zst_static_dyn",
            r#"#![crate_type = "lib"]
pub trait Tr { fn f(&self, x: u32) -> u32; }
pub struct Z;
impl Tr for Z { fn f(&self, x: u32) -> u32 { x ^ 3 } }
pub static ZS: Z = Z;
#[inline(never)]
fn data_addr_ref(p: &dyn Tr) -> usize { p as *const dyn Tr as *const () as usize }
#[no_mangle]
pub fn static_dyn(x: u32) -> u32 {
    let r: &dyn Tr = &ZS;
    ((data_addr_ref(r) == (&ZS as *const Z as usize)) as u32) | (r.f(x) << 1)
}
"#,
        ),
    ];
    for (stem, src) in cases {
        let output = run_backend_on_source_with_args(stem, src, &["-Copt-level=2"]);
        let stderr = output.stderr.as_str();
        eprintln!("rustc {stem} stderr:\n{stderr}");
        assert!(
            !output.status.success(),
            "{stem}: a non-promoted ZST constant coerced to a trait object compiled; its \
             data pointer is not the dangling address. stderr: <<<{stderr}>>>"
        );
        assert!(
            stderr.contains("trait-object unsize source is not a place operand"),
            "{stem}: the ZST constant trait object did not fail closed at the unsize \
             source. stderr: <<<{stderr}>>>"
        );
        assert_no_backend_load_failure(stderr);
    }
    positive_evidence::record(Evidence::ExpectedRefusal, Certs::On);
}

/// RETAINED ADDRESS, pointer locals: `keep` stores the address of the POINTER
/// local `p` (and of the `Box` local `b`) in a static, so a later callee may
/// retarget it through the kept address. The escape analysis gives each a
/// scalar cell; every deref, reborrow and drop through it reads the pointer
/// back from that cell for the statement. These shapes compile (their runtime
/// agreement with LLVM is checked by the `rp_*` exports of the wasm32
/// differential corpus and by the native execution differential); none may
/// fail closed, and in particular none may fall back to a `[TCG-RETAINED-ADDR]`
/// refusal or to the SSA-binding refusals of the deref paths. The static array
/// is read through patterns: a native `panic=abort` bounds check is refused
/// (`[TCG-ASSERT-PANIC]`).
#[test]
fn retained_pointer_locals_compile() {
    let src = r#"#![crate_type = "lib"]
static mut KEPT: usize = 0;
static A: [u32; 4] = [11, 22, 33, 44];
#[inline(never)]
fn keep(p: &mut *mut u32) {
    unsafe { KEPT = p as *mut *mut u32 as usize }
}
#[inline(never)]
fn retarget(i: usize) {
    let [a, b, c, d] = &A;
    let e = match i & 3 {
        0 => a,
        1 => b,
        2 => c,
        _ => d,
    };
    unsafe { *(KEPT as *mut *mut u32) = (&raw const *e) as *mut u32 }
}
#[no_mangle]
pub fn kept_pointer(x: u32) -> u32 {
    let [first, ..] = &A;
    let mut p: *mut u32 = (&raw const *first) as *mut u32;
    keep(&mut p);
    retarget(x as usize);
    unsafe { *p }
}
#[no_mangle]
pub fn kept_entry_pointer(mut p: *mut u32, x: u32) -> u32 {
    keep(&mut p);
    retarget(x as usize);
    unsafe { *p }
}
static mut KB: *mut Box<u32> = core::ptr::null_mut();
#[inline(never)]
fn keep_box(b: &mut Box<u32>) {
    unsafe { KB = b }
}
#[inline(never)]
fn replace_kept(v: u32) {
    unsafe { core::mem::forget(core::ptr::replace(KB, Box::new(v))) }
}
#[no_mangle]
pub fn kept_box(x: u32) -> u32 {
    let mut b = Box::new(x);
    keep_box(&mut b);
    replace_kept(x ^ 5);
    *b + 1
}
#[no_mangle]
pub fn opaque_box_callee(f: fn(&mut Box<u32>), x: u32) -> u32 {
    let mut b = Box::new(x);
    f(&mut b);
    *b + 1
}
"#;
    for opt in ["-Copt-level=0", "-Copt-level=2"] {
        let output = run_backend_on_source_with(
            "retained_pointer_locals",
            src,
            &[opt, "-Cpanic=abort", "--emit=obj"],
            &["no-proof-certs"],
        );
        let stderr = output.stderr.as_str();
        eprintln!("rustc stderr ({opt}):\n{stderr}");
        assert_no_backend_load_failure(stderr);
        assert!(
            output.status.success(),
            "pointer and Box locals whose address a callee keeps failed to compile at {opt}. \
             stderr was: <<<{stderr}>>>"
        );
    }
    positive_evidence::record(Evidence::Compiled, Certs::Off);
}
