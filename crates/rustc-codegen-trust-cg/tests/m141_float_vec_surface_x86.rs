#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: the O0 float-Vec surface whose scalar gates are shared by
// the byte-movement, dedup, equality, and slice-contains lowerings. Every guest
// is compiled for x86_64 with both rustc's LLVM backend and trust-cg, then run
// and compared. Raw `to_bits` checks pin byte preservation; `NaN` and signed-zero
// checks pin Rust's IEEE `PartialEq` semantics.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

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
    for candidate in candidates {
        if candidate.exists() {
            return candidate;
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m141");
    let built = target_dir
        .join("release")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(
        built.exists(),
        "expected dylib at {built:?} but none produced"
    );
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

fn workdir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m141_float_vec_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn compile(dir: &Path, stem: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write guest source");
    let bin = dir.join(stem);
    let mut cmd = Command::new("rustup");
    cmd.args([
        "run",
        pinned_toolchain().as_str(),
        "rustc",
        "--edition=2021",
    ])
    .args(["--crate-type", "bin", "--target", TARGET, "-Cpanic=abort"])
    .arg("-Copt-level=0");
    if let Some(dylib) = backend {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
    }
    let output = cmd
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    assert!(
        output.status.success(),
        "compile of `{stem}` failed ({} backend):\n{}",
        if backend.is_some() {
            "trust-cg"
        } else {
            "LLVM"
        },
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

fn run(bin: &Path) -> Output {
    Command::new(bin).output().expect("run compiled guest")
}

fn defined_symbols(bin: &Path) -> String {
    let output = Command::new("nm").arg(bin).output().expect("run nm");
    assert!(
        output.status.success(),
        "`nm {}` failed: {}",
        bin.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

const FLOAT_MOVERS: &str = r#"
#[inline(never)]
fn check(ok: bool, code: i32) {
    if !ok {
        std::process::exit(code);
    }
}

#[inline(never)]
fn bits32(values: &[f32], expected: &[u32]) -> bool {
    if values.len() != expected.len() {
        return false;
    }
    let mut i = 0usize;
    while i < values.len() {
        if values[i].to_bits() != expected[i] {
            return false;
        }
        i += 1;
    }
    true
}

#[inline(never)]
fn bits64(values: &[f64], expected: &[u64]) -> bool {
    if values.len() != expected.len() {
        return false;
    }
    let mut i = 0usize;
    while i < values.len() {
        if values[i].to_bits() != expected[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn main() {
    let n32a = f32::from_bits(0x7fc0_1234);
    let n32b = f32::from_bits(0x7fc0_5678);
    let n64a = f64::from_bits(0x7ff8_0000_0000_1234);
    let n64b = f64::from_bits(0x7ff8_0000_0000_5678);

    // The shared fresh-copy lowering also serves to_owned, clone, and Vec::from.
    let mut source32 = [1.5f32, -0.0, n32a];
    let copied32 = source32.to_vec();
    source32[0] = 9.0;
    check(bits32(&copied32, &[0x3fc0_0000, 0x8000_0000, 0x7fc0_1234]), 1);
    let owned32: Vec<f32> = source32[..].to_owned();
    check(bits32(&owned32, &[0x4110_0000, 0x8000_0000, 0x7fc0_1234]), 2);
    let cloned32 = copied32.clone();
    check(bits32(&cloned32, &[0x3fc0_0000, 0x8000_0000, 0x7fc0_1234]), 3);
    let from32 = Vec::from(&source32[..]);
    check(bits32(&from32, &[0x4110_0000, 0x8000_0000, 0x7fc0_1234]), 4);

    let source64 = [1.25f64, -0.0, n64a].to_vec();
    let mut extended64 = [n64b].to_vec();
    extended64.extend(&source64);
    check(
        bits64(
            &extended64,
            &[
                0x7ff8_0000_0000_5678,
                0x3ff4_0000_0000_0000,
                0x8000_0000_0000_0000,
                0x7ff8_0000_0000_1234,
            ],
        ),
        5,
    );

    let moved_source = [n32a, -2.25f32].to_vec();
    let mut moved_extend = [0.0f32].to_vec();
    moved_extend.extend(moved_source);
    check(bits32(&moved_extend, &[0, 0x7fc0_1234, 0xc010_0000]), 6);

    let mut bulk32 = [-0.0f32].to_vec();
    bulk32.extend_from_slice(&[n32a, n32b]);
    check(
        bits32(&bulk32, &[0x8000_0000, 0x7fc0_1234, 0x7fc0_5678]),
        7,
    );

    let mut append64 = [-3.5f64].to_vec();
    let mut other64 = [n64a, 9.0f64].to_vec();
    append64.append(&mut other64);
    check(
        other64.is_empty()
            && bits64(
                &append64,
                &[
                    0xc00c_0000_0000_0000,
                    0x7ff8_0000_0000_1234,
                    0x4022_0000_0000_0000,
                ],
            ),
        8,
    );

    let mut split32 = [1.5f32, -0.0, n32a, n32b].to_vec();
    let tail32 = split32.split_off(2);
    check(
        bits32(&split32, &[0x3fc0_0000, 0x8000_0000])
            && bits32(&tail32, &[0x7fc0_1234, 0x7fc0_5678]),
        9,
    );

    let clone_source64 = [n64b, -0.0f64].to_vec();
    let mut clone_dest64 = [1.0f64, 2.0, 3.0].to_vec();
    clone_dest64.clone_from(&clone_source64);
    check(
        bits64(
            &clone_dest64,
            &[0x7ff8_0000_0000_5678, 0x8000_0000_0000_0000],
        ),
        10,
    );

    let repeated32 = [n32a, -0.0f32].repeat(3);
    check(
        bits32(
            &repeated32,
            &[
                0x7fc0_1234,
                0x8000_0000,
                0x7fc0_1234,
                0x8000_0000,
                0x7fc0_1234,
                0x8000_0000,
            ],
        ),
        11,
    );

    // PartialEq, not bit equality: signed zero dedups; every NaN remains.
    let mut dedup32 = [0.0f32, -0.0, n32a, n32a, n32b, 5.0, 5.0].to_vec();
    dedup32.dedup();
    check(
        bits32(
            &dedup32,
            &[0, 0x7fc0_1234, 0x7fc0_1234, 0x7fc0_5678, 0x40a0_0000],
        ),
        12,
    );
    let mut dedup64 = [-0.0f64, 0.0, n64a, n64a, 9.0, 9.0].to_vec();
    dedup64.dedup();
    check(
        bits64(
            &dedup64,
            &[
                0x8000_0000_0000_0000,
                0x7ff8_0000_0000_1234,
                0x7ff8_0000_0000_1234,
                0x4022_0000_0000_0000,
            ],
        ),
        13,
    );
}
"#;

const FLOAT_VEC_EQ: &str = r#"
#[inline(never)]
fn check(ok: bool, code: i32) {
    if !ok {
        std::process::exit(code);
    }
}

fn main() {
    let n32 = f32::from_bits(0x7fc0_1234);
    let n64 = f64::from_bits(0x7ff8_0000_0000_1234);

    let a32 = [1.0f32, 0.0, 3.0].to_vec();
    let b32 = [1.0f32, -0.0, 3.0].to_vec();
    check(a32 == b32, 21);
    let nan32a = [n32].to_vec();
    let nan32b = [n32].to_vec();
    check(nan32a != nan32b, 22);

    let a64 = [1.0f64, 0.0, 3.0].to_vec();
    let b64 = [1.0f64, -0.0, 3.0].to_vec();
    check(a64 == b64, 23);
    let nan64a = [n64].to_vec();
    let nan64b = [n64].to_vec();
    check(nan64a != nan64b, 24);
    check(a64 != [1.0f64, -0.0].to_vec(), 25);

    // Integer parity for the shared helper registration path.
    check([1i32, 2].to_vec() == [1i32, 2].to_vec(), 26);
}
"#;

const FLOAT_SLICE_EQ: &str = r#"
use std::hint::black_box;

#[inline(never)]
fn check(ok: bool, code: i32) {
    if !ok {
        std::process::exit(code);
    }
}

fn main() {
    let n32 = black_box(f32::from_bits(0x7fc0_1234));
    let n64 = black_box(f64::from_bits(0x7ff8_0000_0000_1234));

    let a32 = [black_box(1.0f32), black_box(0.0), black_box(3.0)];
    let b32 = [black_box(1.0f32), black_box(-0.0), black_box(3.0)];
    let sa32: &[f32] = black_box(&a32);
    let sb32: &[f32] = black_box(&b32);
    check(sa32 == sb32, 26);
    let na32 = [n32];
    let nb32 = [n32];
    let sna32: &[f32] = black_box(&na32);
    let snb32: &[f32] = black_box(&nb32);
    check(sna32 != snb32, 27);

    let a64 = [black_box(1.0f64), black_box(0.0), black_box(3.0)];
    let b64 = [black_box(1.0f64), black_box(-0.0), black_box(3.0)];
    let sa64: &[f64] = black_box(&a64);
    let sb64: &[f64] = black_box(&b64);
    check(sa64 == sb64, 28);
    let na64 = [n64];
    let nb64 = [n64];
    let sna64: &[f64] = black_box(&na64);
    let snb64: &[f64] = black_box(&nb64);
    check(sna64 != snb64, 29);
}
"#;

const FLOAT_CONTAINS: &str = r#"
#[inline(never)]
fn check(ok: bool, code: i32) {
    if !ok {
        std::process::exit(code);
    }
}

fn main() {
    let a32 = [1.5f32, -0.0, f32::from_bits(0x7fc0_1234)];
    check(a32.contains(&1.5), 41);
    check(a32.contains(&0.0), 42);
    check(a32.contains(&-0.0), 43);
    check(!a32.contains(&2.5), 44);
    check(!a32.contains(&f32::NAN), 45);

    let a64 = [1.25f64, -0.0, f64::from_bits(0x7ff8_0000_0000_1234)];
    check(a64.contains(&1.25), 46);
    check(a64.contains(&0.0), 47);
    check(a64.contains(&-0.0), 48);
    check(!a64.contains(&2.5), 49);
    check(!a64.contains(&f64::NAN), 50);

    // Integer parity for the shared contains helper registration path.
    check([10i32, 20, 30].contains(&20), 51);
}
"#;

#[test]
fn float_vec_surface_matches_llvm_at_o0() {
    if !cfg!(target_os = "macos") {
        eprintln!("skipping: the integration target is {TARGET}");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }

    let dylib = ensure_dylib_built();
    let dir = workdir();
    for (name, source, expected_helpers) in [
        (
            "movers",
            FLOAT_MOVERS,
            &["__trustcg_vec_dedup_f32", "__trustcg_vec_dedup_f64"][..],
        ),
        (
            "vec_equality",
            FLOAT_VEC_EQ,
            &["__trustcg_slice_eq_f32", "__trustcg_slice_eq_f64"][..],
        ),
        (
            "slice_equality",
            FLOAT_SLICE_EQ,
            // Direct slice equality lowers through core's slice body rather than
            // the Vec-specific helper interception. Keep it in a separate guest
            // so this runtime check cannot be satisfied by the Vec cases above.
            &[][..],
        ),
        (
            "contains",
            FLOAT_CONTAINS,
            &[
                "__trustcg_slice_contains_f32",
                "__trustcg_slice_contains_f64",
            ][..],
        ),
    ] {
        let llvm = run(&compile(&dir, &format!("{name}_llvm"), source, None));
        assert!(
            llvm.status.success(),
            "`{name}` LLVM oracle failed: status={:?}, stderr={}",
            llvm.status,
            String::from_utf8_lossy(&llvm.stderr)
        );
        let trust_bin = compile(&dir, &format!("{name}_trust"), source, Some(&dylib));
        let symbols = defined_symbols(&trust_bin);
        for expected in expected_helpers {
            assert!(
                symbols.contains(expected),
                "`{name}` did not emit expected helper `{expected}`"
            );
        }
        let trust = run(&trust_bin);
        assert_eq!(
            trust.status,
            llvm.status,
            "`{name}` status differs from LLVM; trust stderr={}",
            String::from_utf8_lossy(&trust.stderr)
        );
        assert_eq!(
            trust.stdout, llvm.stdout,
            "`{name}` stdout differs from LLVM"
        );
        assert_eq!(
            trust.stderr, llvm.stderr,
            "`{name}` stderr differs from LLVM"
        );
    }
    let _ = std::fs::remove_dir_all(dir);
}
