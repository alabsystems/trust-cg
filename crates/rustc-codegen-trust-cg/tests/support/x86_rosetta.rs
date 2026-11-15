//! x86-64 execution for the bridge's cross-backend tests, on an x86-64 host or
//! under Rosetta on Apple silicon.
//!
//! The installed Trust package ships `rust-std` for its host only, so on an
//! aarch64-apple-darwin host every x86-64 cross-backend test used to SKIP ("no
//! x86_64 std") and nothing on this host could ever see an x86-64 argument
//! placement across the backend boundary. Rosetta executes x86-64 binaries
//! there, and a `#![no_std]` program needs only `core` and
//! `compiler_builtins`, which this module builds ONCE per test process and opt
//! level from the compiler's own library source — the `library/` tree at the
//! commit `trustc -vV` reports — with the LLVM backend (`trustc` without a
//! codegen backend).
//!
//! The source is `$TRUST_RUST_SRC` (a directory holding `library/`) or
//! `git -C ${TRUST_SRC_REPO:-$HOME/trust} archive <commit> library/...`. On an
//! Apple-silicon host with Rosetta, a missing source is a FAILURE that names
//! both variables, never a skip: the route exists and the test must run. Only a
//! host with no x86-64 execution route at all reports `Unavailable`.
//!
//! [`x86_link_core`] builds the same `core` on any host for a test that only
//! compiles and LINKS x86-64 programs (no execution route needed).
//!
//! Test rung, `targo --unverified`: nothing here makes a proof claim, and a run
//! under Rosetta qualifies Rosetta's execution of the x86-64 code, not a
//! native x86-64 machine.
#![allow(dead_code)]

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::{Mutex, OnceLock};

pub const X86_TARGET: &str = "x86_64-apple-darwin";

/// How this host executes an `x86_64-apple-darwin` binary.
#[derive(Clone, Debug)]
pub enum X86Exec {
    /// An x86-64 macOS host with the target's `rust-std` in the sysroot.
    Native,
    /// Apple silicon with Rosetta: `core` + `compiler_builtins` for the opt
    /// level live in `core_dir`, and binaries run under `arch -x86_64`.
    Rosetta { core_dir: PathBuf },
    /// No x86-64 execution route on this host.
    Unavailable(String),
}

impl X86Exec {
    /// Compile flags every x86-64 `#![no_std]` crate of a test adds (the target
    /// included), so the program links against this route's `core`.
    pub fn compile_args(&self) -> Vec<OsString> {
        match self {
            X86Exec::Rosetta { core_dir } => no_std_compile_args(core_dir),
            X86Exec::Native | X86Exec::Unavailable(_) => vec![
                "--target".into(),
                X86_TARGET.into(),
                "-Clink-arg=-lSystem".into(),
            ],
        }
    }

    /// Run a linked x86-64 binary; `None` when this host cannot.
    pub fn run(&self, bin: &Path) -> Option<Output> {
        match self {
            X86Exec::Native => Some(Command::new(bin).output().expect("run x86-64 binary")),
            X86Exec::Rosetta { .. } => Some(
                Command::new("arch")
                    .arg("-x86_64")
                    .arg(bin)
                    .output()
                    .expect("run x86-64 binary under Rosetta"),
            ),
            X86Exec::Unavailable(_) => None,
        }
    }
}

/// The compile flags of an x86-64 `#![no_std]` crate linked against the
/// `core` + `compiler_builtins` in `core_dir` (from [`x86_link_core`]), the
/// target included.
pub fn no_std_compile_args(core_dir: &Path) -> Vec<OsString> {
    let mut core = OsString::from("core=");
    core.push(core_dir.join("libcore.rlib"));
    let mut builtins = OsString::from("compiler_builtins=");
    builtins.push(core_dir.join("libcompiler_builtins.rlib"));
    vec![
        "--target".into(),
        X86_TARGET.into(),
        "--extern".into(),
        core,
        "--extern".into(),
        builtins,
        "-L".into(),
        core_dir.as_os_str().to_owned(),
        "-Clink-arg=-lSystem".into(),
    ]
}

fn rosetta_available() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
        && Command::new("arch")
            .args(["-x86_64", "/usr/bin/true"])
            .output()
            .is_ok_and(|out| out.status.success())
}

/// The commit `trustc -vV` reports for the build compiler.
fn compiler_commit() -> String {
    let out = super::toolchain_support::rustc_driver_command()
        .arg("-vV")
        .output()
        .expect("run the build compiler -vV");
    assert!(out.status.success(), "build compiler -vV failed");
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .map(|hash| hash.trim().to_owned())
        .filter(|hash| hash.len() == 40 && hash.chars().all(|c| c.is_ascii_hexdigit()))
        .unwrap_or_else(|| panic!("build compiler reports no commit-hash:\n{text}"))
}

fn work_root() -> PathBuf {
    PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("x86_rosetta_core")
}

/// The compiler's own `library/` tree, extracted once per commit.
fn library_source(commit: &str) -> PathBuf {
    if let Some(dir) = std::env::var_os("TRUST_RUST_SRC") {
        let dir = PathBuf::from(dir);
        assert!(
            dir.join("library/core/src/lib.rs").is_file(),
            "TRUST_RUST_SRC={dir:?} has no library/core/src/lib.rs"
        );
        return dir;
    }
    let dest = work_root().join(format!("src-{commit}"));
    if dest.join("library/core/src/lib.rs").is_file()
        && dest
            .join("library/compiler-builtins/compiler-builtins/src/lib.rs")
            .is_file()
    {
        return dest;
    }
    let repo = std::env::var_os("TRUST_SRC_REPO")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join("trust")))
        .expect("HOME or TRUST_SRC_REPO");
    let staging = work_root().join(format!("src-{commit}.tmp-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&staging);
    std::fs::create_dir_all(&staging).expect("create library staging dir");
    let archive = Command::new("git")
        .arg("-C")
        .arg(&repo)
        .args(["archive", "--format=tar", commit])
        .args([
            "library/core",
            "library/compiler-builtins",
            "library/stdarch",
            "library/portable-simd",
        ])
        .output()
        .unwrap_or_else(|e| panic!("run git archive in {repo:?}: {e}"));
    assert!(
        archive.status.success(),
        "an x86-64 `core` built from source (Rosetta execution, or a link-only x86-64 test) \
         needs the compiler's library source at commit {commit}: set TRUST_RUST_SRC to a \
         directory holding its `library/`, or TRUST_SRC_REPO to a git checkout that has the \
         commit (default $HOME/trust). `git archive` in {repo:?} said: {}",
        String::from_utf8_lossy(&archive.stderr)
    );
    let mut tar = Command::new("tar")
        .arg("-x")
        .arg("-C")
        .arg(&staging)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .expect("spawn tar");
    {
        use std::io::Write;
        tar.stdin
            .take()
            .expect("tar stdin")
            .write_all(&archive.stdout)
            .expect("feed tar");
    }
    assert!(tar.wait().expect("wait tar").success(), "tar -x failed");
    if std::fs::rename(&staging, &dest).is_err() {
        // Another test process published it first; theirs is the same tree.
        let _ = std::fs::remove_dir_all(&staging);
    }
    assert!(dest.join("library/core/src/lib.rs").is_file());
    dest
}

fn build_core(src: &Path, commit: &str, opt: &str) -> PathBuf {
    let dest = work_root().join(format!("{commit}-O{opt}"));
    if dest.join("libcore.rlib").is_file() && dest.join("libcompiler_builtins.rlib").is_file() {
        return dest;
    }
    let staging = work_root().join(format!("{commit}-O{opt}.tmp-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&staging);
    std::fs::create_dir_all(&staging).expect("create core staging dir");
    let run = |mut cmd: Command, what: &str| {
        let out = cmd
            .env("RUSTC_BOOTSTRAP", "1")
            .output()
            .unwrap_or_else(|e| panic!("spawn {what}: {e}"));
        assert!(
            out.status.success(),
            "building x86-64 {what} (LLVM, O{opt}) failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        );
    };
    let mut core = super::toolchain_support::rustc_driver_command();
    core.args([
        "--edition",
        "2024",
        "--crate-type",
        "lib",
        "--crate-name",
        "core",
        "-Zforce-unstable-if-unmarked",
        "-Ztrust-verify=off",
        "-Cpanic=abort",
        "--target",
        X86_TARGET,
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("--out-dir")
    .arg(&staging)
    .arg(src.join("library/core/src/lib.rs"));
    run(core, "core");
    let mut builtins = super::toolchain_support::rustc_driver_command();
    let mut core_extern = OsString::from("core=");
    core_extern.push(staging.join("libcore.rlib"));
    builtins
        .args([
            "--edition",
            "2024",
            "--crate-type",
            "lib",
            "--crate-name",
            "compiler_builtins",
            "-Zforce-unstable-if-unmarked",
            "-Ztrust-verify=off",
            "-Cpanic=abort",
            "--target",
            X86_TARGET,
            "--cfg",
            "feature=\"compiler-builtins\"",
            "--cfg",
            "feature=\"mem\"",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("--extern")
        .arg(core_extern)
        .arg("-L")
        .arg(&staging)
        .arg("--out-dir")
        .arg(&staging)
        .arg(src.join("library/compiler-builtins/compiler-builtins/src/lib.rs"));
    run(builtins, "compiler_builtins");
    if std::fs::rename(&staging, &dest).is_err() {
        let _ = std::fs::remove_dir_all(&staging);
    }
    assert!(
        dest.join("libcore.rlib").is_file(),
        "no libcore.rlib at {dest:?}"
    );
    dest
}

/// The x86-64 execution route for programs compiled at `-Copt-level={opt}`.
pub fn x86_execution(opt: &str) -> X86Exec {
    if cfg!(all(target_os = "macos", target_arch = "x86_64"))
        && super::toolchain_support::target_std_available(X86_TARGET)
    {
        return X86Exec::Native;
    }
    if !rosetta_available() {
        return X86Exec::Unavailable(
            "neither an x86-64 macOS host with its rust-std nor Rosetta on Apple silicon".into(),
        );
    }
    X86Exec::Rosetta {
        core_dir: x86_link_core(opt),
    }
}

/// An x86-64 `core` + `compiler_builtins` for `#![no_std]` programs compiled
/// at `-Copt-level={opt}`, built once per test process and opt level from the
/// compiler's own library source with the LLVM backend, on ANY host: it
/// needs no execution route, so a test that only compiles and LINKS x86-64
/// programs (macOS `cc` links `x86_64-apple-darwin` on Apple silicon without
/// Rosetta) can use it. Compile against it with [`no_std_compile_args`].
pub fn x86_link_core(opt: &str) -> PathBuf {
    static BUILT: OnceLock<Mutex<std::collections::HashMap<String, PathBuf>>> = OnceLock::new();
    let built = BUILT.get_or_init(Default::default);
    let mut built = built.lock().unwrap_or_else(|poison| poison.into_inner());
    if let Some(dir) = built.get(opt) {
        return dir.clone();
    }
    let commit = compiler_commit();
    let src = library_source(&commit);
    let dir = build_core(&src, &commit, opt);
    built.insert(opt.to_owned(), dir.clone());
    dir
}

/// A `#![no_std]` program's prelude: a panic handler, `black_box`, an
/// `exit(v)` that ends the process with `v % 251` through libSystem's `exit`,
/// and an (never called) `rust_eh_personality`, which generic code from a
/// sysroot `core` built with unwinding references even at `-Cpanic=abort`.
/// A caller body written as `fn main() { exit(...) }` is renamed
/// `rust_main` and called from a C `main`.
pub const NO_STD_CALLER_PRELUDE: &str = "#![no_std]\n#![no_main]\n\
    use core::hint::black_box;\n\
    #[panic_handler] fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n\
    #[unsafe(no_mangle)] pub extern \"C\" fn rust_eh_personality() {}\n\
    unsafe extern \"C\" { #[link_name = \"exit\"] fn libc_exit(code: i32) -> !; }\n\
    fn exit(v: u64) -> ! { unsafe { libc_exit((v % 251) as i32) } }\n";

/// Turn a `fn main() { ... }` caller body (written against
/// [`NO_STD_CALLER_PRELUDE`]'s `exit` and `black_box`) into a whole
/// `#![no_std]` program.
pub fn no_std_caller(body: &str) -> String {
    assert!(
        body.contains("fn main()"),
        "a caller body must define `fn main()`: {body}"
    );
    format!(
        "{NO_STD_CALLER_PRELUDE}{}\n#[unsafe(no_mangle)] pub extern \"C\" fn main(_c: i32, _v: *const *const u8) -> i32 {{ rust_main(); 0 }}\n",
        body.replacen("fn main()", "fn rust_main()", 1)
    )
}

/// The build compiler's version as rustc embeds it in an rlib's metadata:
/// `trustc -V` up to its first closing parenthesis
/// (`rustc 1.99.0-dev (321aaeda7 2026-09-17)`).
pub fn embedded_compiler_version() -> String {
    let out = super::toolchain_support::rustc_driver_command()
        .arg("-V")
        .output()
        .expect("run the build compiler -V");
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let end = text
        .find(')')
        .expect("a version with a commit in parentheses");
    text[..=end].to_owned()
}

/// Whether `rlib` was written by the build compiler (its metadata embeds
/// [`embedded_compiler_version`]).
pub fn rlib_is_from_build_compiler(rlib: &Path) -> bool {
    let want = embedded_compiler_version();
    std::fs::read(rlib).is_ok_and(|bytes| {
        bytes
            .windows(want.len())
            .any(|window| window == want.as_bytes())
    })
}

/// The x86-64 lane of an rlib x bin cross-backend fixture (`m140`, `m141`,
/// `m144`, `m145`, `m146`) on THIS host.
///
/// Those fixtures were written as `std` programs for an x86-64 host, and on
/// Apple silicon they used to return early ("no x86-64 std"). The lane keeps
/// the native route exactly as it was, and adds Rosetta: the same callee and
/// caller sources rewritten as `#![no_std]` programs ([`no_std_callee`],
/// [`no_std_program`]) against this module's `core`, run under `arch -x86_64`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum XbackLane {
    /// An x86-64 Linux or macOS host with its x86-64 `rust-std`: the programs
    /// as written, for `target`, run directly.
    Native { target: &'static str },
    /// Apple silicon with Rosetta: `#![no_std]` programs for
    /// [`X86_TARGET`], each opt level linked against its own `core`.
    Rosetta,
}

impl XbackLane {
    /// This host's x86-64 lane. `native_target` is the host's x86-64 triple
    /// (`host_target_support::X86_64_TARGET`). `Err(reason)` only where the
    /// fixture returned early before this lane existed — a non-x86-64 host
    /// without Rosetta, or an x86-64 host without the target's `rust-std`. On
    /// an Apple-silicon macOS host the lane is Rosetta, and a missing route or
    /// library source is a FAILURE, never a skip.
    pub fn for_host(native_target: &'static str) -> Result<Self, String> {
        if cfg!(target_arch = "x86_64") && cfg!(any(target_os = "macos", target_os = "linux")) {
            return if super::toolchain_support::target_std_available(native_target) {
                Ok(XbackLane::Native {
                    target: native_target,
                })
            } else {
                Err(format!(
                    "rust-std for {native_target} not installed for the pinned toolchain"
                ))
            };
        }
        if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            return match x86_execution("0") {
                X86Exec::Rosetta { .. } => Ok(XbackLane::Rosetta),
                other => panic!(
                    "an Apple-silicon macOS host runs the x86-64 lane under Rosetta, got {other:?}"
                ),
            };
        }
        Err(
            "the x86-64 lane runs natively on an x86-64 Linux or macOS host, or under \
             Rosetta on Apple silicon"
                .into(),
        )
    }

    /// The target triple every compile of the lane names.
    pub fn target(&self) -> &'static str {
        match self {
            XbackLane::Native { target } => target,
            XbackLane::Rosetta => X86_TARGET,
        }
    }

    /// A short name for failure reports.
    pub fn label(&self) -> &'static str {
        match self {
            XbackLane::Native { .. } => "x86-64 (native)",
            XbackLane::Rosetta => "x86-64 (Rosetta)",
        }
    }

    /// The target and link arguments of every compile at `-Copt-level={opt}`.
    pub fn compile_args(&self, opt: &str) -> Vec<OsString> {
        match self {
            XbackLane::Native { target } => vec!["--target".into(), (*target).into()],
            XbackLane::Rosetta => x86_execution(opt).compile_args(),
        }
    }

    /// The callee crate's source for this lane.
    pub fn callee_source(&self, src: &str) -> String {
        match self {
            XbackLane::Native { .. } => src.to_owned(),
            XbackLane::Rosetta => no_std_callee(src),
        }
    }

    /// A caller program's source for this lane, from the `std` program the
    /// fixture writes.
    pub fn caller_source(&self, std_program: &str) -> String {
        match self {
            XbackLane::Native { .. } => std_program.to_owned(),
            XbackLane::Rosetta => no_std_program(std_program),
        }
    }

    /// Run a linked binary built at `-Copt-level={opt}`; its exit code, or a
    /// description of how it ended without one.
    pub fn run(&self, bin: &Path, opt: &str) -> Result<i32, String> {
        let out = match self {
            XbackLane::Native { .. } => Command::new(bin)
                .output()
                .map_err(|e| format!("run {bin:?}: {e}"))?,
            XbackLane::Rosetta => x86_execution(opt)
                .run(bin)
                .ok_or_else(|| "no x86-64 execution route".to_owned())?,
        };
        out.status
            .code()
            .ok_or_else(|| format!("{bin:?} exited via signal: {:?}", out.status))
    }
}

/// The two lines every x86-64 xback fixture's `std` caller header opens with.
/// [`NO_STD_CALLER_PRELUDE`] defines both names, with the same meaning.
const STD_CALLER_LINES: [&str; 2] = [
    "use std::hint::black_box;",
    "fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }",
];

/// Rewrite a callee crate written against `std` as a `#![no_std]` crate: the
/// `std::` paths it uses (`hint`, `ops`, `ptr`, `mem`, `fmt`) are `core`'s.
pub fn no_std_callee(src: &str) -> String {
    let src = src.replace("std::", "core::");
    if src.contains("#![no_std]") {
        src
    } else {
        format!("#![no_std]\n{src}")
    }
}

/// Rewrite a whole `std` caller program — the fixture's header (its first
/// line `use std::hint::black_box;`, an `exit(v)` through
/// `std::process::exit`, any helpers) and a `fn main()` body — as a
/// `#![no_std]` program ([`no_std_caller`]). Every `std::` path left is
/// `core`'s; a header that does not carry both standard lines, or any
/// `std::process` use beyond them, is a test-authoring error and panics.
pub fn no_std_program(std_program: &str) -> String {
    let mut seen = [false; 2];
    let mut kept = String::new();
    for line in std_program.lines() {
        match STD_CALLER_LINES.iter().position(|std| line.trim() == *std) {
            Some(i) => seen[i] = true,
            None => {
                kept.push_str(line);
                kept.push('\n');
            }
        }
    }
    assert!(
        seen.iter().all(|s| *s),
        "a std caller program must carry both {STD_CALLER_LINES:?}:\n{std_program}"
    );
    assert!(
        !kept.contains("std::process"),
        "a std caller program uses `std::process` beyond its `exit`:\n{std_program}"
    );
    no_std_caller(&kept.replace("std::", "core::"))
}
