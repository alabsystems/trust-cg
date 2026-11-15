//! Calls through `extern "rust-call"` fn pointers, `dyn` trait methods, foreign
//! items and reified closure bodies cross the backend boundary in rustc's own
//! convention: every such program must compile with the bridge and print the
//! value LLVM computes, in all four library x binary pairings at O0-O3.
//!
//! rustc's `FnAbi` untuples a `rust-call` argument tuple. While the bridge
//! declared and passed the tuple as ONE by-value parameter, a callee it did not
//! declare took the untupled arguments. Measured 2026-10-02 at `13a7b0ad9`
//! (AArch64 Linux): an LLVM-built library's `extern "rust-call" fn((u64, [f32;
//! 4], u8)) -> u64` called through a pointer from a bridge-built binary
//! returned a different wrong value on each run (all-LLVM:
//! 3478433575752971906), and the `(f64, f64)` pointer, the non-`Fn*` `dyn`
//! trait method and the foreign item below returned wrong values. A `(bool,
//! u64)` tuple's lane carried the tuple's padding above the `bool` rustc
//! zero-extends, so a bridge binary read `false` as `true`. The address of a
//! `FnOnce` closure's own body SIGSEGV'd (rustc passes its 8-byte environment
//! in a register, the bridge declared a pointer), and so did the address of a
//! `Fn` closure body whose `&str` comes after six `u64`, or after a `u128` and
//! three `u64` (rustc splits the pair across `x7` and the stack, the bridge's
//! whole slot went on the stack), read out of an inline `const` block or a
//! static (measured at `65fc9aaf3` and `fd6f7475f`). Those shapes were then
//! refused by name (`[TCG-RUST-CALL-ABI]`, `[TCG-ARG-ABI]`). Since round 10 the
//! bridge declares every `rust-call` callable with its tuple's ELEMENTS as
//! rustc's `FnAbi` lists them, passes every such call untupled
//! (`rust_call_spread`), declares closure bodies' `Pair` arguments and by-value
//! environments by rustc's own modes, and compares every declaration's byte
//! placement with rustc's (`check_signature_placement`). So each driver below
//! (`driver_template.rs`), the `caller.rs` library, the `exported.rs`
//! `(bool, u64)` item and the `admitted.rs` shapes must now match LLVM.
//!
//! A hand-written `Fn` impl taking six `u64` and a `&str`, whose symbol crosses
//! a crate boundary: non-generic and `#[inline(never)]`, so rustc exports it at
//! every level (`exported_spread.rs`), and generic, exported only under
//! `-Zshare-generics` (`exported_spread_generic.rs`). Each driver calls it
//! directly, from its own generic and through a vtable it builds. While the
//! bridge declared the tuple as one parameter, the library compiled with the
//! callee-side comparison disabled and an LLVM binary over it SIGSEGV'd
//! (measured 2026-10-04, AArch64 Linux, L06-P16); that line refused it by name
//! (`refuse_tupled_rust_call_shared_symbol`, deleted). Under one rule
//! (docs/decision-record.md OD-RUST-CALL-ONE-RULE-20261008, LD-26) both must
//! compile and print LLVM's value in all four pairings at O0-O3.
//! Diagnostic native execution under `no-proof-certs`; it does not qualify
//! mandatory machine proof.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// (library backend, binary backend); the first pairing is the LLVM oracle.
const PAIRINGS: [(&str, &str); 4] = [
    ("llvm", "llvm"),
    ("cg", "cg"),
    ("cg", "llvm"),
    ("llvm", "cg"),
];

fn mx(h: u64, v: u64) -> u64 {
    (h ^ v).wrapping_mul(0x100000001b3).rotate_left(5)
}

/// `callees::repro((k, [_, _, _, last], tail))`.
fn repro(k: u64, last: f32, tail: u8) -> u64 {
    mx(mx(k, u64::from(last.to_bits())), u64::from(tail))
}

/// One driver binary: its name, `main`'s call expression, and the value
/// LLVM's program prints (computed here, independently of either backend).
struct Driver {
    name: &'static str,
    call: &'static str,
    value: u64,
}

/// `callees::call_pair` of a closure body over `callees::pair_value` with
/// environment value `s`.
fn pair(k: u64, s: u64) -> u64 {
    mx(mx(k + 2 + 3 + 4 + 5 + 6, 12 * 256 + u64::from(b'h')), s)
}

/// The driver closure whose body's address the `closure_pair_*` drivers take.
const PAIR_CLOSURE: &str = "|a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, t: &'static str| \
                            pair_value(a, b, c, d, e, f, t, s)";

/// The `&str` and environment `callees::call_wide` and `call_fit` pass.
fn wide_text(s: u64) -> u64 {
    mx(12 * 256 + u64::from(b'h'), s)
}

/// `callees::call_wide` of a closure body over `callees::wide_value`.
fn wide(k: u64, s: u64) -> u64 {
    mx(mx(mx(3, k), 4 + 3 * 5 + 5 * 6), wide_text(s))
}

/// `callees::call_fit` of a closure body over `callees::fit_value`.
fn fit(k: u64, s: u64) -> u64 {
    mx(mx(mx(3, k), 4 + 3 * 5), wide_text(s))
}

/// `exported_spread`'s `Spread(s)` called with `(k, 2, 3, 4, 5, 6, "hello")`.
fn spread(k: u64, s: u64) -> u64 {
    mx(
        mx(k + 2 * 2 + 3 * 3 + 4 * 4 + 5 * 5 + 6 * 6, s),
        5 * 256 + u64::from(b'h'),
    )
}

fn drivers() -> [Driver; 12] {
    let k = 41;
    [
        Driver {
            name: "closure_u128_fit_pointer",
            call: "{ let s = bb(2000u64); let c = move |w: u128, a: u64, b: u64, t: &'static str| \
                   fit_value(w, a, b, t, s); call_fit(bb(reify_fit(&c)), &s, k) }",
            value: fit(k, 2000),
        },
        Driver {
            name: "fn_pointer",
            call: "(bb(get_repro()))((k, [1.0, 2.0, 3.0, 5.0], 8))",
            value: repro(k, 5.0, 8),
        },
        Driver {
            name: "float_pair_pointer",
            call: "(bb(get_float_pair()))((k as f64 * 0.5, 1.25))",
            value: mx(20.5f64.to_bits(), 1.25f64.to_bits()),
        },
        Driver {
            name: "dyn_method",
            call: "bb(make_tr(bb(3))).m((k, [1.0, 2.0, 3.0, 5.0], 8))",
            value: mx(repro(k, 5.0, 8), 3),
        },
        Driver {
            name: "foreign_item",
            call: "unsafe { foreign::rcf((k, [1.0, 2.0, 3.0, 5.0], 8)) }",
            value: repro(k, 5.0, 8),
        },
        Driver {
            name: "bool_pointer",
            call: "bb(get_flag())((bb(k) > 100, k)) + bb(get_flag())((bb(k) < 100, k))",
            value: k,
        },
        Driver {
            name: "bool_item",
            call: "flag((bb(k) > 100, k)) + flag((bb(k) < 100, k))",
            value: k,
        },
        Driver {
            name: "closure_body_pointer",
            call: "{ let c = once_closure(bb(2000)); let q = bb(reify_once(&c)); q(c, (k,)) }",
            value: k * 3 + 2000,
        },
        Driver {
            name: "closure_pair_pointer",
            call: "{ let s = bb(2000u64); let c = move PAIR_CLOSURE; \
                   call_pair(bb(reify_pair(&c)), &s, k) }",
            value: pair(k, 2000),
        },
        Driver {
            name: "closure_pair_constant",
            call: "{ let s = bb(2000u64); let c = move PAIR_CLOSURE; \
                   call_pair(bb(const_pair(&c)), &s, k) }",
            value: pair(k, 2000),
        },
        Driver {
            name: "closure_pair_static",
            call: "{ static SP: Erased = { let c = |a: u64, b: u64, c: u64, d: u64, e: u64, \
                   f: u64, t: &'static str| pair_value(a, b, c, d, e, f, t, 7); \
                   Erased(pair_body(&c) as *const ()) }; call_pair(bb(SP.0), &k, k) }",
            value: pair(k, 7),
        },
        Driver {
            name: "closure_u128_pair_pointer",
            call: "{ let s = bb(2000u64); let c = move |w: u128, a: u64, b: u64, c: u64, \
                   t: &'static str| wide_value(w, a, b, c, t, s); \
                   call_wide(bb(reify_wide(&c)), &s, k) }",
            value: wide(k, 2000),
        },
    ]
}

/// `admitted_driver.rs`'s output, computed here.
fn admitted_stdout() -> String {
    let k = 41u64;
    let text = &"hello world, rust-call!"[..(k as usize % 20) + 2];
    format!(
        "one {}\ntwo {}\nnarrow {}\ntext {}\nunit {}\nm {}\nmine {}\n",
        mx(k, 7),
        mx(k, k * 3),
        mx((k as u8 ^ 0x80).into(), k),
        mx(
            text.len() as u64,
            u64::from(text.as_bytes()[text.len() - 1])
        ),
        mx(7, 9),
        mx(mx(k, k + 1), 3),
        mx(k ^ 5, k),
    )
}

fn compile_command(backend: &Path, lane: &str, opt: u32, args: &[String]) -> Command {
    let mut command = rustc_command();
    command
        .args(["--target", TARGET, "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .args(args);
    if lane == "cg" {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg(super::cg_knobs());
    }
    command
}

fn library(
    backend: &Path,
    lane: &str,
    opt: u32,
    dir: &Path,
    source: &Path,
) -> (Output, String, PathBuf) {
    let name = source.file_stem().unwrap().to_str().unwrap();
    let rlib = dir.join(format!("lib{name}.rlib"));
    let mut args = vec![
        "--crate-type=rlib".to_owned(),
        format!("--crate-name={name}"),
        "-o".to_owned(),
        rlib.display().to_string(),
    ];
    args.push(source.display().to_string());
    let (output, transcript) = run_bounded(
        &mut compile_command(backend, lane, opt, &args),
        600,
        &dir.join(format!("{name}.log")),
    );
    (output, transcript, rlib)
}

fn binary(
    backend: &Path,
    lane: &str,
    opt: u32,
    dir: &Path,
    source: &Path,
    externs: &[String],
) -> (Output, String, PathBuf) {
    let program = dir.join("program");
    let mut args = vec![
        "--crate-type=bin".to_owned(),
        "--crate-name=driver".to_owned(),
        "-o".to_owned(),
        program.display().to_string(),
    ];
    args.extend(externs.iter().cloned());
    args.push(source.display().to_string());
    let (output, transcript) = run_bounded(
        &mut compile_command(backend, lane, opt, &args),
        600,
        &dir.join("compile.log"),
    );
    (output, transcript, program)
}

fn run(program: &Path, dir: &Path) -> String {
    let output = checked(&mut Command::new(program), 60, &dir.join("run.log"));
    assert!(
        output.stderr.is_empty(),
        "{} wrote stderr",
        program.display()
    );
    String::from_utf8(output.stdout).unwrap()
}

/// The check; each host's `#[test]` calls it (Linux AArch64 and Darwin AArch64,
/// each for its own native target).
pub(super) fn no_proof_rust_call_pointer_calls_match_llvm() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-rust-call-pointers.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-rust-call-pointers-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    for (name, source) in [
        (
            "callees.rs",
            include_str!("rust_call_pointer_calls/callees.rs"),
        ),
        (
            "caller.rs",
            include_str!("rust_call_pointer_calls/caller.rs"),
        ),
        (
            "caller_driver.rs",
            include_str!("rust_call_pointer_calls/caller_driver.rs"),
        ),
        (
            "admitted.rs",
            include_str!("rust_call_pointer_calls/admitted.rs"),
        ),
        (
            "admitted_driver.rs",
            include_str!("rust_call_pointer_calls/admitted_driver.rs"),
        ),
        (
            "exported.rs",
            include_str!("rust_call_pointer_calls/exported.rs"),
        ),
        (
            "exported_driver.rs",
            include_str!("rust_call_pointer_calls/exported_driver.rs"),
        ),
        (
            "exported_spread.rs",
            include_str!("rust_call_pointer_calls/exported_spread.rs"),
        ),
        (
            "exported_spread_driver.rs",
            include_str!("rust_call_pointer_calls/exported_spread_driver.rs"),
        ),
        (
            "exported_spread_generic.rs",
            include_str!("rust_call_pointer_calls/exported_spread_generic.rs"),
        ),
        (
            "exported_spread_generic_driver.rs",
            include_str!("rust_call_pointer_calls/exported_spread_generic_driver.rs"),
        ),
    ] {
        std::fs::write(root.join(name), source).unwrap();
    }
    let template = include_str!("rust_call_pointer_calls/driver_template.rs");
    assert!(template.contains("let v = CALL;"));
    let drivers = drivers();
    for driver in &drivers {
        let call = driver.call.replace("PAIR_CLOSURE", PAIR_CLOSURE);
        std::fs::write(
            root.join(format!("{}.rs", driver.name)),
            template.replace("let v = CALL;", &format!("let v = {call};")),
        )
        .unwrap();
    }
    let admitted = admitted_stdout();
    let mut runs = 0;
    for opt in 0..=3 {
        let level = root.join(format!("O{opt}"));
        // The callee and caller libraries, built by each backend.
        let mut callees = std::collections::BTreeMap::new();
        let mut callers = std::collections::BTreeMap::new();
        for lane in ["llvm", "cg"] {
            let dir = level.join(format!("callees-{lane}"));
            std::fs::create_dir_all(&dir).unwrap();
            let (output, transcript, rlib) =
                library(&backend, lane, opt, &dir, &root.join("callees.rs"));
            assert!(
                output.status.success(),
                "O{opt}: {lane} callees: {transcript}"
            );
            callees.insert(lane, format!("--extern=callees={}", rlib.display()));
            let dir = level.join(format!("caller-{lane}"));
            std::fs::create_dir_all(&dir).unwrap();
            let (output, transcript, rlib) =
                library(&backend, lane, opt, &dir, &root.join("caller.rs"));
            assert!(
                output.status.success(),
                "O{opt}: {lane} caller: {transcript}"
            );
            callers.insert(lane, format!("--extern=caller={}", rlib.display()));
        }
        for driver in &drivers {
            for (library, binary_lane) in PAIRINGS {
                let dir = level.join(format!("{}-{library}-{binary_lane}", driver.name));
                std::fs::create_dir_all(&dir).unwrap();
                let source = root.join(format!("{}.rs", driver.name));
                let (output, transcript, program) = binary(
                    &backend,
                    binary_lane,
                    opt,
                    &dir,
                    &source,
                    &[callees[library].clone()],
                );
                let what = format!(
                    "O{opt} {}: {library} library with {binary_lane} binary",
                    driver.name
                );
                assert!(output.status.success(), "{what}: {transcript}");
                assert_eq!(
                    run(&program, &dir),
                    format!("v {}\n", driver.value),
                    "{what}"
                );
                runs += 1;
            }
        }
        // A LIBRARY calling the `rust-call` pointers it is handed, in every
        // pairing (its pointers are the same library side's `callees` items).
        for (library, binary_lane) in PAIRINGS {
            let dir = level.join(format!("caller-driver-{library}-{binary_lane}"));
            std::fs::create_dir_all(&dir).unwrap();
            let (output, transcript, program) = binary(
                &backend,
                binary_lane,
                opt,
                &dir,
                &root.join("caller_driver.rs"),
                &[callees[library].clone(), callers[library].clone()],
            );
            let what = format!("O{opt} caller: {library} libraries with {binary_lane} binary");
            assert!(output.status.success(), "{what}: {transcript}");
            assert_eq!(
                run(&program, &dir),
                format!("v {} 41\n", repro(41, 4.0, 9)),
                "{what}"
            );
            runs += 1;
        }
        // A `(bool, u64)` item a library DEFINES: rustc's caller extends the
        // `bool`, and the bridge's body reads it at its own width.
        for lane in ["llvm", "cg"] {
            let dir = level.join(format!("exported-{lane}"));
            std::fs::create_dir_all(&dir).unwrap();
            let (output, transcript, rlib) =
                library(&backend, lane, opt, &dir, &root.join("exported.rs"));
            let what = format!("O{opt} exported ({lane} library, LLVM binary)");
            assert!(output.status.success(), "{what}: {transcript}");
            let dir = level.join(format!("exported-{lane}-llvm"));
            std::fs::create_dir_all(&dir).unwrap();
            let (output, transcript, program) = binary(
                &backend,
                "llvm",
                opt,
                &dir,
                &root.join("exported_driver.rs"),
                &[format!("--extern=exported={}", rlib.display())],
            );
            assert!(output.status.success(), "{what}: {transcript}");
            assert_eq!(run(&program, &dir), "v 130 130\n", "{what}");
            runs += 1;
        }
        // A `rust-call` item whose symbol crosses a crate boundary, with a
        // tuple that does not place like one parameter: in every pairing, the
        // binary reaching the library's definition by symbol.
        let value = spread(41, 7);
        for (name, expected) in [
            ("exported_spread", format!("v {value} {value} {value}\n")),
            (
                "exported_spread_generic",
                format!("v {value} {value} {value} {value}\n"),
            ),
        ] {
            let mut libraries = std::collections::BTreeMap::new();
            for lane in ["llvm", "cg"] {
                let dir = level.join(format!("{name}-{lane}"));
                std::fs::create_dir_all(&dir).unwrap();
                let (output, transcript, rlib) =
                    library(&backend, lane, opt, &dir, &root.join(format!("{name}.rs")));
                assert!(
                    output.status.success(),
                    "O{opt} {name} ({lane} library): {transcript}"
                );
                libraries.insert(lane, rlib);
            }
            for (library, binary_lane) in PAIRINGS {
                let dir = level.join(format!("{name}-{library}-{binary_lane}"));
                std::fs::create_dir_all(&dir).unwrap();
                let (output, transcript, program) = binary(
                    &backend,
                    binary_lane,
                    opt,
                    &dir,
                    &root.join(format!("{name}_driver.rs")),
                    &[format!("--extern={name}={}", libraries[library].display())],
                );
                let what = format!("O{opt} {name}: {library} library with {binary_lane} binary");
                assert!(output.status.success(), "{what}: {transcript}");
                assert_eq!(run(&program, &dir), expected, "{what}");
                runs += 1;
            }
        }
        // The shapes whose tuple already placed like its elements, in every
        // pairing.
        let mut libraries = std::collections::BTreeMap::new();
        for lane in ["llvm", "cg"] {
            let dir = level.join(format!("admitted-{lane}"));
            std::fs::create_dir_all(&dir).unwrap();
            let (output, transcript, rlib) =
                library(&backend, lane, opt, &dir, &root.join("admitted.rs"));
            assert!(
                output.status.success(),
                "O{opt} admitted ({lane} library): {transcript}"
            );
            libraries.insert(lane, rlib);
        }
        for (library, binary_lane) in PAIRINGS {
            let dir = level.join(format!("admitted-{library}-{binary_lane}"));
            std::fs::create_dir_all(&dir).unwrap();
            let (output, transcript, program) = binary(
                &backend,
                binary_lane,
                opt,
                &dir,
                &root.join("admitted_driver.rs"),
                &[format!(
                    "--extern=admitted={}",
                    libraries[library].display()
                )],
            );
            let what = format!("O{opt} admitted: {library} library with {binary_lane} binary");
            assert!(output.status.success(), "{what}: {transcript}");
            assert_eq!(run(&program, &dir), admitted, "{what}");
            runs += 1;
        }
    }
    assert_eq!(sha256(&backend), digest);
    assert_eq!(
        runs,
        4 * (drivers.len() * PAIRINGS.len()
            + PAIRINGS.len()
            + 2
            + 2 * PAIRINGS.len()
            + PAIRINGS.len())
    );
    eprintln!(
        "rust-call boundary calls: {runs} native runs over 4 pairings at O0-O3, none refused"
    );
}
