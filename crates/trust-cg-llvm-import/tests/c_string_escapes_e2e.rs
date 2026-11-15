#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / c_string_escapes_e2e.rs
//
// L02-P14: `c"..."` initializers decode exactly as LLVM's `UnEscapeLexed`
// decodes them (`\\` is one backslash and is recognized before a hex escape,
// `\XX` is one byte, any other backslash is itself), and a decoded length
// that differs from the declared `[N x i8]` is refused by name, as LLVM's
// parser refuses it.
//
// * Host-neutral: every corpus row imports to its expected bytes, the corpus
//   compiles for both explicit AArch64 targets, and each length mismatch is
//   refused by name.
// * Native (macOS AArch64): the corpus is compiled by trust-cg and, as the
//   LLVM reference, by clang reading the same `.ll` (LLVM's own IR parser);
//   a clang-compiled C driver prints every array's bytes from each object,
//   linked by ld64. Both runs, and the expected bytes, must agree; clang must
//   also reject every module the importer refuses.
//
// * Native (Linux AArch64 GNU): the same full corpus is compared with llc
//   at O0-O3 through GNU ld, gold and LLD, for non-PIE and PIE links.
//   Both malformed-length modules must get LLVM's actual type-mismatch
//   diagnostic, and repaired-length controls must compile.
//
// Testing evidence about the importer's string decoding, not a proof.

mod common;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "../../trust-cg-codegen/tests/common/rosetta.rs"]
mod native_process;

use std::fmt::Write as _;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_llvm_import::{Error, import_text};

use common::{TARGETS, compile_for};

/// `(c-string body as spelled in LLVM text, the bytes LLVM decodes it to)`.
fn corpus() -> Vec<(String, Vec<u8>)> {
    let mut rows: Vec<(String, Vec<u8>)> = [
        // The ledger's case: four bytes before, three (a, \, NUL) in LLVM.
        (r"a\\\00", &b"a\\\0"[..]),
        (r"\\", b"\\"),
        (r"\\\\", b"\\\\"),
        (r"\5C\5c", b"\\\\"),
        (r"\\41", b"\\41"),
        (r"\\\41", b"\\A"),
        (r"\\\\\41", b"\\\\A"),
        (r"\4a\4A\00\7f\80\ff", b"JJ\0\x7f\x80\xff"),
        (r"\x41", b"\\x41"),
        (r"\0g", b"\\0g"),
        (r"\g0", b"\\g0"),
        (r"a\4", b"a\\4"),
        (r"a\", b"a\\"),
        (r"\", b"\\"),
        (r"\22;[,]{}\00", b"\";[,]{}\0"),
        ("\u{e9}\\C3\\A9", b"\xc3\xa9\xc3\xa9"),
    ]
    .into_iter()
    .map(|(body, bytes)| (body.to_owned(), bytes.to_vec()))
    .collect();
    // Every byte value as a hex escape, in both digit cases.
    let mut all = String::new();
    let mut bytes = Vec::new();
    for value in 0..=255u8 {
        if value % 2 == 0 {
            write!(all, "\\{value:02x}").unwrap();
        } else {
            write!(all, "\\{value:02X}").unwrap();
        }
        bytes.push(value);
    }
    rows.push((all, bytes));
    rows
}

/// The corpus as an LLVM module: `@esc_<i> = constant [N x i8] c"<body>"`,
/// and `@esc_rows()` returning the row count (a module needs a function).
fn corpus_module() -> String {
    let rows = corpus();
    let mut ll = String::new();
    for (index, (body, bytes)) in rows.iter().enumerate() {
        writeln!(
            ll,
            "@esc_{index} = constant [{} x i8] c\"{body}\", align 1",
            bytes.len()
        )
        .unwrap();
    }
    writeln!(
        ll,
        "define i32 @esc_rows() {{\n  ret i32 {}\n}}",
        rows.len()
    )
    .unwrap();
    ll
}

fn global_bytes(module: &trust_ir::Module, name: &str) -> Vec<u8> {
    let global = module
        .globals
        .iter()
        .find(|global| global.name == name)
        .unwrap_or_else(|| panic!("{name} imported"));
    let initializer = global.initializer.as_ref().expect("an initialized global");
    // The importer types a data image (`[u8; N]` or a packed byte/pointer
    // struct); read back the bytes it stands for.
    trust_cg_lower::global_image::flat_image_elements(module, &global.ty, initializer)
        .unwrap_or_else(|| panic!("{name}: not a data image: {:?} {initializer:?}", global.ty))
        .iter()
        .map(|element| match element {
            trust_ir::Constant::Int(value) => u8::try_from(*value).expect("a byte"),
            other => panic!("{name}: non-byte element {other:?}"),
        })
        .collect()
}

/// Modules whose decoded string length is not the declared one, with the
/// named refusal each must get.
fn length_mismatches() -> Vec<(String, String)> {
    vec![
        // The ledger's module: LLVM reads three bytes, the type declares four.
        (
            "@s = constant [4 x i8] c\"a\\\\\\00\", align 1\n".to_owned(),
            "global `@s`: c-string initializer c\"a\\\\\\00\" decodes to 3 byte(s), but its \
             type is [4 x i8]"
                .to_owned(),
        ),
        // The same string inside an aggregate initializer.
        (
            "@w = constant [1 x { i32, [4 x i8] }] [{ i32, [4 x i8] } { i32 7, [4 x i8] \
             c\"a\\\\\\00\" }], align 4\n"
                .to_owned(),
            "aggregate initializer: c-string initializer c\"a\\\\\\00\" decodes to 3 byte(s), \
             but its type is [4 x i8]"
                .to_owned(),
        ),
    ]
}

#[test]
fn every_corpus_row_imports_to_the_bytes_llvm_decodes() {
    let rows = corpus();
    let module = import_text(&corpus_module(), "c_string_escapes").expect("the corpus imports");
    for (index, (body, bytes)) in rows.iter().enumerate() {
        assert_eq!(
            global_bytes(&module, &format!("esc_{index}")),
            *bytes,
            "c\"{body}\""
        );
    }
    for triple in TARGETS {
        for level in [OptLevel::O0, OptLevel::O2] {
            let object = compile_for(&corpus_module(), "c_string_escapes", triple, level);
            assert!(!object.is_empty(), "{triple} {level:?}");
        }
    }
    // Well-formed near misses of the mismatches below import.
    for (src, bytes) in [
        ("@s = constant [1 x i8] c\"\\\\\", align 1\n", &b"\\"[..]),
        ("@s = constant [3 x i8] c\"\\\\41\", align 1\n", b"\\41"),
    ] {
        let module = import_text(src, "control").expect(src);
        assert_eq!(global_bytes(&module, "s"), bytes, "{src}");
    }
}

#[test]
fn a_decoded_length_the_type_does_not_declare_is_refused_by_name() {
    let rows = length_mismatches();
    assert_eq!(rows.len(), 2);
    for (src, want) in rows {
        match import_text(&src, "length_mismatch") {
            Err(Error::Unsupported(reason)) => assert!(
                reason.starts_with(&want)
                    && reason.ends_with(
                        "(a c-string whose decoded length differs from its declared array type)"
                    ),
                "{src}\n{reason}"
            ),
            other => panic!("{src}: expected the named length refusal, got {other:?}"),
        }
    }
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use std::fmt::Write as _;
    use std::fs;
    use std::path::Path;
    use std::process::Command;

    use trust_cg_codegen::pipeline::OptLevel;

    #[cfg(target_os = "macos")]
    use super::common::native_c_command;
    use super::common::{compile_for_host, describe_status, unique_temp_dir};
    use super::{corpus, corpus_module, length_mismatches};

    #[cfg(target_os = "macos")]
    fn run(command: &mut Command, what: &str) -> Vec<u8> {
        let output = command
            .output()
            .unwrap_or_else(|error| panic!("{what}: {error}"));
        assert!(
            output.status.success(),
            "{what} failed with {}\nstdout:\n{}\nstderr:\n{}",
            describe_status(output.status),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    }

    /// A C driver that prints every corpus array's bytes in hex, one line
    /// per row, from whichever object defines them.
    fn driver() -> String {
        let mut c = String::from("#include <stdio.h>\nint esc_rows(void);\n");
        let rows = corpus();
        for (index, (_, bytes)) in rows.iter().enumerate() {
            writeln!(
                c,
                "extern const unsigned char esc_{index}[{}];",
                bytes.len()
            )
            .unwrap();
        }
        c.push_str(
            "static void dump(int row, const unsigned char *p, unsigned n) {\n\
             \x20   printf(\"%d:\", row);\n\
             \x20   for (unsigned i = 0; i < n; i++) printf(\" %02x\", p[i]);\n\
             \x20   printf(\"\\n\");\n}\nint main(void) {\n",
        );
        for (index, (_, bytes)) in rows.iter().enumerate() {
            writeln!(c, "    dump({index}, esc_{index}, {});", bytes.len()).unwrap();
        }
        c.push_str("    printf(\"rows %d\\n\", esc_rows());\n    return 0;\n}\n");
        c
    }

    fn expected() -> String {
        let mut out = String::new();
        for (index, (_, bytes)) in corpus().iter().enumerate() {
            write!(out, "{index}:").unwrap();
            for byte in bytes {
                write!(out, " {byte:02x}").unwrap();
            }
            out.push('\n');
        }
        writeln!(out, "rows {}", corpus().len()).unwrap();
        out
    }

    #[cfg(target_os = "macos")]
    fn link_and_run(dir: &Path, object: &str, program: &str) -> String {
        run(
            native_c_command()
                .current_dir(dir)
                .args(["driver.o", object, "-o", program]),
            &format!("cc -o {program}"),
        );
        String::from_utf8(run(&mut Command::new(dir.join(program)), program)).unwrap()
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn trust_cg_and_clang_emit_the_same_bytes_for_every_escape() {
        let dir = unique_temp_dir("c-string-escapes");
        fs::write(dir.join("driver.c"), driver()).unwrap();
        run(
            native_c_command()
                .current_dir(&*dir)
                .args(["-O2", "-c", "driver.c", "-o", "driver.o"]),
            "clang -c driver.c",
        );
        fs::write(dir.join("corpus.ll"), corpus_module()).unwrap();
        // The LLVM reference: clang reads the same IR with LLVM's parser.
        run(
            native_c_command().current_dir(&*dir).args([
                "-c",
                "-x",
                "ir",
                "corpus.ll",
                "-o",
                "llvm.o",
            ]),
            "clang -c corpus.ll",
        );
        let reference = link_and_run(&dir, "llvm.o", "llvm");
        assert_eq!(
            reference,
            expected(),
            "LLVM decodes the corpus differently from the table"
        );
        for level in [OptLevel::O0, OptLevel::O2] {
            let object = format!("trust-cg-{level:?}.o");
            fs::write(
                dir.join(&object),
                compile_for_host(&corpus_module(), "c_string_escapes", level),
            )
            .unwrap();
            assert_eq!(
                link_and_run(&dir, &object, &format!("trust-cg-{level:?}")),
                reference,
                "trust-cg {level:?}"
            );
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn clang_rejects_every_module_the_importer_refuses_for_length() {
        let dir = unique_temp_dir("c-string-length");
        for (index, (src, _)) in length_mismatches().into_iter().enumerate() {
            let name = format!("mismatch{index}.ll");
            fs::write(dir.join(&name), &src).unwrap();
            let output = native_c_command()
                .current_dir(&*dir)
                .args(["-c", "-x", "ir", &name, "-o", "/dev/null"])
                .output()
                .expect("run clang");
            assert!(
                !output.status.success(),
                "clang accepted a module the importer refuses:\n{src}"
            );
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn darwin_c_oracle_compiles_and_links_with_shadowed_path() {
        use std::os::unix::fs::PermissionsExt;

        let dir = unique_temp_dir("darwin-c-oracle-shadow");
        for name in ["clang", "cc"] {
            let path = dir.join(name);
            fs::write(
                &path,
                "#!/bin/sh\necho unexpected-PATH-compiler >&2\nexit 86\n",
            )
            .unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        fs::write(
            dir.join("driver.c"),
            "#include <stdio.h>\nint main(void) { return puts(\"darwin-c-oracle\") < 0; }\n",
        )
        .unwrap();
        let path = format!("{}:/usr/bin:/bin", dir.display());
        run(
            native_c_command()
                .env("PATH", &path)
                .current_dir(&*dir)
                .args(["-c", "driver.c", "-o", "driver.o"]),
            "compile C with a shadowed PATH",
        );
        run(
            native_c_command()
                .env("PATH", path)
                .current_dir(&*dir)
                .args(["driver.o", "-o", "driver"]),
            "link C with a shadowed PATH",
        );
        assert_eq!(
            run(&mut Command::new(dir.join("driver")), "run C oracle"),
            b"darwin-c-oracle\n"
        );
    }

    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    mod linux {
        use std::path::PathBuf;
        use std::process::Output;
        use std::sync::atomic::{AtomicUsize, Ordering};

        use trust_cg_codegen::jit_diagnostics::sha256_hex;

        use super::{
            Command, OptLevel, Path, compile_for_host, corpus, corpus_module, describe_status,
            driver, expected, fs, length_mismatches, unique_temp_dir,
        };
        use crate::{common, native_process};

        const RETAIN: &str = "TCG_RETAIN_TEST_EVIDENCE";
        const TARGET: &str = common::LINUX;

        /// Retention is opt-in. Ordinary successful tests still clean their
        /// scratch; the shared guard controls retention on a failing test.
        fn finish(directory: common::ScratchDir) {
            if std::env::var_os(RETAIN).is_some() {
                eprintln!(
                    "retained Linux c-string evidence: {}",
                    directory.path().display()
                );
                std::mem::forget(directory);
            }
        }

        fn capture(directory: &Path, command: &mut Command, native: bool) -> Output {
            let retain = std::env::var_os(RETAIN).is_some();
            let program = PathBuf::from(command.get_program());
            let before = native.then(|| {
                assert!(program.is_absolute() && program.starts_with(directory));
                assert!(!program.is_symlink());
                let bytes = fs::read(&program).expect("read native image before execution");
                let digest = sha256_hex(&bytes);
                if retain {
                    use std::io::Write as _;
                    let snapshot = directory.join(format!("native-image-{digest}.elf"));
                    match fs::OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .open(&snapshot)
                    {
                        Ok(mut file) => file.write_all(&bytes).expect("retain pre-execution image"),
                        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                            assert!(!snapshot.is_symlink());
                            assert_eq!(fs::read(snapshot).unwrap(), bytes);
                        }
                        Err(error) => panic!("retain pre-execution image: {error}"),
                    }
                }
                digest
            });
            let timeout = if native {
                native_process::codegen_run_timeout()
            } else {
                native_process::codegen_link_timeout()
            };
            let result = native_process::command_output_with_timeout(command, timeout)
                .expect("launch c-string control command");
            let after = native.then(|| sha256_hex(&fs::read(&program).unwrap()));
            if retain {
                static NEXT: AtomicUsize = AtomicUsize::new(0);
                let path = directory.join(format!(
                    "native-command-{:06}.json",
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                let record = serde_json::json!({
                    "program": command.get_program().to_string_lossy(),
                    "args": command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>(),
                    "current_dir": command.get_current_dir(),
                    "success": result.output.status.success(),
                    "exit_code": result.output.status.code(),
                    "timed_out": result.timed_out,
                    "stdout": String::from_utf8_lossy(&result.output.stdout),
                    "stderr": String::from_utf8_lossy(&result.output.stderr),
                    "native_image_sha256_before": &before,
                    "native_image_sha256_after": &after,
                    "retained_native_image": before.as_ref().map(|digest| format!("native-image-{digest}.elf")),
                });
                let file = fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .open(path)
                    .unwrap();
                serde_json::to_writer_pretty(file, &record).unwrap();
            }
            assert!(!result.timed_out, "command timed out: {command:?}");
            assert_eq!(before, after, "executed native fixture changed");
            result.output
        }

        fn successful(directory: &Path, command: &mut Command, native: bool) -> Vec<u8> {
            let output = capture(directory, command, native);
            assert!(
                output.status.success(),
                "{command:?} failed with {}\nstdout:\n{}\nstderr:\n{}",
                describe_status(output.status),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            output.stdout
        }

        /// Resolve llc from an explicit selection or the compiler's own
        /// sysroot, and require the compiler's LLVM major. The compiler
        /// queries scrub the test controls that a Trust compiler refuses.
        fn llc(directory: &Path) -> PathBuf {
            let compiler = std::env::var_os("RUSTC").unwrap_or_else(|| "trustc".into());
            let query = |args: &[&str]| {
                let mut command = Command::new(&compiler);
                command.args(args);
                for (name, _) in std::env::vars_os() {
                    if name.to_string_lossy().starts_with("TCG_")
                        || name.to_string_lossy().starts_with("TRUST_CG_")
                    {
                        command.env_remove(name);
                    }
                }
                String::from_utf8(successful(directory, &mut command, false)).unwrap()
            };
            let compiler_version = query(&["-vV"]);
            let major = compiler_version
                .lines()
                .find_map(|line| line.strip_prefix("LLVM version: ")?.split('.').next())
                .expect("compiler discloses its LLVM major");
            let selected = std::env::var_os("TCG_LLC")
                .map(PathBuf::from)
                .unwrap_or_else(|| {
                    PathBuf::from(query(&["--print", "sysroot"]).trim())
                        .join("lib/rustlib/aarch64-unknown-linux-gnu/bin/llc")
                });
            assert!(
                selected.is_absolute() && selected.is_file(),
                "required llc: {selected:?}"
            );
            let version = String::from_utf8(successful(
                directory,
                Command::new(&selected).arg("--version"),
                false,
            ))
            .unwrap();
            assert!(
                version.lines().any(|line| {
                    line.trim()
                        .strip_prefix("LLVM version ")
                        .and_then(|value| value.split('.').next())
                        == Some(major)
                }),
                "llc must match compiler LLVM {major}: {version}"
            );
            eprintln!("Linux c-string oracle: {selected:?}\n{version}");
            selected
        }

        fn llvm_object(directory: &Path, llc: &Path, input: &str, output: &str, level: u8) {
            successful(
                directory,
                Command::new(llc).current_dir(directory).args([
                    &format!("-mtriple={TARGET}"),
                    "-filetype=obj",
                    "-relocation-model=pic",
                    &format!("-O={level}"),
                    input,
                    "-o",
                    output,
                ]),
                false,
            );
        }

        fn link_and_run(
            directory: &Path,
            object: &str,
            name: &str,
            linker: &str,
            pie: bool,
        ) -> String {
            successful(
                directory,
                Command::new("cc")
                    .current_dir(directory)
                    .arg(format!("-fuse-ld={linker}"))
                    .args([
                        if pie { "-pie" } else { "-no-pie" },
                        "driver.o",
                        object,
                        "-o",
                        name,
                    ]),
                false,
            );
            String::from_utf8(successful(
                directory,
                &mut Command::new(directory.join(name)),
                true,
            ))
            .unwrap()
        }

        #[test]
        fn trust_cg_and_llc_emit_every_escape_through_all_linux_linkers() {
            assert_eq!(
                corpus().len(),
                17,
                "retain the original full corpus denominator"
            );
            let directory = unique_temp_dir("linux-c-string-escapes");
            fs::write(directory.join("driver.c"), driver()).unwrap();
            fs::write(directory.join("corpus.ll"), corpus_module()).unwrap();
            fs::write(directory.join("expected.stdout"), expected()).unwrap();
            let requirements = serde_json::json!({
                "TCG_REQUIRE_GOLD": std::env::var_os("TCG_REQUIRE_GOLD").is_some(),
                "TCG_REQUIRE_LLD": std::env::var_os("TCG_REQUIRE_LLD").is_some(),
                "TCG_REQUIRE_LLC": std::env::var_os("TCG_REQUIRE_LLC").is_some(),
            });
            let case = serde_json::json!({
                "schema": "trust-cg.test.linux-c-string.v1",
                "target": TARGET, "corpus_rows": corpus().len(),
                "all_byte_values": 256, "optimizations": [0, 1, 2, 3],
                "linkers": ["bfd", "gold", "lld"], "pie_modes": [false, true],
                "required_native_executions": 48, "floor_requirements": requirements,
            });
            fs::write(
                directory.join("case.json"),
                serde_json::to_vec_pretty(&case).unwrap(),
            )
            .unwrap();
            successful(
                &directory,
                Command::new("cc")
                    .current_dir(&*directory)
                    .args(["-O2", "-fPIC", "-c", "driver.c", "-o", "driver.o"]),
                false,
            );
            let llc = llc(&directory);
            let want = expected();
            for (level, opt) in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3]
                .into_iter()
                .enumerate()
            {
                let llvm = format!("llvm-O{level}.o");
                llvm_object(
                    &directory,
                    &llc,
                    "corpus.ll",
                    &llvm,
                    u8::try_from(level).unwrap(),
                );
                let tcg = format!("trust-cg-O{level}.o");
                fs::write(
                    directory.join(&tcg),
                    compile_for_host(&corpus_module(), "c_string_escapes", opt),
                )
                .unwrap();
                for linker in ["bfd", "gold", "lld"] {
                    for pie in [false, true] {
                        let model = if pie { "pie" } else { "nopie" };
                        let reference = link_and_run(
                            &directory,
                            &llvm,
                            &format!("llvm-O{level}-{linker}-{model}"),
                            linker,
                            pie,
                        );
                        assert_eq!(reference, want, "llc O{level}/{linker}/{model}");
                        let actual = link_and_run(
                            &directory,
                            &tcg,
                            &format!("trust-cg-O{level}-{linker}-{model}"),
                            linker,
                            pie,
                        );
                        assert_eq!(actual, reference, "trust-cg O{level}/{linker}/{model}");
                    }
                }
            }
            eprintln!(
                "LINUX_C_STRING rows=17 all_bytes=256 optimizations=4 linkers=3 pie_modes=2 native_executions=48 matched=48"
            );
            finish(directory);
        }

        #[test]
        fn llc_rejects_both_original_length_mismatches_and_accepts_corrected_controls() {
            let directory = unique_temp_dir("linux-c-string-length");
            let llc = llc(&directory);
            let malformed = length_mismatches();
            assert_eq!(malformed.len(), 2, "retain both original malformed modules");
            for (index, (source, _)) in malformed.into_iter().enumerate() {
                let name = format!("mismatch{index}.ll");
                fs::write(directory.join(&name), &source).unwrap();
                let output = capture(
                    &directory,
                    Command::new(&llc).current_dir(&*directory).args([
                        &format!("-mtriple={TARGET}"),
                        "-filetype=obj",
                        &name,
                        "-o",
                        &format!("mismatch{index}.o"),
                    ]),
                    false,
                );
                let diagnostic = String::from_utf8(output.stderr).unwrap();
                assert_eq!(output.status.code(), Some(1), "{diagnostic}");
                assert!(
                    diagnostic.contains("constant expression type mismatch"),
                    "{diagnostic}"
                );
                assert!(diagnostic.contains("'[3 x i8]'"), "{diagnostic}");
                assert!(diagnostic.contains("'[4 x i8]'"), "{diagnostic}");
                let control = format!("corrected{index}.ll");
                fs::write(
                    directory.join(&control),
                    source.replace("[4 x i8]", "[3 x i8]"),
                )
                .unwrap();
                llvm_object(
                    &directory,
                    &llc,
                    &control,
                    &format!("corrected{index}.o"),
                    0,
                );
                assert!(
                    !fs::read(directory.join(format!("corrected{index}.o")))
                        .unwrap()
                        .is_empty()
                );
            }
            eprintln!(
                "LINUX_C_STRING_LENGTH malformed=2 type_mismatch_refusals=2 corrected_controls=2"
            );
            finish(directory);
        }
    }
}
