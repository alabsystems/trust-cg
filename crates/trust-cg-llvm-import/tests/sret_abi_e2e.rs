#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / sret_abi_e2e.rs
//
// L01-P11: an imported function that returns an aggregate through a hidden
// buffer (LLVM `sret`) must take and pass that buffer's address in X8, as
// AAPCS64 requires, not as an ordinary first argument in X0.
//
// * Host-neutral: the `sret` parameter reaches trust-ir on definitions and
//   declarations, and the module compiles for both explicit AArch64 targets
//   (Mach-O and ELF); a callee whose `sret` the importer does not carry
//   (an indirect call through the buffer) is refused by name.
// * Native (macOS AArch64): clang's own IR of a C program at -O0..-O3 is
//   imported, compiled by trust-cg at O0 and O2, linked by ld64 (through
//   `cc`) against a clang-compiled C driver that both CALLS the imported
//   sret functions and is CALLED by them (C callees returning 24- and 32-byte
//   aggregates), and run. Its stdout must equal the same program built
//   entirely by clang at the same level. Before L01-P11 the imported caller
//   passed the buffer in X0 and the program crashed.
//
// All of it is testing evidence about the importer and the backend's call
// lowering, not a proof.

mod common;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_llvm_import::{Error, import_text};

use common::{TARGETS, compile_for};

// The C fixtures below feed only the clang-backed `native` module, which runs
// on AArch64 macOS (clang is the IR source); they share its cfg so other
// hosts do not compile them as dead code.
/// The C program whose clang IR is imported: two sret definitions, and
/// callers of sret functions defined here and in the C driver.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const SRET_C: &str = r#"
struct big { long a, b, c; };
struct mix { double d; long l; char tag[9]; };
struct big c_make_big(long x);
struct mix c_make_mix(long x, double y);

__attribute__((noinline)) struct big make_big(long x) {
    struct big r = { x, x * 2, x * 3 };
    return r;
}
__attribute__((noinline)) struct mix make_mix(long x, double y) {
    struct mix r = { y * 0.5, x - 11, { 'm', 'i', 'x', 0, 1, 2, 3, 4, (char)x } };
    return r;
}
long use_big(long x) {
    struct big r = c_make_big(x + 1);
    return r.a + r.b * 10 + r.c * 100;
}
long use_own(long x) {
    struct big r = make_big(x);
    return r.a ^ r.b ^ r.c;
}
double use_mix(long x, double y) {
    struct mix r = c_make_mix(x, y);
    return r.d + (double)r.l + (double)r.tag[8] + (double)r.tag[0];
}
"#;

/// The clang-compiled driver: the C callees the imported code calls, and a
/// `main` that calls the imported definitions directly and through the
/// imported callers. The inputs keep every product in range (no signed
/// overflow, so no undefined behaviour either compiler may exploit).
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const DRIVER_C: &str = r#"
#include <stdio.h>
struct big { long a, b, c; };
struct mix { double d; long l; char tag[9]; };
struct big make_big(long x);
struct mix make_mix(long x, double y);
long use_big(long x);
long use_own(long x);
double use_mix(long x, double y);

struct big c_make_big(long x) {
    struct big r = { x + 7, x - 7, x * 5 };
    return r;
}
struct mix c_make_mix(long x, double y) {
    struct mix r = { y + 1.25, x * 3, { 'c', 1, 2, 3, 4, 5, 6, 7, (char)(x + 1) } };
    return r;
}

int main(void) {
    static const long xs[] = { 0, 1, -1, 42, 123456789, -987654321, 1L << 40, -(1L << 40) };
    static const double ys[] = { 0.0, -2.5, 1e300, 3.75 };
    for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
        long x = xs[i];
        double y = ys[i % 4];
        struct big b = make_big(x);
        struct mix m = make_mix(x, y);
        printf("%ld %ld %ld | %ld %ld | %.17g %ld", b.a, b.b, b.c, use_big(x), use_own(x), m.d, m.l);
        for (int k = 0; k < 9; k++) printf(" %d", m.tag[k]);
        printf(" | %.17g\n", use_mix(x, y));
    }
    printf("sret-abi rows=%u\n", (unsigned)(sizeof xs / sizeof xs[0]));
    return 0;
}
"#;

/// A caller that returns an aggregate through a function pointer: the
/// indirect call's `sret` argument has no trust-ir spelling.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const INDIRECT_C: &str = r#"
struct big { long a, b, c; };
long via_pointer(struct big (*f)(long), long x) {
    struct big r = f(x);
    return r.a + r.c;
}
"#;

/// Hand-written clang-shaped IR: an sret definition, an sret declaration
/// and both kinds of call, for the host-neutral rows.
const SRET_LL: &str = r#"
%struct.big = type { i64, i64, i64 }

declare void @c_make_big(ptr dead_on_unwind writable sret(%struct.big) align 8, i64 noundef)

define void @make_big(ptr dead_on_unwind noalias writable sret(%struct.big) align 8 %0, i64 noundef %1) {
  store i64 %1, ptr %0, align 8
  %3 = getelementptr inbounds i8, ptr %0, i64 8
  %4 = shl i64 %1, 1
  store i64 %4, ptr %3, align 8
  %5 = getelementptr inbounds i8, ptr %0, i64 16
  %6 = mul i64 %1, 3
  store i64 %6, ptr %5, align 8
  ret void
}

define i64 @use_big(i64 noundef %0) {
  %2 = alloca %struct.big, align 8
  call void @c_make_big(ptr dead_on_unwind writable sret(%struct.big) align 8 %2, i64 noundef %0)
  %3 = load i64, ptr %2, align 8
  call void @make_big(ptr dead_on_unwind writable sret(%struct.big) align 8 %2, i64 noundef %3)
  %4 = getelementptr inbounds i8, ptr %2, i64 16
  %5 = load i64, ptr %4, align 8
  ret i64 %5
}
"#;

#[test]
fn sret_reaches_trust_ir_and_compiles_for_both_aarch64_targets() {
    let module = import_text(SRET_LL, "sret_abi").expect("the sret module imports");
    for name in ["c_make_big", "make_big"] {
        let function = module
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap_or_else(|| panic!("{name} imported"));
        assert!(
            function
                .attrs
                .params
                .first()
                .is_some_and(|attrs| attrs.sret),
            "{name}: {:?}",
            function.attrs.params
        );
    }
    for triple in TARGETS {
        for level in [OptLevel::O0, OptLevel::O2] {
            // `compile_for` asserts the container and panics on a refusal.
            let object = compile_for(SRET_LL, "sret_abi", triple, level);
            assert!(!object.is_empty(), "{triple} {level:?}");
        }
    }
}

#[test]
fn indirect_call_with_a_hidden_return_buffer_is_refused_by_name() {
    let ll = "%struct.big = type { i64, i64, i64 }\n\
              define i64 @via_pointer(ptr %0, i64 %1) {\n\
              \x20 %3 = alloca %struct.big, align 8\n\
              \x20 call void %0(ptr dead_on_unwind writable sret(%struct.big) align 8 %3, i64 noundef %1)\n\
              \x20 %4 = load i64, ptr %3, align 8\n\
              \x20 ret i64 %4\n\
              }\n";
    assert_indirect_sret_refusal(ll, "hand-written");
}

fn assert_indirect_sret_refusal(ll: &str, what: &str) {
    match import_text(ll, "indirect_sret") {
        Err(Error::Unsupported(reason)) => assert!(
            reason.starts_with(
                "indirect call, argument 0: a hidden return-buffer (`sret`) argument (trust-ir \
                 states the buffer only on a declared callee"
            ),
            "{what}: {reason}"
        ),
        Err(other) => panic!("{what}: expected the named indirect-sret refusal, got {other}"),
        Ok(_) => panic!("{what}: an indirect call through an sret buffer must be refused"),
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod native {
    use std::fs;
    use std::path::Path;
    use std::process::Command;

    use trust_cg_codegen::pipeline::OptLevel;
    use trust_cg_llvm_import::import_text;

    use super::common::{compile_for_host, describe_status, native_c_command, unique_temp_dir};
    use super::{DRIVER_C, INDIRECT_C, SRET_C, assert_indirect_sret_refusal};

    const CLANG_LEVELS: [&str; 4] = ["-O0", "-O1", "-O2", "-O3"];

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

    fn clang(dir: &Path, args: &[&str], what: &str) {
        run(native_c_command().current_dir(dir).args(args), what);
    }

    fn clang_ir(dir: &Path, source: &str, name: &str, level: &str) -> String {
        let c = dir.join(format!("{name}.c"));
        fs::write(&c, source).unwrap();
        let ll = format!("{name}{level}.ll");
        clang(
            dir,
            &[level, "-S", "-emit-llvm", "-o", &ll, c.to_str().unwrap()],
            &format!("clang {level} -emit-llvm {name}.c"),
        );
        fs::read_to_string(dir.join(ll)).unwrap()
    }

    /// Link `objects` with `cc` (ld64) and run the program; its stdout.
    fn link_and_run(dir: &Path, objects: &[&str], program: &str) -> String {
        let mut link = native_c_command();
        link.current_dir(dir).args(objects).args(["-o", program]);
        run(&mut link, &format!("cc -o {program}"));
        String::from_utf8(run(&mut Command::new(dir.join(program)), program)).unwrap()
    }

    #[test]
    fn imported_sret_callers_and_callees_match_clang_through_ld64_at_o0_to_o3() {
        let dir = unique_temp_dir("sret-abi");
        fs::write(dir.join("driver.c"), DRIVER_C).unwrap();
        clang(
            &dir,
            &["-O2", "-c", "driver.c", "-o", "driver.o"],
            "clang -c driver.c",
        );
        let mut rows = 0;
        for level in CLANG_LEVELS {
            let ll = clang_ir(&dir, SRET_C, "sret", level);
            // The IR is clang's own: sret definitions, sret declarations and
            // sret calls, which the importer carries onto trust-ir.
            assert!(
                ll.contains("sret(%struct.big)") && ll.contains("sret(%struct.mix)"),
                "clang {level}: no sret in\n{ll}"
            );
            let module = import_text(&ll, "sret_abi").expect("clang's sret IR imports");
            for name in ["make_big", "make_mix", "c_make_big", "c_make_mix"] {
                let function = module
                    .functions
                    .iter()
                    .find(|function| function.name == name)
                    .unwrap_or_else(|| panic!("clang {level}: {name} imported"));
                assert!(
                    function
                        .attrs
                        .params
                        .first()
                        .is_some_and(|attrs| attrs.sret),
                    "clang {level}: {name} lost its sret parameter"
                );
            }

            let reference_object = format!("reference{level}.o");
            clang(
                &dir,
                &[level, "-c", "sret.c", "-o", &reference_object],
                &format!("clang {level} -c sret.c"),
            );
            let reference = link_and_run(
                &dir,
                &["driver.o", &reference_object],
                &format!("reference{level}"),
            );
            assert!(
                reference.ends_with("sret-abi rows=8\n"),
                "clang {level} reference: {reference}"
            );

            let trust_levels: &[OptLevel] = if level == "-O0" {
                &[OptLevel::O0, OptLevel::O2]
            } else {
                &[OptLevel::O2]
            };
            for &trust_level in trust_levels {
                let object = compile_for_host(&ll, "sret_abi", trust_level);
                let object_name = format!("trust-cg{level}-{trust_level:?}.o");
                fs::write(dir.join(&object_name), object).unwrap();
                let stdout = link_and_run(
                    &dir,
                    &["driver.o", &object_name],
                    &format!("trust-cg{level}-{trust_level:?}"),
                );
                assert_eq!(
                    stdout, reference,
                    "clang {level} IR compiled by trust-cg {trust_level:?} disagrees with clang \
                     {level}"
                );
                rows += 1;
            }
        }
        assert_eq!(rows, 5);
    }

    #[test]
    fn clangs_indirect_sret_call_is_refused_by_name_at_every_level() {
        let dir = unique_temp_dir("sret-indirect");
        for level in CLANG_LEVELS {
            let ll = clang_ir(&dir, INDIRECT_C, "indirect", level);
            assert_indirect_sret_refusal(&ll, &format!("clang {level}"));
        }
    }
}
