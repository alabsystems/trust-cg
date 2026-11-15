#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / int_ext_abi_e2e.rs
//
// L01-P11 (the call-ABI parameter attributes): `zeroext` / `signext` on an
// `i8` or `i16` parameter, argument or return value say how the value is
// widened to 32 bits as it crosses a call edge. DarwinPCS makes the caller
// extend an argument and the callee its return value, and a clang-compiled
// peer reads the register without re-extending. The importer typed every
// LLVM `i8`/`i16` as trust-ir `I8`/`I16`, which the backend sign-extends, so
// an imported caller passed `(unsigned char)255` to a clang callee as -1 and
// an imported `unsigned char` function returned 200 to a clang caller as -56.
//
// * Host-neutral: a `zeroext` edge is typed as the unsigned twin
//   (`U8`/`U16`) on definitions, declarations and both kinds of call, with a
//   `Bitcast` between it and the body's signless type; the module compiles
//   for both explicit AArch64 targets. The extensions trust-ir cannot state
//   are refused by name.
// * Native (macOS AArch64): clang's own IR of a C callee unit and a C caller
//   unit at -O0..-O3 is imported, compiled by trust-cg (O0 and O2 for the -O0
//   IR, O2 otherwise), linked by ld64 (through `cc`) with a clang-compiled
//   driver and the other unit built by clang or by trust-cg, and run. Its
//   stdout must equal the program built entirely by clang at the same level.
//   `_Bool` (`zeroext i1`) rows run at -O1..-O3: clang's -O0 IR reloads a
//   `_Bool` through `trunc i8 to i1`, which the backend refuses by name.
//
// All of it is testing evidence about the importer and the backend's call
// lowering, not a proof.

mod common;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_llvm_import::{Error, import_text};
use trust_ir::{CastOp, Module, Ty, inst::Inst};

use common::{TARGETS, compile_for};

/// Hand-written clang-shaped IR: extended parameters and returns on a
/// definition, on declarations, on a direct call before the callee's
/// header, and on an indirect call.
const EXT_LL: &str = r#"
define i32 @caller(i32 noundef %x, ptr noundef %fp) {
  %t = trunc i32 %x to i8
  %a = call i32 @ext_u8(i8 noundef zeroext %t)
  %h = trunc i32 %x to i16
  %b = call signext i16 @ext_s16(i16 noundef signext %h)
  %c = call zeroext i8 @own_u8(i8 noundef zeroext %t, i16 noundef signext %h)
  %d = call zeroext i16 @ext_ret_u16(i32 noundef %x)
  %e = call zeroext i8 %fp(i16 noundef zeroext %h)
  %bw = sext i16 %b to i32
  %cw = zext i8 %c to i32
  %dw = zext i16 %d to i32
  %ew = zext i8 %e to i32
  %s1 = add i32 %a, %bw
  %s2 = add i32 %s1, %cw
  %s3 = add i32 %s2, %dw
  %s4 = add i32 %s3, %ew
  ret i32 %s4
}

define zeroext i8 @own_u8(i8 noundef zeroext %c, i16 noundef signext %s) {
  %w = trunc i16 %s to i8
  %r = add i8 %c, %w
  ret i8 %r
}

declare i32 @ext_u8(i8 noundef zeroext)
declare signext i16 @ext_s16(i16 noundef signext)
declare zeroext i16 @ext_ret_u16(i32 noundef)
"#;

fn func_ty<'m>(module: &'m Module, name: &str) -> &'m trust_ir::FuncTy {
    let function = module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("{name} imported"));
    &module.func_types[function.ty.index() as usize]
}

fn bitcasts(module: &Module, name: &str) -> Vec<(Ty, Ty)> {
    let function = module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("{name} imported"));
    function
        .blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .filter_map(|node| match &node.inst {
            Inst::Cast {
                op: CastOp::Bitcast,
                src_ty,
                dst_ty,
                ..
            } => Some((src_ty.clone(), dst_ty.clone())),
            _ => None,
        })
        .collect()
}

#[test]
fn zeroext_edges_are_unsigned_and_compile_for_both_aarch64_targets() {
    let module = import_text(EXT_LL, "int_ext_abi").expect("the extension module imports");

    let ty = func_ty(&module, "ext_u8");
    assert_eq!(
        (ty.params.clone(), ty.returns.clone()),
        (vec![Ty::U8], vec![Ty::I32])
    );
    let ty = func_ty(&module, "ext_s16");
    assert_eq!(
        (ty.params.clone(), ty.returns.clone()),
        (vec![Ty::I16], vec![Ty::I16])
    );
    let ty = func_ty(&module, "ext_ret_u16");
    assert_eq!(
        (ty.params.clone(), ty.returns.clone()),
        (vec![Ty::I32], vec![Ty::U16])
    );
    let ty = func_ty(&module, "own_u8");
    assert_eq!(
        (ty.params.clone(), ty.returns.clone()),
        (vec![Ty::U8, Ty::I16], vec![Ty::U8])
    );

    // The definition takes its `zeroext` parameter at `U8`, reinterprets it
    // to the body's `I8`, and reinterprets the result back before `ret`.
    let own = module
        .functions
        .iter()
        .find(|function| function.name == "own_u8")
        .unwrap();
    let entry = &own.blocks[own.entry.as_usize()];
    assert_eq!(
        entry
            .params
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>(),
        vec![Ty::U8, Ty::I16]
    );
    assert_eq!(
        bitcasts(&module, "own_u8"),
        vec![(Ty::U8, Ty::I8), (Ty::I8, Ty::U8)]
    );
    // The caller passes each `zeroext` argument at the edge's type and takes
    // each `zeroext` result back: `@ext_u8`, `@own_u8` and the indirect call's
    // argument, then the results of `@own_u8`, `@ext_ret_u16` and the
    // indirect call.
    let mut caller = bitcasts(&module, "caller");
    caller.sort_by_key(|pair| format!("{pair:?}"));
    let mut expected = vec![
        (Ty::I8, Ty::U8),
        (Ty::I8, Ty::U8),
        (Ty::I16, Ty::U16),
        (Ty::U8, Ty::I8),
        (Ty::U16, Ty::I16),
        (Ty::U8, Ty::I8),
    ];
    expected.sort_by_key(|pair| format!("{pair:?}"));
    assert_eq!(caller, expected);

    for triple in TARGETS {
        for level in [OptLevel::O0, OptLevel::O2] {
            // `compile_for` asserts the container and panics on a refusal.
            let object = compile_for(EXT_LL, "int_ext_abi", triple, level);
            assert!(!object.is_empty(), "{triple} {level:?}");
        }
    }
}

fn assert_refused(ll: &str, expected: &str) {
    match import_text(ll, "int_ext_refusal") {
        Err(Error::Unsupported(reason)) => {
            assert!(
                reason.contains(expected),
                "expected `{expected}` in: {reason}"
            )
        }
        Err(other) => panic!("expected the named refusal `{expected}`, got {other}"),
        Ok(_) => panic!("expected the named refusal `{expected}`, but the module imported"),
    }
}

#[test]
fn extensions_trust_ir_cannot_state_are_refused_by_name() {
    // `signext i1` passes true as all ones; trust-ir's `Bool` is 0 or 1.
    assert_refused(
        "define i32 @f(i1 signext %b) {\n  %r = zext i1 %b to i32\n  ret i32 %r\n}\n",
        "function `@f`, parameter 0: `signext i1`",
    );
    assert_refused(
        "declare signext i1 @g()\n",
        "function declaration `@g`, return value: `signext i1`",
    );
    // A call that zero-extends where its callee's edge sign-extends: LLVM
    // extends when either says so, trust-ir states it once, on the callee.
    assert_refused(
        "define i32 @g(i8 %c) {\n  %r = zext i8 %c to i32\n  ret i32 %r\n}\n\
         define i32 @h(i8 %c) {\n  %r = call i32 @g(i8 zeroext %c)\n  ret i32 %r\n}\n",
        "call to `@g` at line 6, argument 0: states `zeroext` but the callee's call edge is \
         typed `I8`",
    );
    // A call before the callee's header that states another extension.
    assert_refused(
        "define i32 @h(i8 %c) {\n  %r = call i32 @k(i8 zeroext %c)\n  ret i32 %r\n}\n\
         declare i32 @k(i8 signext)\n",
        "function `@k`: its headers and calls state different `zeroext` / `signext`",
    );
    // A narrow variadic argument with an extension.
    assert_refused(
        "declare i32 @v(i32, ...)\n\
         define i32 @h(i8 %c) {\n  %r = call i32 (i32, ...) @v(i32 1, i8 zeroext %c)\n  \
         ret i32 %r\n}\n",
        "argument 1: `zeroext` on a narrow variadic argument",
    );
    // Both at once (LLVM's verifier rejects the pair).
    assert_refused(
        "declare i32 @w(i8 zeroext signext)\n",
        "parameter 0: both `zeroext` and `signext`",
    );
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod native {
    use std::fs;
    use std::path::Path;
    use std::process::Command;

    use trust_cg_codegen::pipeline::OptLevel;

    use super::common::{compile_for_host, describe_status, native_c_command, unique_temp_dir};

    /// The callee unit: narrow parameters and returns of each signedness.
    const CALLEE_C: &str = r#"
int take_u8(unsigned char c) { return c; }
int take_u16(unsigned short c) { return c; }
int take_s8(signed char c) { return c; }
int take_s16(short c) { return c * 3; }
unsigned char ret_u8(int x) { return (unsigned char)(x + 1); }
signed char ret_s8(int x) { return (signed char)(x - 1); }
unsigned short ret_u16(int x) { return (unsigned short)(x * 3); }
short ret_s16(int x) { return (short)x; }
unsigned char mix(unsigned char a, signed char b, unsigned short c, short d) {
    return (unsigned char)(a + b + c + d);
}
"#;

    /// The caller unit: direct calls of the callee unit, and calls through
    /// function pointers (the indirect edge states its own extensions).
    const CALLER_C: &str = r#"
int take_u8(unsigned char c);
int take_u16(unsigned short c);
int take_s8(signed char c);
int take_s16(short c);
unsigned char ret_u8(int x);
signed char ret_s8(int x);
unsigned short ret_u16(int x);
short ret_s16(int x);
unsigned char mix(unsigned char a, signed char b, unsigned short c, short d);
int call_u8(int x) { return take_u8((unsigned char)x); }
int call_u16(int x) { return take_u16((unsigned short)x); }
int call_s8(int x) { return take_s8((signed char)x); }
int call_s16(int x) { return take_s16((short)x); }
int use_u8(int x) { return ret_u8(x) + 1; }
int use_s8(int x) { return ret_s8(x) + 1; }
int use_u16(int x) { return ret_u16(x) + 1; }
int use_s16(int x) { return ret_s16(x) + 1; }
int use_mix(int x) {
    return mix((unsigned char)x, (signed char)(x >> 3), (unsigned short)(x * 7), (short)(x * 5));
}
int via_u8(int (*f)(unsigned char), int x) { return f((unsigned char)x); }
int via_ret_u16(unsigned short (*f)(int), int x) { return f(x) + 2; }
"#;

    /// `_Bool` (`zeroext i1`) units, for clang -O1..-O3.
    const BOOL_CALLEE_C: &str = r#"
int take_b(_Bool b) { return b ? 7 : 3; }
_Bool ret_b(int x) { return x > 5; }
"#;
    const BOOL_CALLER_C: &str = r#"
int take_b(_Bool b);
_Bool ret_b(int x);
int call_b(int x) { return take_b(x > 2); }
int use_b(int x) { return ret_b(x) + 1; }
"#;

    const DRIVER_C: &str = r#"
#include <stdio.h>
int take_u8(unsigned char c);
unsigned short ret_u16(int x);
int call_u8(int x);
int call_u16(int x);
int call_s8(int x);
int call_s16(int x);
int use_u8(int x);
int use_s8(int x);
int use_u16(int x);
int use_s16(int x);
int use_mix(int x);
int via_u8(int (*f)(unsigned char), int x);
int via_ret_u16(unsigned short (*f)(int), int x);
int main(void) {
    static const int xs[] = { 0, 1, 127, 128, 200, 255, 256, 32767, 32768, 40000, 65535, 65536,
                              -1, -128, -129, -32768, 0x12345678 };
    unsigned n = sizeof xs / sizeof xs[0];
    for (unsigned i = 0; i < n; i++) {
        int x = xs[i];
        printf("%d: %d %d %d %d | %d %d %d %d | %d | %d %d\n", x,
               call_u8(x), call_u16(x), call_s8(x), call_s16(x),
               use_u8(x), use_s8(x), use_u16(x), use_s16(x),
               use_mix(x), via_u8(take_u8, x), via_ret_u16(ret_u16, x));
    }
    printf("int-ext rows=%u\n", n);
    return 0;
}
"#;

    const BOOL_DRIVER_C: &str = r#"
#include <stdio.h>
int call_b(int x);
int use_b(int x);
int main(void) {
    static const int xs[] = { -3, 0, 2, 3, 5, 6, 1000 };
    unsigned n = sizeof xs / sizeof xs[0];
    for (unsigned i = 0; i < n; i++) printf("%d: %d %d\n", xs[i], call_b(xs[i]), use_b(xs[i]));
    printf("bool-ext rows=%u\n", n);
    return 0;
}
"#;

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

    fn link_and_run(dir: &Path, objects: &[&str], program: &str) -> String {
        let mut link = native_c_command();
        link.current_dir(dir).args(objects).args(["-o", program]);
        run(&mut link, &format!("cc -o {program}"));
        String::from_utf8(run(&mut Command::new(dir.join(program)), program)).unwrap()
    }

    /// For each clang level: the all-clang reference, then every mix of a
    /// trust-cg-compiled callee unit and caller unit with the clang one.
    /// Returns the number of trust-cg builds that matched.
    fn differential(
        dir: &Path,
        units: [(&str, &str); 2],
        driver: &str,
        levels: &[&str],
        expected_tail: &str,
    ) -> usize {
        fs::write(dir.join("driver.c"), driver).unwrap();
        clang(
            dir,
            &["-O2", "-c", "driver.c", "-o", "driver.o"],
            "clang -c driver.c",
        );
        for (name, source) in units {
            fs::write(dir.join(format!("{name}.c")), source).unwrap();
        }
        let mut matched = 0;
        for &level in levels {
            let mut clang_objects = Vec::new();
            let mut ir = Vec::new();
            for (name, _) in units {
                let object = format!("{name}{level}.o");
                clang(
                    dir,
                    &[level, "-c", &format!("{name}.c"), "-o", &object],
                    &format!("clang {level} -c {name}.c"),
                );
                clang_objects.push(object);
                let ll = format!("{name}{level}.ll");
                clang(
                    dir,
                    &[level, "-S", "-emit-llvm", &format!("{name}.c"), "-o", &ll],
                    &format!("clang {level} -emit-llvm {name}.c"),
                );
                ir.push(fs::read_to_string(dir.join(ll)).unwrap());
            }
            assert!(
                ir.iter().any(|ll| ll.contains("zeroext")),
                "clang {level}: no zeroext in the IR"
            );
            let reference = link_and_run(
                dir,
                &["driver.o", &clang_objects[0], &clang_objects[1]],
                &format!("reference{level}"),
            );
            assert!(
                reference.ends_with(expected_tail),
                "clang {level} reference: {reference}"
            );

            let trust_levels: &[OptLevel] = if level == "-O0" {
                &[OptLevel::O0, OptLevel::O2]
            } else {
                &[OptLevel::O2]
            };
            for &trust_level in trust_levels {
                let mut trust_objects = Vec::new();
                for ((name, _), ll) in units.iter().zip(&ir) {
                    let object = format!("trust-{name}{level}-{trust_level:?}.o");
                    fs::write(dir.join(&object), compile_for_host(ll, name, trust_level)).unwrap();
                    trust_objects.push(object);
                }
                // trust-cg callee + clang caller, clang callee + trust-cg
                // caller, and both units by trust-cg.
                let mixes = [
                    [&trust_objects[0], &clang_objects[1]],
                    [&clang_objects[0], &trust_objects[1]],
                    [&trust_objects[0], &trust_objects[1]],
                ];
                for (index, [callee, caller]) in mixes.iter().enumerate() {
                    let program = format!("mix{index}{level}-{trust_level:?}");
                    let stdout = link_and_run(dir, &["driver.o", callee, caller], &program);
                    assert_eq!(
                        stdout, reference,
                        "{callee} + {caller} disagrees with clang {level}"
                    );
                    matched += 1;
                }
            }
        }
        matched
    }

    #[test]
    fn narrow_extension_edges_match_clang_through_ld64_at_o0_to_o3() {
        let dir = unique_temp_dir("int-ext-abi");
        let matched = differential(
            &dir,
            [("callee", CALLEE_C), ("caller", CALLER_C)],
            DRIVER_C,
            &["-O0", "-O1", "-O2", "-O3"],
            "int-ext rows=17\n",
        );
        assert_eq!(matched, 15);
    }

    #[test]
    fn bool_extension_edges_match_clang_through_ld64_at_o1_to_o3() {
        let dir = unique_temp_dir("bool-ext-abi");
        let matched = differential(
            &dir,
            [
                ("bool_callee", BOOL_CALLEE_C),
                ("bool_caller", BOOL_CALLER_C),
            ],
            BOOL_DRIVER_C,
            &["-O1", "-O2", "-O3"],
            "bool-ext rows=7\n",
        );
        assert_eq!(matched, 9);
    }
}
