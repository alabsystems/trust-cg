// Copyright 2026 Andrew Yates | Apache-2.0
//! By-reference composite arguments on AArch64 (Linux floor target, with
//! host-neutral rows the Darwin floor also runs).
//!
//! AAPCS64 §6.8.2 B.4 (DarwinPCS keeps the rule) replaces a composite larger
//! than 16 bytes that is not an HFA/HVA by a pointer to a copy the CALLER
//! allocates, and the callee owns that copy: a C callee may write its
//! parameter. trust-cg represents an aggregate value by the address of its
//! storage, and it used to pass that address itself, so a C callee that wrote
//! its parameter changed the caller's value (2026-09-23: the aggregate insert
//! fix's `cg_calls_c` probe failed 4 of 16 checks at every level).
//!
//! The corpora (`fixtures/large_aggregate_args`) pass such composites from a
//! parameter, a constant, a load, a block parameter, an insert result, the same
//! value twice, a loop, a trust-cg callee, and through a function pointer, an
//! sret call, a variadic call, an invoke and eight-register spills to the
//! stack, with 20-, 24-, 32-, 16-aligned 32-, 40-, 320-, 1,024- and
//! 72,000-byte types. Every C/C++ callee digests the bytes it received and
//! then writes every by-reference parameter (the invoke callees also throw on
//! odd input); each trust-cg function stores what it passed after the call.
//!
//! The trust-ir adapter makes the copy (a `Memcpy`, a `memcpy` call above 32
//! bytes) or passes a load/constant/insert's own slot when the call is that
//! value's only use, and an invoke with such an argument moves into a block
//! of its own after the copy. The first version copied inline in instruction
//! selection with no size limit: a 72,000-byte argument took 47 s to compile
//! at O1 and a 288,000-byte one did not finish at O2.
//!
//! Host-neutral rows: the corpora are canonical trust-ir; the main, tail,
//! invoke and scaling corpora compile for Linux and Darwin at O0-O3, and the
//! variadic one on Linux (Darwin refuses a by-reference anonymous argument by
//! name); a call passing a composite by reference keeps its `BL` at every
//! level on both targets while the scalar control becomes a tail branch at
//! O2/O3; the scaling corpus (72 KB, 288 KB, 64 calls passing 1 KiB) emits a
//! bounded number of instructions; every invoke with a by-reference argument
//! sits alone in its protected block; and the lowered LIR copies exactly the
//! arguments whose storage the caller still reads. The Linux-only rows link each
//! level's objects against the C oracle (`driver.c`, with `cc`) and the C++
//! oracle (`invoke_driver.cc`, with `c++`) and require every digest and every
//! stored byte to match. Execution and structural evidence, not a proof.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::Module;

#[path = "common/native_host.rs"]
mod host;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

const CORPUS: &str = include_str!("fixtures/large_aggregate_args/corpus.trust_ir");
const TAIL: &str = include_str!("fixtures/large_aggregate_args/tail.trust_ir");
const VARIADIC: &str = include_str!("fixtures/large_aggregate_args/variadic.trust_ir");
const INVOKE: &str = include_str!("fixtures/large_aggregate_args/invoke.trust_ir");
const SCALING: &str = include_str!("fixtures/large_aggregate_args/scaling.trust_ir");
const INVOKE_VARIADIC: &str =
    include_str!("fixtures/large_aggregate_args/invoke_variadic.trust_ir");
const LINUX: &str = "aarch64-unknown-linux-gnu";
const DARWIN: &str = "aarch64-apple-darwin";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Every trust-cg function the C driver checks, with its corpus and its
/// expected number of checks (the driver's `shape NAME checks=N` line).
/// `cg_sink` is only a callee of `cg_to_cg`.
const SHAPES: &[(&str, &str, u32)] = &[
    ("corpus", "param_pass", 45),
    ("corpus", "const_pass", 15),
    ("corpus", "load_pass", 81),
    ("corpus", "twice_pass", 45),
    ("corpus", "spill_pass", 45),
    ("corpus", "mixed_pass", 60),
    ("corpus", "huge_pass", 123),
    ("corpus", "indirect_pass", 45),
    ("corpus", "sret_pass", 81),
    ("corpus", "loop_pass", 60),
    ("corpus", "cg_writes_param", 81),
    ("corpus", "cg_to_cg", 45),
    ("corpus", "phi_pass", 78),
    ("tail", "tail_pass", 45),
    ("tail", "tail_const", 3),
    ("tail", "tail_huge", 123),
    ("tail", "tail_scalar", 3),
    ("variadic", "var_mut_pass", 45),
    ("variadic", "var_value_pass", 24),
    ("corpus", "five_pass", 18),
    ("corpus", "giant_pass", 15),
    ("corpus", "many_pass", 9),
    // `k_param_pass`/`k_block_pass` (corpus) and `var_param_k`,
    // `var_block_k`, `var_param_m2` (variadic): parameters over 256 bytes
    // forwarded in fixed and anonymous positions.
    ("driver", "param_big", 36),
];

/// The variadic-invoke corpus's shapes and their C++ oracle check counts.
/// Read only by the Linux-native leg.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
const INVOKE_VARIADIC_SHAPES: &[(&str, u32)] = &[("inv_var_param", 8), ("inv_var_block_k", 12)];

/// The invoke corpus's shapes, with their C++ oracle check counts
/// (`inv_load` covers `inv_load_copy` and `inv_load_fast`). Read only by the
/// Linux-native leg.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
const INVOKE_SHAPES: &[(&str, u32)] = &[("inv_param", 8), ("inv_load", 20), ("inv_giant", 6)];

fn parse(name: &str) -> Module {
    let text = match name {
        "corpus" => CORPUS,
        "tail" => TAIL,
        "variadic" => VARIADIC,
        "invoke" => INVOKE,
        "scaling" => SCALING,
        "invoke_variadic" => INVOKE_VARIADIC,
        other => panic!("no corpus {other}"),
    };
    trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{name} parses: {e:?}"))
}

fn module_for(name: &str, triple: &str) -> Module {
    let mut module = parse(name);
    module
        .target_info
        .as_mut()
        .expect("the corpus declares a target")
        .triple = triple.into();
    module
}

fn compile(module: &Module, triple: &str, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error:?}"))
}

fn magic(triple: &str) -> &'static [u8] {
    if triple == LINUX {
        b"\x7fELF"
    } else {
        &[0xcf, 0xfa, 0xed, 0xfe]
    }
}

#[test]
fn corpora_are_canonical_trust_ir_defining_every_shape() {
    for name in [
        "corpus",
        "tail",
        "variadic",
        "invoke",
        "scaling",
        "invoke_variadic",
    ] {
        let module = parse(name);
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "{name} must validate: {errors:?}");
        for (_, shape, _) in SHAPES.iter().filter(|(corpus, _, _)| *corpus == name) {
            assert!(
                module
                    .functions
                    .iter()
                    .any(|f| f.name == *shape && !f.blocks.is_empty()),
                "{shape} is not defined in {name}"
            );
        }
    }
    for (name, functions) in [
        ("corpus", &["k_param_pass", "k_block_pass"][..]),
        (
            "variadic",
            &["var_param_k", "var_block_k", "var_param_m2"][..],
        ),
        ("invoke_variadic", &["inv_var_param", "inv_var_block_k"][..]),
    ] {
        let module = parse(name);
        for function in functions {
            assert!(
                module
                    .functions
                    .iter()
                    .any(|f| f.name == *function && !f.blocks.is_empty()),
                "{function} is not defined in {name}"
            );
        }
    }
}

/// The main, tail, invoke and scaling corpora compile for both conventions
/// at every level. The variadic corpus compiles for base AAPCS64; DarwinPCS
/// refuses a by-reference anonymous argument (`[TCG-VARARG-ABI]`) because
/// clang's caller and `va_arg` disagree about it. The variadic-invoke corpus
/// compiles for base AAPCS64, and DarwinPCS refuses an invoke of a variadic
/// callee by name, because an invoke carries no fixed-argument count to put
/// the anonymous arguments on the stack by. Until 2026-09-23 the variadic
/// corpus's parameters over 256 bytes (`var_param_k`, `var_block_k`,
/// `var_param_m2`) were refused on Linux too (`[TCG-BYREF-COPY]`).
#[test]
fn corpora_compile_for_linux_and_darwin_o0_through_o3() {
    for triple in [LINUX, DARWIN] {
        for name in ["corpus", "tail", "invoke", "scaling"] {
            let module = module_for(name, triple);
            for level in LEVELS {
                let object = compile(&module, triple, level)
                    .unwrap_or_else(|e| panic!("{name} {triple} {level:?}: {e}"));
                assert_eq!(&object[..4], magic(triple), "{name} {triple} {level:?}");
            }
        }
    }
    for (name, darwin_refusal) in [
        ("variadic", "passes anonymous argument"),
        ("invoke_variadic", "invoke of variadic callee"),
    ] {
        let linux = module_for(name, LINUX);
        let darwin = module_for(name, DARWIN);
        for level in LEVELS {
            let object = compile(&linux, LINUX, level)
                .unwrap_or_else(|e| panic!("{name} {LINUX} {level:?}: {e}"));
            assert_eq!(&object[..4], magic(LINUX), "{name} {level:?}");
            let refusal = compile(&darwin, DARWIN, level)
                .expect_err("DarwinPCS refuses the anonymous by-reference placement");
            assert!(
                refusal.contains("[TCG-VARARG-ABI]") && refusal.contains(darwin_refusal),
                "{name} {DARWIN} {level:?}: {refusal}"
            );
        }
    }
}

/// Unconditional `B` / `BL` with a zero immediate: a branch to a relocated
/// external symbol.
const EXTERNAL_B: u32 = 0x1400_0000;
const EXTERNAL_BL: u32 = 0x9400_0000;

/// The copy of a by-reference argument lives in the caller's frame, which a
/// tail branch frees before the callee runs. `tail_pass`, `tail_const` and
/// `tail_huge` keep their `BL` at every level on both targets (`tail_huge`'s
/// 320-byte copy adds a `BL memcpy`); the register-only `tail_scalar` control
/// becomes a `B` where the tail pass runs (O2/O3), so the pass was live on
/// this corpus.
#[test]
fn by_reference_calls_in_tail_position_keep_their_bl() {
    for triple in [LINUX, DARWIN] {
        let module = module_for("tail", triple);
        for level in LEVELS {
            let object = compile(&module, triple, level).unwrap();
            let words = host::text_words(&object);
            let b = words.iter().filter(|w| **w == EXTERNAL_B).count();
            let bl = words.iter().filter(|w| **w == EXTERNAL_BL).count();
            let tail_pass_runs = matches!(level, OptLevel::O2 | OptLevel::O3);
            let want = if tail_pass_runs { (1, 4) } else { (0, 5) };
            assert_eq!((b, bl), want, "{triple} {level:?}: (B, BL)");
        }
    }
}

/// Emitted instructions for the scaling corpus at every level: 72,000- and
/// 288,000-byte by-reference arguments that are copied, and 64 calls in one
/// block each passing a copy of a 1 KiB value. The first version unrolled
/// every copy inline (4,500 LDP/STP pairs for 72 KB) and the per-block passes
/// are quadratic in block length (47 s at O1 for 72 KB; 288 KB at O2 did not
/// finish). A copy is now one `memcpy` call, so the code is bounded; the part
/// that still grows with the frame is the epilogue's existing 4,080-byte
/// `ADD SP` steps (about 140 for the 576 KB frame of `pass288k`).
#[test]
fn by_reference_copies_keep_code_size_bounded() {
    const MAX_INSTRUCTIONS: usize = 1_400;
    for triple in [LINUX, DARWIN] {
        let module = module_for("scaling", triple);
        for level in LEVELS {
            let start = std::time::Instant::now();
            let object = compile(&module, triple, level)
                .unwrap_or_else(|e| panic!("scaling {triple} {level:?}: {e}"));
            let words = host::text_words(&object);
            eprintln!(
                "scaling {triple} {level:?}: {} instructions, {:.2?}",
                words.len(),
                start.elapsed()
            );
            assert!(
                words.len() <= MAX_INSTRUCTIONS,
                "scaling {triple} {level:?}: {} instructions",
                words.len()
            );
            // One BL per call and one `memcpy` per copy (64 + 64 for
            // `many64`, 2 + 2 for the others), and a `memmove` for each of
            // the three aggregate loads and three aggregate stores.
            let bl = words.iter().filter(|w| **w == EXTERNAL_BL).count();
            assert_eq!(bl, 64 + 64 + 2 + 2 + 6, "scaling {triple} {level:?}: BL");
        }
    }
}

/// The adapter's decision per argument, pinned on the lowered LIR as the
/// `Memcpy` lengths each function makes before its calls: a parameter, a
/// constant or load read again, and a value passed twice are copied; a load
/// used only by its call passes its own slot (`giant_load_pass`: no copy).
#[test]
fn adapter_copies_only_storage_the_caller_still_reads() {
    use trust_cg_lower::instructions::{Opcode, Value};
    let functions =
        permit_translate_module(&module_for("corpus", LINUX)).expect("the corpus lowers");
    for (name, want) in [
        ("param_pass", vec![32]),
        ("const_pass", vec![32, 32]),
        ("load_pass", vec![32]),
        ("twice_pass", vec![32, 32]),
        ("five_pass", vec![40]),
        ("giant_pass", vec![72_000]),
        ("giant_load_pass", vec![]),
        ("many_pass", vec![1_024; 8]),
        // A parameter (not owned) is copied; a block parameter is filled by
        // its edge copy and copied again for the call.
        ("k_param_pass", vec![1_024]),
        ("k_block_pass", vec![1_024, 1_024]),
    ] {
        let (function, _) = functions
            .iter()
            .find(|(f, _)| f.name == name)
            .unwrap_or_else(|| panic!("no lowered {name}"));
        let insts: Vec<_> = function
            .block_order
            .iter()
            .flat_map(|block| function.blocks[block].instructions.iter())
            .collect();
        let length = |value: Value| {
            insts
                .iter()
                .find_map(|i| match i.opcode {
                    Opcode::Iconst { imm, .. } if i.results.contains(&value) => Some(imm),
                    _ => None,
                })
                .expect("a constant copy length")
        };
        let copies: Vec<i64> = insts
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::Memcpy))
            .map(|i| length(i.args[2]))
            .collect();
        assert_eq!(copies, want, "{name}: Memcpy lengths");
    }
}

/// Every invoke with a by-reference argument sits alone in its protected
/// block, entered by a jump from the block that made the copy (or holds the
/// load whose slot it passes); the exception metadata names that block.
#[test]
fn invokes_with_by_reference_arguments_sit_alone_in_their_block() {
    use trust_cg_lower::instructions::Opcode;
    let functions =
        permit_translate_module(&module_for("invoke", LINUX)).expect("the invoke corpus lowers");
    for name in ["inv_param", "inv_load_copy", "inv_load_fast", "inv_giant"] {
        let (function, _) = functions
            .iter()
            .find(|(f, _)| f.name == name)
            .unwrap_or_else(|| panic!("no lowered {name}"));
        let invoke_blocks: Vec<_> = function
            .blocks
            .iter()
            .filter(|(_, block)| {
                block
                    .instructions
                    .iter()
                    .any(|i| matches!(i.opcode, Opcode::Invoke { .. }))
            })
            .collect();
        assert_eq!(invoke_blocks.len(), 1, "{name}");
        let (invoke_block, block) = invoke_blocks[0];
        assert_eq!(
            block.instructions.len(),
            1,
            "{name}: {:?}",
            block.instructions
        );
        let sites: Vec<_> = function.eh_info.call_sites.iter().collect();
        assert_eq!(sites.len(), 1, "{name}");
        assert_eq!(sites[0].call_block, *invoke_block, "{name}");
        let predecessors: Vec<_> = function
            .blocks
            .values()
            .filter(|b| {
                b.instructions.last().is_some_and(
                    |i| matches!(i.opcode, Opcode::Jump { dest } if dest == *invoke_block),
                )
            })
            .collect();
        assert_eq!(predecessors.len(), 1, "{name}");
        let copies = predecessors[0]
            .instructions
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::Memcpy))
            .count();
        let want = if name == "inv_load_fast" { 0 } else { 1 };
        assert_eq!(copies, want, "{name}: argument copies before the invoke");
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod native {
    use super::{
        INVOKE_SHAPES, INVOKE_VARIADIC_SHAPES, LEVELS, LINUX, SHAPES, compile, module_for, process,
    };
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use trust_cg_codegen::pipeline::OptLevel;

    const DRIVER: &str = include_str!("fixtures/large_aggregate_args/driver.c");
    const INVOKE_DRIVER: &str = include_str!("fixtures/large_aggregate_args/invoke_driver.cc");
    const INVOKE_VARIADIC_DRIVER: &str =
        include_str!("fixtures/large_aggregate_args/invoke_variadic_driver.cc");
    const CORPORA: [&str; 3] = ["corpus", "tail", "variadic"];

    fn scratch() -> crate::fresh_dir::ScratchDir {
        crate::fresh_dir::create("trust-cg-large-aggregate-args-")
    }

    /// Link the level's objects against the C oracle and run it; returns
    /// stdout and whether the driver exited successfully.
    fn run_driver(dir: &Path, level: OptLevel, objects: &[(String, Vec<u8>)]) -> (String, bool) {
        run_with(dir, level, objects, "cc", "driver.c", DRIVER)
    }

    fn run_with(
        dir: &Path,
        level: OptLevel,
        objects: &[(String, Vec<u8>)],
        compiler: &str,
        driver_name: &str,
        driver: &str,
    ) -> (String, bool) {
        let binary = dir.join(format!("driver-{level:?}"));
        fs::write(dir.join(driver_name), driver).unwrap();
        let mut link = Command::new(compiler);
        link.args(["-O2", "-Wall", "-Werror"])
            .arg(dir.join(driver_name));
        for (name, object) in objects {
            let path = dir.join(name);
            fs::write(&path, object).unwrap();
            link.arg(path);
        }
        link.arg("-o").arg(&binary);
        let link = process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
            .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{level:?} link files={dir:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        assert!(!run.timed_out, "{level:?} timed out files={dir:?}");
        (
            String::from_utf8_lossy(&run.output.stdout).into_owned(),
            run.output.status.success(),
        )
    }

    #[test]
    fn native_shapes_match_the_c_oracle_o0_through_o3() {
        let retain = std::env::var_os("TCG_LARGE_AGGREGATE_ARGS_RETAIN").map(PathBuf::from);
        let total: u32 = SHAPES.iter().map(|(_, _, checks)| checks).sum();
        for level in LEVELS {
            let objects: Vec<(String, Vec<u8>)> = CORPORA
                .iter()
                .map(|name| {
                    let object = compile(&module_for(name, LINUX), LINUX, level)
                        .unwrap_or_else(|e| panic!("{name} {level:?}: {e}"));
                    (format!("{name}-{level:?}.o"), object)
                })
                .collect();
            let dir = scratch();
            let (stdout, success) = run_driver(&dir, level, &objects);
            if let Some(retain) = &retain {
                fs::create_dir_all(retain).unwrap();
                for (name, object) in &objects {
                    fs::write(retain.join(name), object).unwrap();
                }
                fs::write(retain.join(format!("{level:?}.stdout")), &stdout).unwrap();
                fs::write(retain.join("driver.c"), DRIVER).unwrap();
            }
            let lines: Vec<&str> = stdout.lines().collect();
            for (_, name, checks) in SHAPES {
                let want = format!("shape {name} checks={checks} failures=0 ok");
                assert!(
                    lines.contains(&want.as_str()),
                    "{level:?}: missing `{want}` files={dir:?}\n{stdout}"
                );
            }
            let summary = format!("large-aggregate-args shapes_failed=0 checks={total} failures=0");
            assert_eq!(
                lines.last().copied(),
                Some(summary.as_str()),
                "{level:?} files={dir:?}\n{stdout}"
            );
            assert!(success, "{level:?}: driver failed files={dir:?}\n{stdout}");
            eprintln!("{level:?}: {summary}");
            fs::remove_dir_all(&dir).unwrap();
        }
    }

    /// The invoke corpus against the C++ oracle at O0-O3: the callees write
    /// their parameter and throw on odd input, and the values the trust-cg
    /// functions store on both paths, and the sources, are unchanged.
    #[test]
    fn native_invokes_match_the_cxx_oracle_o0_through_o3() {
        let retain = std::env::var_os("TCG_LARGE_AGGREGATE_ARGS_RETAIN").map(PathBuf::from);
        let total: u32 = INVOKE_SHAPES.iter().map(|(_, checks)| checks).sum();
        for level in LEVELS {
            let object = compile(&module_for("invoke", LINUX), LINUX, level)
                .unwrap_or_else(|e| panic!("invoke {level:?}: {e}"));
            let objects = vec![(format!("invoke-{level:?}.o"), object)];
            let dir = scratch();
            let (stdout, success) = run_with(
                &dir,
                level,
                &objects,
                "c++",
                "invoke_driver.cc",
                INVOKE_DRIVER,
            );
            if let Some(retain) = &retain {
                fs::create_dir_all(retain).unwrap();
                fs::write(retain.join(&objects[0].0), &objects[0].1).unwrap();
                fs::write(retain.join(format!("invoke-{level:?}.stdout")), &stdout).unwrap();
                fs::write(retain.join("invoke_driver.cc"), INVOKE_DRIVER).unwrap();
            }
            let lines: Vec<&str> = stdout.lines().collect();
            for (name, checks) in INVOKE_SHAPES {
                let want = format!("shape {name} checks={checks} failures=0 ok");
                assert!(
                    lines.contains(&want.as_str()),
                    "{level:?}: missing `{want}` files={dir:?}\n{stdout}"
                );
            }
            let summary =
                format!("large-aggregate-invoke shapes_failed=0 checks={total} failures=0");
            assert_eq!(
                lines.last().copied(),
                Some(summary.as_str()),
                "{level:?} files={dir:?}\n{stdout}"
            );
            assert!(success, "{level:?}: driver failed files={dir:?}\n{stdout}");
            eprintln!("{level:?}: {summary}");
            fs::remove_dir_all(&dir).unwrap();
        }
    }

    /// Invokes of a variadic callee on Linux against the C++ oracle at O0-O3:
    /// a parameter and a 1,024-byte block parameter forwarded as anonymous
    /// by-reference arguments to callees that write them and throw on odd
    /// input.
    #[test]
    fn native_variadic_invokes_match_the_cxx_oracle_o0_through_o3() {
        let retain = std::env::var_os("TCG_LARGE_AGGREGATE_ARGS_RETAIN").map(PathBuf::from);
        let total: u32 = INVOKE_VARIADIC_SHAPES
            .iter()
            .map(|(_, checks)| checks)
            .sum();
        for level in LEVELS {
            let object = compile(&module_for("invoke_variadic", LINUX), LINUX, level)
                .unwrap_or_else(|e| panic!("invoke_variadic {level:?}: {e}"));
            let objects = vec![(format!("invoke-variadic-{level:?}.o"), object)];
            let dir = scratch();
            let (stdout, success) = run_with(
                &dir,
                level,
                &objects,
                "c++",
                "invoke_variadic_driver.cc",
                INVOKE_VARIADIC_DRIVER,
            );
            if let Some(retain) = &retain {
                fs::create_dir_all(retain).unwrap();
                fs::write(retain.join(&objects[0].0), &objects[0].1).unwrap();
                fs::write(
                    retain.join(format!("invoke-variadic-{level:?}.stdout")),
                    &stdout,
                )
                .unwrap();
                fs::write(
                    retain.join("invoke_variadic_driver.cc"),
                    INVOKE_VARIADIC_DRIVER,
                )
                .unwrap();
            }
            let lines: Vec<&str> = stdout.lines().collect();
            for (name, checks) in INVOKE_VARIADIC_SHAPES {
                let want = format!("shape {name} checks={checks} failures=0 ok");
                assert!(
                    lines.contains(&want.as_str()),
                    "{level:?}: missing `{want}` files={dir:?}\n{stdout}"
                );
            }
            let summary = format!(
                "large-aggregate-invoke-variadic shapes_failed=0 checks={total} failures=0"
            );
            assert_eq!(
                lines.last().copied(),
                Some(summary.as_str()),
                "{level:?} files={dir:?}\n{stdout}"
            );
            assert!(success, "{level:?}: driver failed files={dir:?}\n{stdout}");
            eprintln!("{level:?}: {summary}");
            fs::remove_dir_all(&dir).unwrap();
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
