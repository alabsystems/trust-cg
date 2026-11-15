// Copyright 2026 Andrew Yates | Apache-2.0
//! TrustIR reference-counting operations (`Inst::Retain`, `Inst::Release`,
//! `Inst::IsUnique`) compiled to ELF for aarch64-unknown-linux-gnu and, on a
//! Linux AArch64 host, executed natively (ledger L05-P3).
//!
//! The shared corpus (`common/arc_ops_corpus.rs`) declares the exact Clean
//! RC-runtime triple as bodyless externals, which is what makes the backend
//! lower the ARC ops to calls. Host-neutral rows compile it at O0-O3 and
//! check, with an independent ELF64 reader and the `trust-cg-lift` decoder,
//! that every RC-runtime and allocator entry is reached by a `BL` carrying an
//! `R_AARCH64_CALL26` relocation against the undefined global symbol, in the
//! expected number; three object mutations show the check can fail. They
//! also pin the trust-ir reference interpreter, run on the corpus's
//! `CleanHeap` twin (`corpus::oracle_twin`), to the corpus's closed forms
//! (it counts a reference-counted cell natively and refuses a release past
//! zero and a `Dealloc` of such a cell), pin the same interpreter, run on
//! the corpus AS COMPILED (`corpus::interpret_as_compiled`), to refusing
//! every row as undefined behaviour naming the rule ("not a
//! reference-counted cell", trust-ir `25624afd`), and keep what stays out of
//! scope refused by name: the same bodies without the exact triple, `Ty::Rc`,
//! `SwiftHeap`/`CleanHeap` cells and a `Dealloc` (refused in every body,
//! G18-1; the corpus frees by calls).
//!
//! trust-ir defines the ARC ops only on a `SwiftHeap`/`CleanHeap` cell (its
//! reference interpreter and Lean's `requireArcRef` both refuse them on any
//! other allocation), and this backend compiles only `CMalloc`/`RustHeap`
//! ones, so the program the Linux-only rows execute is undefined in trust-ir,
//! as the as-compiled interpreter row shows: they test the backend's
//! lowering against the C driver's side-table model of the triple, not the
//! pinned runtime, and are no evidence that the program is defined (the
//! corpus module docs say why the twin is the oracle).
//!
//! The Linux-only rows link each object with
//! `cc -Wl,--wrap=malloc,--wrap=free` against the corpus's C driver, which is
//! the counting runtime (a side table keyed by pointer, seeded at count 1 by
//! the allocator hooks), and run it at O0-O3: every printed result must equal
//! the interpreter's on the twin, and the driver's per-step counts, frees at
//! zero and balance must equal its constant traces. Those counts are driver
//! observations, not interpreter values. Two driver builds that answer the
//! wrong polarity or never free at zero must fail (harness self-checks, not
//! backend controls). Set `ARC_OPS_LINUX_RETAIN_DIR` to a directory to keep
//! each level's object, driver and binaries there for an evidence archive.
//! Execution and object-structure evidence against a stand-in runtime, not
//! proof, and not an execution of the Clean runtime.

#[path = "common/arc_ops_corpus.rs"]
mod corpus;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::BTreeMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lift::disasm::aarch64::{Instruction, decode};
use trust_ir::inst::AllocOrigin;

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const SHT_SYMTAB: u32 = 2;
const SHT_RELA: u32 = 4;
const SHF_EXECINSTR: u64 = 4;
const R_AARCH64_CALL26: u32 = 283;
const R_AARCH64_JUMP26: u32 = 282;

fn compile(module: &trust_ir::Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error:?}"))
}

fn bytes<const N: usize>(object: &[u8], offset: usize) -> Result<[u8; N], String> {
    object
        .get(offset..offset + N)
        .and_then(|slice| slice.try_into().ok())
        .ok_or_else(|| format!("read of {N} bytes at {offset:#x} is out of bounds"))
}

fn u16_at(object: &[u8], offset: usize) -> Result<u16, String> {
    bytes(object, offset).map(u16::from_le_bytes)
}

fn u32_at(object: &[u8], offset: usize) -> Result<u32, String> {
    bytes(object, offset).map(u32::from_le_bytes)
}

fn u64_at(object: &[u8], offset: usize) -> Result<usize, String> {
    bytes(object, offset).map(|raw| u64::from_le_bytes(raw) as usize)
}

fn c_string(object: &[u8], offset: usize) -> Result<String, String> {
    let tail = object
        .get(offset..)
        .ok_or_else(|| format!("string at {offset:#x} is out of bounds"))?;
    let end = tail
        .iter()
        .position(|byte| *byte == 0)
        .ok_or_else(|| format!("string at {offset:#x} is unterminated"))?;
    String::from_utf8(tail[..end].to_vec()).map_err(|error| error.to_string())
}

struct Section {
    kind: u32,
    flags: u64,
    offset: usize,
    size: usize,
    link: usize,
    info: usize,
}

/// A relocation applied to an executable section.
struct TextRelocation {
    symbol: String,
    kind: u32,
    undefined_global: bool,
    /// File offsets of the relocation record and the relocated instruction.
    record: usize,
    instruction: usize,
}

/// Independent System V ELF64 little-endian relocatable-object reader.
fn text_relocations(object: &[u8]) -> Result<Vec<TextRelocation>, String> {
    if object.get(..6) != Some(b"\x7fELF\x02\x01".as_slice()) {
        return Err("not an ELF64 little-endian object".into());
    }
    if u16_at(object, 16)? != 1 || u16_at(object, 18)? != 183 {
        return Err("not an AArch64 relocatable object".into());
    }
    let (shoff, shentsize, shnum) = (
        u64_at(object, 0x28)?,
        u16_at(object, 0x3a)? as usize,
        u16_at(object, 0x3c)? as usize,
    );
    if shentsize != 64 {
        return Err(format!("section header size {shentsize}"));
    }
    let sections = (0..shnum)
        .map(|index| {
            let header = shoff + index * shentsize;
            Ok(Section {
                kind: u32_at(object, header + 4)?,
                flags: u64_at(object, header + 8)? as u64,
                offset: u64_at(object, header + 24)?,
                size: u64_at(object, header + 32)?,
                link: u32_at(object, header + 40)? as usize,
                info: u32_at(object, header + 44)? as usize,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut relocations = Vec::new();
    for rela in sections.iter().filter(|section| section.kind == SHT_RELA) {
        let target = sections.get(rela.info).ok_or("rela target out of range")?;
        if target.flags & SHF_EXECINSTR == 0 {
            continue;
        }
        let symtab = sections.get(rela.link).ok_or("rela symtab out of range")?;
        if symtab.kind != SHT_SYMTAB {
            return Err("rela link is not a symbol table".into());
        }
        let strtab = sections.get(symtab.link).ok_or("strtab out of range")?;
        for entry in 0..rela.size / 24 {
            let record = rela.offset + entry * 24;
            let offset = u64_at(object, record)?;
            let info = u64_at(object, record + 8)? as u64;
            let symbol = symtab.offset + (info >> 32) as usize * 24;
            let name = c_string(object, strtab.offset + u32_at(object, symbol)? as usize)?;
            let binding = bytes::<1>(object, symbol + 4)?[0] >> 4;
            let section_index = u16_at(object, symbol + 6)?;
            if offset + 4 > target.size {
                return Err(format!("relocation offset {offset:#x} outside its section"));
            }
            relocations.push(TextRelocation {
                symbol: name,
                kind: info as u32,
                undefined_global: binding == 1 && section_index == 0,
                record,
                instruction: target.offset + offset,
            });
        }
    }
    Ok(relocations)
}

/// Count the `BL` call sites of each RC-runtime and allocator entry,
/// refusing any other relocation or instruction shape against one.
fn runtime_call_sites(object: &[u8]) -> Result<BTreeMap<String, usize>, String> {
    let mut sites = BTreeMap::new();
    for relocation in text_relocations(object)? {
        if !corpus::CALL_SITES
            .iter()
            .any(|(name, _)| *name == relocation.symbol)
        {
            continue;
        }
        if relocation.kind != R_AARCH64_CALL26 || !relocation.undefined_global {
            return Err(format!(
                "{} is reached by relocation type {} (undefined global: {})",
                relocation.symbol, relocation.kind, relocation.undefined_global
            ));
        }
        let word = u32_at(object, relocation.instruction)?;
        match decode(word) {
            Ok(Instruction::UncondBranch(branch)) if branch.link => {}
            other => {
                return Err(format!(
                    "{} relocation applies to {word:#010x} ({other:?}), not BL",
                    relocation.symbol
                ));
            }
        }
        *sites.entry(relocation.symbol).or_insert(0) += 1;
    }
    Ok(sites)
}

fn expected_call_sites() -> BTreeMap<String, usize> {
    corpus::CALL_SITES
        .iter()
        .map(|(name, count)| (name.to_string(), *count))
        .collect()
}

#[test]
fn elf_object_calls_every_rc_entry_through_bl_o0_through_o3() {
    let module = corpus::corpus(TRIPLE);
    for opt_level in LEVELS {
        let object = compile(&module, opt_level).unwrap();
        let sites = runtime_call_sites(&object);
        assert_eq!(sites, Ok(expected_call_sites()), "{opt_level:?}");
        let rc: Vec<(&str, usize)> = corpus::RC_TRIPLE
            .iter()
            .map(|name| (*name, sites.as_ref().unwrap()[*name]))
            .collect();
        eprintln!("{opt_level:?}: CALL26 BL sites {rc:?}");
    }

    // Mutation controls on the O0 object: a release reached by a
    // non-linking relocation, a relocated instruction that is not BL, and a
    // retain retargeted to the release entry (one CALL26 moves between
    // symbols, so the per-symbol counts no longer match).
    let object = compile(&module, OptLevel::O0).unwrap();
    let relocations = text_relocations(&object).unwrap();
    let release = relocations
        .iter()
        .find(|relocation| relocation.symbol == "clean_dec")
        .unwrap();
    let retain = relocations
        .iter()
        .find(|relocation| relocation.symbol == "clean_inc")
        .unwrap();
    let mut jump = object.clone();
    jump[release.record + 8..release.record + 12].copy_from_slice(&R_AARCH64_JUMP26.to_le_bytes());
    assert!(runtime_call_sites(&jump).is_err());
    let mut branch = object.clone();
    branch[release.instruction + 3] &= 0x7f; // BL -> B
    assert!(runtime_call_sites(&branch).is_err());
    let mut retarget = object.clone();
    let release_symbol: [u8; 4] = bytes(&object, release.record + 12).unwrap();
    retarget[retain.record + 12..retain.record + 16].copy_from_slice(&release_symbol);
    let moved = runtime_call_sites(&retarget).unwrap();
    assert_ne!(moved, expected_call_sites());
    assert_eq!(moved["clean_inc"] + 1, expected_call_sites()["clean_inc"]);
    assert_eq!(moved["clean_dec"], expected_call_sites()["clean_dec"] + 1);
}

#[test]
fn elf_backend_refuses_arc_ops_without_the_exact_clean_triple_o0_through_o3() {
    for runtime in corpus::RcRuntime::NOT_THE_TRIPLE {
        let module = corpus::corpus_with(TRIPLE, runtime);
        for opt_level in LEVELS {
            let error = compile(&module, opt_level)
                .expect_err("ARC ops without the exact Clean triple must be refused");
            // A mis-declared pinned RC entry point is trust-ir's own refusal,
            // and since WS7.3 ingestion admission reports it first, by name;
            // a missing or partial triple is the backend's.
            match runtime.validator_refusal() {
                Some(finding) => assert!(
                    error.contains(finding),
                    "{runtime:?} {opt_level:?}: {error}"
                ),
                None => assert!(
                    error.contains("ARC ") && error.contains("declares no RC runtime"),
                    "{runtime:?} {opt_level:?}: {error}"
                ),
            }
        }
    }
}

#[test]
fn elf_backend_keeps_rc_type_foreign_heaps_and_cross_function_dealloc_refused() {
    for opt_level in [OptLevel::O0, OptLevel::O3] {
        let cases = [
            (
                "Ty::Rc parameter",
                corpus::rc_type_module(TRIPLE),
                &["Ty::Rc", "refcount ownership"][..],
            ),
            (
                "CleanHeap cell",
                corpus::foreign_heap_module(TRIPLE, AllocOrigin::CleanHeap),
                &["AllocOrigin::CleanHeap", "fail-closed"][..],
            ),
            (
                "SwiftHeap cell",
                corpus::foreign_heap_module(TRIPLE, AllocOrigin::SwiftHeap),
                &["AllocOrigin::SwiftHeap", "fail-closed"][..],
            ),
            (
                "Dealloc of a caller's cell",
                corpus::cross_function_dealloc_module(TRIPLE),
                &["[TCG-DEALLOC]", "UnlowerableForCodegen"][..],
            ),
        ];
        for (what, module, needles) in cases {
            let error = compile(&module, opt_level).expect_err(what);
            assert!(
                needles.iter().all(|needle| error.contains(needle)),
                "{what} {opt_level:?}: {error}"
            );
        }
    }
}

#[test]
fn interpreter_oracle_runs_the_clean_heap_twin_to_the_closed_forms_and_refuses_its_ub() {
    let module = corpus::corpus(TRIPLE);
    // The twin moves every compiled cell to the reference-counted heap: the
    // compiled module's cells are all malloc'd, the twin's all `CleanHeap`.
    let compiled = corpus::heap_origins(&module);
    assert!(!compiled.is_empty());
    assert!(
        compiled
            .iter()
            .all(|origin| matches!(origin, AllocOrigin::CMalloc | AllocOrigin::RustHeap)),
        "{compiled:?}"
    );
    assert_eq!(
        corpus::heap_origins(&corpus::oracle_twin(&module)),
        vec![AllocOrigin::CleanHeap; compiled.len()]
    );
    for (name, args, closed_form) in corpus::ORACLE {
        let value = corpus::interpret(&module, name, args);
        assert_eq!(value, Ok(*closed_form), "{}", corpus::call_key(name, args));
        eprintln!(
            "interpreter {}={}",
            corpus::call_key(name, args),
            closed_form
        );
    }
    for (name, args, text) in corpus::INTERPRETER_UB {
        let key = corpus::call_key(name, args);
        let error = match corpus::interpret(&module, name, args) {
            Ok(value) => panic!("{key}: the twin's run is undefined behaviour, got {value}"),
            Err(error) => error,
        };
        assert!(error.contains(text), "{key}: {error}");
        eprintln!("interpreter {key} refused: {text}");
    }
}

/// The premise of the twin, checked rather than stated: on the corpus AS
/// COMPILED (every cell `CMalloc`/`RustHeap`, only the release bodies added)
/// the pinned interpreter refuses every row — each [`corpus::ORACLE`] row
/// the native comparison uses and each [`corpus::INTERPRETER_UB`] row — as
/// undefined behaviour at an ARC op on a non-reference-counted heap cell
/// (trust-ir `25624afd`, `arc_allocation_mut` / `is_unique`). The twin run
/// of the same rows is the closed-form test above; the two differ only in
/// the origin of the cells.
#[test]
fn interpreter_refuses_every_row_of_the_corpus_as_compiled_as_a_non_rc_arc_op() {
    let module = corpus::corpus(TRIPLE);
    let rows = corpus::ORACLE
        .iter()
        .map(|(name, args, _)| (*name, *args))
        .chain(
            corpus::INTERPRETER_UB
                .iter()
                .map(|(name, args, _)| (*name, *args)),
        );
    for (name, args) in rows {
        let key = corpus::call_key(name, args);
        let error = match corpus::interpret_as_compiled(&module, name, args) {
            Ok(value) => panic!(
                "{key}: an ARC op on a CMalloc/RustHeap cell is undefined in trust-ir, got {value}"
            ),
            Err(error) => error,
        };
        assert!(
            error.contains("code: UndefinedBehavior"),
            "{key}: undefined behaviour expected: {error}"
        );
        assert!(
            ["Retain", "Release", "IsUnique"]
                .iter()
                .any(|op| error.contains(&format!("message: \"{op}: pointer addresses "))),
            "{key}: the refusal must be an ARC op's: {error}"
        );
        assert!(
            error.contains("a CMalloc heap cell") || error.contains("a RustHeap heap cell"),
            "{key}: the refusal must name the compiled cell's origin: {error}"
        );
        assert!(
            error.contains("not a reference-counted cell"),
            "{key}: the refusal must name the rule: {error}"
        );
        eprintln!("interpreter (as compiled) {key} refused: {error}");
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

/// Environment variable naming a directory that keeps each native run's
/// files (object, driver source, binaries) instead of deleting them.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
const RETAIN_ENV: &str = "ARC_OPS_LINUX_RETAIN_DIR";

/// A fresh directory for one native run and whether it is retained.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn native_dir(tag: &str) -> (std::path::PathBuf, bool) {
    if let Some(root) = std::env::var_os(RETAIN_ENV) {
        let dir = std::path::Path::new(&root).join(tag);
        assert!(
            !dir.exists(),
            "{dir:?} already exists; retain into a fresh directory"
        );
        std::fs::create_dir_all(&dir).unwrap();
        return (dir, true);
    }
    (
        fresh_dir::create(&format!("trust-cg-arc-ops-linux-{tag}-")).keep(),
        false,
    )
}

/// Link `dir/module.o` against the driver built with `defines` into
/// `dir/<binary>` and run it; returns (exit success, stdout).
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn link_and_run(dir: &std::path::Path, binary: &str, defines: &[&str]) -> (bool, String) {
    use std::process::Command;
    let output = dir.join(binary);
    let link = process::command_output_with_timeout(
        Command::new("cc")
            .arg("-O2")
            .arg("-fno-builtin")
            .args(defines)
            .arg(dir.join("driver.c"))
            .arg(dir.join("module.o"))
            .arg("-Wl,--wrap=malloc,--wrap=free")
            .arg("-o")
            .arg(&output),
        process::codegen_link_timeout(),
    )
    .unwrap();
    assert!(
        !link.timed_out && link.output.status.success(),
        "{binary} files={dir:?}: {}",
        String::from_utf8_lossy(&link.output.stderr)
    );
    let run =
        process::run_executable_with_timeout(&output, process::codegen_run_timeout()).unwrap();
    assert!(!run.timed_out, "{binary} files={dir:?}: timed out");
    // A failing driver must fail by verdict, not by a crash.
    assert!(
        run.output.status.code().is_some(),
        "{binary} files={dir:?}: killed by a signal: {:?} {}",
        run.output.status,
        String::from_utf8_lossy(&run.output.stderr)
    );
    (
        run.output.status.success(),
        String::from_utf8_lossy(&run.output.stdout).into_owned(),
    )
}

/// The driver's `function(args)=value` result lines.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn printed_results(stdout: &str) -> BTreeMap<String, u64> {
    stdout
        .lines()
        .filter(|line| !line.starts_with("trace ") && !line.starts_with("FAIL"))
        .filter_map(|line| line.split_once('='))
        .map(|(key, value)| (key.to_string(), value.parse().expect("decimal result")))
        .collect()
}

/// Compile the corpus at `opt_level` into a fresh native directory.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn prepare(
    module: &trust_ir::Module,
    opt_level: OptLevel,
    tag: &str,
) -> (std::path::PathBuf, bool) {
    let object = compile(module, opt_level).unwrap();
    let (dir, retained) = native_dir(&format!("{tag}-{opt_level:?}"));
    std::fs::write(dir.join("module.o"), &object).unwrap();
    std::fs::write(dir.join("driver.c"), corpus::DRIVER).unwrap();
    (dir, retained)
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[test]
fn native_arc_ops_match_the_interpreter_and_balance_the_counting_runtime_o0_through_o3() {
    let module = corpus::corpus(TRIPLE);
    let oracle: BTreeMap<String, u64> = corpus::ORACLE
        .iter()
        .map(|(name, args, _)| {
            let key = corpus::call_key(name, args);
            let value = corpus::interpret(&module, name, args)
                .unwrap_or_else(|error| panic!("interpreter oracle for {key}: {error}"));
            (key, value)
        })
        .collect();
    for opt_level in LEVELS {
        let (dir, retained) = prepare(&module, opt_level, "arc-ops");
        let (success, stdout) = link_and_run(&dir, "driver", &[]);
        assert!(success, "{opt_level:?} files={dir:?}: {stdout}");
        assert_eq!(
            stdout.lines().last(),
            Some(corpus::EXPECTED_PASS),
            "{opt_level:?} files={dir:?}: incomplete native execution\n{stdout}"
        );
        assert_eq!(
            printed_results(&stdout),
            oracle,
            "{opt_level:?} files={dir:?}: native results differ from the reference interpreter\n{stdout}"
        );
        eprintln!(
            "{opt_level:?}: {}; {} results equal the interpreter",
            corpus::EXPECTED_PASS,
            oracle.len()
        );
        if !retained {
            std::fs::remove_dir_all(&dir).unwrap();
        }
    }
}

/// Harness self-checks, not backend controls: a runtime answering the wrong
/// polarity, or one that never frees at zero, must make the driver fail.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[test]
fn native_harness_self_checks_fail_on_inverted_polarity_and_missing_free_o0_through_o3() {
    let module = corpus::corpus(TRIPLE);
    for opt_level in LEVELS {
        let (dir, retained) = prepare(&module, opt_level, "self-check");

        let (success, stdout) = link_and_run(&dir, "driver-inverted", &["-DCG_INVERT_EXCLUSIVE"]);
        assert!(
            !success,
            "{opt_level:?}: inverted polarity passed\n{stdout}"
        );
        assert!(
            stdout.contains("FAIL arc_share_cycle(7) r "),
            "{opt_level:?}\n{stdout}"
        );
        assert!(
            stdout.contains("FAIL arc_is_unique_after(0) u "),
            "{opt_level:?}\n{stdout}"
        );
        let differing = corpus::ORACLE
            .iter()
            .filter(|(name, args, closed_form)| {
                printed_results(&stdout).get(&corpus::call_key(name, args)) != Some(closed_form)
            })
            .count();
        assert!(
            differing > 0,
            "{opt_level:?}: the interpreter comparison must fail\n{stdout}"
        );

        let (success, stdout) = link_and_run(&dir, "driver-never-free", &["-DCG_NEVER_FREE"]);
        assert!(
            !success,
            "{opt_level:?}: a runtime that never frees passed\n{stdout}"
        );
        assert!(
            stdout.contains("FAIL arc_share_cycle(7) frees_at_zero "),
            "{opt_level:?}\n{stdout}"
        );
        assert!(
            stdout.contains("FAIL arc_share_cycle(7) live_count "),
            "{opt_level:?}\n{stdout}"
        );
        eprintln!(
            "{opt_level:?}: inverted polarity fails ({differing} results differ from the interpreter); never-free fails"
        );
        if !retained {
            std::fs::remove_dir_all(&dir).unwrap();
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
