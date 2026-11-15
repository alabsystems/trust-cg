// Inline-only (trust-ir `AvailableExternally`) runtime bodies at the AOT seam
// (`Compiler::compile`), the object-file half of `docs/jit-inline-only-bodies.md`.
//
// The fixture is the shape a frontend with a runtime ships: ONE definition of
// a helper (`tcg_aot_read_lit`, defined by the C runtime the object is linked
// with) plus an inline-only body of its fast path (a bounds check and a load)
// whose out-of-range case calls the runtime's out-of-line remainder
// (`tcg_aot_read_lit_slow`). At O1+ the AOT inliner splices the fast path into
// the caller, so the linked definition is never called and only out-of-range
// reads reach the remainder; at O0, under `TCG_NO_INLINE_ONLY_BODIES`, in a
// compile that emits proofs, and when the symbol is preemptible under `pic`,
// every read calls the definition through the undefined symbol. Every arm
// answers every read identically.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_codegen::{
    CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel,
    INLINE_ONLY_BODIES_KILL_SWITCH, InlineOnlyAdmission, RelocationModel, admit_inline_only_bodies,
};
use trust_cg_lower::{CodegenLicensePolicy, GuardCarrierArch, ObjectAccessModel};
use trust_ir::{
    Endianness, ICmpOp, Linkage, Module, StructPassingPolicy, TargetInfo, Ty, Visibility,
};
use trust_ir_build::ModuleBuilder;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

const DEFINITION: &str = "tcg_aot_read_lit";
const SLOW: &str = "tcg_aot_read_lit_slow";
const DARWIN: &str = "aarch64-apple-darwin";
const LINUX: &str = "aarch64-unknown-linux-gnu";
const X86_LINUX: &str = "x86_64-unknown-linux-gnu";

/// `entry(table, i) = tcg_aot_read_lit(table, i) + tcg_aot_read_lit(table, i + 1)`
/// for `triple`, with an inline-only body of `tcg_aot_read_lit` of
/// `visibility` (when `inline_only`), or a plain declaration of it.
fn read_module(inline_only: bool, visibility: Visibility, triple: &str) -> Module {
    let mut mb = ModuleBuilder::new("aot_inline_only_bodies");
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let slow = mb.declare_function(SLOW, ft);
    let read = if inline_only {
        let mut fb = mb.function(DEFINITION, ft);
        fb.set_linkage(Linkage::AvailableExternally);
        let entry = fb.create_block();
        let table = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        let fast = fb.create_block();
        let slow_block = fb.create_block();
        fb.switch_to_block(entry);
        let len = fb.load(Ty::I64, table);
        let in_range = fb.icmp(ICmpOp::Ult, Ty::I64, index, len);
        fb.condbr(in_range, fast, vec![], slow_block, vec![]);
        fb.switch_to_block(fast);
        let one = fb.iconst(Ty::I64, 1);
        let slot = fb.add(Ty::I64, index, one);
        let element = fb.gep(Ty::I64, table, vec![slot]);
        let value = fb.load(Ty::I64, element);
        fb.ret(vec![value]);
        fb.switch_to_block(slow_block);
        let rest = fb.call(slow, vec![table, index]);
        fb.ret(vec![rest]);
        fb.build()
    } else {
        mb.declare_function(DEFINITION, ft)
    };
    {
        let mut fb = mb.function("entry", ft);
        let entry = fb.create_block();
        let table = fb.add_block_param(entry, Ty::Ptr);
        let index = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let first = fb.call(read, vec![table, index]);
        let one = fb.iconst(Ty::I64, 1);
        let next = fb.add(Ty::I64, index, one);
        let second = fb.call(read, vec![table, next]);
        let sum = fb.add(Ty::I64, first, second);
        fb.ret(vec![sum]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    for function in &mut module.functions {
        if function.name == DEFINITION && inline_only {
            function.visibility = visibility;
        }
    }
    assert_eq!(trust_ir_build::validate_module(&module), []);
    module
}

fn target_of(triple: &str) -> Target {
    if triple.starts_with("x86_64") {
        Target::X86_64
    } else {
        Target::Aarch64
    }
}

// The library's own error type, returned as the compiler returns it.
#[allow(clippy::result_large_err)]
fn compile_with(
    module: &Module,
    triple: &str,
    opt_level: OptLevel,
    relocation_model: RelocationModel,
    emit_proofs: bool,
) -> Result<CompilationResult, trust_cg_codegen::CompileError> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            target: target_of(triple),
            relocation_model,
            emit_proofs,
            trace_level: CompilerTraceLevel::Full,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).expect("target triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
}

fn compile(module: &Module, triple: &str, opt_level: OptLevel) -> CompilationResult {
    compile_with(module, triple, opt_level, RelocationModel::Static, false)
        .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error}"))
}

fn spliced(result: &CompilationResult) -> Vec<(String, usize)> {
    result
        .inline_only_bodies
        .spliced
        .iter()
        .map(|u| (u.name.clone(), u.sites))
        .collect()
}

fn trace_detail(result: &CompilationResult, phase: &str) -> Option<String> {
    result
        .trace
        .as_ref()?
        .entries
        .iter()
        .find(|entry| entry.phase == phase)
        .and_then(|entry| entry.detail.clone())
}

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

#[test]
fn the_aot_seam_splices_and_discloses_an_inline_only_body_at_o1_and_above() {
    for triple in [DARWIN, LINUX, X86_LINUX] {
        let module = read_module(true, Visibility::Default, triple);
        for opt_level in OPT_LEVELS {
            let result = compile(&module, triple, opt_level);
            if opt_level == OptLevel::O0 {
                assert_eq!(
                    result.inline_only_bodies,
                    Default::default(),
                    "{triple}: no inliner at O0"
                );
                continue;
            }
            assert_eq!(
                spliced(&result),
                vec![(DEFINITION.to_string(), 2)],
                "{triple} {opt_level:?}"
            );
            assert!(result.inline_only_bodies.withheld.is_empty());
            let premises = result.inline_only_bodies.premises();
            assert_eq!(premises.len(), 1);
            assert!(premises[0].contains("one-definition rule"), "{premises:?}");
            let detail = trace_detail(&result, "ir_inline").expect("ir_inline trace entry");
            assert!(
                detail.contains("2 inline-only site(s) from 1 body(ies), 0 withheld"),
                "{triple} {opt_level:?}: {detail}"
            );
        }
    }
}

#[test]
fn a_module_without_inline_only_bodies_keeps_the_aot_trace_spelling() {
    let result = compile(
        &read_module(false, Visibility::Default, DARWIN),
        DARWIN,
        OptLevel::O2,
    );
    assert_eq!(result.inline_only_bodies, Default::default());
    let detail = trace_detail(&result, "ir_inline").expect("ir_inline trace entry");
    assert!(!detail.contains("inline-only"), "{detail}");
}

#[test]
fn the_kill_switch_and_o0_emit_the_bytes_of_a_module_that_only_declares_the_helper() {
    // Without a splice, the module with an inline-only body and the module
    // that only DECLARES the helper are the same codegen input: the body is
    // never emitted and every call routes to the undefined symbol.
    for triple in [DARWIN, LINUX, X86_LINUX] {
        let declared = |opt_level| {
            compile(
                &read_module(false, Visibility::Default, triple),
                triple,
                opt_level,
            )
        };
        let with_body = |opt_level| {
            compile(
                &read_module(true, Visibility::Default, triple),
                triple,
                opt_level,
            )
        };
        assert_eq!(
            with_body(OptLevel::O0).object_code,
            declared(OptLevel::O0).object_code,
            "{triple} O0"
        );
        trust_cg_codegen::env_lock::with_env_overrides(
            &[(INLINE_ONLY_BODIES_KILL_SWITCH, "1")],
            || {
                for opt_level in [OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let killed = with_body(opt_level);
                    assert!(killed.inline_only_bodies.spliced.is_empty());
                    assert_eq!(killed.inline_only_bodies.withheld.len(), 1);
                    assert!(
                        killed.inline_only_bodies.withheld[0]
                            .reason
                            .contains(INLINE_ONLY_BODIES_KILL_SWITCH),
                        "{:?}",
                        killed.inline_only_bodies.withheld
                    );
                    assert_eq!(
                        killed.object_code,
                        declared(opt_level).object_code,
                        "{triple} {opt_level:?}: the kill switch restores the declaration's bytes"
                    );
                }
            },
        );
        // With the switch off the splice changes the object.
        assert_ne!(
            with_body(OptLevel::O2).object_code,
            declared(OptLevel::O2).object_code,
            "{triple}"
        );
    }
}

#[test]
fn a_preemptible_body_under_pic_is_withheld_and_hidden_or_static_is_spliced() {
    let cases = [
        (RelocationModel::Pic, Visibility::Default, false),
        (RelocationModel::Pic, Visibility::Hidden, true),
        (RelocationModel::Pic, Visibility::Protected, true),
        (RelocationModel::Static, Visibility::Default, true),
        (RelocationModel::Pie, Visibility::Default, true),
    ];
    for (relocation_model, visibility, admitted) in cases {
        let label = format!("{relocation_model} {visibility:?}");
        let result = compile_with(
            &read_module(true, visibility, LINUX),
            LINUX,
            OptLevel::O2,
            relocation_model,
            false,
        )
        .unwrap_or_else(|error| panic!("{label}: {error}"));
        if admitted {
            assert_eq!(
                spliced(&result),
                vec![(DEFINITION.to_string(), 2)],
                "{label}"
            );
            assert!(result.inline_only_bodies.withheld.is_empty(), "{label}");
        } else {
            assert!(result.inline_only_bodies.spliced.is_empty(), "{label}");
            assert_eq!(result.inline_only_bodies.withheld.len(), 1, "{label}");
            let reason = &result.inline_only_bodies.withheld[0].reason;
            assert!(reason.contains("preemptible"), "{label}: {reason}");
            // The call reaches the symbol, exactly as for a declaration.
            let declared = compile_with(
                &read_module(false, Visibility::Default, LINUX),
                LINUX,
                OptLevel::O2,
                relocation_model,
                false,
            )
            .unwrap_or_else(|error| panic!("{label} declaration: {error}"));
            assert_eq!(result.object_code, declared.object_code, "{label}");
        }
    }
}

#[test]
fn a_proof_claim_withholds_every_inline_only_body() {
    let module = read_module(true, Visibility::Default, DARWIN);
    for (makes_claim, admitted) in [(true, false), (false, true)] {
        let candidates = admit_inline_only_bodies(
            &module,
            GuardCarrierArch::AArch64,
            ObjectAccessModel::default(),
            &permit_unlicensed(),
            InlineOnlyAdmission::for_proof_claim(makes_claim),
        );
        if admitted {
            assert_eq!(candidates.bodies.len(), 1);
            assert!(candidates.withheld.is_empty());
        } else {
            assert!(candidates.bodies.is_empty());
            assert_eq!(candidates.withheld.len(), 1);
            assert!(
                candidates.withheld[0]
                    .reason
                    .contains("proof-producing compile"),
                "{:?}",
                candidates.withheld
            );
        }
    }
    // A compile that emits proofs either refuses the module for an unrelated
    // proof gap or compiles it with every inline-only body withheld; it never
    // splices one.
    match compile_with(&module, DARWIN, OptLevel::O2, RelocationModel::Static, true) {
        Ok(result) => {
            assert!(result.inline_only_bodies.spliced.is_empty());
            assert_eq!(result.inline_only_bodies.withheld.len(), 1);
        }
        Err(error) => assert!(
            !matches!(error, trust_cg_codegen::CompileError::IrInline { .. }),
            "{error}"
        ),
    }
}

/// Link the object for `triple` (the host's) with a C runtime that defines the
/// helper and its remainder, run it, and return what it printed.
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn link_and_run(object: &[u8], label: &str) -> String {
    use std::process::Command;
    let directory = fresh_dir::create("trust-cg-aot-inline-only-");
    let object_path = directory.join("module.o");
    std::fs::write(&object_path, object).unwrap();
    let runner = directory.join("runner.c");
    std::fs::write(
        &runner,
        format!(
            r#"#include <stdint.h>
#include <stdio.h>
static unsigned long definition_calls, slow_calls;
int64_t {SLOW}(const int64_t *table, int64_t index) {{
    (void)table;
    slow_calls++;
    return -1000 - index;
}}
int64_t {DEFINITION}(const int64_t *table, int64_t index) {{
    definition_calls++;
    if ((uint64_t)index < (uint64_t)table[0]) return table[1 + index];
    return {SLOW}(table, index);
}}
extern int64_t entry(const int64_t *table, int64_t index);
int main(void) {{
    static const int64_t table[5] = {{4, 10, 20, 30, 40}};
    static const int64_t indices[7] = {{-1, 0, 1, 2, 3, 4, 9}};
    for (int k = 0; k < 7; k++) printf("%lld ", (long long)entry(table, indices[k]));
    printf("definition=%lu slow=%lu\n", definition_calls, slow_calls);
    return 0;
}}
"#
        ),
    )
    .unwrap();
    let binary = directory.join("runner");
    let linked = Command::new("cc")
        .arg("-O0")
        .arg(&runner)
        .arg(&object_path)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run cc");
    assert!(
        linked.status.success(),
        "{label}: link failed: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let ran = Command::new(&binary)
        .output()
        .expect("run the linked fixture");
    assert!(ran.status.success(), "{label}: {ran:?}");
    std::fs::remove_dir_all(&directory).ok();
    String::from_utf8(ran.stdout).unwrap()
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
#[test]
fn inlined_and_called_fast_paths_answer_identically_when_linked_and_run() {
    let host = if cfg!(target_os = "macos") {
        DARWIN
    } else {
        LINUX
    };
    const TABLE: [i64; 5] = [4, 10, 20, 30, 40];
    const INDICES: [i64; 7] = [-1, 0, 1, 2, 3, 4, 9];
    let read = |i: i64| {
        if (i as u64) < (TABLE[0] as u64) {
            TABLE[1 + i as usize]
        } else {
            -1000 - i
        }
    };
    let answers: String = INDICES
        .iter()
        .map(|i| format!("{} ", read(*i) + read(i + 1)))
        .collect();
    let slow = INDICES
        .iter()
        .flat_map(|i| [*i, i + 1])
        .filter(|i| (*i as u64) >= (TABLE[0] as u64))
        .count();
    let reads = INDICES.len() * 2;
    for opt_level in OPT_LEVELS {
        for (inline_only, killed) in [(false, false), (true, false), (true, true)] {
            let label = format!("{opt_level:?} inline_only={inline_only} killed={killed}");
            let module = read_module(inline_only, Visibility::Default, host);
            let result = if killed {
                trust_cg_codegen::env_lock::with_env_overrides(
                    &[(INLINE_ONLY_BODIES_KILL_SWITCH, "1")],
                    || compile(&module, host, opt_level),
                )
            } else {
                compile(&module, host, opt_level)
            };
            let spliced = !result.inline_only_bodies.spliced.is_empty();
            assert_eq!(
                spliced,
                inline_only && !killed && opt_level != OptLevel::O0,
                "{label}"
            );
            let definition_calls = if spliced { 0 } else { reads };
            assert_eq!(
                link_and_run(&result.object_code, &label),
                format!("{answers}definition={definition_calls} slow={slow}\n"),
                "{label}"
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
