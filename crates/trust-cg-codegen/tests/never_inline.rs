// trust-cg-codegen/tests/never_inline.rs
//
// `CompilerConfig::never_inline`: a function named there is never spliced by
// OPT-4, the module inliner (the only inliner a compile runs), so every call
// to it stays a call. Checked on the objects `Compiler::compile` emits for
// AArch64 Mach-O and ELF at O1-O3 (the relocation naming the callee), on the
// x86-64 object path (the inliner's own count, since OPT-4 runs before the
// target dispatch), and on the host JIT (its count and the result).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::{BTreeSet, HashMap};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

/// `leaf(x) = x + 1` and `entry(x) = leaf(x) + 2`, both External: `leaf` is a
/// pure single-block leaf OPT-4 splices into `entry` at O1 and above.
fn leaf_module() -> Module {
    let mut module = Module::new("never_inline");
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let add_constant = |id: u32, name: &str, call: Option<u32>, constant: i128| {
        let mut function = Function::new(FuncId::new(id), name, unary, BlockId::new(0));
        let mut body = Vec::new();
        let operand = if let Some(callee) = call {
            body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(callee),
                    args: vec![ValueId::new(0)],
                })
                .with_result(ValueId::new(1)),
            );
            ValueId::new(1)
        } else {
            ValueId::new(0)
        };
        body.extend([
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(constant),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: operand,
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ]);
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body,
        }];
        function
    };
    module
        .try_add_function(add_constant(0, "leaf", None, 1))
        .expect("Module::try_add_function: test fixture");
    module
        .try_add_function(add_constant(1, "entry", Some(0), 2))
        .expect("Module::try_add_function: test fixture");
    module
}

fn config(opt_level: OptLevel, never_inline: &[&str]) -> CompilerConfig {
    CompilerConfig {
        opt_level,
        parallel: false,
        trace_level: CompilerTraceLevel::Full,
        never_inline: never_inline.iter().map(|name| (*name).to_owned()).collect(),
        ..CompilerConfig::default()
    }
}

/// The number of call sites OPT-4 spliced, read from its trace entry
/// (`"<sites> sites / <rounds> rounds..."`); `None` when it did not run.
fn spliced_sites(trace: Option<&trust_cg_codegen::CompilerTrace>) -> Option<usize> {
    let detail = trace?
        .entries
        .iter()
        .find(|entry| entry.phase == "ir_inline")?
        .detail
        .clone()?;
    detail.split(' ').next()?.parse().ok()
}

/// Branch relocations in the object's text that name `leaf`: Mach-O
/// `ARM64_RELOC_BRANCH26` against `_leaf`, ELF `R_AARCH64_CALL26`/`JUMP26`
/// against `leaf` (a call or a tail call).
fn branches_to_leaf(triple: &str, object: &[u8]) -> usize {
    if triple.contains("apple") {
        const ARM64_RELOC_BRANCH26: u8 = 2;
        let records = trust_cg_codegen::macho::reparse::read_object_records(object)
            .expect("AArch64 Mach-O object");
        records
            .section_relocations
            .iter()
            .flatten()
            .filter(|record| {
                record.r_extern
                    && record.r_type == ARM64_RELOC_BRANCH26
                    && records
                        .symbols
                        .get(record.r_symbolnum as usize)
                        .is_some_and(|symbol| symbol.name == "_leaf")
            })
            .count()
    } else {
        const R_AARCH64_JUMP26: u32 = 282;
        const R_AARCH64_CALL26: u32 = 283;
        let records = trust_cg_codegen::elf::reparse::read_object_records(object)
            .expect("AArch64 ELF object");
        records
            .relocations
            .iter()
            .filter(|relocation| {
                [R_AARCH64_CALL26, R_AARCH64_JUMP26].contains(&relocation.record.reloc_type)
                    && records
                        .symbols
                        .get(relocation.record.symbol_index as usize)
                        .is_some_and(|symbol| symbol.name == "leaf")
            })
            .count()
    }
}

fn compile(triple: &str, config: CompilerConfig) -> CompilationResult {
    Compiler::new_for_target_spec(config, TargetSpec::parse(triple).expect("triple"))
        .with_codegen_license(permit_unlicensed())
        .compile(&leaf_module())
        .unwrap_or_else(|error| panic!("{triple}: {error:?}"))
}

/// OPT-4 splices `leaf` into `entry` at O1-O3 unless `leaf` is in the
/// never-inline set, when the call stays a branch relocation against `leaf`.
/// A never-inline name the module does not define changes nothing, and at O0
/// (no OPT-4) the call stays a call either way.
#[test]
fn never_inline_set_is_honored_by_opt4() {
    for triple in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        for opt_level in [OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let label = format!("{triple} {opt_level:?}");
            for unrelated in [&[][..], &["not_in_the_module"]] {
                let inlined = compile(triple, config(opt_level, unrelated));
                assert!(
                    spliced_sites(inlined.trace.as_ref()).is_some_and(|sites| sites >= 1),
                    "{label} {unrelated:?}: OPT-4 splices the leaf (the control is load-bearing)"
                );
                assert_eq!(
                    branches_to_leaf(triple, &inlined.object_code),
                    0,
                    "{label} {unrelated:?}: no call to the spliced leaf remains"
                );
            }
            let kept = compile(triple, config(opt_level, &["leaf"]));
            assert_eq!(
                spliced_sites(kept.trace.as_ref()),
                Some(0),
                "{label}: OPT-4 ran and spliced nothing"
            );
            assert_eq!(
                branches_to_leaf(triple, &kept.object_code),
                1,
                "{label}: the never-inline call stays a branch to `leaf`"
            );
        }
        let at_o0 = compile(triple, config(OptLevel::O0, &[]));
        assert_eq!(spliced_sites(at_o0.trace.as_ref()), None, "{triple} O0");
        assert_eq!(
            branches_to_leaf(triple, &at_o0.object_code),
            1,
            "{triple} O0"
        );
    }

    // OPT-4 runs before the target dispatch, so the x86-64 object path reads
    // the same set.
    for triple in ["x86_64-unknown-linux-gnu", "x86_64-apple-darwin"] {
        let mut x86 = config(OptLevel::O2, &[]);
        x86.target = trust_cg_codegen::target::Target::X86_64;
        let inlined = compile(triple, x86.clone());
        assert!(
            spliced_sites(inlined.trace.as_ref()).is_some_and(|sites| sites >= 1),
            "{triple}: OPT-4 splices the leaf"
        );
        x86.never_inline = BTreeSet::from(["leaf".to_owned()]);
        let kept = compile(triple, x86);
        assert_eq!(spliced_sites(kept.trace.as_ref()), Some(0), "{triple}");
    }
}

/// The host JIT's module step reads the same set; the result is the same
/// either way.
#[test]
fn never_inline_set_is_honored_by_the_jit_module_step() {
    for (never_inline, spliced) in [(&[][..], true), (&["leaf"][..], false)] {
        let mut jit_config = CompilerConfig::for_host_jit_unchecked();
        jit_config.opt_level = OptLevel::O2;
        jit_config.trace_level = CompilerTraceLevel::Full;
        jit_config.never_inline = never_inline.iter().map(|name| (*name).to_owned()).collect();
        let jit = Compiler::new(jit_config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&leaf_module(), &HashMap::new())
            .expect("the module JITs");
        let sites = spliced_sites(jit.trace.as_ref()).expect("the JIT module step ran");
        assert_eq!(sites >= 1, spliced, "{never_inline:?}: {sites} site(s)");
        let entry = unsafe {
            jit.buffer
                .get_fn_bound::<extern "C" fn(i64) -> i64>("entry")
                .expect("entry symbol")
        };
        for input in [-5, 0, 40] {
            assert_eq!(entry.as_ref()(input), input + 3, "{never_inline:?}");
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
