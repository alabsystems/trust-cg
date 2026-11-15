// trust-cg-codegen/tests/e2e_x86_64_i128_const_shift.rs - 128-bit shifts by a constant on x86-64
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A 128-bit `Ishl`/`Ushr`/`Sshr` by a constant amount trust-ir defines is
//! selected as immediate shifts of the two 64-bit halves (ruling OD-215,
//! `X86InstructionSelector::emit_i128_const_shift`) instead of the general
//! count-in-RCX path with three `cmov`s.
//!
//! Nineteen trust-ir functions, compiled through the AOT `Compiler` at O0..O3
//! for the host's x86-64 triple: `u128 << k`, `u128 >> k` and `i128 >> k` for
//! every `k` in {0, 1, 63, 64, 65, 127} (the amount spelled as the rustc
//! bridge spells a constant 128-bit amount: an in-range constant at the
//! shifted value's type), and `(x >> 64) as u64`, the high-limb extraction of
//! `u128::widening_mul`, `carrying_mul` and Display.
//!
//! * The decode leg (any host with an objdump that reads the object): no
//!   `cmov` and no shift by CL anywhere in the object, at every opt level.
//!   With `TCG_NO_X86_I128_CONST_SHIFT` set (the fold's standalone opt-out)
//!   the same leg asserts the general path instead, so one binary measures
//!   both. Each function's instruction count at O0 is printed
//!   (`I128_CONST_SHIFT_SIZE`).
//! * The native leg (an x86-64 host that links and runs x86-64): a C driver
//!   compares every function, at every opt level, with C's own `unsigned
//!   __int128` / `__int128` shift (an arithmetic `>>` of a signed value in
//!   clang) on 144 values whose halves are edge words: both sign bits (127
//!   and the low half's 63) set and clear, all ones, alternating patterns.

mod common;

use std::fs;

use common::disasm::disassemble_x86_text;
use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout, x86_64_cc, x86_64_link_run_or_skip,
};
use common::x86_64_object::{HOST_IS_MACHO, assert_host_x86_64_object};
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

const AMOUNTS: [u32; 6] = [0, 1, 63, 64, 65, 127];
const KINDS: [(&str, BinOp); 3] = [
    ("shl", BinOp::Shl),
    ("lshr", BinOp::LShr),
    ("ashr", BinOp::AShr),
];
const HIGH_LIMB: &str = "tcg_i128c_lshr_64_as_u64";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn name(kind: &str, amount: u32) -> String {
    format!("tcg_i128c_{kind}_{amount}")
}

fn all_names() -> Vec<String> {
    let mut names: Vec<String> = KINDS
        .iter()
        .flat_map(|(kind, _)| AMOUNTS.iter().map(move |amount| name(kind, *amount)))
        .collect();
    names.push(HIGH_LIMB.to_owned());
    names
}

/// Add `name(x) = x <op> amount` (or, `truncated`, its low 64 bits).
fn add_shift(builder: &mut ModuleBuilder, name: &str, op: BinOp, amount: u32, truncated: bool) {
    let ty = if op == BinOp::AShr {
        Ty::I128
    } else {
        Ty::U128
    };
    let result = if truncated { Ty::U64 } else { ty.clone() };
    let signature = builder.add_func_type(vec![ty.clone()], vec![result]);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, ty.clone());
    f.switch_to_block(entry);
    let count = f.iconst(ty.clone(), i128::from(amount));
    let shifted = f.binop(op, ty.clone(), x, count);
    let value = if truncated {
        f.trunc(ty, Ty::U64, shifted)
    } else {
        shifted
    };
    f.ret(vec![value]);
    f.build();
}

/// Every function, or (`only`) the one named.
fn module(only: Option<&str>) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("e2e_x86_64_i128_const_shift");
    for (kind, op) in KINDS {
        for amount in AMOUNTS {
            let function = name(kind, amount);
            if only.is_none_or(|only| only == function) {
                add_shift(&mut builder, &function, op, amount, false);
            }
        }
    }
    if only.is_none_or(|only| only == HIGH_LIMB) {
        add_shift(&mut builder, HIGH_LIMB, BinOp::LShr, 64, true);
    }
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn host_triple() -> &'static str {
    if HOST_IS_MACHO {
        "x86_64-apple-darwin"
    } else {
        "x86_64-unknown-linux-gnu"
    }
}

fn compile(module: &trust_ir::Module, opt_level: OptLevel) -> Vec<u8> {
    let spec = TargetSpec::parse(host_triple()).expect("x86-64 triple");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            emit_proofs: false,
            parallel: false,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed());
    compiler
        .compile(module)
        .unwrap_or_else(|error| panic!("{opt_level:?}: compile: {error}"))
        .object_code
}

/// Whether the fold's standalone opt-out is set for this process (the
/// selector reads it when it is built).
fn fold_opted_out() -> bool {
    std::env::var_os("TCG_NO_X86_I128_CONST_SHIFT").is_some_and(|value| value != "0")
}

/// The decode leg: no `cmov` and no shift by CL in the object at any opt
/// level (with the opt-out, the general path's `cmov`s instead), and each
/// function's O0 instruction count printed.
#[test]
fn i128_constant_shifts_have_no_count_register_or_cmov_at_any_opt_level() {
    let test = "i128_constant_shifts_have_no_count_register_or_cmov_at_any_opt_level";
    let names = all_names();
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let whole = module(None);
    let general = fold_opted_out();
    for opt_level in OPT_LEVELS {
        let object = compile(&whole, opt_level);
        assert_host_x86_64_object(&format!("{test} {opt_level:?}"), &object, &names, &[]);
        let Some(insns) = disassemble_x86_text(&object) else {
            eprintln!("SKIP: {test}: no objdump decodes this object");
            return;
        };
        let cmovs = insns
            .iter()
            .filter(|insn| insn.mnemonic.starts_with("cmov"))
            .count();
        let by_cl = insns
            .iter()
            .filter(|insn| {
                ["shl", "shr", "sar"]
                    .iter()
                    .any(|op| insn.mnemonic.starts_with(op))
                    && insn.operands.contains("%cl")
            })
            .count();
        eprintln!(
            "[{test}] {opt_level:?} general={general}: {} instructions, {cmovs} cmov, \
             {by_cl} shifts by CL",
            insns.len()
        );
        if general {
            assert!(cmovs > 0 && by_cl > 0, "{opt_level:?}: {insns:#?}");
        } else {
            assert_eq!((cmovs, by_cl), (0, 0), "{opt_level:?}: {insns:#?}");
        }
    }
    for function in &names {
        let object = compile(&module(Some(function)), OptLevel::O0);
        let Some(insns) = disassemble_x86_text(&object) else {
            return;
        };
        eprintln!(
            "I128_CONST_SHIFT_SIZE function={function} opt=O0 general={general} insns={}",
            insns.len()
        );
    }
}

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

typedef unsigned __int128 u128;
typedef __int128 i128;

/* Every function takes and returns its 128-bit value in RDI:RSI / RAX:RDX,
   whatever its signedness; each is called through one pointer type. */
#define DECL(k) \
    extern u128 tcg_i128c_shl_##k(u128); \
    extern u128 tcg_i128c_lshr_##k(u128); \
    extern u128 tcg_i128c_ashr_##k(u128);
DECL(0) DECL(1) DECL(63) DECL(64) DECL(65) DECL(127)
extern uint64_t tcg_i128c_lshr_64_as_u64(u128);

struct shift { const char *name; u128 (*fn)(u128); int kind; unsigned amount; };
#define ROW(k) \
    {"shl_" #k, tcg_i128c_shl_##k, 0, k}, \
    {"lshr_" #k, tcg_i128c_lshr_##k, 1, k}, \
    {"ashr_" #k, tcg_i128c_ashr_##k, 2, k},
static const struct shift shifts[] = {ROW(0) ROW(1) ROW(63) ROW(64) ROW(65) ROW(127)};

static u128 reference(int kind, u128 x, unsigned k) {
    switch (kind) {
    case 0: return x << k;
    case 1: return x >> k;
    default: return (u128)((i128)x >> k);
    }
}

static void print128(const char *what, u128 v) {
    printf("%s=0x%016llx%016llx", what, (unsigned long long)(v >> 64),
           (unsigned long long)v);
}

int main(void) {
    static const uint64_t halves[] = {
        0, 1, 2, 0x7fffffffffffffffull, 0x8000000000000000ull, 0x8000000000000001ull,
        0xffffffffffffffffull, 0xfffffffffffffffeull, 0x5555555555555555ull,
        0xaaaaaaaaaaaaaaaaull, 0x0123456789abcdefull, 0xfedcba9876543210ull};
    const unsigned n = sizeof halves / sizeof halves[0];
    const unsigned nshifts = sizeof shifts / sizeof shifts[0];
    int checks = 0, failures = 0;
    for (unsigned i = 0; i < n; i++) {
        for (unsigned j = 0; j < n; j++) {
            u128 x = ((u128)halves[i] << 64) | halves[j];
            for (unsigned s = 0; s < nshifts; s++) {
                u128 got = shifts[s].fn(x);
                u128 want = reference(shifts[s].kind, x, shifts[s].amount);
                checks++;
                if (got != want) {
                    printf("%s(", shifts[s].name);
                    print128("x", x);
                    printf("): ");
                    print128("got", got);
                    printf(" ");
                    print128("want", want);
                    printf("\n");
                    failures++;
                }
            }
            uint64_t high = tcg_i128c_lshr_64_as_u64(x);
            checks++;
            if (high != (uint64_t)(x >> 64)) {
                printf("lshr_64_as_u64: got=0x%016llx\n", (unsigned long long)high);
                failures++;
            }
        }
    }
    printf("checks=%d failures=%d\n", checks, failures);
    return failures == 0 ? 0 : 1;
}
"#;

/// The native leg: every function at every opt level against C's own shift.
#[test]
fn i128_constant_shifts_run_exactly_on_this_host() {
    let test = "i128_constant_shifts_run_exactly_on_this_host";
    let names = all_names();
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let module = module(None);
    let mut objects = Vec::new();
    for opt_level in OPT_LEVELS {
        let object = compile(&module, opt_level);
        assert_host_x86_64_object(&format!("{test} {opt_level:?}"), &object, &names, &[]);
        objects.push((opt_level, object));
    }
    if !x86_64_link_run_or_skip(test, "x86-64 link/run leg") {
        return;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{test}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER).unwrap();
    for (opt_level, object) in objects {
        let object_path = dir.join(format!("i128_const_shift_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("i128_const_shift_{opt_level:?}"));
        let mut link = x86_64_cc();
        link.arg("-o").arg(&binary).arg(&driver).arg(&object_path);
        let linked = command_output_with_timeout(&mut link, codegen_link_timeout()).unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{opt_level:?}: link failed: {}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let run = run_executable_with_timeout(&binary, codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
        eprintln!(
            "[{test}] {opt_level:?} general={}: {}",
            fold_opted_out(),
            stdout.trim_end()
        );
        assert!(
            !run.timed_out
                && run.output.status.success()
                && stdout.contains("checks=2736 failures=0"),
            "{opt_level:?}: a 128-bit shift by a constant computed a wrong value (status {:?}):\n\
             {stdout}",
            run.output.status
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// `function`'s pre-RA x86-64 rows, `(opcode, operands)` in layout order,
/// selected as `Compiler::compile_x86_64` drives the selector (System V),
/// with the constant-amount `I128` shift fold on or off; `None` when the
/// selector refuses the function.
fn select_x86(
    function: &trust_cg_lower::function::Function,
    fold: bool,
) -> Option<trust_cg_lower::x86_64_isel::X86ISelFunction> {
    use trust_cg_lower::x86_64_isel::{X86CallAbi, X86InstructionSelector};
    let signature = trust_cg_lower::function::Signature {
        params: function.signature.params.clone(),
        returns: function.signature.returns.clone(),
    };
    let mut isel = X86InstructionSelector::with_abi(
        function.name.clone(),
        signature.clone(),
        X86CallAbi::SystemV,
    );
    isel.set_i128_const_shift_fold(fold);
    isel.set_stack_slots(function.stack_slots.clone());
    isel.seed_value_types(&function.value_types);
    isel.seed_function_value_use_counts(function);
    isel.seed_pure_callees(&function.pure_callees);
    isel.seed_sret_param(function.abi_sret_param).ok()?;
    isel.seed_sret_arg_callees(&function.sret_arg_callees);
    isel.seed_sret_arg_indirect_callees(&function.sret_arg_indirect_callees);
    let order = function.layout_order();
    isel.seed_iconst_origins(
        order
            .iter()
            .map(|block| function.blocks[block].instructions.as_slice()),
    );
    for block in &order {
        isel.ensure_block(*block);
    }
    isel.lower_formal_arguments(&signature, function.entry_block)
        .ok()?;
    for block in &order {
        let body = &function.blocks[block];
        if *block != function.entry_block && !body.params.is_empty() {
            isel.define_block_params(&body.params);
        }
        isel.select_block(*block, &body.instructions).ok()?;
    }
    isel.finalize_with_eh_info(&function.eh_info).ok()
}

/// A selected function's rows, `(opcode, operands)` in layout order.
fn rows_of(
    selected: &trust_cg_lower::x86_64_isel::X86ISelFunction,
) -> Vec<(trust_cg_ir::x86_64_ops::X86Opcode, String)> {
    selected
        .block_order
        .iter()
        .flat_map(|block| &selected.blocks[block].insts)
        .map(|inst| (inst.opcode, format!("{:?}", inst.operands)))
        .collect()
}

/// The body theorem's verdict on a selected function (no solver): built,
/// with its bound rows and parts, or refused, with the reason's first words.
fn body_verdict(
    function: &trust_cg_lower::function::Function,
    selected: &trust_cg_lower::x86_64_isel::X86ISelFunction,
) -> String {
    use trust_cg_verify::x86_source_bound_body::{X86SourceBoundAbi, source_bound_x86_body};
    match source_bound_x86_body(function, selected, Some(X86SourceBoundAbi::SystemV)) {
        Ok(body) => format!(
            "built(rows={},parts={})",
            body.bound_rows().len(),
            body.parts().len()
        ),
        Err(refusal) => {
            let text = refusal.to_string();
            format!("refused({})", text.chars().take(120).collect::<String>())
        }
    }
}

/// A diagnostic, not a check (the census proxy of the OD-215 report): every
/// function of every `.trust_irbin` module in `TCG_I128_CONST_SHIFT_CENSUS_DIR`
/// (a census's dump of `core`'s trust-ir), lowered by the x86-64 adapter as a
/// compile lowers it, then selected twice, with the fold on and off: a
/// function whose pre-RA rows differ is one whose bytes the fold changes.
/// Prints one `I128_CONST_SHIFT_CENSUS` line per such function and a
/// summary.
#[test]
#[ignore]
fn census_proxy_lists_functions_with_a_folded_i128_shift() {
    use trust_cg_ir::x86_64_ops::X86Opcode;
    let Some(dir) = std::env::var_os("TCG_I128_CONST_SHIFT_CENSUS_DIR") else {
        eprintln!(
            "SKIP: set TCG_I128_CONST_SHIFT_CENSUS_DIR to a directory of .trust_irbin modules"
        );
        return;
    };
    let mut paths: Vec<_> = fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "trust_irbin"))
        .collect();
    paths.sort();
    let (mut modules, mut whole, mut functions, mut folded_functions) = (0, 0, 0, 0);
    let (mut stubbed, mut folded, mut isel_refused, mut lane_lost) = (0, 0, 0, 0);
    let mut failed = Vec::new();
    for path in &paths {
        let bytes = fs::read(path).unwrap();
        // The bare trust-ir reader: a census dump's bodies carry no codegen
        // license stamp, which `pipeline::decode_binary` refuses; this
        // proxy lowers them under `Permit` and emits nothing.
        let module = match trust_ir::binary::deserialize_module(&bytes) {
            Ok(module) => module,
            Err(error) => {
                failed.push(format!("{}: {error}", path.display()));
                continue;
            }
        };
        modules += 1;
        // Lower the module once, as a compile does. A body the adapter
        // refuses (a census failed root) would stop the batch at its first
        // refusal, so every refused body (`census_module_translation_...`,
        // which decides each one) is first replaced by `unreachable` in its
        // entry block: the proxy reads the other functions' LIR, and a
        // refused function emits no bytes to change.
        let mut module = module;
        let mut stubbed_here = 0;
        for _ in 0..4 {
            let refused =
                match trust_cg_lower::census_module_translation_with_access_model_and_license(
                    &module,
                    trust_cg_lower::GuardCarrierArch::X86_64,
                    trust_cg_lower::TlsDialect::default().into(),
                    &permit_unlicensed(),
                    trust_cg_lower::ObjectSymbolPolicy::X86_64_MACHO_MODULE,
                ) {
                    Ok(rows) => rows,
                    Err(error) => {
                        failed.push(format!("{}: module refused: {error}", path.display()));
                        break;
                    }
                };
            if refused.is_empty() {
                break;
            }
            for (id, _) in &refused {
                let function = module
                    .functions
                    .iter_mut()
                    .find(|function| function.id == *id)
                    .expect("a refused function of the module");
                let entry = function
                    .blocks
                    .iter()
                    .find(|block| block.id == function.entry)
                    .map(|block| block.params.clone())
                    .unwrap_or_default();
                let mut block = trust_ir::Block::new(function.entry);
                block.params = entry;
                block.body = vec![trust_ir::InstrNode::new(trust_ir::Inst::Unreachable)];
                function.blocks = vec![block];
                function.proofs.clear();
                function.summary = None;
                stubbed_here += 1;
            }
        }
        stubbed += stubbed_here;
        // The x86-64 Mach-O compile's own symbol policy (a hidden function
        // definition admitted, as `Compiler::compile_x86_64` admits it).
        let lowered: Vec<trust_cg_lower::function::Function> =
            match trust_cg_lower::translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references(
                &module,
                trust_cg_lower::GuardCarrierArch::X86_64,
                trust_cg_lower::TlsDialect::default(),
                &permit_unlicensed(),
                trust_cg_lower::ObjectSymbolPolicy::X86_64_MACHO_MODULE,
            ) {
                Ok((functions, _)) => {
                    whole += 1;
                    functions
                        .into_iter()
                        .map(|(function, _)| function)
                        .collect()
                }
                Err(error) => {
                    failed.push(format!("{}: batch refused: {error}", path.display()));
                    continue;
                }
            };
        for function in lowered {
            functions += 1;
            // The exact criterion at selection: the function's pre-RA rows
            // with the fold on and off, selected as `Compiler::compile_x86_64`
            // drives the selector. Each fold replaces one general-path shift,
            // which carries exactly three `cmov`s, so the `cmov` difference
            // over 3 counts the folded shifts.
            let (Some(on_fn), Some(off_fn)) =
                (select_x86(&function, true), select_x86(&function, false))
            else {
                isel_refused += 1;
                continue;
            };
            let (on, off) = (rows_of(&on_fn), rows_of(&off_fn));
            if on != off {
                let cmovs = |rows: &[(X86Opcode, String)]| {
                    rows.iter()
                        .filter(|(opcode, _)| *opcode == X86Opcode::Cmovcc)
                        .count()
                };
                let shifts = (cmovs(&off) - cmovs(&on)) / 3;
                folded += shifts;
                folded_functions += 1;
                let (before, after) = (
                    body_verdict(&function, &off_fn),
                    body_verdict(&function, &on_fn),
                );
                if before.starts_with("built") && !after.starts_with("built") {
                    lane_lost += 1;
                }
                eprintln!(
                    "I128_CONST_SHIFT_CENSUS fn={} folded_shifts={shifts} rows={}->{} \
                     theorem_before={before} theorem_after={after}",
                    function.name,
                    off.len(),
                    on.len()
                );
            }
        }
    }
    eprintln!(
        "I128_CONST_SHIFT_CENSUS_SUMMARY modules={modules}/{} batch_translated={whole} \
         refused_bodies_stubbed={stubbed} functions={functions} isel_refused={isel_refused} \
         functions_that_change={folded_functions} folded_shifts={folded} \
         theorems_lost={lane_lost} unreadable={failed:?}",
        paths.len()
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
