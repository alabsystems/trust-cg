// trust-cg-codegen/tests/e2e_cegis_superopt.rs - CEGIS superopt pipeline wiring tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression coverage for issue #395: wire the CEGIS superopt pass into the
// pipeline and expose direct observability for integration tests.

use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(feature = "verify")]
use trust_cg_codegen::pipeline::{CegisPassStats, CegisRunOutcome};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, build_add_test_function};
#[cfg(feature = "verify")]
use trust_cg_ir::regs::X0;
#[cfg(feature = "verify")]
use trust_cg_ir::{
    AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature, Type as IrType, VReg,
};

use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty, ValueId,
};

#[cfg(feature = "verify")]
#[path = "common/aarch64_native.rs"]
mod aarch64_native;

static CEGIS_PIPELINE_COUNTER: AtomicU64 = AtomicU64::new(0);

fn unique_test_triple() -> String {
    let id = CEGIS_PIPELINE_COUNTER.fetch_add(1, Ordering::Relaxed);
    // Use an explicit Apple Mach-O AArch64 triple so object emission satisfies the
    // post-merge fail-closed contract (bare `aarch64-unknown-unknown` triples are
    // rejected before Mach-O emission). The `-apple-` infix keeps the triple a
    // valid Mach-O target while the trailing suffix preserves a unique CEGIS
    // cache key per pipeline.
    format!(
        "aarch64-apple-darwin-cegis-test-{}-{}",
        std::process::id(),
        id
    )
}

const CEGIS_TEST_BUDGET_SEC: u64 = 1;

fn make_cegis_pipeline() -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        cegis_superopt_budget_sec: Some(CEGIS_TEST_BUDGET_SEC),
        target_triple: unique_test_triple(),
        ..Default::default()
    })
}

#[cfg(feature = "verify")]
fn make_no_cegis_pipeline() -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        // Explicit Apple Mach-O triple: bare `aarch64-unknown-unknown` now fails
        // closed before object emission under the post-merge contract.
        target_triple: "aarch64-apple-darwin".to_string(),
        ..Default::default()
    })
}

fn build_add_trust_ir() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("test");
    let ft_id = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "add32", ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module
        .try_add_function(func.clone())
        .expect("Module::try_add_function: test fixture");
    (func, module)
}

#[cfg(feature = "verify")]
fn scalar_type_for(class: RegClass) -> IrType {
    match class {
        RegClass::Gpr32 => IrType::I32,
        RegClass::Gpr64 => IrType::I64,
        other => panic!("unsupported CEGIS scalar class in test: {other:?}"),
    }
}

#[cfg(feature = "verify")]
fn alloc_vreg(func: &mut MachFunction, class: RegClass) -> VReg {
    VReg::new(func.alloc_vreg(), class)
}

#[cfg(feature = "verify")]
fn append_inst(func: &mut MachFunction, opcode: AArch64Opcode, operands: Vec<MachOperand>) {
    let id = func.push_inst(MachInst::new(opcode, operands));
    func.append_inst(func.entry, id);
}

#[cfg(feature = "verify")]
fn append_i32_return(func: &mut MachFunction, value: VReg) {
    let copy = MachInst::new(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X0), MachOperand::VReg(value)],
    );
    let id = func.push_inst(copy);
    func.append_inst(func.entry, id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]);
    let id = func.push_inst(ret);
    func.append_inst(func.entry, id);
}

#[cfg(feature = "verify")]
fn build_layer_a_mul_zero_func(name: &str, class: RegClass, optimized: bool) -> MachFunction {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![], vec![scalar_type_for(class)]),
    );
    let v_zero = alloc_vreg(&mut func, class);
    let v_lhs = alloc_vreg(&mut func, class);
    let v_dst = alloc_vreg(&mut func, class);

    append_inst(
        &mut func,
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v_zero), MachOperand::Imm(0)],
    );
    append_inst(
        &mut func,
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v_lhs), MachOperand::Imm(7)],
    );
    if optimized {
        append_inst(
            &mut func,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v_dst), MachOperand::Imm(0)],
        );
    } else {
        append_inst(
            &mut func,
            AArch64Opcode::MulRR,
            vec![
                MachOperand::VReg(v_dst),
                MachOperand::VReg(v_lhs),
                MachOperand::VReg(v_zero),
            ],
        );
    }

    append_i32_return(&mut func, v_dst);
    func
}

#[cfg(feature = "verify")]
fn build_layer_b_movz_add_func(
    name: &str,
    class: RegClass,
    src_imm: i64,
    add_imm: i64,
    optimized: bool,
) -> MachFunction {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![], vec![scalar_type_for(class)]),
    );
    let v_src = alloc_vreg(&mut func, class);
    let v_imm = alloc_vreg(&mut func, class);
    let v_dst = alloc_vreg(&mut func, class);

    append_inst(
        &mut func,
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v_src), MachOperand::Imm(src_imm)],
    );
    if optimized {
        append_inst(
            &mut func,
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(v_dst),
                MachOperand::VReg(v_src),
                MachOperand::Imm(add_imm),
            ],
        );
    } else {
        append_inst(
            &mut func,
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(v_imm), MachOperand::Imm(add_imm)],
        );
        append_inst(
            &mut func,
            AArch64Opcode::AddRR,
            vec![
                MachOperand::VReg(v_dst),
                MachOperand::VReg(v_src),
                MachOperand::VReg(v_imm),
            ],
        );
    }

    append_i32_return(&mut func, v_dst);
    func
}

#[cfg(feature = "verify")]
fn compile_ir_object(pipeline: &Pipeline, mut func: MachFunction) -> Vec<u8> {
    pipeline
        .compile_ir_function(&mut func)
        .expect("hand-crafted CEGIS codegen case should compile")
}

#[cfg(feature = "verify")]
fn assert_cegis_codegen_matches_hand_optimized(
    case_name: &str,
    source: MachFunction,
    hand_optimized: MachFunction,
    check_stats: fn(&CegisPassStats),
) {
    let mut probe = source.clone();
    let run = make_cegis_pipeline()
        .run_cegis_superopt_with_outcome(&mut probe)
        .expect("CEGIS pass should run for the probe function");
    let stats = run.stats;
    // Each case has exactly one solver-backed candidate. The budget only
    // gates starting a verification, so the outcome must not depend on how
    // long that proof took (its first run in a process also establishes the
    // independent checker's identity, which can exceed the 1 s budget).
    eprintln!(
        "{case_name}: solver_ms={} against a {} s budget",
        stats.solver_ms, CEGIS_TEST_BUDGET_SEC
    );
    // An AY the identity rule refuses here stops every solver-backed search;
    // the failure then names that refusal, not only the pass's counters.
    assert_eq!(
        run.outcome,
        CegisRunOutcome::Complete { committed: true },
        "{case_name}: a search whose only candidate was proven must complete, got {stats:?}{}",
        trust_cg_verify::ay_bridge::solver_refusal_note()
            .map(|note| format!("; {note}"))
            .unwrap_or_default()
    );
    assert_eq!(stats.budget_exhausted, 0, "{case_name}: {stats:?}");
    check_stats(&stats);
    assert!(
        stats.verified >= 1,
        "{case_name}: expected at least one proven rewrite, got {stats:?}"
    );

    let no_cegis = make_no_cegis_pipeline();
    let unoptimized_obj = compile_ir_object(&no_cegis, source.clone());
    let hand_optimized_obj = compile_ir_object(&no_cegis, hand_optimized);
    assert_ne!(
        unoptimized_obj, hand_optimized_obj,
        "{case_name}: disabled CEGIS output should differ from the hand-optimized baseline"
    );

    let cegis_obj = compile_ir_object(&make_cegis_pipeline(), source);
    assert_eq!(
        cegis_obj, hand_optimized_obj,
        "{case_name}: CEGIS-enabled codegen must match the hand-optimized object bytes"
    );
}

#[test]
fn test_cegis_flag_is_noop_when_disabled() {
    let pipeline = Pipeline::new(PipelineConfig::for_target("aarch64-apple-darwin"));
    let mut func = build_add_test_function();

    assert!(pipeline.run_cegis_superopt(&mut func).is_none());
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_flag_runs_pass() {
    let pipeline = make_cegis_pipeline();
    let mut func = build_add_test_function();

    let stats = pipeline
        .run_cegis_superopt(&mut func)
        .expect("CEGIS pass should run when budget is enabled");

    assert_eq!(stats.functions_seen, 1);
    assert_eq!(stats.cache_misses, 1);
    assert_eq!(stats.cache_puts, 1);
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_cache_hit_on_repeat() {
    let pipeline = make_cegis_pipeline();

    let mut func1 = build_add_test_function();
    let first = pipeline
        .run_cegis_superopt(&mut func1)
        .expect("first CEGIS run should execute");
    assert_eq!(first.cache_misses, 1);
    assert_eq!(first.cache_puts, 1);

    let mut func2 = build_add_test_function();
    let second = pipeline
        .run_cegis_superopt(&mut func2)
        .expect("second CEGIS run should execute");
    assert_eq!(second.functions_seen, 1);
    assert_eq!(second.cache_hits, 1);
    assert_eq!(second.cache_misses, 0);
}

#[test]
fn test_full_pipeline_with_cegis_flag() {
    let pipeline = make_cegis_pipeline();
    let (trust_ir_func, module) = build_add_trust_ir();
    let (lir_func, _) = trust_cg_lower::translate_function_with_license(
        &trust_ir_func,
        &module,
        &permit_unlicensed(),
    )
    .expect("trust_ir add function should translate");

    let obj_bytes = pipeline
        .compile_function(&lir_func)
        .expect("full pipeline should compile with the CEGIS flag enabled");

    assert!(
        !obj_bytes.is_empty(),
        "pipeline should produce non-empty object bytes"
    );
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_codegen_layer_a_mul_zero_i32_matches_hand_movz() {
    let source = build_layer_a_mul_zero_func("cegis_layer_a_i32_codegen", RegClass::Gpr32, false);
    let hand_optimized =
        build_layer_a_mul_zero_func("cegis_layer_a_i32_codegen", RegClass::Gpr32, true);

    assert_cegis_codegen_matches_hand_optimized(
        "Layer A i32 MulRR-by-zero",
        source,
        hand_optimized,
        |stats| {
            assert!(
                stats.layer_a_committed >= 1,
                "Layer A i32 case should commit, got {stats:?}"
            );
            assert_eq!(stats.layer_b_committed, 0);
        },
    );
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_codegen_layer_b_movz_add_small_imm_matches_hand_addri() {
    let source = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm7_codegen",
        RegClass::Gpr32,
        3,
        7,
        false,
    );
    let hand_optimized = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm7_codegen",
        RegClass::Gpr32,
        3,
        7,
        true,
    );

    assert_cegis_codegen_matches_hand_optimized(
        "Layer B i32 Movz+AddRR imm7",
        source,
        hand_optimized,
        |stats| {
            assert!(
                stats.layer_b_committed >= 1,
                "Layer B imm7 case should commit, got {stats:?}"
            );
            assert_eq!(stats.layer_a_committed, 0);
        },
    );
}

#[cfg(feature = "verify")]
#[test]
fn test_cegis_codegen_layer_b_movz_add_max_imm12_matches_hand_addri() {
    let source = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm4095_codegen",
        RegClass::Gpr32,
        11,
        4095,
        false,
    );
    let hand_optimized = build_layer_b_movz_add_func(
        "cegis_layer_b_i32_imm4095_codegen",
        RegClass::Gpr32,
        11,
        4095,
        true,
    );

    assert_cegis_codegen_matches_hand_optimized(
        "Layer B i32 Movz+AddRR imm4095",
        source,
        hand_optimized,
        |stats| {
            assert!(
                stats.layer_b_committed >= 1,
                "Layer B imm4095 case should commit, got {stats:?}"
            );
            assert_eq!(stats.layer_a_committed, 0);
        },
    );
}

// ---------------------------------------------------------------------------
// Native end-to-end rows: operand-0 readers of a CEGIS constant
// ---------------------------------------------------------------------------

/// A 64-bit mask built by a constant expression. At O2 the constant folder
/// rewrites it in place into `Movz #0x5555` plus three `Movk`s, so one vreg
/// holds the mask with no copies left in the arena. The mask is ANDed, and
/// also stored (`StrRI mask, ...`) or compared (`CmpRR mask, y`): in both
/// the second reader reads the mask at operand 0. `cegis_mask_only` is the
/// control, a window CEGIS may and does fuse into `AND #imm`.
#[cfg(feature = "verify")]
const CEGIS_OPERAND_ZERO_TIR: &str = r#"; TrustIr text format v1
module "cegis_operand_zero_readers"

functy.0 = (u64, ptr) -> (u64)

functy.1 = (u64, u64) -> (u64)

functy.2 = (u64) -> (u64)

fn @cegis_mask_store(functy.0) {
bb0(%0: u64, %1: ptr):
    %2 = const u64 1431655765
    %3 = const u64 32
    %4 = shl u64 %2, %3
    %5 = or u64 %4, %2
    %6 = and u64 %0, %5
    store u64 %5, ptr %1
    ret %6
}

fn @cegis_mask_compare(functy.1) {
bb0(%0: u64, %1: u64):
    %2 = const u64 1431655765
    %3 = const u64 32
    %4 = shl u64 %2, %3
    %5 = or u64 %4, %2
    %6 = and u64 %0, %5
    %7 = icmp eq u64 %5, %1
    %8 = select u64 %7, %6, %0
    ret %8
}

fn @cegis_mask_only(functy.2) {
bb0(%0: u64):
    %2 = const u64 1431655765
    %3 = const u64 32
    %4 = shl u64 %2, %3
    %5 = or u64 %4, %2
    %6 = and u64 %0, %5
    ret %6
}
"#;

/// The oracle: C computes every expected value itself. Each function is
/// called through an eight-argument pointer whose unused arguments are a
/// poison value, so `x2`-`x7` never hold a leftover of an earlier call (the
/// mask, say) that could make a read of an undefined register look right.
#[cfg(feature = "verify")]
const CEGIS_OPERAND_ZERO_DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>

uint64_t cegis_mask_store(uint64_t x, uint64_t *slot);
uint64_t cegis_mask_compare(uint64_t x, uint64_t y);
uint64_t cegis_mask_only(uint64_t x);

typedef uint64_t (*call8)(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,
                          uint64_t, uint64_t);

#define MASK 0x5555555555555555ull
#define POISON 0xBADC0FFEE0DDF00Dull

static uint64_t call2(call8 fn, uint64_t a, uint64_t b) {
    return fn(a, b, POISON, POISON, POISON, POISON, POISON, POISON);
}

int main(void) {
    static const uint64_t xs[] = {
        0, 1, 0xFFFFFFFFFFFFFFFFull, MASK, ~MASK, 0x0123456789ABCDEFull,
        0x8000000000000001ull,
    };
    int bad = 0;
    for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
        uint64_t x = xs[i];
        uint64_t slot = 0xDEADBEEFDEADBEEFull;
        uint64_t got = call2((call8)cegis_mask_store, x, (uint64_t)(uintptr_t)&slot);
        if (got != (x & MASK) || slot != MASK) {
            printf("cegis_mask_store(%#llx) = %#llx, stored %#llx; want %#llx, stored %#llx\n",
                   (unsigned long long)x, (unsigned long long)got,
                   (unsigned long long)slot, (unsigned long long)(x & MASK),
                   (unsigned long long)MASK);
            bad = 1;
        }
        const uint64_t ys[] = {MASK, x, 0};
        for (unsigned j = 0; j < 3; j++) {
            uint64_t want = ys[j] == MASK ? (x & MASK) : x;
            got = call2((call8)cegis_mask_compare, x, ys[j]);
            if (got != want) {
                printf("cegis_mask_compare(%#llx, %#llx) = %#llx; want %#llx\n",
                       (unsigned long long)x, (unsigned long long)ys[j],
                       (unsigned long long)got, (unsigned long long)want);
                bad = 1;
            }
        }
        got = call2((call8)cegis_mask_only, x, POISON);
        if (got != (x & MASK)) {
            printf("cegis_mask_only(%#llx) = %#llx; want %#llx\n", (unsigned long long)x,
                   (unsigned long long)got, (unsigned long long)(x & MASK));
            bad = 1;
        }
    }
    puts(bad ? "MISMATCH" : "ok");
    return bad;
}
"#;

/// Compile `module` for the host's native AArch64 triple at `opt_level` with
/// CEGIS on, as `--cegis-superopt=<secs>` does.
#[cfg(feature = "verify")]
fn compile_native_with_cegis(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    use trust_cg_codegen::target::TargetSpec;
    use trust_cg_codegen::{Compiler, CompilerConfig};

    let triple = if cfg!(all(
        target_arch = "aarch64",
        target_os = "linux",
        target_env = "gnu"
    )) {
        "aarch64-unknown-linux-gnu"
    } else {
        "aarch64-apple-darwin"
    };
    let mut module = module.clone();
    module.target_info = Some(trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            cegis_superopt_budget_sec: Some(30),
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).expect("native triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    .expect("CEGIS-enabled native compile")
    .object_code
}

/// Search revision 2 counted reads as "every operand after operand 0". For
/// `cegis_mask_store` and `cegis_mask_compare` the AND was then the mask's
/// only read, so Layer C rewrote it to `AND #0x5555555555555555` and spliced
/// the `Movz`/`Movk` chain out while the store and the compare still read the
/// mask register: the store wrote, and the compare tested, whatever that
/// register held. The row links both builds against a C oracle and runs them
/// on this host; the CEGIS build must also differ from the reference (the
/// control's fusion), so CEGIS demonstrably ran.
#[cfg(feature = "verify")]
#[test]
fn cegis_native_operand_zero_readers_keep_the_materialized_mask() {
    let module = trust_ir::parser::parse_module(CEGIS_OPERAND_ZERO_TIR).expect("parse");
    let reference = aarch64_native::compile(&module, OptLevel::O2);
    let cegis = compile_native_with_cegis(&module, OptLevel::O2);
    assert_ne!(
        reference, cegis,
        "CEGIS must fuse the control function's mask into an AND immediate"
    );
    for (tag, object) in [("reference", &reference), ("cegis", &cegis)] {
        aarch64_native::link_run(
            &format!("cegis-operand-zero-readers-{tag}"),
            object,
            CEGIS_OPERAND_ZERO_DRIVER,
        );
    }
}

/// The CEGIS cache has no MAC and its codec checks only the format. An entry
/// whose recorded `AndRI` mask is overwritten in place (0x5555555555555555 to
/// 0x3333333333333333, still a logical immediate, so the entry still decodes)
/// was replayed as recorded: `cegis_mask_only(-1)` returned
/// 0x3333333333333333. Replay now applies only the body the matcher rebuilds,
/// so the tampered entry is stale: the function is searched again, the object
/// is byte-identical to the honest one and computes the oracle's results,
/// and the entry is rewritten. The row uses its own private cache root.
#[cfg(feature = "verify")]
#[test]
fn cegis_native_tampered_cache_entry_is_refused_and_refreshed() {
    use std::path::{Path, PathBuf};
    use trust_cg_verify::cegis_pass::MachOperandBlob;
    use trust_cg_verify::{CEGIS_CACHE_ENV, CegisCacheEntry, RewriteLayer};

    const MASK: i64 = 0x5555_5555_5555_5555;
    const TAMPERED: i64 = 0x3333_3333_3333_3333;

    let scratch = tempfile::tempdir().expect("private scratch directory");
    let root = scratch.path().join("cegis-cache");
    let root_env = root.to_str().expect("UTF-8 temp path").to_string();
    let module = trust_ir::parser::parse_module(CEGIS_OPERAND_ZERO_TIR).expect("parse");
    let compile = || {
        trust_cg_process_env::with_env_overrides(&[(CEGIS_CACHE_ENV, root_env.as_str())], || {
            compile_native_with_cegis(&module, OptLevel::O2)
        })
    };
    let entries = |root: &Path| -> Vec<(PathBuf, CegisCacheEntry)> {
        let mut found = Vec::new();
        for shard in std::fs::read_dir(root).expect("the compile populated the cache root") {
            let shard = shard.expect("shard").path();
            if !shard.is_dir() {
                continue;
            }
            for file in std::fs::read_dir(&shard).expect("read shard") {
                let path = file.expect("entry").path();
                let bytes = std::fs::read(&path).expect("read entry");
                if let Some(entry) = CegisCacheEntry::decode(&bytes) {
                    found.push((path, entry));
                }
            }
        }
        found
    };
    // The immediate of an entry's single Layer C `AndRI` rewrite, if any.
    let and_imm = |entry: &CegisCacheEntry| -> Option<i64> {
        let [rewrite] = entry.proven_rewrites.as_slice() else {
            return None;
        };
        let [body] = rewrite.replacement.as_slice() else {
            return None;
        };
        match (rewrite.layer, body.opcode.as_str(), body.operands.last()) {
            (RewriteLayer::C, "AndRI", Some(MachOperandBlob::Imm(imm))) => Some(*imm),
            _ => None,
        }
    };

    let honest = compile();
    let fused: Vec<(PathBuf, i64)> = entries(&root)
        .into_iter()
        .filter_map(|(path, entry)| and_imm(&entry).map(|imm| (path, imm)))
        .collect();
    assert_eq!(
        fused.len(),
        1,
        "one entry records the AndRI fusion: {fused:?}"
    );
    let (path, imm) = fused[0].clone();
    assert_eq!(imm, MASK);

    // Overwrite the recorded immediate in place, as anyone able to write the
    // cache root could.
    let mut bytes = std::fs::read(&path).expect("read entry");
    let at: Vec<usize> = bytes
        .windows(8)
        .enumerate()
        .filter(|(_, window)| *window == MASK.to_le_bytes())
        .map(|(offset, _)| offset)
        .collect();
    assert_eq!(at.len(), 1, "the mask is recorded once");
    bytes[at[0]..at[0] + 8].copy_from_slice(&TAMPERED.to_le_bytes());
    std::fs::write(&path, &bytes).expect("tamper entry");
    let tampered = CegisCacheEntry::decode(&bytes).expect("the tampered entry still decodes");
    assert_eq!(and_imm(&tampered), Some(TAMPERED));

    let rerun = compile();
    assert!(
        rerun == honest,
        "the tampered body must not reach the object"
    );
    aarch64_native::link_run(
        "cegis-tampered-cache-entry",
        &rerun,
        CEGIS_OPERAND_ZERO_DRIVER,
    );
    let refreshed = CegisCacheEntry::decode(&std::fs::read(&path).expect("read entry"))
        .expect("the entry decodes after the rerun");
    assert_eq!(
        and_imm(&refreshed),
        Some(MASK),
        "the fresh search rewrites the entry"
    );

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = |path: &Path| {
            std::fs::metadata(path)
                .expect("metadata")
                .permissions()
                .mode()
                & 0o7777
        };
        assert_eq!(mode(&root), 0o700, "the cache creates a private root");
        assert_eq!(mode(&path), 0o600, "and private entries");
    }
}

/// A Movz-fed add whose constant has no `ADD #imm12` encoding: instruction
/// selection keeps `Movz #5000` and an `AddRR`, once with the constant also
/// compared at operand 0. Search revision 2's Layer B accepted any `imm16`
/// and emitted `AddRI #5000`, which the encoder rejects, so the compile
/// failed; the matcher now admits only encodable immediates and leaves both
/// windows alone.
#[cfg(feature = "verify")]
const CEGIS_WIDE_ADD_TIR: &str = r#"; TrustIr text format v1
module "cegis_wide_add"

functy.0 = (u32) -> (u32)

functy.1 = (u32, u32) -> (u32)

fn @cegis_wide_add(functy.0) {
bb0(%0: u32):
    %2 = const u32 5000
    %3 = add u32 %0, %2
    ret %3
}

fn @cegis_wide_add_compare(functy.1) {
bb0(%0: u32, %1: u32):
    %2 = const u32 5000
    %3 = add u32 %0, %2
    %4 = icmp eq u32 %2, %1
    %5 = select u32 %4, %3, %0
    ret %5
}
"#;

#[cfg(feature = "verify")]
const CEGIS_WIDE_ADD_DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>

uint32_t cegis_wide_add(uint32_t x);
uint32_t cegis_wide_add_compare(uint32_t x, uint32_t y);

int main(void) {
    static const uint32_t xs[] = {0, 1, 4999, 5000, 0xFFFFFFFFu, 0x80000000u};
    int bad = 0;
    for (unsigned i = 0; i < sizeof xs / sizeof xs[0]; i++) {
        uint32_t x = xs[i];
        uint32_t got = cegis_wide_add(x);
        if (got != x + 5000u) {
            printf("cegis_wide_add(%#x) = %#x; want %#x\n", x, got, x + 5000u);
            bad = 1;
        }
        const uint32_t ys[] = {5000u, x, 0};
        for (unsigned j = 0; j < 3; j++) {
            uint32_t want = ys[j] == 5000u ? x + 5000u : x;
            got = cegis_wide_add_compare(x, ys[j]);
            if (got != want) {
                printf("cegis_wide_add_compare(%#x, %#x) = %#x; want %#x\n", x, ys[j], got, want);
                bad = 1;
            }
        }
    }
    puts(bad ? "MISMATCH" : "ok");
    return bad;
}
"#;

#[cfg(feature = "verify")]
#[test]
fn cegis_native_movz_fed_add_keeps_an_unencodable_constant() {
    let module = trust_ir::parser::parse_module(CEGIS_WIDE_ADD_TIR).expect("parse");
    let reference = aarch64_native::compile(&module, OptLevel::O2);
    let cegis = compile_native_with_cegis(&module, OptLevel::O2);
    assert_eq!(
        reference, cegis,
        "no Layer B window here has an encodable replacement"
    );
    aarch64_native::link_run("cegis-wide-add", &cegis, CEGIS_WIDE_ADD_DRIVER);
}

/// A CEGIS-enabled compile whose verifier cannot run because AY is refused
/// names that refusal. X-HOST-P13's closure audit (2026-10-03): under umask
/// 0002 a repository script left `<cache>/trust-cg` `0775`, AY's identity rule
/// then admitted no AY, and this suite's solver-backed rows failed
/// `CegisIncomplete { completion: VerifierError }` with nothing about AY. For
/// a build that records the toolchain AY the refusal now carries the
/// `TCG-AY-IDENTITY-*` refusal (the directory, its mode and the remedy); a
/// build that records no AY carries none. The directory is never changed.
/// Runs in a child test process whose `XDG_CACHE_HOME` holds such a
/// directory.
#[cfg(all(feature = "verify", unix))]
#[test]
fn cegis_refusal_names_an_ay_refused_beneath_a_group_writable_cache() {
    use std::os::unix::fs::PermissionsExt;
    const CHILD: &str = "CEGIS_OPEN_CACHE_CHILD";
    const NAME: &str = "cegis_refusal_names_an_ay_refused_beneath_a_group_writable_cache";
    let mode = |path: &std::path::Path| {
        std::fs::symlink_metadata(path)
            .unwrap()
            .permissions()
            .mode()
            & 0o7777
    };
    let Some(cache) = std::env::var_os(CHILD).map(std::path::PathBuf::from) else {
        let base = tempfile::tempdir().unwrap();
        std::fs::set_permissions(base.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
        let cache = base.path().canonicalize().unwrap();
        let trust_cg = cache.join("trust-cg");
        std::fs::create_dir(&trust_cg).unwrap();
        std::fs::set_permissions(&trust_cg, std::fs::Permissions::from_mode(0o775)).unwrap();
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
            .env(CHILD, &cache)
            .env("XDG_CACHE_HOME", &cache)
            // The toolchain route, and the CEGIS cache under the same base.
            .env_remove("AY_SOLVER_PATH")
            .env_remove(trust_cg_verify::CEGIS_CACHE_ENV)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        for line in stdout
            .lines()
            .filter(|line| line.contains("OPEN_CACHE_CEGIS_REFUSAL"))
        {
            println!(
                "{}",
                &line[line.find("OPEN_CACHE_CEGIS_REFUSAL").unwrap_or(0)..]
            );
        }
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "child: {}\n{stdout}\n{stderr}",
            output.status
        );
        assert_eq!(
            mode(&trust_cg),
            0o775,
            "an existing directory is never changed"
        );
        return;
    };
    let trust_cg = cache.join("trust-cg");
    let recorded = trust_cg_verify::ay_identity::recorded_toolchain_ay_identity().is_ok();
    let mut func = build_layer_a_mul_zero_func("cegis_open_cache", RegClass::Gpr32, false);
    match make_cegis_pipeline().compile_ir_function(&mut func) {
        Err(error @ trust_cg_codegen::pipeline::PipelineError::CegisIncomplete { .. }) => {
            let message = error.to_string();
            println!("OPEN_CACHE_CEGIS_REFUSAL {message}");
            let trust_cg_codegen::pipeline::PipelineError::CegisIncomplete { ay_refusal, .. } =
                &error
            else {
                unreachable!()
            };
            if recorded {
                let note = ay_refusal.as_deref().expect("the AY refusal");
                for needed in [
                    "no AY is admitted in this process".to_owned(),
                    "[TCG-AY-IDENTITY-UNMATERIALIZED]".to_owned(),
                    format!("{} has mode 0775", trust_cg.display()),
                    format!("`chmod go-w {}`", trust_cg.display()),
                ] {
                    assert!(note.contains(&needed), "{needed:?} missing from {note}");
                }
                assert!(message.ends_with(&format!("; {note}")), "{message}");
            } else {
                assert_eq!(ay_refusal, &None, "{message}");
            }
        }
        // Only a build that records no AY can complete the search here: it
        // admits no AY anywhere, so nothing is refused.
        other => assert!(
            !recorded,
            "an AY refused beneath the open cache must stop the CEGIS search: {:?}",
            other.map(|object| object.len())
        ),
    }
    assert_eq!(
        mode(&trust_cg),
        0o775,
        "an existing directory is never changed"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
