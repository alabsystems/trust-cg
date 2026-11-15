// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use std::collections::HashSet;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_ir::Module;

#[test]
fn optimized_original_masked_bounds_uses_only_emitted_frame_effects() {
    let module: Module = serde_json::from_str(include_str!(
        "../../trust-cg-verify/tests/fixtures/const_references/bounds_unwind-O1-module0.trust-ir.json"
    )).unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let (original, context) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut source = original.clone();
        if level != OptLevel::O0 {
            let stats = trust_cg_opt::lir_unsigned_range::simplify_function(&mut source);
            println!("RANGE {level:?}: {stats:?}");
        }
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: level,
            verify: false,
            ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
        });
        let (machine, metrics) = pipeline
            .prepare_function_with_metrics(&source, Some(&context))
            .unwrap();
        let emitted: HashSet<_> = machine
            .block_order
            .iter()
            .flat_map(|block| machine.block(*block).insts.iter().copied())
            .collect();
        let layout = metrics.frame_layout.unwrap();
        let live_call = emitted.iter().any(|id| machine.inst(*id).is_call());
        assert!(
            machine.insts.iter().any(|inst| inst.is_call()),
            "retained call exercises the arena/layout distinction"
        );
        // The range fold proves the masked index in bounds, and from O1 on
        // CfgSimplify (275e8973a) removes the panic arm it made unreachable, so
        // the call survives only in the arena. O0 keeps it live.
        if level != OptLevel::O0 {
            assert!(!live_call, "{level:?}");
            assert_eq!(layout.total_frame_size, 0);
            assert!(layout.is_leaf && !layout.uses_frame_pointer);
            if level != OptLevel::O1 {
                assert_eq!(emitted.len(), 3);
                assert!(emitted.iter().all(|id| matches!(
                    machine.inst(*id).opcode,
                    trust_cg_ir::AArch64Opcode::AndRI
                        | trust_cg_ir::AArch64Opcode::StrRO
                        | trust_cg_ir::AArch64Opcode::Ret
                )));
            }
        } else {
            assert!(live_call);
            assert!(!layout.is_leaf);
            assert!(layout.total_frame_size >= 16);
        }
    }
}

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[test]
fn original_masked_bounds_native_abi_and_arena_at_every_level() {
    use std::{fs, process::Command};
    use trust_cg_codegen::{Compiler, CompilerConfig, target::TargetSpec};
    let module: Module = serde_json::from_str(include_str!(
        "../../trust-cg-verify/tests/fixtures/const_references/bounds_unwind-O1-module0.trust-ir.json"
    )).unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let panic = module
        .functions
        .iter()
        .find(|function| function.blocks.is_empty())
        .unwrap();
    let directory = crate::fresh_dir::create("trust-cg-live-frame-");
    let source = directory.join("runner.c");
    fs::write(
        &source,
        format!(
            r#"#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
extern void checked_bounds_unwind(uint64_t *, uint64_t, uint64_t);
void unexpected_panic(void) __asm__("{}");
void unexpected_panic(void) {{ _Exit(90); }}
int main(void) {{
    const uint64_t indices[] = {{0,1,7,8,UINT64_MAX,UINT64_C(1)<<32,UINT64_C(1)<<63}};
    uint64_t seed=0x123456789abcdefULL;
    for(unsigned row=0;row<1025;row++) {{
        uint64_t arena[16], before[16];
        unsigned start=1+row%8;
        for(unsigned i=0;i<16;i++) arena[i]=before[i]=UINT64_C(0xa5a5a5a5a5a5a5a5)^(row*16+i);
        seed^=seed<<13; seed^=seed>>7; seed^=seed<<17;
        uint64_t index=row<7?indices[row]:seed;
        uint64_t value=row==0?0:row==1?UINT64_MAX:seed^UINT64_C(0xfedcba9876543210);
        checked_bounds_unwind(arena+start,index,value);
        for(unsigned i=0;i<16;i++) {{
            uint64_t expected=i==start+(index&7)?value:before[i];
            if(arena[i]!=expected) return 12;
        }}
    }}
    puts("LIVE_FRAME_NATIVE calls=1025");
    return 0;
}}
"#,
            panic.name
        ),
    )
    .unwrap();
    let assembly = directory.join("abi.S");
    fs::write(&assembly, include_str!("fixtures/live_frame/abi.S")).unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let output = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                panic_unwind: true,
                ..Default::default()
            },
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .unwrap();
        let object = directory.join(format!("masked-{level:?}.o"));
        fs::write(&object, output.object_code).unwrap();
        let binary = directory.join(format!("runner-{level:?}"));
        let linked = process::command_output_with_timeout(
            Command::new("cc")
                .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                .arg(&source)
                .arg(&assembly)
                .arg(&object)
                .args(["-Wl,-z,noexecstack", "-o"])
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        fs::write(
            directory.join(format!("link-{level:?}.log")),
            &linked.output.stderr,
        )
        .unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let ran = process::command_output_with_timeout(
            &mut Command::new(&binary),
            process::codegen_run_timeout(),
        )
        .unwrap();
        fs::write(
            directory.join(format!("run-{level:?}.log")),
            &ran.output.stdout,
        )
        .unwrap();
        assert!(!ran.timed_out && ran.output.status.success());
        assert_eq!(
            String::from_utf8_lossy(&ran.output.stdout).trim(),
            "LIVE_FRAME_NATIVE calls=1025"
        );
    }
    println!("LIVE_FRAME_NATIVE_ARTIFACTS={}", directory.display());
    println!("LIVE_FRAME_NATIVE_CALLS=4100");
}

/// A native callee observes SP on every visit to the caller's entry block.
/// Re-entering that block must not repeat frame allocation or stack probing.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[test]
fn entry_backedges_keep_native_stack_and_probed_slot_stable() {
    use std::{fs, process::Command};
    use trust_cg_codegen::{Compiler, CompilerConfig, target::TargetSpec};
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    let mut builder = ModuleBuilder::new_with_target_info(
        "entry_frame",
        trust_ir::TargetInfo {
            triple: "aarch64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![], vec![Ty::I64]);
    let tick = builder.declare_function("entry_tick", signature);
    let touch_signature = builder.add_func_type(vec![Ty::Ptr], vec![]);
    let touch = builder.declare_function("entry_touch", touch_signature);
    let byte = builder.add_type(Ty::I8);
    for (name, probed) in [("entry_small", false), ("entry_probed", true)] {
        let mut function = builder.function(name, signature);
        let entry = function.create_block();
        let exit = function.create_block();
        function.switch_to_block(entry);
        if probed {
            let slot = function.alloca_aligned(Ty::Array(byte, 1 << 20), 16);
            function.call_void(touch, vec![slot]);
        }
        let remaining = function.call(tick, vec![]);
        let zero = function.iconst(Ty::I64, 0);
        let again = function.icmp(ICmpOp::Ne, Ty::I64, remaining, zero);
        function.condbr(again, entry, vec![], exit, vec![]);
        function.switch_to_block(exit);
        let result = function.iconst(Ty::I64, 0x12345678);
        function.ret(vec![result]);
        function.build();
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "entry-frame module: {errors:?}");
    let directory = crate::fresh_dir::create("trust-cg-entry-frame-");
    let source = directory.join("driver.c");
    fs::write(
        &source,
        r#"#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern int64_t entry_small(void), entry_probed(void), entry_bad(void);
static uintptr_t expected_sp, expected_slot;
static uint64_t remaining, calls, touches;
static int probed;

/* The assembly tail-call passes SP before any C callee frame is allocated. */
int64_t entry_checked_tick(uintptr_t sp) {
    if (sp & 15) { fputs("ENTRY_STACK_UNALIGNED\n", stderr); _Exit(82); }
    if (calls && sp != expected_sp) {
        fputs("ENTRY_STACK_CHANGED\n", stderr);
        _Exit(83);
    }
    expected_sp = sp;
    ++calls;
    if (touches != (probed ? calls : 0)) _Exit(84);
    if (!remaining) return 0;
    --remaining;
    return 1;
}

void entry_touch(volatile unsigned char *slot) {
    if (touches && (uintptr_t)slot != expected_slot) _Exit(85);
    expected_slot = (uintptr_t)slot;
    ++touches;
    slot[0] = 0xa5;
    slot[(1 << 20) - 1] = 0x5a;
}

static void reset(uint64_t count, int large) {
    remaining = count;
    calls = touches = 0;
    expected_sp = expected_slot = 0;
    probed = large;
}

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "bad")) {
        reset(2, 0);
        (void)entry_bad();
        return 86; /* The independently injected frame error must be caught. */
    }
    const uint64_t counts[] = {0, 1, 2, 7, 31, 4096};
    uint64_t observations = 0;
    for (int large = 0; large != 2; ++large) {
        for (unsigned i = 0; i != sizeof counts / sizeof *counts; ++i) {
            reset(counts[i], large);
            int64_t result = large ? entry_probed() : entry_small();
            if (result != INT64_C(0x12345678) || remaining || calls != counts[i] + 1)
                return 87;
            observations += calls;
        }
    }
    if (observations != 8286) return 88;
    puts("ENTRY_FRAME_NATIVE calls=12 stack_observations=8286");
    return 0;
}
"#,
    )
    .unwrap();
    let assembly = directory.join("observer.S");
    fs::write(
        &assembly,
        r#".text
.p2align 2
.global entry_tick
.type entry_tick,%function
entry_tick:
    mov x0,sp
    b entry_checked_tick
.size entry_tick,.-entry_tick

/* Negative control: each backedge deliberately allocates another frame. */
.p2align 2
.global entry_bad
.type entry_bad,%function
entry_bad:
    stp x29,x30,[sp,#-16]!
    mov x29,sp
    bl entry_tick
    cbnz x0,entry_bad
    ldp x29,x30,[sp],#16
    ret
.size entry_bad,.-entry_bad
.section .note.GNU-stack,"",%progbits
"#,
    )
    .unwrap();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let output = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: level,
                ..Default::default()
            },
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .unwrap_or_else(|error| panic!("{level:?}: {error:?}"));
        let object = directory.join(format!("entry-{level:?}.o"));
        fs::write(&object, output.object_code).unwrap();
        let binary = directory.join(format!("entry-{level:?}"));
        let linked = process::command_output_with_timeout(
            Command::new("cc")
                .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                .arg(&source)
                .arg(&assembly)
                .arg(&object)
                .args(["-Wl,-z,noexecstack", "-o"])
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{level:?} link: {}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        for bad in [true, false] {
            let mut command = Command::new(&binary);
            if bad {
                command.arg("bad");
            }
            let ran =
                process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
                    .unwrap();
            fs::write(
                directory.join(format!("run-{level:?}-bad-{bad}.stderr")),
                &ran.output.stderr,
            )
            .unwrap();
            fs::write(
                directory.join(format!("run-{level:?}-bad-{bad}.stdout")),
                &ran.output.stdout,
            )
            .unwrap();
            assert!(!ran.timed_out, "{level:?}, bad={bad}: timed out");
            if bad {
                assert_eq!(ran.output.status.code(), Some(83));
                assert_eq!(ran.output.stderr, b"ENTRY_STACK_CHANGED\n");
            } else {
                assert!(
                    ran.output.status.success(),
                    "{level:?}: {:?}: {}",
                    ran.output.status,
                    String::from_utf8_lossy(&ran.output.stderr)
                );
                assert_eq!(
                    ran.output.stdout,
                    b"ENTRY_FRAME_NATIVE calls=12 stack_observations=8286\n"
                );
            }
        }
    }
    println!("ENTRY_FRAME_NATIVE_ARTIFACTS={}", directory.display());
    println!("ENTRY_FRAME_NATIVE_CALLS=48 STACK_OBSERVATIONS=33144 NEGATIVE_CONTROLS=4");
}

#[path = "common/native_host.rs"]
mod native_host;

/// Leaves whose LIR source the verifier's source-bound frame owner never
/// judges: multiply by a constant (the refusal control of
/// `test_aarch64_parallel_and_serial_multi_function_byte_identical`), a load
/// and a store. Each body contains an ADD or SUB, which the zero-storage
/// policy frames only for that owner.
fn unowned_leaf_module() -> Module {
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;
    let mut mb = ModuleBuilder::new("unowned_leaf_frames");
    for (idx, name) in ["add_fn", "mul_sub_fn", "add_double_fn"].iter().enumerate() {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function(*name, ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let k = fb.iconst(Ty::I64, (idx as i128) + 3);
        let sum = fb.add(Ty::I64, a, b);
        let product = fb.mul(Ty::I64, sum, k);
        let result = fb.sub(Ty::I64, product, a);
        fb.ret(vec![result]);
        fb.build();
    }
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("load_add", ty);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let loaded = fb.load(Ty::I64, pointer);
    let sum = fb.add(Ty::I64, loaded, x);
    fb.ret(vec![sum]);
    fb.build();
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![]);
    let mut fb = mb.function("store_sub", ty);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::I64, 1);
    let difference = fb.sub(Ty::I64, x, one);
    fb.store(Ty::I64, pointer, difference);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

/// An affine leaf the owner does judge: ELF keeps its envelope.
fn owned_leaf_module() -> Module {
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;
    let mut mb = ModuleBuilder::new("owned_leaf_frame");
    let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("add_pair", ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let sum = fb.add(Ty::I64, a, b);
    fb.ret(vec![sum]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

fn object_for(module: &Module, triple: &str, level: OptLevel) -> Vec<u8> {
    use trust_cg_codegen::{Compiler, CompilerConfig, target::TargetSpec};
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: level,
            ..Default::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("{triple} {level:?}: {error}"))
    .object_code
}

const STP_FP_LR_PRE16: u32 = 0xa9bf_7bfd; // stp x29, x30, [sp, #-16]!
const MOV_FP_SP: u32 = 0x9100_03fd; // mov x29, sp
const LDP_FP_LR_POST16: u32 = 0xa8c1_7bfd; // ldp x29, x30, [sp], #16
const RET: u32 = 0xd65f_03c0; // ret

/// Linux has no red zone, but a zero-storage leaf needs no frame record under
/// AAPCS64. The FP/LR envelope the ELF zero-storage policy keeps around ADD,
/// SUB and immediate-LSL bodies exists only for the verifier's source-bound
/// frame owner, so a leaf whose source that owner never judges is lowered
/// exactly as the red-zone Mach-O target lowers it. An affine leaf still keeps
/// the exact envelope on ELF (and is frameless on Mach-O).
#[test]
fn unowned_leaves_are_frameless_on_elf_and_owned_leaves_keep_the_envelope() {
    let unowned = unowned_leaf_module();
    let owned = owned_leaf_module();
    for (module, admitted) in [(&unowned, false), (&owned, true)] {
        for function in &module.functions {
            let (lir, _) = trust_cg_lower::translate_function_with_license(
                function,
                module,
                &permit_unlicensed(),
            )
            .unwrap();
            assert_eq!(
                trust_cg_verify::source_bound_frame::source_admits_frame_owner(&lir),
                admitted,
                "{}",
                function.name
            );
        }
    }
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let linux =
            native_host::text_words(&object_for(&unowned, "aarch64-unknown-linux-gnu", level));
        let darwin = native_host::text_words(&object_for(&unowned, "aarch64-apple-darwin", level));
        assert_eq!(
            linux, darwin,
            "{level:?}: ELF {linux:08x?} differs from Mach-O {darwin:08x?}"
        );
        assert!(
            !linux
                .iter()
                .any(|word| matches!(*word, STP_FP_LR_PRE16 | MOV_FP_SP | LDP_FP_LR_POST16)),
            "{level:?}: {linux:08x?}"
        );
        assert_eq!(linux.iter().filter(|word| **word == RET).count(), 5);
        // AAPCS64 (6.4.5.1) lets a process access only [SP, stack-base); Linux
        // has no red zone. A frameless leaf that never names SP can neither
        // move SP nor touch memory below it. The native test cannot observe
        // this: any conforming callee may allocate and write below the
        // caller's SP.
        assert!(
            !linux.iter().any(|word| names_stack_pointer(*word)),
            "{level:?}: {linux:08x?}"
        );

        let linux =
            native_host::text_words(&object_for(&owned, "aarch64-unknown-linux-gnu", level));
        let darwin = native_host::text_words(&object_for(&owned, "aarch64-apple-darwin", level));
        let (body, ret) = darwin.split_at(darwin.len() - 1);
        assert_eq!(ret, [RET], "{level:?}: {darwin:08x?}");
        let enveloped: Vec<u32> = [STP_FP_LR_PRE16, MOV_FP_SP]
            .into_iter()
            .chain(body.iter().copied())
            .chain([LDP_FP_LR_POST16, RET])
            .collect();
        assert_eq!(linux, enveloped, "{level:?}");
    }
}

/// Whether an A64 word names SP: a load/store base register (except the
/// PC-relative literal loads, which have no base), or an ADD/SUB immediate or
/// extended-register operand (where register 31 is SP unless it is the
/// flag-setting form's destination, which is ZR). Decoded from the ISA fields,
/// independently of the compiler's encoder.
fn names_stack_pointer(word: u32) -> bool {
    let rd = word & 31;
    let rn = (word >> 5) & 31;
    let sets_flags = (word >> 29) & 1 == 1;
    let load_store = (word >> 27) & 1 == 1 && (word >> 25) & 1 == 0;
    let literal = (word >> 27) & 0b111 == 0b011 && (word >> 24) & 1 == 0;
    let add_sub_immediate = (word >> 23) & 0x3f == 0x22;
    let add_sub_extended = (word >> 24) & 0x1f == 0b01011 && (word >> 21) & 1 == 1;
    (load_store && !literal && rn == 31)
        || ((add_sub_immediate || add_sub_extended) && (rn == 31 || (rd == 31 && !sets_flags)))
}

#[test]
fn stack_pointer_decoder_recognizes_every_form_it_rejects() {
    for (word, names) in [
        (STP_FP_LR_PRE16, true),
        (LDP_FP_LR_POST16, true),
        (MOV_FP_SP, true),
        (0xd100_43ff, true),  // sub sp, sp, #16
        (0xf940_03e0, true),  // ldr x0, [sp]
        (0xf900_0001, false), // str x1, [x0]
        (0xf940_0000, false), // ldr x0, [x0]
        (0x5800_03e0, false), // ldr x0, <literal> (imm19 bits in Rn's place)
        (0x8b01_0000, false), // add x0, x0, x1
        (0xf100_001f, false), // cmp x0, #0 (subs xzr, ...)
        (0xd65f_03c0, false), // ret
    ] {
        assert_eq!(names_stack_pointer(word), names, "{word:08x}");
    }
}

/// The frame decision uses the owner's own applicability check. A single-block
/// select leaf lies inside the owner's domain: ELF keeps its envelope at every
/// level and the owner binds the prepared machine function (construction only;
/// discharge needs the admitted AY/Clean proof tools). Its unjudged neighbour,
/// the same select feeding a multiply, is frameless on ELF, word for word the
/// Mach-O lowering.
#[test]
fn select_leaf_frame_owner_boundary_on_elf() {
    use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    let build = |multiply: bool| {
        let mut mb = ModuleBuilder::new("select_leaf_boundary");
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("select_leaf", ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let less = fb.icmp(ICmpOp::Slt, Ty::I64, a, b);
        let mut result = fb.select(Ty::I64, less, a, b);
        if multiply {
            let three = fb.iconst(Ty::I64, 3);
            result = fb.mul(Ty::I64, result, three);
        }
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert!(trust_ir_build::validate_module(&module).is_empty());
        module
    };
    for multiply in [false, true] {
        let module = build(multiply);
        let (lir, context) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_eq!(
            trust_cg_verify::source_bound_frame::source_admits_frame_owner(&lir),
            !multiply
        );
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let what = format!("multiply={multiply} {level:?}");
            let linux =
                native_host::text_words(&object_for(&module, "aarch64-unknown-linux-gnu", level));
            let darwin =
                native_host::text_words(&object_for(&module, "aarch64-apple-darwin", level));
            if multiply {
                assert_eq!(linux, darwin, "{what}");
                assert!(!linux.contains(&STP_FP_LR_PRE16), "{what}: {linux:08x?}");
                continue;
            }
            let (body, ret) = darwin.split_at(darwin.len() - 1);
            assert_eq!(ret, [RET], "{what}: {darwin:08x?}");
            let enveloped: Vec<u32> = [STP_FP_LR_PRE16, MOV_FP_SP]
                .into_iter()
                .chain(body.iter().copied())
                .chain([LDP_FP_LR_POST16, RET])
                .collect();
            assert_eq!(linux, enveloped, "{what}");
            let machine = Pipeline::new(PipelineConfig {
                opt_level: level,
                verify: false,
                ..PipelineConfig::for_target("aarch64-unknown-linux-gnu")
            })
            .prepare_function_with_metrics(&lir, Some(&context))
            .unwrap()
            .0;
            let bound = trust_cg_verify::source_bound_frame::source_bound_frame(&lir, &machine);
            assert!(bound.is_ok(), "{what}: {:?}", bound.err());
        }
    }
}

/// The unwind phase's C side. Phase 1 calls every leaf through `abi_call2`
/// with a value matrix. Phase 2 forks a traced child. The tracer stops the
/// child at `tcg_call_site` (the trampoline's BLR), records SP there and the
/// return address `tcg_call_site + 4`, steps into the leaf and then k more
/// instructions, and injects SIGUSR1. It does this for every k along the
/// leaf's executed path. The handler runs on an alternate signal stack, so the
/// kernel's signal frame does not overwrite the stack below the leaf's SP. It
/// unwinds with the libgcc unwinder and requires, for the caller of the
/// interrupted leaf, the CFA libgcc reports (the leaf's CFA) to equal the
/// recorded SP and the IP to equal the recorded return address. The
/// trampoline leaves a poison return address in the sixteen bytes just below
/// the call SP, written while that storage was still allocated. A rule that
/// reads LR from below the CFA therefore fails instead of finding a
/// coincidentally correct value.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
const UNOWNED_LEAF_DRIVER: &str = r#"#define _GNU_SOURCE
#include <dlfcn.h>
#include <elf.h>
#include <errno.h>
#include <link.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ptrace.h>
#include <sys/uio.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <ucontext.h>
#include <unistd.h>
#include <unwind.h>

extern uint64_t add_fn(uint64_t, uint64_t), mul_sub_fn(uint64_t, uint64_t);
extern uint64_t add_double_fn(uint64_t, uint64_t);
extern uint64_t load_add(const uint64_t *, uint64_t);
extern void store_sub(uint64_t *, uint64_t);
/* Exits 71 (SP or FP not restored), 72 (x19-x28) or 73 (d8-d15). */
extern uint64_t abi_call2(const void *fn, uint64_t a, uint64_t b);
extern const char tcg_call_site[];
void tcg_poison_ra(void) {}

static const struct { const char *name; const void *fn; } leaves[] = {
    {"add_fn", (const void *)add_fn}, {"mul_sub_fn", (const void *)mul_sub_fn},
    {"add_double_fn", (const void *)add_double_fn}, {"load_add", (const void *)load_add},
    {"store_sub", (const void *)store_sub},
};
#define LEAVES (sizeof leaves / sizeof *leaves)

static const uint64_t values[] = {
    0, 1, 2, 3, 5, UINT64_C(0x7fffffffffffffff), UINT64_C(0x8000000000000000),
    UINT64_MAX, UINT64_MAX - 1, UINT64_C(0x5555555555555555),
    UINT64_C(0x123456789abcdef0), UINT64_C(0xfedcba9876543210),
};
#define VALUES (sizeof values / sizeof *values)

/* Written by the tracer while the child is stopped. */
volatile uint64_t tcg_expected_cfa, tcg_expected_ra, tcg_advance;
static volatile unsigned current;
static unsigned checked[LEAVES];

struct walk { uintptr_t pc, cfa, ip; int leaf, caller, frames; };

/* libgcc reports on each frame the CFA of the frame it called. */
static _Unwind_Reason_Code walk_frame(struct _Unwind_Context *context, void *argument) {
    struct walk *walk = argument;
    if (++walk->frames > 32) return _URC_NORMAL_STOP;
    int before = 0;
    uintptr_t ip = _Unwind_GetIPInfo(context, &before);
    if (walk->leaf) {
        walk->caller = 1;
        walk->ip = ip;
        walk->cfa = _Unwind_GetCFA(context);
        return _URC_NORMAL_STOP;
    }
    if (before && ip == walk->pc) walk->leaf = 1;
    return _URC_NO_REASON;
}

static void fail(int code, uintptr_t pc) {
    dprintf(2, "UNWIND_FAIL fn=%s offset=%lu code=%d\n", leaves[current].name,
            (unsigned long)(pc - (uintptr_t)leaves[current].fn), code);
    _exit(code);
}

static void on_step(int number, siginfo_t *info, void *raw) {
    (void)number; (void)info;
    ucontext_t *context = raw;
    struct walk walk = {.pc = context->uc_mcontext.pc};
    _Unwind_Backtrace(walk_frame, &walk);
    if (!walk.leaf) fail(93, walk.pc);
    if (!walk.caller) fail(94, walk.pc);
    if (walk.cfa != tcg_expected_cfa) fail(91, walk.pc);
    if (walk.ip != tcg_expected_ra) fail(92, walk.pc);
    ++checked[current];
}

static uint64_t cell = 11;
static void call_leaf(unsigned index) {
    uint64_t a = index >= 3 ? (uintptr_t)&cell : 5;
    (void)abi_call2(leaves[index].fn, a, 7);
}

static int child(void) {
    stack_t alternate = {.ss_sp = malloc(1 << 16), .ss_size = 1 << 16};
    if (!alternate.ss_sp || sigaltstack(&alternate, NULL)) _exit(100);
    struct sigaction action;
    memset(&action, 0, sizeof action);
    action.sa_sigaction = on_step;
    action.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGUSR1, &action, NULL)) _exit(100);
    if (ptrace(PTRACE_TRACEME, 0, 0, 0)) _exit(101);
    raise(SIGSTOP);
    for (current = 0; current < LEAVES; ++current) {
        do call_leaf(current); while (!tcg_advance);
        tcg_advance = 0;
    }
    for (unsigned i = 0; i != LEAVES; ++i) printf("UNWIND %s pcs=%u\n", leaves[i].name, checked[i]);
    fflush(stdout);
    _exit(0);
}

static int stopped(pid_t pid) {
    int status;
    if (waitpid(pid, &status, 0) != pid) return 110;
    if (WIFEXITED(status)) return WEXITSTATUS(status) ? WEXITSTATUS(status) : 111;
    if (!WIFSTOPPED(status)) return 112;
    if (WSTOPSIG(status) != SIGTRAP) {
        dprintf(2, "TRACE_UNEXPECTED signal=%d\n", WSTOPSIG(status));
        kill(pid, SIGKILL);
        return 113;
    }
    return 0;
}

static int registers(pid_t pid, struct user_regs_struct *regs) {
    struct iovec vector = {regs, sizeof *regs};
    return ptrace(PTRACE_GETREGSET, pid, (void *)NT_PRSTATUS, &vector) ? 114 : 0;
}

static int poke(pid_t pid, volatile const void *address, uint64_t value) {
    return ptrace(PTRACE_POKEDATA, pid, (void *)address, (void *)value) ? 115 : 0;
}

static uint64_t saved_word;
static int arm(pid_t pid) {
    uintptr_t word = (uintptr_t)tcg_call_site & ~(uintptr_t)7;
    unsigned shift = ((uintptr_t)tcg_call_site & 7) * 8;
    errno = 0;
    long original = ptrace(PTRACE_PEEKTEXT, pid, (void *)word, 0);
    if (errno) return 116;
    saved_word = (uint64_t)original;
    uint64_t patched = (saved_word & ~(UINT64_C(0xffffffff) << shift))
                       | (UINT64_C(0xd4200000) << shift); /* brk #0 */
    return ptrace(PTRACE_POKETEXT, pid, (void *)word, (void *)patched) ? 117 : 0;
}

/* Continue to the call site, restore it, record the expected CFA and return
   address, and step through the BLR into the leaf. */
static int enter(pid_t pid, int signal, uintptr_t entry) {
    struct user_regs_struct regs;
    int code;
    if (ptrace(PTRACE_CONT, pid, 0, (void *)(uintptr_t)signal)) return 118;
    if ((code = stopped(pid)) || (code = registers(pid, &regs))) return code;
    if (regs.pc != (uintptr_t)tcg_call_site) return 119;
    uintptr_t word = (uintptr_t)tcg_call_site & ~(uintptr_t)7;
    if (ptrace(PTRACE_POKETEXT, pid, (void *)word, (void *)saved_word)) return 117;
    if ((code = poke(pid, &tcg_expected_cfa, regs.sp))
        || (code = poke(pid, &tcg_expected_ra, regs.pc + 4)))
        return code;
    if (ptrace(PTRACE_SINGLESTEP, pid, 0, 0)) return 120;
    if ((code = stopped(pid)) || (code = registers(pid, &regs))) return code;
    return regs.pc == entry ? 0 : 121;
}

static int step(pid_t pid, uintptr_t *pc) {
    struct user_regs_struct regs;
    int code;
    if (ptrace(PTRACE_SINGLESTEP, pid, 0, 0)) return 120;
    if ((code = stopped(pid)) || (code = registers(pid, &regs))) return code;
    *pc = regs.pc;
    return 0;
}

static int tracer(pid_t pid) {
    int code, status;
    /* The child stops itself with SIGSTOP once it is traced. */
    if (waitpid(pid, &status, 0) != pid || !WIFSTOPPED(status) || WSTOPSIG(status) != SIGSTOP)
        return 122;
    unsigned total = 0;
    int signal = 0;
    if ((code = arm(pid))) return code;
    for (unsigned i = 0; i != LEAVES; ++i) {
        Dl_info info;
        const ElfW(Sym) *symbol = NULL;
        if (!dladdr1(leaves[i].fn, &info, (void **)&symbol, RTLD_DL_SYMENT) || !symbol) return 123;
        uintptr_t entry = (uintptr_t)leaves[i].fn, end = entry + symbol->st_size;
        /* Discover the executed path. */
        if ((code = enter(pid, signal, entry))) return code;
        unsigned path = 0;
        uintptr_t pc = entry;
        while (pc >= entry && pc < end) {
            if (++path > 4096) return 124;
            if ((code = step(pid, &pc))) return code;
        }
        if (pc != (uintptr_t)tcg_call_site + 4) return 125;
        if ((code = arm(pid))) return code;
        signal = 0;
        for (unsigned k = 0; k != path; ++k) {
            if ((code = enter(pid, signal, entry))) return code;
            for (unsigned j = 0; j != k; ++j) {
                if ((code = step(pid, &pc))) return code;
                if (pc < entry || pc >= end) return 127;
            }
            if (k + 1 == path && (code = poke(pid, &tcg_advance, 1))) return code;
            if (!(k + 1 == path && i + 1 == LEAVES) && (code = arm(pid))) return code;
            signal = SIGUSR1;
        }
        printf("TRACE %s path=%u size=%lu\n", leaves[i].name, path,
               (unsigned long)symbol->st_size);
        total += path;
    }
    if (ptrace(PTRACE_CONT, pid, 0, (void *)(uintptr_t)signal)) return 118;
    if (waitpid(pid, &status, 0) != pid) return 110;
    if (!WIFEXITED(status)) return 126;
    if (WEXITSTATUS(status)) return WEXITSTATUS(status);
    printf("UNOWNED_LEAF_UNWIND pcs=%u\n", total);
    return 0;
}

int main(void) {
    unsigned calls = 0;
    for (unsigned i = 0; i != VALUES; ++i) {
        for (unsigned j = 0; j != VALUES; ++j) {
            uint64_t a = values[i], b = values[j], sum = a + b;
            if (abi_call2((const void *)add_fn, a, b) != sum * 3 - a) return 10;
            if (abi_call2((const void *)mul_sub_fn, a, b) != sum * 4 - a) return 11;
            if (abi_call2((const void *)add_double_fn, a, b) != sum * 5 - a) return 12;
            uint64_t slot = a;
            if (abi_call2((const void *)load_add, (uintptr_t)&slot, b) != sum) return 13;
            (void)abi_call2((const void *)store_sub, (uintptr_t)&slot, b);
            if (slot != b - 1) return 14;
            calls += 5;
        }
    }
    printf("UNOWNED_LEAF_NATIVE calls=%u\n", calls);
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) return 15;
    if (pid == 0) return child();
    return tracer(pid);
}
"#;

/// Sentinel callee-saved state around one call. AAPCS64 requires the callee
/// to preserve x19-x28, d8-d15, SP and FP; each class has its own exit code.
/// Memory below the caller's SP is not checked here: a conforming callee may
/// allocate stack and write there. The byte test pins that the frameless
/// leaves never name SP.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
const UNOWNED_LEAF_TRAMPOLINE: &str = r#".text
.p2align 2
.global abi_call2
.type abi_call2,%function
abi_call2:
    sub sp, sp, #160
    stp x19, x20, [sp, #0]
    stp x21, x22, [sp, #16]
    stp x23, x24, [sp, #32]
    stp x25, x26, [sp, #48]
    stp x27, x28, [sp, #64]
    stp x29, x30, [sp, #80]
    stp d8, d9, [sp, #96]
    stp d10, d11, [sp, #112]
    stp d12, d13, [sp, #128]
    stp d14, d15, [sp, #144]
    mov x29, sp
    .irp reg,19,20,21,22,23,24,25,26,27,28
    mov x\reg, #\reg
    .endr
    .irp reg,8,9,10,11,12,13,14,15
    mov x9, #\reg
    fmov d\reg, x9
    .endr
    // Poison return address just below the call SP, written while allocated.
    adrp x9, tcg_poison_ra
    add x9, x9, :lo12:tcg_poison_ra
    sub sp, sp, #16
    stp x9, x9, [sp]
    add sp, sp, #16
    mov x16, x0
    mov x0, x1
    mov x1, x2
.global tcg_call_site
tcg_call_site:
    blr x16
    mov x9, sp
    cmp x9, x29
    b.ne .Lsp_fail
    .irp reg,19,20,21,22,23,24,25,26,27,28
    cmp x\reg, #\reg
    b.ne .Lgpr_fail
    .endr
    .irp reg,8,9,10,11,12,13,14,15
    fmov x9, d\reg
    cmp x9, #\reg
    b.ne .Lfpr_fail
    .endr
    ldp x19, x20, [sp, #0]
    ldp x21, x22, [sp, #16]
    ldp x23, x24, [sp, #32]
    ldp x25, x26, [sp, #48]
    ldp x27, x28, [sp, #64]
    ldp x29, x30, [sp, #80]
    ldp d8, d9, [sp, #96]
    ldp d10, d11, [sp, #112]
    ldp d12, d13, [sp, #128]
    ldp d14, d15, [sp, #144]
    add sp, sp, #160
    ret
.Lsp_fail:
    mov x0, #71
    b .Lexit
.Lgpr_fail:
    mov x0, #72
    b .Lexit
.Lfpr_fail:
    mov x0, #73
.Lexit:
    mov x8, #93
    svc #0
.size abi_call2, .-abi_call2
.section .note.GNU-stack,"",%progbits
"#;

/// Hand-written leaves for the controls: correct frameless multiply and store
/// leaves, plus one `load_add` variant each.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn control_leaves(load_add: &str) -> String {
    let leaf = |name: &str, body: &str| {
        format!(
            ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\n{body}.size {name}, .-{name}\n"
        )
    };
    let frameless = |body: &str| format!("    .cfi_startproc\n{body}    ret\n    .cfi_endproc\n");
    [
        ".text\n".to_owned(),
        leaf(
            "add_fn",
            &frameless("    add x2, x0, x1\n    add x1, x2, x2, lsl #1\n    sub x0, x1, x0\n"),
        ),
        leaf(
            "mul_sub_fn",
            &frameless("    add x2, x0, x1\n    lsl x1, x2, #2\n    sub x0, x1, x0\n"),
        ),
        leaf(
            "add_double_fn",
            &frameless("    add x2, x0, x1\n    add x1, x2, x2, lsl #2\n    sub x0, x1, x0\n"),
        ),
        leaf("load_add", load_add),
        leaf(
            "store_sub",
            &frameless("    sub x1, x1, #1\n    str x1, [x0]\n"),
        ),
        ".section .note.GNU-stack,\"\",%progbits\n".to_owned(),
    ]
    .concat()
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn link_and_run_leaves(
    directory: &std::path::Path,
    name: &str,
    leaves: &std::path::Path,
    run_timeout: std::time::Duration,
) -> (Option<i32>, String, String) {
    use std::{fs, process::Command};
    let source = directory.join("driver.c");
    let trampoline = directory.join("abi.S");
    if !source.exists() {
        fs::write(&source, UNOWNED_LEAF_DRIVER).unwrap();
        fs::write(&trampoline, UNOWNED_LEAF_TRAMPOLINE).unwrap();
    }
    let binary = directory.join(name);
    let linked = process::command_output_with_timeout(
        Command::new("cc")
            .args([
                "-std=gnu11",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-rdynamic",
            ])
            .arg(&source)
            .arg(&trampoline)
            .arg(leaves)
            .args(["-ldl", "-Wl,-z,noexecstack", "-o"])
            .arg(&binary),
        process::codegen_link_timeout(),
    )
    .unwrap();
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{name} link: {}",
        String::from_utf8_lossy(&linked.output.stderr)
    );
    let ran =
        process::command_output_with_timeout(&mut Command::new(&binary), run_timeout).unwrap();
    let stdout = String::from_utf8_lossy(&ran.output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&ran.output.stderr).into_owned();
    fs::write(directory.join(format!("{name}.stdout")), &stdout).unwrap();
    fs::write(directory.join(format!("{name}.stderr")), &stderr).unwrap();
    assert!(!ran.timed_out, "{name}: timed out (a hang is a failure)");
    (ran.output.status.code(), stdout, stderr)
}

/// Run the newly frameless ELF leaves natively at O0-O3. `abi_call2` checks
/// the callee-saved registers, SP and FP after each of 720 calls per level.
/// The traced unwind phase then interrupts each leaf at every instruction on
/// its executed path and checks the unwinder's CFA and return address for the
/// leaf's caller (see [`UNOWNED_LEAF_DRIVER`]). Every step must be covered:
/// the path length equals the symbol's instruction count. Controls, each run
/// under a short timeout where a hang fails the test:
/// - a legal framed `load_add` with correct CFI passes both phases;
/// - clobbering x29 or leaving SP moved exits 71, x19 exits 72, d8 exits 73;
/// - a frameless FDE that saves LR at CFA-8 exits 92 (poison return address);
/// - CFA=SP+16 with no LR rule exits 91, as does a frame whose CFI never
///   leaves CFA=SP (first reported at the PC after the STP, offset 4);
/// - no FDE at all exits 94 (no caller frame).
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[test]
fn unowned_frameless_leaves_run_and_unwind_natively_at_every_level() {
    use std::fs;

    let module = unowned_leaf_module();
    let directory = crate::fresh_dir::create("trust-cg-unowned-leaf-");
    let expect_pass = |name: &str, stdout: &str, sizes_from_object: bool| {
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(
            lines.first(),
            Some(&"UNOWNED_LEAF_NATIVE calls=720"),
            "{name}"
        );
        let mut total = 0;
        for leaf in [
            "add_fn",
            "mul_sub_fn",
            "add_double_fn",
            "load_add",
            "store_sub",
        ] {
            let trace = lines
                .iter()
                .find_map(|line| line.strip_prefix(&format!("TRACE {leaf} path=")))
                .unwrap_or_else(|| panic!("{name}: no trace for {leaf}: {stdout}"));
            let (path, size) = trace.split_once(" size=").unwrap();
            let (path, size): (u32, u32) = (path.parse().unwrap(), size.parse().unwrap());
            if sizes_from_object {
                assert_eq!(
                    path * 4,
                    size,
                    "{name} {leaf}: every instruction must be interrupted"
                );
            }
            assert!(path >= 2, "{name} {leaf}");
            assert!(
                lines.contains(&format!("UNWIND {leaf} pcs={path}").as_str()),
                "{name} {leaf}: {stdout}"
            );
            total += path;
        }
        assert_eq!(
            lines.last(),
            Some(&format!("UNOWNED_LEAF_UNWIND pcs={total}").as_str()),
            "{name}"
        );
        total
    };
    let mut interrupted = 0;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object_code = object_for(&module, "aarch64-unknown-linux-gnu", level);
        assert!(
            !native_host::text_words(&object_code).contains(&STP_FP_LR_PRE16),
            "{level:?}"
        );
        let object = directory.join(format!("unowned-{level:?}.o"));
        fs::write(&object, object_code).unwrap();
        let name = format!("unowned-{level:?}");
        let (code, stdout, stderr) =
            link_and_run_leaves(&directory, &name, &object, process::codegen_run_timeout());
        assert_eq!(code, Some(0), "{name}: {stdout}{stderr}");
        interrupted += expect_pass(&name, &stdout, true);
    }

    let frameless = |body: &str, cfi: &str| {
        format!("    .cfi_startproc\n{cfi}{body}    ret\n    .cfi_endproc\n")
    };
    let load = "    ldr x0, [x0]\n    add x0, x0, x1\n";
    let framed = |cfi_after_push: &str, cfi_after_pop: &str| {
        format!(
            "    .cfi_startproc\n    stp x29, x30, [sp, #-16]!\n{cfi_after_push}    mov x29, sp\n{load}    ldp x29, x30, [sp], #16\n{cfi_after_pop}    ret\n    .cfi_endproc\n"
        )
    };
    let controls: Vec<(&str, String, i32, Option<&str>)> = vec![
        (
            "legal-framed",
            framed(
                "    .cfi_def_cfa_offset 16\n    .cfi_offset x29, -16\n    .cfi_offset x30, -8\n",
                "    .cfi_def_cfa_offset 0\n    .cfi_restore x29\n    .cfi_restore x30\n",
            ),
            0,
            None,
        ),
        (
            "clobber-x29",
            frameless(&format!("{load}    mov x29, #0\n"), ""),
            71,
            None,
        ),
        (
            "sp-not-restored",
            frameless(
                &format!("    sub sp, sp, #16\n    .cfi_def_cfa_offset 16\n{load}"),
                "",
            ),
            71,
            None,
        ),
        (
            "clobber-x19",
            frameless(&format!("{load}    mov x19, #0\n"), ""),
            72,
            None,
        ),
        (
            "clobber-d8",
            frameless(&format!("{load}    fmov d8, xzr\n"), ""),
            73,
            None,
        ),
        (
            "lr-rule-below-cfa",
            frameless(load, "    .cfi_offset x30, -8\n"),
            92,
            Some("fn=load_add offset=0 code=92"),
        ),
        (
            "cfa-sp-plus-16",
            frameless(load, "    .cfi_def_cfa_offset 16\n"),
            91,
            Some("fn=load_add offset=0 code=91"),
        ),
        (
            "framed-stale-cfa",
            framed("", ""),
            91,
            Some("fn=load_add offset=4 code=91"),
        ),
        (
            "no-fde",
            format!("{load}    ret\n"),
            94,
            Some("fn=load_add offset=0 code=94"),
        ),
    ];
    for (name, load_add, expected, diagnostic) in &controls {
        let leaves = directory.join(format!("control-{name}.S"));
        fs::write(&leaves, control_leaves(load_add)).unwrap();
        let (code, stdout, stderr) = link_and_run_leaves(
            &directory,
            &format!("control-{name}"),
            &leaves,
            std::time::Duration::from_secs(30),
        );
        assert_eq!(code, Some(*expected), "control {name}: {stdout}{stderr}");
        if *expected == 0 {
            expect_pass(name, &stdout, false);
        }
        if let Some(diagnostic) = diagnostic {
            assert!(stderr.contains(diagnostic), "control {name}: {stderr}");
        }
    }
    println!("UNOWNED_LEAF_NATIVE_ARTIFACTS={}", directory.display());
    println!(
        "UNOWNED_LEAF_NATIVE_CALLS=2880 INTERRUPTED_PCS={interrupted} CONTROLS={}",
        controls.len()
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
