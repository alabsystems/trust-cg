// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual raw-MachIR optimization/allocation/object execution (ELF on Linux,
//! Mach-O on macOS), not frontend or
//! formal-proof coverage. Assembly wrappers supply the incoming architectural
//! NZCV state; the independent controls execute unfused ADD+CSEL instructions.

#![cfg(feature = "verify")]

use super::{native_host, process};
use std::{fmt::Write, fs, process::Command};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::{
    AArch64Opcode as Op, MachFunction, MachInst, MachOperand as Arg, RegClass, Signature, Type,
    VReg,
    regs::{W0, W1, X0, X1},
};

const CONDITIONS: [&str; 16] = [
    "eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv",
];
const CALLS_PER_TIER: usize = 64 * 16 * 3;
const CHECKS_PER_TIER: usize = CALLS_PER_TIER * 4;

fn append(function: &mut MachFunction, inst: MachInst) {
    let id = function.push_inst(inst);
    function.append_inst(function.entry, id);
}

fn input_function(width: u32, cc: usize, increment_true: bool) -> MachFunction {
    let (class, ty, r0, r1) = if width == 32 {
        (RegClass::Gpr32, Type::I32, W0, W1)
    } else {
        (RegClass::Gpr64, Type::I64, X0, X1)
    };
    let mut function = MachFunction::new(
        format!("pass_w{width}_cc{cc:02}_t{}", u8::from(increment_true)),
        Signature::new(vec![ty.clone(), ty.clone(), Type::I64], vec![ty]),
    );
    let base = VReg::new(function.alloc_vreg(), class);
    let other = VReg::new(function.alloc_vreg(), class);
    let increment = VReg::new(function.alloc_vreg(), class);
    let result = VReg::new(function.alloc_vreg(), class);
    let first_copy = MachInst::new(Op::Copy, vec![Arg::VReg(base), Arg::PReg(r0)]);
    append(
        &mut function,
        if width == 32 {
            first_copy.with_implicit_uses(&[W1])
        } else {
            first_copy.with_implicit_uses(&[X1])
        },
    );
    append(
        &mut function,
        MachInst::new(Op::Copy, vec![Arg::VReg(other), Arg::PReg(r1)]),
    );
    append(
        &mut function,
        MachInst::new(
            Op::AddRI,
            vec![Arg::VReg(increment), Arg::VReg(base), Arg::Imm(1)],
        ),
    );
    let (t, f) = if increment_true {
        (increment, other)
    } else {
        (other, increment)
    };
    append(
        &mut function,
        MachInst::new(
            Op::Csel,
            vec![
                Arg::VReg(result),
                Arg::VReg(t),
                Arg::VReg(f),
                Arg::Imm(cc as i64),
            ],
        ),
    );
    append(
        &mut function,
        MachInst::new(Op::Copy, vec![Arg::PReg(r0), Arg::VReg(result)]),
    );
    append(
        &mut function,
        if width == 32 {
            MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[W0])
        } else {
            MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0])
        },
    );
    function
}

/// `target` is the object-file symbol the wrapper branches to: a pipeline
/// function from another object (spelled by `native_host::c_symbol`) or a
/// local control label in this assembly file.
fn wrapper(assembly: &mut String, name: &str, target: &str) {
    // 32-byte frame preserves FP/LR and the C-owned output pointer across BL.
    // No instruction between MSR and the callee, or between its return and MRS,
    // changes flags. The wrapper exposes the full architectural X0 result even
    // when the callee's matching return copy writes W0 (zero-extension control).
    writeln!(
        assembly,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\n\
        stp x29,x30,[sp,#-32]!\nmov x29,sp\nstr x3,[sp,#16]\nmsr nzcv,x2\n\
        bl {target}\nmrs x9,nzcv\nldr x10,[sp,#16]\nstr x9,[x10]\n\
        ldp x29,x30,[sp],#32\nret\n.size {name},.-{name}"
    )
    .unwrap();
}

fn sources() -> (String, String) {
    let mut assembly = String::from(".text\n");
    let mut driver = String::from(
        r#"
#include <stdint.h>
#include <stdio.h>
typedef uint64_t (*function_t)(uint64_t,uint64_t,uint64_t,uint64_t*);
struct test_case {function_t cg,as; unsigned width,cc,increment_true;};
static unsigned holds(unsigned cc,unsigned flags) {
 unsigned n=(flags>>3)&1,z=(flags>>2)&1,c=(flags>>1)&1,v=flags&1;
 switch(cc) {case 0:return z;case 1:return !z;case 2:return c;case 3:return !c;
 case 4:return n;case 5:return !n;case 6:return v;case 7:return !v;
 case 8:return c&&!z;case 9:return !c||z;case 10:return n==v;case 11:return n!=v;
 case 12:return !z&&(n==v);case 13:return z||(n!=v);case 14:case 15:return 1;default:return 0;}
}
static unsigned calls,controls,checks,failures;
static void check(uint64_t got,uint64_t want,unsigned i,unsigned f,unsigned p,const char*kind) {
 checks++;if(got!=want) {if(failures<8)fprintf(stderr,"case%u flags%u input%u %s got%llx want%llx\n",i,f,p,kind,(unsigned long long)got,(unsigned long long)want);failures++;}
}
"#,
    );
    let mut rows = String::from("static const struct test_case cases[]={\n");
    for width in [32, 64] {
        for (cc, condition) in CONDITIONS.iter().enumerate() {
            for increment_true in [false, true] {
                let name = input_function(width, cc, increment_true).name;
                wrapper(
                    &mut assembly,
                    &format!("call_{name}"),
                    &native_host::c_symbol(&name),
                );
                wrapper(
                    &mut assembly,
                    &format!("control_{name}"),
                    &format!("asm_{name}"),
                );
                let bank = if width == 32 { "w" } else { "x" };
                let (t, f) = if increment_true { (4, 1) } else { (1, 4) };
                writeln!(
                    assembly,
                    ".p2align 2\n.type asm_{name},%function\nasm_{name}:\n\
                    add {bank}4,{bank}0,#1\ncsel {bank}0,{bank}{t},{bank}{f},{condition}\nret\n\
                    .size asm_{name},.-asm_{name}"
                )
                .unwrap();
                writeln!(driver, "extern uint64_t call_{name}(uint64_t,uint64_t,uint64_t,uint64_t*),control_{name}(uint64_t,uint64_t,uint64_t,uint64_t*);").unwrap();
                writeln!(
                    rows,
                    "{{call_{name},control_{name},{width},{cc},{}}},",
                    u8::from(increment_true)
                )
                .unwrap();
            }
        }
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    rows.push_str("};\n");
    driver.push_str(&rows);
    driver.push_str(r#"
static const uint64_t inputs[3][2]={{5,99},{UINT64_MAX,37},{0x80000000ULL,0x8000000000000001ULL}};
int main(int argc,char**argv) {
 if(argc!=2)return 2;FILE*out=fopen(argv[1],"wb");if(!out)return 3;
 for(unsigned i=0;i<64;i++)for(unsigned f=0;f<16;f++)for(unsigned p=0;p<3;p++) {
  const struct test_case*t=&cases[i];uint64_t flags=(uint64_t)f<<28;
  uint64_t base=inputs[p][0],other=inputs[p][1],sum=base+1;
  uint64_t want=holds(t->cc,f)==t->increment_true?sum:other;
  if(t->width==32)want=(uint32_t)want;
  uint64_t cgflags=UINT64_MAX,asflags=UINT64_MAX;
  uint64_t cg=t->cg(base,other,flags,&cgflags);calls++;
  uint64_t as=t->as(base,other,flags,&asflags);controls++;
  check(cg,want,i,f,p,"CG value");check(as,want,i,f,p,"assembly value");
  check(cgflags,flags,i,f,p,"CG flags");check(asflags,flags,i,f,p,"assembly flags");
  uint64_t record[5]={cg,as,want,cgflags,asflags};
  if(fwrite(record,sizeof(uint64_t),5,out)!=5)return 4;
 }
 if(fclose(out))return 5;
 if(calls!=3072||controls!=3072||checks!=12288||failures) {fprintf(stderr,"calls%u controls%u checks%u failures%u\n",calls,controls,checks,failures);return 1;}
 puts("PASS 3072 CG pipeline calls, 3072 assembly controls, 12288 value/flag checks");return 0;
}
"#);
    (assembly, driver)
}

#[test]
fn conditional_select_optimizer_native_al_nv_and_normal_conditions() {
    let directory_scratch = crate::fresh_dir::create("trust-cg-csel-pass-native-");
    let directory = directory_scratch.to_path_buf();
    eprintln!("conditional-select pass evidence={directory:?}");
    let (assembly, driver) = sources();
    fs::write(
        directory.join("controls.S"),
        native_host::assembly(&assembly),
    )
    .unwrap();
    fs::write(directory.join("driver.c"), driver).unwrap();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let tier = directory.join(format!("{opt:?}"));
        fs::create_dir(&tier).unwrap();
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: opt,
            target_triple: native_host::TRIPLE.into(),
            verify: true, // Diagnostic mode, not proof-required publication.
            ..Default::default()
        });
        let mut objects = Vec::new();
        let mut ordinary_csinc = 0;
        let mut unconditional_false_csinc = 0;
        for width in [32, 64] {
            for cc in 0..16 {
                for increment_true in [false, true] {
                    let mut function = input_function(width, cc, increment_true);
                    fs::write(
                        tier.join(format!("{}.input", function.name)),
                        format!("{function:#?}"),
                    )
                    .unwrap();
                    let (bytes, stats) = pipeline
                        .compile_ir_function_with_stats(&mut function)
                        .unwrap_or_else(|error| {
                            panic!("{opt:?}/{}/{directory:?}: {error:?}", function.name)
                        });
                    native_host::assert_native_object(&bytes);
                    fs::write(
                        tier.join(format!("{}.final", function.name)),
                        format!("{function:#?}"),
                    )
                    .unwrap();
                    fs::write(
                        tier.join(format!("{}.stats", function.name)),
                        format!("{stats:#?}"),
                    )
                    .unwrap();
                    let has_csinc = function.block_order.iter().any(|&block| {
                        function
                            .block(block)
                            .insts
                            .iter()
                            .any(|&id| function.inst(id).opcode == Op::Csinc)
                    });
                    ordinary_csinc += usize::from(cc < 14 && has_csinc);
                    unconditional_false_csinc +=
                        usize::from(cc >= 14 && !increment_true && has_csinc);
                    let object = tier.join(format!("{}.o", function.name));
                    fs::write(&object, bytes).unwrap();
                    objects.push(object);
                }
            }
        }
        assert_eq!(objects.len(), 64);
        if matches!(opt, OptLevel::O2 | OptLevel::O3) {
            assert!(
                ordinary_csinc > 0,
                "{opt:?}/{directory:?}: ordinary CSINC optimization was not exercised"
            );
            assert_eq!(
                unconditional_false_csinc, 4,
                "{opt:?}/{directory:?}: safe AL/NV false-arm folds were disabled"
            );
        }
        let binary = tier.join("run");
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .arg(format!("-{opt:?}"))
                .arg("-Werror")
                .args(native_host::link_hardening_args())
                .arg(directory.join("driver.c"))
                .arg(directory.join("controls.S"))
                .args(&objects)
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        fs::write(tier.join("link.stdout"), &link.output.stdout).unwrap();
        fs::write(tier.join("link.stderr"), &link.output.stderr).unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{opt:?}/{directory:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let results = tier.join("results.bin");
        let run = process::command_output_with_timeout(
            Command::new(&binary).arg(&results),
            process::codegen_run_timeout(),
        )
        .unwrap();
        fs::write(tier.join("stdout.log"), &run.output.stdout).unwrap();
        fs::write(tier.join("stderr.log"), &run.output.stderr).unwrap();
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt:?}/{directory:?}: {} {}",
            String::from_utf8_lossy(&run.output.stdout),
            String::from_utf8_lossy(&run.output.stderr)
        );
        let marker = format!(
            "PASS {CALLS_PER_TIER} CG pipeline calls, {CALLS_PER_TIER} assembly controls, {CHECKS_PER_TIER} value/flag checks"
        );
        assert_eq!(String::from_utf8_lossy(&run.output.stdout).trim(), marker);
        assert_eq!(
            fs::metadata(results).unwrap().len(),
            (CALLS_PER_TIER * 5 * 8) as u64
        );
        eprintln!(
            "{opt:?}: {marker}; ordinary CSINC functions={ordinary_csinc}, safe unconditional false-arm CSINC functions={unconditional_false_csinc}"
        );
    }
}
