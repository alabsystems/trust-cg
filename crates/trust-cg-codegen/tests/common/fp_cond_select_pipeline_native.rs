// Copyright 2026 Andrew Yates | Apache-2.0
//! Native LIR/ISel/optimization/allocation/object (ELF or Mach-O) regressions, not a frontend or
//! formal proof. Float payloads never enter host floating-point arithmetic.
//! The full Q0 observation also checks the emitted scalar instruction's upper
//! zeroing; this is an instruction-level property, not a scalar ABI guarantee.
//! Final CG NZCV is retained diagnostically: LIR does not expose flags, so an
//! equivalent instruction sequence need not preserve the source comparison's
//! flags through return. The independent CMP/FCSEL control has that contract.

#![cfg(feature = "verify")]

use super::{native_host, process};
use sha2::{Digest, Sha256};
use std::{fmt::Write, fs, path::Path, process::Command};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::AArch64Opcode as Op;
use trust_cg_lower::{
    Function, Type,
    function::{BasicBlock, Signature},
    instructions::{Block, Instruction, IntCC, Opcode, Value},
};

const CONDITIONS: [(IntCC, &str); 10] = [
    (IntCC::Equal, "eq"),
    (IntCC::NotEqual, "ne"),
    (IntCC::SignedLessThan, "lt"),
    (IntCC::SignedGreaterThanOrEqual, "ge"),
    (IntCC::SignedGreaterThan, "gt"),
    (IntCC::SignedLessThanOrEqual, "le"),
    (IntCC::UnsignedLessThan, "cc"),
    (IntCC::UnsignedGreaterThanOrEqual, "cs"),
    (IntCC::UnsignedGreaterThan, "hi"),
    (IntCC::UnsignedLessThanOrEqual, "ls"),
];
const FUNCTIONS: usize = 64;
const INTEGER_PAIRS: usize = 8;
const PAYLOADS: usize = 16;
const CALLS: usize = FUNCTIONS * INTEGER_PAIRS * PAYLOADS * PAYLOADS;
const CHECKS: usize = CALLS * 7;

#[derive(Clone, Copy)]
struct Case {
    integer_width: u32,
    float_width: u32,
    condition: usize,
    compare: bool,
}

impl Case {
    fn name(self) -> String {
        format!(
            "fp_select_i{}_f{}_cc{}_cmp{}",
            self.integer_width,
            self.float_width,
            self.condition,
            u8::from(self.compare)
        )
    }

    fn input(self) -> Function {
        let integer = if self.integer_width == 32 {
            Type::I32
        } else {
            Type::I64
        };
        let float = if self.float_width == 32 {
            Type::F32
        } else {
            Type::F64
        };
        let mut function = Function::new(
            self.name(),
            Signature {
                params: vec![integer.clone(), integer, float.clone(), float.clone()],
                returns: vec![float],
            },
        );
        let mut instructions = Vec::new();
        if self.compare {
            instructions.push(Instruction {
                opcode: Opcode::Icmp {
                    cond: CONDITIONS[self.condition].0,
                },
                args: vec![Value(0), Value(1)],
                results: vec![Value(4)],
            });
        }
        instructions.push(Instruction {
            opcode: Opcode::Select {
                cond: if self.compare {
                    IntCC::NotEqual
                } else {
                    CONDITIONS[self.condition].0
                },
            },
            args: vec![
                if self.compare { Value(4) } else { Value(0) },
                Value(2),
                Value(3),
            ],
            results: vec![Value(5)],
        });
        instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(5)],
            results: vec![],
        });
        let entry = Block(0);
        function.entry_block = entry;
        function.block_order = vec![entry];
        function.blocks.insert(
            entry,
            BasicBlock {
                instructions,
                ..Default::default()
            },
        );
        function
    }
}

fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for integer_width in [32, 64] {
        for float_width in [32, 64] {
            for compare in [false, true] {
                for condition in 0..if compare { 10 } else { 6 } {
                    cases.push(Case {
                        integer_width,
                        float_width,
                        condition,
                        compare,
                    });
                }
            }
        }
    }
    assert_eq!(cases.len(), FUNCTIONS);
    cases
}

fn wrapper(assembly: &mut String, name: &str, target: &str, width: u32) {
    let lane = if width == 32 { "s" } else { "d" };
    let gpr = if width == 32 { "w" } else { "x" };
    // Integer-only C ABI: x0/x1 carry comparison inputs, x2/x3 payload bits,
    // x4 the result pointer. The callee has the real mixed integer/FP ABI.
    // Preserve FP/LR, the result pointer and caller FPSR in a 48-byte frame.
    // Dirty every unused input-vector bit before inserting the scalar payload.
    // Neither the wrapper nor the controls execute floating-point arithmetic.
    writeln!(
        assembly,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\n\
         stp x29,x30,[sp,#-48]!\nmov x29,sp\nstr x4,[sp,#16]\n\
         mrs x9,fpsr\nstr x9,[sp,#24]\nmsr fpsr,xzr\n\
         movi v0.16b,#165\nmovi v1.16b,#90\n\
         ins v0.{lane}[0],{gpr}2\nins v1.{lane}[0],{gpr}3\n\
         bl {target}\nldr x10,[sp,#16]\nstr q0,[x10]\n\
         mrs x9,nzcv\nstr x9,[x10,#16]\nmrs x9,fpsr\nstr x9,[x10,#24]\n\
         ldr x9,[sp,#24]\nmsr fpsr,x9\nldp x29,x30,[sp],#48\nret\n\
         .size {name},.-{name}"
    )
    .unwrap();
}

fn sources(cases: &[Case]) -> (String, String) {
    let mut assembly = String::from(".text\n");
    let mut driver = String::from(
        r#"
#include <stdint.h>
#include <stdio.h>
typedef void (*function_t)(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t*);
struct test_case {function_t cg,as;unsigned integer_width,float_width,cc,compare;};
static uint64_t calls,controls,checks,failures;
static unsigned predicate(unsigned cc,uint64_t a,uint64_t b,unsigned width) {
 uint64_t mask=width==32?UINT32_MAX:UINT64_MAX;
 uint64_t sign=UINT64_C(1)<<(width-1);
 a&=mask;b&=mask;
 switch(cc) {
 case 0:return a==b;case 1:return a!=b;
 case 2:return (a^sign)<(b^sign);case 3:return (a^sign)>=(b^sign);
 case 4:return (a^sign)>(b^sign);case 5:return (a^sign)<=(b^sign);
 case 6:return a<b;case 7:return a>=b;case 8:return a>b;case 9:return a<=b;
 default:return 0;
 }
}
static uint64_t subtract_flags(uint64_t a,uint64_t b,unsigned width) {
 uint64_t mask=width==32?UINT32_MAX:UINT64_MAX,sign=UINT64_C(1)<<(width-1);
 a&=mask;b&=mask;uint64_t r=(a-b)&mask;
 unsigned n=(r&sign)!=0,z=r==0,c=a>=b,v=((a^b)&(a^r)&sign)!=0;
 return (uint64_t)((n<<3)|(z<<2)|(c<<1)|v)<<28;
}
static void check(uint64_t got,uint64_t want,unsigned i,unsigned p,unsigned a,unsigned b,const char*kind) {
 checks++;
 if(got!=want) {
  if(failures<12)fprintf(stderr,"case%u pair%u payload%u/%u %s got%016llx want%016llx\n",i,p,a,b,kind,(unsigned long long)got,(unsigned long long)want);
  failures++;
 }
}
"#,
    );
    let mut rows = String::from("static const struct test_case cases[]={\n");
    for &case in cases {
        let name = case.name();
        wrapper(
            &mut assembly,
            &format!("call_{name}"),
            &native_host::c_symbol(&name),
            case.float_width,
        );
        wrapper(
            &mut assembly,
            &format!("control_{name}"),
            &format!("asm_{name}"),
            case.float_width,
        );
        let integer = if case.integer_width == 32 { "w" } else { "x" };
        let float = if case.float_width == 32 { "s" } else { "d" };
        let rhs = if case.compare {
            format!("{integer}1")
        } else {
            "#0".into()
        };
        let cc = CONDITIONS[case.condition].1;
        writeln!(
            assembly,
            ".p2align 2\n.type asm_{name},%function\nasm_{name}:\n\
             cmp {integer}0,{rhs}\nfcsel {float}0,{float}0,{float}1,{cc}\nret\n\
             .size asm_{name},.-asm_{name}"
        )
        .unwrap();
        writeln!(driver, "extern void call_{name}(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t*),control_{name}(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t*);").unwrap();
        writeln!(
            rows,
            "{{call_{name},control_{name},{},{},{},{}}},",
            case.integer_width,
            case.float_width,
            case.condition,
            u8::from(case.compare)
        )
        .unwrap();
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    rows.push_str("};\n");
    driver.push_str(&rows);
    driver.push_str(r#"
/* +/-0, +/-1, signed minimum subnormal, largest subnormal, minimum normal,
 * signed maximum finite, infinities, distinct quiet and signaling NaNs. */
static const uint64_t payloads[2][16]={
 {0,0x80000000ULL,0x3f800000ULL,0xbf800000ULL,1,0x80000001ULL,
  0x007fffffULL,0x00800000ULL,0x7f7fffffULL,0xff7fffffULL,
  0x7f800000ULL,0xff800000ULL,0x7fc12345ULL,0xffc54321ULL,0x7f800001ULL,0xff800123ULL},
 {0,0x8000000000000000ULL,0x3ff0000000000000ULL,0xbff0000000000000ULL,
  1,0x8000000000000001ULL,0x000fffffffffffffULL,0x0010000000000000ULL,
  0x7fefffffffffffffULL,0xffefffffffffffffULL,0x7ff0000000000000ULL,0xfff0000000000000ULL,
  0x7ff8123456789abcULL,0xfff8abcdef123456ULL,0x7ff0000000000001ULL,0xfff0000012345678ULL}
};
static const uint64_t integers[8][2]={
 {0,0},{1,0},{0,1},{UINT64_MAX,0},{0,UINT64_MAX},
 {0x8000000080000000ULL,0x7fffffff7fffffffULL},
 {0x7fffffff7fffffffULL,0x8000000080000000ULL},{0x100000000ULL,0}
};
int main(int argc,char**argv) {
 if(argc!=2)return 2;
 FILE*out=fopen(argv[1],"wb");if(!out)return 3;
 if(sizeof(cases)/sizeof(cases[0])!=64)return 4;
 unsigned arm_seen[64]={0};
 for(unsigned i=0;i<64;i++)for(unsigned p=0;p<8;p++)for(unsigned a=0;a<16;a++)for(unsigned b=0;b<16;b++) {
  const struct test_case*t=&cases[i];
  uint64_t x=integers[p][0],y=integers[p][1],rhs=t->compare?y:0;
  unsigned choice=predicate(t->cc,x,rhs,t->integer_width);arm_seen[i]|=1U<<choice;
  uint64_t av=payloads[t->float_width==64][a],bv=payloads[t->float_width==64][b];
  uint64_t want=choice?av:bv,wantflags=subtract_flags(x,rhs,t->integer_width);
  uint64_t cg[4]={UINT64_MAX,UINT64_MAX,UINT64_MAX,UINT64_MAX};
  uint64_t as[4]={UINT64_MAX,UINT64_MAX,UINT64_MAX,UINT64_MAX};
  t->cg(x,y,av,bv,cg);calls++;t->as(x,y,av,bv,as);controls++;
  check(cg[0],want,i,p,a,b,"CG bits");check(as[0],want,i,p,a,b,"assembly bits");
  check(cg[1],0,i,p,a,b,"CG upper64");check(as[1],0,i,p,a,b,"assembly upper64");
  /* CG final NZCV is recorded, not source-visible or required to equal CMP. */
  check(as[2],wantflags,i,p,a,b,"assembly NZCV");
  check(cg[3],0,i,p,a,b,"CG FPSR");check(as[3],0,i,p,a,b,"assembly FPSR");
  uint64_t record[10]={cg[0],cg[1],cg[2],cg[3],as[0],as[1],as[2],as[3],want,wantflags};
  if(fwrite(record,sizeof(uint64_t),10,out)!=10)return 5;
 }
 if(fclose(out))return 6;
 for(unsigned i=0;i<64;i++)if(arm_seen[i]!=3) {fprintf(stderr,"case%u did not execute both arms\n",i);return 7;}
 if(calls!=131072||controls!=131072||checks!=917504||failures) {
  fprintf(stderr,"calls%llu controls%llu checks%llu failures%llu\n",(unsigned long long)calls,(unsigned long long)controls,(unsigned long long)checks,(unsigned long long)failures);return 1;
 }
 puts("PASS 131072 CG LIR pipeline calls, 131072 assembly controls, 917504 exact-bit/state checks");return 0;
}
"#);
    (assembly, driver)
}

fn hash_artifacts(directory: &Path) {
    fn visit(root: &Path, directory: &Path, rows: &mut Vec<(String, String)>) {
        for entry in fs::read_dir(directory).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                visit(root, &path, rows);
            } else if path.file_name().unwrap() != "SHA256SUMS" {
                let digest = format!("{:x}", Sha256::digest(fs::read(&path).unwrap()));
                rows.push((
                    path.strip_prefix(root).unwrap().to_str().unwrap().into(),
                    digest,
                ));
            }
        }
    }
    let mut rows = Vec::new();
    visit(directory, directory, &mut rows);
    rows.sort();
    let text: String = rows
        .into_iter()
        .map(|(name, digest)| format!("{digest}  {name}\n"))
        .collect();
    fs::write(directory.join("SHA256SUMS"), text).unwrap();
}

#[test]
fn fp_conditional_select_lir_pipeline_preserves_exact_bits_and_comparison_flags() {
    let directory_scratch = crate::fresh_dir::create("trust-cg-fcsel-pipeline-native-");
    let directory = directory_scratch.to_path_buf();
    eprintln!("FP conditional-select LIR pipeline evidence={directory:?}");
    let cases = cases();
    let (assembly, driver) = sources(&cases);
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
            target_triple: native_host::TRIPLE.into(),
            opt_level: opt,
            verify: true, // Diagnostic verification; no proof-required authority.
            ..Default::default()
        });
        let mut prepared = Vec::new();
        for &case in &cases {
            let input = case.input();
            let name = input.name.clone();
            fs::write(tier.join(format!("{name}.lir")), format!("{input:#?}")).unwrap();
            let (machine, metrics) = pipeline
                .prepare_function_with_metrics(&input, None)
                .unwrap_or_else(|error| panic!("{opt:?}/{name}/{directory:?}: {error:?}"));
            fs::write(tier.join(format!("{name}.machir")), format!("{machine:#?}")).unwrap();
            fs::write(
                tier.join(format!("{name}.metrics")),
                format!("{metrics:#?}"),
            )
            .unwrap();
            let instructions: Vec<_> = machine
                .block_order
                .iter()
                .flat_map(|&b| machine.block(b).insts.iter().map(|&i| machine.inst(i)))
                .collect();
            assert_eq!(
                instructions
                    .iter()
                    .filter(|i| i.opcode == Op::FcselRR)
                    .count(),
                1,
                "{opt:?}/{name}: actual FP select was not exercised"
            );
            assert!(
                instructions.iter().all(|i| i.opcode != Op::Csel),
                "{opt:?}/{name}: FP select unexpectedly entered integer bank"
            );
            prepared.push(machine);
        }
        let object = tier.join("selects.o");
        let bytes = pipeline
            .compile_module(&prepared)
            .unwrap_or_else(|error| panic!("{opt:?}/{directory:?}: {error:?}"));
        native_host::assert_native_object(&bytes);
        fs::write(&object, bytes).unwrap();
        let binary = tier.join("run");
        let mut link = Command::new("cc");
        link.arg(format!("-{opt:?}"))
            .args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
            .args(native_host::link_hardening_args())
            .arg(directory.join("driver.c"))
            .arg(directory.join("controls.S"))
            .arg(&object)
            .arg("-o")
            .arg(&binary);
        fs::write(
            tier.join("link.command"),
            format!("{link:?}\ntimeout={:?}\n", process::codegen_link_timeout()),
        )
        .unwrap();
        let linked =
            process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
                .unwrap();
        fs::write(tier.join("link.stdout"), &linked.output.stdout).unwrap();
        fs::write(tier.join("link.stderr"), &linked.output.stderr).unwrap();
        hash_artifacts(&directory);
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{opt:?}/{directory:?}: {}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let records = tier.join("results.bin");
        let mut command = Command::new(&binary);
        command.arg(&records);
        fs::write(
            tier.join("run.command"),
            format!(
                "{command:?}\ntimeout={:?}\n",
                process::codegen_run_timeout()
            ),
        )
        .unwrap();
        let run =
            process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
                .unwrap();
        fs::write(tier.join("stdout.log"), &run.output.stdout).unwrap();
        fs::write(tier.join("stderr.log"), &run.output.stderr).unwrap();
        hash_artifacts(&directory);
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt:?}/{directory:?}: {} {}",
            String::from_utf8_lossy(&run.output.stdout),
            String::from_utf8_lossy(&run.output.stderr)
        );
        let marker = format!(
            "PASS {CALLS} CG LIR pipeline calls, {CALLS} assembly controls, {CHECKS} exact-bit/state checks"
        );
        assert_eq!(String::from_utf8_lossy(&run.output.stdout).trim(), marker);
        assert_eq!(
            fs::metadata(records).unwrap().len(),
            (CALLS * 10 * 8) as u64
        );
        eprintln!("{opt:?}: {marker}; {FUNCTIONS} prepared LIR functions with actual FCSEL");
    }
}
