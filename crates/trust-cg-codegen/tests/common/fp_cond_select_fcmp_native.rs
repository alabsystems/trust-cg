// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual floating-compare/FP-select LIR through the normal AArch64 pipeline.
//! Native differential evidence only: no source/proof authority or general FP
//! completion. IEEE comparisons use FPCR=0; flags and FP status are diagnostic.

#![cfg(feature = "verify")]

use super::{native_host, process};
use sha2::{Digest, Sha256};
use std::{fmt::Write, fs, path::Path, process::Command};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::AArch64Opcode as Op;
use trust_cg_lower::{
    Function, Type,
    function::{BasicBlock, Signature},
    instructions::{Block, FloatCC, Instruction, IntCC, Opcode, Value},
};

const CONDITIONS: [FloatCC; 14] = [
    FloatCC::Equal,
    FloatCC::NotEqual,
    FloatCC::LessThan,
    FloatCC::LessThanOrEqual,
    FloatCC::GreaterThan,
    FloatCC::GreaterThanOrEqual,
    FloatCC::Ordered,
    FloatCC::Unordered,
    FloatCC::UnorderedEqual,
    FloatCC::UnorderedNotEqual,
    FloatCC::UnorderedLessThan,
    FloatCC::UnorderedLessThanOrEqual,
    FloatCC::UnorderedGreaterThan,
    FloatCC::UnorderedGreaterThanOrEqual,
];
const FUNCTIONS: usize = 112;
const COMPARE_VALUES: usize = 16;
const PAYLOAD_PAIRS: usize = 4;
const CALLS: usize = FUNCTIONS * COMPARE_VALUES * COMPARE_VALUES * PAYLOAD_PAIRS;
const CHECKS: usize = CALLS * 10;

#[derive(Clone, Copy)]
struct Case {
    compare_width: u32,
    payload_width: u32,
    condition: usize,
    equal_sense: bool,
}

fn float_type(width: u32) -> Type {
    if width == 32 { Type::F32 } else { Type::F64 }
}

impl Case {
    fn name(self) -> String {
        format!(
            "fcmp_select_c{}_p{}_cc{}_eq{}",
            self.compare_width,
            self.payload_width,
            self.condition,
            u8::from(self.equal_sense)
        )
    }

    fn input(self) -> Function {
        let compare = float_type(self.compare_width);
        let payload = float_type(self.payload_width);
        let mut function = Function::new(
            self.name(),
            Signature {
                params: vec![compare.clone(), compare, payload.clone(), payload.clone()],
                returns: vec![payload],
            },
        );
        let entry = Block(0);
        function.entry_block = entry;
        function.block_order = vec![entry];
        function.blocks.insert(
            entry,
            BasicBlock {
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Fcmp {
                            cond: CONDITIONS[self.condition],
                        },
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(4)],
                    },
                    Instruction {
                        opcode: Opcode::Select {
                            cond: if self.equal_sense {
                                IntCC::Equal
                            } else {
                                IntCC::NotEqual
                            },
                        },
                        args: vec![Value(4), Value(2), Value(3)],
                        results: vec![Value(5)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(5)],
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        function
    }
}

fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for compare_width in [32, 64] {
        for payload_width in [32, 64] {
            for condition in 0..14 {
                for equal_sense in [false, true] {
                    cases.push(Case {
                        compare_width,
                        payload_width,
                        condition,
                        equal_sense,
                    });
                }
            }
        }
    }
    assert_eq!(cases.len(), FUNCTIONS);
    cases
}

fn wrapper(assembly: &mut String, name: &str, target: &str, case: Case) {
    // C supplies four integer bit patterns in x0-x3 and an output pointer in
    // x4. The generated function receives four actual FP ABI arguments v0-v3.
    // No host FP arithmetic can quiet a NaN or change the payload beforehand.
    // FPCR/FPSR and the output pointer survive BL in a 64-byte aligned frame.
    writeln!(
        assembly,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\n\
         stp x29,x30,[sp,#-64]!\nmov x29,sp\nstr x4,[sp,#16]\n\
         mrs x9,fpcr\nstr x9,[sp,#24]\nmrs x9,fpsr\nstr x9,[sp,#32]\n\
         msr fpcr,xzr\nmsr fpsr,xzr\nisb"
    )
    .unwrap();
    for r in 0..4 {
        let width = if r < 2 {
            case.compare_width
        } else {
            case.payload_width
        };
        let lane = if width == 32 { "s" } else { "d" };
        let gpr = if width == 32 { "w" } else { "x" };
        writeln!(
            assembly,
            "movi v{r}.16b,#{}\nins v{r}.{lane}[0],{gpr}{r}",
            161 + r
        )
        .unwrap();
    }
    writeln!(
        assembly,
        "bl {target}\nldr x10,[sp,#16]\nstr q0,[x10]\n\
         mrs x9,nzcv\nstr x9,[x10,#16]\nmrs x9,fpsr\nstr x9,[x10,#24]\n\
         mrs x9,fpcr\nstr x9,[x10,#32]\n\
         ldr x9,[sp,#24]\nmsr fpcr,x9\nldr x9,[sp,#32]\nmsr fpsr,x9\nisb\n\
         ldp x29,x30,[sp],#64\nret\n.size {name},.-{name}"
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
struct test_case {function_t cg,as;unsigned compare_width,payload_width,cc,equal_sense;};
static uint64_t calls,controls,checks,failures;
static void read_controls(uint64_t*fpcr,uint64_t*fpsr) {
 __asm__ volatile("mrs %0,fpcr\n\tmrs %1,fpsr" : "=r"(*fpcr),"=r"(*fpsr) : : "memory");
}
static void write_controls(uint64_t fpcr,uint64_t fpsr) {
 __asm__ volatile("msr fpcr,%0\n\tmsr fpsr,%1\n\tisb" : : "r"(fpcr),"r"(fpsr) : "memory");
}
/* Integer-only IEEE ordering. Infinities order by magnitude, both zeros are
 * equal, and either sign/payload of NaN makes the comparison unordered. */
static unsigned predicate(unsigned cc,uint64_t a,uint64_t b,unsigned width) {
 uint64_t sign=width==32?0x80000000ULL:0x8000000000000000ULL;
 uint64_t exponent=width==32?0x7f800000ULL:0x7ff0000000000000ULL;
 uint64_t fraction=width==32?0x007fffffULL:0x000fffffffffffffULL;
 if(width==32) {a=(uint32_t)a;b=(uint32_t)b;}
 unsigned unordered=((a&exponent)==exponent&&(a&fraction)!=0)||((b&exponent)==exponent&&(b&fraction)!=0);
 unsigned equal=(a==b)||((a&~sign)==0&&(b&~sign)==0);
 unsigned less=0;
 if(!unordered&&!equal)less=((a^b)&sign)?((a&sign)!=0):((a&sign)?a>b:a<b);
 unsigned greater=!unordered&&!equal&&!less;
 switch(cc) {
 case 0:return !unordered&&equal;case 1:return !unordered&&!equal;
 case 2:return !unordered&&less;case 3:return !unordered&&(less||equal);
 case 4:return !unordered&&greater;case 5:return !unordered&&(greater||equal);
 case 6:return !unordered;case 7:return unordered;
 case 8:return unordered||equal;case 9:return unordered||!equal;
 case 10:return unordered||less;case 11:return unordered||less||equal;
 case 12:return unordered||greater;case 13:return unordered||greater||equal;
 default:return 0;
 }
}
static void check(uint64_t got,uint64_t want,unsigned i,unsigned a,unsigned b,unsigned p,const char*kind) {
 checks++;
 if(got!=want) {
  if(failures<12)fprintf(stderr,"case%u compare%u/%u payload%u %s got%016llx want%016llx\n",i,a,b,p,kind,(unsigned long long)got,(unsigned long long)want);
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
            case,
        );
        wrapper(
            &mut assembly,
            &format!("control_{name}"),
            &format!("asm_{name}"),
            case,
        );
        let compare = if case.compare_width == 32 { "s" } else { "d" };
        let payload = if case.payload_width == 32 { "s" } else { "d" };
        writeln!(
            assembly,
            ".p2align 2\n.type asm_{name},%function\nasm_{name}:\nfcmp {compare}0,{compare}1"
        )
        .unwrap();
        // Deliberately materialize the reference predicate, even when CG can
        // directly fold FCMP flags into FCSEL. Ordered-not-equal uses NE && VC,
        // independent of production's MI || GT composition.
        match case.condition {
            1 => assembly.push_str("cset w9,ne\ncset w10,vc\nand w9,w9,w10\n"),
            8 => assembly.push_str("cset w9,eq\ncset w10,vs\norr w9,w9,w10\n"),
            cc => {
                let conditions = [
                    "eq", "", "mi", "ls", "gt", "ge", "vc", "vs", "", "ne", "lt", "le", "hi", "pl",
                ];
                writeln!(assembly, "cset w9,{}", conditions[cc]).unwrap();
            }
        }
        let sense = if case.equal_sense { "eq" } else { "ne" };
        writeln!(assembly, "cmp w9,#0\nfcsel {payload}0,{payload}2,{payload}3,{sense}\nret\n.size asm_{name},.-asm_{name}").unwrap();
        writeln!(driver, "extern void call_{name}(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t*),control_{name}(uint64_t,uint64_t,uint64_t,uint64_t,uint64_t*);").unwrap();
        writeln!(
            rows,
            "{{call_{name},control_{name},{},{},{},{}}},",
            case.compare_width,
            case.payload_width,
            case.condition,
            u8::from(case.equal_sense)
        )
        .unwrap();
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    rows.push_str("};\n");
    driver.push_str(&rows);
    driver.push_str(r#"
/* Signed zeros, +/-1, signed minimum subnormal, maximum subnormal, minimum
 * normal, signed maximum finite, infinities, quiet and signaling NaNs. */
static const uint64_t comparisons[2][16]={
 {0,0x80000000ULL,0x3f800000ULL,0xbf800000ULL,1,0x80000001ULL,
  0x007fffffULL,0x00800000ULL,0x7f7fffffULL,0xff7fffffULL,
  0x7f800000ULL,0xff800000ULL,0x7fc12345ULL,0xffc54321ULL,0x7f800001ULL,0xff800123ULL},
 {0,0x8000000000000000ULL,0x3ff0000000000000ULL,0xbff0000000000000ULL,
  1,0x8000000000000001ULL,0x000fffffffffffffULL,0x0010000000000000ULL,
  0x7fefffffffffffffULL,0xffefffffffffffffULL,0x7ff0000000000000ULL,0xfff0000000000000ULL,
  0x7ff8123456789abcULL,0xfff8abcdef123456ULL,0x7ff0000000000001ULL,0xfff0000012345678ULL}
};
static const uint64_t payloads[2][4][2]={
 {{0,0x80000000ULL},{0x7fc12345ULL,0xff800123ULL},{0x80000001ULL,0x7f7fffffULL},{0xff800000ULL,0x3f800000ULL}},
 {{0,0x8000000000000000ULL},{0x7ff8123456789abcULL,0xfff0000012345678ULL},
  {0x8000000000000001ULL,0x7fefffffffffffffULL},{0xfff0000000000000ULL,0x3ff0000000000000ULL}}
};
int main(int argc,char**argv) {
 if(argc!=2)return 2;
 FILE*out=fopen(argv[1],"wb");if(!out)return 3;
 if(sizeof(cases)/sizeof(cases[0])!=112) {fclose(out);return 4;}
 uint64_t original_fpcr,original_fpsr,observed_fpcr,observed_fpsr;
 const uint64_t caller_fpcr=0x03400000ULL,caller_fpsr=0x0800009fULL;
 read_controls(&original_fpcr,&original_fpsr);
 write_controls(caller_fpcr,caller_fpsr);
 read_controls(&observed_fpcr,&observed_fpsr);
 int status=0;
 if(observed_fpcr!=caller_fpcr||observed_fpsr!=caller_fpsr) {status=8;goto cleanup;}
 unsigned arms[112]={0};
 for(unsigned i=0;i<112;i++)for(unsigned a=0;a<16;a++)for(unsigned b=0;b<16;b++)for(unsigned p=0;p<4;p++) {
  const struct test_case*t=&cases[i];
  uint64_t x=comparisons[t->compare_width==64][a],y=comparisons[t->compare_width==64][b];
  unsigned value=predicate(t->cc,x,y,t->compare_width);
  unsigned choice=t->equal_sense?!value:value;arms[i]|=1U<<choice;
  uint64_t av=payloads[t->payload_width==64][p][0],bv=payloads[t->payload_width==64][p][1],want=choice?av:bv;
  uint64_t cg[5]={UINT64_MAX,UINT64_MAX,UINT64_MAX,UINT64_MAX,UINT64_MAX};
  uint64_t as[5]={UINT64_MAX,UINT64_MAX,UINT64_MAX,UINT64_MAX,UINT64_MAX};
  uint64_t cg_restored_fpcr,cg_restored_fpsr,as_restored_fpcr,as_restored_fpsr;
  t->cg(x,y,av,bv,cg);calls++;
  read_controls(&cg_restored_fpcr,&cg_restored_fpsr);
  t->as(x,y,av,bv,as);controls++;
  read_controls(&as_restored_fpcr,&as_restored_fpsr);
  check(cg[0],want,i,a,b,p,"CG selected bits");check(as[0],want,i,a,b,p,"assembly selected bits");
  check(cg[1],0,i,a,b,p,"CG upper64");check(as[1],0,i,a,b,p,"assembly upper64");
  check(cg[4],0,i,a,b,p,"CG FPCR");check(as[4],0,i,a,b,p,"assembly FPCR");
  check(cg_restored_fpcr,caller_fpcr,i,a,b,p,"CG caller FPCR restored");
  check(as_restored_fpcr,caller_fpcr,i,a,b,p,"assembly caller FPCR restored");
  check(cg_restored_fpsr,caller_fpsr,i,a,b,p,"CG caller FPSR restored");
  check(as_restored_fpsr,caller_fpsr,i,a,b,p,"assembly caller FPSR restored");
  /* NZCV/FPSR are retained diagnostics, not source-observable semantics. */
  uint64_t record[15]={cg[0],cg[1],cg[2],cg[3],cg[4],as[0],as[1],as[2],as[3],as[4],want,
   cg_restored_fpcr,cg_restored_fpsr,as_restored_fpcr,as_restored_fpsr};
  if(fwrite(record,sizeof(uint64_t),15,out)!=15) {status=5;goto cleanup;}
 }
cleanup:
 if(fclose(out)&&status==0)status=6;
 write_controls(original_fpcr,original_fpsr);
 read_controls(&observed_fpcr,&observed_fpsr);
 if(observed_fpcr!=original_fpcr||observed_fpsr!=original_fpsr)status=9;
 if(status)return status;
 for(unsigned i=0;i<112;i++)if(arms[i]!=3) {fprintf(stderr,"case%u did not execute both arms\n",i);return 7;}
 if(calls!=114688||controls!=114688||checks!=1146880||failures) {
  fprintf(stderr,"calls%llu controls%llu checks%llu failures%llu\n",(unsigned long long)calls,(unsigned long long)controls,(unsigned long long)checks,(unsigned long long)failures);return 1;
 }
 puts("PASS 114688 CG FCMP-LIR calls, 114688 assembly controls, 1146880 exact-bit/control checks");return 0;
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
                rows.push((
                    path.strip_prefix(root).unwrap().to_str().unwrap().into(),
                    format!("{:x}", Sha256::digest(fs::read(&path).unwrap())),
                ));
            }
        }
    }
    let mut rows = Vec::new();
    visit(directory, directory, &mut rows);
    rows.sort();
    fs::write(
        directory.join("SHA256SUMS"),
        rows.into_iter()
            .map(|(name, digest)| format!("{digest}  {name}\n"))
            .collect::<String>(),
    )
    .unwrap();
}

#[test]
fn fp_compare_select_lir_all_predicates_preserve_ieee_choices_and_payload_bits() {
    let directory_scratch = crate::fresh_dir::create("trust-cg-fcsel-fcmp-native-");
    let directory = directory_scratch.to_path_buf();
    eprintln!("FP compare/select LIR evidence={directory:?}");
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
            verify: true, // Diagnostics only, not proof-required compilation.
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
                "{opt:?}/{name}: FCSEL absent or duplicated"
            );
            assert!(
                instructions.iter().any(|i| i.opcode == Op::Fcmp),
                "{opt:?}/{name}: actual floating comparison absent"
            );
            assert!(
                instructions.iter().all(|i| i.opcode != Op::Csel),
                "{opt:?}/{name}: selected FP payload entered integer CSEL"
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
            "PASS {CALLS} CG FCMP-LIR calls, {CALLS} assembly controls, {CHECKS} exact-bit/control checks"
        );
        assert_eq!(String::from_utf8_lossy(&run.output.stdout).trim(), marker);
        assert_eq!(
            fs::metadata(records).unwrap().len(),
            (CALLS * 15 * 8) as u64
        );
        eprintln!(
            "{opt:?}: {marker}; {FUNCTIONS} prepared LIR functions with actual FCMP and FCSEL"
        );
    }
}
