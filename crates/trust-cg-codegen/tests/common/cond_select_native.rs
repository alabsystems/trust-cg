// Copyright 2026 Andrew Yates | Apache-2.0
//! Native raw-word/assembler/C/model differential controls. This bypasses
//! instruction selection, optimization, allocation and certified publication;
//! it grants no source-binding or formal-proof credit.

use super::native_host;
use super::*;
use std::{fmt::Write, fs, process::Command};
use trust_cg_verify::aarch64_csel_semantics::{DecodedConditionalSelect, RegisterState};

const LAYOUTS: [[u16; 3]; 10] = [
    [0, 1, 2],
    [1, 1, 2],
    [2, 1, 2],
    [0, 1, 1],
    [1, 1, 1],
    [0, 31, 2],
    [0, 1, 31],
    [31, 1, 2],
    [0, 31, 31],
    [31, 31, 31],
];
const INPUTS: [[u64; 4]; 8] = [
    [0xdeadbeef12345678, 0, 1, 0x1122334455667788],
    [u64::MAX, 1, u64::MAX, 0x1122334455667788],
    [0xdeadbeef12345678, u64::MAX, 0, 0x1122334455667788],
    [
        0xdeadbeef12345678,
        0x80000000,
        0xffffffff,
        0x1122334455667788,
    ],
    [
        0xdeadbeef12345678,
        0x7fffffff,
        0x80000000,
        0x1122334455667788,
    ],
    [
        0xdeadbeef12345678,
        0x8000000000000000,
        0x7fffffffffffffff,
        0x1122334455667788,
    ],
    [
        0xdeadbeef12345678,
        0x1234567800000001,
        0xfedcba9876543210,
        0x1122334455667788,
    ],
    [0xdeadbeef12345678, 5, 99, 0x1122334455667788],
];

fn register_name(width: u16, r: u16) -> String {
    let prefix = if width == 32 { "w" } else { "x" };
    if r == 31 {
        format!("{prefix}zr")
    } else {
        format!("{prefix}{r}")
    }
}

fn thunk(asm: &mut String, name: &str, operation: &str) {
    writeln!(
        asm,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\n\
        mov x4,x0\nmov x5,x1\nldp x0,x1,[x4]\nldp x2,x3,[x4,#16]\nmsr nzcv,x5\n\
        .global {name}_word\n{name}_word:\n{operation}\n\
        stp x0,x1,[x4]\nstp x2,x3,[x4,#16]\nmrs x5,nzcv\nstr x5,[x4,#32]\nret\n\
        .size {name},.-{name}"
    )
    .unwrap();
}

#[test]
fn conditional_select_native_words_preserve_values_aliases_and_flags() {
    let directory_scratch = crate::fresh_dir::create("trust-cg-csel-native-");
    let directory = directory_scratch.to_path_buf();
    let mut asm = String::from(".text\n");
    let mut c = String::from(
        r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef void (*function_t)(uint64_t*,uint64_t);
struct test_case {function_t cg,as; const uint32_t *cw,*aw; unsigned op,width,cc,d,n,m;};
static unsigned checks,failures,calls,controls,words;
static void check(uint64_t got,uint64_t expected) {
 checks++; if(got!=expected) {if(failures<8)fprintf(stderr,"check%u: got%llx expected%llx\n",checks,(unsigned long long)got,(unsigned long long)expected);failures++;}
}
static unsigned holds(unsigned cc,unsigned flags) {
 unsigned n=(flags>>3)&1,z=(flags>>2)&1,c=(flags>>1)&1,v=flags&1;
 switch(cc) {case 0:return z;case 1:return !z;case 2:return c;case 3:return !c;
 case 4:return n;case 5:return !n;case 6:return v;case 7:return !v;
 case 8:return c&&!z;case 9:return !c||z;case 10:return n==v;case 11:return n!=v;
 case 12:return !z&&(n==v);case 13:return z||(n!=v);case 14:case 15:return 1;default:return 0;}
}
"#,
    );
    let mut cases = Vec::new();
    for (op_index, (opcode, mnemonic)) in FAMILY
        .into_iter()
        .zip(["csel", "csinc", "csinv", "csneg"])
        .enumerate()
    {
        for width in [32, 64] {
            for cc in 0..16 {
                for layout in LAYOUTS {
                    let index = cases.len();
                    let inst = instruction(opcode, width, cc, layout);
                    let word = encode_instruction(&inst).unwrap();
                    assert!(matches!(check(&inst, word), DecodeCheckOutcome::Match));
                    thunk(
                        &mut asm,
                        &format!("cg{index}"),
                        &format!(".inst 0x{word:08x}"),
                    );
                    let [d, n, m] = layout.map(|r| register_name(width, r));
                    let condition = [
                        "eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt",
                        "gt", "le", "al", "nv",
                    ][cc as usize];
                    thunk(
                        &mut asm,
                        &format!("as{index}"),
                        &format!("{mnemonic} {d},{n},{m},{condition}"),
                    );
                    writeln!(c, "extern void cg{index}(uint64_t*,uint64_t),as{index}(uint64_t*,uint64_t); extern const uint32_t cg{index}_word[],as{index}_word[];").unwrap();
                    cases.push((word, op_index, width, cc, layout));
                }
            }
        }
    }
    assert_eq!(cases.len(), 1280);
    asm.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    c.push_str("static const struct test_case cases[]={\n");
    for (index, (_, op, width, cc, [d, n, m])) in cases.iter().enumerate() {
        writeln!(
            c,
            "{{cg{index},as{index},cg{index}_word,as{index}_word,{op},{width},{cc},{d},{n},{m}}},"
        )
        .unwrap();
    }
    c.push_str("};\nstatic const uint64_t inputs[8][4]={\n");
    for input in INPUTS {
        writeln!(
            c,
            "{{{:#x}ULL,{:#x}ULL,{:#x}ULL,{:#x}ULL}},",
            input[0], input[1], input[2], input[3]
        )
        .unwrap();
    }
    c.push_str(r#"
};
int main(int argc,char**argv) {
 if(argc!=2)return 2;FILE*out=fopen(argv[1],"wb");if(!out)return 3;
 for(unsigned i=0;i<1280;i++) {
  const struct test_case*t=&cases[i];check(*t->cw,*t->aw);words++;
  for(unsigned f=0;f<16;f++)for(unsigned p=0;p<8;p++) {
   uint64_t cg[5],as[5],expected[5];memcpy(cg,inputs[p],32);memcpy(as,inputs[p],32);memcpy(expected,inputs[p],32);
   cg[4]=as[4]=0xdeadbeef;expected[4]=(uint64_t)f<<28;
   uint64_t a=t->n==31?0:inputs[p][t->n],b=t->m==31?0:inputs[p][t->m],result;
   if(holds(t->cc,f))result=a;else switch(t->op){case 0:result=b;break;case 1:result=b+1;break;case 2:result=~b;break;default:result=0-b;break;}
   if(t->width==32)result=(uint32_t)result;if(t->d!=31)expected[t->d]=result;
   t->cg(cg,(uint64_t)f<<28);calls++;t->as(as,(uint64_t)f<<28);controls++;
   for(unsigned r=0;r<5;r++){check(cg[r],expected[r]);check(as[r],expected[r]);}
   if(fwrite(cg,sizeof(uint64_t),5,out)!=5)return 4;
  }
 }
 if(fclose(out))return 5;
 if(calls!=163840||controls!=163840||words!=1280||checks!=1639680||failures) {fprintf(stderr,"calls%u controls%u words%u checks%u failures%u\n",calls,controls,words,checks,failures);return 1;}
 puts("PASS 163840 CG calls, 163840 assembly controls, 1280 word comparisons, 1639680 value/flag/word checks");return 0;
}
"#);
    fs::write(directory.join("controls.S"), native_host::assembly(&asm)).unwrap();
    fs::write(directory.join("driver.c"), c).unwrap();
    let binary = directory.join("run");
    let compiled = process::command_output_with_timeout(
        Command::new("cc")
            .args(["-O2", "-Werror"])
            .args(native_host::link_hardening_args())
            .arg(directory.join("driver.c"))
            .arg(directory.join("controls.S"))
            .arg("-o")
            .arg(&binary),
        process::codegen_link_timeout(),
    )
    .unwrap();
    assert!(
        !compiled.timed_out && compiled.output.status.success(),
        "files={directory:?}: {}",
        String::from_utf8_lossy(&compiled.output.stderr)
    );
    let results = directory.join("states.bin");
    let run = process::command_output_with_timeout(
        Command::new(&binary).arg(&results),
        process::codegen_run_timeout(),
    )
    .unwrap();
    fs::write(directory.join("stdout.log"), &run.output.stdout).unwrap();
    fs::write(directory.join("stderr.log"), &run.output.stderr).unwrap();
    assert!(
        !run.timed_out && run.output.status.success(),
        "files={directory:?}: {} {}",
        String::from_utf8_lossy(&run.output.stdout),
        String::from_utf8_lossy(&run.output.stderr)
    );
    let marker = "PASS 163840 CG calls, 163840 assembly controls, 1280 word comparisons, 1639680 value/flag/word checks";
    assert_eq!(String::from_utf8_lossy(&run.output.stdout).trim(), marker);
    let states = fs::read(results).unwrap();
    assert_eq!(states.len(), 163840 * 5 * 8);
    let mut actual = states
        .as_chunks::<8>()
        .0
        .iter()
        .map(|bytes| u64::from_le_bytes(*bytes));
    let mut model_checks = 0;
    for (word, _, _, _, _) in cases {
        let decoded = DecodedConditionalSelect::decode(word).unwrap();
        for flags in 0..16 {
            for input in INPUTS {
                let mut state = RegisterState {
                    x: [0; 31],
                    sp: 0,
                    nzcv: flags,
                };
                state.x[..4].copy_from_slice(&input);
                let expected = decoded.execute(&state).unwrap();
                for value in expected.x[..4]
                    .iter()
                    .copied()
                    .chain([u64::from(expected.nzcv) << 28])
                {
                    assert_eq!(
                        actual.next().unwrap(),
                        value,
                        "word={word:08x}, flags={flags}, input={input:x?}, files={directory:?}"
                    );
                    model_checks += 1;
                }
            }
        }
    }
    assert!(actual.next().is_none());
    assert_eq!(model_checks, 819200);
    eprintln!(
        "{marker}; {model_checks} independent model/native state checks; evidence={directory:?}"
    );
}
