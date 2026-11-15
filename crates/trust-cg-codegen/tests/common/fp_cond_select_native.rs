// Copyright 2026 Andrew Yates | Apache-2.0
//! Native FCSEL word/assembler/C controls; no source or proof authority.
//! All V registers are observed, including upper lanes and ordinary V31 data.

use super::{native_host, process};
use sha2::{Digest, Sha256};
use std::{fmt::Write, fs, io::Read, path::Path, process::Command};
use trust_cg_codegen::{
    aarch64::{decode_check::A64DecodeCheck, encode::encode_instruction},
    decode_check::{DecodeCheck, DecodeCheckOutcome},
};
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, regs::PReg};

const LAYOUTS: [[u16; 3]; 12] = [
    [0, 1, 2],
    [1, 1, 2],
    [2, 1, 2],
    [0, 1, 1],
    [1, 1, 1],
    [31, 1, 2],
    [0, 31, 2],
    [0, 1, 31],
    [31, 31, 31],
    [8, 9, 15],
    [15, 8, 9],
    [30, 16, 29],
];

fn hash_artifacts(directory: &Path) {
    let mut rows = Vec::new();
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.file_name().unwrap() == "SHA256SUMS" {
            continue;
        }
        let mut input = fs::File::open(&path).unwrap();
        let mut hash = Sha256::new();
        let mut buffer = [0; 65536];
        loop {
            let bytes = input.read(&mut buffer).unwrap();
            if bytes == 0 {
                break;
            }
            hash.update(&buffer[..bytes]);
        }
        rows.push(format!(
            "{:x}  {}\n",
            hash.finalize(),
            path.file_name().unwrap().to_str().unwrap()
        ));
    }
    rows.sort();
    fs::write(directory.join("SHA256SUMS"), rows.concat()).unwrap();
}

fn thunk(output: &mut String, name: &str, operation: &str) {
    // x0 points to state; x1/x2/x3 supply NZCV/FPCR/FPSR. All V registers
    // are loaded before the single measured instruction and then observed.
    // Preserve the caller's full Q8-Q15 and FP controls; no callee-saved GPR
    // is touched. The 128-byte frame retains AAPCS64's 16-byte alignment.
    writeln!(
        output,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\nsub sp,sp,#128"
    )
    .unwrap();
    for pair in 0..4 {
        writeln!(
            output,
            "stp q{},q{},[sp,#{}]",
            8 + pair * 2,
            9 + pair * 2,
            pair * 32
        )
        .unwrap();
    }
    output.push_str("mrs x4,fpcr\nmrs x5,fpsr\nmov x6,sp\nstr x6,[x0,#536]\nmsr fpcr,x2\nmsr fpsr,x3\nisb\nmsr nzcv,x1\n");
    for pair in 0..16 {
        writeln!(
            output,
            "ldp q{},q{},[x0,#{}]",
            pair * 2,
            pair * 2 + 1,
            pair * 32
        )
        .unwrap();
    }
    writeln!(output, ".global {name}_word\n{name}_word:\n{operation}").unwrap();
    for pair in 0..16 {
        writeln!(
            output,
            "stp q{},q{},[x0,#{}]",
            pair * 2,
            pair * 2 + 1,
            pair * 32
        )
        .unwrap();
    }
    output.push_str("mrs x1,nzcv\nstr x1,[x0,#512]\nmrs x1,fpcr\nstr x1,[x0,#520]\nmrs x1,fpsr\nstr x1,[x0,#528]\nmov x1,sp\nstr x1,[x0,#544]\nmsr fpcr,x4\nmsr fpsr,x5\nisb\n");
    for pair in 0..4 {
        writeln!(
            output,
            "ldp q{},q{},[sp,#{}]",
            8 + pair * 2,
            9 + pair * 2,
            pair * 32
        )
        .unwrap();
    }
    writeln!(output, "add sp,sp,#128\nret\n.size {name},.-{name}").unwrap();
}

#[test]
fn fp_select_native_bits_all_conditions_aliases_and_preserved_state() {
    let directory_scratch = crate::fresh_dir::create("trust-cg-fcsel-native-");
    let directory = directory_scratch.to_path_buf();
    let mut assembly = String::from(".text\n");
    let mut driver = String::from(
        r#"
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
struct state {uint64_t q[32][2],nzcv,fpcr,fpsr,sp_before,sp_after;};
_Static_assert(offsetof(struct state,nzcv)==512,"state layout");
_Static_assert(offsetof(struct state,sp_before)==536,"SP layout");
_Static_assert(sizeof(struct state)==552,"state size");
typedef void (*function_t)(struct state*,uint64_t,uint64_t,uint64_t);
struct test_case {function_t cg,as;const uint32_t*cw,*aw;unsigned width,cc,d,n,m;};
static uint64_t checks,failures,calls,controls,words;
static void check(uint64_t got,uint64_t expected) {
 checks++;if(got!=expected){if(failures<8)fprintf(stderr,"check%llu: got%llx expected%llx\n",(unsigned long long)checks,(unsigned long long)got,(unsigned long long)expected);failures++;}
}
static unsigned holds(unsigned cc,unsigned flags) {
 unsigned n=(flags>>3)&1,z=(flags>>2)&1,c=(flags>>1)&1,v=flags&1;
 switch(cc){case 0:return z;case 1:return !z;case 2:return c;case 3:return !c;
 case 4:return n;case 5:return !n;case 6:return v;case 7:return !v;
 case 8:return c&&!z;case 9:return !c||z;case 10:return n==v;case 11:return n!=v;
 case 12:return !z&&(n==v);case 13:return z||(n!=v);case 14:case 15:return 1;default:return 0;}
}
static const uint64_t fp32[]={0,0x80000000,1,0x80000001,0x007fffff,0x00800000,0x3f800000,0xbf800000,0x7f7fffff,0x7f800000,0xff800000,0x7fc12345,0xffc23456,0x7f812345,0xff812346,0xffffffff};
static const uint64_t fp64[]={0,0x8000000000000000ULL,1,0x8000000000000001ULL,0x000fffffffffffffULL,0x0010000000000000ULL,0x3ff0000000000000ULL,0xbff0000000000000ULL,0x7fefffffffffffffULL,0x7ff0000000000000ULL,0xfff0000000000000ULL,0x7ff8123456789abcULL,0xfff823456789abcdULL,0x7ff0123456789abcULL,0xfff0123456789abdULL,0xffffffffffffffffULL};
static const uint64_t control_modes[]={0,0x03400000,0x02800000,0x01c00000};
"#,
    );
    let mut cases = Vec::new();
    for width in [32, 64] {
        for cc in 0..16 {
            for [d, n, m] in LAYOUTS {
                let base = if width == 32 { 128 } else { 96 };
                let inst = MachInst::new(
                    AArch64Opcode::FcselRR,
                    vec![
                        MachOperand::PReg(PReg::new(base + d)),
                        MachOperand::PReg(PReg::new(base + n)),
                        MachOperand::PReg(PReg::new(base + m)),
                        MachOperand::Imm(cc),
                    ],
                );
                let word = encode_instruction(&inst).unwrap();
                assert!(matches!(
                    A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ));
                let i = cases.len();
                thunk(
                    &mut assembly,
                    &format!("cg{i}"),
                    &format!(".inst 0x{word:08x}"),
                );
                let reg = if width == 32 { 's' } else { 'd' };
                let cond = [
                    "eq", "ne", "cs", "cc", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt",
                    "le", "al", "nv",
                ][cc as usize];
                thunk(
                    &mut assembly,
                    &format!("as{i}"),
                    &format!("fcsel {reg}{d},{reg}{n},{reg}{m},{cond}"),
                );
                writeln!(driver, "extern void cg{i}(struct state*,uint64_t,uint64_t,uint64_t),as{i}(struct state*,uint64_t,uint64_t,uint64_t);extern const uint32_t cg{i}_word[],as{i}_word[];").unwrap();
                cases.push((width, cc, d, n, m));
            }
        }
    }
    assert_eq!(cases.len(), 384);
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    driver.push_str("static const struct test_case cases[]={\n");
    for (i, (width, cc, d, n, m)) in cases.iter().enumerate() {
        writeln!(
            driver,
            "{{cg{i},as{i},cg{i}_word,as{i}_word,{width},{cc},{d},{n},{m}}},"
        )
        .unwrap();
    }
    driver.push_str(r#"
};
int main(int argc,char**argv) {
 if(argc!=2)return 2;FILE*out=fopen(argv[1],"wb");if(!out)return 3;
 for(unsigned i=0;i<384;i++) {
  const struct test_case*t=&cases[i];const uint64_t*bits=t->width==32?fp32:fp64;
  check(*t->cw,*t->aw);words++;
  for(unsigned f=0;f<16;f++)for(unsigned p=0;p<16;p++)for(unsigned mode=0;mode<4;mode++) {
   struct state cg={0},as={0},expected={0};
   for(unsigned r=0;r<32;r++) {
    expected.q[r][0]=bits[(p+5*r)%16];
    if(t->width==32)expected.q[r][0]|=(0xa5a50000ULL+r)<<32;
    expected.q[r][1]=0xfedcba9876543210ULL^((uint64_t)r<<32)^p;
   }
   cg=as=expected;
   unsigned source=holds(t->cc,f)?t->n:t->m;
   uint64_t result=expected.q[source][0];if(t->width==32)result=(uint32_t)result;
   expected.q[t->d][0]=result;expected.q[t->d][1]=0;
   expected.nzcv=(uint64_t)f<<28;expected.fpcr=control_modes[mode];
   expected.fpsr=(p&1)?0x0800009f:0;
   t->cg(&cg,expected.nzcv,expected.fpcr,expected.fpsr);calls++;
   t->as(&as,expected.nzcv,expected.fpcr,expected.fpsr);controls++;
   for(unsigned r=0;r<32;r++)for(unsigned half=0;half<2;half++){check(cg.q[r][half],expected.q[r][half]);check(as.q[r][half],expected.q[r][half]);}
   check(cg.nzcv,expected.nzcv);check(as.nzcv,expected.nzcv);
   check(cg.fpcr,expected.fpcr);check(as.fpcr,expected.fpcr);
   check(cg.fpsr,expected.fpsr);check(as.fpsr,expected.fpsr);
   check(cg.sp_after,cg.sp_before);check(as.sp_after,as.sp_before);
   check(cg.sp_before&15,0);check(as.sp_before&15,0);
   if(fwrite(&cg,sizeof(cg),1,out)!=1)return 4;
  }
 }
 if(fclose(out))return 5;
 if(calls!=393216||controls!=393216||words!=384||checks!=54264192||failures){fprintf(stderr,"calls%llu controls%llu words%llu checks%llu failures%llu\n",(unsigned long long)calls,(unsigned long long)controls,(unsigned long long)words,(unsigned long long)checks,(unsigned long long)failures);return 1;}
 puts("PASS 393216 CG calls, 393216 assembly controls, 384 word comparisons, 54264192 state checks");return 0;
}
"#);
    fs::write(
        directory.join("controls.S"),
        native_host::assembly(&assembly),
    )
    .unwrap();
    fs::write(directory.join("driver.c"), driver).unwrap();
    let binary = directory.join("run");
    let mut link = Command::new("cc");
    link.args(["-O2", "-Werror"])
        .args(native_host::link_hardening_args())
        .arg(directory.join("driver.c"))
        .arg(directory.join("controls.S"))
        .arg("-o")
        .arg(&binary);
    fs::write(
        directory.join("link.command"),
        format!("{link:?}\ntimeout={:?}\n", process::codegen_link_timeout()),
    )
    .unwrap();
    let built =
        process::command_output_with_timeout(&mut link, process::codegen_link_timeout()).unwrap();
    fs::write(directory.join("build.stdout.log"), &built.output.stdout).unwrap();
    fs::write(directory.join("build.stderr.log"), &built.output.stderr).unwrap();
    hash_artifacts(&directory);
    assert!(
        !built.timed_out && built.output.status.success(),
        "files={directory:?}: {}",
        String::from_utf8_lossy(&built.output.stderr)
    );
    let mut command = Command::new(&binary);
    command.arg(directory.join("states.bin"));
    fs::write(
        directory.join("run.command"),
        format!(
            "{command:?}\ntimeout={:?}\n",
            process::codegen_run_timeout()
        ),
    )
    .unwrap();
    let run =
        process::command_output_with_timeout(&mut command, process::codegen_run_timeout()).unwrap();
    fs::write(directory.join("stdout.log"), &run.output.stdout).unwrap();
    fs::write(directory.join("stderr.log"), &run.output.stderr).unwrap();
    hash_artifacts(&directory);
    assert!(
        !run.timed_out && run.output.status.success(),
        "files={directory:?}: {}",
        String::from_utf8_lossy(&run.output.stderr)
    );
    let marker = "PASS 393216 CG calls, 393216 assembly controls, 384 word comparisons, 54264192 state checks";
    assert_eq!(String::from_utf8_lossy(&run.output.stdout).trim(), marker);
    assert_eq!(
        fs::metadata(directory.join("states.bin")).unwrap().len(),
        393216 * 552
    );
    eprintln!("{marker}; evidence={directory:?}");
}
