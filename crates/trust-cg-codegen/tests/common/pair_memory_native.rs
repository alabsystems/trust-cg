// Copyright 2026 Andrew Yates | Apache-2.0
//! Finite pair-memory oracle for AArch64 Linux GNU and macOS. SP starts at the bottom of an actual
//! allocated frame; there are no below-current-SP accesses or heap SP pivots.
//! Negative SP offsets, asynchronous stack behavior, atomicity, and SVE are not
//! native claims. Signed bounds are executed through ordinary X bases.

use super::*;
use sha2::{Digest, Sha256};
use std::{fmt::Write, fs, io::Read, path::Path, process::Command, time::Duration};

const SIZE: usize = 4096;
const PATTERNS: usize = 4;

#[derive(Clone, Copy, Debug)]
struct Case {
    op: Op,
    data: Data,
    rt: u16,
    rt2: u16,
    sp: bool,
    offset: i64,
}
impl Case {
    fn new_width(self) -> bool {
        matches!(self.op, Op::StpPreIndex | Op::LdpPostIndex)
            && matches!(self.data, Data::W | Data::S | Data::Q)
    }
}

fn cases(new_width: bool) -> Vec<Case> {
    let mut all = Vec::new();
    for (op, data) in profiles() {
        let mut transfers = if data.fp() {
            vec![(0, 1)]
        } else {
            vec![(9, 10), (31, 10), (9, 31)]
        };
        if !load(op) {
            if data.fp() {
                transfers.push((0, 0));
            } else {
                transfers.extend([(9, 9), (31, 31)]);
            }
        }
        for (rt, rt2) in transfers {
            for sp in [false, true] {
                let scale = data.bytes();
                let offsets = if !sp {
                    vec![-64 * scale, -scale, 0, scale, 63 * scale]
                } else if mode(op) == 2 {
                    vec![0, scale, 63 * scale]
                } else {
                    vec![0, 16, 63 * scale / 16 * 16]
                };
                for offset in offsets {
                    all.push(Case {
                        op,
                        data,
                        rt,
                        rt2,
                        sp,
                        offset,
                    });
                }
            }
        }
    }
    assert_eq!(all.len(), 424);
    // No writeback here: a GPR destination may alias the base. The wrapper
    // never dereferences the resulting base; the C oracle compares its bits.
    for op in [Op::StpRI, Op::LdpRI] {
        for data in [Data::W, Data::X] {
            for (rt, rt2) in [(0, 10), (9, 0)] {
                for scaled in [-64, -1, 0, 1, 63] {
                    all.push(Case {
                        op,
                        data,
                        rt,
                        rt2,
                        sp: false,
                        offset: scaled * data.bytes(),
                    });
                }
            }
        }
    }
    assert_eq!(all.len(), 464);
    let selected: Vec<_> = all
        .into_iter()
        .filter(|case| case.new_width() == new_width)
        .collect();
    assert_eq!(selected.len(), if new_width { 112 } else { 352 });
    selected
}

fn oracle(case: Case) -> String {
    let register = |n| {
        if !case.data.fp() && n == 31 {
            format!("{}zr", case.data.bank())
        } else {
            format!("{}{n}", case.data.bank())
        }
    };
    let mnemonic = if load(case.op) { "ldp" } else { "stp" };
    let base = if case.sp { "sp" } else { "x0" };
    let first = register(case.rt);
    let second = register(case.rt2);
    let offset = case.offset;
    match mode(case.op) {
        1 => format!("{mnemonic} {first},{second},[{base}],#{offset}"),
        2 => format!("{mnemonic} {first},{second},[{base},#{offset}]"),
        3 => format!("{mnemonic} {first},{second},[{base},#{offset}]!"),
        _ => unreachable!(),
    }
}

fn wrapper(assembly: &mut String, name: &str, case: Case, instruction: &str) {
    writeln!(
        assembly,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:"
    )
    .unwrap();
    if case.sp {
        // X6=caller SP, X7=frame bottom, X8=C buffer. All are caller-saved
        // and distinct from X9/X10 transfer lanes. Copy helpers use X11-X15.
        writeln!(assembly,"mov x6,sp\nsub sp,sp,#2,lsl #12\nmov x7,sp\nmov x8,x0\nmov x12,x8\nmov x13,x7\nmov x11,#256\n.L{name}_in:\nldp x14,x15,[x12],#16\nstp x14,x15,[x13],#16\nsubs x11,x11,#1\nb.ne .L{name}_in").unwrap();
    }
    if case.data.fp() {
        assembly.push_str("ldr q0,[x1]\nldr q1,[x1,#16]\n");
    } else {
        assembly.push_str("ldr x9,[x1]\nldr x10,[x1,#16]\n");
    }
    writeln!(assembly, ".global {name}_word\n{name}_word:\n{instruction}").unwrap();
    if case.sp {
        // Capture before restoring; all SP writeback profiles are nonnegative,
        // aligned and inside the allocated frame. No memory access intervenes.
        assembly.push_str("mov x5,sp\nmov sp,x7\nsub x5,x5,x7\nadd x5,x8,x5\n");
    } else {
        assembly.push_str("mov x5,x0\n");
    }
    for (position, rt) in [case.rt, case.rt2].into_iter().enumerate() {
        let output = position * 16;
        if case.data.fp() {
            writeln!(assembly, "str q{rt},[x2,#{output}]").unwrap();
        } else {
            // ZR has no stored state. Observe an independent seeded witness
            // register to ensure an ignored load did not alter another lane.
            let reg = if rt == 31 { 9 + position as u16 } else { rt };
            writeln!(assembly, "stp x{reg},xzr,[x2,#{output}]").unwrap();
        }
    }
    assembly.push_str("str x5,[x2,#32]\n");
    if case.sp {
        writeln!(assembly,"mov x12,x7\nmov x13,x8\nmov x11,#256\n.L{name}_out:\nldp x14,x15,[x12],#16\nstp x14,x15,[x13],#16\nsubs x11,x11,#1\nb.ne .L{name}_out\nmov sp,x6").unwrap();
    }
    writeln!(assembly, "ret\n.size {name},.-{name}").unwrap();
}

fn snapshot(directory: &Path) {
    let mut rows = Vec::new();
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.file_name().unwrap() == "SHA256SUMS" {
            continue;
        }
        assert!(fs::symlink_metadata(&path).unwrap().is_file());
        let mut input = fs::File::open(&path).unwrap();
        let mut hash = Sha256::new();
        let mut buffer = [0; 65536];
        loop {
            let n = input.read(&mut buffer).unwrap();
            if n == 0 {
                break;
            }
            hash.update(&buffer[..n]);
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

fn command(
    directory: &Path,
    label: &str,
    cmd: &mut Command,
    bound: Duration,
) -> Result<process::TimedCommandOutput, String> {
    fs::write(
        directory.join(format!("{label}.argv")),
        format!("{cmd:?}\ntimeout={bound:?}\n"),
    )
    .unwrap();
    let result = process::command_output_with_timeout(cmd, bound);
    match &result {
        Ok(out) => {
            fs::write(
                directory.join(format!("{label}.stdout")),
                &out.output.stdout,
            )
            .unwrap();
            fs::write(
                directory.join(format!("{label}.stderr")),
                &out.output.stderr,
            )
            .unwrap();
            fs::write(
                directory.join(format!("{label}.status")),
                format!(
                    "status={}\ntimed_out={}\n",
                    out.output.status, out.timed_out
                ),
            )
            .unwrap();
        }
        Err(error) => {
            fs::write(
                directory.join(format!("{label}.spawn-error")),
                error.to_string(),
            )
            .unwrap();
        }
    }
    snapshot(directory);
    result.map_err(|error| error.to_string())
}

pub fn run(new_width: bool) {
    // Host gate, constant by design: `cfg!` fixes the compile target, so clippy sees a
    // constant where this harness needs a runtime refusal.
    #[allow(clippy::assertions_on_constants)]
    {
        assert!(cfg!(target_endian = "little"));
    }
    let category = if new_width { "new-width" } else { "parent" };
    let directory_scratch = crate::fresh_dir::create(&format!("trust-cg-pair-memory-{category}-"));
    let directory = directory_scratch.to_path_buf();
    eprintln!("pair native evidence={directory:?}");
    fs::write(
        directory.join("portable-fixture.rs"),
        include_bytes!("../aarch64_pair_memory_decode.rs"),
    )
    .unwrap();
    fs::write(
        directory.join("native-fixture.rs"),
        include_bytes!("pair_memory_native.rs"),
    )
    .unwrap();
    let cases = cases(new_width);
    let count = cases.len();
    let calls = count * PATTERNS;
    let checks = calls * 2 * (SIZE + 72);
    let mut admission = String::from("case\top\tdata\trt\trt2\tsp\toffset\texpected\tactual\n");
    let mut assembly = String::from(".text\n");
    let mut driver = String::from(DRIVER);
    let mut rows = Vec::new();
    let (mut refused, mut wrong) = (0, 0);
    let mut failures = Vec::new();
    for (id, case) in cases.into_iter().enumerate() {
        let rn = if case.sp { 31 } else { 0 };
        assert!(legal_fields(case.op, case.data, case.rt, case.rt2, rn));
        let intent = inst(case.op, case.data, case.rt, case.rt2, rn, Some(case.offset));
        let expected = word(case.op, case.data, case.rt, case.rt2, rn, case.offset);
        let encoded = encode_instruction(&intent);
        writeln!(
            admission,
            "{id}\t{:?}\t{:?}\t{}\t{}\t{}\t{}\t{expected:08x}\t{encoded:?}",
            case.op, case.data, case.rt, case.rt2, case.sp, case.offset
        )
        .unwrap();
        match encoded {
            Ok(bits) if bits == expected => {
                wrapper(
                    &mut assembly,
                    &format!("g{id}"),
                    case,
                    &format!(".inst 0x{bits:08x}"),
                );
                wrapper(&mut assembly, &format!("a{id}"), case, &oracle(case));
                writeln!(driver,"extern void g{id}(unsigned char*,const unsigned char*,struct Snapshot*); extern void a{id}(unsigned char*,const unsigned char*,struct Snapshot*); extern const uint32_t g{id}_word[],a{id}_word[];").unwrap();
                rows.push(format!("{{g{id},a{id},g{id}_word,a{id}_word,0x{expected:08x}u,{},{},{},{},{},{},{},{}}}",case.data.bytes(),u8::from(case.data.fp()),u8::from(load(case.op)),mode(case.op),case.rt,case.rt2,u8::from(case.sp),case.offset));
            }
            other => {
                if other.is_err() {
                    refused += 1;
                } else {
                    wrong += 1;
                }
                if failures.len() < 16 {
                    failures.push(format!("case{id} {intent:?}: {other:?}"));
                }
            }
        }
    }
    fs::write(directory.join("admission.tsv"), admission).unwrap();
    fs::write(directory.join("admission.status"),format!("category={category}\nattempted={count}\naccepted={}\nrefused={refused}\nwrong_word={wrong}\n",rows.len())).unwrap();
    // All requested encodings are attempted before this failure. The separate
    // parent test remains independently runnable when new widths are refused.
    snapshot(&directory);
    eprintln!(
        "PAIR_NATIVE_ADMISSION category={category} attempted={count} accepted={} refused={refused} wrong_word={wrong}",
        rows.len()
    );
    assert_eq!(
        rows.len(),
        count,
        "native admission failure; evidence={directory:?}\n{}",
        failures.join("\n")
    );
    assembly.push_str(".section .note.GNU-stack,\"\",%progbits\n");
    writeln!(driver,"static const struct Case cases[]={{ {} }};\n#define CASE_COUNT {count}\n#define CALL_COUNT {calls}\n#define CHECK_COUNT {checks}",rows.join(",\n")).unwrap();
    driver.push_str(MAIN);
    fs::write(directory.join("words.S"), native_host::assembly(&assembly)).unwrap();
    fs::write(directory.join("driver.c"), driver).unwrap();
    snapshot(&directory);
    let executable = directory.join("native");
    let link = command(
        &directory,
        "link",
        Command::new("cc")
            .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
            .arg(directory.join("driver.c"))
            .arg(directory.join("words.S"))
            .arg("-o")
            .arg(&executable),
        process::codegen_link_timeout(),
    )
    .expect("required link launch");
    assert!(
        !link.timed_out
            && link.output.status.code() == Some(0)
            && link.output.stdout.is_empty()
            && link.output.stderr.is_empty(),
        "link failed; {directory:?}: {}",
        String::from_utf8_lossy(&link.output.stderr)
    );
    let normal = command(
        &directory,
        "native",
        &mut Command::new(&executable),
        process::codegen_run_timeout(),
    );
    let mut may_continue =
        matches!(&normal,Ok(out) if !out.timed_out && out.output.status.code().is_some());
    let mut results = Vec::new();
    // Normal wrong-answer exits still run all poison controls. An incomplete
    // process supplies no assurance of cleanup; record remaining controls unrun.
    for label in [
        "poison-first",
        "poison-second",
        "poison-base",
        "poison-memory",
    ] {
        let result = if may_continue {
            command(
                &directory,
                label,
                Command::new(&executable).arg(format!("--{label}")),
                process::codegen_run_timeout(),
            )
        } else {
            fs::write(
                directory.join(format!("{label}.unrun")),
                "prior process did not complete with an observed normal exit\n",
            )
            .unwrap();
            Err("prior abnormal/incomplete process".into())
        };
        may_continue =
            matches!(&result,Ok(out) if !out.timed_out && out.output.status.code().is_some());
        results.push((label, result));
    }
    let expected = format!(
        "PAIR_MEMORY_NATIVE cases={count} cg_calls={calls} asm_calls={calls} words={} checks={checks} cg_mismatches=0 asm_mismatches=0\n",
        count * 2
    );
    match normal {
        Ok(out)
            if !out.timed_out
                && out.output.status.code() == Some(0)
                && out.output.stdout == expected.as_bytes()
                && out.output.stderr.is_empty() => {}
        _ => failures.push("normal native result did not match full successful census".into()),
    }
    for (label, result) in results {
        let marker = match label {
            "poison-first" => "EXPECTED_FIRST_MISMATCH case=0 route=0 byte=0\n",
            "poison-second" => "EXPECTED_SECOND_MISMATCH case=0 route=0 byte=0\n",
            "poison-base" => "EXPECTED_BASE_MISMATCH case=0 route=0\n",
            "poison-memory" => "EXPECTED_MEMORY_MISMATCH case=0 route=0 byte=1792\n",
            _ => unreachable!(),
        };
        match result {
            Ok(out)
                if !out.timed_out
                    && out.output.status.code() == Some(97)
                    && out.output.stdout.is_empty()
                    && out.output.stderr == marker.as_bytes() => {}
            _ => failures.push(format!("{label}: exact normal97 control failed")),
        }
    }
    snapshot(&directory);
    assert!(
        failures.is_empty(),
        "evidence={directory:?}\n{}",
        failures.join("\n")
    );
}

const DRIVER: &str = r#"
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#define SIZE 4096
struct Snapshot { unsigned char first[16],second[16]; uint64_t base; };
struct Output { unsigned char before[16]; struct Snapshot data; unsigned char after[16]; };
_Static_assert(sizeof(struct Snapshot)==40 && offsetof(struct Snapshot,base)==32,"snapshot layout");
_Static_assert(sizeof(struct Output)==72 && offsetof(struct Output,data)==16 && offsetof(struct Output,after)==56,"output canary layout");
typedef void (*Fn)(unsigned char*,const unsigned char*,struct Snapshot*);
struct Case { Fn cg,oracle; const uint32_t *cg_word,*asm_word; uint32_t word; unsigned bytes,fp,load,mode,rt,rt2,sp; int offset; };
static _Alignas(16) unsigned char buffers[2][SIZE],expected[SIZE],seed[32];
static unsigned long calls[2],mismatches[2],checks,words;
static uint64_t read_le(const unsigned char *p,unsigned n) { uint64_t v=0;for(unsigned j=0;j<n;++j)v|=(uint64_t)p[j]<<(8*j);return v; }
static void write_le(unsigned char *p,uint64_t v,unsigned n) {for(unsigned j=0;j<n;++j)p[j]=(unsigned char)(v>>(8*j));}
static uint64_t gpr_input(unsigned reg,unsigned position,uint64_t base) {
    if(reg==0)return base;
    if(reg==31)reg=9+position; /* independent witness for discarded zero lane */
    return read_le(seed+(reg==9?0:16),8);
}
"#;

const MAIN: &str = r#"
int main(int argc,char **argv) {
    const int pfirst=argc==2 && strcmp(argv[1],"--poison-first")==0;
    const int psecond=argc==2 && strcmp(argv[1],"--poison-second")==0;
    const int pbase=argc==2 && strcmp(argv[1],"--poison-base")==0;
    const int pmemory=argc==2 && strcmp(argv[1],"--poison-memory")==0;
    const int poison=pfirst||psecond||pbase||pmemory;
    if(argc!=1 && !poison)return 96;
    if(sizeof(cases)/sizeof(cases[0])!=CASE_COUNT)return 98;
    const unsigned char edges[]={0,0x7f,0x80,0xff};
    for(size_t i=0;i<CASE_COUNT;++i) {
        const struct Case *c=&cases[i];
        if(*c->cg_word!=c->word || *c->asm_word!=c->word)return 95;
        words+=2;
        const int base=c->sp?0:2048;
        const int address=base+(c->mode==1?0:c->offset);
        const int updated=base+(c->mode==2?0:c->offset);
        if(c->bytes>16 || c->bytes<4 || (!c->fp && c->bytes>8) || address<0 || address+(int)(2*c->bytes)>SIZE-16 || updated<0 || updated>SIZE-16)return 98;
        if(c->sp && c->mode!=2 && c->offset%16!=0)return 98;
        for(unsigned pattern=0;pattern<4;++pattern) {
            for(unsigned j=0;j<32;++j)seed[j]=(unsigned char)(0x91+j*29+pattern*43);
            for(unsigned route=0;route<2;++route) {
                unsigned char *buffer=buffers[route];
                for(unsigned j=0;j<SIZE;++j)expected[j]=(unsigned char)((j*37+pattern*71)^(j>>3));
                for(unsigned j=0;j<2*c->bytes;++j)expected[address+j]=(unsigned char)(edges[pattern]^(j*47));
                memcpy(buffer,expected,SIZE);
                struct Output wanted,actual;memset(&wanted,0xa6,sizeof(wanted));memset(&actual,0xa6,sizeof(actual));
                memset(&wanted.data,0,sizeof(wanted.data));wanted.data.base=(uint64_t)(uintptr_t)(buffer+updated);
                const unsigned regs[]={c->rt,c->rt2};
                for(unsigned position=0;position<2;++position) {
                    unsigned char *out=position?wanted.data.second:wanted.data.first;
                    const unsigned reg=regs[position];const unsigned at=(unsigned)address+position*c->bytes;
                    if(c->fp) {
                        memcpy(out,seed+reg*16,16);
                        if(c->load){memset(out,0,16);memcpy(out,expected+at,c->bytes);}
                        else memcpy(expected+at,seed+reg*16,c->bytes);
                    } else {
                        const uint64_t input=gpr_input(reg,position,(uint64_t)(uintptr_t)(buffer+base));
                        uint64_t value=input;
                        if(c->load && reg!=31)value=read_le(expected+at,c->bytes);
                        if(!c->load)write_le(expected+at,reg==31?0:input,c->bytes);
                        write_le(out,value,8);
                        if(c->load && c->mode==2 && reg==0)wanted.data.base=value;
                    }
                }
                if(i==0 && pattern==0 && route==0) {
                    if(pfirst)wanted.data.first[0]^=1;
                    if(psecond)wanted.data.second[0]^=1;
                    if(pbase)wanted.data.base^=1;
                    if(pmemory)expected[address]^=1;
                }
                const Fn fn=route?c->oracle:c->cg;fn(buffer+base,seed,&actual.data);++calls[route];
                const unsigned char *a=(const unsigned char*)&actual,*w=(const unsigned char*)&wanted;
                unsigned bad=0,first=0,mbad=0,mfirst=0;
                for(unsigned j=0;j<72;++j){++checks;if(a[j]!=w[j]){if(!bad)first=j;++bad;}}
                for(unsigned j=0;j<SIZE;++j){++checks;if(buffer[j]!=expected[j]){if(!mbad)mfirst=j;++mbad;}}
                if(bad||mbad) {
                    if(poison && i==0 && pattern==0 && route==0) {
                        if(bad==1 && mbad==0 && pfirst && first==16){fprintf(stderr,"EXPECTED_FIRST_MISMATCH case=0 route=0 byte=0\n");return 97;}
                        if(bad==1 && mbad==0 && psecond && first==32){fprintf(stderr,"EXPECTED_SECOND_MISMATCH case=0 route=0 byte=0\n");return 97;}
                        if(bad==1 && mbad==0 && pbase && first==48){fprintf(stderr,"EXPECTED_BASE_MISMATCH case=0 route=0\n");return 97;}
                        if(bad==0 && mbad==1 && pmemory && mfirst==(unsigned)address){fprintf(stderr,"EXPECTED_MEMORY_MISMATCH case=0 route=0 byte=%u\n",mfirst);return 97;}
                    }
                    ++mismatches[route];fprintf(stderr,"PAIR_MISMATCH case=%zu pattern=%u route=%u state_bytes=%u first=%u memory_bytes=%u first=%u\n",i,pattern,route,bad,first,mbad,mfirst);
                }
            }
        }
    }
    if(poison || calls[0]!=CALL_COUNT || calls[1]!=CALL_COUNT || checks!=CHECK_COUNT || words!=CASE_COUNT*2)return 98;
    printf("PAIR_MEMORY_NATIVE cases=%u cg_calls=%lu asm_calls=%lu words=%lu checks=%lu cg_mismatches=%lu asm_mismatches=%lu\n",CASE_COUNT,calls[0],calls[1],words,checks,mismatches[0],mismatches[1]);
    return mismatches[0]||mismatches[1]?1:0;
}
"#;
