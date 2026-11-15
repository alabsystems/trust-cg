// Copyright 2026 Andrew Yates | Apache-2.0
//! Fixed AArch64 narrow-register-offset native controls (Linux GNU and macOS).
//! This helper is copied to tests/common only after review. It checks emitted
//! words against independent assembler output and C byte/state semantics; it does
//! not establish spill execution, source refinement, or proof authority.

use sha2::{Digest, Sha256};
use std::{fmt::Write, fs, io::Read, path::Path, process::Command, time::Duration};
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_ir::{
    AArch64Opcode as Op, MachInst, MachOperand as Arg,
    regs::{self, PReg},
};

#[path = "rosetta.rs"]
mod process;

#[path = "native_host.rs"]
mod native_host;

const CASES: usize = 720;
const CALLS: usize = CASES * 4 * 4;
const CHECKS: usize = CASES * 2 + CALLS * 2 * (1024 + 16 + 2);
const MODES: [Option<i64>; 9] = [
    None,
    Some(4),
    Some(5),
    Some(6),
    Some(7),
    Some(12),
    Some(13),
    Some(14),
    Some(15),
];

fn snapshot(directory: &Path) {
    let mut rows = Vec::new();
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.file_name().unwrap() == "SHA256SUMS" {
            continue;
        }
        assert!(path.symlink_metadata().unwrap().file_type().is_file());
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

fn run_command(
    directory: &Path,
    label: &str,
    command: &mut Command,
    bound: Duration,
) -> Result<process::TimedCommandOutput, String> {
    fs::write(
        directory.join(format!("{label}.argv")),
        format!("{command:?}\ntimeout={bound:?}\n"),
    )
    .unwrap();
    fs::write(
        directory.join(format!("{label}.status")),
        "state=attempting\n",
    )
    .unwrap();
    let result = process::command_output_with_timeout(command, bound);
    match result {
        Ok(result) => {
            fs::write(
                directory.join(format!("{label}.stdout")),
                &result.output.stdout,
            )
            .unwrap();
            fs::write(
                directory.join(format!("{label}.stderr")),
                &result.output.stderr,
            )
            .unwrap();
            fs::write(
                directory.join(format!("{label}.status")),
                format!(
                    "state=returned\nstatus={}\ncode={:?}\ntimed_out={}\n",
                    result.output.status,
                    result.output.status.code(),
                    result.timed_out,
                ),
            )
            .unwrap();
            snapshot(directory);
            Ok(result)
        }
        Err(error) => {
            let detail = format!("{error}");
            fs::write(
                directory.join(format!("{label}.status")),
                format!("state=spawn-or-capture-error\nerror={detail}\n"),
            )
            .unwrap();
            snapshot(directory);
            Err(detail)
        }
    }
}

#[derive(Clone, Copy)]
struct Case {
    load: bool,
    bytes: u8,
    wide: bool,
    zero: bool,
    sp: bool,
    mode: Option<i64>,
    index_zero: bool,
    alias: u8, // 0 distinct, 1 Rt=Rn, 2 Rt=Rm; no writeback or alias ban.
}

fn cases() -> Vec<Case> {
    let mut rows = Vec::new();
    for load in [false, true] {
        for bytes in [1, 2] {
            for wide in [false, true] {
                for zero in [false, true] {
                    for sp in [false, true] {
                        for mode in MODES {
                            for index_zero in [false, true] {
                                rows.push(Case {
                                    load,
                                    bytes,
                                    wide,
                                    zero,
                                    sp,
                                    mode,
                                    index_zero,
                                    alias: 0,
                                });
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(rows.len(), 576);
    for load in [false, true] {
        for bytes in [1, 2] {
            for wide in [false, true] {
                for alias in [1, 2] {
                    for mode in MODES {
                        rows.push(Case {
                            load,
                            bytes,
                            wide,
                            zero: false,
                            sp: false,
                            mode,
                            index_zero: false,
                            alias,
                        });
                    }
                }
            }
        }
    }
    assert_eq!(rows.len(), CASES);
    assert_eq!(rows.iter().filter(|row| row.sp).count(), 288);
    assert_eq!(rows.iter().filter(|row| row.alias != 0).count(), 144);
    rows
}

fn register(wide: bool, field: u16) -> PReg {
    assert!(field < 32);
    if field == 31 {
        if wide { regs::XZR } else { regs::WZR }
    } else {
        PReg::new(if wide { field } else { 32 + field })
    }
}

fn opcode(case: Case) -> Op {
    match (case.load, case.bytes) {
        (false, 1) => Op::StrbRO,
        (false, 2) => Op::StrhRO,
        (true, 1) => Op::LdrbRO,
        (true, 2) => Op::LdrhRO,
        _ => unreachable!(),
    }
}

fn intent(case: Case, rt: u16, rn: u16, rm: u16) -> MachInst {
    let low32 = matches!(case.mode.unwrap_or(6), 4 | 5 | 12 | 13);
    let mut operands = vec![
        Arg::PReg(register(case.wide, rt)),
        Arg::PReg(PReg::new(rn)),
        Arg::PReg(register(!low32, rm)),
    ];
    if let Some(mode) = case.mode {
        operands.push(Arg::Imm(mode));
    }
    MachInst::new(opcode(case), operands)
}

fn expected_word(case: Case, rt: u16, rn: u16, rm: u16) -> u32 {
    // Arm A64 2025-03 pp520/524/917/922; no encoder field helper is reused.
    let fixed = match (case.load, case.bytes) {
        (false, 1) => 0x3820_0800,
        (false, 2) => 0x7820_0800,
        (true, 1) => 0x3860_0800,
        (true, 2) => 0x7860_0800,
        _ => unreachable!(),
    };
    let mode = case.mode.unwrap_or(6) as u32;
    assert!(matches!(mode, 4 | 5 | 6 | 7 | 12 | 13 | 14 | 15));
    fixed
        | (u32::from(rm) << 16)
        | ((mode >> 1) << 13)
        | ((mode & 1) << 12)
        | (u32::from(rn) << 5)
        | u32::from(rt)
}

fn oracle(case: Case, rt: u16) -> String {
    let mnemonic = match (case.load, case.bytes) {
        (false, 1) => "strb",
        (false, 2) => "strh",
        (true, 1) => "ldrb",
        (true, 2) => "ldrh",
        _ => unreachable!(),
    };
    // Both MachineIR W/X carrier spellings denote the opcode's byte/halfword
    // transfer; architectural assembly always uses Wt (or WZR), never Xt.
    let target = if case.zero {
        "wzr".to_string()
    } else {
        format!("w{rt}")
    };
    let base = if case.sp { "sp" } else { "x0" };
    let mode = case.mode.unwrap_or(6);
    let option = mode >> 1;
    let bank = if option == 2 || option == 6 { 'w' } else { 'x' };
    let index = if case.index_zero {
        format!("{bank}zr")
    } else {
        format!("{bank}4")
    };
    let extension = match option {
        2 => "uxtw",
        3 => "lsl",
        6 => "sxtw",
        7 => "sxtx",
        _ => unreachable!(),
    };
    // In LDRB/STRB S=0 means omitted amount, S=1 means explicit #0.
    // Omitting the LSL clause selects option=3/S=0. Other extensions remain
    // explicit but omit their amount. Halfword S=1 instead spells #1.
    let suffix = if mode & 1 == 0 {
        if option == 3 {
            String::new()
        } else {
            format!(",{extension}")
        }
    } else {
        format!(",{extension} #{}", case.bytes - 1)
    };
    format!("{mnemonic} {target},[{base},{index}{suffix}]")
}

fn wrapper(assembly: &mut String, prefix: char, id: usize, case: Case, rt: u16, instruction: &str) {
    let name = format!("{prefix}{id}");
    // void f(base=x0, raw_index=x1, seed=x2, Snapshot*=x3).
    // Only caller-saved x0/x4-x17 change. No BL, LR, callee-saved GPR or SIMD
    // register changes; the explicit output pointer avoids aggregate-return ABI.
    writeln!(
        assembly,
        ".p2align 2\n.global {name}\n.type {name},%function\n{name}:\nmov x4,x1\nldr x9,[x2]"
    )
    .unwrap();
    if case.sp {
        // All SP addresses are nonnegative within this live aligned 2KiB
        // allocation; negative signed offsets use an ordinary X base instead.
        writeln!(assembly, "mov x10,sp\nsub sp,sp,#2048\nmov x11,sp\nmov x12,x0\nmov x13,x12\nmov x14,x11\nmov x15,#64\n.L{name}_in:\nldp x16,x17,[x13],#16\nstp x16,x17,[x14],#16\nsubs x15,x15,#1\nb.ne .L{name}_in").unwrap();
    }
    writeln!(assembly, ".global {name}_word\n{name}_word:\n{instruction}").unwrap();
    if case.sp {
        // Capture actual SP, restore frame SP before copying the full buffer
        // back, then restore the caller's exact SP before returning.
        writeln!(assembly, "mov x5,sp\nmov sp,x11\nsub x5,x5,x11\nadd x5,x12,x5\nmov x13,x11\nmov x14,x12\nmov x15,#64\n.L{name}_out:\nldp x16,x17,[x13],#16\nstp x16,x17,[x14],#16\nsubs x15,x15,#1\nb.ne .L{name}_out\nmov sp,x10").unwrap();
    } else {
        assembly.push_str("mov x5,x0\n");
    }
    // ZR transfers leave seeded x9 unchanged; every other load is observed in
    // its full X register so missing upper-zero semantics cannot hide in W.
    writeln!(
        assembly,
        "stp x{},xzr,[x3]\nstp x5,x4,[x3,#16]\nret\n.size {name},.-{name}",
        if case.zero { 9 } else { rt }
    )
    .unwrap();
}

pub fn run() {
    // Host gate, constant by design: `cfg!` fixes the compile target, so clippy sees a
    // constant where this harness needs a runtime refusal.
    #[allow(clippy::assertions_on_constants)]
    {
        assert!(native_host::NATIVE && cfg!(target_endian = "little"));
    }
    let directory_scratch = crate::fresh_dir::create("trust-cg-narrow-register-offset-native-");
    let directory = directory_scratch.to_path_buf();
    eprintln!("narrow register-offset native evidence={directory:?}");
    // These include paths describe the reviewed destination under tests/common.
    for (name, bytes) in [
        (
            "fixture-native.rs",
            include_bytes!("narrow_register_offset_native.rs").as_slice(),
        ),
        (
            "fixture-portable.rs",
            include_bytes!("../aarch64_narrow_register_offset_decode.rs").as_slice(),
        ),
        (
            "fixture-process.rs",
            include_bytes!("rosetta.rs").as_slice(),
        ),
        (
            "fixture-termination.rs",
            include_bytes!("process_termination.rs").as_slice(),
        ),
    ] {
        fs::write(directory.join(name), bytes).unwrap();
    }
    for label in [
        "link",
        "native",
        "poison-transfer",
        "poison-base",
        "poison-byte",
    ] {
        fs::write(
            directory.join(format!("{label}.status")),
            "state=not-attempted\n",
        )
        .unwrap();
    }
    snapshot(&directory);
    let mut assembly = String::from(".text\n");
    let mut driver = String::from(DRIVER);
    let mut table = Vec::new();
    let mut tsv = String::from(
        "id\topcode\tbytes\twide\tzero\tsp\tauthored_mode\tpacked_mode\tindex_zero\talias\trt\trn\trm\tword\n",
    );
    let mut encoded_bytes = Vec::new();
    let mut refusals = Vec::new();
    for (id, case) in cases().into_iter().enumerate() {
        let rt = if case.zero {
            31
        } else {
            match case.alias {
                1 => 0,
                2 => 4,
                _ => 9,
            }
        };
        let rn = if case.sp { 31 } else { 0 };
        let rm = if case.index_zero { 31 } else { 4 };
        let wanted = expected_word(case, rt, rn, rm);
        let instruction = intent(case, rt, rn, rm);
        let encoded = match encode_instruction(&instruction) {
            Ok(actual) if actual == wanted => actual,
            other => {
                refusals.push(format!(
                    "case={id} intent={instruction:?} expected={wanted:08x} actual={other:?}\n"
                ));
                continue;
            }
        };
        encoded_bytes.extend_from_slice(&encoded.to_le_bytes());
        for (prefix, text) in [
            ('g', format!(".inst 0x{encoded:08x}")),
            ('a', oracle(case, rt)),
        ] {
            wrapper(&mut assembly, prefix, id, case, rt, &text);
            writeln!(driver, "extern void {prefix}{id}(unsigned char*,uint64_t,const unsigned char*,struct Snapshot*); extern const uint32_t {prefix}{id}_word[];").unwrap();
        }
        table.push(format!(
            "{{g{id},a{id},g{id}_word,a{id}_word,0x{wanted:08x}u,{},{},{},{},{},{},{}}}",
            case.bytes,
            u8::from(case.load),
            u8::from(case.zero),
            case.mode.unwrap_or(6),
            u8::from(case.index_zero),
            case.alias,
            u8::from(case.sp)
        ));
        writeln!(
            tsv,
            "{id}\t{:?}\t{}\t{}\t{}\t{}\t{:?}\t{}\t{}\t{}\t{rt}\t{rn}\t{rm}\t{wanted:08x}",
            opcode(case),
            case.bytes,
            u8::from(case.wide),
            u8::from(case.zero),
            u8::from(case.sp),
            case.mode,
            case.mode.unwrap_or(6),
            u8::from(case.index_zero),
            case.alias
        )
        .unwrap();
    }
    fs::write(directory.join("encoding-refusals.txt"), refusals.concat()).unwrap();
    fs::write(directory.join("encoded-words.bin"), encoded_bytes).unwrap();
    fs::write(directory.join("cases.tsv"), tsv).unwrap();
    assembly.push_str(".section .note.GNU-stack,\"\",%progbits\n");
    writeln!(
        driver,
        "static const struct Case cases[]={{ {} }};",
        table.join(",\n")
    )
    .unwrap();
    driver.push_str(MAIN);
    fs::write(directory.join("words.S"), native_host::assembly(&assembly)).unwrap();
    fs::write(directory.join("driver.c"), driver).unwrap();
    fs::write(
        directory.join("generation.txt"),
        format!(
            "expected_cases={CASES}\nencoded_cases={}\nrefusals={}\n",
            table.len(),
            refusals.len()
        ),
    )
    .unwrap();
    snapshot(&directory);
    assert!(
        refusals.is_empty(),
        "{} native case encoding refusals; {directory:?}",
        refusals.len()
    );
    assert_eq!(table.len(), CASES);
    let executable = directory.join("native");
    let link = run_command(
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
    .unwrap_or_else(|error| {
        panic!("required link failed to launch/capture: {error}; {directory:?}")
    });
    assert!(
        !link.timed_out
            && link.output.status.code() == Some(0)
            && link.output.stdout.is_empty()
            && link.output.stderr.is_empty(),
        "link refusal; {directory:?}"
    );
    let normal = run_command(
        &directory,
        "native",
        &mut Command::new(&executable),
        process::codegen_run_timeout(),
    )
    .unwrap_or_else(|error| {
        panic!("required native control failed to launch/capture: {error}; {directory:?}")
    });
    // A returned normal exit may report a semantic mismatch. Retain it and run
    // all three poison controls before final assertions. Timeout/signal/error
    // never authorizes more children; their prewritten not-attempted rows stay.
    assert!(
        !normal.timed_out && normal.output.status.code().is_some(),
        "native did not normally retire; {directory:?}"
    );
    let mut failures = Vec::new();
    let marker = format!(
        "NARROW_REGISTER_OFFSET_NATIVE_PASS cases={CASES} cg_calls={CALLS} asm_calls={CALLS} checks={CHECKS}\n"
    );
    if normal.output.status.code() != Some(0)
        || normal.output.stdout != marker.as_bytes()
        || !normal.output.stderr.is_empty()
    {
        failures.push("normal status/output mismatch".to_string());
    }
    for (label, expected) in [
        (
            "poison-transfer",
            "EXPECTED_TRANSFER_MISMATCH case=0 route=0 byte=0\n",
        ),
        ("poison-base", "EXPECTED_BASE_MISMATCH case=0 route=0\n"),
        (
            "poison-byte",
            "EXPECTED_BYTE_MISMATCH case=0 route=0 byte=512\n",
        ),
    ] {
        let result = run_command(
            &directory,
            label,
            Command::new(&executable).arg(format!("--{label}")),
            process::codegen_run_timeout(),
        )
        .unwrap_or_else(|error| panic!("{label} launch/capture failure: {error}; {directory:?}"));
        assert!(
            !result.timed_out && result.output.status.code().is_some(),
            "{label} did not normally retire; {directory:?}"
        );
        if result.output.status.code() != Some(97)
            || !result.output.stdout.is_empty()
            || result.output.stderr != expected.as_bytes()
        {
            failures.push(format!("{label} exact status/output mismatch"));
        }
    }
    fs::write(
        directory.join("qualification.txt"),
        format!("failures={failures:?}\n"),
    )
    .unwrap();
    snapshot(&directory);
    assert!(failures.is_empty(), "{failures:?}; {directory:?}");
}

const DRIVER: &str = r#"
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#define SIZE 1024
struct Snapshot { unsigned char data[16]; uint64_t base,index; };
_Static_assert(sizeof(struct Snapshot)==32 && offsetof(struct Snapshot,base)==16 && offsetof(struct Snapshot,index)==24,"assembly Snapshot layout");
typedef void (*Fn)(unsigned char*,uint64_t,const unsigned char*,struct Snapshot*);
struct Case { Fn cg,oracle; const uint32_t *cg_word,*asm_word; uint32_t word; unsigned bytes,load,zero,mode,index_zero,alias,sp; };
static _Alignas(16) unsigned char buffers[2][SIZE],expected[SIZE],seed[16];
static unsigned long checks,calls[2],mismatches;
static uint64_t read_le(const unsigned char *p,unsigned n) {
    uint64_t v=0; for(unsigned j=0;j<n;++j) v|=(uint64_t)p[j]<<(8*j); return v;
}
static void write_le(unsigned char *p,uint64_t v,unsigned n) {
    for(unsigned j=0;j<n;++j) p[j]=(unsigned char)(v>>(8*j));
}
static uint64_t raw_index(unsigned option,unsigned profile,unsigned sp) {
    const uint64_t u[]={0,1,7,UINT64_C(0xa5a5a5a500000007)};
    const uint64_t s[]={0,1,UINT64_C(0xa5a5a5a5ffffffff),UINT64_C(0x5a5a5a5afffffff9)};
    const uint64_t x[]={0,1,UINT64_MAX,UINT64_MAX-6};
    const uint64_t positive[]={0,1,7,3};
    if(sp) return option==2 || option==6?u[profile]:positive[profile];
    return option==2?u[profile]:option==6?s[profile]:x[profile];
}
static int address_index(const struct Case *c,uint64_t raw,size_t *address) {
    const unsigned option=c->mode>>1;
    uint64_t ext=c->index_zero?0:raw;
    if(option==2 || option==6) {
        ext&=UINT64_C(0xffffffff);
        if(option==6 && (ext&UINT64_C(0x80000000))) ext|=UINT64_C(0xffffffff00000000);
    }
    const unsigned shift=(c->mode&1) && c->bytes==2?1:0;
    const uint64_t delta=ext<<shift; /* unsigned modular arithmetic, no signed UB */
    const size_t base=c->sp?0:512;
    size_t pos;
    if(delta>>63) {
        const uint64_t magnitude=(~delta)+1;
        if(c->sp || magnitude>496) return 0;
        pos=base-(size_t)magnitude;
    } else {
        if(delta>496) return 0;
        pos=base+(size_t)delta;
    }
    if((!c->sp && pos<16) || pos+c->bytes>SIZE-16) return 0;
    *address=pos; return 1;
}
"#;

const MAIN: &str = r#"
int main(int argc,char **argv) {
    const int poison_transfer=argc==2 && strcmp(argv[1],"--poison-transfer")==0;
    const int poison_base=argc==2 && strcmp(argv[1],"--poison-base")==0;
    const int poison_byte=argc==2 && strcmp(argv[1],"--poison-byte")==0;
    const int poisoned=poison_transfer || poison_base || poison_byte;
    if(argc!=1 && !poisoned) return 96;
    if(sizeof(cases)/sizeof(cases[0])!=720) return 98;
    /* Verify every actual object instruction before executing any generated word. */
    for(size_t i=0;i<720;++i) {
        const struct Case *c=&cases[i]; checks+=2;
        if(*c->cg_word!=c->word || *c->asm_word!=c->word) {
            fprintf(stderr,"WORD_MISMATCH case=%zu\n",i); return 95;
        }
    }
    const unsigned char edges[]={0,0x7f,0x80,0xff};
    for(size_t i=0;i<720;++i) {
        const struct Case *c=&cases[i];
        for(unsigned profile=0;profile<4;++profile) {
            const uint64_t raw=raw_index(c->mode>>1,profile,c->sp);
            const size_t base=c->sp?0:512;
            size_t address=0; if(!address_index(c,raw,&address)) return 98;
            for(unsigned pattern=0;pattern<4;++pattern) {
                for(unsigned j=0;j<16;++j) seed[j]=(unsigned char)(0x97+j*31+pattern*73);
                for(unsigned route=0;route<2;++route) {
                    unsigned char *buffer=buffers[route];
                    for(size_t j=0;j<SIZE;++j) expected[j]=(unsigned char)((j*37+pattern*71)^(j>>3));
                    for(unsigned j=0;j<c->bytes;++j) expected[address+j]=edges[pattern];
                    memcpy(buffer,expected,SIZE);
                    struct Snapshot wanted={{0},(uint64_t)(uintptr_t)(buffer+base),raw}, actual;
                    memset(&actual,0xa6,sizeof(actual));
                    const uint64_t input=c->alias==1?wanted.base:c->alias==2?raw:read_le(seed,8);
                    uint64_t value=input;
                    if(c->load && !c->zero) value=read_le(expected+address,c->bytes);
                    else if(!c->load) write_le(expected+address,c->zero?0:input,c->bytes);
                    write_le(wanted.data,value,8); /* full X, including high zeros after either narrow load */
                    if(c->load && c->alias==1) wanted.base=value;
                    if(c->load && c->alias==2) wanted.index=value;
                    if(i==0 && profile==0 && pattern==0 && route==0) {
                        if(poison_transfer) wanted.data[0]^=1;
                        if(poison_base) wanted.base^=1;
                        if(poison_byte) expected[address]^=1;
                    }
                    const Fn fn=route?c->oracle:c->cg;
                    fn(buffer+base,raw,seed,&actual); ++calls[route];
                    unsigned bad=0,kind=0; size_t first=0;
                    checks+=2;
                    if(actual.base!=wanted.base) { ++bad; kind=1; }
                    if(actual.index!=wanted.index) { if(!bad) kind=2; ++bad; }
                    for(unsigned j=0;j<16;++j) {
                        ++checks;
                        if(actual.data[j]!=wanted.data[j]) { if(!bad) {kind=3;first=j;} ++bad; }
                    }
                    for(size_t j=0;j<SIZE;++j) {
                        ++checks;
                        if(buffer[j]!=expected[j]) { if(!bad) {kind=4;first=j;} ++bad; }
                    }
                    if(poisoned) {
                        if(i!=0 || profile!=0 || pattern!=0 || route!=0 || bad!=1) return 99;
                        if(poison_transfer && kind==3 && first==0) fprintf(stderr,"EXPECTED_TRANSFER_MISMATCH case=0 route=0 byte=0\n");
                        else if(poison_base && kind==1) fprintf(stderr,"EXPECTED_BASE_MISMATCH case=0 route=0\n");
                        else if(poison_byte && kind==4 && first==512) fprintf(stderr,"EXPECTED_BYTE_MISMATCH case=0 route=0 byte=512\n");
                        else return 99;
                        return 97;
                    }
                    if(bad && mismatches<16) fprintf(stderr,"STATE_MISMATCH case=%zu profile=%u pattern=%u route=%u checks_failed=%u first_kind=%u first_byte=%zu\n",i,profile,pattern,route,bad,kind,first);
                    mismatches+=bad;
                }
            }
        }
    }
    if(calls[0]!=11520 || calls[1]!=11520 || checks!=720UL*2+11520UL*2*(1024+16+2)) return 98;
    if(mismatches) {
        fprintf(stderr,"NARROW_REGISTER_OFFSET_NATIVE_FAIL cases=720 cg_calls=%lu asm_calls=%lu checks=%lu mismatches=%lu\n",calls[0],calls[1],checks,mismatches);
        return 1;
    }
    printf("NARROW_REGISTER_OFFSET_NATIVE_PASS cases=720 cg_calls=%lu asm_calls=%lu checks=%lu\n",calls[0],calls[1],checks);
    return 0;
}
"#;
