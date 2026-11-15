// Copyright 2026 Andrew Yates | Apache-2.0
//! Fixed native FP/SIMD immediate-memory controls against C byte copies.
//! These are finite encoder-execution tests, not lowering or memory proofs.

use sha2::{Digest, Sha256};
use std::{fmt::Write, fs, io::Read, path::Path, process::Command, time::Duration};
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as Arg, regs::PReg};

#[path = "rosetta.rs"]
mod process;

#[path = "native_host.rs"]
mod native_host;

const FUNCTIONS: usize = 4 * 3 * 7 * 2;
const PATTERNS: usize = 16;
const CALLS: usize = FUNCTIONS * PATTERNS;
const CHECKS: usize = FUNCTIONS + CALLS * 3;

fn file_hash(path: &Path) -> String {
    let mut input = fs::File::open(path).unwrap();
    let mut hash = Sha256::new();
    let mut buffer = [0; 65536];
    loop {
        let count = input.read(&mut buffer).unwrap();
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
    }
    format!("{:x}", hash.finalize())
}

fn hash_artifacts(directory: &Path) {
    let mut rows = Vec::new();
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.file_name().unwrap() != "SHA256SUMS" {
            rows.push(format!(
                "{}  {}\n",
                file_hash(&path),
                path.file_name().unwrap().to_str().unwrap()
            ));
        }
    }
    rows.sort();
    fs::write(directory.join("SHA256SUMS"), rows.concat()).unwrap();
}

fn command(directory: &Path, name: &str, command: &mut Command, timeout: Duration) -> Vec<u8> {
    fs::write(
        directory.join(format!("{name}.command")),
        format!("{command:?}\ntimeout={timeout:?}\n"),
    )
    .unwrap();
    let result = match process::command_output_with_timeout(command, timeout) {
        Ok(result) => result,
        Err(error) => {
            fs::write(
                directory.join(format!("{name}.spawn-error")),
                error.to_string(),
            )
            .unwrap();
            hash_artifacts(directory);
            panic!("{name} could not run; evidence={directory:?}: {error}");
        }
    };
    fs::write(
        directory.join(format!("{name}.stdout")),
        &result.output.stdout,
    )
    .unwrap();
    fs::write(
        directory.join(format!("{name}.stderr")),
        &result.output.stderr,
    )
    .unwrap();
    fs::write(
        directory.join(format!("{name}.status")),
        format!(
            "status={}\ntimed_out={}\n",
            result.output.status, result.timed_out
        ),
    )
    .unwrap();
    hash_artifacts(directory);
    assert!(
        !result.timed_out && result.output.status.success(),
        "{name} failed; evidence={directory:?}: {}",
        String::from_utf8_lossy(&result.output.stderr)
    );
    result.output.stdout
}

fn wrapper(assembly: &mut String, index: usize, rt: u16, load: bool, word: u32) {
    // C arguments: x0=input base, x1=output base, x2=16-byte register image.
    // These are leaf functions. Preserve full Q15 (the only selected
    // callee-saved register) in an aligned frame; no callee-saved GPR is used.
    writeln!(assembly, ".p2align 2\n.global f{index}\n.type f{index},%function\nf{index}:\nsub sp,sp,#16\nstr q15,[sp]").unwrap();
    if !load {
        writeln!(assembly, "ldr q{rt},[x2]").unwrap();
    } else {
        // Deliberately nonzero upper lanes make narrow-load zeroing observable.
        writeln!(assembly, "movi v{rt}.16b,#165").unwrap();
    }
    writeln!(assembly, ".global f{index}_word\nf{index}_word:\n.inst 0x{word:08x}\nstr q{rt},[x2]\nldr q15,[sp]\nadd sp,sp,#16\nret\n.size f{index},.-f{index}").unwrap();
}

/// Called only on the native AArch64 hosts (Linux GNU and macOS). A missing
/// host C compiler, assembler/linker support, or execution is a failure, never
/// a native skip. Linux builds with GCC; macOS builds with the Xcode clang.
pub fn run() {
    // Host gate, constant by design: both operands fix the compile target, so clippy sees a
    // constant where this harness needs a runtime refusal. Per the doc comment above, a
    // non-native or big-endian host is a FAILURE here, never a skip.
    #[allow(clippy::assertions_on_constants)]
    {
        assert!(native_host::NATIVE && cfg!(target_endian = "little"));
    }
    let directory_scratch = crate::fresh_dir::create("trust-cg-fp-memory-native-");
    let directory = directory_scratch.to_path_buf();
    eprintln!("FP memory native evidence={directory:?}");
    let mut assembly = String::from(".text\n");
    let mut driver = String::from(DRIVER_PREFIX);
    let mut rows = Vec::new();
    let mut words = String::from("case\twidth\tload\tRt\tRn\toffset_bytes\tword\n");
    for width in [16_u16, 32, 64, 128] {
        let scale = i64::from(width / 8);
        let register_base = match width {
            16 => 165,
            32 => 128,
            64 => 96,
            128 => 64,
            _ => unreachable!(),
        };
        for rt in [0_u16, 15, 31] {
            for offset in [-256, -1, 0, 1, 255, scale, 4095 * scale] {
                for load in [false, true] {
                    let rn = if load { 0 } else { 1 };
                    let intent = MachInst::new(
                        if load { Op::LdrRI } else { Op::StrRI },
                        vec![
                            Arg::PReg(PReg::new(register_base + rt)),
                            Arg::PReg(PReg::new(rn)),
                            Arg::Imm(offset),
                        ],
                    );
                    let word = encode_instruction(&intent).unwrap();
                    let index = rows.len();
                    wrapper(&mut assembly, index, rt, load, word);
                    writeln!(driver, "extern void f{index}(const unsigned char*,unsigned char*,unsigned char*);extern const uint32_t f{index}_word[];").unwrap();
                    rows.push(format!(
                        "{{f{index},f{index}_word,{word}u,{width},{},{offset}}},\n",
                        u8::from(load)
                    ));
                    writeln!(
                        words,
                        "{index}\t{width}\t{}\t{rt}\t{rn}\t{offset}\t0x{word:08x}",
                        u8::from(load)
                    )
                    .unwrap();
                }
            }
        }
    }
    assert_eq!(rows.len(), FUNCTIONS);
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    driver.push_str("static const struct test_case cases[]={\n");
    driver.push_str(&rows.concat());
    driver.push_str("};\n");
    driver.push_str(DRIVER_MAIN);
    fs::write(directory.join("memory.S"), native_host::assembly(&assembly)).unwrap();
    fs::write(directory.join("driver.c"), driver).unwrap();
    fs::write(directory.join("words.tsv"), words).unwrap();
    fs::write(directory.join("scope.txt"), format!("functions={FUNCTIONS}\npatterns={PATTERNS}\ncalls={CALLS}\nchecks={CHECKS}\nFixed native .inst execution against C memcpy; no source/proof authority.\nRunner bounds process polling, not OS stalls or escaped descendants.\nThe host C compiler inherits the existing test environment; compiler hash is not a hermetic transitive toolchain attestation.\n")).unwrap();
    hash_artifacts(&directory);
    let compiler = fs::canonicalize(if native_host::DARWIN {
        "/usr/bin/clang"
    } else {
        "/usr/bin/gcc"
    })
    .unwrap_or_else(|error| {
        panic!("required host C compiler missing; evidence={directory:?}: {error}")
    });
    let compiler_hash = file_hash(&compiler);
    fs::write(
        directory.join("compiler.identity"),
        format!("path={compiler:?}\nsha256={compiler_hash}\n"),
    )
    .unwrap();
    command(
        &directory,
        "compiler-version",
        Command::new(&compiler).arg("--version"),
        process::codegen_probe_timeout(),
    );
    let binary = directory.join("run");
    let mut build = Command::new(&compiler);
    build
        .args(["-std=c11", "-O2", "-Werror"])
        .args(native_host::link_hardening_args())
        .arg(directory.join("driver.c"))
        .arg(directory.join("memory.S"))
        .arg("-o")
        .arg(&binary);
    command(
        &directory,
        "build",
        &mut build,
        process::codegen_link_timeout(),
    );
    assert_eq!(
        file_hash(&compiler),
        compiler_hash,
        "host C compiler identity changed; evidence={directory:?}"
    );
    let mut execute = Command::new(&binary);
    execute.arg(directory.join("states.bin"));
    let output = command(
        &directory,
        "run",
        &mut execute,
        process::codegen_run_timeout(),
    );
    let marker = format!(
        "PASS {FUNCTIONS} encoded functions, {CALLS} native calls, {CHECKS} exact word/array checks"
    );
    assert_eq!(
        String::from_utf8_lossy(&output).trim(),
        marker,
        "evidence={directory:?}"
    );
    assert_eq!(
        fs::metadata(directory.join("states.bin")).unwrap().len(),
        (CALLS * 64) as u64
    );
    hash_artifacts(&directory);
    eprintln!("{marker}; evidence={directory:?}");
}

const DRIVER_PREFIX: &str = r#"
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
_Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,"little endian fixture");
enum { MEMORY_BYTES=66560, ORIGIN=512, PATTERNS=16, FUNCTIONS=168 };
typedef void (*function_t)(const unsigned char*,unsigned char*,unsigned char*);
struct test_case {function_t call;const uint32_t* location;uint32_t word;unsigned width,load;int64_t offset;};
struct state {unsigned char before[16],q[16],after[16];};
_Static_assert(sizeof(struct state)==48,"state canary layout");
_Static_assert(offsetof(struct state,q)==16,"register image layout");
static _Alignas(16) unsigned char input[MEMORY_BYTES],saved_input[MEMORY_BYTES],output[MEMORY_BYTES],expected_output[MEMORY_BYTES];
static uint64_t checks,calls,failures;
static const uint64_t patterns[PATTERNS][2]={
 {0,UINT64_MAX},{UINT64_MAX,0},{0xaaaaaaaaaaaaaaaaULL,0x5555555555555555ULL},
 {0x0123456789abcdefULL,0xfedcba9876543210ULL},{1,0x8000000000000000ULL},
 {0x8000000000000000ULL,1},{0x7ff0000000000000ULL,0xfff0000000000000ULL},
 {0x7ff8123456789abcULL,0x7ff0123456789abcULL},{0x7f800000,0xff800000},
 {0x7fc12345,0x7f812346},{0x7c00,0xfc00},{0x7e35,0x7d23},
 {0x8000,1},{0x80000000,1},{0x0010000000000000ULL,0x000fffffffffffffULL},
 {0xdeadbeef13579bdfULL,0x2468ace00badf00dULL}
};
static void compare(const void*got,const void*want,size_t size,unsigned i,unsigned p,const char*what) {
 checks++;
 if(memcmp(got,want,size)) {
  if(failures<16) {
   const unsigned char*g=got,*w=want;size_t k=0;while(k<size&&g[k]==w[k])k++;
   fprintf(stderr,"case%u pattern%u %s byte%zu: got%02x expected%02x\n",i,p,what,k,g[k],w[k]);
  }
  failures++;
 }
}
"#;

const DRIVER_MAIN: &str = r#"
_Static_assert(sizeof(cases)/sizeof(cases[0])==FUNCTIONS,"function census");
int main(int argc,char**argv) {
 if(argc!=2)return 2;
 FILE*records=fopen(argv[1],"wb");if(!records)return 3;
 for(unsigned i=0;i<FUNCTIONS;i++) {
  const struct test_case*t=&cases[i];size_t bytes=t->width/8;
  int64_t at=ORIGIN+t->offset;
  if(at<256||at+(int64_t)bytes>MEMORY_BYTES-256){fclose(records);return 4;}
  compare(t->location,&t->word,4,i,0,"actual instruction word");
  for(unsigned p=0;p<PATTERNS;p++) {
   _Alignas(16) struct state actual,expected;
   memset(&actual,0xa5,sizeof(actual));memset(actual.after,0x5a,sizeof(actual.after));
   for(size_t k=0;k<MEMORY_BYTES;k++) {
    input[k]=(unsigned char)(k^(k>>8)^(k>>16)^(17*p));
    output[k]=(unsigned char)(0xd3^(k*13)^(k>>8)^(29*p));
   }
   memcpy(expected_output,output,sizeof(output));
   if(t->load) {
    memcpy(input+(size_t)at,patterns[p],bytes);
    expected=actual;memset(expected.q,0,sizeof(expected.q));
    memcpy(expected.q,input+(size_t)at,bytes);
   } else {
    memcpy(actual.q,patterns[p],sizeof(actual.q));expected=actual;
    memcpy(expected_output+(size_t)at,actual.q,bytes);
   }
   memcpy(saved_input,input,sizeof(input));
   t->call(input+ORIGIN,output+ORIGIN,actual.q);calls++;
   compare(input,saved_input,sizeof(input),i,p,"whole input/canaries");
   compare(output,expected_output,sizeof(output),i,p,"whole output/canaries");
   compare(&actual,&expected,sizeof(actual),i,p,"register image/canaries");
   uint64_t row[8]={i,p,t->width,(uint64_t)t->offset,t->word,0,0,failures};
   memcpy(&row[5],actual.q,sizeof(actual.q));
   if(fwrite(row,sizeof(row),1,records)!=1){fclose(records);return 5;}
  }
 }
 if(fclose(records))return 6;
 if(calls!=2688||checks!=8232||failures) {
  fprintf(stderr,"calls%llu checks%llu failures%llu\n",(unsigned long long)calls,(unsigned long long)checks,(unsigned long long)failures);
  return 1;
 }
 puts("PASS 168 encoded functions, 2688 native calls, 8232 exact word/array checks");
 return 0;
}
"#;
