//! Native Linux ELF twin of `static_data_aarch64.rs`: `MonoItem::Static` data
//! compiled through the rustc bridge for `aarch64-unknown-linux-gnu`, linked
//! with GNU `cc` against C drivers and run, with an LLVM twin of every lane.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! This target is mandatory on its named host, not a portable skip; the shared
//! harness (`support/linux_runtime_twin.rs`) fails it by name when a
//! prerequisite is missing and binds the backend the runner supplies.
//!
//! FIXTURES. The Darwin twin's four crates and C drivers are kept
//! byte-identical (the script test
//! `test_runtime_twins_keep_the_darwin_crates_and_drivers` pins them):
//! immutable scalar and byte-array statics, a mutable static shared by Rust
//! readers/writers and C, the over-aligned statics (a writable `u128`, a
//! read-only `#[repr(align(64))]` struct and `u128`, and the nested
//! allocations behind `AY_REFS`), and pointer-bearing statics whose
//! relocations name `extern` statics beside a closure's `fn` pointer. One
//! Linux crate adds what the task names and the Darwin crates leave implicit:
//! zero-initialized statics (`.bss`), relocations in data to a string, a
//! nested slice, two functions and another static, and address identity
//! between Rust and C views of the same storage.
//!
//! WHAT IS CHECKED, AT O0-O3, FOR CG AND LLVM ALIKE. Each crate is compiled by
//! both compilers (`--emit=obj`, one codegen unit, `-Cpanic=abort`; the
//! over-aligned and extern crates with `-Cdebug-assertions=off`, as on
//! Darwin), linked with its drivers and run three times; every run must print
//! exactly the model and end exactly as modelled, so the CG and LLVM
//! executables agree byte for byte. Object facts, read with GNU `readelf`
//! (never from the backend's own notes): every `#[no_mangle]` static is one
//! `GLOBAL OBJECT` definition of its size, at an address and in a section
//! aligned to its alignment, in its storage class (read-only `PROGBITS`
//! without `W`; initialized writable `PROGBITS`; zero-initialized `NOBITS`;
//! relocated read-only-after-relocation data), with exactly its count of
//! `R_AARCH64_ABS64` relocations in its bytes and no other relocation; each
//! extern static is imported and named by two data relocations. The storage
//! class of every static must also equal the LLVM twin's at that level.
//!
//! The Darwin over-aligned driver's 16-byte `__atomic_fetch_add` is the
//! alignment-faulting access there (clang's `caspal`); GNU cc lowers it to a
//! libatomic call, which does not fault on a misaligned address. A prelude
//! therefore routes the unchanged driver's `__atomic_fetch_add` through an
//! `LDAXP`/`STLXP` exclusive-pair loop, which does.
//!
//! CONTROLS (CG and LLVM, every level). A store through a pointer to the
//! immutable `AY_STATIC_N` must die on `SIGSEGV`: the static is in read-only
//! memory. An exclusive pair on `AY_WIDE_A + 8` must die on `SIGBUS`: the
//! driver's access really is alignment-sensitive on this host. An
//! out-of-bounds index into the static `AY_TABLE` must take the bounds-check
//! panic edge rather than read past it: the run dies on `SIGABRT` in the
//! aborting stub of `core::panicking::panic_bounds_check`, which names itself
//! on stderr before it aborts, and CG and LLVM must fire the same stub. The
//! Darwin immutable lane runs with certificates ON and admits only its panic
//! handler's proof refusal; here every bridge compile passes `no-proof-certs`,
//! so no proof promotion runs and that control does not apply. Its comment
//! that a native `panic=abort` bounds check is refused (`[TCG-ASSERT-PANIC]`)
//! does not hold on this host: the bridge compiles it, and the out-of-bounds
//! control runs it.
//!
//! EVIDENCE BOUNDARY. Native TESTING evidence without certificates: the
//! frontend runs with `-Ztrust-verify=off` and the backend with the
//! `no-proof-certs` knob. The section, symbol and relocation rows are
//! unproven object-side facts; GNU cc/ld, binutils and glibc are trusted. No
//! certificate, proof, shared-object or dynamic-loading behaviour is claimed.
//!
//! The artifacts directory is removed when the test passes; setting
//! `STATIC_DATA_LINUX_KEEP_ARTIFACTS=1` retains it.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/linux_runtime_twin.rs"]
mod twin;

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;
use twin::{Bridge, Ending, LaneRow, ObjectFacts};

const MARKER: &str = "TCG_BRIDGE_STATIC_DATA_EXECUTION";
const KEEP_ARTIFACTS: &str = "STATIC_DATA_LINUX_KEEP_ARTIFACTS";
/// Native executions of each linked CG/LLVM executable.
const RUNS_PER_LANE: usize = 3;
const SIGABRT: i32 = twin::SIGABRT;
/// The core panic entry the out-of-bounds control must abort through.
const BOUNDS_PANIC: &str = "panic_bounds_check";
const SIGBUS: i32 = 7;
const SIGSEGV: i32 = 11;

/// Byte-identical to `STATIC_CRATE` in `static_data_aarch64.rs`.
const STATIC_CRATE: &str = "\
#![no_std]\n\
#![no_main]\n\
#[no_mangle]\npub static AY_STATIC_N: u32 = 0xDEAD_BEEF;\n\
#[no_mangle]\npub static AY_STATIC_BYTES: [u8; 4] = [0x42, 0x43, 0x00, 0x44];\n\
#[no_mangle]\npub static AY_STATIC_W: u64 = 0x0102_0304_0506_0708;\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

/// Byte-identical to `DRIVER_C` in `static_data_aarch64.rs`.
const DRIVER_C: &str = "\
#include <stdint.h>\n\
extern const uint32_t AY_STATIC_N;\n\
extern const uint8_t  AY_STATIC_BYTES[4];\n\
extern const uint64_t AY_STATIC_W;\n\
int main(void){\n\
    if (AY_STATIC_N != 0xDEADBEEFu) return 1;\n\
    if (AY_STATIC_BYTES[0] != 0x42) return 2;\n\
    if (AY_STATIC_BYTES[1] != 0x43) return 3;\n\
    if (AY_STATIC_BYTES[2] != 0x00) return 4;\n\
    if (AY_STATIC_BYTES[3] != 0x44) return 5;\n\
    if (AY_STATIC_W != 0x0102030405060708ull) return 6;\n\
    return 0;\n\
}\n";

/// Byte-identical to the mutable-static test's `src` in `static_data_aarch64.rs`.
const MUTABLE_CRATE: &str = "\
#![no_std]\n#![no_main]\n\
#[no_mangle]\npub static mut AY_STATIC_MUT: u32 = 7;\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_static_get() -> u32 { AY_STATIC_MUT }\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_static_set(value: u32) { AY_STATIC_MUT = value; }\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

/// Byte-identical to the mutable-static test's `driver` in `static_data_aarch64.rs`.
const MUTABLE_DRIVER: &str = "\
#include <stdint.h>\n\
extern uint32_t AY_STATIC_MUT;\n\
extern uint32_t ay_static_get(void);\n\
extern void ay_static_set(uint32_t);\n\
int main(void) {\n\
    if (AY_STATIC_MUT != 7u) return 1;\n\
    if (ay_static_get() != 7u) return 2;\n\
    AY_STATIC_MUT = 19u;\n\
    if (ay_static_get() != 19u) return 3;\n\
    ay_static_set(42u);\n\
    if (AY_STATIC_MUT != 42u) return 4;\n\
    return 0;\n\
}\n";

/// Byte-identical to the over-aligned test's `SRC` in `static_data_aarch64.rs`.
const OVERALIGNED_CRATE: &str = "\
#![no_std]\n#![no_main]\n\
#[no_mangle]\npub static mut AY_PAD_A: u64 = 0x0A;\n\
#[no_mangle]\npub static mut AY_PAD_B: u64 = 0x0B;\n\
#[no_mangle]\npub static mut AY_WIDE_A: u128 = 0x1111_2222_3333_4444_5555_6666_7777_8888;\n\
#[no_mangle]\npub static mut AY_WIDE_B: u64 = 0x0D;\n\
#[no_mangle]\npub static mut AY_WIDE_C: u128 = 0x9999_aaaa_bbbb_cccc_dddd_eeee_ffff_0000;\n\
#[repr(C, align(64))]\npub struct Line { pub a: u64, pub b: u64, pub c: u8 }\n\
#[no_mangle]\npub static AY_LINE: Line = Line { a: 7, b: 9, c: 1 };\n\
#[no_mangle]\npub static AY_PAD_C: u64 = 0x0C;\n\
#[no_mangle]\npub static AY_BIG: u128 = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;\n\
#[repr(C)]\npub struct Refs { pub a: &'static u128, pub b: &'static u64, pub c: &'static u128 }\n\
#[no_mangle]\npub static AY_REFS: Refs = Refs {\n\
    a: &0x0f0f_0f0f_0f0f_0f0f_f0f0_f0f0_f0f0_f0f1,\n\
    b: &0x77,\n\
    c: &0x1234_5678_9abc_def0_0fed_cba9_8765_4321,\n\
};\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_wide_lo() -> u64 { AY_WIDE_A as u64 ^ AY_WIDE_C as u64 }\n\
#[no_mangle]\npub unsafe extern \"C\" fn ay_wide_addr() -> usize { core::ptr::addr_of!(AY_WIDE_A) as usize }\n\
#[no_mangle]\npub extern \"C\" fn ay_refs_lo() -> u64 { (*AY_REFS.a as u64) ^ (*AY_REFS.c as u64) ^ *AY_REFS.b }\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

/// Byte-identical to the over-aligned test's `DRIVER` in `static_data_aarch64.rs`.
const OVERALIGNED_DRIVER: &str = "\
#include <stdint.h>\n\
typedef unsigned __int128 u128;\n\
struct Line { uint64_t a, b; uint8_t c; } __attribute__((aligned(64)));\n\
struct Refs { const u128 *a; const uint64_t *b; const u128 *c; };\n\
extern uint64_t AY_PAD_A, AY_PAD_B, AY_WIDE_B;\n\
extern const uint64_t AY_PAD_C;\n\
extern u128 AY_WIDE_A, AY_WIDE_C;\n\
extern const struct Line AY_LINE;\n\
extern const u128 AY_BIG;\n\
extern const struct Refs AY_REFS;\n\
extern uint64_t ay_wide_lo(void);\n\
extern uintptr_t ay_wide_addr(void);\n\
extern uint64_t ay_refs_lo(void);\n\
static u128 w(uint64_t hi, uint64_t lo) { return ((u128)hi << 64) | lo; }\n\
int main(void) {\n\
    if ((uintptr_t)&AY_WIDE_A % 16) return 10;\n\
    if ((uintptr_t)&AY_WIDE_C % 16) return 11;\n\
    if ((uintptr_t)&AY_LINE % 64) return 12;\n\
    if ((uintptr_t)&AY_BIG % 16) return 13;\n\
    if ((uintptr_t)AY_REFS.a % 16) return 14;\n\
    if ((uintptr_t)AY_REFS.c % 16) return 15;\n\
    if (ay_wide_addr() != (uintptr_t)&AY_WIDE_A) return 16;\n\
    u128 old_a = __atomic_fetch_add(&AY_WIDE_A, 1, __ATOMIC_SEQ_CST);\n\
    u128 old_c = __atomic_fetch_add(&AY_WIDE_C, 2, __ATOMIC_SEQ_CST);\n\
    if (old_a != w(0x1111222233334444ull, 0x5555666677778888ull)) return 20;\n\
    if (old_c != w(0x9999aaaabbbbccccull, 0xddddeeeeffff0000ull)) return 21;\n\
    if (ay_wide_lo() != (0x5555666677778889ull ^ 0xddddeeeeffff0002ull)) return 22;\n\
    if (AY_LINE.a != 7 || AY_LINE.b != 9 || AY_LINE.c != 1) return 30;\n\
    if (AY_BIG != w(0x0123456789abcdefull, 0xfedcba9876543210ull)) return 31;\n\
    if (*AY_REFS.a != w(0x0f0f0f0f0f0f0f0full, 0xf0f0f0f0f0f0f0f1ull)) return 32;\n\
    if (*AY_REFS.b != 0x77 || *AY_REFS.c != w(0x123456789abcdef0ull, 0x0fedcba987654321ull)) return 33;\n\
    if (ay_refs_lo() != (0xf0f0f0f0f0f0f0f1ull ^ 0x0fedcba987654321ull ^ 0x77)) return 34;\n\
    if (AY_PAD_A != 0x0A || AY_PAD_B != 0x0B || AY_PAD_C != 0x0C || AY_WIDE_B != 0x0D) return 40;\n\
    return 0;\n\
}\n";

/// Byte-identical to the extern-static test's `src` in `static_data_aarch64.rs`.
const EXTERN_CRATE: &str = "\
#![no_std]\n#![no_main]\n\
extern \"C\" { static AY_EXT_ONE: u32; static AY_EXT_TWO: u32; }\n\
pub struct P(*const u32);\nunsafe impl Sync for P {}\n\
static PTR: P = P(&raw const AY_EXT_ONE);\n\
static PAIR: &[P; 2] = &[P(&raw const AY_EXT_ONE), P(&raw const AY_EXT_TWO)];\n\
pub struct Mix(*const u32, fn(u32, u32) -> u32);\nunsafe impl Sync for Mix {}\n\
static MIX: &Mix = &Mix(&raw const AY_EXT_TWO, |a, b| a ^ b);\n\
#[no_mangle]\npub extern \"C\" fn ay_ext_direct() -> u32 { unsafe { *core::hint::black_box(&PTR).0 } }\n\
#[no_mangle]\npub extern \"C\" fn ay_ext_nested() -> u32 {\n\
    let [first, second] = core::hint::black_box(PAIR);\n\
    unsafe { (*first.0).wrapping_mul(3).wrapping_add(*second.0) }\n\
}\n\
#[no_mangle]\npub extern \"C\" fn ay_ext_mix(a: u32) -> u32 {\n\
    let m = core::hint::black_box(MIX);\n\
    unsafe { (m.1)(*m.0, a) }\n\
}\n\
#[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

/// Byte-identical to the extern-static test's `driver` in `static_data_aarch64.rs`.
const EXTERN_DRIVER: &str = "\
#include <stdint.h>\n\
uint32_t AY_EXT_ONE = 0x1234u;\n\
uint32_t AY_EXT_TWO = 0xABCDu;\n\
extern uint32_t ay_ext_direct(void);\n\
extern uint32_t ay_ext_nested(void);\n\
extern uint32_t ay_ext_mix(uint32_t);\n\
int main(void) {\n\
    if (ay_ext_direct() != 0x1234u) return 1;\n\
    if (ay_ext_nested() != 0x1234u * 3u + 0xABCDu) return 2;\n\
    if (ay_ext_mix(0xFFu) != (0xABCDu ^ 0xFFu)) return 3;\n\
    AY_EXT_TWO = 7u;\n\
    if (ay_ext_mix(5u) != (7u ^ 5u)) return 4;\n\
    return 0;\n\
}\n";

/// Prepended to [`OVERALIGNED_DRIVER`] (and the misaligned control): the
/// driver's 16-byte `__atomic_fetch_add` becomes an `LDAXP`/`STLXP` loop, the
/// access that faults on an address not aligned to 16 (GNU cc would call
/// libatomic, which does not fault).
const EXCLUSIVE_PRELUDE: &str = r#"#include <stdint.h>
static unsigned __int128 ay_exclusive_fetch_add(unsigned __int128 *cell, unsigned __int128 delta) {
    uint64_t lo, hi, new_lo, new_hi;
    uint32_t failed;
    do {
        __asm__ volatile("ldaxp %0, %1, [%5]\n\t"
                         "adds %2, %0, %6\n\t"
                         "adc %3, %1, %7\n\t"
                         "stlxp %w4, %2, %3, [%5]"
                         : "=&r"(lo), "=&r"(hi), "=&r"(new_lo), "=&r"(new_hi), "=&r"(failed)
                         : "r"(cell), "r"((uint64_t)delta), "r"((uint64_t)(delta >> 64))
                         : "memory", "cc");
    } while (failed);
    return ((unsigned __int128)hi << 64) | lo;
}
#define __atomic_fetch_add(cell, delta, order) ay_exclusive_fetch_add((cell), (delta))
"#;

/// The SIGBUS control's driver, after [`EXCLUSIVE_PRELUDE`]: the same
/// exclusive pair on the 8-mod-16 address inside `AY_WIDE_A`.
const MISALIGNED_CONTROL: &str = r#"#include <stdio.h>
extern unsigned __int128 AY_WIDE_A;
int main(void) {
    printf("AY_WIDE_A%%16=%u\n", (unsigned)((uintptr_t)&AY_WIDE_A % 16));
    fflush(stdout);
    ay_exclusive_fetch_add((unsigned __int128 *)((char *)&AY_WIDE_A + 8), 1);
    printf("the exclusive pair on an 8-mod-16 address did not fault\n");
    return 0;
}
"#;

/// The SIGSEGV control: a store to the immutable `AY_STATIC_N` of
/// [`STATIC_CRATE`].
const READONLY_CONTROL: &str = r#"#include <stdint.h>
#include <stdio.h>
extern const uint32_t AY_STATIC_N;
int main(void) {
    printf("AY_STATIC_N=%#x\n", AY_STATIC_N);
    fflush(stdout);
    *(volatile uint32_t *)&AY_STATIC_N = 1u;
    printf("the store to an immutable static did not fault\n");
    return 0;
}
"#;

/// Linux extension: zero-initialized statics, relocations in data to a
/// string, a nested slice, two functions and another static, a read-only
/// table, and Rust accessors whose addresses and values the driver compares
/// with its own view of the same storage.
const LAYOUT_CRATE: &str = r#"#![no_std]
#![no_main]
#[no_mangle]
pub static mut AY_ZERO_WORDS: [u64; 8] = [0; 8];
#[no_mangle]
pub static AY_ZERO_CONST: [u32; 4] = [0; 4];
#[no_mangle]
pub static AY_GREETING: &str = "hello, statics";
#[no_mangle]
pub static AY_PRIMES: &[u16] = &[2, 3, 5, 7, 11, 13];
pub extern "C" fn ay_double(x: u32) -> u32 { x.wrapping_mul(2) }
pub extern "C" fn ay_square(x: u32) -> u32 { x.wrapping_mul(x) }
#[no_mangle]
pub static AY_OPS: [extern "C" fn(u32) -> u32; 2] = [ay_double, ay_square];
#[no_mangle]
pub static AY_TARGET: u32 = 0x5151;
#[no_mangle]
pub static AY_SELF_REF: &u32 = &AY_TARGET;
#[no_mangle]
pub static AY_TABLE: [u32; 4] = [11, 22, 33, 44];

#[no_mangle]
pub extern "C" fn ay_zero_addr() -> usize { core::ptr::addr_of!(AY_ZERO_WORDS) as usize }
#[no_mangle]
pub unsafe extern "C" fn ay_zero_bump(i: usize, d: u64) -> u64 {
    let p = core::ptr::addr_of_mut!(AY_ZERO_WORDS) as *mut u64;
    let slot = p.add(i & 7);
    *slot = (*slot).wrapping_add(d);
    *slot
}
#[no_mangle]
pub extern "C" fn ay_zero_sum() -> u64 {
    let mut s = 0u64;
    let p = core::ptr::addr_of!(AY_ZERO_WORDS) as *const u64;
    let mut i = 0;
    while i < 8 { s = s.wrapping_add(unsafe { *p.add(i) }); i += 1; }
    s
}
#[no_mangle]
pub extern "C" fn ay_greeting_len() -> usize { core::hint::black_box(AY_GREETING).len() }
#[no_mangle]
pub extern "C" fn ay_greeting_byte(i: usize) -> u8 { core::hint::black_box(AY_GREETING).as_bytes()[i % 14] }
#[no_mangle]
pub extern "C" fn ay_primes_sum() -> u32 { let p = core::hint::black_box(AY_PRIMES); let mut s = 0u32; for x in p { s += *x as u32; } s }
#[no_mangle]
pub extern "C" fn ay_apply(i: usize, x: u32) -> u32 { let ops = core::hint::black_box(&AY_OPS); (ops[i & 1])(x) }
#[no_mangle]
pub extern "C" fn ay_self_ref() -> u32 { **core::hint::black_box(&AY_SELF_REF) }
#[no_mangle]
pub extern "C" fn ay_target_addr() -> usize { core::ptr::addr_of!(AY_TARGET) as usize }
#[no_mangle]
pub extern "C" fn ay_table_at(i: usize) -> u32 { core::hint::black_box(&AY_TABLE)[i] }
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
"#;

const LAYOUT_DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>
extern uint64_t AY_ZERO_WORDS[8];
extern const uint32_t AY_ZERO_CONST[4];
struct str { const char *ptr; uintptr_t len; };
struct slice { const uint16_t *ptr; uintptr_t len; };
extern const struct str AY_GREETING;
extern const struct slice AY_PRIMES;
extern uint32_t (*const AY_OPS[2])(uint32_t);
extern const uint32_t AY_TARGET;
extern const uint32_t *const AY_SELF_REF;
extern uintptr_t ay_zero_addr(void);
extern uint64_t ay_zero_bump(uintptr_t, uint64_t);
extern uint64_t ay_zero_sum(void);
extern uintptr_t ay_greeting_len(void);
extern uint8_t ay_greeting_byte(uintptr_t);
extern uint32_t ay_primes_sum(void);
extern uint32_t ay_apply(uintptr_t, uint32_t);
extern uint32_t ay_self_ref(void);
extern uintptr_t ay_target_addr(void);
extern uint32_t ay_table_at(uintptr_t);
int main(void) {
    uint64_t zero = 0;
    for (int i = 0; i < 8; i++) zero |= AY_ZERO_WORDS[i];
    for (int i = 0; i < 4; i++) zero |= AY_ZERO_CONST[i];
    printf("zero_initial=%llu zero_sum=%llu\n", (unsigned long long)zero, (unsigned long long)ay_zero_sum());
    printf("zero_addr_identity=%d\n", ay_zero_addr() == (uintptr_t)AY_ZERO_WORDS);
    printf("bump=%llu ", (unsigned long long)ay_zero_bump(3, 5));
    AY_ZERO_WORDS[3] += 100;
    printf("bump2=%llu c_view=%llu sum=%llu\n", (unsigned long long)ay_zero_bump(3, 1),
           (unsigned long long)AY_ZERO_WORDS[3], (unsigned long long)ay_zero_sum());
    printf("greeting=%.*s len=%lu rust_len=%lu byte7=%c\n", (int)AY_GREETING.len, AY_GREETING.ptr,
           (unsigned long)AY_GREETING.len, (unsigned long)ay_greeting_len(), ay_greeting_byte(7));
    unsigned sum = 0;
    for (uintptr_t i = 0; i < AY_PRIMES.len; i++) sum += AY_PRIMES.ptr[i];
    printf("primes len=%lu c_sum=%u rust_sum=%u\n", (unsigned long)AY_PRIMES.len, sum, ay_primes_sum());
    printf("ops c=%u,%u rust=%u,%u\n", AY_OPS[0](21), AY_OPS[1](12), ay_apply(0, 21), ay_apply(1, 12));
    printf("self_ref=%x identity=%d rust_addr=%d\n", ay_self_ref(), AY_SELF_REF == &AY_TARGET,
           ay_target_addr() == (uintptr_t)&AY_TARGET);
    printf("table=%u,%u\n", ay_table_at(0), ay_table_at(3));
    return 0;
}
"#;

const LAYOUT_MODEL: &str = "zero_initial=0 zero_sum=0\n\
zero_addr_identity=1\n\
bump=5 bump2=106 c_view=106 sum=106\n\
greeting=hello, statics len=14 rust_len=14 byte7=s\n\
primes len=6 c_sum=41 rust_sum=41\n\
ops c=42,144 rust=42,144\n\
self_ref=5151 identity=1 rust_addr=1\n\
table=11,44\n";

/// The bounds control: index 4 of the four-entry `AY_TABLE`.
const BOUNDS_CONTROL: &str = r#"#include <stdint.h>
#include <stdio.h>
extern uint32_t ay_table_at(uintptr_t);
int main(void) {
    printf("AY_TABLE[3]=%u\n", ay_table_at(3));
    fflush(stdout);
    printf("AY_TABLE[4]=%u\n", ay_table_at(4));
    return 0;
}
"#;

/// One crate of this target and the extra compile flags it takes.
struct Crate {
    name: &'static str,
    source: String,
    flags: &'static [&'static str],
}

/// One linked executable: a driver of one crate, its model stdout and ending.
struct Driver {
    name: &'static str,
    crate_name: &'static str,
    source: String,
    model: &'static str,
    ending: Ending,
}

fn crates() -> Vec<Crate> {
    let darwin = &["-Cdebug-assertions=off"];
    vec![
        Crate {
            name: "immutable",
            source: STATIC_CRATE.into(),
            flags: &[],
        },
        Crate {
            name: "mutable",
            source: MUTABLE_CRATE.into(),
            flags: &[],
        },
        Crate {
            name: "overaligned",
            source: OVERALIGNED_CRATE.into(),
            flags: darwin,
        },
        Crate {
            name: "externs",
            source: EXTERN_CRATE.into(),
            flags: darwin,
        },
        Crate {
            name: "layout",
            source: LAYOUT_CRATE.into(),
            flags: &[],
        },
    ]
}

fn drivers() -> Vec<Driver> {
    vec![
        Driver {
            name: "immutable",
            crate_name: "immutable",
            source: DRIVER_C.into(),
            model: "",
            ending: Ending::Exit(0),
        },
        Driver {
            name: "readonly_store",
            crate_name: "immutable",
            source: READONLY_CONTROL.into(),
            model: "AY_STATIC_N=0xdeadbeef\n",
            ending: Ending::Signal(SIGSEGV),
        },
        Driver {
            name: "mutable",
            crate_name: "mutable",
            source: MUTABLE_DRIVER.into(),
            model: "",
            ending: Ending::Exit(0),
        },
        Driver {
            name: "overaligned",
            crate_name: "overaligned",
            source: format!("{EXCLUSIVE_PRELUDE}{OVERALIGNED_DRIVER}"),
            model: "",
            ending: Ending::Exit(0),
        },
        Driver {
            name: "misaligned_exclusive",
            crate_name: "overaligned",
            source: format!("{EXCLUSIVE_PRELUDE}{MISALIGNED_CONTROL}"),
            model: "AY_WIDE_A%16=0\n",
            ending: Ending::Signal(SIGBUS),
        },
        Driver {
            name: "externs",
            crate_name: "externs",
            source: EXTERN_DRIVER.into(),
            model: "",
            ending: Ending::Exit(0),
        },
        Driver {
            name: "layout",
            crate_name: "layout",
            source: LAYOUT_DRIVER.into(),
            model: LAYOUT_MODEL,
            ending: Ending::Exit(0),
        },
        Driver {
            name: "out_of_bounds",
            crate_name: "layout",
            source: BOUNDS_CONTROL.into(),
            model: "AY_TABLE[3]=44\n",
            ending: Ending::Signal(SIGABRT),
        },
    ]
}

/// The storage class of a static's section in its object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Storage {
    /// `PROGBITS`, allocated, not writable.
    ReadOnly,
    /// `PROGBITS`, allocated and writable, no relocation in the static.
    Data,
    /// `NOBITS`, allocated and writable: zero-initialized.
    Bss,
    /// Allocated and writable at link time with `R_AARCH64_ABS64` slots
    /// (`.data.rel.ro`, read-only after relocation in the executable).
    Relocated,
}

/// (crate, symbol, size, alignment, storage, `R_AARCH64_ABS64` slots).
const STATICS: [(&str, &str, u64, u64, Storage, usize); 21] = [
    ("immutable", "AY_STATIC_N", 4, 4, Storage::ReadOnly, 0),
    ("immutable", "AY_STATIC_BYTES", 4, 1, Storage::ReadOnly, 0),
    ("immutable", "AY_STATIC_W", 8, 8, Storage::ReadOnly, 0),
    ("mutable", "AY_STATIC_MUT", 4, 4, Storage::Data, 0),
    ("overaligned", "AY_PAD_A", 8, 8, Storage::Data, 0),
    ("overaligned", "AY_PAD_B", 8, 8, Storage::Data, 0),
    ("overaligned", "AY_WIDE_A", 16, 16, Storage::Data, 0),
    ("overaligned", "AY_WIDE_B", 8, 8, Storage::Data, 0),
    ("overaligned", "AY_WIDE_C", 16, 16, Storage::Data, 0),
    ("overaligned", "AY_LINE", 64, 64, Storage::ReadOnly, 0),
    ("overaligned", "AY_PAD_C", 8, 8, Storage::ReadOnly, 0),
    ("overaligned", "AY_BIG", 16, 16, Storage::ReadOnly, 0),
    ("overaligned", "AY_REFS", 24, 8, Storage::Relocated, 3),
    ("layout", "AY_ZERO_WORDS", 64, 8, Storage::Bss, 0),
    ("layout", "AY_ZERO_CONST", 16, 4, Storage::ReadOnly, 0),
    ("layout", "AY_GREETING", 16, 8, Storage::Relocated, 1),
    ("layout", "AY_PRIMES", 16, 8, Storage::Relocated, 1),
    ("layout", "AY_OPS", 16, 8, Storage::Relocated, 2),
    ("layout", "AY_TARGET", 4, 4, Storage::ReadOnly, 0),
    ("layout", "AY_SELF_REF", 8, 8, Storage::Relocated, 1),
    ("layout", "AY_TABLE", 16, 4, Storage::ReadOnly, 0),
];

/// Each extern static of [`EXTERN_CRATE`] and its data relocations: `PTR` and
/// `PAIR[0]` name `AY_EXT_ONE`, `PAIR[1]` and `MIX.0` name `AY_EXT_TWO`.
const EXTERN_RELOCATIONS: [(&str, usize); 2] = [("AY_EXT_ONE", 2), ("AY_EXT_TWO", 2)];

fn compile(lane: &Path, krate: &Crate, opt: u32, bridge: Option<Bridge<'_>>) -> Vec<ObjectFacts> {
    let source = lane.join(format!("{}.rs", krate.name));
    std::fs::write(&source, &krate.source).unwrap();
    let object_dir = lane.join(format!("{}-objects", krate.name));
    std::fs::create_dir(&object_dir).unwrap();
    let mut command = twin::rustc_command();
    command.args(["--crate-type", "staticlib"]);
    twin::select_backend(&mut command, bridge);
    command
        .args([
            "-Ccodegen-units=1",
            "-Cpanic=abort",
            "--target",
            twin::TARGET,
        ])
        .arg(format!("-Copt-level={opt}"))
        .args(krate.flags)
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&object_dir)
        .arg(&source);
    let compiler = twin::compiler_name(bridge);
    let (output, transcript) = twin::run_bounded(
        &mut command,
        180,
        &lane.join(format!("{}-compile.log", krate.name)),
    );
    assert!(
        output.status.success(),
        "{compiler} O{opt} `{}` compile failed: {transcript}",
        krate.name
    );
    let objects = twin::inspect_objects(&object_dir);
    assert!(
        !objects.is_empty(),
        "{compiler} O{opt} `{}` emitted no object",
        krate.name
    );
    objects
}

/// The storage class and checks of one `#[no_mangle]` static.
fn check_static(
    objects: &[&ObjectFacts],
    name: &str,
    size: u64,
    align: u64,
    storage: Storage,
    pointers: usize,
    what: &str,
) -> Storage {
    let object = twin::definer(objects, name);
    let symbol = object.defined(name).unwrap();
    assert_eq!(
        (symbol.kind.as_str(), symbol.bind.as_str(), symbol.size),
        ("OBJECT", "GLOBAL", size),
        "{what}: `{name}` must be one GLOBAL OBJECT of {size} bytes"
    );
    let section = object.section_of(symbol);
    assert_eq!(
        object
            .sections
            .values()
            .filter(|other| other.name == section.name)
            .count(),
        1,
        "{what}: `{name}`'s section name {} is not unique in {}",
        section.name,
        object.file_name()
    );
    assert!(
        symbol.value % align == 0 && section.align >= align,
        "{what}: `{name}` at {:#x} in {} (align {}) is not {align}-aligned",
        symbol.value,
        section.name,
        section.align
    );
    let relocations = object.relocations_in(symbol);
    assert!(
        relocations.iter().all(|row| row.kind == "R_AARCH64_ABS64"),
        "{what}: `{name}` carries a relocation other than R_AARCH64_ABS64: {relocations:?}"
    );
    assert_eq!(
        relocations.len(),
        pointers,
        "{what}: `{name}` must carry {pointers} pointer relocation(s)"
    );
    let writable = section.flags.contains('W');
    assert!(
        section.flags.contains('A'),
        "{what}: `{name}` is not allocated"
    );
    let observed = match (section.kind.as_str(), writable, pointers) {
        ("PROGBITS", false, 0) => Storage::ReadOnly,
        ("PROGBITS", true, 0) => Storage::Data,
        ("NOBITS", true, 0) => Storage::Bss,
        ("PROGBITS", true, _) => Storage::Relocated,
        other => panic!(
            "{what}: `{name}` has unexpected storage {other:?} in {}",
            section.name
        ),
    };
    assert_eq!(
        observed, storage,
        "{what}: `{name}` is in {} [{}], not {storage:?} storage",
        section.name, section.flags
    );
    observed
}

/// Compile every crate with one compiler at one level, check its statics,
/// link and run every driver. Returns the lane rows and the storage classes.
fn lane(
    artifacts: &Path,
    opt: u32,
    bridge: Option<Bridge<'_>>,
) -> (
    Vec<LaneRow>,
    BTreeMap<&'static str, Storage>,
    serde_json::Value,
) {
    let compiler = twin::compiler_name(bridge);
    let lane = artifacts.join(format!("{compiler}_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let mut objects: BTreeMap<&'static str, Vec<ObjectFacts>> = BTreeMap::new();
    for krate in crates() {
        objects.insert(krate.name, compile(&lane, &krate, opt, bridge));
    }
    let what = format!("{compiler} O{opt}");
    let mut storage = BTreeMap::new();
    let mut pointer_relocations = 0;
    for (krate, name, size, align, class, pointers) in STATICS {
        let linked: Vec<&ObjectFacts> = objects[krate].iter().collect();
        storage.insert(
            name,
            check_static(&linked, name, size, align, class, pointers, &what),
        );
        pointer_relocations += pointers;
    }
    let externs: Vec<&ObjectFacts> = objects["externs"].iter().collect();
    for (name, expected) in EXTERN_RELOCATIONS {
        assert!(
            externs.iter().any(|facts| facts.imports(name))
                && externs.iter().all(|facts| facts.defined(name).is_none()),
            "{what}: `{name}` must be imported, never defined"
        );
        let slots = externs
            .iter()
            .flat_map(|facts| {
                facts.relocations.iter().filter(move |row| {
                    row.kind == "R_AARCH64_ABS64"
                        && !row.section.starts_with(".text")
                        && !row.section.starts_with(".eh_frame")
                        && facts.symbol(row.symbol_index).name == name
                })
            })
            .count();
        assert_eq!(slots, expected, "{what}: data relocations naming `{name}`");
        pointer_relocations += expected;
    }
    let mut rows = Vec::new();
    let mut abort_stubs = 0;
    for driver in drivers() {
        let run_dir = lane.join(driver.name);
        std::fs::create_dir(&run_dir).unwrap();
        let linked: Vec<&ObjectFacts> = objects[driver.crate_name].iter().collect();
        let source = run_dir.join("driver.c");
        std::fs::write(&source, &driver.source).unwrap();
        let executable = run_dir.join(format!("{}.elf", driver.name));
        let mut command = Command::new("cc");
        command.arg("-o").arg(&executable).arg(&source);
        let (stubs, count) = twin::abort_stubs(&run_dir, &linked);
        if let Some(stubs) = stubs {
            command.arg(stubs);
        }
        abort_stubs += count;
        for facts in &linked {
            command.arg(&facts.path);
        }
        twin::checked(&mut command, 60, &run_dir.join("link.log"));
        let row = twin::model_runs(
            &run_dir,
            &executable,
            driver.name,
            compiler,
            opt,
            RUNS_PER_LANE,
            driver.ending,
            driver.model,
        );
        // The only modelled abort is the out-of-bounds control's bounds-check
        // panic edge; a different stub would be a different program.
        if driver.ending == Ending::Signal(SIGABRT) {
            row.assert_aborted_through(BOUNDS_PANIC);
        }
        rows.push(row);
    }
    let objects_row = serde_json::json!({
        "compiler": compiler,
        "opt_level": opt,
        "statics": STATICS.len(),
        "pointer_relocations": pointer_relocations,
        "extern_imports": EXTERN_RELOCATIONS.len(),
        "abort_stubs": abort_stubs,
        "storage": storage.iter().map(|(name, class)| (name.to_string(), format!("{class:?}")))
            .collect::<BTreeMap<String, String>>(),
    });
    (rows, storage, objects_row)
}

#[test]
fn static_data_matches_llvm_and_the_model_linux() {
    twin::require_knobs("static_data_linux");
    let artifacts = twin::Artifacts::new("trust-cg-static-data-linux", KEEP_ARTIFACTS);
    let root = artifacts.root.clone();
    twin::require_host(&root);
    let (backend, digest) = twin::backend();
    let bridge = Bridge {
        path: &backend,
        knobs: twin::NO_PROOF_CERTS,
    };
    let mut lanes = Vec::new();
    let mut objects = Vec::new();
    for opt in twin::OPT_LEVELS {
        let (cg_rows, cg_storage, cg_objects) = lane(&root, opt, Some(bridge));
        let (llvm_rows, llvm_storage, llvm_objects) = lane(&root, opt, None);
        assert_eq!(
            cg_storage, llvm_storage,
            "O{opt}: the CG statics' storage classes differ from the LLVM twin's"
        );
        lanes.extend(cg_rows);
        lanes.extend(llvm_rows);
        objects.push(cg_objects);
        objects.push(llvm_objects);
        assert_eq!(
            twin::sha256(&backend),
            digest,
            "backend changed during O{opt}"
        );
    }
    let names: Vec<&str> = drivers().iter().map(|driver| driver.name).collect();
    twin::assert_twins_agree(&lanes, &names);
    let models: BTreeMap<String, String> = drivers()
        .iter()
        .map(|driver| {
            (
                driver.name.to_string(),
                twin::sha256_of(driver.model.as_bytes(), &root.join("model.txt")),
            )
        })
        .collect();
    twin::print_marker(
        MARKER,
        serde_json::json!({
            "runs_per_lane": RUNS_PER_LANE,
            "lanes": lanes.iter().map(LaneRow::json).collect::<Vec<_>>(),
            "objects": objects,
            "model_sha256": models,
        }),
        &digest,
    );
    artifacts.finish();
}

#[test]
fn darwin_fixtures_are_the_ones_this_target_runs() {
    // The Darwin crates stay unchanged; only the over-aligned driver gains the
    // prelude, and the prelude only redefines the one atomic it uses.
    assert_eq!(OVERALIGNED_DRIVER.matches("__atomic_fetch_add(").count(), 2);
    assert_eq!(EXCLUSIVE_PRELUDE.matches("#define").count(), 1);
    let names: Vec<&str> = drivers().iter().map(|driver| driver.name).collect();
    assert_eq!(
        names,
        [
            "immutable",
            "readonly_store",
            "mutable",
            "overaligned",
            "misaligned_exclusive",
            "externs",
            "layout",
            "out_of_bounds"
        ]
    );
    for (krate, name, ..) in STATICS {
        let source = crates()
            .into_iter()
            .find(|candidate| candidate.name == krate)
            .unwrap()
            .source;
        assert!(
            source.contains(&format!("static {name}:"))
                || source.contains(&format!("static mut {name}:")),
            "{name} is not a static of {krate}"
        );
    }
}
