// CORPUS FIXTURE — FUZZ-5: an `extern "C"` (C-ABI) function taking a by-value
// aggregate with a System V SSE (floating-point) eightbyte (`{ i64, f64 }` =
// one INTEGER + one SSE eightbyte). The System V C ABI passes the SSE eightbyte
// in an XMM register (and the INTEGER eightbyte in a GPR). The bridge originally
// built a by-value aggregate's ABI as uniform INTEGER lanes, marshaling every
// eightbyte through a GPR — self-consistent inside a pure-bridge program (so a
// rustc-vs-rustc differential MATCHES, which is why this fixture passes the
// corpus) but a SILENT WRONG VALUE at a real ABI boundary to / from
// independently-compiled (clang / LLVM) code (found by the FUZZ-5 clang-oracle
// differential). The bridge now threads CLASS-CORRECT per-eightbyte SSE/INTEGER
// lane types so the SSE eightbyte routes to XMM, matching clang/LLVM exactly —
// this program now COMPILES and its exit MATCHES LLVM. The full clang-oracle
// conformance validation (both directions, all SSE shapes, O0/O2/O3) lives in the
// pinned `m136_x86_c_abi_sse_aggregate` test. (The equivalent `extern "Rust"`
// shape is unchanged — see the `#69` mixed-int-sse fixture.)
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;
#[repr(C)]
#[derive(Clone, Copy)]
struct Mixed {
    a: i64,
    x: f64,
}
#[inline(never)]
extern "C" fn use_mixed(m: Mixed) -> i64 {
    m.a + (m.x as i64)
}
#[no_mangle]
pub extern "C" fn main() -> i32 {
    let m = Mixed {
        a: black_box(7),
        x: black_box(35.0_f64),
    };
    (use_mixed(black_box(m)) & 0xff) as i32
}
