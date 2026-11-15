// CORPUS FIXTURE: a borrow of a SIZED PREFIX FIELD of a slice-tail DST whose
// DESTINATION local is a SCALAR CELL.
//
// `_3 = &((*_1).1: u64)` with `_1: &Hdr<[u8]>` is lowered by `slice_tail::assign`,
// which runs before every other `lower_assign` arm. `_3` becomes a scalar cell
// when its own address is taken in the same body: `_2 = &_3` passed to a call
// (the ref-of-ref chain rule) or moved into an aggregate (the aggregate rule).
// A cell is read back from memory, so the borrow must be STORED into the cell;
// an SSA-only binding leaves the cell uninitialized and the callee
// dereferences whatever the stack held there.
//
// MIR at `-Copt-level=0` (the pinned Trust compiler, 2026-09-28):
//   direct:     _3 = &((*_1).1: u64);      _2 = &_3; read(copy _2)
//   direct_raw: _3 = &raw const ((*_1).1); _2 = &_3; read_raw(copy _2)
//   tup:        _4 = &((*_1).1: u64);      _3 = &_4; _2 = (move _3, const 1)
//
// Measured on aarch64-apple-darwin before the fix, with `no-proof-certs`: LLVM
// prints 72623859790382856 three times; the bridge binary aborted with a stack
// overflow at `-Copt-level=0` and died with SIGSEGV at `-Copt-level=2`.
//
// Every value is printed from a bare local (the bridge's `core::fmt`
// interception declines projected argument places).

#![allow(dead_code)]

struct Hdr<T: ?Sized> {
    a: u8,
    n: u64,
    c: u16,
    tail: T,
}

#[inline(never)]
fn read(x: &&u64) -> u64 {
    **x
}

#[inline(never)]
fn read_raw(x: &*const u64) -> u64 {
    unsafe { **x }
}

#[inline(never)]
fn direct(h: &Hdr<[u8]>) -> u64 {
    read(&&h.n)
}

#[inline(never)]
fn direct_raw(h: *const Hdr<[u8]>) -> u64 {
    read_raw(&unsafe { &raw const (*h).n })
}

#[inline(never)]
fn tup(h: &Hdr<[u8]>) -> u64 {
    let t = (&&h.n, 1u64);
    read(t.0)
}

fn main() {
    let v: Hdr<[u8; 3]> = Hdr {
        a: 7,
        n: 0x0102_0304_0506_0708,
        c: 0xBEEF,
        tail: [1, 2, 3],
    };
    let h: &Hdr<[u8]> = &v;
    let d = direct(h);
    let r = direct_raw(h);
    let t = tup(h);
    println!("direct={}", d);
    println!("raw={}", r);
    println!("tup={}", t);
}
