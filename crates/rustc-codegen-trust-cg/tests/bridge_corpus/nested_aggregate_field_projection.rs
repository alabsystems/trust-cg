#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box as bb;

// A struct CONSTRUCTION whose nested-aggregate field is sourced from a PROJECTION of
// a by-value aggregate argument (`Outer { inner: o.inner, k: o.k + 1 }`). rustc spills
// the projection to a temp (`_2 = move (o.0: Inner); _0 = Outer { inner: move _2, .. }`)
// and passes/returns the whole nested aggregate by value, so this exercises the ENTIRE
// nested-aggregate-leaf plumbing at once:
//   * packing a SCALARIZED aggregate WITH a nested aggregate field into a by-value
//     call-arg slot (`pack_scalarized_aggregate_byval_slot` -> flat-leaf enumeration),
//   * loading a memory-backed source's nested-aggregate field into scalarized flat
//     bindings (`lower_memory_nested_aggregate_field_use`),
//   * storing a scalarized nested-aggregate operand into a memory slot at its byte
//     offsets (`store_operand_into_memory_at` scalarized-source recursion),
//   * copying a whole nested-aggregate field mem->mem for a function that RETURNS it.
//
// `Inner { a: i8, b: i64 }` is field-REORDERED by rustc (b@0, a@8), and `Outer2` adds a
// 3rd nesting level, so a wrong byte offset at any level yields a different value than
// the LLVM oracle. Every field feeds the result; distinct per-field weights make any
// mis-addressed leaf diverge.
struct Inner {
    a: i8,
    b: i64,
}
struct Outer {
    inner: Inner,
    k: i64,
}
struct Outer2 {
    mid: Outer,
    n: i64,
}

#[inline(never)]
fn mk(o: Outer) -> Outer {
    Outer {
        inner: o.inner,
        k: o.k + 1,
    }
}

#[inline(never)]
fn mk2(o: Outer2) -> Outer2 {
    Outer2 {
        mid: o.mid,
        n: o.n + 1,
    }
}

#[inline(never)]
fn take_inner(o: Outer) -> Inner {
    o.inner
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let o = Outer {
        inner: Inner {
            a: bb(3i8),
            b: bb(4i64),
        },
        k: bb(5i64),
    };
    let r = mk(o);
    // r = Outer { inner: Inner { a: 3, b: 4 }, k: 6 }
    let part1 = (r.inner.a as i64) * 1 + r.inner.b * 10 + r.k * 100; // 3 + 40 + 600 = 643

    let o2 = Outer2 {
        mid: Outer {
            inner: Inner {
                a: bb(1i8),
                b: bb(2i64),
            },
            k: bb(3i64),
        },
        n: bb(4i64),
    };
    let s = mk2(o2);
    // s = Outer2 { mid: Outer { inner: Inner { a: 1, b: 2 }, k: 3 }, n: 5 }
    let part2 = (s.mid.inner.a as i64) + s.mid.inner.b * 10 + s.mid.k * 100 + s.n * 1000;
    // 1 + 20 + 300 + 5000 = 5321

    let inner = take_inner(Outer {
        inner: Inner {
            a: bb(7i8),
            b: bb(8i64),
        },
        k: bb(9i64),
    });
    let part3 = (inner.a as i64) + inner.b * 10; // 7 + 80 = 87

    ((part1 + part2 + part3) & 0x7f) as i32
}
