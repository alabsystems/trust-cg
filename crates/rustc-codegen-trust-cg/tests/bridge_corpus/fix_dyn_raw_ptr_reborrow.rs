// CORPUS FIXTURE — `&raw const/mut (*r)` on a `&dyn Trait`, into a SLOT-BACKED
// `*const/*mut dyn Trait`.
//
// This is the last statement of `alloc::boxed::Box::<dyn Error + Send + Sync>::
// into_raw` (`_3 = &mut (*_7); _0 = &raw mut (*_3)`, with `_0` returned by value
// and therefore slot-backed), and it was a `library/alloc` census root reading
// `memory-backed aggregate assignment Rvalue::RValue::RawPtr` — the `Rvalue::Ref`
// arm for the very same statement one line earlier already lowered, and its
// `Rvalue::RawPtr` twin did not exist.
//
// THE FAILURE MODE IT PINS. A `*mut dyn Trait` is `{ data, vtable }`. Writing one
// lane and not the other leaves the vtable half uninitialized, so the virtual call
// through the returned pointer jumps to whatever was in the slot; writing them in
// the wrong ORDER calls through the DATA pointer. Both show up here as a value
// that differs from LLVM's, or as a trap. Two distinct impls are used so a
// single-vtable shortcut cannot pass: `A::v` and `B::v` return different
// functions of different field counts.
//
// REVERT BEHAVIOUR (measured on this base, 2026-09-26): `to_raw` is refused with
// `memory-backed aggregate assignment Rvalue::RawPtr`, which carries NO `[TCG-...]`
// tag, so this harness reports it as a CRASH-grade failure ("failed WITHOUT a
// named [TCG-...] refusal") rather than an honest INCOMPLETE. That is deliberate:
// the row cannot go quiet.
//
// `wrapping_mul`/`wrapping_add` rather than `*`/`+`: an overflow-checked operation
// emits `AArch64::CSet`, which has no opcode-proof mapping on this host
// (`[TCG-PROOF-465]`) and would make both rows INCOMPLETE for a reason that has
// nothing to do with this lane.
//
// Edition 2015 (the harness passes no `--edition`).
#![allow(dead_code)]

trait Sp { fn v(&self) -> i64; }
struct A(i64);
struct B(i64, i64);
impl Sp for A { fn v(&self) -> i64 { self.0.wrapping_mul(3).wrapping_add(1) } }
impl Sp for B { fn v(&self) -> i64 { self.0.wrapping_mul(100).wrapping_add(self.1) } }

#[inline(never)]
fn to_raw<'a>(r: &'a (dyn Sp + 'a)) -> *const (dyn Sp + 'a) { &raw const *r }

#[inline(never)]
fn call_it(p: *const (dyn Sp + '_)) -> i64 { unsafe { (&*p).v() } }

fn main() {
    let a = A(7);
    let b = B(5, 9);
    let x = call_it(to_raw(&a));
    let y = call_it(to_raw(&b));
    println!("x={} y={}", x, y);
}
