// CORPUS FIXTURE — lane discriminant-consts-operands: `Rvalue::Discriminant`
// of a FIELDLESS Direct-tagged enum where the source is (a) a scalar ENTRY ARG
// with no prior aggregate binding (`Ordering::then_with`, `atomic_load`'s
// `order`), (b) `(*&arg)` of such an arg (`Ordering::as_raw`), (c) the `Some`
// payload of a niche `Option<Fieldless>` (`FormattingOptions::debug_as_hex`),
// and (d) a field read through `&Struct` (`ParseIntError`'s `match self.kind`).
// Every printed value depends on the decoded discriminant; a wrong widening
// (zero- vs sign-extension of the `#[repr(i8)]` tag) or a wrong byte offset
// changes the output. The structs live in statics so `main` never builds an
// enum-field aggregate (a shape outside this lane); the buffers below are
// written through raw pointers for the same reason.
#![feature(core_intrinsics)]
#![allow(internal_features)]
#[derive(Clone, Copy)]
enum Order { Relaxed, Release, Acquire, AcqRel, SeqCst }
#[repr(i8)]
#[derive(Clone, Copy)]
enum Sign { Neg = -1, Zero = 0, Pos = 1 }
#[derive(Clone, Copy)]
enum Hex { Lower, Upper }
#[derive(Clone, Copy)]
enum Kind { Empty, Invalid, Overflow }
struct Err { code: u32, kind: Kind }
static ERR0: Err = Err { code: 1, kind: Kind::Empty };
static ERR1: Err = Err { code: 2, kind: Kind::Invalid };
static ERR2: Err = Err { code: 3, kind: Kind::Overflow };

#[inline(never)]
fn order_code(o: Order) -> u32 {
    match o { Order::Relaxed => 10, Order::Release => 20, Order::Acquire => 30, Order::AcqRel => 40, Order::SeqCst => 50 }
}
#[inline(never)]
fn sign_raw(s: Sign) -> i8 { unsafe { core::intrinsics::discriminant_value(&s) } }
#[inline(never)]
fn sign_wide(s: Sign) -> i64 { match s { Sign::Neg => -7, Sign::Zero => 0, Sign::Pos => 7 } }
#[inline(never)]
fn hex_flag(h: Option<Hex>) -> u32 {
    match h { None => 0, Some(Hex::Lower) => 16, Some(Hex::Upper) => 32 }
}
#[inline(never)]
fn describe(e: &Err) -> u32 {
    match e.kind { Kind::Empty => 100, Kind::Invalid => 200, Kind::Overflow => 300 }
}
#[inline(never)]
fn code_of(e: &Err) -> u32 { e.code }
fn main() {
    let mut acc = 0u32;
    acc = acc * 3 + order_code(Order::Relaxed);
    acc = acc * 3 + order_code(Order::Release);
    acc = acc * 3 + order_code(Order::Acquire);
    acc = acc * 3 + order_code(Order::AcqRel);
    acc = acc * 3 + order_code(Order::SeqCst);
    println!("orders {}", acc);
    println!("neg raw {} wide {}", sign_raw(Sign::Neg), sign_wide(Sign::Neg));
    println!("zero raw {} wide {}", sign_raw(Sign::Zero), sign_wide(Sign::Zero));
    println!("pos raw {} wide {}", sign_raw(Sign::Pos), sign_wide(Sign::Pos));
    println!("hex {} {} {}", hex_flag(None), hex_flag(Some(Hex::Lower)), hex_flag(Some(Hex::Upper)));
    println!("err {} {}", code_of(&ERR0), describe(&ERR0));
    println!("err {} {}", code_of(&ERR1), describe(&ERR1));
    println!("err {} {}", code_of(&ERR2), describe(&ERR2));
}
