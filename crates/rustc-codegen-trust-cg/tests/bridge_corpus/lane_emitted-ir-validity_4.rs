// CORPUS FIXTURE — lane emitted-ir-validity, shape 4: a reference to a
// SUB-AGGREGATE field at layout OFFSET 0 of a struct read through `&self`,
// returned as `&Field` (`SocketAddrV6::ip` / `SocketAddrV4::ip` in core: the
// address record at offset 0 of the socket address). The borrow's address IS
// the base pointer, and the bridge bound the base VALUE (typed
// `Ref(Tuple(outer))`) to the `&Field` local, so trust-cg's return-signature
// check refused with "has Ref(Tuple([I16, I16, I16])), expected
// Ref(Tuple([I8, I8, I8, I8]))". The value is now retyped through an explicit
// `PtrToPtr` cast. The printed values come back through the returned field
// reference, so a wrong pointee type or offset shows up. The accessors are
// reached through fn POINTERS: a DIRECT call of a `-> &Aggregate` fn is a
// separate (call-site) refusal owned by another lane.
use std::hint::black_box;

#[derive(Clone, Copy)]
struct Addr4 {
    a: u8,
    b: u8,
    c: u8,
    d: u8,
}

struct Sock4 {
    ip: Addr4,
    port: u16,
}

impl Sock4 {
    #[inline(never)]
    fn ip(&self) -> &Addr4 {
        &self.ip
    }
    #[inline(never)]
    fn port(&self) -> u16 {
        self.port
    }
}

struct Lo3 {
    x: u16,
    y: u16,
    z: u16,
}

struct Pair {
    lo: Lo3,
    hi: u32,
}

impl Pair {
    #[inline(never)]
    fn lo(&self) -> &Lo3 {
        &self.lo
    }
}

#[inline(never)]
fn sum4(a: &Addr4) -> u32 {
    a.a as u32 + a.b as u32 * 2 + a.c as u32 * 3 + a.d as u32 * 4
}

fn main() {
    let s = Sock4 {
        ip: Addr4 { a: black_box(10), b: 0, c: 0, d: black_box(7) },
        port: black_box(8080),
    };
    let ip_of: fn(&Sock4) -> &Addr4 = black_box(Sock4::ip);
    let ip = ip_of(&s);
    println!("{}", sum4(ip));
    println!("{}", ip.d as u16 + s.port());
    let p = Pair { lo: Lo3 { x: black_box(3), y: 4, z: 5 }, hi: black_box(9) };
    let lo_of: fn(&Pair) -> &Lo3 = black_box(Pair::lo);
    let lo = lo_of(&p);
    println!("{}", lo.x as u32 + lo.y as u32 + lo.z as u32 + p.hi);
}
