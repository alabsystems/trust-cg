// trust-cg-codegen/wasm/helpers.rs - runtime helpers written in trust-ir
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runtime helpers the lane emits a `call` to for operations wasm has no
//! instruction for. Each is written HERE IN TRUST-IR and lowered by this same
//! backend, so it goes through the same lowering, structural checks and
//! differential oracle as any other trust-ir the lane compiles. Nothing about
//! a helper is hand-emitted wasm.
//!
//! * `fmod` / `fmodf` (float remainder). A relocatable object calls the
//!   library instead (`fmod` / `fmodf` from compiler-builtins, exactly what
//!   LLVM's wasm32 lowering of `frem` calls); a CLOSED module has no library,
//!   so it carries its own copy. `fmod` is musl's exact integer algorithm
//!   (`src/math/fmod.c`, MIT): the remainder of an IEEE-754 division is always
//!   exactly representable, so it is computed on the significands by
//!   shift-and-subtract, never by a rounded `x - trunc(x / y) * y`. The two
//!   loops musl uses to normalize a significand are replaced by a
//!   count-leading-zeros, which computes the same shift.
//! * 128-bit division and remainder ([`divmod128_module`]). Both a closed
//!   module and an object carry ONE copy, whatever the number of division
//!   sites; there is no library dependency. See [`DIVMOD128_TEMPLATE`] (O0)
//!   and [`DIVMOD128_ESTIMATE_TEMPLATE`] (O1 and above) for the algorithms
//!   and their result on the inputs trust-ir leaves undefined, and
//!   [`divmod128_helper_name`] for how an object names it.

use trust_ir::Module;

use crate::pipeline::OptLevel;

use super::lower::WasmLowerError;

/// The exported name of the `f64` remainder helper in a closed module.
pub const FMOD_HELPER: &str = "__tcg_fmod";
/// The exported name of the `f32` remainder helper in a closed module.
pub const FMODF_HELPER: &str = "__tcg_fmodf";

/// The helper template, with `{F}` the float type, `{T}`/`{S}` the unsigned /
/// signed integer of the same width, and the format's field widths.
const FMOD_TEMPLATE: &str = r#"
fn @{NAME}(functy.0) {
bbentry(%x: {F}, %y: {F}):
    %c0 = const {T} 0
    %c1 = const {T} 1
    %cnorm = const {T} {NORM}
    %cmant = const {T} {MSHIFT}
    %csign = const {T} {SSHIFT}
    %cexp = const {T} {EXPMASK}
    %cmask = const {T} {MANTMASK}
    %chid = const {T} {HIDDEN}
    %cadj = const {T} {CLZADJ}
    %s0 = const {S} 0
    %s1 = const {S} 1
    %fz = const {F} 0.0
    %ux = bitcast {F} %x to {T}
    %uy = bitcast {F} %y to {T}
    %exs = lshr {T} %ux, %cmant
    %exu = and {T} %exs, %cexp
    %eys = lshr {T} %uy, %cmant
    %eyu = and {T} %eys, %cexp
    %sx = lshr {T} %ux, %csign
    %ay = shl {T} %uy, %c1
    %yzero = icmp eq {T} %ay, %c0
    %ynan = fcmp une {F} %y, %y
    %xinf = icmp eq {T} %exu, %cexp
    %sp1 = or bool %yzero, %ynan
    %sp = or bool %sp1, %xinf
    condbr %sp, bbnan, bbcmp
bbnan:
    %xy = fmul {F} %x, %y
    %nanr = fdiv {F} %xy, %xy
    ret %nanr
bbcmp:
    %ax = shl {T} %ux, %c1
    %le = icmp ule {T} %ax, %ay
    condbr %le, bbsmall, bbnormx
bbsmall:
    %eq = icmp eq {T} %ax, %ay
    condbr %eq, bbzero, bbretx
bbzero:
    %zr = fmul {F} %fz, %x
    ret %zr
bbretx:
    ret %x
bbnormx:
    %exz = icmp eq {T} %exu, %c0
    condbr %exz, bbsubx, bbnormalx
bbsubx:
    %ix = shl {T} %ux, %cnorm
    %lzx = ctlz {T} %ix
    %lzxs = bitcast {T} %lzx to {S}
    %exa = sub {S} %s0, %lzxs
    %shx = add {T} %lzx, %c1
    %uxa = shl {T} %ux, %shx
    br bbnormy(%exa, %uxa)
bbnormalx:
    %uxm = and {T} %ux, %cmask
    %uxb = or {T} %uxm, %chid
    %exb = bitcast {T} %exu to {S}
    br bbnormy(%exb, %uxb)
bbnormy(%ex: {S}, %u0: {T}):
    %eyz = icmp eq {T} %eyu, %c0
    condbr %eyz, bbsuby, bbnormaly
bbsuby:
    %iy = shl {T} %uy, %cnorm
    %lzy = ctlz {T} %iy
    %lzys = bitcast {T} %lzy to {S}
    %eya = sub {S} %s0, %lzys
    %shy = add {T} %lzy, %c1
    %uya = shl {T} %uy, %shy
    br bbyready(%eya, %uya)
bbnormaly:
    %uym = and {T} %uy, %cmask
    %uyb = or {T} %uym, %chid
    %eyb = bitcast {T} %eyu to {S}
    br bbyready(%eyb, %uyb)
bbyready(%ey: {S}, %uyn: {T}):
    br bbloop(%ex, %u0)
bbloop(%e: {S}, %u: {T}):
    %more = icmp sgt {S} %e, %ey
    condbr %more, bbstep, bbtail(%e, %u)
bbstep:
    %d = sub {T} %u, %uyn
    %dn = lshr {T} %d, %csign
    %dneg = icmp ne {T} %dn, %c0
    condbr %dneg, bbshift(%u), bbstepnz
bbstepnz:
    %dz = icmp eq {T} %d, %c0
    condbr %dz, bbzero, bbshift(%d)
bbshift(%v: {T}):
    %v2 = shl {T} %v, %c1
    %e2 = sub {S} %e, %s1
    br bbloop(%e2, %v2)
bbtail(%et: {S}, %ut: {T}):
    %dt = sub {T} %ut, %uyn
    %dtn = lshr {T} %dt, %csign
    %dtneg = icmp ne {T} %dtn, %c0
    condbr %dtneg, bbnorm(%ut), bbtailnz
bbtailnz:
    %dtz = icmp eq {T} %dt, %c0
    condbr %dtz, bbzero, bbnorm(%dt)
bbnorm(%w: {T}):
    %lzw = ctlz {T} %w
    %shw = sub {T} %lzw, %cadj
    %w2 = shl {T} %w, %shw
    %shws = bitcast {T} %shw to {S}
    %ef = sub {S} %et, %shws
    %pos = icmp sgt {S} %ef, %s0
    condbr %pos, bbscaleup, bbscaledown
bbscaleup:
    %w3 = sub {T} %w2, %chid
    %efu = bitcast {S} %ef to {T}
    %efh = shl {T} %efu, %cmant
    %w4 = or {T} %w3, %efh
    br bbdone(%w4)
bbscaledown:
    %sd = sub {S} %s1, %ef
    %sdu = bitcast {S} %sd to {T}
    %w5 = lshr {T} %w2, %sdu
    br bbdone(%w5)
bbdone(%res: {T}):
    %sb = shl {T} %sx, %csign
    %rb = or {T} %res, %sb
    %r = bitcast {T} %rb to {F}
    ret %r
}
"#;

/// The 128-bit division helper the lane carries at O0 (the baseline, whose
/// text and so whose symbol an O0 object keeps unchanged):
/// `(nlo, nhi, dlo, dhi, out, mode) -> ()`.
///
/// It divides `n = nhi:nlo` by `d = dhi:dlo` (two `u64` halves each) and
/// stores the selected 128-bit result's halves at `out` (low) and `out + 8`
/// (high). `mode` bit 0 selects the remainder (else the quotient); bit 1
/// selects SIGNED division. A signed division divides the magnitudes and
/// negates: the quotient when the operands' signs differ, the remainder when
/// the dividend is negative (the remainder takes the dividend's sign). The
/// lane's call sites pass `mode` as a constant: 0 `udiv`, 1 `urem`, 2 `sdiv`,
/// 3 `srem`.
///
/// The unsigned core takes the cheapest exact path:
///
/// * `d == 0`: quotient all-ones, remainder `n` — the result the lane's
///   restoring shift-subtract produced for a zero divisor, kept so the
///   lowering of these inputs does not change. trust-ir makes division by
///   zero (and signed `MIN / -1`) undefined behaviour, so the lane never
///   traps on them and no program the interpreter accepts reaches this arm;
///   `MIN / -1` divides the magnitudes `2^127 / 1` and negates, giving `MIN`
///   with remainder 0, also as before;
/// * both high halves zero: one `u64` division and remainder;
/// * a divisor that fits in 64 bits: two-step long division. The high
///   quotient half is `nhi / dlo`; the low half divides the 128-bit
///   `(nhi % dlo):nlo`, whose quotient fits in 64 bits, by Knuth's algorithm D
///   on 32-bit digits in the form of Hacker's Delight `divlu` (normalize the
///   divisor by its leading zeros, estimate each quotient digit from the top
///   divisor digit, and correct the estimate at most twice);
/// * a divisor of more than 64 bits: `n < d` gives quotient 0; otherwise the
///   quotient has `s + 1` significant bits, `s = clz(dhi) - clz(nhi)`, and a
///   restoring shift-subtract runs exactly that many steps on `d << s`.
///
/// Every shift amount is in `0..64` (`x >> (64 - s)` is spelled
/// `(x >> 1) >> (63 - s)`), every `u64` division has a nonzero divisor, and
/// every other operation wraps, so the helper itself is free of undefined
/// behaviour on every input.
pub(crate) const DIVMOD128_TEMPLATE: &str = r#"
fn @{NAME}(functy.0) {
bbentry(%nlo: u64, %nhi: u64, %dlo: u64, %dhi: u64, %out: ptr, %mode: u32):
    %c0 = const u64 0
    %c1 = const u64 1
    %c32 = const u64 32
    %c63 = const u64 63
    %cmax = const u64 18446744073709551615
    %cdig = const u64 4294967295
    %cbase = const u64 4294967296
    %m0 = const u32 0
    %m1 = const u32 1
    %m2 = const u32 2
    %modes = and u32 %mode, %m2
    %signed = icmp ne u32 %modes, %m0
    %moder = and u32 %mode, %m1
    %wantrem = icmp ne u32 %moder, %m0
    %nsign = lshr u64 %nhi, %c63
    %nisneg = icmp ne u64 %nsign, %c0
    %na = and bool %signed, %nisneg
    %dsign = lshr u64 %dhi, %c63
    %disneg = icmp ne u64 %dsign, %c0
    %nb = and bool %signed, %disneg
    %nnlo = sub u64 %c0, %nlo
    %nlonz = icmp ne u64 %nlo, %c0
    %nborrow = zext bool %nlonz to u64
    %nnhi0 = sub u64 %c0, %nhi
    %nnhi = sub u64 %nnhi0, %nborrow
    %ulo = select u64 %na, %nnlo, %nlo
    %uhi = select u64 %na, %nnhi, %nhi
    %ndlo = sub u64 %c0, %dlo
    %dlonz = icmp ne u64 %dlo, %c0
    %dborrow = zext bool %dlonz to u64
    %ndhi0 = sub u64 %c0, %dhi
    %ndhi = sub u64 %ndhi0, %dborrow
    %vlo = select u64 %nb, %ndlo, %dlo
    %vhi = select u64 %nb, %ndhi, %dhi
    %vor = or u64 %vlo, %vhi
    %vzero = icmp eq u64 %vor, %c0
    condbr %vzero, bbdone(%cmax, %cmax, %ulo, %uhi), bbnonzero
bbnonzero:
    %vhizero = icmp eq u64 %vhi, %c0
    condbr %vhizero, bbnarrow, bbwide
bbnarrow:
    %uhizero = icmp eq u64 %uhi, %c0
    condbr %uhizero, bbword, bblong
bbword:
    %wq = udiv u64 %ulo, %vlo
    %wr = urem u64 %ulo, %vlo
    br bbdone(%wq, %c0, %wr, %c0)
bblong:
    %qhigh = udiv u64 %uhi, %vlo
    %khigh = urem u64 %uhi, %vlo
    %s = ctlz u64 %vlo
    %v = shl u64 %vlo, %s
    %vn1 = lshr u64 %v, %c32
    %vn0 = and u64 %v, %cdig
    %ks = shl u64 %khigh, %s
    %ulo1 = lshr u64 %ulo, %c1
    %s63 = sub u64 %c63, %s
    %ulox = lshr u64 %ulo1, %s63
    %un32 = or u64 %ks, %ulox
    %un10 = shl u64 %ulo, %s
    %un1 = lshr u64 %un10, %c32
    %un0 = and u64 %un10, %cdig
    %qe1 = udiv u64 %un32, %vn1
    %re1 = urem u64 %un32, %vn1
    br bbfixa(%qe1, %re1)
bbfixa(%qa: u64, %ra: u64):
    %qabig = icmp uge u64 %qa, %cbase
    condbr %qabig, bbdeca, bbchka
bbchka:
    %pa = mul u64 %qa, %vn0
    %rash = shl u64 %ra, %c32
    %ta = or u64 %rash, %un1
    %overa = icmp ugt u64 %pa, %ta
    condbr %overa, bbdeca, bbstepb(%qa)
bbdeca:
    %qad = sub u64 %qa, %c1
    %rad = add u64 %ra, %vn1
    %radsmall = icmp ult u64 %rad, %cbase
    condbr %radsmall, bbfixa(%qad, %rad), bbstepb(%qad)
bbstepb(%q1: u64):
    %un32sh = shl u64 %un32, %c32
    %un21a = or u64 %un32sh, %un1
    %q1v = mul u64 %q1, %v
    %un21 = sub u64 %un21a, %q1v
    %qe0 = udiv u64 %un21, %vn1
    %re0 = urem u64 %un21, %vn1
    br bbfixb(%qe0, %re0)
bbfixb(%qb: u64, %rb: u64):
    %qbbig = icmp uge u64 %qb, %cbase
    condbr %qbbig, bbdecb, bbchkb
bbchkb:
    %pb = mul u64 %qb, %vn0
    %rbsh = shl u64 %rb, %c32
    %tb = or u64 %rbsh, %un0
    %overb = icmp ugt u64 %pb, %tb
    condbr %overb, bbdecb, bbfinish(%qb)
bbdecb:
    %qbd = sub u64 %qb, %c1
    %rbd = add u64 %rb, %vn1
    %rbdsmall = icmp ult u64 %rbd, %cbase
    condbr %rbdsmall, bbfixb(%qbd, %rbd), bbfinish(%qbd)
bbfinish(%q0: u64):
    %un21sh = shl u64 %un21, %c32
    %un210 = or u64 %un21sh, %un0
    %q0v = mul u64 %q0, %v
    %rnorm = sub u64 %un210, %q0v
    %lrem = lshr u64 %rnorm, %s
    %q1sh = shl u64 %q1, %c32
    %lq = or u64 %q1sh, %q0
    br bbdone(%lq, %qhigh, %lrem, %c0)
bbwide:
    %hlt = icmp ult u64 %uhi, %vhi
    %heq = icmp eq u64 %uhi, %vhi
    %llt = icmp ult u64 %ulo, %vlo
    %eqlt = and bool %heq, %llt
    %nlessd = or bool %hlt, %eqlt
    condbr %nlessd, bbdone(%c0, %c0, %ulo, %uhi), bbshift
bbshift:
    %czn = ctlz u64 %uhi
    %czd = ctlz u64 %vhi
    %sh = sub u64 %czd, %czn
    %xhi0 = shl u64 %vhi, %sh
    %vlo1 = lshr u64 %vlo, %c1
    %sh63 = sub u64 %c63, %sh
    %vlox = lshr u64 %vlo1, %sh63
    %xhi1 = or u64 %xhi0, %vlox
    %xlo1 = shl u64 %vlo, %sh
    %steps = add u64 %sh, %c1
    br bbloop(%c0, %ulo, %uhi, %xlo1, %xhi1, %steps)
bbloop(%q: u64, %rlo: u64, %rhi: u64, %xlo: u64, %xhi: u64, %i: u64):
    %gth = icmp ugt u64 %rhi, %xhi
    %eqh = icmp eq u64 %rhi, %xhi
    %gel = icmp uge u64 %rlo, %xlo
    %eqge = and bool %eqh, %gel
    %ge = or bool %gth, %eqge
    %bit = zext bool %ge to u64
    %qsh = shl u64 %q, %c1
    %qn = or u64 %qsh, %bit
    %mlo = select u64 %ge, %xlo, %c0
    %mhi = select u64 %ge, %xhi, %c0
    %lbor = icmp ult u64 %rlo, %mlo
    %lborw = zext bool %lbor to u64
    %rlon = sub u64 %rlo, %mlo
    %rhia = sub u64 %rhi, %mhi
    %rhin = sub u64 %rhia, %lborw
    %xlos = lshr u64 %xlo, %c1
    %xhib = shl u64 %xhi, %c63
    %xlon = or u64 %xlos, %xhib
    %xhin = lshr u64 %xhi, %c1
    %in = sub u64 %i, %c1
    %more = icmp ne u64 %in, %c0
    condbr %more, bbloop(%qn, %rlon, %rhin, %xlon, %xhin, %in), bbdone(%qn, %c0, %rlon, %rhin)
bbdone(%oqlo: u64, %oqhi: u64, %orlo: u64, %orhi: u64):
    %rslo = select u64 %wantrem, %orlo, %oqlo
    %rshi = select u64 %wantrem, %orhi, %oqhi
    %qneg = xor bool %na, %nb
    %neg = select bool %wantrem, %na, %qneg
    %ngl = sub u64 %c0, %rslo
    %rslonz = icmp ne u64 %rslo, %c0
    %rsbor = zext bool %rslonz to u64
    %ngh0 = sub u64 %c0, %rshi
    %ngh = sub u64 %ngh0, %rsbor
    %fl = select u64 %neg, %ngl, %rslo
    %fh = select u64 %neg, %ngh, %rshi
    store u64 %fl, ptr %out
    %ione = const usize 1
    %hiptr = gep u64, ptr %out, %ione
    store u64 %fh, ptr %hiptr
    ret
}
"#;

/// The 128-bit division helper the lane carries at O1 and above: the
/// interface, modes, signs and fast paths of [`DIVMOD128_TEMPLATE`], except
/// that a divisor of more than 64 bits gets a quotient estimate in place of
/// the restoring shift-subtract. In full:
///
/// The helper: `(nlo, nhi, dlo, dhi, out, mode) -> ()`.
///
/// It divides `n = nhi:nlo` by `d = dhi:dlo` (two `u64` halves each) and
/// stores the selected 128-bit result's halves at `out` (low) and `out + 8`
/// (high). `mode` bit 0 selects the remainder (else the quotient); bit 1
/// selects SIGNED division. A signed division divides the magnitudes and
/// negates: the quotient when the operands' signs differ, the remainder when
/// the dividend is negative (the remainder takes the dividend's sign). The
/// lane's call sites pass `mode` as a constant: 0 `udiv`, 1 `urem`, 2 `sdiv`,
/// 3 `srem`.
///
/// The unsigned core takes the cheapest exact path:
///
/// * `d == 0`: quotient all-ones, remainder `n` — the result the lane's
///   restoring shift-subtract produced for a zero divisor, kept so the
///   lowering of these inputs does not change. trust-ir makes division by
///   zero (and signed `MIN / -1`) undefined behaviour, so the lane never
///   traps on them and no program the interpreter accepts reaches this arm;
///   `MIN / -1` divides the magnitudes `2^127 / 1` and negates, giving `MIN`
///   with remainder 0, also as before;
/// * both high halves zero: one `u64` division and remainder;
/// * a divisor that fits in 64 bits: two-step long division. The high
///   quotient half is `nhi / dlo`; the low half divides the 128-bit
///   `(nhi % dlo):nlo`, whose quotient fits in 64 bits, by Knuth's algorithm D
///   on 32-bit digits in the form of Hacker's Delight `divlu` (normalize the
///   divisor by its leading zeros, estimate each quotient digit from the top
///   divisor digit, and correct the estimate at most twice);
/// * a divisor of more than 64 bits: `n < d` gives quotient 0; otherwise the
///   quotient fits in 64 bits and is estimated by one 128-by-64 division
///   (Hacker's Delight `udivdi3` with 64-bit words): with `s = clz(dhi)`,
///   `v1` the top 64 bits of `d << s` (so `v1 >= 2^63`) and `n >> 1`
///   (whose high word is below `2^63 <= v1`, so the quotient fits),
///   `q1 = (n >> 1) / v1` by the `divlu` steps, then
///   `q0 = q1 >> (63 - s)`, decremented when nonzero, is the quotient or
///   one less; one comparison of `n - q0 * d` (the product's high word by
///   32-bit partial products, which cannot overflow because
///   `q0 * d <= n`) with `d` corrects it and gives the remainder.
///
/// The wide path carries its own copy of the `divlu` steps, without the
/// normalization (`v1` is normalized already) or the remainder, so the
/// 64-bit path's blocks are unchanged by it.
///
/// Every shift amount is in `0..64` (`x >> (64 - s)` is spelled
/// `(x >> 1) >> (63 - s)`), every `u64` division has a nonzero divisor, and
/// every other operation wraps, so the helper itself is free of undefined
/// behaviour on every input.
pub(crate) const DIVMOD128_ESTIMATE_TEMPLATE: &str = r#"
fn @{NAME}(functy.0) {
bbentry(%nlo: u64, %nhi: u64, %dlo: u64, %dhi: u64, %out: ptr, %mode: u32):
    %c0 = const u64 0
    %c1 = const u64 1
    %c32 = const u64 32
    %c63 = const u64 63
    %cmax = const u64 18446744073709551615
    %cdig = const u64 4294967295
    %cbase = const u64 4294967296
    %m0 = const u32 0
    %m1 = const u32 1
    %m2 = const u32 2
    %modes = and u32 %mode, %m2
    %signed = icmp ne u32 %modes, %m0
    %moder = and u32 %mode, %m1
    %wantrem = icmp ne u32 %moder, %m0
    %nsign = lshr u64 %nhi, %c63
    %nisneg = icmp ne u64 %nsign, %c0
    %na = and bool %signed, %nisneg
    %dsign = lshr u64 %dhi, %c63
    %disneg = icmp ne u64 %dsign, %c0
    %nb = and bool %signed, %disneg
    %nnlo = sub u64 %c0, %nlo
    %nlonz = icmp ne u64 %nlo, %c0
    %nborrow = zext bool %nlonz to u64
    %nnhi0 = sub u64 %c0, %nhi
    %nnhi = sub u64 %nnhi0, %nborrow
    %ulo = select u64 %na, %nnlo, %nlo
    %uhi = select u64 %na, %nnhi, %nhi
    %ndlo = sub u64 %c0, %dlo
    %dlonz = icmp ne u64 %dlo, %c0
    %dborrow = zext bool %dlonz to u64
    %ndhi0 = sub u64 %c0, %dhi
    %ndhi = sub u64 %ndhi0, %dborrow
    %vlo = select u64 %nb, %ndlo, %dlo
    %vhi = select u64 %nb, %ndhi, %dhi
    %vor = or u64 %vlo, %vhi
    %vzero = icmp eq u64 %vor, %c0
    condbr %vzero, bbdone(%cmax, %cmax, %ulo, %uhi), bbnonzero
bbnonzero:
    %vhizero = icmp eq u64 %vhi, %c0
    condbr %vhizero, bbnarrow, bbwide
bbnarrow:
    %uhizero = icmp eq u64 %uhi, %c0
    condbr %uhizero, bbword, bblong
bbword:
    %wq = udiv u64 %ulo, %vlo
    %wr = urem u64 %ulo, %vlo
    br bbdone(%wq, %c0, %wr, %c0)
bblong:
    %qhigh = udiv u64 %uhi, %vlo
    %khigh = urem u64 %uhi, %vlo
    %s = ctlz u64 %vlo
    %v = shl u64 %vlo, %s
    %vn1 = lshr u64 %v, %c32
    %vn0 = and u64 %v, %cdig
    %ks = shl u64 %khigh, %s
    %ulo1 = lshr u64 %ulo, %c1
    %s63 = sub u64 %c63, %s
    %ulox = lshr u64 %ulo1, %s63
    %un32 = or u64 %ks, %ulox
    %un10 = shl u64 %ulo, %s
    %un1 = lshr u64 %un10, %c32
    %un0 = and u64 %un10, %cdig
    %qe1 = udiv u64 %un32, %vn1
    %re1 = urem u64 %un32, %vn1
    br bbfixa(%qe1, %re1)
bbfixa(%qa: u64, %ra: u64):
    %qabig = icmp uge u64 %qa, %cbase
    condbr %qabig, bbdeca, bbchka
bbchka:
    %pa = mul u64 %qa, %vn0
    %rash = shl u64 %ra, %c32
    %ta = or u64 %rash, %un1
    %overa = icmp ugt u64 %pa, %ta
    condbr %overa, bbdeca, bbstepb(%qa)
bbdeca:
    %qad = sub u64 %qa, %c1
    %rad = add u64 %ra, %vn1
    %radsmall = icmp ult u64 %rad, %cbase
    condbr %radsmall, bbfixa(%qad, %rad), bbstepb(%qad)
bbstepb(%q1: u64):
    %un32sh = shl u64 %un32, %c32
    %un21a = or u64 %un32sh, %un1
    %q1v = mul u64 %q1, %v
    %un21 = sub u64 %un21a, %q1v
    %qe0 = udiv u64 %un21, %vn1
    %re0 = urem u64 %un21, %vn1
    br bbfixb(%qe0, %re0)
bbfixb(%qb: u64, %rb: u64):
    %qbbig = icmp uge u64 %qb, %cbase
    condbr %qbbig, bbdecb, bbchkb
bbchkb:
    %pb = mul u64 %qb, %vn0
    %rbsh = shl u64 %rb, %c32
    %tb = or u64 %rbsh, %un0
    %overb = icmp ugt u64 %pb, %tb
    condbr %overb, bbdecb, bbfinish(%qb)
bbdecb:
    %qbd = sub u64 %qb, %c1
    %rbd = add u64 %rb, %vn1
    %rbdsmall = icmp ult u64 %rbd, %cbase
    condbr %rbdsmall, bbfixb(%qbd, %rbd), bbfinish(%qbd)
bbfinish(%q0: u64):
    %un21sh = shl u64 %un21, %c32
    %un210 = or u64 %un21sh, %un0
    %q0v = mul u64 %q0, %v
    %rnorm = sub u64 %un210, %q0v
    %lrem = lshr u64 %rnorm, %s
    %q1sh = shl u64 %q1, %c32
    %lq = or u64 %q1sh, %q0
    br bbdone(%lq, %qhigh, %lrem, %c0)
bbwide:
    %hlt = icmp ult u64 %uhi, %vhi
    %heq = icmp eq u64 %uhi, %vhi
    %llt = icmp ult u64 %ulo, %vlo
    %eqlt = and bool %heq, %llt
    %nlessd = or bool %hlt, %eqlt
    condbr %nlessd, bbdone(%c0, %c0, %ulo, %uhi), bbshift
bbshift:
    %wsh = ctlz u64 %vhi
    %wvhi = shl u64 %vhi, %wsh
    %wvlo1 = lshr u64 %vlo, %c1
    %wsh63 = sub u64 %c63, %wsh
    %wvlox = lshr u64 %wvlo1, %wsh63
    %wv1 = or u64 %wvhi, %wvlox
    %wuhi = lshr u64 %uhi, %c1
    %wulo1 = lshr u64 %ulo, %c1
    %wuhib = shl u64 %uhi, %c63
    %wulo = or u64 %wulo1, %wuhib
    %wvn1 = lshr u64 %wv1, %c32
    %wvn0 = and u64 %wv1, %cdig
    %wun1 = lshr u64 %wulo, %c32
    %wun0 = and u64 %wulo, %cdig
    %wqe1 = udiv u64 %wuhi, %wvn1
    %wre1 = urem u64 %wuhi, %wvn1
    br bbwfixa(%wqe1, %wre1)
bbwfixa(%wqa: u64, %wra: u64):
    %wqabig = icmp uge u64 %wqa, %cbase
    condbr %wqabig, bbwdeca, bbwchka
bbwchka:
    %wpa = mul u64 %wqa, %wvn0
    %wrash = shl u64 %wra, %c32
    %wta = or u64 %wrash, %wun1
    %wovera = icmp ugt u64 %wpa, %wta
    condbr %wovera, bbwdeca, bbwstepb(%wqa)
bbwdeca:
    %wqad = sub u64 %wqa, %c1
    %wrad = add u64 %wra, %wvn1
    %wradsmall = icmp ult u64 %wrad, %cbase
    condbr %wradsmall, bbwfixa(%wqad, %wrad), bbwstepb(%wqad)
bbwstepb(%wq1: u64):
    %wun32sh = shl u64 %wuhi, %c32
    %wun21a = or u64 %wun32sh, %wun1
    %wq1v = mul u64 %wq1, %wv1
    %wun21 = sub u64 %wun21a, %wq1v
    %wqe0 = udiv u64 %wun21, %wvn1
    %wre0 = urem u64 %wun21, %wvn1
    br bbwfixb(%wqe0, %wre0)
bbwfixb(%wqb: u64, %wrb: u64):
    %wqbbig = icmp uge u64 %wqb, %cbase
    condbr %wqbbig, bbwdecb, bbwchkb
bbwchkb:
    %wpb = mul u64 %wqb, %wvn0
    %wrbsh = shl u64 %wrb, %c32
    %wtb = or u64 %wrbsh, %wun0
    %woverb = icmp ugt u64 %wpb, %wtb
    condbr %woverb, bbwdecb, bbwidefix(%wqb)
bbwdecb:
    %wqbd = sub u64 %wqb, %c1
    %wrbd = add u64 %wrb, %wvn1
    %wrbdsmall = icmp ult u64 %wrbd, %cbase
    condbr %wrbdsmall, bbwfixb(%wqbd, %wrbd), bbwidefix(%wqbd)
bbwidefix(%wq0: u64):
    %wq1sh = shl u64 %wq1, %c32
    %wlq = or u64 %wq1sh, %wq0
    %wd = sub u64 %c63, %wsh
    %wqe = lshr u64 %wlq, %wd
    %wqnz = icmp ne u64 %wqe, %c0
    %wqdec = zext bool %wqnz to u64
    %xq = sub u64 %wqe, %wqdec
    %wa0 = and u64 %xq, %cdig
    %wa1 = lshr u64 %xq, %c32
    %wb0 = and u64 %vlo, %cdig
    %wb1 = lshr u64 %vlo, %c32
    %wp00 = mul u64 %wa0, %wb0
    %wp01 = mul u64 %wa0, %wb1
    %wp10 = mul u64 %wa1, %wb0
    %wp11 = mul u64 %wa1, %wb1
    %wp00h = lshr u64 %wp00, %c32
    %wp01l = and u64 %wp01, %cdig
    %wp10l = and u64 %wp10, %cdig
    %wmida = add u64 %wp00h, %wp01l
    %wmid = add u64 %wmida, %wp10l
    %wp01h = lshr u64 %wp01, %c32
    %wp10h = lshr u64 %wp10, %c32
    %wmidh = lshr u64 %wmid, %c32
    %whia = add u64 %wp11, %wp01h
    %whib = add u64 %whia, %wp10h
    %wmulhi = add u64 %whib, %wmidh
    %wplo = mul u64 %xq, %vlo
    %wqvhi = mul u64 %xq, %vhi
    %wphi = add u64 %wmulhi, %wqvhi
    %wrlo = sub u64 %ulo, %wplo
    %wlb = icmp ult u64 %ulo, %wplo
    %wlbw = zext bool %wlb to u64
    %wrhia = sub u64 %uhi, %wphi
    %wrhi = sub u64 %wrhia, %wlbw
    %wgth = icmp ugt u64 %wrhi, %vhi
    %weqh = icmp eq u64 %wrhi, %vhi
    %wgel = icmp uge u64 %wrlo, %vlo
    %weqge = and bool %weqh, %wgel
    %wge = or bool %wgth, %weqge
    %wbit = zext bool %wge to u64
    %wqf = add u64 %xq, %wbit
    %wmlo = select u64 %wge, %vlo, %c0
    %wmhi = select u64 %wge, %vhi, %c0
    %wfb = icmp ult u64 %wrlo, %wmlo
    %wfbw = zext bool %wfb to u64
    %wflo = sub u64 %wrlo, %wmlo
    %wfhia = sub u64 %wrhi, %wmhi
    %wfhi = sub u64 %wfhia, %wfbw
    br bbdone(%wqf, %c0, %wflo, %wfhi)
bbdone(%oqlo: u64, %oqhi: u64, %orlo: u64, %orhi: u64):
    %rslo = select u64 %wantrem, %orlo, %oqlo
    %rshi = select u64 %wantrem, %orhi, %oqhi
    %qneg = xor bool %na, %nb
    %neg = select bool %wantrem, %na, %qneg
    %ngl = sub u64 %c0, %rslo
    %rslonz = icmp ne u64 %rslo, %c0
    %rsbor = zext bool %rslonz to u64
    %ngh0 = sub u64 %c0, %rshi
    %ngh = sub u64 %ngh0, %rsbor
    %fl = select u64 %neg, %ngl, %rslo
    %fh = select u64 %neg, %ngh, %rshi
    store u64 %fl, ptr %out
    %ione = const usize 1
    %hiptr = gep u64, ptr %out, %ione
    store u64 %fh, ptr %hiptr
    ret
}
"#;

/// The symbol an OBJECT compiled at the lane's default level (O2) gives the
/// 128-bit division helper: `__tcg_divmod128_` plus the first 16 hex digits
/// of the SHA-256 of [`DIVMOD128_ESTIMATE_TEMPLATE`]
/// ([`divmod128_helper_name_at`] names the helper of any level; at O0 it is
/// [`DIVMOD128_TEMPLATE`]'s).
///
/// The definition is weak and hidden (link-once): every trust-cg object that
/// divides 128-bit integers carries a copy, `wasm-ld` binds every reference
/// to one of them, and no copy is exported. The name is in the
/// implementation-reserved `__` namespace, and the digest makes two objects
/// share the symbol only when they carry the same helper text, so copies the
/// linker interchanges compute the same function. An object whose module
/// itself names ANY symbol under [`DIVMOD128_SYMBOL_PREFIX`] is refused
/// (`[TCG-WASM-SYMBOL]`), whether or not that module divides: a frontend may
/// split one crate over several objects (the bridge's per-function
/// fallback), so the object that defines such a name need not be the one
/// that divides.
pub fn divmod128_helper_name() -> String {
    divmod128_helper_name_at(OptLevel::O2)
}

/// The helper's template at `level`: the baseline at O0 (an O0 object's
/// code is unchanged by the estimate), the estimate at O1 and above. Two
/// objects of different levels carry their helpers under different names,
/// and each binds its own calls to its own.
fn divmod128_template(level: OptLevel) -> &'static str {
    if level == OptLevel::O0 {
        DIVMOD128_TEMPLATE
    } else {
        DIVMOD128_ESTIMATE_TEMPLATE
    }
}

/// [`divmod128_helper_name`] of the helper an object compiled at `level`
/// carries.
pub(crate) fn divmod128_helper_name_at(level: OptLevel) -> String {
    let digest = crate::jit_diagnostics::sha256_hex(divmod128_template(level).as_bytes());
    format!("{DIVMOD128_SYMBOL_PREFIX}{}", &digest[..16])
}

/// The prefix of every symbol name the object lane reserves for its 128-bit
/// division helper ([`divmod128_helper_name`]).
pub const DIVMOD128_SYMBOL_PREFIX: &str = "__tcg_divmod128_";

/// `mode` of a 128-bit division call: bit 0 remainder, bit 1 signed.
pub(crate) fn divmod128_mode(signed: bool, remainder: bool) -> i32 {
    i32::from(remainder) | (i32::from(signed) << 1)
}

fn divmod128_text(name: &str, level: OptLevel) -> String {
    let body = divmod128_template(level).replace("{NAME}", name);
    format!(
        "; TrustIr text format v1\nmodule \"tcg_helpers\"\ntarget \"wasm32-unknown-unknown\" 4 \
         little\n\nfuncty.0 = (u64, u64, u64, u64, ptr, u32) -> ()\n{}",
        number_names(&body)
    )
}

/// The one-function trust-ir module of the 128-bit division helper of
/// `level`, named `name` ([`divmod128_helper_name_at`] in an object).
pub(crate) fn divmod128_module(name: &str, level: OptLevel) -> Result<Module, WasmLowerError> {
    trust_ir::parser::parse_module(&divmod128_text(name, level)).map_err(|e| {
        WasmLowerError::UnsupportedInst(format!(
            "internal 128-bit division helper failed to parse: {e}"
        ))
    })
}

/// Rename the template's `%name` values and `bbname` blocks to the text
/// format's numeric spellings (`%N`, `bbN`), in order of first appearance.
fn number_names(text: &str) -> String {
    use std::collections::HashMap;
    let mut values: HashMap<String, usize> = HashMap::new();
    let mut blocks: HashMap<String, usize> = HashMap::new();
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    let ident_end = |mut j: usize| {
        while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
            j += 1;
        }
        j
    };
    while i < bytes.len() {
        let at_word_start =
            i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_');
        if bytes[i] == b'%' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_alphabetic() {
            let end = ident_end(i + 1);
            let name = &text[i + 1..end];
            let n = values.len();
            let id = *values.entry(name.to_string()).or_insert(n);
            out.push_str(&format!("%{id}"));
            i = end;
        } else if at_word_start
            && text[i..].starts_with("bb")
            && i + 2 < bytes.len()
            && bytes[i + 2].is_ascii_alphabetic()
        {
            let end = ident_end(i + 2);
            let name = &text[i + 2..end];
            let n = blocks.len();
            let id = *blocks.entry(name.to_string()).or_insert(n);
            out.push_str(&format!("bb{id}"));
            i = end;
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }
    out
}

fn fmod_text(single: bool) -> String {
    let (name, f, t, s) = if single {
        (FMODF_HELPER, "f32", "u32", "i32")
    } else {
        (FMOD_HELPER, "f64", "u64", "i64")
    };
    // (significand-normalize shift, significand bits, sign bit, exponent mask,
    // significand mask, hidden bit, clz of a normalized significand)
    let (norm, mshift, sshift, expmask, mantmask, hidden, clzadj): (
        u32,
        u32,
        u32,
        u64,
        u64,
        u64,
        u32,
    ) = if single {
        (9, 23, 31, 0xff, (1 << 23) - 1, 1 << 23, 8)
    } else {
        (12, 52, 63, 0x7ff, (1 << 52) - 1, 1 << 52, 11)
    };
    let body = FMOD_TEMPLATE
        .replace("{NAME}", name)
        .replace("{F}", f)
        .replace("{T}", t)
        .replace("{S}", s)
        .replace("{NORM}", &norm.to_string())
        .replace("{MSHIFT}", &mshift.to_string())
        .replace("{SSHIFT}", &sshift.to_string())
        .replace("{EXPMASK}", &expmask.to_string())
        .replace("{MANTMASK}", &mantmask.to_string())
        .replace("{HIDDEN}", &hidden.to_string())
        .replace("{CLZADJ}", &clzadj.to_string());
    format!(
        "; TrustIr text format v1\nmodule \"tcg_helpers\"\ntarget \"wasm32-unknown-unknown\" 4 \
         little\n\nfuncty.0 = ({f}, {f}) -> ({f})\n{}",
        number_names(&body)
    )
}

/// The one-function trust-ir module of the `f64` (`single == false`) or `f32`
/// remainder helper.
pub(crate) fn fmod_module(single: bool) -> Result<Module, WasmLowerError> {
    trust_ir::parser::parse_module(&fmod_text(single)).map_err(|e| {
        WasmLowerError::UnsupportedInst(format!("internal fmod helper failed to parse: {e}"))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Ty};

    fn float(ty: Ty, bits: u64) -> InterpretValue {
        InterpretValue {
            ty,
            kind: InterpretValueKind::FloatBits(bits),
        }
    }

    fn run(module: &Module, args: Vec<InterpretValue>) -> u64 {
        // `fmod(1e300, 5e-324)` walks ~2100 exponent steps.
        let interp = Interpreter::with_module(module).with_options(InterpretOptions {
            fuel: 10_000_000,
            max_call_depth: 16,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        });
        let f = module.functions[0].id;
        let out = interp.execute_func(f, args).expect("helper executes");
        match out.returns[0].kind {
            InterpretValueKind::FloatBits(bits) => bits,
            ref other => panic!("helper returned {other:?}"),
        }
    }

    /// The helper is exact on the reference interpreter over a spread of
    /// operands, including subnormals, signed zeros, infinities and NaN.
    #[test]
    fn fmod_helper_matches_rust_remainder() {
        let module = fmod_module(false).unwrap();
        let samples = [
            0.0,
            -0.0,
            1.0,
            -1.0,
            0.5,
            2.5,
            7.25,
            -7.25,
            1e300,
            -1e-300,
            5e-324,
            1e-310,
            3.0e10,
            f64::MAX,
            f64::MIN_POSITIVE,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
            std::f64::consts::PI,
            1.0 / 3.0,
        ];
        for &x in &samples {
            for &y in &samples {
                let got = f64::from_bits(run(
                    &module,
                    vec![float(Ty::F64, x.to_bits()), float(Ty::F64, y.to_bits())],
                ));
                let want = x % y;
                assert!(
                    got.to_bits() == want.to_bits() || (got.is_nan() && want.is_nan()),
                    "fmod({x:e}, {y:e}) = {got:e}, want {want:e}"
                );
            }
        }
    }

    /// The 128-bit division result the lane has always produced: Rust's
    /// operators where trust-ir defines the operation; on a zero divisor the
    /// restoring algorithm's all-ones quotient / dividend remainder (signed:
    /// of the magnitudes, then negated), and `MIN / -1 == MIN`, remainder 0.
    pub(crate) fn divmod128_reference(n: u128, d: u128, signed: bool, rem: bool) -> u128 {
        if !signed {
            return match (d, rem) {
                (0, false) => u128::MAX,
                (0, true) => n,
                (_, false) => n / d,
                (_, true) => n % d,
            };
        }
        let (a, b) = (n as i128, d as i128);
        match (b, rem) {
            (0, false) => {
                if a < 0 {
                    1
                } else {
                    u128::MAX
                }
            }
            (0, true) => n,
            _ if a == i128::MIN && b == -1 => {
                if rem {
                    0
                } else {
                    n
                }
            }
            (_, false) => (a / b) as u128,
            (_, true) => (a % b) as u128,
        }
    }

    /// The helper of `template` plus a driver that hands it a 16-byte slot
    /// and returns the halves it stored.
    fn divmod128_driver(template: &str) -> Module {
        let helper = number_names(&template.replace("{NAME}", "helper"));
        let driver = number_names(
            "\nfn @drive(functy.1) {\nbbentry(%a: u64, %b: u64, %c: u64, %d: u64, %m: u32):\n    \
             %slot = alloca u128\n    call @func.0(%a, %b, %c, %d, %slot, %m)\n    \
             %lo = load u64, ptr %slot\n    %one = const usize 1\n    \
             %hp = gep u64, ptr %slot, %one\n    %hi = load u64, ptr %hp\n    ret %lo, %hi\n}\n",
        );
        let text = format!(
            "; TrustIr text format v1\nmodule \"t\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
             functy.0 = (u64, u64, u64, u64, ptr, u32) -> ()\n\
             functy.1 = (u64, u64, u64, u64, u32) -> (u64, u64)\n{helper}{driver}"
        );
        trust_ir::parser::parse_module(&text).expect("driver parses")
    }

    fn u64v(v: u64) -> InterpretValue {
        InterpretValue::int(Ty::U64, i128::from(v)).unwrap()
    }

    fn run_divmod(module: &Module, n: u128, d: u128, mode: i32) -> u128 {
        let interp = Interpreter::with_module(module).with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 8,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        });
        let f = module.function_by_name("drive").unwrap().id;
        let args = vec![
            u64v(n as u64),
            u64v((n >> 64) as u64),
            u64v(d as u64),
            u64v((d >> 64) as u64),
            InterpretValue::int(Ty::U32, i128::from(mode)).unwrap(),
        ];
        let out = interp
            .execute_func(f, args)
            .unwrap_or_else(|e| panic!("helper({n:#x}, {d:#x}, mode {mode}) is UB-free: {e}"));
        let half = |i: usize| match &out.returns[i].kind {
            InterpretValueKind::Int(v) => v.as_signed() as u64,
            other => panic!("half {i}: {other:?}"),
        };
        u128::from(half(0)) | (u128::from(half(1)) << 64)
    }

    /// Both templates: the O0 baseline and the O1-and-above estimate.
    const TEMPLATES: [&str; 2] = [DIVMOD128_TEMPLATE, DIVMOD128_ESTIMATE_TEMPLATE];

    /// On the reference interpreter each helper is free of undefined
    /// behaviour and computes [`divmod128_reference`] in all four modes over
    /// the edge classes: zero, one, all-ones, `MIN`, powers of two and their
    /// neighbours at the 2^32 / 2^64 / 2^96 boundaries, divisors larger than
    /// the dividend, and normalized divisors that exercise both quotient-digit
    /// corrections.
    #[test]
    fn divmod128_helper_matches_the_reference_on_edge_classes() {
        for template in TEMPLATES {
            edge_classes(&divmod128_driver(template));
        }
    }

    fn edge_classes(module: &Module) {
        let module = module.clone();
        let mut edges: Vec<u128> = vec![0, 1, 2, 3, 7, 10, u128::MAX, u128::MAX - 1];
        for k in [31u32, 32, 33, 63, 64, 65, 95, 96, 127] {
            let p = 1u128 << k;
            edges.extend([p - 1, p, p + 1, p.wrapping_neg()]);
        }
        edges.extend([
            0xffff_ffff_0000_0001,
            0x8000_0000_0000_0001,
            0x8000_0000_ffff_ffff_ffff_ffff_ffff_ffff,
            0x1234_5678_9abc_def0_0fed_cba9_8765_4321,
        ]);
        let mut checks = 0;
        for &n in &edges {
            for &d in &edges {
                for mode in 0..4 {
                    let want = divmod128_reference(n, d, mode & 2 != 0, mode & 1 != 0);
                    let got = run_divmod(&module, n, d, mode);
                    assert_eq!(got, want, "mode {mode}: {n:#x} by {d:#x}");
                    checks += 1;
                }
            }
        }
        assert!(checks > 5_000, "{checks}");
    }

    /// Random operands of independently random bit lengths (so every path —
    /// one word, the 64-bit divisor with both quotient-digit corrections, and
    /// the short shift-subtract — is taken many times), in all four modes.
    #[test]
    fn divmod128_helper_matches_the_reference_on_random_operands() {
        for template in TEMPLATES {
            random_operands(&divmod128_driver(template));
        }
    }

    fn random_operands(module: &Module) {
        let module = module.clone();
        let mut s: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = || {
            s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            s ^ (s >> 29)
        };
        for _ in 0..8_000 {
            let mut operand = || {
                let bits = next() % 129;
                let v = (u128::from(next()) << 64) | u128::from(next());
                let v = if bits == 128 {
                    v
                } else {
                    v & ((1u128 << bits) - 1)
                };
                // Half negated, so signed division sees every sign pair.
                if next() & 1 == 1 { v.wrapping_neg() } else { v }
            };
            let (n, d) = (operand(), operand());
            let mode = (next() % 4) as i32;
            let want = divmod128_reference(n, d, mode & 2 != 0, mode & 1 != 0);
            assert_eq!(
                run_divmod(&module, n, d, mode),
                want,
                "mode {mode}: {n:#x} by {d:#x}"
            );
        }
    }

    /// Divisors of more than 64 bits at every normalization shift, against
    /// dividends at and above them (the wide path's estimate, its decrement
    /// and its correction), including the quotient's extremes: `n = d`,
    /// `n = 2d - 1`, all-ones over the smallest wide divisor (the largest
    /// quotient, `2^64 - 1`) and dividends whose estimate needs the
    /// correction (`d` with every low bit set). All four modes.
    #[test]
    fn divmod128_helper_matches_the_reference_on_wide_divisors() {
        for template in TEMPLATES {
            wide_divisors(&divmod128_driver(template));
        }
    }

    fn wide_divisors(module: &Module) {
        let module = module.clone();
        let mut s: u64 = 0xD1B5_4A32_D192_ED03;
        let mut next = || {
            s = s
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            s ^ (s >> 29)
        };
        let mut checks = 0;
        for shift in 0..64u32 {
            let top = 1u128 << (127 - shift);
            let wide = [
                top,
                top | (top - 1),
                top | u128::from(u64::MAX),
                top | (u128::from(next()) << 64 >> shift.max(1)) | u128::from(next()),
            ];
            for &d in &wide {
                let mut dividends = vec![d, d.wrapping_mul(2).wrapping_sub(1), u128::MAX];
                for _ in 0..6 {
                    let n = (u128::from(next()) << 64) | u128::from(next());
                    dividends.push(n);
                    dividends.push(n | d);
                }
                for &n in &dividends {
                    for mode in 0..4 {
                        let want = divmod128_reference(n, d, mode & 2 != 0, mode & 1 != 0);
                        assert_eq!(
                            run_divmod(&module, n, d, mode),
                            want,
                            "mode {mode}: {n:#x} by {d:#x}"
                        );
                        checks += 1;
                    }
                }
            }
        }
        assert!(checks > 15_000, "{checks}");
        assert_eq!(
            divmod128_reference(u128::MAX, 1u128 << 64, false, false),
            u128::from(u64::MAX)
        );
        assert_eq!(
            run_divmod(&module, u128::MAX, 1u128 << 64, 0),
            u128::from(u64::MAX)
        );
    }

    #[test]
    fn fmodf_helper_matches_rust_remainder() {
        let module = fmod_module(true).unwrap();
        let samples = [
            0.0f32,
            -0.0,
            1.0,
            -1.0,
            0.5,
            2.5,
            7.25,
            -7.25,
            1e30,
            -1e-30,
            1e-45,
            1e-40,
            3.0e7,
            f32::MAX,
            f32::MIN_POSITIVE,
            f32::INFINITY,
            f32::NAN,
            1.0 / 3.0,
        ];
        for &x in &samples {
            for &y in &samples {
                let got = f32::from_bits(run(
                    &module,
                    vec![
                        float(Ty::F32, u64::from(x.to_bits())),
                        float(Ty::F32, u64::from(y.to_bits())),
                    ],
                ) as u32);
                let want = x % y;
                assert!(
                    got.to_bits() == want.to_bits() || (got.is_nan() && want.is_nan()),
                    "fmodf({x:e}, {y:e}) = {got:e}, want {want:e}"
                );
            }
        }
    }
}
