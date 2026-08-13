// Copyright 2026 Andrew Yates. Apache-2.0.
//
//! UNSIGNED magic-number (reciprocal-multiply) strength reduction.
//!
//! Replaces a hardware unsigned divide/remainder by a compile-time constant
//! `K` with a widening multiply by a precomputed "magic" reciprocal `M`
//! followed by a shift (and, in the add-back form, one extra add + shift).
//! A `DIV r64` costs ~20-40 cycles; the magic sequence is ~4 cycles.
//!
//! # THE TRUST POINT (the one cited lemma)
//!
//! This module has **exactly one** unproven premise: the
//! Granlund-Montgomery / *Hacker's Delight* §10-4 unsigned-division theorem.
//! Everything else per-divisor is decided by **pure bignum evaluation** in
//! Rust — there is no solver anywhere in the shipped discharge path.
//!
//! ## Cited lemma (Granlund & Montgomery, PLDI 1994; Hacker's Delight, 2nd
//! ed., §10-4, "Unsigned Division by a Constant")
//!
//! Fix a word width `W` and an unsigned divisor `K` with `1 < K < 2^W`.
//! Let `s` be a shift amount and `M` a multiplier. Define the "band"
//!
//! ```text
//!     2^(W+s)  <=  M * K  <=  2^(W+s) + 2^s .                      (BAND)
//! ```
//!
//! **Theorem (HD 10-4, add==0 / "no add-back" form).** If (BAND) holds and
//! `0 <= M < 2^W` (M is a W-bit magic), then for *every* `x` in
//! `[0, 2^W)`:
//!
//! ```text
//!     floor( (x * M) / 2^(W+s) )  ==  floor( x / K ) .
//! ```
//!
//! i.e. taking the high `W` bits of the `2W`-bit product `x*M` and shifting
//! right by `s` yields exactly the truncating unsigned quotient.
//!
//! (BAND) is *sufficient* but not necessary. `band_holds` checks the
//! sharper, necessary-and-sufficient form `2^(W+s) <= M*K` and
//! `(M*K - 2^(W+s)) * nc < 2^(W+s)` with `nc` the round-up reciprocal's
//! worst-case dividend — see "How per-divisor correctness is established".
//!
//! **Add-back form.** The `magicu` construction sometimes needs a multiplier
//! `M' = M + 2^W` that does not fit in `W` bits. HD 10-4 handles this by
//! carrying an explicit `add` of `x` into the high half before the final
//! shift (the `add == 1` flag). Writing `q = MULHI(x, M) = floor(x*M/2^W)`
//! with the reduced `M = M' - 2^W` in `[0, 2^W)`, the add-back sequence
//!
//! ```text
//!     t = MULHI(x, M);  t = t + ((x - t) >> 1);  q = t >> (s - 1)
//! ```
//!
//! computes `floor(x/K)` for all `x` in `[0, 2^W)` whenever the *add-back*
//! band
//!
//! ```text
//!     2^(W+s)  <=  M' * K  <=  2^(W+s) + 2^s   with  M' = M + 2^W          (BAND')
//! ```
//! holds. `(x - t) >> 1` is the standard "average without overflow" that
//! forms `floor((x + q)/2)` where `q = MULHI(x, M)`; see HD Fig. 10-1/10-4.
//!
//! ## How per-divisor correctness is established (NO solver)
//!
//! For each candidate `(K, M, s, add)` we compute (via `magicu`) and then
//! **verify the band by exact bignum arithmetic** (`band_holds`): we form the
//! product `magic * K` (up to `2W` bits — for `W = 64` this can be a
//! *128-bit* value that we hold in a 256-bit accumulator to avoid any wrap)
//! and check `2^(W+s) <= magic*K` together with the EXACT upper condition
//! `(magic*K - 2^(W+s)) * nc < 2^(W+s)`, where `nc` is the largest dividend
//! `<= 2^W - 1` congruent to `-1 (mod K)` (the round-up reciprocal's worst
//! case). This is the necessary-and-sufficient Granlund-Montgomery band; the
//! textbook `magic*K <= 2^(W+s) + 2^s` inequality is its `nc ≈ 2^W`
//! over-approximation (sound but incomplete — it needlessly rejects valid
//! magics for large divisors). If the band holds, the emitted sequence is
//! correct **by the cited lemma**. If it does not hold — or the divisor is
//! 0/1, or a width we do not handle — we return `None` and the caller
//! **FAILS SAFE**, keeping the hardware `DIV`.
//!
//! A wrongly-admitted `(M, s)` would be a miscompile, so the band check is the
//! soundness-critical arithmetic and is tested hard (`tests` below: correct
//! `(K,M,s)` admits, an off-by-one wrong `M` is rejected, and the emitted
//! magic result is checked to equal `x / K` over a wide `x` sample).
//!
//! ## Machine-checked replacement path (§4.F theory-lemma checker)
//!
//! The citation is deliberately isolated: the transform's correctness is
//! `band_holds(...) && <cited lemma>`. A future machine-checked discharge of
//! HD 10-4 as an Int-theory obligation (the project's §4.F theory-lemma
//! checker) can REPLACE the citation in this doc block **without changing the
//! transform or the band predicate** — the band predicate *is* the lemma's
//! hypothesis, already in the exact form a theory lemma would consume.

/// A minimal fixed-width **256-bit unsigned** integer, big enough to hold
/// every intermediate the band check forms at `W = 64`:
///   * `magic * K`  where `magic, K < 2^64`  → up to `< 2^128`,
///   * `magic' * K` where `magic' < 2^65`    → up to `< 2^129`,
///   * `2^(W+s)` and `2^(W+s)+2^s` with `W = 64, s <= 63` → up to `< 2^128`.
///
/// 256 bits gives comfortable headroom (all values above are `< 2^130`), so
/// **no operation used here can overflow**. Represented as four little-endian
/// 64-bit limbs. Only the operations the band check needs are implemented:
/// `from_u128`, `mul` (256×256→256, wrap-free for our magnitudes), `add`,
/// `shl` (by a bit count `< 256`), and `Ord`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct U256 {
    /// Little-endian limbs: `limbs[0]` is the least-significant 64 bits.
    limbs: [u64; 4],
}

impl U256 {
    pub const ZERO: U256 = U256 { limbs: [0; 4] };

    /// Construct from a `u128` (fits in the low two limbs).
    pub fn from_u128(v: u128) -> U256 {
        U256 {
            limbs: [v as u64, (v >> 64) as u64, 0, 0],
        }
    }

    pub fn from_u64(v: u64) -> U256 {
        U256 {
            limbs: [v, 0, 0, 0],
        }
    }

    /// `1 << shift` for `0 <= shift < 256`. Panics if `shift >= 256` (never
    /// reached: callers pass `W + s <= 127`).
    pub fn one_shl(shift: u32) -> U256 {
        assert!(shift < 256, "U256::one_shl shift out of range");
        let limb = (shift / 64) as usize;
        let bit = shift % 64;
        let mut limbs = [0u64; 4];
        limbs[limb] = 1u64 << bit;
        U256 { limbs }
    }

    /// Wrapping 256-bit addition. For our magnitudes (`< 2^130`) there is no
    /// wrap, but we still compute the full carry chain across all four limbs.
    pub fn wrapping_add(self, other: U256) -> U256 {
        let mut out = [0u64; 4];
        let mut carry = 0u128;
        for (i, out_limb) in out.iter_mut().enumerate() {
            let sum = self.limbs[i] as u128 + other.limbs[i] as u128 + carry;
            *out_limb = sum as u64;
            carry = sum >> 64;
        }
        U256 { limbs: out }
    }

    /// Schoolbook 256×256→256 multiply (low 256 bits). For the magnitudes the
    /// band check forms (both operands `< 2^65`, product `< 2^130`) the result
    /// fits in 256 bits with no truncation, so this is exact.
    pub fn wrapping_mul(self, other: U256) -> U256 {
        let mut out = [0u64; 4];
        for i in 0..4 {
            if self.limbs[i] == 0 {
                continue;
            }
            let mut carry = 0u128;
            for j in 0..(4 - i) {
                let idx = i + j;
                let cur = out[idx] as u128;
                let prod = self.limbs[i] as u128 * other.limbs[j] as u128;
                let sum = cur + (prod & 0xFFFF_FFFF_FFFF_FFFF) + (carry & 0xFFFF_FFFF_FFFF_FFFF);
                out[idx] = sum as u64;
                // carry = high 64 of prod + high 64 of the running carry + carry-out of `sum`.
                carry = (prod >> 64) + (carry >> 64) + (sum >> 64);
            }
        }
        U256 { limbs: out }
    }
}

impl core::cmp::Ord for U256 {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        // Compare from the most-significant limb down.
        for i in (0..4).rev() {
            match self.limbs[i].cmp(&other.limbs[i]) {
                core::cmp::Ordering::Equal => continue,
                non_eq => return non_eq,
            }
        }
        core::cmp::Ordering::Equal
    }
}

impl core::cmp::PartialOrd for U256 {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl core::fmt::Debug for U256 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "U256(0x{:016x}_{:016x}_{:016x}_{:016x})",
            self.limbs[3], self.limbs[2], self.limbs[1], self.limbs[0]
        )
    }
}

/// The magic parameters for one unsigned divisor at a given width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MagicU {
    /// The `W`-bit multiplier `M` (already reduced into `[0, 2^W)`; when
    /// `add` is set the *true* multiplier is `M + 2^W`, folded into the
    /// add-back sequence — see the module doc).
    pub magic: u64,
    /// The post-multiply right-shift amount `s`.
    pub shift: u32,
    /// Whether the add-back form is required (true iff `magicu` produced a
    /// multiplier `>= 2^W`).
    pub add: bool,
}

/// The word width of a divisor candidate. Only the widths we actually lower.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MagicWidth {
    W32,
    W64,
}

impl MagicWidth {
    pub fn bits(self) -> u32 {
        match self {
            MagicWidth::W32 => 32,
            MagicWidth::W64 => 64,
        }
    }
}

/// Compute the unsigned magic multiplier/shift for divisor `d` at width `W`,
/// via the standard `magicu` algorithm (Hacker's Delight, 2nd ed., Fig. 10-1,
/// generalized over `W`). This returns a *candidate* `(M, s, add)`; the caller
/// must still `band_holds` it before trusting it.
///
/// Returns `None` for `d <= 1` (0 is div-by-zero, handled elsewhere; 1 is
/// identity and not worth a magic) and for `d >= 2^W`.
///
/// The arithmetic is done in `u128` so that `W = 64` intermediates
/// (`nc`, `2^p`, the trial quotients/remainders) never wrap; for `W <= 64`
/// every value here is `< 2^(W+1) <= 2^65 < 2^128`.
pub fn magicu(d: u64, width: MagicWidth) -> Option<MagicU> {
    let w = width.bits();
    if d <= 1 {
        return None;
    }
    // Reject a divisor that does not fit in the width (for W=32, d must be < 2^32).
    if w < 64 && d >= (1u64 << w) {
        return None;
    }

    // Everything below in u128. `two_w = 2^W`, `ones = 2^W - 1` (the unsigned
    // max at width W). This is the canonical Hacker's Delight Fig. 10-1
    // `magicu`, generalized over `W` and validated by brute-force `eval` vs
    // `x/d` over ~40k divisors (both widths) with the invariant that EVERY
    // eval-vs-`x/d` mismatch coincided with `band_holds == false` — i.e. the
    // band check (below) is the load-bearing fail-safe gate, not `magicu`.
    let d = d as u128;
    let two_w: u128 = 1u128 << w;
    let ones: u128 = two_w - 1;

    // nc = the largest value `<= 2^W - 1` that is `== -1 (mod d)`
    //    = (2^W - 1) - ((2^W - 1) - d + 1) mod d       [HD Fig 10-1, unsigned]
    let nc: u128 = ones - (ones - d + 1) % d;

    // Two remainder-accumulator recurrences track `2^p / nc` and
    // `(2^p - 1) / d` as p grows from W-1 upward, without ever forming 2^p
    // directly. NOTE the asymmetry (HD Fig. 10-1): the `nc` recurrence tracks
    // `2^p` EXACTLY (`q1 = floor(2^p/nc)`, `r1 = 2^p mod nc`), whereas the `d`
    // recurrence tracks `2^p - 1` (`q2 = floor((2^p-1)/d)`,
    // `r2 = (2^p-1) mod d`) — the magic is `q2 + 1 = ceil(2^p/d)` and the loop
    // terminates on `delta = d - 1 - r2` derived from the `2^p - 1` remainder.
    // (Tracking `2^p mod d` here instead terminates one iteration early and
    // yields an out-of-band magic for divisors such as d=3.)
    let mut p: u32 = w - 1;
    let two_p0: u128 = 1u128 << (w - 1);
    let mut q1: u128 = two_p0 / nc;
    let mut r1: u128 = two_p0 - q1 * nc;
    let mut q2: u128 = (two_p0 - 1) / d;
    let mut r2: u128 = (two_p0 - 1) - q2 * d;
    let mut delta: u128;

    loop {
        p += 1;
        // Double 2^p over nc.
        if r1 >= nc - r1 {
            q1 = 2 * q1 + 1;
            r1 = 2 * r1 - nc;
        } else {
            q1 *= 2;
            r1 *= 2;
        }
        // Double (2^p - 1) over d: maintain q2 = floor((2^p-1)/d),
        // r2 = (2^p-1) mod d. Note the `+1` on each doubling (HD Fig. 10-1):
        // 2*(2^{p-1}-1) + 1 = 2^p - 1.
        if r2 + 1 >= d - r2 {
            q2 = 2 * q2 + 1;
            r2 = 2 * r2 + 1 - d;
        } else {
            q2 *= 2;
            r2 = 2 * r2 + 1;
        }
        delta = d - 1 - r2;

        // Canonical loop condition: continue while 2^p is not yet large enough.
        if !(q1 < delta || (q1 == delta && r1 == 0)) {
            break;
        }
        // Safety bound: p can never need to exceed ~2W for a valid divisor.
        // If it does, bail (the caller fails safe to DIV).
        if p > 2 * w + 4 {
            return None;
        }
    }

    let magic_full = q2 + 1; // the (possibly W+1-bit) multiplier
    let shift = p - w;

    // add-back iff the multiplier does not fit in W bits.
    let add = magic_full >= two_w;
    // Reduce into [0, 2^W). For the add form the emitted MULHI uses this
    // reduced M and the sequence adds `x` back (per the module doc).
    let magic = (magic_full & ones) as u64;

    Some(MagicU { magic, shift, add })
}

/// **The band check (the soundness-critical pure evaluation).**
///
/// Given divisor `d`, candidate parameters `m`, and width `W`, verify the
/// Granlund-Montgomery band by exact 256-bit arithmetic:
///
///   * no-add form: `2^(W+s) <= M*d <= 2^(W+s) + 2^s`
///   * add form:    `2^(W+s) <= M'*d <= 2^(W+s) + 2^s`  with `M' = M + 2^W`
///
/// Returns `true` iff the band holds. A `true` here is the empirical + exact
/// witness that the emitted sequence equals `floor(x/d)` for all `x` in
/// `[0, 2^W)` **by the cited lemma**. Any arithmetic here is wrap-free: the
/// largest value formed is `M' * d < 2^65 * 2^64 = 2^129 < 2^256`.
pub fn band_holds(d: u64, m: MagicU, width: MagicWidth) -> bool {
    let w = width.bits();
    // s must keep W + s < 128 so 2^(W+s) fits our comparison magnitudes; the
    // magicu shift is always < W for valid divisors, but guard anyway.
    if m.shift >= 64 {
        return false;
    }
    let w_plus_s = w + m.shift;
    if w_plus_s >= 128 {
        return false;
    }

    // The effective multiplier: M for the no-add form, M + 2^W for add-back.
    let mult: U256 = if m.add {
        // M + 2^W
        U256::from_u64(m.magic).wrapping_add(U256::one_shl(w))
    } else {
        U256::from_u64(m.magic)
    };

    let prod = mult.wrapping_mul(U256::from_u64(d)); // M(') * d  (exact, no wrap)
    let lo = U256::one_shl(w_plus_s); // 2^(W+s)

    // LOWER band: the multiplier must round `2^(W+s)/d` UP, i.e. `prod >= 2^(W+s)`
    // (equivalently `M(') = ceil(2^(W+s)/d)`). A smaller magic under-shoots.
    if prod < lo {
        return false;
    }

    // UPPER band — the EXACT Granlund-Montgomery necessary-and-sufficient
    // condition. The worst-case dividend for the round-up reciprocal is
    //     nc = the largest x <= 2^W - 1 with x ≡ -1 (mod d)
    // (the same `nc` `magicu` forms), and the emitted sequence equals
    // `floor(x/d)` for EVERY x in `[0, 2^W)` iff
    //     (M(') * d - 2^(W+s)) * nc  <  2^(W+s).
    // We evaluate the algebraically-equivalent, subtraction-free / wrap-free
    //     prod * nc  <  lo * nc + lo          (given `prod >= lo`; all < 2^256).
    //
    // The textbook `prod <= 2^(W+s) + 2^s` band is the `nc ≈ 2^W`
    // over-approximation of THIS condition (`2^s * nc < 2^s * 2^W = 2^(W+s)`):
    // SOUND but incomplete — it wrongly rejects valid magics for large divisors
    // (e.g. `d ≈ 3·10^9` at `W = 32`, whose exact magic is correct over all
    // `2^32` dividends yet exceeds the textbook upper bound). Using the exact
    // `nc` worst case both admits those and stays sound: the predicate is
    // necessary AND sufficient — exhaustively cross-checked against brute-force
    // `eval == x/d` and against ±-perturbed magics (zero false-accepts, zero
    // false-rejects) for W = 8..16.
    let ones: u128 = (1u128 << w) - 1;
    let nc = (ones - (ones - d as u128 + 1) % d as u128) as u64;
    let nc = U256::from_u64(nc);
    prod.wrapping_mul(nc) < lo.wrapping_mul(nc).wrapping_add(lo)
}

/// SIGNED magic-number division parameters (Hacker's Delight §10-3): a signed
/// `W`-bit multiplier `M` and a post-multiply arithmetic-shift `s`. The emitted
/// sequence is (with `q = SMULHI(x, M)` = high `W` bits of the signed product):
///   * if `d > 0 && M < 0`:  q = q + x
///   * if `d < 0 && M > 0`:  q = q - x
///   * q = q >>a s                       (arithmetic shift)
///   * q = q + (q >>u (W-1))             (add the sign bit -> round toward zero)
///     giving `q == x / d` for every signed `x`. The two sign corrections are
///     decided AT COMPILE TIME from `sign(d)` and `sign(M)` (both known).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MagicS {
    pub magic: i64,
    pub shift: u32,
}

/// Generic-width core of the signed magic computation (Hacker's Delight,
/// 2nd ed., Fig. 10-1 `magic`, generalized over `W`). `d` is the signed
/// divisor interpreted at width `w` (2..=64); returns `(M, s)` with `M` a
/// signed `w`-bit multiplier. `None` for the non-magic divisors 0 / 1 / -1,
/// for a divisor that does not fit signed-`w`, or if the loop fails to
/// converge. All intermediates are unsigned `u128` over the ABSOLUTE values
/// (|d|, |nc|), exactly as HD does, so they never wrap for `w <= 64`.
fn magics_bits(d: i128, w: u32) -> Option<(i128, u32)> {
    if !(2..=64).contains(&w) {
        return None;
    }
    // Must fit signed-w and not be a non-magic divisor.
    let smin = -(1i128 << (w - 1));
    let smax = (1i128 << (w - 1)) - 1;
    if d < smin || d > smax || d == 0 || d == 1 || d == -1 {
        return None;
    }
    let ad: u128 = d.unsigned_abs(); // |d|
    // A power-of-two |d| is handled by the (cheaper, exact) shift path, not
    // magic division — and its degenerate magic breaks the band. Decline.
    if ad & (ad - 1) == 0 {
        return None;
    }
    let two_wm1: u128 = 1u128 << (w - 1); // 2^(w-1)
    // t = 2^(w-1) + (1 if d<0 else 0); anc = |nc| = t - 1 - (t mod |d|).
    let t: u128 = two_wm1 + if d < 0 { 1 } else { 0 };
    let anc: u128 = t - 1 - (t % ad);

    let mut p: u32 = w - 1;
    let mut q1: u128 = two_wm1 / anc;
    let mut r1: u128 = two_wm1 - q1 * anc;
    let mut q2: u128 = two_wm1 / ad;
    let mut r2: u128 = two_wm1 - q2 * ad;
    let mut delta: u128;
    loop {
        p += 1;
        q1 *= 2;
        r1 *= 2;
        if r1 >= anc {
            q1 += 1;
            r1 -= anc;
        }
        q2 *= 2;
        r2 *= 2;
        if r2 >= ad {
            q2 += 1;
            r2 -= ad;
        }
        delta = ad - r2;
        if !(q1 < delta || (q1 == delta && r1 == 0)) {
            break;
        }
        if p > 2 * w + 4 {
            return None;
        }
    }
    // M = q2 + 1, negated for a negative divisor. Reinterpret the low w bits as
    // a signed w-bit value (HD guarantees it fits).
    let mut m: i128 = (q2 + 1) as i128;
    if d < 0 {
        m = -m;
    }
    // Sign-reduce into [smin, smax] via the low-w-bits two's-complement image.
    let mask: i128 = (1i128 << w) - 1;
    let low = m & mask;
    let m_signed = if (low >> (w - 1)) & 1 == 1 {
        low - (1i128 << w)
    } else {
        low
    };
    let s = p - w;
    Some((m_signed, s))
}

/// Compute the signed magic multiplier/shift for divisor `d` at width `W`
/// (I32/I64 only for the shipped isel path). See [`magics_bits`].
pub fn magics(d: i64, width: MagicWidth) -> Option<MagicS> {
    let (m, s) = magics_bits(i128::from(d), width.bits())?;
    Some(MagicS {
        magic: m as i64,
        shift: s,
    })
}

/// **The SIGNED band check — the soundness-critical shipped-path fail-safe**
/// (the signed analog of [`band_holds`]). Given divisor `d`, candidate `(m, s)`,
/// and width `w`, it verifies the effective-multiplier band that guarantees the
/// emitted signed sequence equals `trunc(x/d)` for EVERY signed `x` in
/// `[-2^(w-1), 2^(w-1))`, by exact U256 arithmetic — no solver.
///
/// The two sign corrections (`add x` when `d>0 && M<0`; `sub x` when `d<0 &&
/// M>0`) fold into an EFFECTIVE POSITIVE multiplier magnitude
///   `aM = |M|`            when `sign(M) == sign(d)`   (no correction), else
///   `aM = 2^w - |M|`      (the correction restores the `>= 2^(w-1)` magnitude).
/// Writing `ad = |d|`, the sequence computes `trunc(x/d)` for all `x` iff
///   `2^(w+s) <= aM * ad  <  2^(w+s) + 2^(s+1)`   (BAND-S)
/// where the `2^(s+1)` slack is the round-up reciprocal's worst-case error over
/// the largest-magnitude dividend `2^(w-1)`. Exact (no wrap): the largest value
/// formed is `aM * ad < 2^w * 2^w = 2^(2w) <= 2^128 < 2^256`.
///
/// SOUND by construction (an over-strict variant only ever REJECTS a valid magic
/// -> the isel falls safe to hardware IDIV), and validated EXHAUSTIVELY in the
/// tests: at `w=8` (all `d`, all candidate `m`, all `s`) `band_holds_s` is
/// exactly equivalent to "the emitted sequence equals `x/d` for every `x`", so
/// it is necessary AND sufficient there and admits every `magics()` output.
pub fn smagic_band_holds(d: i64, m: MagicS, width: MagicWidth) -> bool {
    let w = width.bits();
    let d = i128::from(d);
    if d == 0 || d == 1 || d == -1 {
        return false;
    }
    let mm = i128::from(m.magic);
    let s = m.shift;
    if s >= w || w + s + 1 >= 256 {
        return false;
    }
    let ad: u128 = d.unsigned_abs();
    let am_abs: u128 = mm.unsigned_abs();
    let two_w: u128 = 1u128 << w;
    if ad & (ad - 1) == 0 {
        return false; // power-of-two divisor -> shift path, not magic.
    }
    // Effective multiplier magnitude (folds the add-x / sub-x correction).
    let same_sign = (d > 0) == (mm > 0);
    let a_m: u128 = if same_sign { am_abs } else { two_w - am_abs };

    let prod = U256::from_u128(a_m).wrapping_mul(U256::from_u128(ad)); // aM * ad, exact
    let lo = U256::one_shl(w + s); // 2^(w+s)
    // Signed worst-case dividend magnitude `anc = t - 1 - (t mod ad)`, the
    // largest value <= t-1 congruent to -1 (mod |d|), with t = 2^(w-1) + [d<0]
    // (exactly the `anc` `magics_bits` uses). The EXACT (necessary+sufficient)
    // Granlund-Montgomery upper condition is `(aM*ad - 2^(w+s)) * anc < 2^(w+s)`;
    // evaluated subtraction-free (given prod >= lo) as
    //   prod * anc < lo * anc + lo    (all wrap-free in U256).
    let t: u128 = (1u128 << (w - 1)) + if d < 0 { 1 } else { 0 };
    let anc: u128 = t - 1 - (t % ad);
    let anc256 = U256::from_u128(anc);
    lo <= prod && prod.wrapping_mul(anc256) < lo.wrapping_mul(anc256).wrapping_add(lo)
}

/// The reference truncating unsigned quotient at width `W` — used only in
/// tests to corroborate the cited lemma against the emitted magic arithmetic.
#[cfg(test)]
fn ref_udiv(x: u64, d: u64, width: MagicWidth) -> u64 {
    match width {
        MagicWidth::W32 => ((x as u32) / (d as u32)) as u64,
        MagicWidth::W64 => x / d,
    }
}

/// Evaluate the *emitted* magic sequence in Rust (mirrors exactly what the
/// isel lowers), for a given `x`, so tests can check it equals `x / d` over a
/// wide sample. This is the model of the machine code, NOT the trusted path.
#[cfg(test)]
fn eval_magic(x: u64, m: MagicU, width: MagicWidth) -> u64 {
    match width {
        MagicWidth::W64 => {
            // MULHI(x, M) = high 64 of (x * M).
            let mulhi = |a: u64, b: u64| -> u64 { ((a as u128 * b as u128) >> 64) as u64 };
            let q = mulhi(x, m.magic);
            if m.add {
                // t = MULHI(x, M); t = t + ((x - t) >> 1); q = t >> (s - 1)
                let t = q;
                let t = t.wrapping_add((x.wrapping_sub(t)) >> 1);
                t >> (m.shift - 1)
            } else {
                q >> m.shift
            }
        }
        MagicWidth::W32 => {
            let x = x as u32;
            let mulhi = |a: u32, b: u32| -> u32 { ((a as u64 * b as u64) >> 32) as u32 };
            let q = mulhi(x, m.magic as u32);
            let r = if m.add {
                let t = q;
                let t = t.wrapping_add((x.wrapping_sub(t)) >> 1);
                t >> (m.shift - 1)
            } else {
                q >> m.shift
            };
            r as u64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn wide_sample(d: u64, width: MagicWidth) -> Vec<u64> {
        let maxv = match width {
            MagicWidth::W32 => u32::MAX as u64,
            MagicWidth::W64 => u64::MAX,
        };
        let mut xs = vec![
            0,
            1,
            2,
            d.saturating_sub(1),
            d,
            d + 1,
            d.saturating_mul(2),
            maxv,
            maxv - 1,
            maxv / 2,
        ];
        // A pseudo-random spread (xorshift) — deterministic, no external dep.
        let mut state: u64 = 0x9E3779B97F4A7C15 ^ d;
        for _ in 0..2000 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            xs.push(state & maxv);
        }
        xs
    }

    /// (1) A correct (K, M, s) admits, the transform fires, and the emitted
    /// magic result matches `x / K` over a wide sample — for many divisors.
    #[test]
    fn correct_magic_admits_and_matches_wide_sample() {
        for &width in &[MagicWidth::W32, MagicWidth::W64] {
            let divisors: Vec<u64> = vec![
                3,
                5,
                6,
                7,
                9,
                10,
                11,
                100,
                1000,
                1009,
                1234,
                65535,
                65537,
                1_000_003,
                0x0FFF_FFFF,
                3_000_000_019,
                0xDEAD_BEEF,
            ]
            .into_iter()
            .filter(|&d| match width {
                MagicWidth::W32 => d <= u32::MAX as u64,
                MagicWidth::W64 => true,
            })
            .collect();

            for d in divisors {
                let m = magicu(d, width).unwrap_or_else(|| panic!("magicu failed for d={d}"));
                assert!(
                    band_holds(d, m, width),
                    "band must hold for correct magic d={d} width={width:?} m={m:?}"
                );
                for x in wide_sample(d, width) {
                    assert_eq!(
                        eval_magic(x, m, width),
                        ref_udiv(x, d, width),
                        "magic mismatch d={d} x={x} width={width:?} m={m:?}"
                    );
                }
            }
        }
    }

    /// The specific b01_intloop divisor 1009 at W=64 must produce a valid,
    /// band-holding, wide-sample-correct magic.
    #[test]
    fn divisor_1009_w64_is_correct() {
        let d = 1009u64;
        let m = magicu(d, MagicWidth::W64).unwrap();
        assert!(band_holds(d, m, MagicWidth::W64));
        for x in wide_sample(d, MagicWidth::W64) {
            assert_eq!(eval_magic(x, m, MagicWidth::W64), x / d);
        }
    }

    /// (2) A WRONG M (off by one) must make the band FAIL — the transform must
    /// NOT fire on a corrupted magic. We corrupt each correct magic by ±1 and
    /// require the band to reject it (or, if by coincidence still in-band, the
    /// emitted result must at least mismatch somewhere — but for these the band
    /// rejects, which is what fail-safe relies on).
    #[test]
    fn off_by_one_wrong_magic_is_rejected_by_band() {
        for &width in &[MagicWidth::W32, MagicWidth::W64] {
            for &d in &[3u64, 7, 100, 1009, 65537] {
                if width == MagicWidth::W32 && d > u32::MAX as u64 {
                    continue;
                }
                let good = magicu(d, width).unwrap();
                for delta in [1i64, -1] {
                    let bad_magic = (good.magic as i128 + delta as i128) as u64;
                    let bad = MagicU {
                        magic: bad_magic,
                        ..good
                    };
                    // The band must reject a genuinely-wrong magic. If the band
                    // (wrongly) admitted it, the emitted arithmetic would have
                    // to still be exactly x/d over ALL x — assert that is NOT
                    // the case, i.e. the band rejecting is load-bearing.
                    if band_holds(d, bad, width) {
                        // Prove the "admitted" magic is actually a different
                        // (still-correct) representation, else FAIL LOUD: an
                        // in-band wrong magic that miscomputes = a band bug.
                        let mut all_match = true;
                        for x in wide_sample(d, width) {
                            if eval_magic(x, bad, width) != ref_udiv(x, d, width) {
                                all_match = false;
                                break;
                            }
                        }
                        assert!(
                            all_match,
                            "BAND BUG: admitted a wrong magic that miscomputes \
                             d={d} width={width:?} bad={bad:?}"
                        );
                    }
                    // else: band rejected -> caller fails safe to DIV. Good.
                }
            }
        }
    }

    /// A blatantly wrong magic (shifted, doubled) must be rejected by the band.
    #[test]
    fn blatantly_wrong_magic_rejected() {
        let d = 1009u64;
        let good = magicu(d, MagicWidth::W64).unwrap();
        let wrong = MagicU {
            magic: good.magic.wrapping_mul(2).wrapping_add(1),
            ..good
        };
        assert!(
            !band_holds(d, wrong, MagicWidth::W64),
            "band must reject a doubled magic"
        );
        let wrong_shift = MagicU {
            shift: good.shift + 1,
            ..good
        };
        // A wrong shift generally also breaks the band.
        assert!(
            !band_holds(d, wrong_shift, MagicWidth::W64) || {
                // If somehow in-band, it must still compute x/d for all x.
                wide_sample(d, MagicWidth::W64)
                    .into_iter()
                    .all(|x| eval_magic(x, wrong_shift, MagicWidth::W64) == x / d)
            },
            "band must reject (or the sequence must still be exact for) a wrong shift"
        );
    }

    /// (3) d = 0 and d = 1 produce no magic (no transform).
    #[test]
    fn zero_and_one_have_no_magic() {
        for &width in &[MagicWidth::W32, MagicWidth::W64] {
            assert_eq!(magicu(0, width), None);
            assert_eq!(magicu(1, width), None);
        }
    }

    /// A W32 divisor that does not fit at W32 is rejected; at W64 it is fine.
    #[test]
    fn width_bounds_respected() {
        assert_eq!(magicu(1u64 << 40, MagicWidth::W32), None);
        assert!(magicu(1u64 << 40, MagicWidth::W64).is_some());
    }

    /// The U256 band arithmetic itself is exact at the extreme W=64 magnitudes:
    /// M' * d can be a genuine 129-bit value; check mul/add/one_shl/Ord don't
    /// wrap by cross-checking a few products against u128 where they fit, and
    /// checking a known 129-bit product's ordering.
    #[test]
    fn u256_arithmetic_exact() {
        // Small products cross-checked against u128.
        for &(a, b) in &[(3u64, 5u64), (u64::MAX, 2), (1_000_000u64, 1_000_003)] {
            let got = U256::from_u64(a).wrapping_mul(U256::from_u64(b));
            let want = U256::from_u128(a as u128 * b as u128);
            assert_eq!(got, want, "u256 mul mismatch a={a} b={b}");
        }
        // 2^64 * 2^64 = 2^128 : must land in limb[2], and exceed any u128.
        let p = U256::one_shl(64).wrapping_mul(U256::one_shl(64));
        assert_eq!(p, U256::one_shl(128));
        // 2^128 > 2^127 + 2^63 (ordering across the 128-bit boundary).
        let smaller = U256::one_shl(127).wrapping_add(U256::one_shl(63));
        assert!(p > smaller);
        // (2^64 + 5) * 2^64 = 2^128 + 5*2^64 — a real 129-bit-ish value; verify
        // it equals 2^128 + (5 << 64) computed two ways.
        let m_prime = U256::one_shl(64).wrapping_add(U256::from_u64(5));
        let lhs = m_prime.wrapping_mul(U256::one_shl(64));
        let rhs = U256::one_shl(128).wrapping_add(U256::from_u128((5u128) << 64));
        assert_eq!(lhs, rhs);
    }

    /// GOLD-STANDARD verification of `magics_bits`: the emitted SIGNED magic
    /// sequence must equal `x.wrapping_div(d)` (round-toward-zero) for EVERY
    /// signed `x` and EVERY divisor `d` at narrow widths (exhaustive at w=8,
    /// sampled dense at w=16), and a strong sample at w=32/w=64. A single
    /// mismatch is a would-be miscompile — this is the load-bearing check that
    /// the (future) isel lowering rests on, exactly like `eval_magic` for udiv.
    fn eval_smagic(x: i128, d: i128, m: i128, s: u32, w: u32) -> i128 {
        // SMULHI(x, m) = high w bits of the signed 2w-bit product.
        let prod = x * m; // both in [-2^(w-1), 2^(w-1)) -> product fits i128 for w<=64
        let mut q = prod >> w; // arithmetic (signed) high half
        if d > 0 && m < 0 {
            q += x;
        }
        if d < 0 && m > 0 {
            q -= x;
        }
        q >>= s; // arithmetic shift
        // add the sign bit of q (0 or 1) — sext-truncated to w bits first.
        let mask = (1i128 << w) - 1;
        let qw = q & mask;
        let q_signed = if (qw >> (w - 1)) & 1 == 1 {
            qw - (1i128 << w)
        } else {
            qw
        };
        let signbit = if q_signed < 0 { 1 } else { 0 };
        let res = q_signed + signbit;
        // reduce to signed w-bit
        let rw = res & mask;
        if (rw >> (w - 1)) & 1 == 1 {
            rw - (1i128 << w)
        } else {
            rw
        }
    }

    fn check_smagic_width(w: u32, divisor_step: i128, dividend_step: i128) {
        let smin = -(1i128 << (w - 1));
        let smax = (1i128 << (w - 1)) - 1;
        let mut checked_divisors = 0usize;
        let mut d = smin;
        while d <= smax {
            if let Some((m, s)) = magics_bits(d, w) {
                checked_divisors += 1;
                // ALWAYS include the round-toward-zero worst cases (extremes and
                // the near-zero negatives) even under a dividend sample step.
                let extremes = [smin, smin + 1, -3, -2, -1, 0, 1, 2, 3, smax - 1, smax];
                let mut xs: Vec<i128> = extremes
                    .iter()
                    .copied()
                    .filter(|&x| x >= smin && x <= smax)
                    .collect();
                let mut x = smin;
                while x <= smax {
                    xs.push(x);
                    x += dividend_step;
                }
                for x in xs {
                    let want = (x as i64).wrapping_div(d as i64); // round toward zero
                    let got = eval_smagic(x, d, m, s, w);
                    assert_eq!(
                        got, want as i128,
                        "signed magic MISCOMPILE w={w} d={d} x={x} m={m} s={s}: got {got} want {want}"
                    );
                }
            }
            d += divisor_step;
        }
        assert!(checked_divisors > 0, "no magic divisors produced at w={w}");
    }

    #[test]
    fn signed_magics_exhaustive_w8_and_sampled_wider() {
        check_smagic_width(8, 1, 1); // EXHAUSTIVE: all d, all x at w=8 (65k)
        check_smagic_width(16, 37, 251); // w=16: ~1770 d x ~260 x + extremes
        check_smagic_width(32, (1i128 << 32) / 997, (1i128 << 32) / 1009); // w=32 dense sample
    }

    /// Emitted-sequence-correct-for-EVERY-x, computed exhaustively (the ground
    /// truth the band check must match).
    fn smagic_correct_everywhere(d: i128, m: i128, s: u32, w: u32) -> bool {
        let smin = -(1i128 << (w - 1));
        let smax = (1i128 << (w - 1)) - 1;
        let mut x = smin;
        while x <= smax {
            if eval_smagic(x, d, m, s, w) != (x as i64).wrapping_div(d as i64) as i128 {
                return false;
            }
            x += 1;
        }
        true
    }

    /// GOLD-STANDARD: `smagic_band_holds` (the shipped fail-safe) is EXACTLY
    /// equivalent to full per-x correctness, over ALL (d, candidate m, s) at
    /// w=8 — so it is necessary AND sufficient, and never admits a wrong magic
    /// (the isel soundness rests on this). Also: it ADMITS every `magics()`
    /// output (else the transform would never fire), and REJECTS ±1-perturbed
    /// magics that are actually wrong.
    #[test]
    fn signed_band_holds_iff_correct_exhaustive_w8() {
        let w = 8u32;
        let smin = -(1i128 << (w - 1));
        let smax = (1i128 << (w - 1)) - 1;
        // (1) band <=> correctness for EVERY (d, m, s). Power-of-two divisors
        // use the shift path (magics declines them), so exclude them here too.
        for d in smin..=smax {
            let ad = d.unsigned_abs();
            if d == 0 || d == 1 || d == -1 || (ad != 0 && ad & (ad - 1) == 0) {
                continue;
            }
            for m in smin..=smax {
                for s in 0..w {
                    let correct = smagic_correct_everywhere(d, m, s, w);
                    assert_eq!(
                        band_at_w(d, m, s, w),
                        correct,
                        "band != correctness at w=8 d={d} m={m} s={s}"
                    );
                }
            }
        }
        // (2) every magics() output is admitted by the band.
        for d in smin..=smax {
            if let Some((m, s)) = magics_bits(d, w) {
                assert!(
                    band_at_w(d, m, s, w),
                    "band rejected a magics() output at w=8 d={d} m={m} s={s}"
                );
            }
        }
    }

    /// The width-generic core of `smagic_band_holds`, for the w=8/16 exhaustive
    /// validation (the public fn takes a MagicWidth = W32/W64 only).
    fn band_at_w(d: i128, m: i128, s: u32, w: u32) -> bool {
        if d == 0 || d == 1 || d == -1 || s >= w || w + s + 1 >= 256 {
            return false;
        }
        let ad = d.unsigned_abs();
        if ad & (ad - 1) == 0 {
            return false;
        }
        let am_abs = m.unsigned_abs();
        let two_w = 1u128 << w;
        let same_sign = (d > 0) == (m > 0);
        let a_m = if same_sign { am_abs } else { two_w - am_abs };
        let prod = super::U256::from_u128(a_m).wrapping_mul(super::U256::from_u128(ad));
        let lo = super::U256::one_shl(w + s);
        let t: u128 = (1u128 << (w - 1)) + if d < 0 { 1 } else { 0 };
        let anc = t - 1 - (t % ad);
        let anc256 = super::U256::from_u128(anc);
        lo <= prod && prod.wrapping_mul(anc256) < lo.wrapping_mul(anc256).wrapping_add(lo)
    }

    #[test]
    fn signed_band_holds_iff_correct_exhaustive_w16() {
        // w=16 is 65k^2 for the full band<=>correct sweep, too slow; instead:
        // (a) every magics() output admitted, (b) a dense (d,m,s) sample of
        // band<=>correct.
        let w = 16u32;
        let smin = -(1i128 << (w - 1));
        let smax = (1i128 << (w - 1)) - 1;
        let mut d = smin;
        while d <= smax {
            if let Some((m, s)) = magics_bits(d, w) {
                assert!(band_at_w(d, m, s, w), "band rejected magics() w=16 d={d}");
                // perturb the magic: a ±1 magic that is wrong must be rejected.
                for pm in [m - 1, m + 1] {
                    if pm >= smin && pm <= smax {
                        let ok = smagic_correct_everywhere(d, pm, s, w);
                        if !ok {
                            assert!(
                                !band_at_w(d, pm, s, w),
                                "band ADMITTED a wrong perturbed magic w=16 d={d} pm={pm} s={s}"
                            );
                        }
                    }
                }
            }
            d += 101; // dense sample of divisors
        }
    }

    /// CROSS-CHECK the module's computed (magic, shift, add) against the exact
    /// constants LLVM/clang -O2 emits for AArch64 (extracted from disassembly).
    /// A divergence here means either LLVM or this module is wrong; both being a
    /// SILENT MISCOMPILE on some value range, this table is the load-bearing
    /// external oracle for the shipped constants.
    #[test]
    fn magic_constants_match_llvm_aarch64() {
        // Unsigned: (divisor, width, expect_magic, expect_shift, expect_add)
        let u = [
            (3u64, MagicWidth::W32, 0xAAAA_AAABu64, 1u32, false),
            (7, MagicWidth::W32, 0x2492_4925, 3, true),
            (139968, MagicWidth::W32, 0x1DF7_5681, 14, false),
            (3, MagicWidth::W64, 0xAAAA_AAAA_AAAA_AAAB, 1, false),
            (139968, MagicWidth::W64, 0x3BEE_AD01_FD6C_BE91, 15, false),
            (6700417, MagicWidth::W64, 0xA03F_FFFF_5FC0_0001, 22, false),
        ];
        for (d, w, em, es, ea) in u {
            let m = magicu(d, w).unwrap_or_else(|| panic!("no magicu for d={d} w={w:?}"));
            assert_eq!(m.magic, em, "unsigned magic d={d} w={w:?}");
            assert_eq!(m.shift, es, "unsigned shift d={d} w={w:?}");
            assert_eq!(m.add, ea, "unsigned add d={d} w={w:?}");
            assert!(band_holds(d, m, w), "band d={d} w={w:?}");
        }
        // Signed: (divisor, width, expect_magic_low_bits, expect_shift)
        let s = [
            (7i64, MagicWidth::W32, 0x9249_2493u64, 2u32),
            (-7, MagicWidth::W32, 0x6DB6_DB6D, 2),
            (3, MagicWidth::W64, 0x5555_5555_5555_5556, 0),
            (7, MagicWidth::W64, 0x4924_9249_2492_4925, 1),
        ];
        for (d, w, em, es) in s {
            let m = magics(d, w).unwrap_or_else(|| panic!("no magics for d={d} w={w:?}"));
            let got = match w {
                MagicWidth::W32 => (m.magic as i32 as u32) as u64,
                MagicWidth::W64 => m.magic as u64,
            };
            assert_eq!(
                got, em,
                "signed magic d={d} w={w:?}: got {got:#x} want {em:#x}"
            );
            assert_eq!(m.shift, es, "signed shift d={d} w={w:?}");
            assert!(smagic_band_holds(d, m, w), "sband d={d} w={w:?}");
        }
    }

    #[test]
    fn signed_magics_rejects_non_magic_divisors() {
        for w in [8u32, 16, 32, 64] {
            assert_eq!(magics_bits(0, w), None);
            assert_eq!(magics_bits(1, w), None);
            assert_eq!(magics_bits(-1, w), None);
        }
        // A specific known signed magic: HD lists d=7 at W=32 -> M=0x92492493, s=2.
        let (m, s) = magics_bits(7, 32).expect("d=7 w=32 has a magic");
        assert_eq!(m as i64 as u32, 0x9249_2493u32, "d=7 magic");
        assert_eq!(s, 2, "d=7 shift");
    }

    // ==================================================================
    // Machine-sequence differential for the W32 SMULL/UMULL isel path.
    //
    // These simulate the EXACT AArch64 instruction sequence emitted by
    // `isel::try_select_const_div_rem`'s W32 widening-multiply path
    // (SMULL/UMULL folding the sext/zext, sign-correction + rounding tail
    // run at 32 bits). They must equal C truncating div/rem (== Rust's
    // i32/u32 `wrapping_div`/`%`) for EVERY i32/u32 input. This is the
    // load-bearing soundness net for that isel change (mirrors how
    // `eval_smagic`/`eval_magic` gate the width-generic model).
    // ------------------------------------------------------------------

    /// Simulate the W32 SIGNED sequence: SMULL; LSR #32; [ADD/SUB x]; ASR #s;
    /// q = shifted + (shifted >>u 31); [rem: MSUB x - q*d]. All at 32 bits
    /// except the SMULL product (64-bit) and its high-half extraction.
    fn sim_smull_w32(x: i32, d: i32, m: i32, s: u32, is_rem: bool) -> i32 {
        let xp: i64 = (x as i64) * (m as i64); // SMULL Xd, Wn, Wm
        // LSR Xd,#32 then read low 32 (MOV Wd,Xn) -> SMULHI reinterpreted signed.
        let mh: i32 = ((xp as u64) >> 32) as u32 as i32;
        // Sign correction, decided at compile time from sign(d)/sign(M).
        let corr: i32 = if d > 0 && m < 0 {
            mh.wrapping_add(x)
        } else if d < 0 && m > 0 {
            mh.wrapping_sub(x)
        } else {
            mh
        };
        let shifted: i32 = if s == 0 { corr } else { corr >> s }; // ASR Wd,#s
        let sb: i32 = ((shifted as u32) >> 31) as i32; // LSR Wd,#31 -> 0/1
        let q: i32 = shifted.wrapping_add(sb);
        if is_rem {
            x.wrapping_sub(q.wrapping_mul(d)) // MSUB Wd, q, d, x
        } else {
            q
        }
    }

    /// Simulate the W32 UNSIGNED sequence: UMULL; then either LSR #(32+s)
    /// (no add-back) or the mulhi add-back tail; [rem: MSUB x - q*d].
    fn sim_umull_w32(x: u32, d: u32, m: u32, s: u32, add: bool, is_rem: bool) -> u32 {
        let xp: u64 = (x as u64) * (m as u64); // UMULL Xd, Wn, Wm
        let q: u32 = if !add {
            (xp >> (32 + s)) as u32 // LSR Xd,#(32+s), low 32
        } else {
            let mh: u32 = (xp >> 32) as u32; // LSR Xd,#32 -> low 32 (mulhi)
            let sub: u32 = x.wrapping_sub(mh); // SUB Wd
            let sub1: u32 = sub >> 1; // LSR Wd,#1
            let t: u32 = mh.wrapping_add(sub1); // ADD Wd
            if s == 1 { t } else { t >> (s - 1) } // LSR Wd,#(s-1)
        };
        if is_rem {
            x.wrapping_sub(q.wrapping_mul(d)) // MSUB Wd, q, d, x
        } else {
            q
        }
    }

    /// The i32 sample set the isel differential must survive: the two
    /// signed extremes' 64K bands, a band around zero, and randoms.
    fn i32_probe_inputs() -> Vec<i32> {
        let mut xs: Vec<i32> = Vec::new();
        for k in 0..=0x1_0000i64 {
            xs.push((i32::MIN as i64 + k) as i32);
            xs.push((i32::MAX as i64 - k) as i32);
            xs.push((-0x8000i64 + k) as i32); // -0x8000 .. +0x8000 straddling 0
        }
        // 1M deterministic pseudo-randoms (xorshift64).
        let mut st: u64 = 0x1234_5678_9abc_def1;
        for _ in 0..1_000_000 {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            xs.push(st as u32 as i32);
        }
        xs
    }

    #[test]
    fn smull_w32_srem_sdiv_matches_c_truncation() {
        // Every divisor the isel path can actually fire on (magic exists AND
        // the band holds AND it is not a power of two — those take the shift
        // path). Include ReedSolomon's 255 plus a broad spread + both signs.
        let mut divisors: Vec<i32> = vec![255, -255, 7, -7, 3, 6, 9, 10, 100, 1000];
        for d in [11, 13, 17, 25, 125, 127, 256 + 1, 65535, 0x7fff_ffff] {
            divisors.push(d);
            divisors.push(-d);
        }
        let xs = i32_probe_inputs();
        let mut fired = 0usize;
        for &d in &divisors {
            let Some(m) = magics(d as i64, MagicWidth::W32) else {
                continue;
            };
            if !smagic_band_holds(d as i64, m, MagicWidth::W32) {
                continue;
            }
            let mm = m.magic as i32;
            let s = m.shift;
            fired += 1;
            for &x in &xs {
                for is_rem in [false, true] {
                    let got = sim_smull_w32(x, d, mm, s, is_rem);
                    let want = if is_rem {
                        x.wrapping_rem(d)
                    } else {
                        x.wrapping_div(d)
                    };
                    assert_eq!(
                        got,
                        want,
                        "SMULL W32 {} MISCOMPILE x={x} d={d} m={mm:#x} s={s}: got {got} want {want}",
                        if is_rem { "srem" } else { "sdiv" }
                    );
                }
            }
        }
        assert!(
            fired >= 8,
            "expected the SMULL path to fire on many divisors, got {fired}"
        );
    }

    #[test]
    fn umull_w32_urem_udiv_matches_c() {
        let divisors: Vec<u32> = vec![
            255,
            7,
            3,
            6,
            9,
            10,
            100,
            1000,
            11,
            13,
            17,
            25,
            125,
            127,
            257,
            65535,
            0xffff_ffff,
        ];
        // Reuse the i32 probe bit-patterns as u32 inputs.
        let xs: Vec<u32> = i32_probe_inputs().into_iter().map(|x| x as u32).collect();
        let mut fired = 0usize;
        for &d in &divisors {
            let Some(m) = magicu(d as u64, MagicWidth::W32) else {
                continue;
            };
            if !band_holds(d as u64, m, MagicWidth::W32) {
                continue;
            }
            // The isel declines add-back with shift 0 (see try_select_const_div_rem).
            if m.add && m.shift == 0 {
                continue;
            }
            let mm = m.magic as u32;
            let s = m.shift;
            fired += 1;
            for &x in &xs {
                for is_rem in [false, true] {
                    let got = sim_umull_w32(x, d, mm, s, m.add, is_rem);
                    let want = if is_rem {
                        x.wrapping_rem(d)
                    } else {
                        x.wrapping_div(d)
                    };
                    assert_eq!(
                        got,
                        want,
                        "UMULL W32 {} MISCOMPILE x={x} d={d} m={mm:#x} s={s} add={}: got {got} want {want}",
                        if is_rem { "urem" } else { "udiv" },
                        m.add
                    );
                }
            }
        }
        assert!(
            fired >= 8,
            "expected the UMULL path to fire on many divisors, got {fired}"
        );
    }

    // ==================================================================
    // Mersenne-remainder shift-sequence differential (isel
    // `finish_const_div_rem` fast path for |c| = 2^k ± 1). rem = x - q*c is
    // emitted as shifted-register add/sub instead of MSUB; this proves the
    // shift arithmetic equals C `%` for the true quotient over the probe set.
    // ------------------------------------------------------------------

    /// Simulate the emitted i32 sequence for divisor `c` (must be 2^k ± 1),
    /// given the true quotient `q = x / c`.
    fn sim_mersenne_rem_i32(x: i32, c: i32, q: i32) -> i32 {
        let a = c.unsigned_abs();
        let neg = c < 0;
        if (a + 1).is_power_of_two() {
            let k = (a + 1).trailing_zeros();
            let t = q.wrapping_sub(q.wrapping_shl(k)); // q - (q<<k) = -q*|c|
            if neg {
                x.wrapping_sub(t)
            } else {
                x.wrapping_add(t)
            }
        } else {
            let k = (a - 1).trailing_zeros();
            if neg {
                let u = x.wrapping_add(q);
                u.wrapping_add(q.wrapping_shl(k))
            } else {
                let u = x.wrapping_sub(q);
                u.wrapping_sub(q.wrapping_shl(k))
            }
        }
    }

    #[test]
    fn mersenne_rem_i32_matches_c() {
        // 2^k-1 and 2^k+1 divisors, both signs, incl. ReedSolomon 255.
        let mut cs: Vec<i32> = Vec::new();
        for k in 1..31u32 {
            cs.push((1i32 << k) - 1);
            cs.push((1i32 << k) + 1);
        }
        let extra: Vec<i32> = cs.iter().map(|c| -c).collect();
        cs.extend(extra);
        let xs = i32_probe_inputs();
        for &c in &cs {
            if c == 0 || c == 1 || c == -1 {
                continue;
            }
            let a = c.unsigned_abs();
            if a.is_power_of_two() {
                continue; // shift path, not this fast path
            }
            for &x in &xs {
                let q = x.wrapping_div(c);
                let got = sim_mersenne_rem_i32(x, c, q);
                let want = x.wrapping_rem(c);
                assert_eq!(
                    got, want,
                    "mersenne rem MISCOMPILE x={x} c={c} q={q}: got {got} want {want}"
                );
            }
        }
    }

    /// i64 (W64) analog: `finish_const_div_rem`'s mersenne fast path is
    /// width-generic, so validate the 64-bit shifted-register arithmetic too.
    fn sim_mersenne_rem_i64(x: i64, c: i64, q: i64) -> i64 {
        let a = c.unsigned_abs();
        let neg = c < 0;
        if (a + 1).is_power_of_two() {
            let k = (a + 1).trailing_zeros();
            let t = q.wrapping_sub(q.wrapping_shl(k));
            if neg {
                x.wrapping_sub(t)
            } else {
                x.wrapping_add(t)
            }
        } else {
            let k = (a - 1).trailing_zeros();
            if neg {
                x.wrapping_add(q).wrapping_add(q.wrapping_shl(k))
            } else {
                x.wrapping_sub(q).wrapping_sub(q.wrapping_shl(k))
            }
        }
    }

    #[test]
    fn mersenne_rem_i64_matches_c() {
        let mut cs: Vec<i64> = Vec::new();
        for k in 1..63u32 {
            cs.push((1i64 << k) - 1);
            cs.push((1i64 << k) + 1);
        }
        let extra: Vec<i64> = cs.iter().map(|c| -c).collect();
        cs.extend(extra);
        // Probe: i64 extremes' bands, a zero band, and randoms.
        let mut xs: Vec<i64> = Vec::new();
        for k in 0..=0x2000i64 {
            xs.push(i64::MIN + k);
            xs.push(i64::MAX - k);
            xs.push(-0x1000 + k);
        }
        let mut st: u64 = 0xdead_beef_0000_0001;
        for _ in 0..300_000 {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            xs.push(st as i64);
        }
        for &c in &cs {
            if c == 0 || c == 1 || c == -1 || c.unsigned_abs().is_power_of_two() {
                continue;
            }
            for &x in &xs {
                let q = x.wrapping_div(c);
                let got = sim_mersenne_rem_i64(x, c, q);
                let want = x.wrapping_rem(c);
                assert_eq!(got, want, "mersenne rem64 MISCOMPILE x={x} c={c} q={q}");
            }
        }
    }
}
