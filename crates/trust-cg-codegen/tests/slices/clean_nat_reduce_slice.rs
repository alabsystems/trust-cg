// R13 — THE NAT REDUCER, LIVE. Verbatim transcription of clean-kernel's
// literal-arithmetic Nat reducer (tc/reduction/nat.rs) + the BigNat
// arbitrary-precision arithmetic (expr/types.rs + expr/bignat_ops.rs), wired
// into a faithful whnf_core + lazy-delta def_eq at the PRODUCTION hook
// positions, verified native == JIT (Clean's CIC kernel through Trust:
// Rust -> MIR -> trust-ir -> trust-cg -> machine code).
//
// This is SOUNDNESS-CRITICAL: a wrong Nat literal reduction lets you prove
// False (2+2 =?= 5). No prior round exercised reduce_nat — every scenario input
// returned None on the R6..R12 stub. This round makes it LIVE and proves it
// computes the RIGHT answer, bit-for-bit against an independent oracle.
//
// PRODUCTION HOOK POSITIONS transcribed verbatim:
//   * whnf_core pre-check (tc/whnf.rs:421-424): App with a visible Const head
//     -> reduce_nat(e) BEFORE beta/delta.
//   * whnf_core beta_or_iota stuck fallback (tc/whnf.rs:616-626): after
//     iota/quot, reduce_nat(&app_with_whnf).
//   * lazy_delta_reduction loop top (tc/def_eq/delta.rs:88-134): (1)
//     is_def_eq_offset, (2) reduce_nat under the
//     `(!t.has_fvar_quick() && !s.has_fvar_quick()) || eager_reduce` guard,
//     (3) reduce_native (registry empty), (4) try_monad_reduce (registry empty).
//
// THE BLIND CONTROL: `Verifier.blind_nat` gates reduce_nat's FIRST line
// (`if self.blind_nat { return None; }`). Aware and blind share EVERY other
// line of the engine, so any verdict divergence is 100% attributable to
// reduce_nat — the sharpest possible falsifiability construction. A second
// gate `blind_offset` isolates is_def_eq_offset the same way.
//
// MODELED BOUNDARIES (documented, inert on the exercised surface):
//   [B-u128]  CLOSED: trust-cg now lowers the u128 `mul.overflow` used by
//             BigNat multiplication. Nat.mul / Nat.pow therefore run through
//             the same production-position `reduce_nat` hook as every other
//             Nat operation and are differentially checked native==JIT against
//             an independent u128 oracle.
//   [B-name]  Name modeled as its identity hash `Name{h:u64}` (name_eq = h==h);
//             reduce_nat/is_def_eq_offset only need name IDENTITY. Production
//             Names (murmur/mix chains) are de-modeled in R4/R5/R6/R7.
//   [B-levels] Const is monomorphic (implicit empty level list); Sort carries a
//             u32 depth. The nat consts all have empty levels; full Max/IMax is
//             verified in R1/R6.
//   [B-lit]   Literal = Nat(BigNat) only (the String variant is out of scope —
//             the nat reducer never touches it; String is de-modeled in R3/R4).
//   [B-ctx]   No LocalContext (fvars are always free/valueless here); the R8/R9
//             context zeta / proof-irrel machinery is out of scope.
//   [B8]      iota/quot reduction stubbed None (registry empty) — so a
//             bodyless-def Nat.add has NO delta/iota fallback, making reduce_nat
//             the UNIQUE fold path (production ALSO reaches reduce_nat as a
//             pre-check before any unfold; the difference is only the slower
//             fallback the stub removes, which sharpens attribution).
//   [B9]      BigNat internals use index loops in place of the production
//             iterator chains (iter().rev().zip(), .all(), .last()) — pure
//             evaluation-strategy rewrites, bit-identical results. Closure
//             arguments to reduce_bin_bignat_op are inlined per op.
//   [B-meta]  ExprMeta.hash is a plain in-fn FNV-style mix (NOT the production
//             KaniHasher/SipHash — those are closed in R6/R7). It is used only
//             for the native==JIT bit-identity check; both sides compute the
//             same mix. has_fvar IS faithful (drives reduce_nat's fvar guard).
//
// Source of truth (read in full):
//   $HOME/clean/crates/clean-kernel/src/tc/reduction/nat.rs      (reduce_nat etc.)
//   $HOME/clean/crates/clean-kernel/src/expr/types.rs:166-370    (BigNat)
//   $HOME/clean/crates/clean-kernel/src/expr/bignat_ops.rs       (div/mod/gcd/…)
//   $HOME/clean/crates/clean-kernel/src/tc/whnf.rs:421,616       (whnf hooks)
//   $HOME/clean/crates/clean-kernel/src/tc/def_eq/delta.rs:88    (lazy-delta hooks)

#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(unused_parens)]

use std::convert::TryFrom;
use std::sync::Arc; // pre-2021 prelude (the MIR driver's edition)

// ════════════════════════════════════════════════════════════════════════════
// Name — [B-name]: identity hash.
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Name {
    pub h: u64,
}
pub fn name_eq(a: &Name, b: &Name) -> bool {
    a.h == b.h
}

// The interned Nat/Bool op names (distinct identity hashes). reduce_nat keys on
// these exactly as production keys on names::NAT_ADD etc.
pub fn nat_zero_name() -> Name {
    Name { h: 1001 }
}
pub fn nat_succ_name() -> Name {
    Name { h: 1002 }
}
pub fn nat_pred_name() -> Name {
    Name { h: 1003 }
}
pub fn nat_add_name() -> Name {
    Name { h: 1004 }
}
pub fn nat_sub_name() -> Name {
    Name { h: 1005 }
}
pub fn nat_mul_name() -> Name {
    Name { h: 1006 }
}
pub fn nat_div_name() -> Name {
    Name { h: 1007 }
}
pub fn nat_mod_name() -> Name {
    Name { h: 1008 }
}
pub fn nat_gcd_name() -> Name {
    Name { h: 1009 }
}
pub fn nat_pow_name() -> Name {
    Name { h: 1010 }
}
pub fn nat_beq_name() -> Name {
    Name { h: 1011 }
}
pub fn nat_ble_name() -> Name {
    Name { h: 1012 }
}
pub fn nat_land_name() -> Name {
    Name { h: 1013 }
}
pub fn nat_lor_name() -> Name {
    Name { h: 1014 }
}
pub fn nat_xor_name() -> Name {
    Name { h: 1015 }
}
pub fn nat_shl_name() -> Name {
    Name { h: 1016 }
}
pub fn nat_shr_name() -> Name {
    Name { h: 1017 }
}
pub fn bool_true_name() -> Name {
    Name { h: 2001 }
}
pub fn bool_false_name() -> Name {
    Name { h: 2002 }
}
// Non-nat test consts (for the inertness / delta scenarios).
pub fn nm_foo() -> Name {
    Name { h: 3001 }
}
pub fn nm_bar() -> Name {
    Name { h: 3002 }
}
pub fn nm_dfn() -> Name {
    Name { h: 3003 }
} // a def whose body is `foo` (delta)
pub fn nm_g() -> Name {
    Name { h: 3004 }
}

// ════════════════════════════════════════════════════════════════════════════
// BigNat — expr/types.rs:166-370 + bignat_ops.rs. [B9] index loops.
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone)]
pub enum BigNat {
    Small(u64),
    Big(Vec<u64>),
}

// wrapping mul helper for the hash mix (kept out of BigNat arithmetic).
fn wmul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

impl BigNat {
    // limbs() — production returns &[u64] (from_ref / slice). Here we return an
    // OWNED Vec<u64> clone (index-loop) to keep the ABI simple. [B9]
    pub fn limbs(&self) -> Vec<u64> {
        match self {
            BigNat::Small(v) => {
                let mut r: Vec<u64> = Vec::new();
                r.push(*v);
                r
            }
            BigNat::Big(l) => {
                let mut r: Vec<u64> = Vec::new();
                let mut i = 0usize;
                while i < l.len() {
                    r.push(l[i]);
                    i += 1;
                }
                r
            }
        }
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self {
            BigNat::Small(v) => Some(*v),
            BigNat::Big(_) => None,
        }
    }

    // types.rs:245-251 is_zero — [B9] index loop for the Big arm.
    pub fn is_zero(&self) -> bool {
        match self {
            BigNat::Small(v) => *v == 0,
            BigNat::Big(l) => {
                let mut i = 0usize;
                while i < l.len() {
                    if l[i] != 0 {
                        return false;
                    }
                    i += 1;
                }
                true
            }
        }
    }

    // types.rs:208-224 from_limbs — [B9] index-based high-zero strip.
    pub fn from_limbs(limbs_in: Vec<u64>) -> BigNat {
        let mut limbs = limbs_in;
        if limbs.len() == 0 {
            return BigNat::Small(0);
        }
        while limbs.len() > 1 {
            let last = limbs[limbs.len() - 1];
            if last == 0 {
                limbs.pop();
            } else {
                break;
            }
        }
        if limbs.len() == 1 {
            BigNat::Small(limbs[0])
        } else {
            BigNat::Big(limbs)
        }
    }

    // types.rs:179-198 Ord::cmp — [B9] index loop, MSB-first. Returns
    // -1 (self<other), 0 (equal), 1 (self>other).
    pub fn cmp_big(&self, other: &BigNat) -> i32 {
        let a = self.limbs();
        let b = other.limbs();
        if a.len() < b.len() {
            return -1;
        }
        if a.len() > b.len() {
            return 1;
        }
        // same number of significant limbs: compare MSB -> LSB
        let n = a.len();
        let mut i = n;
        while i > 0 {
            i -= 1;
            if a[i] < b[i] {
                return -1;
            }
            if a[i] > b[i] {
                return 1;
            }
        }
        0
    }
    pub fn le_big(&self, other: &BigNat) -> bool {
        self.cmp_big(other) <= 0
    }
    pub fn lt_big(&self, other: &BigNat) -> bool {
        self.cmp_big(other) < 0
    }
    pub fn eq_big(&self, other: &BigNat) -> bool {
        self.cmp_big(other) == 0
    }
    pub fn ge_big(&self, other: &BigNat) -> bool {
        self.cmp_big(other) >= 0
    }

    // types.rs:256-274 checked_add_big — verbatim (already an index loop).
    pub fn checked_add_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let max_len = if a.len() > b.len() { a.len() } else { b.len() };
        let mut result: Vec<u64> = Vec::new();
        let mut carry = 0u64;
        let mut i = 0usize;
        while i < max_len {
            let av = if i < a.len() { a[i] } else { 0 };
            let bv = if i < b.len() { b[i] } else { 0 };
            let (sum1, c1) = av.overflowing_add(bv);
            let (sum2, c2) = sum1.overflowing_add(carry);
            result.push(sum2);
            carry = (c1 as u64) + (c2 as u64);
            i += 1;
        }
        if carry > 0 {
            result.push(carry);
        }
        BigNat::from_limbs(result)
    }

    // types.rs:279-295 saturating_sub_big — verbatim (index loop; Lean floored).
    pub fn saturating_sub_big(&self, other: &BigNat) -> BigNat {
        if self.le_big(other) {
            return BigNat::Small(0);
        }
        let a = self.limbs();
        let b = other.limbs();
        let mut result: Vec<u64> = Vec::new();
        let mut borrow = 0u64;
        let mut i = 0usize;
        while i < a.len() {
            let bv = if i < b.len() { b[i] } else { 0 };
            let (diff1, b1) = a[i].overflowing_sub(bv);
            let (diff2, b2) = diff1.overflowing_sub(borrow);
            result.push(diff2);
            borrow = (b1 as u64) + (b2 as u64);
            i += 1;
        }
        BigNat::from_limbs(result)
    }

    // bignat_ops.rs:132-154 checked_shl_big — verbatim (index loop).
    pub fn checked_shl_big(&self, shift: usize) -> BigNat {
        if self.is_zero() {
            return BigNat::Small(0);
        }
        let limb_shift = shift / 64;
        let bit_shift = shift % 64;
        let a = self.limbs();
        let new_len = a.len() + limb_shift + 1;
        let mut result: Vec<u64> = Vec::new();
        let mut z = 0usize;
        while z < new_len {
            result.push(0);
            z += 1;
        }
        let mut carry = 0u64;
        let mut i = 0usize;
        while i < a.len() {
            if bit_shift == 0 {
                result[i + limb_shift] = a[i];
            } else {
                result[i + limb_shift] = result[i + limb_shift] | ((a[i] << bit_shift) | carry);
                carry = a[i] >> (64 - bit_shift);
            }
            i += 1;
        }
        if carry > 0 {
            result[a.len() + limb_shift] = carry;
        }
        BigNat::from_limbs(result)
    }

    // bignat_ops.rs:157-181 shr_big — verbatim (index loop).
    pub fn shr_big(&self, shift: usize) -> BigNat {
        let limb_shift = shift / 64;
        let bit_shift = shift % 64;
        let a = self.limbs();
        if limb_shift >= a.len() {
            return BigNat::Small(0);
        }
        let new_len = a.len() - limb_shift;
        let mut result: Vec<u64> = Vec::new();
        let mut i = 0usize;
        while i < new_len {
            let src_idx = i + limb_shift;
            if bit_shift == 0 {
                result.push(a[src_idx]);
            } else {
                let lo = a[src_idx] >> bit_shift;
                let hi = if src_idx + 1 < a.len() {
                    a[src_idx + 1] << (64 - bit_shift)
                } else {
                    0
                };
                result.push(lo | hi);
            }
            i += 1;
        }
        BigNat::from_limbs(result)
    }

    // bignat_ops.rs:13-21 bignat_bit_length — [B9] countdown index loop.
    pub fn bit_length(&self) -> usize {
        let limbs = self.limbs();
        let mut i = limbs.len();
        while i > 0 {
            i -= 1;
            if limbs[i] != 0 {
                return i * 64 + (64 - (limbs[i].leading_zeros() as usize));
            }
        }
        0
    }

    // bignat_ops.rs:28-68 checked_div_rem_big — verbatim shift-subtract long
    // division (index loops; no u128).
    pub fn checked_div_rem_big(&self, other: &BigNat) -> Option<(BigNat, BigNat)> {
        if other.is_zero() {
            return None;
        }
        // Fast path: both fit in u64.
        match (self, other) {
            (BigNat::Small(a), BigNat::Small(b)) => {
                return Some((BigNat::Small(a / b), BigNat::Small(a % b)));
            }
            _ => {}
        }
        if self.lt_big(other) {
            return Some((BigNat::Small(0), self.clone()));
        }
        let mut remainder = self.clone();
        let self_len = self.limbs().len();
        let mut quotient_limbs: Vec<u64> = Vec::new();
        let mut z = 0usize;
        while z < self_len {
            quotient_limbs.push(0);
            z += 1;
        }
        let divisor_bits = other.bit_length();
        let dividend_bits = remainder.bit_length();
        let mut shift = if dividend_bits > divisor_bits {
            dividend_bits - divisor_bits
        } else {
            0
        };
        loop {
            let shifted_divisor = other.checked_shl_big(shift);
            if remainder.ge_big(&shifted_divisor) {
                remainder = remainder.saturating_sub_big(&shifted_divisor);
                let limb_idx = shift / 64;
                let bit_idx = shift % 64;
                if limb_idx < quotient_limbs.len() {
                    quotient_limbs[limb_idx] = quotient_limbs[limb_idx] | (1u64 << bit_idx);
                }
            }
            if shift == 0 {
                break;
            }
            shift -= 1;
        }
        Some((BigNat::from_limbs(quotient_limbs), remainder))
    }

    // bignat_ops.rs:73-88 — Lean semantics: n/0 = 0, n%0 = n.
    pub fn checked_div_big(&self, other: &BigNat) -> BigNat {
        match self.checked_div_rem_big(other) {
            Some((q, _)) => q,
            None => BigNat::Small(0),
        }
    }
    pub fn checked_mod_big(&self, other: &BigNat) -> BigNat {
        match self.checked_div_rem_big(other) {
            Some((_, r)) => r,
            None => self.clone(),
        }
    }

    // bignat_ops.rs:91-129 bitwise — verbatim (index loops).
    pub fn bitand_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let min_len = if a.len() < b.len() { a.len() } else { b.len() };
        let mut result: Vec<u64> = Vec::new();
        let mut i = 0usize;
        while i < min_len {
            result.push(a[i] & b[i]);
            i += 1;
        }
        BigNat::from_limbs(result)
    }
    pub fn bitor_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let max_len = if a.len() > b.len() { a.len() } else { b.len() };
        let mut result: Vec<u64> = Vec::new();
        let mut i = 0usize;
        while i < max_len {
            let av = if i < a.len() { a[i] } else { 0 };
            let bv = if i < b.len() { b[i] } else { 0 };
            result.push(av | bv);
            i += 1;
        }
        BigNat::from_limbs(result)
    }
    pub fn bitxor_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let max_len = if a.len() > b.len() { a.len() } else { b.len() };
        let mut result: Vec<u64> = Vec::new();
        let mut i = 0usize;
        while i < max_len {
            let av = if i < a.len() { a[i] } else { 0 };
            let bv = if i < b.len() { b[i] } else { 0 };
            result.push(av ^ bv);
            i += 1;
        }
        BigNat::from_limbs(result)
    }

    // bignat_ops.rs:189-198 gcd_big — verbatim Euclid via checked_mod_big.
    pub fn gcd_big(&self, other: &BigNat) -> BigNat {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.checked_mod_big(&b);
            a = b;
            b = r;
        }
        a
    }

    // types.rs:344-369 pred — verbatim (index loop, borrow propagation).
    pub fn pred(&self) -> Option<BigNat> {
        match self {
            BigNat::Small(v) => {
                if *v == 0 {
                    None
                } else {
                    Some(BigNat::Small(*v - 1))
                }
            }
            BigNat::Big(limbs) => {
                let mut new_limbs: Vec<u64> = Vec::new();
                let mut k = 0usize;
                while k < limbs.len() {
                    new_limbs.push(limbs[k]);
                    k += 1;
                }
                let mut borrow = 1u64;
                let mut i = 0usize;
                while i < new_limbs.len() {
                    let (new_val, did_borrow) = new_limbs[i].overflowing_sub(borrow);
                    new_limbs[i] = new_val;
                    borrow = if did_borrow { 1 } else { 0 };
                    if borrow == 0 {
                        break;
                    }
                    i += 1;
                }
                while new_limbs.len() > 1 {
                    let last = new_limbs[new_limbs.len() - 1];
                    if last == 0 {
                        new_limbs.pop();
                    } else {
                        break;
                    }
                }
                if new_limbs.len() == 1 {
                    Some(BigNat::Small(new_limbs[0]))
                } else {
                    Some(BigNat::Big(new_limbs))
                }
            }
        }
    }

    // ── [B-u128] mul/pow: transcribed VERBATIM. The shared reduce_nat engine
    // reaches these helpers directly; the arithmetic, defeq, and mul/pow roots
    // exercise them through native == JIT comparisons. ──
    pub fn mul_big_capped(&self, other: &BigNat, max_limbs: usize) -> Option<BigNat> {
        if self.is_zero() || other.is_zero() {
            return Some(BigNat::Small(0));
        }
        let a = self.limbs();
        let b = other.limbs();
        let result_len = a.len() + b.len();
        if result_len > max_limbs {
            return None;
        }
        let mut result: Vec<u64> = Vec::new();
        let mut z = 0usize;
        while z < result_len {
            result.push(0);
            z += 1;
        }
        let mut i = 0usize;
        while i < a.len() {
            let mut carry = 0u128;
            let mut j = 0usize;
            while j < b.len() {
                let prod = (a[i] as u128) * (b[j] as u128) + (result[i + j] as u128) + carry;
                result[i + j] = prod as u64;
                carry = prod >> 64;
                j += 1;
            }
            if carry > 0 {
                result[i + b.len()] = result[i + b.len()] + (carry as u64);
            }
            i += 1;
        }
        Some(BigNat::from_limbs(result))
    }
    pub fn checked_mul_big(&self, other: &BigNat) -> Option<BigNat> {
        self.mul_big_capped(other, 16)
    }
    pub fn checked_pow_big(&self, exp: &BigNat) -> Option<BigNat> {
        if exp.is_zero() {
            return Some(BigNat::Small(1));
        }
        if self.is_zero() {
            return Some(BigNat::Small(0));
        }
        let one = BigNat::Small(1);
        if self.eq_big(&one) {
            return Some(BigNat::Small(1));
        }
        let exp_u64 = match exp.to_u64() {
            Some(v) => v,
            None => return None,
        };
        let exp_u32 = match u32::try_from(exp_u64) {
            Ok(v) => v,
            Err(_) => return None,
        };
        if exp_u32 > 1023u32 {
            return None;
        }
        let mut result = BigNat::Small(1);
        let mut base = self.clone();
        let mut e: u32 = exp_u32;
        while e > 0u32 {
            if (e & 1u32) == 1u32 {
                result = match result.checked_mul_big(&base) {
                    Some(v) => v,
                    None => return None,
                };
            }
            e = e >> 1u32;
            if e > 0u32 {
                base = match base.checked_mul_big(&base) {
                    Some(v) => v,
                    None => return None,
                };
            }
        }
        Some(result)
    }

    fn hash_mix(&self) -> u64 {
        match self {
            BigNat::Small(v) => wmul(*v ^ 0x9e3779b97f4a7c15, 0x100000001b3),
            BigNat::Big(l) => {
                let mut acc = 0x1000_0000_0000_0000u64;
                let mut i = 0usize;
                while i < l.len() {
                    acc = wmul(acc ^ l[i], 0x100000001b3);
                    i += 1;
                }
                acc
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Literal — [B-lit]: Nat only.
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone)]
pub enum Literal {
    Nat(BigNat),
}
pub fn lit_eq(a: &Literal, b: &Literal) -> bool {
    match (a, b) {
        (Literal::Nat(x), Literal::Nat(y)) => x.eq_big(y),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Reducibility — env/reducibility (compare(): Reducible > Regular(h) >
// Irreducible > Opaque; taller Regular first). def_eq/delta.rs uses .compare().
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Reducibility {
    Reducible,
    Regular(u32),
    Irreducible,
    Opaque,
}
impl Reducibility {
    // Returns Ordering as i32: -1 Less, 0 Equal, 1 Greater (higher = unfold first).
    pub fn rank(&self) -> u32 {
        match self {
            Reducibility::Reducible => 3,
            Reducibility::Regular(_) => 2,
            Reducibility::Irreducible => 1,
            Reducibility::Opaque => 0,
        }
    }
    pub fn compare(&self, other: &Reducibility) -> i32 {
        let ra = self.rank();
        let rb = other.rank();
        if ra != rb {
            if ra < rb {
                return -1;
            } else {
                return 1;
            }
        }
        // same rank: Regular compares by height (taller first => "greater").
        match (self, other) {
            (Reducibility::Regular(ha), Reducibility::Regular(hb)) => {
                if ha < hb {
                    -1
                } else if ha > hb {
                    1
                } else {
                    0
                }
            }
            _ => 0,
        }
    }
    pub fn is_regular(&self) -> bool {
        match self {
            Reducibility::Regular(_) => true,
            _ => false,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Expr / ExprKind / ExprMeta — [B-levels] Sort(u32), Const(Name).
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy)]
pub struct ExprMeta {
    pub has_fvar: bool,
    pub hash: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FVarId(pub u64);

#[derive(Clone)]
pub enum ExprKind {
    BVar(u32),
    FVar(FVarId),
    Sort(u32),
    Const(Name),
    App(Arc<Expr>, Arc<Expr>),
    Lam(Arc<Expr>, Arc<Expr>),
    Pi(Arc<Expr>, Arc<Expr>),
    Let(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    Lit(Literal),
    Proj(Name, u32, Arc<Expr>),
    MData(Arc<Expr>),
}

#[derive(Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub meta: ExprMeta,
}

fn mix2(a: u64, b: u64) -> u64 {
    wmul(a ^ b, 0x100000001b3)
}

impl ExprKind {
    pub fn compute_meta(&self) -> ExprMeta {
        match self {
            ExprKind::BVar(i) => ExprMeta {
                has_fvar: false,
                hash: mix2(1, *i as u64),
            },
            ExprKind::FVar(id) => ExprMeta {
                has_fvar: true,
                hash: mix2(2, id.0),
            },
            ExprKind::Sort(d) => ExprMeta {
                has_fvar: false,
                hash: mix2(3, *d as u64),
            },
            ExprKind::Const(n) => ExprMeta {
                has_fvar: false,
                hash: mix2(4, n.h),
            },
            ExprKind::App(f, a) => ExprMeta {
                has_fvar: f.meta.has_fvar || a.meta.has_fvar,
                hash: mix2(5, mix2(f.meta.hash, a.meta.hash)),
            },
            ExprKind::Lam(t, b) => ExprMeta {
                has_fvar: t.meta.has_fvar || b.meta.has_fvar,
                hash: mix2(6, mix2(t.meta.hash, b.meta.hash)),
            },
            ExprKind::Pi(t, b) => ExprMeta {
                has_fvar: t.meta.has_fvar || b.meta.has_fvar,
                hash: mix2(7, mix2(t.meta.hash, b.meta.hash)),
            },
            ExprKind::Let(t, v, b) => ExprMeta {
                has_fvar: t.meta.has_fvar || v.meta.has_fvar || b.meta.has_fvar,
                hash: mix2(8, mix2(t.meta.hash, mix2(v.meta.hash, b.meta.hash))),
            },
            ExprKind::Lit(l) => match l {
                Literal::Nat(bn) => ExprMeta {
                    has_fvar: false,
                    hash: mix2(9, bn.hash_mix()),
                },
            },
            ExprKind::Proj(n, i, e) => ExprMeta {
                has_fvar: e.meta.has_fvar,
                hash: mix2(10, mix2(n.h, mix2(*i as u64, e.meta.hash))),
            },
            ExprKind::MData(e) => ExprMeta {
                has_fvar: e.meta.has_fvar,
                hash: mix2(11, e.meta.hash),
            },
        }
    }
}

impl Expr {
    pub fn from_kind(kind: ExprKind) -> Expr {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    pub fn has_fvar_quick(&self) -> bool {
        self.meta.has_fvar
    }
    pub fn cnst(name: Name) -> Expr {
        Expr::from_kind(ExprKind::Const(name))
    }
    pub fn app(f: Expr, a: Expr) -> Expr {
        Expr::from_kind(ExprKind::App(Arc::new(f), Arc::new(a)))
    }
    pub fn sort(d: u32) -> Expr {
        Expr::from_kind(ExprKind::Sort(d))
    }
    pub fn fvar(id: u64) -> Expr {
        Expr::from_kind(ExprKind::FVar(FVarId(id)))
    }
    pub fn bvar(i: u32) -> Expr {
        Expr::from_kind(ExprKind::BVar(i))
    }
    pub fn lam(ty: Expr, body: Expr) -> Expr {
        Expr::from_kind(ExprKind::Lam(Arc::new(ty), Arc::new(body)))
    }
    pub fn lit_nat_small(v: u64) -> Expr {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(v))))
    }
    // production Expr::bignat_lit — construct a Nat literal from a BigNat.
    pub fn bignat_lit(v: BigNat) -> Expr {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(v)))
    }
    pub fn mdata(inner: Expr) -> Expr {
        Expr::from_kind(ExprKind::MData(Arc::new(inner)))
    }

    // get_app_fn — walk the App spine to the head.
    pub fn get_app_fn(&self) -> &Expr {
        let mut cur = self;
        loop {
            match &cur.kind {
                ExprKind::App(f, _) => cur = f,
                _ => return cur,
            }
        }
    }
    // get_app_num_args — count App layers.
    pub fn get_app_num_args(&self) -> usize {
        let mut n = 0usize;
        let mut cur = self;
        loop {
            match &cur.kind {
                ExprKind::App(f, _) => {
                    n += 1;
                    cur = f;
                }
                _ => return n,
            }
        }
    }

    // instantiate — beta-substitution of BVar(0) with `val` (no free BVars in
    // our lambda bodies beyond the bound one, so a shallow substitution at
    // depth 0 suffices for the beta scenarios). [B-inst]
    pub fn instantiate(&self, val: &Expr) -> Expr {
        self.inst_at(val, 0)
    }
    fn inst_at(&self, val: &Expr, depth: u32) -> Expr {
        match &self.kind {
            ExprKind::BVar(i) => {
                if *i == depth {
                    val.clone()
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::from_kind(ExprKind::App(
                Arc::new(f.inst_at(val, depth)),
                Arc::new(a.inst_at(val, depth)),
            )),
            ExprKind::Lam(t, b) => Expr::from_kind(ExprKind::Lam(
                Arc::new(t.inst_at(val, depth)),
                Arc::new(b.inst_at(val, depth + 1)),
            )),
            ExprKind::Pi(t, b) => Expr::from_kind(ExprKind::Pi(
                Arc::new(t.inst_at(val, depth)),
                Arc::new(b.inst_at(val, depth + 1)),
            )),
            ExprKind::Let(t, v, b) => Expr::from_kind(ExprKind::Let(
                Arc::new(t.inst_at(val, depth)),
                Arc::new(v.inst_at(val, depth)),
                Arc::new(b.inst_at(val, depth + 1)),
            )),
            ExprKind::Proj(n, i, e) => {
                Expr::from_kind(ExprKind::Proj(*n, *i, Arc::new(e.inst_at(val, depth))))
            }
            ExprKind::MData(e) => Expr::from_kind(ExprKind::MData(Arc::new(e.inst_at(val, depth)))),
            _ => self.clone(),
        }
    }
}

// expr_syntactic_eq — production Expr::PartialEq (structural, sees every kind).
pub fn expr_syntactic_eq(a: &Expr, b: &Expr) -> bool {
    match (&a.kind, &b.kind) {
        (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
        (ExprKind::FVar(x), ExprKind::FVar(y)) => x.0 == y.0,
        (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => name_eq(x, y),
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            expr_syntactic_eq(f1, f2) && expr_syntactic_eq(a1, a2)
        }
        (ExprKind::Lam(t1, b1), ExprKind::Lam(t2, b2)) => {
            expr_syntactic_eq(t1, t2) && expr_syntactic_eq(b1, b2)
        }
        (ExprKind::Pi(t1, b1), ExprKind::Pi(t2, b2)) => {
            expr_syntactic_eq(t1, t2) && expr_syntactic_eq(b1, b2)
        }
        (ExprKind::Let(t1, v1, b1), ExprKind::Let(t2, v2, b2)) => {
            expr_syntactic_eq(t1, t2) && expr_syntactic_eq(v1, v2) && expr_syntactic_eq(b1, b2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => lit_eq(l1, l2),
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            name_eq(n1, n2) && i1 == i2 && expr_syntactic_eq(e1, e2)
        }
        (ExprKind::MData(e1), ExprKind::MData(e2)) => expr_syntactic_eq(e1, e2),
        _ => false,
    }
}

// Constructors for succ / app-of-nat-op used by the scenarios and roots.
pub fn succ_of(e: Expr) -> Expr {
    Expr::app(Expr::cnst(nat_succ_name()), e)
}
pub fn pred_of(e: Expr) -> Expr {
    Expr::app(Expr::cnst(nat_pred_name()), e)
}
pub fn binop(op: Name, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::cnst(op), a), b)
}

// ════════════════════════════════════════════════════════════════════════════
// The Verifier + the reducer + the def_eq engine.
// ════════════════════════════════════════════════════════════════════════════
pub struct Verifier {
    pub blind_nat: bool,
    pub blind_offset: bool,
}

impl Verifier {
    // ── env model [B-name/B-env]: an in-fn match on name identity (the
    // slice-scan collapsed). Nat/Bool ctors + arith heads are AXIOMS
    // (bodyless — Some only for the delta test def `dfn := foo`). Reducibility
    // is Regular(0) for the def, Irreducible/axiom-like for ctors (no body). ──
    fn unfold_definition_model(&self, name: &Name) -> Option<Expr> {
        if name_eq(name, &nm_dfn()) {
            // dfn : _ := foo   (the delta-unfold witness)
            return Some(Expr::cnst(nm_foo()));
        }
        None
    }
    fn get_reducibility(&self, name: &Name) -> Reducibility {
        if name_eq(name, &nm_dfn()) {
            Reducibility::Regular(1)
        } else {
            // Nat/Bool ctors, arith heads, foo/bar/g: no body => not delta.
            Reducibility::Irreducible
        }
    }

    // ── the registry-empty hooks (unchanged from R6..R12): reduce_native and
    // try_monad_reduce stay None (env registers no @[extern]/@[implemented_by]
    // reducers and no monad-class heads appear). eager_reduce false (B4). ──
    fn reduce_native(&self, _e: &Expr) -> Option<Expr> {
        None
    }
    fn try_monad_reduce(&self, _e: &Expr) -> Option<Expr> {
        None
    }
    fn eager_reduce(&self) -> bool {
        false
    }

    // ── tc/reduction/nat.rs:20-26 is_nat_zero_expr — VERBATIM. ──
    pub fn is_nat_zero_expr(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Lit(Literal::Nat(n)) => match n {
                BigNat::Small(0) => true,
                _ => false,
            },
            ExprKind::Const(name) => name_eq(name, &nat_zero_name()),
            _ => false,
        }
    }

    // ── tc/reduction/nat.rs:35-51 is_nat_succ_expr — VERBATIM (pred()? is the
    // n>0 guard). ──
    pub fn is_nat_succ_expr(e: &Expr) -> Option<Expr> {
        match &e.kind {
            ExprKind::Lit(Literal::Nat(n)) => {
                let pred = n.pred()?;
                Some(Expr::from_kind(ExprKind::Lit(Literal::Nat(pred))))
            }
            ExprKind::App(f, arg) => {
                if let ExprKind::Const(name) = &f.kind {
                    if name_eq(name, &nat_succ_name()) {
                        return Some(arg.as_ref().clone());
                    }
                }
                None
            }
            _ => None,
        }
    }

    // ── tc/reduction/nat.rs:60-69 is_def_eq_offset — VERBATIM. The
    // succ^k(base) tower peels layer-by-layer; both-zero -> Some(true); both
    // succ -> recurse the FULL def_eq on the predecessors. blind_offset gates. ──
    pub fn is_def_eq_offset(&self, t: &Expr, s: &Expr) -> Option<bool> {
        if self.blind_offset {
            return None;
        }
        if Self::is_nat_zero_expr(t) && Self::is_nat_zero_expr(s) {
            return Some(true);
        }
        let pred_t = Self::is_nat_succ_expr(t);
        let pred_s = Self::is_nat_succ_expr(s);
        match (pred_t, pred_s) {
            (Some(pt), Some(ps)) => Some(self.is_def_eq_impl(&pt, &ps)),
            _ => None,
        }
    }

    // ── tc/reduction/nat.rs:231-278 get_nat_bignat_whnf — VERBATIM iterative
    // succ-peeling: peel syntactic Nat.succ/literal-successor layers WITHOUT
    // re-entering whnf, accumulate the count, then add to the whnf'd base. ──
    fn get_nat_bignat_whnf(&self, e: &Expr) -> Option<BigNat> {
        let mut succs = BigNat::Small(0);
        let mut cur = e.clone();
        loop {
            // peel syntactic Nat.succ app layers iteratively.
            match &cur.kind {
                ExprKind::App(f, arg) => {
                    if let ExprKind::Const(name) = &f.kind {
                        if name_eq(name, &nat_succ_name()) {
                            let one = BigNat::Small(1);
                            succs = succs.checked_add_big(&one);
                            let next = arg.as_ref().clone();
                            cur = next;
                            continue;
                        }
                    }
                }
                _ => {}
            }
            // head is not a syntactic succ-app: WHNF once.
            let cur_whnf = self.whnf_impl(&cur);
            match &cur_whnf.kind {
                ExprKind::Lit(Literal::Nat(n)) => {
                    return Some(succs.checked_add_big(n));
                }
                ExprKind::Const(name) => {
                    if name_eq(name, &nat_zero_name()) {
                        return Some(succs);
                    }
                    return None;
                }
                ExprKind::App(f, _) => {
                    if let ExprKind::Const(name) = &f.kind {
                        if name_eq(name, &nat_succ_name()) {
                            cur = cur_whnf;
                            continue;
                        }
                    }
                    return None;
                }
                _ => return None,
            }
        }
    }

    // ── tc/reduction/nat.rs:77-202 reduce_nat. The closure argument to
    // reduce_bin_bignat_op is inlined per op [B9]. ──
    pub fn reduce_nat(&self, e: &Expr) -> Option<Expr> {
        if self.blind_nat {
            return None; // THE BLIND CONTROL (single-line divergence).
        }
        let nargs = e.get_app_num_args();
        if nargs == 1 {
            if let ExprKind::App(f, arg) = &e.kind {
                if let ExprKind::Const(name) = &f.kind {
                    if name_eq(name, &nat_succ_name()) {
                        if let Some(v) = self.get_nat_bignat_whnf(arg) {
                            let one = BigNat::Small(1);
                            return Some(Expr::bignat_lit(v.checked_add_big(&one)));
                        }
                    }
                    if name_eq(name, &nat_pred_name()) {
                        if let Some(v) = self.get_nat_bignat_whnf(arg) {
                            let p = match v.pred() {
                                Some(x) => x,
                                None => BigNat::Small(0),
                            };
                            return Some(Expr::bignat_lit(p));
                        }
                    }
                }
            }
        } else if nargs == 2 {
            if let ExprKind::App(f_a1, a2) = &e.kind {
                if let ExprKind::App(f, a1) = &f_a1.kind {
                    if let ExprKind::Const(name) = &f.kind {
                        if name_eq(name, &nat_add_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.checked_add_big(&v2)));
                        }
                        if name_eq(name, &nat_sub_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.saturating_sub_big(&v2)));
                        }
                        if name_eq(name, &nat_mul_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return match v1.checked_mul_big(&v2) {
                                Some(value) => Some(Expr::bignat_lit(value)),
                                None => None,
                            };
                        }
                        if name_eq(name, &nat_div_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.checked_div_big(&v2)));
                        }
                        if name_eq(name, &nat_mod_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.checked_mod_big(&v2)));
                        }
                        if name_eq(name, &nat_gcd_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.gcd_big(&v2)));
                        }
                        if name_eq(name, &nat_pow_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return match v1.checked_pow_big(&v2) {
                                Some(value) => Some(Expr::bignat_lit(value)),
                                None => None,
                            };
                        }
                        if name_eq(name, &nat_beq_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(self.bool_lit(v1.eq_big(&v2)));
                        }
                        if name_eq(name, &nat_ble_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(self.bool_lit(v1.le_big(&v2)));
                        }
                        if name_eq(name, &nat_land_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.bitand_big(&v2)));
                        }
                        if name_eq(name, &nat_lor_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.bitor_big(&v2)));
                        }
                        if name_eq(name, &nat_xor_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            return Some(Expr::bignat_lit(v1.bitxor_big(&v2)));
                        }
                        if name_eq(name, &nat_shl_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            if v1.is_zero() {
                                return Some(Expr::bignat_lit(BigNat::Small(0)));
                            }
                            let shift = v2.to_u64()?;
                            if shift > 1024 {
                                return None;
                            }
                            let result = v1.checked_shl_big(shift as usize);
                            if result.limbs().len() > 16 {
                                return None;
                            }
                            return Some(Expr::bignat_lit(result));
                        }
                        if name_eq(name, &nat_shr_name()) {
                            let v1 = self.get_nat_bignat_whnf(a1)?;
                            let v2 = self.get_nat_bignat_whnf(a2)?;
                            let shift = v2.to_u64()?;
                            if shift > (u64::MAX / 2) {
                                return Some(Expr::bignat_lit(BigNat::Small(0)));
                            }
                            return Some(Expr::bignat_lit(v1.shr_big(shift as usize)));
                        }
                    }
                }
            }
        }
        None
    }

    // Compatibility entry retained for the historical focused root. It now
    // delegates to the same engine hook, preventing the coverage fixture from
    // drifting into a second implementation.
    pub fn reduce_nat_mulpow(&self, e: &Expr) -> Option<Expr> {
        self.reduce_nat(e)
    }

    fn bool_lit(&self, b: bool) -> Expr {
        if b {
            Expr::cnst(bool_true_name())
        } else {
            Expr::cnst(bool_false_name())
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // WHNF — full (with delta). whnf.rs App arm: reduce_nat pre-check (:421)
    // when the spine head is a visible Const; then beta; then the stuck
    // iota/quot/nat/native fallback (:616-626). get_nat_bignat_whnf calls THIS.
    // ════════════════════════════════════════════════════════════════════════
    pub fn whnf_impl(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                // whnf.rs:421 pre-check: head is a visible Const -> reduce_nat(e).
                let f0 = e.get_app_fn();
                if let ExprKind::Const(_) = &f0.kind {
                    if let Some(reduced) = self.reduce_nat(e) {
                        return self.whnf_impl(&reduced);
                    }
                    if let Some(reduced) = self.reduce_native(e) {
                        return self.whnf_impl(&reduced);
                    }
                }
                let f_whnf = self.whnf_impl(f);
                match &f_whnf.kind {
                    ExprKind::Lam(_, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_impl(&reduced)
                    }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        // whnf.rs:612-626 stuck fallback: iota/quot [B8] then nat/native.
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        if let Some(reduced) = self.try_quot_reduction(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        if let Some(reduced) = self.reduce_nat(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        if let Some(reduced) = self.reduce_native(&app) {
                            return self.whnf_impl(&reduced);
                        }
                        app
                    }
                }
            }
            ExprKind::Let(_, val, body) => {
                let reduced = body.instantiate(val);
                self.whnf_impl(&reduced)
            }
            ExprKind::Const(name) => match self.unfold_definition_model(name) {
                Some(val) => self.whnf_impl(&val),
                None => e.clone(),
            },
            // [B-ctx] FVar has no context value -> stuck.
            ExprKind::FVar(_) => e.clone(),
            ExprKind::MData(inner) => self.whnf_impl(inner),
            _ => e.clone(),
        }
    }
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> {
        None // [B8]
    }
    fn try_quot_reduction(&self, _e: &Expr) -> Option<Expr> {
        None // [B8]
    }

    // whnf.rs:341-505 NoDelta core (P1 cheap / P5): beta / zeta / MData, NO
    // Const unfolding; the App pre-check + stuck fallback consult reduce_nat.
    pub fn whnf_core_no_delta(&self, e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f0 = e.get_app_fn();
                if let ExprKind::Const(_) = &f0.kind {
                    if let Some(reduced) = self.reduce_nat(e) {
                        return self.whnf_core_no_delta(&reduced);
                    }
                    if let Some(reduced) = self.reduce_native(e) {
                        return self.whnf_core_no_delta(&reduced);
                    }
                }
                let f_whnf = self.whnf_core_no_delta(f);
                match &f_whnf.kind {
                    ExprKind::Lam(_, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_core_no_delta(&reduced)
                    }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_core_no_delta(&reduced);
                        }
                        if let Some(reduced) = self.try_quot_reduction(&app) {
                            return self.whnf_core_no_delta(&reduced);
                        }
                        if let Some(reduced) = self.reduce_nat(&app) {
                            return self.whnf_core_no_delta(&reduced);
                        }
                        if let Some(reduced) = self.reduce_native(&app) {
                            return self.whnf_core_no_delta(&reduced);
                        }
                        app
                    }
                }
            }
            ExprKind::Let(_, val, body) => {
                let reduced = body.instantiate(val);
                self.whnf_core_no_delta(&reduced)
            }
            // Const is STUCK in NoDelta mode (deferred to lazy delta).
            ExprKind::Const(_) => e.clone(),
            ExprKind::FVar(_) => e.clone(),
            ExprKind::MData(inner) => self.whnf_core_no_delta(inner),
            _ => e.clone(),
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // def_eq — P0 syntactic, quick, P1 no-delta whnf + re-quick, P2 lazy delta
    // (the four hooks), P6 structural congruence. (Proof-irrel / struct-eta /
    // string-lit / unit-like phases are out of scope here — verified R9..R12.)
    // ════════════════════════════════════════════════════════════════════════
    pub fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool {
        self.is_def_eq_impl(a, b)
    }
    pub fn is_def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        // mod.rs:218 P0.
        if expr_syntactic_eq(a, b) {
            return true;
        }
        self.is_def_eq_core(a, b)
    }
    fn is_def_eq_core(&self, a: &Expr, b: &Expr) -> bool {
        // quick at entry.
        match self.quick_is_def_eq(a, b) {
            Some(v) => return v,
            None => {}
        }
        // P1 — no-delta cheap whnf both sides.
        let t = self.whnf_core_no_delta(a);
        let s = self.whnf_core_no_delta(b);
        if !expr_syntactic_eq(&t, a) || !expr_syntactic_eq(&s, b) {
            if expr_syntactic_eq(&t, &s) {
                return true;
            }
            match self.quick_is_def_eq(&t, &s) {
                Some(v) => return v,
                None => {}
            }
        }
        // P2 — lazy delta (the Nat/native/monad hooks live at its loop top).
        match self.lazy_delta_reduction(&t, &s) {
            Ok(v) => v,
            Err((t2, s2)) => self.is_def_eq_structural(&t2, &s2),
        }
    }

    // quick_is_def_eq — the reachable arms (Sort/Lit). Clean has no MVar.
    fn quick_is_def_eq(&self, a: &Expr, b: &Expr) -> Option<bool> {
        match (&a.kind, &b.kind) {
            (ExprKind::Sort(x), ExprKind::Sort(y)) => Some(x == y),
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => Some(lit_eq(l1, l2)),
            _ => None,
        }
    }

    // get_delta_const — a delta-reducible head (a Const with a body that is not
    // reducibility-Opaque). Returns (name, reducibility). def_eq/delta.rs.
    fn get_delta_const(&self, e: &Expr) -> Option<(Name, Reducibility)> {
        let head = e.get_app_fn();
        if let ExprKind::Const(name) = &head.kind {
            // #1277 arity: a delta const must have a body.
            if self.unfold_definition_model(name).is_some() {
                let red = self.get_reducibility(name);
                match red {
                    Reducibility::Opaque => None,
                    _ => Some((*name, red)),
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    // try_unfold_const_in_place — unfold the head const of `e` (rebuild spine).
    fn try_unfold_const_in_place(&self, e: &mut Expr, name: &Name) -> bool {
        match self.unfold_definition_model(name) {
            Some(body) => {
                // Rebuild: replace the head const with its body, keeping args.
                *e = self.replace_head(e, &body);
                true
            }
            None => false,
        }
    }
    fn replace_head(&self, e: &Expr, new_head: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let nf = self.replace_head(f, new_head);
                Expr::from_kind(ExprKind::App(Arc::new(nf), a.clone()))
            }
            ExprKind::Const(_) => new_head.clone(),
            _ => e.clone(),
        }
    }

    // ── def_eq/delta.rs:57-168 lazy_delta_reduction — the four loop-top hooks
    // in production order, then a delta step. ──
    pub fn lazy_delta_reduction(&self, a: &Expr, b: &Expr) -> Result<bool, (Expr, Expr)> {
        let max_iters: u32 = 10_000;
        let mut t = a.clone();
        let mut s = b.clone();
        let mut iterations = 0u32;
        loop {
            iterations += 1;
            if iterations > max_iters {
                return Ok(false); // #1773 conservative.
            }
            // 1. is_def_eq_offset (succ peeling).
            if let Some(result) = self.is_def_eq_offset(&t, &s) {
                return Ok(result);
            }
            // 2. reduce_nat under the fvar guard (or eager_reduce).
            if (!t.has_fvar_quick() && !s.has_fvar_quick()) || self.eager_reduce() {
                if let Some(t_v) = self.reduce_nat(&t) {
                    return Ok(self.is_def_eq_impl(&t_v, &s));
                }
                if let Some(s_v) = self.reduce_nat(&s) {
                    return Ok(self.is_def_eq_impl(&t, &s_v));
                }
            }
            // 3. reduce_native (no fvar guard; registry empty).
            if let Some(t_v) = self.reduce_native(&t) {
                return Ok(self.is_def_eq_impl(&t_v, &s));
            }
            if let Some(s_v) = self.reduce_native(&s) {
                return Ok(self.is_def_eq_impl(&t, &s_v));
            }
            // 4. try_monad_reduce with the progress gate (registry empty).
            if let Some(t_v) = self.try_monad_reduce(&t) {
                if !expr_syntactic_eq(&t_v, &t) {
                    return Ok(self.is_def_eq_impl(&t_v, &s));
                }
            }
            if let Some(s_v) = self.try_monad_reduce(&s) {
                if !expr_syntactic_eq(&s_v, &s) {
                    return Ok(self.is_def_eq_impl(&t, &s_v));
                }
            }
            // delta step.
            match self.lazy_delta_step(&mut t, &mut s) {
                LdStatus::Continue => {}
                LdStatus::DefEqual => return Ok(true),
                LdStatus::DefUnknown => return Err((t, s)),
                LdStatus::DefDiff => return Ok(false),
            }
        }
    }

    fn lazy_delta_step(&self, t: &mut Expr, s: &mut Expr) -> LdStatus {
        let dt = self.get_delta_const(t);
        let ds = self.get_delta_const(s);
        let status = match (dt, ds) {
            (Some((tn, tr)), Some((sn, sr))) => {
                let ord = tr.compare(&sr);
                if ord < 0 {
                    if self.try_unfold_const_in_place(t, &tn)
                        || self.try_unfold_const_in_place(s, &sn)
                    {
                        LdStatus::Continue
                    } else {
                        LdStatus::DefUnknown
                    }
                } else if ord > 0 {
                    if self.try_unfold_const_in_place(s, &sn)
                        || self.try_unfold_const_in_place(t, &tn)
                    {
                        LdStatus::Continue
                    } else {
                        LdStatus::DefUnknown
                    }
                } else {
                    // equal reducibility.
                    if name_eq(&tn, &sn) && tr.is_regular() {
                        if self.is_def_eq_args_only(t, s) {
                            return LdStatus::DefEqual;
                        }
                    }
                    let tc = self.try_unfold_const_in_place(t, &tn);
                    let sc = self.try_unfold_const_in_place(s, &sn);
                    if tc || sc {
                        LdStatus::Continue
                    } else {
                        LdStatus::DefUnknown
                    }
                }
            }
            (Some((tn, _tr)), None) => {
                if self.try_unfold_const_in_place(t, &tn) {
                    LdStatus::Continue
                } else {
                    LdStatus::DefUnknown
                }
            }
            (None, Some((sn, _sr))) => {
                if self.try_unfold_const_in_place(s, &sn) {
                    LdStatus::Continue
                } else {
                    LdStatus::DefUnknown
                }
            }
            (None, None) => LdStatus::DefUnknown,
        };
        match status {
            LdStatus::Continue => self.finish_delta_step(t, s),
            _ => status,
        }
    }
    fn finish_delta_step(&self, t: &Expr, s: &Expr) -> LdStatus {
        if expr_syntactic_eq(t, s) {
            return LdStatus::DefEqual;
        }
        match self.quick_is_def_eq(t, s) {
            Some(true) => LdStatus::DefEqual,
            Some(false) => LdStatus::DefDiff,
            None => LdStatus::Continue,
        }
    }

    // is_def_eq_args_only — same-head spine argument comparison.
    fn is_def_eq_args_only(&self, t: &Expr, s: &Expr) -> bool {
        match (&t.kind, &s.kind) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.is_def_eq_args_only(f1, f2) && self.is_def_eq_impl(a1, a2)
            }
            (ExprKind::Const(_), ExprKind::Const(_)) => true, // heads already matched by name
            _ => expr_syntactic_eq(t, s),
        }
    }

    // P6 structural congruence — App spine / binders / atoms.
    fn is_def_eq_structural(&self, a: &Expr, b: &Expr) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.is_def_eq_impl(f1, f2) && self.is_def_eq_impl(a1, a2)
            }
            (ExprKind::Lam(t1, b1), ExprKind::Lam(t2, b2)) => {
                self.is_def_eq_impl(t1, t2) && self.is_def_eq_impl(b1, b2)
            }
            (ExprKind::Pi(t1, b1), ExprKind::Pi(t2, b2)) => {
                self.is_def_eq_impl(t1, t2) && self.is_def_eq_impl(b1, b2)
            }
            (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
            (ExprKind::Const(x), ExprKind::Const(y)) => name_eq(x, y),
            (ExprKind::FVar(x), ExprKind::FVar(y)) => x.0 == y.0,
            (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => lit_eq(l1, l2),
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                name_eq(n1, n2) && i1 == i2 && self.is_def_eq_impl(e1, e2)
            }
            (ExprKind::MData(e1), _) => self.is_def_eq_impl(e1, b),
            (_, ExprKind::MData(e2)) => self.is_def_eq_impl(a, e2),
            _ => false,
        }
    }
}

enum LdStatus {
    Continue,
    DefEqual,
    DefUnknown,
    DefDiff,
}

// ════════════════════════════════════════════════════════════════════════════
// ROOTS — mono #[cfg_attr(not(test), no_mangle)] entry points (standalone re-emit).
// ════════════════════════════════════════════════════════════════════════════

// Result of a reduce_nat call, extracted to scalars for the oracle + shape.
//   kind: 0 = Nat literal, 1 = Bool.true, 2 = Bool.false, 3 = other/stuck/none.
#[repr(C)]
pub struct ArithResult {
    pub reduced: u64, // 1 if reduce_nat returned Some, else 0
    pub kind: u64,
    pub lo: u64,
    pub hi: u64,
    pub nlimbs: u64,
    pub hash: u64, // the reduced Expr's ExprMeta.hash (compute_meta, native==JIT).
}

fn bignat_from_pair(lo: u64, hi: u64) -> BigNat {
    if hi == 0 {
        BigNat::Small(lo)
    } else {
        let mut v: Vec<u64> = Vec::new();
        v.push(lo);
        v.push(hi);
        BigNat::Big(v)
    }
}

fn op_name(op: u64) -> Name {
    if op == 0 {
        nat_add_name()
    } else if op == 1 {
        nat_sub_name()
    } else if op == 2 {
        nat_mul_name()
    } else if op == 3 {
        nat_div_name()
    } else if op == 4 {
        nat_mod_name()
    } else if op == 5 {
        nat_gcd_name()
    } else if op == 6 {
        nat_pow_name()
    } else if op == 7 {
        nat_beq_name()
    } else if op == 8 {
        nat_ble_name()
    } else if op == 9 {
        nat_land_name()
    } else if op == 10 {
        nat_lor_name()
    } else if op == 11 {
        nat_xor_name()
    } else if op == 12 {
        nat_shl_name()
    } else if op == 13 {
        nat_shr_name()
    } else if op == 14 {
        nat_succ_name()
    } else {
        nat_pred_name()
    } // 15
}

fn classify(e: &Expr, out: &mut ArithResult) {
    out.hash = e.meta.hash;
    match &e.kind {
        ExprKind::Lit(Literal::Nat(bn)) => {
            let l = bn.limbs();
            out.kind = 0;
            out.lo = l[0];
            out.hi = if l.len() > 1 { l[1] } else { 0 };
            out.nlimbs = l.len() as u64;
        }
        ExprKind::Const(n) => {
            if name_eq(n, &bool_true_name()) {
                out.kind = 1;
            } else if name_eq(n, &bool_false_name()) {
                out.kind = 2;
            } else {
                out.kind = 3;
            }
        }
        _ => {
            out.kind = 3;
        }
    }
}

// Build the arith term for (op, a, b) and run the ENGINE reduce_nat (u64-safe).
#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn nat_arith_root(
    out: *mut ArithResult,
    op: u64,
    a_lo: u64,
    a_hi: u64,
    b_lo: u64,
    b_hi: u64,
) {
    let v = Verifier {
        blind_nat: false,
        blind_offset: false,
    };
    let a = Expr::bignat_lit(bignat_from_pair(a_lo, a_hi));
    let term = if op >= 14 {
        Expr::app(Expr::cnst(op_name(op)), a)
    } else {
        let b = Expr::bignat_lit(bignat_from_pair(b_lo, b_hi));
        binop(op_name(op), a, b)
    };
    let mut res = ArithResult {
        reduced: 0,
        kind: 3,
        lo: 0,
        hi: 0,
        nlimbs: 0,
        hash: 0,
    };
    match v.reduce_nat(&term) {
        Some(r) => {
            res.reduced = 1;
            classify(&r, &mut res);
        }
        None => {
            res.reduced = 0;
        }
    }
    unsafe {
        *out = res;
    }
}

// Focused mul/pow root. It reaches the same engine `reduce_nat` implementation
// used by whnf/def-eq, so native and JIT coverage cannot pass through a private
// compatibility reducer.
#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn nat_mulpow_root(
    out: *mut ArithResult,
    op: u64,
    a_lo: u64,
    a_hi: u64,
    b_lo: u64,
    b_hi: u64,
) {
    let v = Verifier {
        blind_nat: false,
        blind_offset: false,
    };
    let a = Expr::bignat_lit(bignat_from_pair(a_lo, a_hi));
    let b = Expr::bignat_lit(bignat_from_pair(b_lo, b_hi));
    let term = binop(op_name(op), a, b);
    let mut res = ArithResult {
        reduced: 0,
        kind: 3,
        lo: 0,
        hi: 0,
        nlimbs: 0,
        hash: 0,
    };
    match v.reduce_nat(&term) {
        Some(r) => {
            res.reduced = 1;
            classify(&r, &mut res);
        }
        None => {
            res.reduced = 0;
        }
    }
    unsafe {
        *out = res;
    }
}

// def_eq scenario dispatcher. idx encodes: low byte = scenario id; bit 8 =
// blind_nat; bit 9 = blind_offset. Returns 1 (accept) / 0 (reject).
#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn nat_defeq_root(idx: u64) -> u64 {
    let scenario = idx & 0xff;
    let blind_nat = (idx & 0x100) != 0;
    let blind_offset = (idx & 0x200) != 0;
    let v = Verifier {
        blind_nat,
        blind_offset,
    };
    let (a, b) = build_defeq_scenario(scenario);
    if v.is_def_eq(&a, &b) { 1 } else { 0 }
}

// The scenario term pairs.
fn build_defeq_scenario(scenario: u64) -> (Expr, Expr) {
    // Nat.zero as a Const (so is_nat_zero_expr's Const arm participates).
    let zero_c = Expr::cnst(nat_zero_name());
    if scenario == 0 {
        // (a) 2 + 2 =?= 4  — ACCEPT requires reduce_nat.
        (
            binop(
                nat_add_name(),
                Expr::lit_nat_small(2),
                Expr::lit_nat_small(2),
            ),
            Expr::lit_nat_small(4),
        )
    } else if scenario == 1 {
        // (b) 2 + 2 =?= 5  — REJECT (folds to 4, 4 != 5). RIGHT answer.
        (
            binop(
                nat_add_name(),
                Expr::lit_nat_small(2),
                Expr::lit_nat_small(2),
            ),
            Expr::lit_nat_small(5),
        )
    } else if scenario == 2 {
        // (c1) succ(succ(succ(zero))) =?= 3 — offset peeling (blind mode) OR
        //      reduce_nat (aware). App-succ-tower-vs-literal: structural
        //      congruence CANNOT accept (kind mismatch), so an accept in
        //      blind_nat mode is UNIQUELY is_def_eq_offset.
        (
            succ_of(succ_of(succ_of(zero_c.clone()))),
            Expr::lit_nat_small(3),
        )
    } else if scenario == 3 {
        // (c2) succ(succ(n)) =?= 2 — variable-base tower; offset peels twice
        //      then gets stuck at n =?= 0 -> REJECT (correct: succ(succ n) != 2).
        (succ_of(succ_of(Expr::fvar(700))), Expr::lit_nat_small(2))
    } else if scenario == 4 {
        // (d) (2^63) + (2^63) =?= 2^64  — add crossing the Small->Big boundary.
        let two63 = 1u64 << 63;
        let big2p64 = Expr::bignat_lit(bignat_from_pair(0, 1)); // Big([0,1]) = 2^64
        (
            binop(
                nat_add_name(),
                Expr::lit_nat_small(two63),
                Expr::lit_nat_small(two63),
            ),
            big2p64,
        )
    } else if scenario == 5 {
        // (d') (2^64) + (2^64) =?= 2^65  — Big + Big -> Big([0,2]).
        let big2p64 = Expr::bignat_lit(bignat_from_pair(0, 1));
        let big2p65 = Expr::bignat_lit(bignat_from_pair(0, 2));
        (binop(nat_add_name(), big2p64.clone(), big2p64), big2p65)
    } else if scenario == 6 {
        // (e) 10 - 3 =?= 7.
        (
            binop(
                nat_sub_name(),
                Expr::lit_nat_small(10),
                Expr::lit_nat_small(3),
            ),
            Expr::lit_nat_small(7),
        )
    } else if scenario == 7 {
        // wrong-answer control witness: 10 - 3 =?= 8 -> REJECT.
        (
            binop(
                nat_sub_name(),
                Expr::lit_nat_small(10),
                Expr::lit_nat_small(3),
            ),
            Expr::lit_nat_small(8),
        )
    } else if scenario == 8 {
        // (f) 7 * 11 =?= 77 — multiplication through the production hook.
        (
            binop(
                nat_mul_name(),
                Expr::lit_nat_small(7),
                Expr::lit_nat_small(11),
            ),
            Expr::lit_nat_small(77),
        )
    } else if scenario == 9 {
        // (g) 3^5 =?= 243 — exponentiation through the production hook.
        (
            binop(
                nat_pow_name(),
                Expr::lit_nat_small(3),
                Expr::lit_nat_small(5),
            ),
            Expr::lit_nat_small(243),
        )
    } else if scenario == 10 {
        // Armed wrong-answer multiplication control.
        (
            binop(
                nat_mul_name(),
                Expr::lit_nat_small(7),
                Expr::lit_nat_small(11),
            ),
            Expr::lit_nat_small(78),
        )
    } else if scenario == 11 {
        // Armed wrong-answer exponentiation control.
        (
            binop(
                nat_pow_name(),
                Expr::lit_nat_small(3),
                Expr::lit_nat_small(5),
            ),
            Expr::lit_nat_small(244),
        )
    }
    // ── NON-NAT inertness set (aware verdict == blind verdict) ──
    else if scenario == 20 {
        // foo =?= foo (Const congruence) -> ACCEPT.
        (Expr::cnst(nm_foo()), Expr::cnst(nm_foo()))
    } else if scenario == 21 {
        // foo =?= bar -> REJECT.
        (Expr::cnst(nm_foo()), Expr::cnst(nm_bar()))
    } else if scenario == 22 {
        // (λx.x) foo =?= foo (beta) -> ACCEPT.
        (
            Expr::app(
                Expr::lam(Expr::sort(0), Expr::bvar(0)),
                Expr::cnst(nm_foo()),
            ),
            Expr::cnst(nm_foo()),
        )
    } else if scenario == 23 {
        // Sort 0 =?= Sort 0 -> ACCEPT.
        (Expr::sort(0), Expr::sort(0))
    } else if scenario == 24 {
        // Sort 0 =?= Sort 1 -> REJECT.
        (Expr::sort(0), Expr::sort(1))
    } else if scenario == 25 {
        // g foo =?= g foo (App congruence) -> ACCEPT.
        (
            Expr::app(Expr::cnst(nm_g()), Expr::cnst(nm_foo())),
            Expr::app(Expr::cnst(nm_g()), Expr::cnst(nm_foo())),
        )
    } else if scenario == 26 {
        // g foo =?= g bar (App congruence, arg differs) -> REJECT.
        (
            Expr::app(Expr::cnst(nm_g()), Expr::cnst(nm_foo())),
            Expr::app(Expr::cnst(nm_g()), Expr::cnst(nm_bar())),
        )
    } else if scenario == 27 {
        // dfn =?= foo (delta unfold: dfn := foo) -> ACCEPT via lazy delta.
        (Expr::cnst(nm_dfn()), Expr::cnst(nm_foo()))
    } else if scenario == 28 {
        // g (2+2) =?= g 4 — reduce_nat UNDER an App congruence (aware ACCEPT,
        // blind REJECT). Shows the hook composes under structural congruence.
        (
            Expr::app(
                Expr::cnst(nm_g()),
                binop(
                    nat_add_name(),
                    Expr::lit_nat_small(2),
                    Expr::lit_nat_small(2),
                ),
            ),
            Expr::app(Expr::cnst(nm_g()), Expr::lit_nat_small(4)),
        )
    } else {
        // default: 0 =?= 0.
        (zero_c.clone(), zero_c)
    }
}
