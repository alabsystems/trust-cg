// SipHasher13-derived portions: Copyright (c) The Rust Project Contributors.
// Licensed under MIT; see third_party/vendor/rust-stdlib-SipHasher13-LICENSE.
// trust-cg-specific transcription rewrites: Copyright 2026 Andrew Yates,
// Apache-2.0.
//
// R7-A — SIPHASH13 DE-MODELING (closes boundary B7: the last meta-hash model).
//
// Rounds 4-6 made `Name.cached_hash` production-exact (the murmur/mix chain),
// but the ExprMeta PAYLOAD hashes (`hash_to_u64` at the Sort/Const/Lit/Proj
// compute_meta arms) still ran through the KaniHasher MODEL (clean's own
// cfg(kani) hasher; declared boundary B7 in every prior slice). Production
// clean-kernel (cfg(not(kani)), expr/meta.rs:367-374) uses
// `std::collections::hash_map::DefaultHasher::new()`, which IS
// `SipHasher13::new_with_keys(0, 0)` (std/src/hash/random.rs:106-108) —
// SipHash-1-3 with both keys fixed to zero: fully deterministic.
//
// THIS SLICE transcribes SipHasher13 VERBATIM from the toolchain std source
// ($HOME/trust/library/core/src/hash/sip.rs — the same library the stage1 rustc
// and the clean-kernel production binary link) and re-runs the payload-hash
// compute_meta arms over it. With this, the whole meta word is
// production-exact end-to-end: content (rounds 4-6) AND hasher (this round).
//
// STD-SOURCE FACTS the transcription rests on (verified in the tree):
//   * DefaultHasher::new() == SipHasher13::new_with_keys(0,0)   [random.rs:106]
//   * DefaultHasher / SipHasher13 override ONLY write / write_str / finish
//     [random.rs:124-143, sip.rs:229-245] — "The underlying `SipHasher13`
//     doesn't override the other `write_*` methods". Every integer write_uN
//     therefore takes the DEFAULT trait body `self.write(&i.to_ne_bytes())`
//     [core/hash/mod.rs:360-431]; to_ne_bytes on aarch64 == little-endian.
//   * write_length_prefix defaults to write_usize [core/hash/mod.rs:483-485].
//   * write_str (SipHasher13 override, sip.rs:302-308) = write(s.as_bytes())
//     then write_u8(0xFF).
//   * Hasher state: k0,k1,length,State{v0,v2,v1,v3},tail,ntail [sip.rs:51-73];
//     reset(): v0=k0^0x736f6d6570736575, v1=k1^0x646f72616e646f6d,
//     v2=k0^0x6c7967656e657261, v3=k1^0x7465646279746573 [sip.rs:200-208].
//   * Sip13Rounds: c_rounds = 1 compress, d_rounds = 3 compresses
//     [sip.rs:360-372]; compress! = the classic SipRound [sip.rs:75-94].
//   * finish(): b = ((length as u64 & 0xff) << 56) | tail; v3^=b; c_rounds;
//     v0^=b; v2^=0xff; d_rounds; v0^v1^v2^v3 [sip.rs:310-325].
//
// PRODUCTION HASH-WRITE SEQUENCES transcribed (what flows into the hasher):
//   * hash_to_u64(name)  — Name::hash (name.rs:461-467): write_u64(cached_hash).
//   * hash_to_u64(lvl)   — Level::hash (level/mod.rs:96-110, cfg(not(kani))):
//     discriminant(self).hash(state) then recursive child hashing.
//     Discriminant<Level> wraps the discriminant_value intrinsic result;
//     default-repr enums have discriminant type isize (rustc_abi
//     ReprOptions::discr_type = IntegerType::Pointer(true)), variant indices
//     in declaration order: Zero=0 Succ=1 Max=2 IMax=3 Param=4. isize::hash =
//     write_isize -> write_usize(i as usize) -> 8 LE bytes  [S3].
//   * hash_to_u64(levels) — <LevelVec as Hash> == <[Level] as Hash>
//     (SmallVec hashes as its slice): write_length_prefix(len) (= write_usize)
//     then per-element Level::hash [core/hash/mod.rs:931-937].
//   * hash_to_u64(lit)   — derive(Hash) on Literal/BigNat: write_usize(discr)
//     (isize discriminant, as above) then payload; u64 payload = write_u64;
//     Vec<u64> payload (BigNat::Big) = write_usize(len) + hash_slice which for
//     integer slices is ONE bulk write of the raw LE bytes
//     [core/hash/mod.rs:806-843] — transcribed as per-limb 8-byte writes [S5];
//     Arc<str> payload (Literal::String) = str::hash = write_str.
//
// TRANSCRIPTION REWRITES (each semantics-preserving, each exercised by the
// differential against the REAL std DefaultHasher over real heap inputs):
//   [S-add]  u64::wrapping_add lowers only as an extern shim leaf (landed
//            convention). To keep the ENTIRE sip permutation in JIT machine
//            code, wrapping adds are computed by 32-bit-half composition in
//            plain never-overflowing u64 ops:
//              lo = (a&0xFFFFFFFF)+(b&0xFFFFFFFF); hi = (a>>32)+(b>>32)+(lo>>32);
//              (hi<<32)|(lo&0xFFFFFFFF)
//            == a.wrapping_add(b) for all inputs (lo<2^33, hi<2^34: the plain
//            + overflow checks are structurally dead; hi<<32 drops the carry
//            exactly as wrapping requires).
//   [S-rotl] u64::rotate_left(N) lowers only as an extern leaf; rewritten
//            (x << n) | (x >> (64 - n)) — identical for the five constant
//            rotations used (13,16,17,21,32; all in 1..=63).
//   [S-min]  cmp::min(length, needed) -> if length < needed {length} else
//            {needed} (core generic min does not lower in-module).
//   [S-load] load_int_le!/u8to64_le use unsafe unaligned LE loads
//            (ptr::copy_nonoverlapping); rewritten as safe byte-indexed LE
//            assembly (the landed murmur convention). debug_assert!s of the
//            std source are cfg(debug)-only and elided.
//   [S2]     write_uN default bodies `self.write(&i.to_ne_bytes())` build the
//            byte array by explicit LE shifts (== to_ne_bytes on aarch64).
//   [S3]     mem::discriminant(..).hash(..) monomorphized by hand: the
//            Discriminant<T>-wrapped isize is written via write_usize
//            (isize::hash -> write_isize -> write_usize default chain), with
//            the variant indices spelled per match arm. Core's generic Hash
//            impls do not lower in-module (probe-verified); byte sequence
//            identical, checked against the REAL std path by the harness.
//   [S5]     BigNat::Big limb hashing: production is write_usize(len) + ONE
//            bulk write of len*8 raw LE bytes; transcribed as write_usize(len)
//            + per-limb write_u64. All preceding writes are 8-byte multiples,
//            so the hasher is block-aligned (ntail==0) when the limbs start
//            and the two forms are bit-identical (same blocks, same length).
//   [S6]     ExprKind is cut to the four payload-hash arms this slice closes
//            (Sort/Const/Lit/Proj) — the other seven arms are hasher-free
//            (pure mix_hash/meta combinators) and verified in rounds 1-6.
//
// MODELED BOUNDARIES that REMAIN (all landed conventions, none of them the
// hasher):
//   [S4]  Name carries only cached_hash here: production Name::hash reads
//         ONLY cached_hash (name.rs:461-467), and the cached_hash CONTENT
//         (murmur/mix construction chain) is verified bit-identical to the
//         real clean-kernel in rounds 4-6. The harness feeds REAL clean-kernel
//         cached_hash goldens in.
//   [B9]  LevelVec = SmallVec<[Level;2]> modeled as Vec<Level> (hashing goes
//         through the identical <[Level] as Hash> sequence); iterator
//         combinators as index loops; vec![..] as new+push.
//   mix_hash's wrapping_mul stays the landed extern shim leaf (faithful host
//   wrapping_mul; the mix_hash CHAIN is golden-verified since round 4).
//   Arc::new / Arc deref INLINED (RUNG 5/6); Arc<str> crossings
//   (from_utf8_unchecked identity, Arc::<str>::from, <Arc<str> as Deref>) and
//   Vec::new/push/u32::min lower to extern decls bound to FAITHFUL host shims
//   (landed). Drops not emitted (leak model).
//
// WHAT REMAINS ON KaniHasher AFTER THIS SLICE (stated for honesty): the
// frozen gate fixtures embedded by rounds 1-6 keep their KaniHasher model —
// that is a fixture convention (regen comparisons must stay byte-identical),
// not a claim; clean's own cfg(kani) builds SELECT KaniHasher by design (that
// IS production behavior under kani). The non-kani production hasher is what
// this slice de-models.
//
// SOURCES (verbatim transcription targets):
//   $HOME/trust/library/core/src/hash/sip.rs      — SipHasher13 (whole write/finish
//                                               path; Sip13Rounds; compress!).
//   $HOME/trust/library/std/src/hash/random.rs    — DefaultHasher::new == keys(0,0).
//   $HOME/trust/library/core/src/hash/mod.rs      — default write_uN bodies;
//                                               [T]::hash; impl_write!.
//   $HOME/clean/crates/clean-kernel/src/expr/meta.rs — hash_to_u64 (:367-374),
//                                               mix_hash (:264-274), ExprMeta.
//   $HOME/clean/crates/clean-kernel/src/expr/kind.rs — compute_meta cfg(not(kani))
//                                               arms (:543-616).
//   $HOME/clean/crates/clean-kernel/src/level/mod.rs — Level (:81), Hash (:96-110),
//                                               has_params_impl (:1245).
//   $HOME/clean/crates/clean-kernel/src/name.rs   — Name::hash (:461-467).
//   $HOME/clean/crates/clean-kernel/src/expr/types.rs — BigNat (:166), Literal
//                                               (:401), LevelVec (:22).
//
// Crate name is load-bearing (appears in the mangled extern-leaf symbols the
// JIT binds): it MUST stay `clean_siphash_slice`.
//
// REGEN (one module per root; trust-ir main — NO frontend changes this round):
//   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//   cd $HOME/trust-ir/frontend
//   env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//     $S/bin/cargo run --bin trust_ir_mir -- \
//     ../../trust-cg/crates/trust-cg-codegen/tests/slices/clean_siphash_slice.rs \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots: sip_bytes_root | sip_ints_root | meta_sip_root

#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_variables)]

use std::sync::Arc;
#[allow(unused_imports)]
use std::convert::TryFrom; // pre-2021 prelude (the MIR driver's edition)

// ════════════════════════════════════════════════════════════════════════════
// std SipHasher13 — VERBATIM transcription (sip.rs), monomorphized at
// S = Sip13Rounds (the only instantiation DefaultHasher uses).
// ════════════════════════════════════════════════════════════════════════════

/// sip.rs:62-73 — State (v0,v2,v1,v3 field order and repr(C) kept VERBATIM).
#[derive(Clone, Copy)]
#[repr(C)]
pub struct SipState {
    pub v0: u64,
    pub v2: u64,
    pub v1: u64,
    pub v3: u64,
}

/// sip.rs:51-60 — Hasher<Sip13Rounds> (PhantomData marker elided; k0/k1 kept:
/// they are real state reset() reads).
pub struct SipHasher13 {
    pub k0: u64,
    pub k1: u64,
    pub length: usize, // how many bytes we've processed
    pub state: SipState, // hash State
    pub tail: u64,     // unprocessed bytes le
    pub ntail: usize,  // how many bytes in tail are valid
}

/// [S-add] u64 wrapping add from plain never-overflowing ops (see header).
#[inline]
fn w_add(a: u64, b: u64) -> u64 {
    let lo = (a & 0xFFFF_FFFF) + (b & 0xFFFF_FFFF);
    let hi = (a >> 32) + (b >> 32) + (lo >> 32);
    (hi << 32) | (lo & 0xFFFF_FFFF)
}

/// [S-rotl] u64 rotate-left for constant n in 1..=63 (see header).
#[inline]
fn rotl(x: u64, n: u32) -> u64 {
    (x << n) | (x >> (64 - n))
}

/// sip.rs:75-94 — compress! VERBATIM (one SipRound), with [S-add]/[S-rotl].
fn sip_compress(state: &mut SipState) {
    state.v0 = w_add(state.v0, state.v1);
    state.v2 = w_add(state.v2, state.v3);
    state.v1 = rotl(state.v1, 13);
    state.v1 ^= state.v0;
    state.v3 = rotl(state.v3, 16);
    state.v3 ^= state.v2;
    state.v0 = rotl(state.v0, 32);

    state.v2 = w_add(state.v2, state.v1);
    state.v0 = w_add(state.v0, state.v3);
    state.v1 = rotl(state.v1, 17);
    state.v1 ^= state.v2;
    state.v3 = rotl(state.v3, 21);
    state.v3 ^= state.v0;
    state.v2 = rotl(state.v2, 32);
}

/// sip.rs:360-364 — Sip13Rounds::c_rounds: ONE compress.
fn sip13_c_rounds(state: &mut SipState) {
    sip_compress(state);
}

/// sip.rs:366-371 — Sip13Rounds::d_rounds: THREE compresses.
fn sip13_d_rounds(state: &mut SipState) {
    sip_compress(state);
    sip_compress(state);
    sip_compress(state);
}

/// [S-load] LE integer loads (== load_int_le! on aarch64 LE). Assembly runs
/// in u64 with u32 shift amounts (the landed murmur/p_arr lowering shapes;
/// narrower-typed shifts do not validate), then truncates — same bits.
#[inline]
fn load_u16_le(buf: &[u8], i: usize) -> u16 {
    ((buf[i] as u64) | ((buf[i + 1] as u64) << 8u32)) as u16
}

#[inline]
fn load_u32_le(buf: &[u8], i: usize) -> u32 {
    ((buf[i] as u64)
        | ((buf[i + 1] as u64) << 8u32)
        | ((buf[i + 2] as u64) << 16u32)
        | ((buf[i + 3] as u64) << 24u32)) as u32
}

#[inline]
fn load_u64_le(buf: &[u8], i: usize) -> u64 {
    (buf[i] as u64)
        | ((buf[i + 1] as u64) << 8u32)
        | ((buf[i + 2] as u64) << 16u32)
        | ((buf[i + 3] as u64) << 24u32)
        | ((buf[i + 4] as u64) << 32u32)
        | ((buf[i + 5] as u64) << 40u32)
        | ((buf[i + 6] as u64) << 48u32)
        | ((buf[i + 7] as u64) << 56u32)
}

/// sip.rs:115-144 — u8to64_le VERBATIM (the 4/2/1 tail-assembly ladder;
/// requires len < 8; the cfg(debug) asserts elided [S-load]).
fn u8to64_le(buf: &[u8], start: usize, len: usize) -> u64 {
    let mut i = 0usize; // current byte index (from LSB) in the output u64
    let mut out: u64 = 0;
    if i + 3 < len {
        out = load_u32_le(buf, start + i) as u64;
        i += 4;
    }
    if i + 1 < len {
        out |= (load_u16_le(buf, start + i) as u64) << ((i * 8) as u32);
        i += 2;
    }
    if i < len {
        out |= (buf[start + i] as u64) << ((i * 8) as u32);
        i += 1;
    }
    out
}

impl SipHasher13 {
    /// sip.rs:166-181 + 184-208 — new() == new_with_keys(0,0); reset() sets
    /// the four SipHash constants (keys are zero: DefaultHasher::new()).
    pub fn new() -> SipHasher13 {
        let key0: u64 = 0;
        let key1: u64 = 0;
        SipHasher13 {
            k0: key0,
            k1: key1,
            length: 0,
            state: SipState {
                v0: key0 ^ 0x736f6d6570736575,
                v2: key0 ^ 0x6c7967656e657261,
                v1: key1 ^ 0x646f72616e646f6d,
                v3: key1 ^ 0x7465646279746573,
            },
            tail: 0,
            ntail: 0,
        }
    }

    /// sip.rs:255-300 — Hasher::write VERBATIM (buffering, tail flush, 8-byte
    /// block loop, tail refill). [S-min] for cmp::min.
    pub fn write(&mut self, msg: &[u8]) {
        let length = msg.len();
        self.length += length;

        let mut needed = 0usize;

        if self.ntail != 0 {
            needed = 8 - self.ntail;
            let take = if length < needed { length } else { needed }; // [S-min]
            self.tail |= u8to64_le(msg, 0, take) << ((8 * self.ntail) as u32);
            if length < needed {
                self.ntail += length;
                return;
            } else {
                self.state.v3 ^= self.tail;
                sip13_c_rounds(&mut self.state);
                self.state.v0 ^= self.tail;
                self.ntail = 0;
            }
        }

        // Buffered tail is now flushed, process new input.
        let len = length - needed;
        let left = len & 0x7; // len % 8

        let mut i = needed;
        while i < len - left {
            let mi = load_u64_le(msg, i);

            self.state.v3 ^= mi;
            sip13_c_rounds(&mut self.state);
            self.state.v0 ^= mi;

            i += 8;
        }

        self.tail = u8to64_le(msg, i, left);
        self.ntail = left;
    }

    /// sip.rs:302-308 — SipHasher13's write_str OVERRIDE: bytes + 0xFF
    /// (prefix-free because 0xFF can't appear in UTF-8).
    pub fn write_str_bytes(&mut self, s: &[u8]) {
        self.write(s);
        self.write_u8(0xFF);
    }

    /// sip.rs:310-325 — Hasher::finish VERBATIM (state copied; length low
    /// byte joins the tail block; 1 c-round; 0xff into v2; 3 d-rounds).
    pub fn finish(&self) -> u64 {
        let mut state = self.state;

        let b: u64 = ((self.length as u64 & 0xff) << 56) | self.tail;

        state.v3 ^= b;
        sip13_c_rounds(&mut state);
        state.v0 ^= b;

        state.v2 ^= 0xff;
        sip13_d_rounds(&mut state);

        state.v0 ^ state.v1 ^ state.v2 ^ state.v3
    }

    // ── The DEFAULT Hasher trait write_uN bodies (core/hash/mod.rs:360-431),
    //    which SipHasher13/DefaultHasher do NOT override: each is
    //    `self.write(&i.to_ne_bytes())`, LE on aarch64 [S2]. ──

    pub fn write_u8(&mut self, i: u8) {
        let bytes: [u8; 1] = [i];
        self.write(&bytes);
    }

    pub fn write_u16(&mut self, i: u16) {
        let x = i as u64;
        let bytes: [u8; 2] = [x as u8, (x >> 8u32) as u8];
        self.write(&bytes);
    }

    pub fn write_u32(&mut self, i: u32) {
        let x = i as u64;
        let bytes: [u8; 4] = [
            x as u8,
            (x >> 8u32) as u8,
            (x >> 16u32) as u8,
            (x >> 24u32) as u8,
        ];
        self.write(&bytes);
    }

    pub fn write_u64(&mut self, i: u64) {
        let bytes: [u8; 8] = [
            i as u8,
            (i >> 8u32) as u8,
            (i >> 16u32) as u8,
            (i >> 24u32) as u8,
            (i >> 32u32) as u8,
            (i >> 40u32) as u8,
            (i >> 48u32) as u8,
            (i >> 56u32) as u8,
        ];
        self.write(&bytes);
    }

    /// write_usize default == write(&i.to_ne_bytes()) — 8 LE bytes on arm64.
    /// (write_isize routes here: write_usize(i as usize).)
    pub fn write_usize(&mut self, i: usize) {
        let x = i as u64;
        let bytes: [u8; 8] = [
            x as u8,
            (x >> 8u32) as u8,
            (x >> 16u32) as u8,
            (x >> 24u32) as u8,
            (x >> 32u32) as u8,
            (x >> 40u32) as u8,
            (x >> 48u32) as u8,
            (x >> 56u32) as u8,
        ];
        self.write(&bytes);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// clean-kernel payload types (the compute_meta hash inputs) — landed shapes.
// ════════════════════════════════════════════════════════════════════════════

/// name.rs:233-239, cut to the hash-visible field [S4]: Name::hash reads ONLY
/// cached_hash; the construction chain is rounds-4/6-verified and the harness
/// feeds REAL clean-kernel cached_hash goldens.
#[derive(Clone)]
pub struct Name {
    pub cached_hash: u64,
}

pub type LevelArc = Arc<Level>;

/// level/mod.rs:81-92 — the production Level (declaration order is
/// hash-load-bearing: it fixes the discriminant indices [S3]).
#[derive(Clone)]
pub enum Level {
    /// Zero (the lowest level)
    Zero,
    /// Successor: l + 1
    Succ(LevelArc),
    /// Maximum: max(l1, l2)
    Max(LevelArc, LevelArc),
    /// Impredicative maximum: imax(l1, l2) = 0 if l2 = 0, else max(l1, l2)
    IMax(LevelArc, LevelArc),
    /// Universe parameter (polymorphism)
    Param(Name),
}

impl Level {
    /// VERBATIM `has_params_impl` (mod.rs:1245-1254); stack_safe pass-through.
    pub fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => l.has_params(),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => l1.has_params() || l2.has_params(),
            Level::Param(_) => true,
        }
    }

    /// PRODUCTION smart constructor (mod.rs:259-262). Also load-bearing for
    /// lowering: a bare `Level::Zero` at operand position becomes a non-scalar
    /// MIR constant the frontend rejects; the call form lowers (the landed R6
    /// convention).
    pub fn zero() -> Self {
        Level::Zero
    }

    /// PRODUCTION smart constructor (mod.rs:264-267): Succ(level_arc(l));
    /// level_arc == Arc::new under cfg(not(kani)).
    pub fn succ(l: Level) -> Self {
        Level::Succ(Arc::new(l))
    }

    /// RAW node builders (NOT the production max/imax smart constructors —
    /// those SIMPLIFY, e.g. max(l,l)=l; the hash differential needs the raw
    /// tree shapes, and production Level::hash must handle ANY tree).
    pub fn max_raw(l1: Level, l2: Level) -> Self {
        Level::Max(Arc::new(l1), Arc::new(l2))
    }

    pub fn imax_raw(l1: Level, l2: Level) -> Self {
        Level::IMax(Arc::new(l1), Arc::new(l2))
    }

    /// PRODUCTION smart constructor shape (mod.rs:351-359): Param(name).
    pub fn param(name: Name) -> Self {
        Level::Param(name)
    }
}

/// expr/types.rs:22 — LevelVec = SmallVec<[Level; 2]>, modeled Vec [B9]
/// (hashes through the identical <[Level] as Hash> write sequence).
pub type LevelVec = Vec<Level>;

/// expr/types.rs:165-171 — BigNat (derive(Hash) semantics transcribed [S3]).
#[derive(Clone)]
pub enum BigNat {
    /// Small value that fits in u64.
    Small(u64),
    /// Large value with multiple limbs (little-endian, lowest limb first).
    Big(Vec<u64>),
}

/// expr/types.rs:399-406 — Literal (derive(Hash) semantics transcribed [S3]).
#[derive(Clone)]
pub enum Literal {
    /// Natural number literal (arbitrary precision)
    Nat(BigNat),
    /// String literal
    String(Arc<str>),
}

// ════════════════════════════════════════════════════════════════════════════
// hash_to_u64 (meta.rs:367-374) over the REAL production hasher — monomorphic
// per-type entry points (a generic hash_to_u64<T> would collide as duplicate
// JIT symbols; the landed rung convention).
// Each: DefaultHasher::new() -> the type's production Hash writes -> finish().
// ════════════════════════════════════════════════════════════════════════════

/// Name::hash (name.rs:461-467): cached_hash.hash(state) == write_u64.
fn sip_hash_name(value: &Name) -> u64 {
    let mut hasher = SipHasher13::new();
    hasher.write_u64(value.cached_hash);
    hasher.finish()
}

/// Level::hash (level/mod.rs:96-110, cfg(not(kani))) monomorphized at the
/// production hasher: discriminant(self).hash(state) [S3: isize -> the
/// write_usize default chain -> 8 LE bytes; indices Zero=0 Succ=1 Max=2
/// IMax=3 Param=4] then recursive field hashing (<Arc<Level> as Hash> derefs
/// to the child Level; Param reaches Name::hash).
fn sip_write_level(hasher: &mut SipHasher13, value: &Level) {
    let discr: usize = match value {
        Level::Zero => 0,
        Level::Succ(_) => 1,
        Level::Max(_, _) => 2,
        Level::IMax(_, _) => 3,
        Level::Param(_) => 4,
    };
    hasher.write_usize(discr);
    match value {
        Level::Zero => {}
        Level::Succ(l) => sip_write_level(hasher, l),
        Level::Max(l, r) | Level::IMax(l, r) => {
            sip_write_level(hasher, l);
            sip_write_level(hasher, r);
        }
        Level::Param(n) => hasher.write_u64(n.cached_hash),
    }
}

fn sip_hash_level(value: &Level) -> u64 {
    let mut hasher = SipHasher13::new();
    sip_write_level(&mut hasher, value);
    hasher.finish()
}

/// <LevelVec as Hash> == <[Level] as Hash> (core/hash/mod.rs:931-937):
/// write_length_prefix(len) [default: write_usize] then per-element
/// Level::hash — the element loop is an index loop [B9].
fn sip_hash_levels(value: &[Level]) -> u64 {
    let mut hasher = SipHasher13::new();
    hasher.write_usize(value.len());
    let mut i = 0usize;
    while i < value.len() {
        sip_write_level(&mut hasher, &value[i]);
        i += 1;
    }
    hasher.finish()
}

/// derive(Hash) for Literal/BigNat transcribed [S3]/[S5]:
/// Literal discr (Nat=0 String=1), then
///   Nat -> BigNat discr (Small=0 Big=1) -> u64 | Vec<u64> payload;
///   String -> <Arc<str> as Hash> -> str::hash -> write_str (bytes + 0xFF).
fn sip_hash_lit(value: &Literal) -> u64 {
    let mut hasher = SipHasher13::new();
    match value {
        Literal::Nat(bn) => {
            hasher.write_usize(0);
            match bn {
                BigNat::Small(n) => {
                    hasher.write_usize(0);
                    hasher.write_u64(*n);
                }
                BigNat::Big(limbs) => {
                    hasher.write_usize(1);
                    // <Vec<u64> as Hash>: write_usize(len) + hash_slice ==
                    // ONE bulk LE-byte write; per-limb write_u64 here [S5]
                    // (block-aligned: bit-identical).
                    hasher.write_usize(limbs.len());
                    let mut i = 0usize;
                    while i < limbs.len() {
                        hasher.write_u64(limbs[i]);
                        i += 1;
                    }
                }
            }
        }
        Literal::String(s) => {
            hasher.write_usize(1);
            // <Arc<str> as Deref> is the landed extern crossing; the byte
            // write + 0xFF suffix run back in-module.
            let st: &str = &**s;
            hasher.write_str_bytes(st.as_bytes());
        }
    }
    hasher.finish()
}

// ════════════════════════════════════════════════════════════════════════════
// expr/meta.rs — mix_hash + ExprMeta (VERBATIM, identical to the verified
// rungs; mix_hash's wrapping_mul is the landed extern shim leaf).
// ════════════════════════════════════════════════════════════════════════════

/// MurmurHash2-64A mixing step. Matches Lean 4's `lean_uint64_mix_hash`.
#[inline]
pub(crate) fn mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let mut h = h ^ k;
    h = h.wrapping_mul(M);
    h
}

// clean's Level has NO MVar variant; the production non-kani body recurses
// structurally and is everywhere-false (the landed convention in every rung).
#[inline]
fn level_has_mvar(_l: &Level) -> bool {
    false
}

#[derive(Clone, Copy)]
pub struct ExprMeta(pub u64);

impl ExprMeta {
    const HASH_MASK: u64 = 0xFFFF_FFFF;
    const DEPTH_SHIFT: u32 = 32;
    const DEPTH_MASK: u64 = 0xFF;
    const HAS_FVAR_BIT: u32 = 40;
    const HAS_EXPR_MVAR_BIT: u32 = 41;
    const HAS_LEVEL_MVAR_BIT: u32 = 42;
    const HAS_LEVEL_PARAM_BIT: u32 = 43;
    const BVAR_RANGE_SHIFT: u32 = 44;
    const MAX_DEPTH: u32 = 255;

    fn pack(
        hash: u32,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> Self {
        let depth = approx_depth.min(Self::MAX_DEPTH);
        let range = loose_bvar_range;
        let bits = (hash as u64)
            | ((depth as u64) << Self::DEPTH_SHIFT)
            | ((has_fvar as u64) << Self::HAS_FVAR_BIT)
            | ((has_expr_mvar as u64) << Self::HAS_EXPR_MVAR_BIT)
            | ((has_level_mvar as u64) << Self::HAS_LEVEL_MVAR_BIT)
            | ((has_level_param as u64) << Self::HAS_LEVEL_PARAM_BIT)
            | ((range as u64) << Self::BVAR_RANGE_SHIFT);
        ExprMeta(bits)
    }

    fn raw(self) -> u64 {
        self.0
    }
    fn hash(self) -> u32 {
        (self.0 & Self::HASH_MASK) as u32
    }
    fn approx_depth(self) -> u8 {
        ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8
    }
    fn has_fvar(self) -> bool {
        (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1
    }
    fn has_expr_mvar(self) -> bool {
        (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1
    }
    fn has_level_mvar(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1
    }
    fn has_level_param(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1
    }
    fn loose_bvar_range(self) -> u32 {
        (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
    }
}

// ════════════════════════════════════════════════════════════════════════════
// expr/kind.rs — the FOUR payload-hash compute_meta arms, cfg(not(kani))
// (:543-616), VERBATIM with hash_to_u64 == the SipHash13 path above [S6].
// ════════════════════════════════════════════════════════════════════════════

pub enum ExprKind {
    Sort(Level),
    Const(Name, LevelVec),
    Lit(Literal),
    Proj(Name, u32, Arc<Expr>),
}

pub struct Expr {
    pub kind: ExprKind,
    pub meta: ExprMeta,
}

impl Expr {
    /// expr/mod.rs:241-246 — from_kind computes meta at construction.
    pub fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    pub fn meta(&self) -> ExprMeta {
        self.meta
    }
}

impl ExprKind {
    fn compute_meta(&self) -> ExprMeta {
        match self {
            // kind.rs:558-566 — Sort.
            ExprKind::Sort(lvl) => ExprMeta::pack(
                mix_hash(11, sip_hash_level(lvl)) as u32,
                0,
                0,
                false,
                false,
                level_has_mvar(lvl),
                lvl.has_params(),
            ),
            // kind.rs:567-581 — Const (the .iter().any() predicates as index
            // loops [B9]).
            ExprKind::Const(name, levels) => {
                let name_hash = sip_hash_name(name);
                let levels_hash = sip_hash_levels(levels);
                let mut has_level_param = false;
                {
                    let mut li = 0usize;
                    while li < levels.len() {
                        if levels[li].has_params() {
                            has_level_param = true;
                            break;
                        }
                        li += 1;
                    }
                }
                let mut has_level_mvar = false;
                {
                    let mut li = 0usize;
                    while li < levels.len() {
                        if level_has_mvar(&levels[li]) {
                            has_level_mvar = true;
                            break;
                        }
                        li += 1;
                    }
                }
                ExprMeta::pack(
                    mix_hash(5, mix_hash(name_hash, levels_hash)) as u32,
                    0,
                    0,
                    false,
                    false,
                    has_level_mvar,
                    has_level_param,
                )
            }
            // kind.rs:588-596 — Lit.
            ExprKind::Lit(lit) => ExprMeta::pack(
                mix_hash(3, sip_hash_lit(lit)) as u32,
                0,
                0,
                false,
                false,
                false,
                false,
            ),
            // kind.rs:597-616 — Proj.
            ExprKind::Proj(name, idx, expr) => {
                let inner = expr.meta();
                let depth = (inner.approx_depth() as u32 + 1).min(255);
                let h = mix_hash(
                    depth as u64,
                    mix_hash(
                        sip_hash_name(name),
                        mix_hash(*idx as u64, inner.hash() as u64),
                    ),
                ) as u32;
                ExprMeta::pack(
                    h,
                    inner.loose_bvar_range(),
                    depth,
                    inner.has_fvar(),
                    inner.has_expr_mvar(),
                    inner.has_level_mvar(),
                    inner.has_level_param(),
                )
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// ROOTS (host marshals raw pointers; everything else runs in-module).
// ════════════════════════════════════════════════════════════════════════════

/// RAW SIP DIFFERENTIAL over byte strings: three sequential write() calls
/// (the host splits one logical message into three chunks — every
/// tail/flush/block interplay is reachable by choosing the split), then
/// finish(). Native oracle: std DefaultHasher fed the identical chunks.
#[no_mangle]
pub extern "C" fn sip_bytes_root(
    p1: *const u8,
    l1: usize,
    p2: *const u8,
    l2: usize,
    p3: *const u8,
    l3: usize,
) -> u64 {
    let c1: &[u8] = unsafe { std::slice::from_raw_parts(p1, l1) };
    let c2: &[u8] = unsafe { std::slice::from_raw_parts(p2, l2) };
    let c3: &[u8] = unsafe { std::slice::from_raw_parts(p3, l3) };
    let mut hasher = SipHasher13::new();
    hasher.write(c1);
    hasher.write(c2);
    hasher.write(c3);
    hasher.finish()
}

/// RAW SIP DIFFERENTIAL over integer-write sequences (the write_uN default
/// bodies): mode selects a sequence mixing widths so 8-byte writes land at
/// every tail offset. Native oracle: std DefaultHasher, same sequence.
#[no_mangle]
pub extern "C" fn sip_ints_root(mode: u64, a: u64, b: u32, c: u8) -> u64 {
    let mut hasher = SipHasher13::new();
    if mode == 0 {
        hasher.write_u64(a);
    } else if mode == 1 {
        hasher.write_u32(b);
    } else if mode == 2 {
        hasher.write_u8(c);
    } else if mode == 3 {
        // u64 write across a 1-byte tail (needed=7 flush path)
        hasher.write_u8(c);
        hasher.write_u64(a);
    } else if mode == 4 {
        hasher.write_u32(b);
        hasher.write_u64(a);
        hasher.write_u8(c);
    } else if mode == 5 {
        hasher.write_usize(a as usize);
    } else if mode == 6 {
        hasher.write_u8(c);
        hasher.write_u8(c ^ 0xFF);
        hasher.write_u8(c.wrapping_add(1));
        hasher.write_u32(b);
        hasher.write_u64(a);
    } else if mode == 7 {
        hasher.write_u16((b & 0xFFFF) as u16);
    } else if mode == 8 {
        // exactly ntail=7 (1+2+4) then a u64 (needed=1 flush + 7 leftover)
        hasher.write_u8(c);
        hasher.write_u16((b & 0xFFFF) as u16);
        hasher.write_u32(b);
        hasher.write_u64(a);
    } else if mode == 9 {
        // the write_str shape (bytes + 0xFF) over the u64's LE bytes
        hasher.write_u64(a);
        hasher.write_u8(0xFF);
    } else {
        // mode >= 10: two u64s (block-aligned back-to-back)
        hasher.write_u64(a);
        hasher.write_u64(a ^ mode);
    }
    hasher.finish()
}

/// THE META DIFFERENTIAL: compute_meta arms over the production SipHash13
/// hash_to_u64. Cases (x/y/z are Name cached_hash values / payloads; sptr,
/// slen carry str bytes or u64 limbs):
///   0: Sort(Zero)                       1: Sort(Succ(Zero))
///   2: Sort(Param{x})                   3: Sort(Max(Succ(Zero), Param{x}))
///   4: Sort(IMax(Param{x}, Param{y}))   5: Const({x}, [])
///   6: Const({x}, [Succ(Param{y}), Zero])
///   7: Lit(Nat(Small(x)))               8: Lit(Nat(Big(limbs from sptr)))
///   9: Lit(String(bytes from sptr))    10: Proj({x}, y as u32, Lit-Small(z))
///  11: Sort(Succ(Param{x}))  (the G2 clean-kernel golden shape)
///  20..=26: the RAW payload hashes (isolate the hasher from mix_hash):
///   20: sip_hash_level(Zero)           21: sip_hash_level(Succ(Param{x}))
///   22: sip_hash_name({x})             23: sip_hash_levels([])
///   24: sip_hash_levels([Succ(Param{y}), Zero])
///   25: sip_hash_lit(Nat Small x)      26: sip_hash_lit(String from sptr)
#[no_mangle]
pub extern "C" fn meta_sip_root(
    case: u64,
    x: u64,
    y: u64,
    z: u64,
    sptr: *const u8,
    slen: usize,
) -> u64 {
    if case == 0 {
        Expr::from_kind(ExprKind::Sort(Level::zero())).meta().raw()
    } else if case == 1 {
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
            .meta()
            .raw()
    } else if case == 2 {
        Expr::from_kind(ExprKind::Sort(Level::param(Name { cached_hash: x })))
            .meta()
            .raw()
    } else if case == 3 {
        Expr::from_kind(ExprKind::Sort(Level::max_raw(
            Level::succ(Level::zero()),
            Level::param(Name { cached_hash: x }),
        )))
        .meta()
        .raw()
    } else if case == 4 {
        Expr::from_kind(ExprKind::Sort(Level::imax_raw(
            Level::param(Name { cached_hash: x }),
            Level::param(Name { cached_hash: y }),
        )))
        .meta()
        .raw()
    } else if case == 5 {
        let levels: LevelVec = Vec::new();
        Expr::from_kind(ExprKind::Const(Name { cached_hash: x }, levels))
            .meta()
            .raw()
    } else if case == 6 {
        let mut levels: LevelVec = Vec::new();
        levels.push(Level::succ(Level::param(Name { cached_hash: y })));
        levels.push(Level::zero());
        Expr::from_kind(ExprKind::Const(Name { cached_hash: x }, levels))
            .meta()
            .raw()
    } else if case == 7 {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(x))))
            .meta()
            .raw()
    } else if case == 8 {
        let limbs_in: &[u64] = unsafe { std::slice::from_raw_parts(sptr as *const u64, slen) };
        let mut limbs: Vec<u64> = Vec::new();
        let mut i = 0usize;
        while i < limbs_in.len() {
            limbs.push(limbs_in[i]);
            i += 1;
        }
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(limbs))))
            .meta()
            .raw()
    } else if case == 9 {
        let bytes: &[u8] = unsafe { std::slice::from_raw_parts(sptr, slen) };
        let s: &str = unsafe { std::str::from_utf8_unchecked(bytes) };
        let arc: Arc<str> = Arc::from(s);
        Expr::from_kind(ExprKind::Lit(Literal::String(arc)))
            .meta()
            .raw()
    } else if case == 10 {
        let inner = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(z))));
        Expr::from_kind(ExprKind::Proj(
            Name { cached_hash: x },
            y as u32,
            Arc::new(inner),
        ))
        .meta()
        .raw()
    } else if case == 11 {
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(Name {
            cached_hash: x,
        }))))
        .meta()
        .raw()
    } else if case == 20 {
        let l = Level::zero();
        sip_hash_level(&l)
    } else if case == 21 {
        let l = Level::succ(Level::param(Name { cached_hash: x }));
        sip_hash_level(&l)
    } else if case == 22 {
        sip_hash_name(&Name { cached_hash: x })
    } else if case == 23 {
        let levels: LevelVec = Vec::new();
        sip_hash_levels(&levels)
    } else if case == 24 {
        let mut levels: LevelVec = Vec::new();
        levels.push(Level::succ(Level::param(Name { cached_hash: y })));
        levels.push(Level::zero());
        sip_hash_levels(&levels)
    } else if case == 25 {
        sip_hash_lit(&Literal::Nat(BigNat::Small(x)))
    } else if case == 26 {
        let bytes: &[u8] = unsafe { std::slice::from_raw_parts(sptr, slen) };
        let s: &str = unsafe { std::str::from_utf8_unchecked(bytes) };
        let arc: Arc<str> = Arc::from(s);
        sip_hash_lit(&Literal::String(arc))
    } else {
        // never-asked guard (the landed convention)
        0xDEAD_BEEF_DEAD_BEEF
    }
}
