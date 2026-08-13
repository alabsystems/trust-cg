// SELF-CONTAINED SwissTable `HashMap::get` slice — Route 2 (faithful VERBATIM
// transcription of hashbrown 0.16.1's GENERIC `Group` SwissTable lookup path).
//
// WHY Route 2 (not Route 1): on aarch64-apple-darwin `neon` is an ABI-MANDATED
// baseline target_feature (rustc: "target feature `neon` must be enabled to
// ensure that the ABI of the current target can be implemented correctly").
// hashbrown's `control/group/mod.rs` selects the NEON `Group` under
// `cfg(all(target_arch="aarch64", target_feature="neon", ...))`, so the
// precompiled std on this target is LOCKED to the NEON Group; -C
// target-feature=-neon is being phased out and would break the ABI. Therefore
// the real-std generic Group cannot be forced here. Instead this slice
// transcribes hashbrown's OWN generic path VERBATIM (the same algorithm the
// NEON Group is a SIMD optimization of), so the lookup is FAITHFUL to
// hashbrown's SwissTable.
//
// WHAT IS TRANSCRIBED (each piece is the verbatim hashbrown 0.16.1 source):
//   * `Tag` + `Tag::EMPTY`/`DELETED`/`is_full`/`full(hash)`  (control/tag.rs)
//   * the generic `Group` (GroupWord = u64) + `repeat`/`load`/`match_tag`/
//     `match_empty`/WIDTH=8                                  (control/group/generic.rs)
//   * `BitMask` + `lowest_set_bit`/`trailing_zeros`/`remove_lowest_bit`/
//     `any_bit_set` + `BitMaskIter`                          (control/bitmask.rs)
//   * `h1`, `ProbeSeq`/`move_next`, `probe_seq`, `find_inner` probe loop,
//     `ctrl`, `data_end`, `bucket_ptr` pointer math          (raw/mod.rs)
//   * `make_hash` (KaniHasher = clean's cfg(kani) FxHash-style hasher) — the
//     SAME verified deterministic env-key hash as the prior leg.
//
// THE TABLE LAYOUT is hashbrown's REAL layout, byte-identical to what the real
// SwissTable allocates: `[T_{n}..T_1 T_0][C_0 C_1 .. C_n][Ca_0..Ca_{WIDTH-1}]`
// with `data_end` (== ctrl base) between the (reversed) data and the control
// bytes; bucket i lives at `data_end - (i+1)*size_of::<T>()`. Native Rust
// `build_table` fills this real layout (placing each entry at its real ideal
// bucket via the real probe), and `env_get` runs the transcribed generic-Group
// probe over it. Building the real layout + running the transcribed probe over
// it PROVES the transcription matches the real algorithm.
//
// The verification (mir_real_hashmap_get_roundtrip) builds ONE table in native
// Rust, passes it BY POINTER to both native `env_get` and the JIT'd `env_get`,
// and asserts agreement on hits (present key -> its value) and misses (absent
// key -> sentinel). KaniHasher is deterministic so native==JIT is well-defined.

#![allow(dead_code)]
#![allow(clippy::all)]
#![allow(unused_unsafe)]

// ───────────────────────── the env key (Name) ─────────────────────────────
// A `Name` is a single interned u64 handle — the real Environment key shape.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Name(pub u64);

// ─────────── KaniHasher: clean's cfg(kani) FxHash-style hasher ─────────────
// VERBATIM the prior verified make_hash leg (expr/meta.rs:285): pure-arithmetic
// multiply-XOR over a single u64 state. The env-key hash is deterministic.
const KANI_MUL: u64 = 0x517cc1b727220a95;

pub struct KaniHasher {
    state: u64,
}
impl KaniHasher {
    pub fn new() -> Self {
        KaniHasher { state: 0 }
    }
    pub fn write_u64(&mut self, i: u64) {
        self.state ^= i;
        self.state = self.state.wrapping_mul(KANI_MUL);
    }
    pub fn finish(&self) -> u64 {
        self.state
    }
}

/// The deterministic env-key hash: `Name(u64)` -> hash. Exactly what
/// `make_hash` computes (a derived `Hash` for a single-u64 key writes its field
/// via `write_u64`). This is the verified make_hash sub-step.
#[inline]
pub fn make_hash(key: &Name) -> u64 {
    let mut h = KaniHasher::new();
    h.write_u64(key.0);
    h.finish()
}

// ───────────────────── Tag (VERBATIM control/tag.rs) ───────────────────────
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct Tag(pub u8);
impl Tag {
    pub const EMPTY: Tag = Tag(0b1111_1111);
    pub const DELETED: Tag = Tag(0b1000_0000);

    /// VERBATIM `Tag::is_full`.
    #[inline]
    pub fn is_full(self) -> bool {
        self.0 & 0x80 == 0
    }

    /// VERBATIM `Tag::full(hash)` (top 7 bits of the hash; MIN_HASH_LEN = 8 on
    /// 64-bit). `top7 = hash >> (8*8 - 7) = hash >> 57`.
    #[inline]
    pub fn full(hash: u64) -> Tag {
        let top7 = hash >> (8 * 8 - 7);
        Tag((top7 & 0x7f) as u8)
    }
}

// ───────────── Group (VERBATIM control/group/generic.rs, u64 SWAR) ─────────
const GROUP_WIDTH: usize = 8; // mem::size_of::<u64>()

/// VERBATIM `repeat(tag)` — replicate a tag byte across the GroupWord.
#[inline]
fn repeat(tag: Tag) -> u64 {
    u64::from_ne_bytes([tag.0; GROUP_WIDTH])
}

/// VERBATIM the generic `Group(u64)`.
#[derive(Copy, Clone)]
pub struct Group(u64);

impl Group {
    pub const WIDTH: usize = GROUP_WIDTH;

    /// VERBATIM `Group::load` — unaligned read of 8 control bytes as a u64.
    #[inline]
    pub unsafe fn load(ptr: *const Tag) -> Self {
        Group(core::ptr::read_unaligned(ptr.cast::<u64>()))
    }

    /// VERBATIM `Group::match_tag` — the u64 SWAR group compare. Returns a
    /// `BitMask` of all tags which *may* equal `tag` (the bithack from
    /// graphics.stanford.edu/~seander/bithacks.html#ValueInWord). NO SIMD.
    #[inline]
    pub fn match_tag(self, tag: Tag) -> BitMask {
        let cmp = self.0 ^ repeat(tag);
        BitMask(
            (cmp.wrapping_sub(repeat(Tag(0x01))) & !cmp & repeat(Tag::DELETED)).to_le(),
        )
    }

    /// VERBATIM `Group::match_empty` — all EMPTY tags (top 2 bits both 1).
    #[inline]
    pub fn match_empty(self) -> BitMask {
        BitMask((self.0 & (self.0 << 1) & repeat(Tag::DELETED)).to_le())
    }
}

// ───────────── BitMask (VERBATIM control/bitmask.rs, u64 word) ─────────────
// BITMASK_STRIDE = 8 (one set bit per byte). On aarch64 (NOT target_arch="arm",
// which is 32-bit ARM) `trailing_zeros` takes the plain `.trailing_zeros()/8`
// branch — VERBATIM the non-arm path.
const BITMASK_STRIDE: usize = 8;

#[derive(Copy, Clone)]
pub struct BitMask(pub u64);

impl BitMask {
    /// VERBATIM `remove_lowest_bit`.
    #[inline]
    fn remove_lowest_bit(self) -> Self {
        BitMask(self.0 & (self.0 - 1))
    }

    /// VERBATIM `any_bit_set`.
    #[inline]
    pub fn any_bit_set(self) -> bool {
        self.0 != 0
    }

    /// VERBATIM `lowest_set_bit` (non-arm path: trailing_zeros / stride). On
    /// aarch64 `cfg!(target_arch = "arm")` is FALSE, so this is the
    /// `self.0.trailing_zeros() as usize / BITMASK_STRIDE` branch, guarded by
    /// the `!= 0` check (the NonZero new() is just to use the nonzero intrinsic;
    /// the value is identical).
    #[inline]
    pub fn lowest_set_bit(self) -> Option<usize> {
        if self.0 == 0 {
            None
        } else {
            Some(self.0.trailing_zeros() as usize / BITMASK_STRIDE)
        }
    }
}

/// VERBATIM `BitMaskIter` (`into_iter` masks with BITMASK_ITER_MASK = !0, a
/// no-op for a match mask that already has <=1 bit per byte).
pub struct BitMaskIter(BitMask);

impl BitMaskIter {
    #[inline]
    fn new(m: BitMask) -> Self {
        BitMaskIter(m)
    }
    /// VERBATIM `BitMaskIter::next`.
    #[inline]
    fn next(&mut self) -> Option<usize> {
        let bit = self.0.lowest_set_bit()?;
        self.0 = self.0.remove_lowest_bit();
        Some(bit)
    }
}

// ─────────────── h1 / ProbeSeq (VERBATIM raw/mod.rs) ───────────────────────
/// VERBATIM `h1` — primary hash, low bits select the initial bucket.
#[inline]
fn h1(hash: u64) -> usize {
    hash as usize
}

/// VERBATIM `ProbeSeq` (triangular probing).
struct ProbeSeq {
    pos: usize,
    stride: usize,
}
impl ProbeSeq {
    /// VERBATIM `ProbeSeq::move_next`.
    #[inline]
    fn move_next(&mut self, bucket_mask: usize) {
        self.stride += GROUP_WIDTH;
        self.pos += self.stride;
        self.pos &= bucket_mask;
    }
}

// ─────────────── the table (hashbrown's REAL layout) ───────────────────────
// The single allocation is `[T_n..T_0][C_0..C_n][Ca_0..Ca_{WIDTH-1}]`. We hold
// `ctrl` = the control-bytes base (== `data_end`, the boundary between the
// reversed data and the control bytes), exactly hashbrown's `RawTableInner.ctrl`
// / `data_end`. `bucket_mask = buckets - 1`. Entry i (a (Name, u64) pair) lives
// at `data_end - (i+1)*size_of::<Entry>()` (hashbrown's `bucket_ptr`).
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Entry {
    pub key: Name,
    pub val: u64,
}

/// A faithful `RawTableInner`: the control-byte base pointer + bucket_mask. The
/// data buckets sit BELOW `ctrl` (at negative offsets), the control bytes AT and
/// ABOVE `ctrl`, exactly like the real allocation.
#[repr(C)]
pub struct EnvTable {
    pub bucket_mask: usize,
    pub ctrl: *const u8,
}

impl EnvTable {
    /// VERBATIM `RawTableInner::probe_seq`.
    #[inline]
    fn probe_seq(&self, hash: u64) -> ProbeSeq {
        ProbeSeq {
            pos: h1(hash) & self.bucket_mask,
            stride: 0,
        }
    }

    /// VERBATIM `RawTableInner::ctrl` — `&Tag` at control index.
    #[inline]
    unsafe fn ctrl(&self, index: usize) -> *const Tag {
        self.ctrl.add(index).cast::<Tag>()
    }

    /// `data_end` (== ctrl base) cast to the entry type — hashbrown's
    /// `data_end::<T>()`.
    #[inline]
    fn data_end(&self) -> *const Entry {
        self.ctrl.cast::<Entry>()
    }

    /// VERBATIM `RawTableInner::bucket_ptr` specialized to `Entry`: bucket i is
    /// at `data_end - (i+1)*size_of::<Entry>()`.
    #[inline]
    unsafe fn bucket(&self, index: usize) -> *const Entry {
        let base = self.data_end();
        base.sub(index + 1)
    }
}

// ─────────────── find_inner / get (VERBATIM raw/mod.rs find_inner) ─────────
// `eq(index)` is the key-equality closure inlined: load bucket `index`'s key and
// compare it to the probe key — the `equivalent_key` the real `get` passes.
const NOT_FOUND: u64 = u64::MAX; // miss sentinel (env_get's None)

/// THE LOOKUP — VERBATIM hashbrown `RawTableInner::find_inner` over the generic
/// `Group`, with the `eq` closure inlined as a key compare and the bucket's
/// value returned on a hit. Returns the entry's `val` on a hit, `NOT_FOUND` on
/// a miss. This IS the real SwissTable `HashMap::get` algorithm (generic path).
#[inline(never)]
pub fn env_get(table: &EnvTable, key: &Name) -> u64 {
    let hash = make_hash(key);
    let tag_hash = Tag::full(hash);
    let mut probe_seq = table.probe_seq(hash);

    loop {
        // load 8 control bytes at the current probe position (Group::load).
        let group = unsafe { Group::load(table.ctrl(probe_seq.pos)) };

        // scan the group for tags that may match h2 (Group::match_tag).
        let mut it = BitMaskIter::new(group.match_tag(tag_hash));
        loop {
            let bit = match it.next() {
                Some(b) => b,
                None => break,
            };
            let index = (probe_seq.pos + bit) & table.bucket_mask;
            // eq(index): compare the bucket's key (the real equivalent_key).
            let entry = unsafe { &*table.bucket(index) };
            if entry.key.0 == key.0 {
                return entry.val;
            }
        }

        // if the group has any EMPTY slot, the key is absent (Group::match_empty).
        if group.match_empty().any_bit_set() {
            return NOT_FOUND;
        }

        probe_seq.move_next(table.bucket_mask);
    }
}

// ───────────────── make_hash_direct (the prior verified leg) ───────────────
// Kept VERBATIM so the existing mir_env_key_make_hash leg still emits from this
// same slice (the IR const there is generated from `make_hash_direct`).
#[inline(never)]
pub fn make_hash_direct(name: &Name) -> u64 {
    let mut h = KaniHasher::new();
    h.write_u64(name.0);
    h.finish()
}
