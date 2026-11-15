// trust-cg-codegen/examples/wasm_vt_islands.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The P5 aterm islands (trust designs/2026-08-24-one-module-every-target.md
//! §5): the terminal engine's two hottest pure functions, generated from the
//! REAL aterm tables and compiled trust-ir→trust-cg-wasm as memory-free,
//! import-free, call-free code:
//!
//!   * `vt_step(state, byte) -> (next_state << 8) | action` — the DEC ANSI
//!     parser transition (aterm-parser's 14×256 `TRANSITIONS` table). Out of
//!     range: `state >= 14` returns the sentinel `0xFFFF`; `byte` is masked
//!     to 8 bits. Runtime per-instance overrides are host state, out of the
//!     island's spec by decision.
//!   * `wcwidth(cp) -> 0|1|2` — aterm-grapheme's `char_width` over the full
//!     u32 domain: surrogates answer 1 (they are not `char`s; island spec
//!     decision), `cp > 0x10FFFF` answers 1.
//!
//! The generator consumes a JSON dump of the tables (`scripts/export_vt_tables.py`
//! compiles the committed aterm table sources and reads their public APIs)
//! and authors both spellings from that one input: the trust-ir
//! functions as balanced compare TREES (pure code, no tables in memory), and
//! a rustc/LLVM twin that embeds the tables and INDEXES them — deliberately
//! different algorithms for the same spec, so the shipped differential
//! compares two compilers *and* two computation strategies.
//!
//!     scripts/trust_cargo.sh run --example wasm_vt_islands -- <tables.json> <outdir>
//!
//! That dump is COMMON-MODE input: it feeds the island, the twin AND the
//! expectations, so a table nobody authored would be believed unanimously and
//! the differential would report agreement. Three things fail this generator
//! closed instead. The dump must NAME itself — the required header is, in this
//! exact key order,
//!
//! ```text
//! {"schema":"aterm.vt-islands.tables","version":1,"aterm_commit":"<rev>",
//!  "vt":[[[next,action] × 256] × 14],"width_runs":[[lo,hi,width], …]}
//! ```
//!
//! and the parser is strict: every byte outside that grammar is a panic, never
//! a skip to the next digit. The table CONTRACTS are then checked here rather
//! than trusted — vt cells must pack into the twin's `u16` (`next` < 14,
//! `action` ≤ 255), and the width runs must tile `0..=0x10FFFF` exactly, in
//! order, answering only 0, 1 or 2, with the surrogates answering 1 per the
//! island policy above. Finally the SHA-256 of the exact input bytes is
//! recorded as `tables_sha256` in the emitted expectations, so a shipped
//! artifact names the table dump it came from.
//!
//! Emits `vt_islands.wasm` (trust-cg bytes, NO wasm-opt), `vt_islands_twin.rs`,
//! and `vt_islands_expected.json` (`tables_sha256`, exhaustive vt expectations
//! incl. out-of-range states, width spot samples, and the width runs the page
//! expands for its exhaustive in-browser check). Every expectation is checked
//! against the trust-ir interpreter here before anything is written.

use std::fmt::Write as _;
use std::io::Write as _;

use sha2::{Digest as _, Sha256};
use trust_cg_codegen::wasm;
use trust_ir::{
    BinOp, CastOp, Constant, Global, ICmpOp, InterpretOptions, InterpretValue, Interpreter,
    Linkage, Ty,
};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

/// The self-naming header the dump MUST carry. The tables are common-mode
/// input to all three spellings of the spec, so an anonymous blob at an
/// arbitrary path is not acceptable provenance: the dump has to say what it
/// is, and say which format version it is in, before a byte of it is believed.
const TABLES_SCHEMA: &str = "aterm.vt-islands.tables";
/// Bump with any change to the dump's shape or field meanings. The generator
/// refuses every other value rather than guessing at a layout.
const TABLES_VERSION: u32 = 1;

/// The DEC ANSI state count. `next_state` is packed into the high byte of a
/// `u16`, so it is bounded here and not merely assumed.
const VT_STATES: usize = 14;
/// The last code point; `wcwidth`'s runs must tile `0..=MAX_CP` exactly.
const MAX_CP: u32 = 0x0010_FFFF;

/// Minimal STRICT parser for the exporter's rigid JSON (a fixed key order,
/// unsigned decimal ints and escape-free strings) — no serde dependency for an
/// example. Strict is the point: the previous spelling scanned forward to the
/// next digit, so a truncated row, a swapped key or a stray `-` resynchronised
/// silently and shifted every following cell. Here every byte outside the
/// grammar panics, naming the offset.
struct P<'a> {
    s: &'a [u8],
    i: usize,
}
impl<'a> P<'a> {
    fn new(s: &'a str) -> Self {
        P {
            s: s.as_bytes(),
            i: 0,
        }
    }
    fn ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() {
            self.i += 1;
        }
    }
    /// Offset plus a short excerpt, for panic messages.
    fn at(&self) -> String {
        let end = (self.i + 24).min(self.s.len());
        format!(
            "offset {} (`{}`)",
            self.i,
            String::from_utf8_lossy(&self.s[self.i..end])
        )
    }
    fn eat(&mut self, ch: u8) -> bool {
        self.ws();
        if self.i < self.s.len() && self.s[self.i] == ch {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, ch: u8) {
        if !self.eat(ch) {
            panic!("tables: expected `{}` at {}", ch as char, self.at());
        }
    }
    /// `"name":`. The dump's key ORDER is part of the format, so keys are
    /// matched in place rather than searched for — a reordered or renamed key
    /// is a refusal, not a silent skip past unrelated bytes.
    fn key(&mut self, name: &str) {
        self.expect(b'"');
        let n = name.as_bytes();
        if self.s.len() < self.i + n.len() + 1
            || &self.s[self.i..self.i + n.len()] != n
            || self.s[self.i + n.len()] != b'"'
        {
            panic!("tables: expected key \"{name}\" at {}", self.at());
        }
        self.i += n.len() + 1;
        self.expect(b':');
    }
    /// A JSON string with NO escapes (the exporter emits none, and accepting
    /// them would mean implementing them).
    fn string(&mut self) -> String {
        self.expect(b'"');
        let start = self.i;
        while self.i < self.s.len() && self.s[self.i] != b'"' {
            if self.s[self.i] == b'\\' {
                panic!("tables: string escapes are not accepted, at {}", self.at());
            }
            self.i += 1;
        }
        if self.i >= self.s.len() {
            panic!("tables: unterminated string from offset {start}");
        }
        let v = String::from_utf8_lossy(&self.s[start..self.i]).into_owned();
        self.i += 1;
        v
    }
    /// A decimal `u32`: at least one digit, no sign, no leading zero, no
    /// overflow. Anything else panics where it stands.
    fn uint(&mut self) -> u32 {
        self.ws();
        let start = self.i;
        while self.i < self.s.len() && self.s[self.i].is_ascii_digit() {
            self.i += 1;
        }
        if self.i == start {
            panic!("tables: expected a decimal integer at {}", self.at());
        }
        let digits = &self.s[start..self.i];
        if digits.len() > 1 && digits[0] == b'0' {
            panic!("tables: integer has a leading zero at offset {start}");
        }
        let mut v: u32 = 0;
        for &d in digits {
            v = v
                .checked_mul(10)
                .and_then(|v| v.checked_add(u32::from(d - b'0')))
                .unwrap_or_else(|| panic!("tables: integer overflows u32 at offset {start}"));
        }
        v
    }
    /// Nothing but whitespace may follow the closing brace.
    fn end(&mut self) {
        self.ws();
        if self.i != self.s.len() {
            panic!("tables: trailing bytes after the object at {}", self.at());
        }
    }
}

/// Lowercase hex SHA-256 of the exact input bytes.
fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut s = String::with_capacity(64);
    for b in digest {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// `(lo, hi, value)` — a contiguous run answering one constant.
type Run = (u32, u32, u32);

fn rle(values: impl Iterator<Item = u32>) -> Vec<Run> {
    let mut runs: Vec<Run> = Vec::new();
    for (i, v) in values.enumerate() {
        let i = i as u32;
        match runs.last_mut() {
            Some((_, hi, val)) if *val == v && *hi + 1 == i => *hi = i,
            _ => runs.push((i, i, v)),
        }
    }
    runs
}

/// Emit a balanced compare tree over contiguous `runs` covering the domain of
/// `probe` (already range-checked by the caller): interior nodes split on
/// `probe < runs[mid].lo`, leaves return their run's constant. Pure code —
/// no memory, no tables. `probe` dominates every generated block, so the
/// blocks carry no params.
fn emit_tree(fb: &mut FunctionBuilder<'_>, probe: trust_ir::ValueId, runs: &[Run]) {
    if runs.len() == 1 {
        let c = fb.iconst(Ty::I32, runs[0].2 as i128);
        fb.ret(vec![c]);
        return;
    }
    let mid = runs.len() / 2;
    let split = fb.iconst(Ty::I32, runs[mid].0 as i32 as i128);
    let below = fb.icmp(ICmpOp::Ult, Ty::I32, probe, split);
    let l = fb.create_block();
    let r = fb.create_block();
    fb.condbr(below, l, vec![], r, vec![]);
    fb.switch_to_block(l);
    emit_tree(fb, probe, &runs[..mid]);
    fb.switch_to_block(r);
    emit_tree(fb, probe, &runs[mid..]);
}

fn build_vt_step(mb: &mut ModuleBuilder, vt: &[Vec<(u32, u32)>]) -> trust_ir::FuncId {
    let sig = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("vt_step", sig);
    let entry = fb.create_block();
    let state = fb.add_block_param(entry, Ty::I32);
    let byte = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let nstates = fb.iconst(Ty::I32, vt.len() as i128);
    let ok = fb.icmp(ICmpOp::Ult, Ty::I32, state, nstates);
    let dispatch = fb.create_block();
    let bad = fb.create_block();
    fb.condbr(ok, dispatch, vec![], bad, vec![]);

    fb.switch_to_block(bad);
    let sentinel = fb.iconst(Ty::I32, 0xFFFF);
    fb.ret(vec![sentinel]);

    // per-state rows as packed (next<<8|action) runs over the masked byte
    fb.switch_to_block(dispatch);
    let mask = fb.iconst(Ty::I32, 255);
    let b = fb.binop(BinOp::And, Ty::I32, byte, mask);
    // balanced tree over the state index, leaves are per-state byte trees
    fn state_tree(
        fb: &mut FunctionBuilder<'_>,
        state: trust_ir::ValueId,
        b: trust_ir::ValueId,
        rows: &[Vec<Run>],
        lo: u32,
    ) {
        if rows.len() == 1 {
            emit_tree(fb, b, &rows[0]);
            return;
        }
        let mid = rows.len() / 2;
        let split = fb.iconst(Ty::I32, (lo + mid as u32) as i128);
        let below = fb.icmp(ICmpOp::Ult, Ty::I32, state, split);
        let l = fb.create_block();
        let r = fb.create_block();
        fb.condbr(below, l, vec![], r, vec![]);
        fb.switch_to_block(l);
        state_tree(fb, state, b, &rows[..mid], lo);
        fb.switch_to_block(r);
        state_tree(fb, state, b, &rows[mid..], lo + mid as u32);
    }
    let rows: Vec<Vec<Run>> = vt
        .iter()
        .map(|row| rle(row.iter().map(|&(n, a)| (n << 8) | a)))
        .collect();
    state_tree(&mut fb, state, b, &rows, 0);
    fb.build()
}

fn build_wcwidth(mb: &mut ModuleBuilder, runs: &[Run]) -> trust_ir::FuncId {
    let sig = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("wcwidth", sig);
    let entry = fb.create_block();
    let cp = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);

    let max = fb.iconst(Ty::I32, i128::from(MAX_CP) + 1);
    let inrange = fb.icmp(ICmpOp::Ult, Ty::I32, cp, max);
    let tree = fb.create_block();
    let beyond = fb.create_block();
    fb.condbr(inrange, tree, vec![], beyond, vec![]);
    fb.switch_to_block(beyond);
    let one = fb.iconst(Ty::I32, 1);
    fb.ret(vec![one]);
    fb.switch_to_block(tree);
    emit_tree(&mut fb, cp, runs);
    fb.build()
}

fn twin_source(vt: &[Vec<(u32, u32)>], runs: &[Run]) -> String {
    let mut s = String::from(
        r#"// GENERATED by trust-cg's examples/wasm_vt_islands.rs — the rustc/LLVM
// twin of the aterm island spec. Table-indexing on purpose: a DIFFERENT
// algorithm than the island's compare trees, same answers. Do not edit.
#![no_std]
// A wasm `unreachable` TRAPS — a panic must fail the differential loudly,
// never hang it (see the canary twin's note).
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

"#,
    );
    let _ = writeln!(s, "static VT: [[u16; 256]; {}] = [", vt.len());
    for row in vt {
        s.push_str("    [");
        for (i, &(n, a)) in row.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            let _ = write!(s, "{}", (n << 8) | a);
        }
        s.push_str("],\n");
    }
    s.push_str("];\n\n");
    let _ = writeln!(s, "static RUNS: [(u32, u32); {}] = [", runs.len());
    for &(lo, _hi, w) in runs {
        let _ = writeln!(s, "    ({lo}, {w}),");
    }
    s.push_str("];\n\n");
    s.push_str(
        r#"#[unsafe(no_mangle)]
pub extern "C" fn vt_step(state: u32, byte: u32) -> u32 {
    if state >= VT.len() as u32 {
        return 0xFFFF;
    }
    VT[state as usize][(byte & 255) as usize] as u32
}

/// The twin's spelling of the island's table-driven export. The twin was
/// always table-driven, so this is the same body under the second name — it
/// exists so the differential can check the island's TWO spellings against a
/// twin under both names rather than silently skipping one.
#[unsafe(no_mangle)]
pub extern "C" fn vt_step_tbl(state: u32, byte: u32) -> u32 {
    vt_step(state, byte)
}

#[unsafe(no_mangle)]
pub extern "C" fn wcwidth(cp: u32) -> u32 {
"#,
    );
    // The domain bound is spelled ONCE, as `MAX_CP`, and printed into the twin
    // from there — the island's compare tree, the reference and this twin are
    // three spellings of one number, and a fourth hand-typed literal is exactly
    // the drift this exhibit exists to catch.
    let _ = writeln!(s, "    if cp > {MAX_CP:#X} {{");
    s.push_str(
        r#"        return 1;
    }
    // binary search for the last run with lo <= cp
    let (mut lo, mut hi) = (0usize, RUNS.len());
    while hi - lo > 1 {
        let mid = (lo + hi) / 2;
        if RUNS[mid].0 <= cp {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    RUNS[lo].1
}
"#,
    );
    s
}

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) as u32
    }
}

/// The TABLE-DRIVEN spelling of `vt_step`, added by P3.
///
/// The compare-tree spelling above is pure code: it exists because the
/// backend had no way to put a table in memory. P3's data segments and
/// `i32.load16_u` remove that constraint, so the same spec can now be
/// written the way the engine itself writes it — a bounds check and one
/// indexed load out of a 14x256 array of packed `u16` cells.
///
/// Both spellings ship in ONE module and the differential checks them
/// against each other over the exhaustive corpus: same compiler, two
/// algorithms, so a bug would have to occur identically in a compare tree
/// and in an indexed load to hide.
fn build_vt_step_table(mb: &mut ModuleBuilder, vt: &[Vec<(u32, u32)>]) -> trust_ir::FuncId {
    // the packed table, little-endian u16 per (state, byte) cell
    let mut image = Vec::with_capacity(vt.len() * 256 * 2);
    for row in vt {
        for &(next, action) in row {
            let packed = ((next << 8) | action) as u16;
            image.extend_from_slice(&packed.to_le_bytes());
        }
    }
    // This generator adds exactly one global, and this is it — asserted
    // against the built module in `main` so the id cannot silently drift.
    let table = trust_ir::value::GlobalId::new(0);
    let image_len = image.len() as u64;
    let u8_ty = mb.add_type(Ty::U8);
    mb.add_global(Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: "VT_TABLE".to_string(),
        ty: Ty::Array(u8_ty, image_len),
        mutable: false,
        initializer: Some(Constant::Bytes {
            data: image,
            utf8: false,
        }),
        linkage: Linkage::Internal,
        tls: None,
        align: Some(2),
    });

    let sig = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("vt_step_tbl", sig);
    let entry = fb.create_block();
    let lookup = fb.create_block();
    let bad = fb.create_block();
    let state = fb.add_block_param(entry, Ty::I32);
    let byte = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let nstates = fb.iconst(Ty::I32, vt.len() as i128);
    let ok = fb.icmp(ICmpOp::Ult, Ty::I32, state, nstates);
    fb.condbr(ok, lookup, vec![], bad, vec![]);

    fb.switch_to_block(bad);
    let sentinel = fb.iconst(Ty::I32, 0xFFFF);
    fb.ret(vec![sentinel]);

    // addr = &VT_TABLE[(state * 256) + (byte & 255)], as a u16-strided GEP:
    // the element stride is the pointee type's, so the lowering — not this
    // generator — owns the *2.
    fb.switch_to_block(lookup);
    let base = fb.global_addr(table);
    let mask = fb.iconst(Ty::I32, 255);
    let b = fb.binop(BinOp::And, Ty::I32, byte, mask);
    let row_stride = fb.iconst(Ty::I32, 256);
    let row = fb.binop(BinOp::Mul, Ty::I32, state, row_stride);
    let cell = fb.binop(BinOp::Add, Ty::I32, row, b);
    let addr = fb.gep(Ty::U16, base, vec![cell]);
    let packed = fb.load(Ty::U16, addr);
    let widened = fb.cast(CastOp::ZExt, Ty::U16, Ty::I32, packed);
    fb.ret(vec![widened]);
    fb.build()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let json_path = args
        .next()
        .expect("usage: wasm_vt_islands <tables.json> <outdir>");
    let out = args
        .next()
        .expect("usage: wasm_vt_islands <tables.json> <outdir>");
    std::fs::create_dir_all(&out).unwrap();
    // Hash the EXACT bytes that are about to be parsed, so `tables_sha256`
    // names the dump this artifact was built from and not a re-serialisation
    // of it.
    let raw = std::fs::read(&json_path).unwrap_or_else(|e| panic!("read {json_path}: {e}"));
    let tables_sha256 = sha256_hex(&raw);
    let text = String::from_utf8(raw).expect("tables: input is not UTF-8");

    // parse the exporter's rigid JSON — strictly, in the format's key order
    let mut p = P::new(&text);
    p.expect(b'{');
    p.key("schema");
    let schema = p.string();
    assert_eq!(
        schema, TABLES_SCHEMA,
        "tables: this dump names itself {schema:?}, not {TABLES_SCHEMA:?}"
    );
    p.expect(b',');
    p.key("version");
    let version = p.uint();
    assert_eq!(
        version, TABLES_VERSION,
        "tables: format version {version} is not the {TABLES_VERSION} this generator reads"
    );
    p.expect(b',');
    p.key("aterm_commit");
    let aterm_commit = p.string();
    // Re-emitted verbatim into the expectations below, so it must be short and
    // printable — the strict string parser already rules out quotes and
    // escapes, which is what keeps that re-emission from being an injection.
    assert!(
        !aterm_commit.is_empty()
            && aterm_commit.len() <= 64
            && aterm_commit.bytes().all(|c| c.is_ascii_graphic()),
        "tables: aterm_commit {aterm_commit:?} is not a printable ASCII revision"
    );
    p.expect(b',');
    p.key("vt");
    p.expect(b'[');
    let mut vt: Vec<Vec<(u32, u32)>> = Vec::new();
    loop {
        p.expect(b'['); // row open
        let mut row = Vec::with_capacity(256);
        loop {
            p.expect(b'[');
            let n = p.uint();
            p.expect(b',');
            let a = p.uint();
            p.expect(b']');
            row.push((n, a));
            if !p.eat(b',') {
                break;
            }
        }
        p.expect(b']'); // row close
        assert_eq!(
            row.len(),
            256,
            "vt row {} has {} cells, want 256",
            vt.len(),
            row.len()
        );
        vt.push(row);
        if !p.eat(b',') {
            break;
        }
    }
    p.expect(b']');
    assert_eq!(
        vt.len(),
        VT_STATES,
        "expected the {VT_STATES}-state DEC ANSI table, got {} rows",
        vt.len()
    );
    // The cell CONTRACT. The island packs `(next << 8) | action` into an i32,
    // but the twin emits the same number as a literal in a `[[u16; 256]; N]`
    // table: a `next` of 256 or an `action` of 4096 does not answer wrong, it
    // emits a twin that rustc REFUSES — and this generator never compiles the
    // twin, so it would report success over an artifact that cannot be built.
    for (s, row) in vt.iter().enumerate() {
        for (b, &(n, a)) in row.iter().enumerate() {
            assert!(
                (n as usize) < VT_STATES,
                "vt[{s}][{b}]: next_state {n} is not a state (< {VT_STATES})"
            );
            assert!(a <= 0xFF, "vt[{s}][{b}]: action {a} does not fit a byte");
            let packed = (n << 8) | a;
            assert!(
                packed <= 0xFFFF,
                "vt[{s}][{b}]: packed {packed:#x} does not fit the twin's u16 table"
            );
            assert_ne!(
                packed, 0xFFFF,
                "vt[{s}][{b}]: packed value collides with the out-of-range sentinel 0xFFFF"
            );
        }
    }

    p.expect(b',');
    p.key("width_runs");
    p.expect(b'[');
    let mut runs: Vec<Run> = Vec::new();
    loop {
        p.expect(b'[');
        let lo = p.uint();
        p.expect(b',');
        let hi = p.uint();
        p.expect(b',');
        let w = p.uint();
        p.expect(b']');
        runs.push((lo, hi, w));
        if !p.eat(b',') {
            break;
        }
    }
    p.expect(b']');
    p.expect(b'}');
    p.end();

    assert!(
        runs.len() > 500,
        "suspiciously few width runs: {}",
        runs.len()
    );
    // The wcwidth CONTRACT. Nothing downstream can catch a violation: the
    // runs feed the island's compare tree, the twin's binary search AND the
    // expectations, so a run answering width 3 — or answering 2 for a
    // surrogate — would make all three spellings agree, unanimously wrong.
    // Walk the domain instead of trusting it: exact ordered tiling of
    // 0..=0x10FFFF, no gap, no overlap, no inverted run, widths in 0..=2, and
    // the documented surrogate policy.
    let mut cursor: u32 = 0;
    for (k, &(lo, hi, w)) in runs.iter().enumerate() {
        assert_eq!(
            lo, cursor,
            "width run {k} starts at {lo:#x}, expected {cursor:#x}: the runs must tile the \
             code-point domain in order, with no gap and no overlap"
        );
        assert!(lo <= hi, "width run {k} is inverted: {lo:#x}..={hi:#x}");
        assert!(hi <= MAX_CP, "width run {k} ends at {hi:#x}, past U+10FFFF");
        assert!(
            w <= 2,
            "width run {k} ({lo:#x}..={hi:#x}) answers width {w}; wcwidth answers 0, 1 or 2"
        );
        // surrogates are not `char`s; the island spec decision is that they
        // answer 1 (see this file's header).
        if lo <= 0xDFFF && hi >= 0xD800 {
            assert_eq!(
                w, 1,
                "width run {k} ({lo:#x}..={hi:#x}) overlaps the surrogate range D800..=DFFF but \
                 answers {w}; the island policy is that surrogates answer 1"
            );
        }
        cursor = hi + 1;
    }
    assert_eq!(
        cursor,
        MAX_CP + 1,
        "width runs stop at {:#x}, short of U+10FFFF",
        cursor.saturating_sub(1)
    );

    let mut mb = ModuleBuilder::new("vt_islands");
    let vt_fid = build_vt_step(&mut mb, &vt);
    let vt_tbl_fid = build_vt_step_table(&mut mb, &vt);
    let wc_fid = build_wcwidth(&mut mb, &runs);
    let mut module = mb
        .build()
        .expect("ModuleBuilder::build: the example module");
    assert_eq!(
        module.globals.len(),
        1,
        "the table island expects exactly one global (the VT table at id 0)"
    );

    let interp = Interpreter::with_module(&module).with_options(InterpretOptions {
        fuel: 1_000_000_000,
        max_call_depth: 16,
        panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
    });
    let run1 = |fid, x: u32| -> u32 {
        let args = vec![InterpretValue::int(Ty::I32, x as i32 as i128).unwrap()];
        interp.execute_func(fid, args).unwrap().returns[0]
            .as_int()
            .unwrap()
            .as_unsigned() as u32
    };
    let run2 = |fid, x: u32, y: u32| -> u32 {
        let args = vec![
            InterpretValue::int(Ty::I32, x as i32 as i128).unwrap(),
            InterpretValue::int(Ty::I32, y as i32 as i128).unwrap(),
        ];
        interp.execute_func(fid, args).unwrap().returns[0]
            .as_int()
            .unwrap()
            .as_unsigned() as u32
    };

    // vt expectations: exhaustive 14x256 + out-of-range states, every one
    // interpreter-checked against the table right here
    let mut vt_in = String::from("\"vt_inputs\":[");
    let mut vt_ex = String::from("\"vt_expected\":[");
    let mut first = true;
    let mut push = |s: u32, b: u32, want: u32, vt_in: &mut String, vt_ex: &mut String| {
        let got = run2(vt_fid, s, b);
        assert_eq!(
            got, want,
            "interp vt_step({s},{b}) = {got}, table says {want}"
        );
        // P3: the SAME spec spelled as an indexed load out of a data segment.
        // A defect would have to occur identically in a generated compare tree
        // and in a memory lookup to survive this.
        let got_tbl = run2(vt_tbl_fid, s, b);
        assert_eq!(
            got_tbl, want,
            "interp vt_step_tbl({s},{b}) = {got_tbl}, table says {want} — the \
             tree and table spellings have drifted"
        );
        if !first {
            vt_in.push(',');
            vt_ex.push(',');
        }
        first = false;
        let _ = write!(vt_in, "[{s},{b}]");
        let _ = write!(vt_ex, "{want}");
    };
    for (s, row) in vt.iter().enumerate() {
        for (b, &(n, a)) in row.iter().enumerate() {
            push(s as u32, b as u32, (n << 8) | a, &mut vt_in, &mut vt_ex);
        }
    }
    for &s in &[14u32, 15, 255, 0xFFFF_FFFF] {
        push(s, 0x41, 0xFFFF, &mut vt_in, &mut vt_ex);
    }
    // byte masking: byte 0x141 behaves as 0x41
    push(
        0,
        0x141,
        {
            let (n, a) = vt[0][0x41];
            (n << 8) | a
        },
        &mut vt_in,
        &mut vt_ex,
    );

    // wcwidth: interpreter spot samples (the page's exhaustive check expands
    // the runs natively); reference derived from the runs
    let width_of = |cp: u32| -> u32 {
        if cp > MAX_CP {
            return 1;
        }
        let ix = runs.partition_point(|r| r.0 <= cp) - 1;
        runs[ix].2
    };
    let mut rng = Lcg(0x13198A2E_03707344); // pi again
    let mut wc_in = String::from("\"width_samples\":[");
    let mut wc_ex = String::from("\"width_expected\":[");
    let mut cps: Vec<u32> = vec![
        0,
        0x1F,
        0x20,
        0x7E,
        0x7F,
        0x80,
        0x300,
        0x1100,
        0x115F,
        0xD7FF,
        0xD800,
        0xDFFF,
        0xE000,
        0xFFFD,
        0x10000,
        0x1F600,
        0x2FFFF,
        0x30000,
        0x323AF,
        0x323B0,
        0x10FFFF,
        0x110000,
        0xFFFF_FFFF,
    ];
    for _ in 0..4096 {
        cps.push(rng.next() % 0x0011_0100);
    }
    for (k, &cp) in cps.iter().enumerate() {
        let want = width_of(cp);
        let got = run1(wc_fid, cp);
        assert_eq!(
            got, want,
            "interp wcwidth({cp:#x}) = {got}, runs say {want}"
        );
        if k > 0 {
            wc_in.push(',');
            wc_ex.push(',');
        }
        let _ = write!(wc_in, "{cp}");
        let _ = write!(wc_ex, "{want}");
    }

    let mut runs_json = String::from("\"width_runs\":[");
    for (k, &(lo, hi, w)) in runs.iter().enumerate() {
        if k > 0 {
            runs_json.push(',');
        }
        let _ = write!(runs_json, "[{lo},{hi},{w}]");
    }
    runs_json.push(']');

    // `tables_sha256` first: a shipped expectations file names the exact table
    // dump it was generated from, so an artifact can be traced back to one
    // byte-identical input instead of to "whatever the exporter emitted that
    // day".
    let provenance = format!(
        "\"tables_schema\":\"{TABLES_SCHEMA}\",\"tables_version\":{TABLES_VERSION},\
         \"tables_sha256\":\"{tables_sha256}\",\"aterm_commit\":\"{aterm_commit}\""
    );
    let json = format!("{{{provenance},{vt_in}],{vt_ex}],{wc_in}],{wc_ex}],{runs_json}}}");

    // compile_module fail-closes on target-free modules; the interpreter above
    // fail-closes the other way (reference execution wants the canonical
    // 64-bit layout), so the wasm32 pin is stamped after interpretation.
    module.target_info = Some(wasm::wasm32_target_info());
    let bytes = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("compile_module");
    let _ = wc_fid;
    std::fs::File::create(format!("{out}/vt_islands.wasm"))
        .unwrap()
        .write_all(&bytes)
        .unwrap();
    std::fs::File::create(format!("{out}/vt_islands_twin.rs"))
        .unwrap()
        .write_all(twin_source(&vt, &runs).as_bytes())
        .unwrap();
    std::fs::File::create(format!("{out}/vt_islands_expected.json"))
        .unwrap()
        .write_all(json.as_bytes())
        .unwrap();
    eprintln!(
        "vt islands: {} bytes of wasm ({} width runs, {} vt rows), twin + expectations written to \
         {out}/ from tables sha256:{tables_sha256} (aterm {aterm_commit})",
        bytes.len(),
        runs.len(),
        vt.len()
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
