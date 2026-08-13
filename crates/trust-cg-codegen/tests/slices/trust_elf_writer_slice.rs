// Trust-toolchain slice — the trust-cg ELF64 OBJECT-WRITER byte machinery, the
// field-packing + fixed-layout struct encoders/decoders, transcribed VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 30, TRUST BATCH 17).
//
// EMIT: README recipe + `-C overflow-checks=off -C debug-assertions=off` (the byte
// sink/source uses lossy narrowing `as` truncations `(x >> 8) as u8`; on the swept
// domain they never overflow, but the flags keep the emit byte-identical). One emit
// per `#[no_mangle]` root.
//
// SURFACE: the ELF64 relocatable-object writer (`elf/constants.rs`, `elf/symbol.rs`,
// `elf/reloc.rs`, `elf/header.rs`). A wrong bit in a field-packing or a wrong byte
// offset produces a MALFORMED `.o` the system linker mis-links or rejects. The
// functions here are the pure, scalar-shaped bit-packers and fixed-layout
// encoders/decoders:
//
//   FIELD PACK/EXTRACT (constants.rs — the classic ELF field-packing bug sites):
//     * `elf64_st_info(bind,typ)`  — constants.rs:324  ((bind<<4)|(typ&0xf))
//     * `elf64_st_bind(info)`      — constants.rs:329  (info>>4)
//     * `elf64_st_type(info)`      — constants.rs:334  (info&0xf)
//     * `elf64_r_info(sym,typ)`    — constants.rs:339  (((sym as u64)<<32)|(typ as u64))
//     * `elf64_r_sym(info)`        — constants.rs:344  ((info>>32) as u32)
//     * `elf64_r_type(info)`       — constants.rs:349  (info as u32)
//   FIXED-LAYOUT ENCODE/DECODE (24-byte entries; encode<->decode are matched pairs):
//     * `Elf64Sym::new`    — symbol.rs:57   (calls elf64_st_info)
//     * `Elf64Sym::encode` — symbol.rs:77   (24-byte Elf64_Sym, LE field layout)
//     * `Elf64Sym::decode` — symbol.rs:89   (inverse)
//     * `Elf64Rela::new`     — reloc.rs:266
//     * `Elf64Rela::r_info`  — reloc.rs:291 (calls elf64_r_info)
//     * `Elf64Rela::encode`  — reloc.rs:296 (24-byte Elf64_Rela, LE field layout)
//     * `Elf64Rela::decode`  — reloc.rs:305 (inverse; r_info split back via r_sym/r_type)
//   HEADER (header.rs — the ELF ident/magic + e_type/e_machine field encoder):
//     * `ElfMachine::to_e_machine` — header.rs:27 (AArch64->183 / X86_64->62 / Riscv64->243)
//     * `Elf64Header::write`       — header.rs:84 (64-byte Elf64_Ehdr, magic 0x7f"ELF" + fields)
//
// THE ROUND'S POWER — up to FOUR independent oracles per value:
//   (1) native==JIT: the verbatim slice, compiled by native rustc, must equal the JIT.
//   (2) LINKED PRODUCTION (second oracle): every fn above is PUBLIC and linked into the
//       test binary (`trust_cg_codegen::elf::{constants::*, symbol::Elf64Sym,
//       reloc::Elf64Rela, header::{Elf64Header,ElfMachine}}`); the JIT output is checked
//       byte-for-byte against the REAL functions run on the same inputs.
//   (3) ENCODE<->DECODE ROUND-TRIP: decode(encode(x)) == x over swept field values, and
//       extract(pack(a,b)) == (a,b) for st_info/r_info. An encoder/decoder ASYMMETRY is a
//       REAL bug (a malformed .o). The 32-bit boundary of r_info ((sym<<32)|type) is the
//       classic bug site (swept at sym {0,1,0x7fffffff,0xffffffff}).
//   (4) ELF-SPEC BYTE LAYOUT: the exact Elf64_Sym / Elf64_Rela / Elf64_Ehdr byte offsets
//       vs the System-V ELF-64 spec (st_name at [0..4] LE, st_info at [4], st_value at
//       [8..16] LE, ...; ELF64_SYM_SIZE=24; r_info=(sym<<32)|type; ident magic 0x7f454c46,
//       EI_CLASS=2, EI_DATA=1) — catches a bug even if encode+decode share the same mistake.
//
// MODELED BOUNDARY (documented honestly):
//   A. BYTE SINK / SOURCE. Production `encode` writes a `[u8; 24]` via
//      `buf[a..b].copy_from_slice(&field.to_le_bytes())`; `decode` reads it back via
//      `u32::from_le_bytes([bytes[0], bytes[1], ...])`. Both `to_le_bytes`/`from_le_bytes`
//      lower to EMPTY extern leaves (the R21/R27 [F4] class — unresolved at JIT link), and
//      slice `copy_from_slice` likewise. So each `copy_from_slice(&x.to_le_bytes())` is
//      rewritten to the explicit per-byte little-endian STORES it performs at the SAME
//      byte offsets (`buf[k] = (x >> (8*i)) as u8`), and each `from_le_bytes` to the
//      explicit shift-OR reconstruct it performs — byte-identical output, offsets literal
//      (so the spec-oracle still checks the layout). The single-byte fields
//      (`buf[4] = self.st_info`, `bytes[4]` etc.) stay VERBATIM. This is the R28/R29
//      LEB128/wasm byte-sink discipline (the manual `[u8;N]` fill + array-by-ref index
//      lower with no extern leaves; probed before writing this slice). The `Elf64Header`
//      `Vec<u8>` sink is modeled as a `[u8; 64]` array + append cursor (append ORDER =
//      byte offset, exactly as the production sequential `extend_from_slice`s); the
//      `ident: [u8;16]` local array + per-index magic writes stay VERBATIM.
//   B. ABI ADAPTERS. u8/u16 fields cross the FFI boundary as u32 (widened, value-identical);
//      the `[u8;24]`/`[u8;64]` buffers cross as fixed u64 words (LE-packed). The
//      `#[unsafe(no_mangle)]` roots are harness adapters (NOT production): each builds the
//      production struct, runs the verbatim callee, and packs the result into a scalar POD.
//
// Everything else is byte-for-byte from elf/constants.rs / elf/symbol.rs / elf/reloc.rs /
// elf/header.rs (compare against those four files).

#![allow(dead_code)]

// ── ELF constants (VERBATIM, elf/constants.rs) ──────────────────────────────
const ELFMAG0: u8 = 0x7f;
const ELFMAG1: u8 = b'E';
const ELFMAG2: u8 = b'L';
const ELFMAG3: u8 = b'F';
const ELFCLASS64: u8 = 2;
const ELFDATA2LSB: u8 = 1;
const EV_CURRENT: u8 = 1;
const ELFOSABI_NONE: u8 = 0;
const EI_NIDENT: usize = 16;
const ET_REL: u16 = 1;
const EM_X86_64: u16 = 62;
const EM_AARCH64: u16 = 183;
const EM_RISCV: u16 = 243;
const ELF64_EHDR_SIZE: usize = 64;
const ELF64_SHDR_SIZE: usize = 64;
const ELF64_SYM_SIZE: usize = 24;
const ELF64_RELA_SIZE: usize = 24;

// ── FIELD PACK/EXTRACT (VERBATIM, elf/constants.rs:324-351) ─────────────────

/// Encode st_info from binding and type.  [constants.rs:324]
fn elf64_st_info(bind: u8, typ: u8) -> u8 {
    (bind << 4) | (typ & 0xf)
}

/// Extract binding from st_info.  [constants.rs:329]
fn elf64_st_bind(info: u8) -> u8 {
    info >> 4
}

/// Extract type from st_info.  [constants.rs:334]
fn elf64_st_type(info: u8) -> u8 {
    info & 0xf
}

/// Encode r_info from symbol index and relocation type.  [constants.rs:339]
fn elf64_r_info(sym: u32, typ: u32) -> u64 {
    ((sym as u64) << 32) | (typ as u64)
}

/// Extract symbol index from r_info.  [constants.rs:344]
fn elf64_r_sym(info: u64) -> u32 {
    (info >> 32) as u32
}

/// Extract relocation type from r_info.  [constants.rs:349]
fn elf64_r_type(info: u64) -> u32 {
    info as u32
}

// ── Elf64Sym (VERBATIM struct + new; encode/decode per boundary A) ──────────

/// A single ELF64 symbol table entry (Elf64_Sym).  [symbol.rs:28]
#[derive(Clone)]
struct Elf64Sym {
    st_name: u32,
    st_info: u8,
    st_other: u8,
    st_shndx: u16,
    st_value: u64,
    st_size: u64,
}

impl Elf64Sym {
    /// Create a symbol with the given attributes.  [symbol.rs:57]
    fn new(
        st_name: u32,
        binding: u8,
        sym_type: u8,
        visibility: u8,
        section_index: u16,
        value: u64,
        size: u64,
    ) -> Self {
        Self {
            st_name,
            st_info: elf64_st_info(binding, sym_type),
            st_other: visibility,
            st_shndx: section_index,
            st_value: value,
            st_size: size,
        }
    }

    /// Encode this symbol entry to its 24-byte little-endian representation.  [symbol.rs:77]
    fn encode(&self) -> [u8; ELF64_SYM_SIZE] {
        let mut buf = [0u8; ELF64_SYM_SIZE];
        // buf[0..4].copy_from_slice(&self.st_name.to_le_bytes());  [boundary A]
        // (the u32/u16 LE split is computed in u64 space to sidestep [F3]: the frontend
        // does not normalize a shift-amount const to a 32-bit LHS; `x as u64 >> k` is
        // byte-identical to the low-byte-of `x >> k` for the low 4/2 bytes.)
        let name = self.st_name as u64;
        buf[0] = name as u8;
        buf[1] = (name >> 8) as u8;
        buf[2] = (name >> 16) as u8;
        buf[3] = (name >> 24) as u8;
        buf[4] = self.st_info;
        buf[5] = self.st_other;
        // buf[6..8].copy_from_slice(&self.st_shndx.to_le_bytes());  [boundary A]
        let shndx = self.st_shndx as u64;
        buf[6] = shndx as u8;
        buf[7] = (shndx >> 8) as u8;
        // buf[8..16].copy_from_slice(&self.st_value.to_le_bytes());  [boundary A]
        buf[8] = self.st_value as u8;
        buf[9] = (self.st_value >> 8) as u8;
        buf[10] = (self.st_value >> 16) as u8;
        buf[11] = (self.st_value >> 24) as u8;
        buf[12] = (self.st_value >> 32) as u8;
        buf[13] = (self.st_value >> 40) as u8;
        buf[14] = (self.st_value >> 48) as u8;
        buf[15] = (self.st_value >> 56) as u8;
        // buf[16..24].copy_from_slice(&self.st_size.to_le_bytes());  [boundary A]
        buf[16] = self.st_size as u8;
        buf[17] = (self.st_size >> 8) as u8;
        buf[18] = (self.st_size >> 16) as u8;
        buf[19] = (self.st_size >> 24) as u8;
        buf[20] = (self.st_size >> 32) as u8;
        buf[21] = (self.st_size >> 40) as u8;
        buf[22] = (self.st_size >> 48) as u8;
        buf[23] = (self.st_size >> 56) as u8;
        buf
    }

    /// Decode a symbol entry from its 24-byte little-endian representation.  [symbol.rs:89]
    fn decode(bytes: &[u8; ELF64_SYM_SIZE]) -> Self {
        Self {
            // u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])  [boundary A]
            // (reconstructed in u64 space then narrowed — byte-identical, sidesteps [F3]).
            st_name: ((bytes[0] as u64)
                | ((bytes[1] as u64) << 8)
                | ((bytes[2] as u64) << 16)
                | ((bytes[3] as u64) << 24)) as u32,
            st_info: bytes[4],
            st_other: bytes[5],
            // u16::from_le_bytes([bytes[6], bytes[7]])  [boundary A]
            st_shndx: ((bytes[6] as u64) | ((bytes[7] as u64) << 8)) as u16,
            // u64::from_le_bytes([bytes[8..16]])  [boundary A]
            st_value: (bytes[8] as u64)
                | ((bytes[9] as u64) << 8)
                | ((bytes[10] as u64) << 16)
                | ((bytes[11] as u64) << 24)
                | ((bytes[12] as u64) << 32)
                | ((bytes[13] as u64) << 40)
                | ((bytes[14] as u64) << 48)
                | ((bytes[15] as u64) << 56),
            // u64::from_le_bytes([bytes[16..24]])  [boundary A]
            st_size: (bytes[16] as u64)
                | ((bytes[17] as u64) << 8)
                | ((bytes[18] as u64) << 16)
                | ((bytes[19] as u64) << 24)
                | ((bytes[20] as u64) << 32)
                | ((bytes[21] as u64) << 40)
                | ((bytes[22] as u64) << 48)
                | ((bytes[23] as u64) << 56),
        }
    }
}

// ── Elf64Rela (VERBATIM struct + new + r_info; encode/decode per boundary A) ─

/// An ELF64 relocation entry with addend (Elf64_Rela).  [reloc.rs:253]
#[derive(Clone)]
struct Elf64Rela {
    r_offset: u64,
    symbol_index: u32,
    reloc_type: u32,
    r_addend: i64,
}

impl Elf64Rela {
    /// Create a new relocation entry.  [reloc.rs:266]
    fn new(offset: u64, symbol_index: u32, reloc_type: u32, addend: i64) -> Self {
        Self {
            r_offset: offset,
            symbol_index,
            reloc_type,
            r_addend: addend,
        }
    }

    /// Compute the packed r_info field.  [reloc.rs:291]
    fn r_info(&self) -> u64 {
        elf64_r_info(self.symbol_index, self.reloc_type)
    }

    /// Encode to 24-byte little-endian representation.  [reloc.rs:296]
    fn encode(&self) -> [u8; ELF64_RELA_SIZE] {
        let mut buf = [0u8; ELF64_RELA_SIZE];
        // buf[0..8].copy_from_slice(&self.r_offset.to_le_bytes());  [boundary A]
        buf[0] = self.r_offset as u8;
        buf[1] = (self.r_offset >> 8) as u8;
        buf[2] = (self.r_offset >> 16) as u8;
        buf[3] = (self.r_offset >> 24) as u8;
        buf[4] = (self.r_offset >> 32) as u8;
        buf[5] = (self.r_offset >> 40) as u8;
        buf[6] = (self.r_offset >> 48) as u8;
        buf[7] = (self.r_offset >> 56) as u8;
        // buf[8..16].copy_from_slice(&self.r_info().to_le_bytes());  [boundary A]
        let info = self.r_info();
        buf[8] = info as u8;
        buf[9] = (info >> 8) as u8;
        buf[10] = (info >> 16) as u8;
        buf[11] = (info >> 24) as u8;
        buf[12] = (info >> 32) as u8;
        buf[13] = (info >> 40) as u8;
        buf[14] = (info >> 48) as u8;
        buf[15] = (info >> 56) as u8;
        // buf[16..24].copy_from_slice(&self.r_addend.to_le_bytes());  [boundary A]
        let ad = self.r_addend as u64; // i64::to_le_bytes has identical byte pattern
        buf[16] = ad as u8;
        buf[17] = (ad >> 8) as u8;
        buf[18] = (ad >> 16) as u8;
        buf[19] = (ad >> 24) as u8;
        buf[20] = (ad >> 32) as u8;
        buf[21] = (ad >> 40) as u8;
        buf[22] = (ad >> 48) as u8;
        buf[23] = (ad >> 56) as u8;
        buf
    }

    /// Decode from 24-byte little-endian representation.  [reloc.rs:305]
    fn decode(bytes: &[u8; ELF64_RELA_SIZE]) -> Self {
        // u64::from_le_bytes([bytes[0..8]])  [boundary A]
        let r_offset = (bytes[0] as u64)
            | ((bytes[1] as u64) << 8)
            | ((bytes[2] as u64) << 16)
            | ((bytes[3] as u64) << 24)
            | ((bytes[4] as u64) << 32)
            | ((bytes[5] as u64) << 40)
            | ((bytes[6] as u64) << 48)
            | ((bytes[7] as u64) << 56);
        // u64::from_le_bytes([bytes[8..16]])  [boundary A]
        let r_info = (bytes[8] as u64)
            | ((bytes[9] as u64) << 8)
            | ((bytes[10] as u64) << 16)
            | ((bytes[11] as u64) << 24)
            | ((bytes[12] as u64) << 32)
            | ((bytes[13] as u64) << 40)
            | ((bytes[14] as u64) << 48)
            | ((bytes[15] as u64) << 56);
        // i64::from_le_bytes([bytes[16..24]])  [boundary A]
        let r_addend = ((bytes[16] as u64)
            | ((bytes[17] as u64) << 8)
            | ((bytes[18] as u64) << 16)
            | ((bytes[19] as u64) << 24)
            | ((bytes[20] as u64) << 32)
            | ((bytes[21] as u64) << 40)
            | ((bytes[22] as u64) << 48)
            | ((bytes[23] as u64) << 56)) as i64;

        Self {
            r_offset,
            symbol_index: elf64_r_sym(r_info),
            reloc_type: elf64_r_type(r_info),
            r_addend,
        }
    }
}

// ── ElfMachine + Elf64Header (VERBATIM; Vec<u8> sink -> [u8;64] per boundary A) ─

/// Target machine architecture for the ELF file.  [header.rs:16]
#[derive(Clone, Copy)]
enum ElfMachine {
    AArch64,
    X86_64,
    Riscv64,
}

impl ElfMachine {
    /// Return the ELF e_machine value for this architecture.  [header.rs:27]
    fn to_e_machine(self) -> u16 {
        match self {
            ElfMachine::AArch64 => EM_AARCH64,
            ElfMachine::X86_64 => EM_X86_64,
            ElfMachine::Riscv64 => EM_RISCV,
        }
    }
}

/// ELF64 file header (Elf64_Ehdr).  [header.rs:58]
struct Elf64Header {
    machine: ElfMachine,
    sh_offset: u64,
    sh_num: u16,
    sh_strndx: u16,
    flags: u32,
}

// MODELED (boundary A): the `Vec<u8>` sink -> a [u8; 64] array + append cursor.
// `push(b)` models `Vec::push`; `push_uN_le` models `extend_from_slice(&x.to_le_bytes())`;
// `extend16` models `extend_from_slice(&ident)`. Append ORDER == byte offset == the ELF
// spec layout, exactly as the production sequential `extend_from_slice`s.
struct Ehdr {
    buf: [u8; ELF64_EHDR_SIZE],
    len: usize,
}

impl Ehdr {
    fn new() -> Self {
        Ehdr {
            buf: [0u8; ELF64_EHDR_SIZE],
            len: 0,
        }
    }
    fn push(&mut self, b: u8) {
        self.buf[self.len] = b;
        self.len += 1;
    }
    fn extend16(&mut self, a: &[u8; EI_NIDENT]) {
        let mut i = 0usize;
        while i < EI_NIDENT {
            self.push(a[i]);
            i += 1;
        }
    }
    // (u16/u32 LE splits computed in u64 space — byte-identical, sidesteps [F3].)
    fn push_u16_le(&mut self, v: u16) {
        let x = v as u64;
        self.push(x as u8);
        self.push((x >> 8) as u8);
    }
    fn push_u32_le(&mut self, v: u32) {
        let x = v as u64;
        self.push(x as u8);
        self.push((x >> 8) as u8);
        self.push((x >> 16) as u8);
        self.push((x >> 24) as u8);
    }
    fn push_u64_le(&mut self, v: u64) {
        self.push(v as u8);
        self.push((v >> 8) as u8);
        self.push((v >> 16) as u8);
        self.push((v >> 24) as u8);
        self.push((v >> 32) as u8);
        self.push((v >> 40) as u8);
        self.push((v >> 48) as u8);
        self.push((v >> 56) as u8);
    }
}

impl Elf64Header {
    /// Serialize the ELF64 header to bytes (little-endian, 64 bytes).  [header.rs:84]
    fn write(&self, out: &mut Ehdr) {
        // e_ident[0..16]
        let mut ident = [0u8; EI_NIDENT];
        ident[0] = ELFMAG0; // 0x7f
        ident[1] = ELFMAG1; // 'E'
        ident[2] = ELFMAG2; // 'L'
        ident[3] = ELFMAG3; // 'F'
        ident[4] = ELFCLASS64; // 64-bit
        ident[5] = ELFDATA2LSB; // Little-endian
        ident[6] = EV_CURRENT; // ELF version 1
        ident[7] = ELFOSABI_NONE; // UNIX System V
        // ident[8..16] = 0 (padding)
        out.extend16(&ident); // out.extend_from_slice(&ident)

        // e_type: ET_REL
        out.push_u16_le(ET_REL);
        // e_machine
        out.push_u16_le(self.machine.to_e_machine());
        // e_version
        out.push_u32_le(EV_CURRENT as u32);
        // e_entry (0 for relocatable objects)
        out.push_u64_le(0);
        // e_phoff (0 for relocatable objects — no program header table)
        out.push_u64_le(0);
        // e_shoff
        out.push_u64_le(self.sh_offset);
        // e_flags
        out.push_u32_le(self.flags);
        // e_ehsize
        out.push_u16_le(ELF64_EHDR_SIZE as u16);
        // e_phentsize (0 — no program headers)
        out.push_u16_le(0);
        // e_phnum (0)
        out.push_u16_le(0);
        // e_shentsize
        out.push_u16_le(ELF64_SHDR_SIZE as u16);
        // e_shnum
        out.push_u16_le(self.sh_num);
        // e_shstrndx
        out.push_u16_le(self.sh_strndx);
    }
}

// ── harness adapter roots (NOT production) ──────────────────────────────────

#[repr(C)]
pub struct StInfoOut {
    pub info: u32,
    pub bind_out: u32,
    pub type_out: u32,
}

#[repr(C)]
pub struct RInfoOut {
    pub info: u64,
    pub sym_out: u32,
    pub type_out: u32,
}

#[repr(C)]
pub struct SymEncOut {
    pub w0: u64,
    pub w1: u64,
    pub w2: u64,
}

#[repr(C)]
pub struct SymDecOut {
    pub st_name: u32,
    pub st_info: u32,
    pub st_other: u32,
    pub st_shndx: u32,
    pub st_value: u64,
    pub st_size: u64,
}

#[repr(C)]
pub struct RelaEncOut {
    pub w0: u64,
    pub w1: u64,
    pub w2: u64,
}

#[repr(C)]
pub struct RelaDecOut {
    pub r_offset: u64,
    pub r_info: u64,
    pub symbol_index: u32,
    pub reloc_type: u32,
    pub r_addend: i64,
}

#[repr(C)]
pub struct HdrOut {
    pub w0: u64,
    pub w1: u64,
    pub w2: u64,
    pub w3: u64,
    pub w4: u64,
    pub w5: u64,
    pub w6: u64,
    pub w7: u64,
}

// pack the low 8 bytes of a [u8;N] window into a u64 (LE).
#[allow(clippy::too_many_arguments)] // Mirrors the eight independent byte lanes.
fn pack8(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8) -> u64 {
    (b0 as u64)
        | ((b1 as u64) << 8)
        | ((b2 as u64) << 16)
        | ((b3 as u64) << 24)
        | ((b4 as u64) << 32)
        | ((b5 as u64) << 40)
        | ((b6 as u64) << 48)
        | ((b7 as u64) << 56)
}

#[unsafe(no_mangle)]
pub extern "C" fn st_info_root(bind: u32, typ: u32, out: *mut StInfoOut) {
    let info = elf64_st_info(bind as u8, typ as u8);
    let bind_out = elf64_st_bind(info);
    let type_out = elf64_st_type(info);
    unsafe {
        (*out).info = info as u32;
        (*out).bind_out = bind_out as u32;
        (*out).type_out = type_out as u32;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn r_info_root(sym: u32, typ: u32, out: *mut RInfoOut) {
    let info = elf64_r_info(sym, typ);
    let sym_out = elf64_r_sym(info);
    let type_out = elf64_r_type(info);
    unsafe {
        (*out).info = info;
        (*out).sym_out = sym_out;
        (*out).type_out = type_out;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn sym_enc_root(
    st_name: u32,
    binding: u32,
    sym_type: u32,
    visibility: u32,
    section_index: u32,
    value: u64,
    size: u64,
    out: *mut SymEncOut,
) {
    let sym = Elf64Sym::new(
        st_name,
        binding as u8,
        sym_type as u8,
        visibility as u8,
        section_index as u16,
        value,
        size,
    );
    let b = sym.encode();
    unsafe {
        (*out).w0 = pack8(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
        (*out).w1 = pack8(b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15]);
        (*out).w2 = pack8(b[16], b[17], b[18], b[19], b[20], b[21], b[22], b[23]);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn sym_dec_root(w0: u64, w1: u64, w2: u64, out: *mut SymDecOut) {
    let mut bytes = [0u8; ELF64_SYM_SIZE];
    let mut i = 0usize;
    while i < 8 {
        bytes[i] = (w0 >> (8 * i)) as u8;
        bytes[i + 8] = (w1 >> (8 * i)) as u8;
        bytes[i + 16] = (w2 >> (8 * i)) as u8;
        i += 1;
    }
    let sym = Elf64Sym::decode(&bytes);
    unsafe {
        (*out).st_name = sym.st_name;
        (*out).st_info = sym.st_info as u32;
        (*out).st_other = sym.st_other as u32;
        (*out).st_shndx = sym.st_shndx as u32;
        (*out).st_value = sym.st_value;
        (*out).st_size = sym.st_size;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rela_enc_root(
    offset: u64,
    symbol_index: u32,
    reloc_type: u32,
    addend: i64,
    out: *mut RelaEncOut,
) {
    let rela = Elf64Rela::new(offset, symbol_index, reloc_type, addend);
    let b = rela.encode();
    unsafe {
        (*out).w0 = pack8(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
        (*out).w1 = pack8(b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15]);
        (*out).w2 = pack8(b[16], b[17], b[18], b[19], b[20], b[21], b[22], b[23]);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rela_dec_root(w0: u64, w1: u64, w2: u64, out: *mut RelaDecOut) {
    let mut bytes = [0u8; ELF64_RELA_SIZE];
    let mut i = 0usize;
    while i < 8 {
        bytes[i] = (w0 >> (8 * i)) as u8;
        bytes[i + 8] = (w1 >> (8 * i)) as u8;
        bytes[i + 16] = (w2 >> (8 * i)) as u8;
        i += 1;
    }
    let rela = Elf64Rela::decode(&bytes);
    unsafe {
        (*out).r_offset = rela.r_offset;
        (*out).r_info = rela.r_info();
        (*out).symbol_index = rela.symbol_index;
        (*out).reloc_type = rela.reloc_type;
        (*out).r_addend = rela.r_addend;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn header_root(
    machine_tag: u32,
    sh_offset: u64,
    sh_num: u32,
    sh_strndx: u32,
    out: *mut HdrOut,
) {
    let machine = if machine_tag == 0 {
        ElfMachine::AArch64
    } else if machine_tag == 1 {
        ElfMachine::X86_64
    } else {
        ElfMachine::Riscv64
    };
    let header = Elf64Header {
        machine,
        sh_offset,
        sh_num: sh_num as u16,
        sh_strndx: sh_strndx as u16,
        flags: 0,
    };
    let mut eh = Ehdr::new();
    header.write(&mut eh);
    let b = eh.buf;
    unsafe {
        (*out).w0 = pack8(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
        (*out).w1 = pack8(b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15]);
        (*out).w2 = pack8(b[16], b[17], b[18], b[19], b[20], b[21], b[22], b[23]);
        (*out).w3 = pack8(b[24], b[25], b[26], b[27], b[28], b[29], b[30], b[31]);
        (*out).w4 = pack8(b[32], b[33], b[34], b[35], b[36], b[37], b[38], b[39]);
        (*out).w5 = pack8(b[40], b[41], b[42], b[43], b[44], b[45], b[46], b[47]);
        (*out).w6 = pack8(b[48], b[49], b[50], b[51], b[52], b[53], b[54], b[55]);
        (*out).w7 = pack8(b[56], b[57], b[58], b[59], b[60], b[61], b[62], b[63]);
    }
}

fn main() {
    let mut o = StInfoOut {
        info: 0,
        bind_out: 0,
        type_out: 0,
    };
    st_info_root(1, 2, &mut o);
    println!(
        "st_info(1,2) = {} bind={} type={}",
        o.info, o.bind_out, o.type_out
    );

    let mut r = RInfoOut {
        info: 0,
        sym_out: 0,
        type_out: 0,
    };
    r_info_root(0x12345678, 257, &mut r);
    println!(
        "r_info = {:#x} sym={:#x} type={}",
        r.info, r.sym_out, r.type_out
    );
}
