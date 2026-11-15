// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A clean-room `__eh_frame` / `.eh_frame` decoder and CFA-program
//! interpreter.
//!
//! Written from the LSB `.eh_frame` layout and DWARF 5 section 6.4 (call
//! frame information), not from trust-cg's CFI emitter
//! (`trust-cg-codegen/src/dwarf_cfi.rs`) or its round-trip gate
//! (`dwarf_cfi_decode_check.rs`, which compares bytes with the emitter's
//! intent and never interprets a program). This module runs each FDE's
//! program to the rows an unwinder would use, so the obligations can compare
//! a row with the machine state at a code offset.

use std::collections::BTreeMap;

use super::lsda::Reader;
use super::macho::Term;
use super::{EhObligationKind, Violation};

fn cfi_error(detail: impl Into<String>) -> Violation {
    Violation::object(EhObligationKind::CfiStructure, detail)
}

/// Resolves the pointer field at section offset `at` under `DW_EH_PE`
/// encoding `encoding`, returning the target and the field's width.
pub(crate) type PointerResolver<'r> = dyn Fn(usize, u8) -> Result<(Term, usize), Violation> + 'r;

/// The width of a pointer field under `encoding` (format nibble).
pub(crate) fn pointer_width(encoding: u8) -> Result<usize, Violation> {
    match encoding & 0x0f {
        0x00 | 0x04 | 0x0c => Ok(8),
        0x03 | 0x0b => Ok(4),
        0x02 | 0x0a => Ok(2),
        other => Err(cfi_error(format!(
            "pointer format {other:#x} (encoding {encoding:#04x}) is outside the admitted fixed-width forms"
        ))),
    }
}

/// One CIE.
#[derive(Debug, Clone)]
pub(crate) struct Cie {
    pub(crate) code_align: u64,
    pub(crate) data_align: i64,
    pub(crate) ra_register: u64,
    pub(crate) augmentation: String,
    pub(crate) personality: Option<Term>,
    pub(crate) lsda_encoding: Option<u8>,
    pub(crate) fde_encoding: u8,
    pub(crate) initial: Vec<u8>,
}

/// One FDE.
#[derive(Debug, Clone)]
pub(crate) struct Fde {
    pub(crate) offset: usize,
    pub(crate) cie: usize,
    pub(crate) pc_begin: Term,
    pub(crate) pc_range: u64,
    pub(crate) lsda: Option<Term>,
    pub(crate) instructions: Vec<u8>,
}

/// A decoded `.eh_frame` section.
#[derive(Debug, Clone, Default)]
pub(crate) struct EhFrame {
    pub(crate) cies: Vec<Cie>,
    pub(crate) fdes: Vec<Fde>,
}

impl EhFrame {
    /// Decode every entry of `bytes`. A zero-length entry is the optional
    /// terminator; nothing may follow it.
    pub(crate) fn decode(bytes: &[u8], pointer: &PointerResolver<'_>) -> Result<Self, Violation> {
        let mut frame = Self::default();
        let mut cie_by_offset = BTreeMap::new();
        let mut at = 0usize;
        while at < bytes.len() {
            let mut reader = Reader::new(bytes, at);
            let length = reader
                .fixed(4)
                .map_err(|_| cfi_error("truncated entry length"))?;
            if length == 0 {
                if reader.pos != bytes.len() {
                    return Err(cfi_error(format!(
                        "bytes follow the zero terminator at {at}"
                    )));
                }
                break;
            }
            if length == 0xffff_ffff {
                return Err(cfi_error("64-bit DWARF entries are not admitted"));
            }
            let body_start = reader.pos;
            let end = usize::try_from(length)
                .ok()
                .and_then(|length| body_start.checked_add(length))
                .filter(|&end| end <= bytes.len())
                .ok_or_else(|| cfi_error(format!("entry at {at} overruns the section")))?;
            let id_at = reader.pos;
            let id = reader.fixed(4)?;
            if id == 0 {
                let cie = decode_cie(bytes, at, reader.pos, end, pointer)?;
                cie_by_offset.insert(at, frame.cies.len());
                frame.cies.push(cie);
            } else {
                let cie_offset = id_at
                    .checked_sub(id as usize)
                    .ok_or_else(|| cfi_error(format!("FDE at {at} points before the section")))?;
                let cie_index = *cie_by_offset.get(&cie_offset).ok_or_else(|| {
                    cfi_error(format!(
                        "FDE at {at} names CIE offset {cie_offset}, which is not a preceding CIE"
                    ))
                })?;
                let cie = &frame.cies[cie_index];
                let fde = decode_fde(bytes, at, reader.pos, end, cie, cie_index, pointer)?;
                frame.fdes.push(fde);
            }
            at = end;
        }
        Ok(frame)
    }
}

fn decode_cie(
    bytes: &[u8],
    at: usize,
    pos: usize,
    end: usize,
    pointer: &PointerResolver<'_>,
) -> Result<Cie, Violation> {
    let body = &bytes[..end];
    let mut reader = Reader::new(body, pos);
    let version = reader.u8()?;
    if version != 1 && version != 3 {
        return Err(cfi_error(format!("CIE at {at} has version {version}")));
    }
    let mut augmentation = Vec::new();
    loop {
        let byte = reader.u8()?;
        if byte == 0 {
            break;
        }
        augmentation.push(byte);
    }
    let augmentation = String::from_utf8(augmentation)
        .map_err(|_| cfi_error(format!("CIE at {at} augmentation is not ASCII")))?;
    let code_align = reader.uleb()?;
    let data_align = reader.sleb()?;
    let ra_register = if version == 1 {
        u64::from(reader.u8()?)
    } else {
        reader.uleb()?
    };
    let mut personality = None;
    let mut lsda_encoding = None;
    let mut fde_encoding = 0x00;
    if let Some(rest) = augmentation.strip_prefix('z') {
        let data_len = reader.uleb()?;
        let data_end = usize::try_from(data_len)
            .ok()
            .and_then(|len| reader.pos.checked_add(len))
            .filter(|&data_end| data_end <= end)
            .ok_or_else(|| cfi_error(format!("CIE at {at} augmentation data overruns")))?;
        for letter in rest.chars() {
            match letter {
                'P' => {
                    let encoding = reader.u8()?;
                    let (target, width) = pointer(reader.pos, encoding)?;
                    reader.pos += width;
                    personality = Some(target);
                }
                'L' => lsda_encoding = Some(reader.u8()?),
                'R' => fde_encoding = reader.u8()?,
                'S' => {
                    // A signal frame: its return address is not a call's,
                    // so the personalities look its call sites up at the
                    // return address itself, not at the return address
                    // minus one as the coverage decision does.
                    return Err(cfi_error(format!(
                        "CIE at {at} marks its frames as signal frames ('S'), which the call-site coverage decision does not model"
                    )));
                }
                other => {
                    return Err(cfi_error(format!(
                        "CIE at {at} augmentation letter {other:?} is not admitted"
                    )));
                }
            }
        }
        if reader.pos != data_end {
            return Err(cfi_error(format!(
                "CIE at {at} augmentation data length disagrees with its letters"
            )));
        }
    } else if !augmentation.is_empty() {
        return Err(cfi_error(format!(
            "CIE at {at} augmentation {augmentation:?} lacks the 'z' prefix"
        )));
    }
    Ok(Cie {
        code_align,
        data_align,
        ra_register,
        augmentation,
        personality,
        lsda_encoding,
        fde_encoding,
        initial: body[reader.pos..end].to_vec(),
    })
}

fn decode_fde(
    bytes: &[u8],
    at: usize,
    pos: usize,
    end: usize,
    cie: &Cie,
    cie_index: usize,
    pointer: &PointerResolver<'_>,
) -> Result<Fde, Violation> {
    let body = &bytes[..end];
    let mut reader = Reader::new(body, pos);
    let (pc_begin, width) = pointer(reader.pos, cie.fde_encoding)?;
    reader.pos += width;
    let pc_range = reader.fixed(pointer_width(cie.fde_encoding)?)?;
    let mut lsda = None;
    if cie.augmentation.starts_with('z') {
        let data_len = reader.uleb()?;
        let data_end = usize::try_from(data_len)
            .ok()
            .and_then(|len| reader.pos.checked_add(len))
            .filter(|&data_end| data_end <= end)
            .ok_or_else(|| cfi_error(format!("FDE at {at} augmentation data overruns")))?;
        if let Some(encoding) = cie.lsda_encoding {
            let (target, width) = pointer(reader.pos, encoding)?;
            reader.pos += width;
            lsda = Some(target);
        }
        if reader.pos != data_end {
            return Err(cfi_error(format!(
                "FDE at {at} augmentation data length disagrees with its CIE"
            )));
        }
    }
    Ok(Fde {
        offset: at,
        cie: cie_index,
        pc_begin,
        pc_range,
        lsda,
        instructions: body[reader.pos..end].to_vec(),
    })
}

/// How a row recovers one register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rule {
    Undefined,
    SameValue,
    /// Saved at `CFA + offset` (bytes).
    Offset(i64),
    /// Held in another register.
    Register(u64),
}

/// One row of the unwind table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) cfa_register: u64,
    pub(crate) cfa_offset: i64,
    pub(crate) rules: BTreeMap<u64, Rule>,
}

/// The rows of one FDE: `(location, row)` in increasing location order; a
/// row holds from its location to the next one.
#[derive(Debug, Clone)]
pub(crate) struct Rows {
    pub(crate) rows: Vec<(u64, Row)>,
}

impl Rows {
    /// The row in effect at function offset `offset`.
    pub(crate) fn at(&self, offset: u64) -> Option<&Row> {
        self.rows
            .iter()
            .rev()
            .find(|(loc, _)| *loc <= offset)
            .map(|(_, row)| row)
    }
}

const DW_CFA_ADVANCE_LOC: u8 = 0x40;
const DW_CFA_OFFSET: u8 = 0x80;
const DW_CFA_RESTORE: u8 = 0xc0;

/// Run the CIE's initial instructions, then the FDE's program.
pub(crate) fn run(cie: &Cie, fde: &Fde) -> Result<Rows, Violation> {
    let mut initial = Row {
        cfa_register: 0,
        cfa_offset: 0,
        rules: BTreeMap::new(),
    };
    let mut ignored = Vec::new();
    execute(cie, &cie.initial, &mut initial, None, &mut ignored, true)?;
    if !ignored.is_empty() {
        return Err(cfi_error("CIE initial instructions advance the location"));
    }
    let mut row = initial.clone();
    let mut rows = Vec::new();
    let end = execute(
        cie,
        &fde.instructions,
        &mut row,
        Some(&initial),
        &mut rows,
        false,
    )?;
    // `execute` records the row as it stood before each advance, at the
    // location it held from; the final row holds from the last location to
    // the end of the range.
    rows.push((end, row));
    Ok(Rows {
        rows: fold_rows(rows),
    })
}

/// `execute` pushes `(loc_before_advance, row_at_that_loc)` for each
/// advance, then the final row; turn that into rows keyed by their start.
fn fold_rows(pushed: Vec<(u64, Row)>) -> Vec<(u64, Row)> {
    let mut out: Vec<(u64, Row)> = Vec::new();
    for (loc, row) in pushed {
        match out.last_mut() {
            Some((last_loc, last_row)) if *last_loc == loc => *last_row = row,
            _ => out.push((loc, row)),
        }
    }
    out
}

fn execute(
    cie: &Cie,
    program: &[u8],
    row: &mut Row,
    initial: Option<&Row>,
    rows: &mut Vec<(u64, Row)>,
    in_cie: bool,
) -> Result<u64, Violation> {
    let mut reader = Reader::new(program, 0);
    let mut loc = 0u64;
    let mut stack: Vec<Row> = Vec::new();
    let factor = |value: u64| -> Result<i64, Violation> {
        i64::try_from(value)
            .ok()
            .and_then(|value| value.checked_mul(cie.data_align))
            .ok_or_else(|| cfi_error(format!("factored offset {value} overflows")))
    };
    let mut advance =
        |delta: u64, row: &Row, rows: &mut Vec<(u64, Row)>| -> Result<(), Violation> {
            if in_cie {
                return Err(cfi_error("CIE initial instructions advance the location"));
            }
            rows.push((loc, row.clone()));
            loc = delta
                .checked_mul(cie.code_align)
                .and_then(|delta| loc.checked_add(delta))
                .ok_or_else(|| cfi_error("location advance overflows"))?;
            Ok(())
        };
    let restore = |register: u64, row: &mut Row| -> Result<(), Violation> {
        let initial =
            initial.ok_or_else(|| cfi_error("DW_CFA_restore in CIE initial instructions"))?;
        match initial.rules.get(&register) {
            Some(rule) => {
                row.rules.insert(register, *rule);
            }
            None => {
                row.rules.remove(&register);
            }
        }
        Ok(())
    };
    while reader.pos < program.len() {
        let opcode = reader.u8()?;
        match opcode & 0xc0 {
            DW_CFA_ADVANCE_LOC => {
                advance(u64::from(opcode & 0x3f), row, rows)?;
                continue;
            }
            DW_CFA_OFFSET => {
                let offset = factor(reader.uleb()?)?;
                row.rules
                    .insert(u64::from(opcode & 0x3f), Rule::Offset(offset));
                continue;
            }
            DW_CFA_RESTORE => {
                restore(u64::from(opcode & 0x3f), row)?;
                continue;
            }
            _ => {}
        }
        match opcode {
            0x00 => {}
            0x02 => {
                let delta = u64::from(reader.u8()?);
                advance(delta, row, rows)?;
            }
            0x03 => {
                let delta = reader.fixed(2)?;
                advance(delta, row, rows)?;
            }
            0x04 => {
                let delta = reader.fixed(4)?;
                advance(delta, row, rows)?;
            }
            0x05 => {
                let register = reader.uleb()?;
                let offset = factor(reader.uleb()?)?;
                row.rules.insert(register, Rule::Offset(offset));
            }
            0x06 => {
                let register = reader.uleb()?;
                restore(register, row)?;
            }
            0x07 => {
                let register = reader.uleb()?;
                row.rules.insert(register, Rule::Undefined);
            }
            0x08 => {
                let register = reader.uleb()?;
                row.rules.insert(register, Rule::SameValue);
            }
            0x09 => {
                let register = reader.uleb()?;
                let other = reader.uleb()?;
                row.rules.insert(register, Rule::Register(other));
            }
            0x0a => stack.push(row.clone()),
            0x0b => {
                *row = stack
                    .pop()
                    .ok_or_else(|| cfi_error("DW_CFA_restore_state with an empty stack"))?;
            }
            0x0c => {
                row.cfa_register = reader.uleb()?;
                row.cfa_offset = i64::try_from(reader.uleb()?)
                    .map_err(|_| cfi_error("DW_CFA_def_cfa offset overflows"))?;
            }
            0x0d => row.cfa_register = reader.uleb()?,
            0x0e => {
                row.cfa_offset = i64::try_from(reader.uleb()?)
                    .map_err(|_| cfi_error("DW_CFA_def_cfa_offset overflows"))?;
            }
            0x11 => {
                let register = reader.uleb()?;
                let offset = reader
                    .sleb()?
                    .checked_mul(cie.data_align)
                    .ok_or_else(|| cfi_error("DW_CFA_offset_extended_sf overflows"))?;
                row.rules.insert(register, Rule::Offset(offset));
            }
            0x12 => {
                row.cfa_register = reader.uleb()?;
                row.cfa_offset = reader
                    .sleb()?
                    .checked_mul(cie.data_align)
                    .ok_or_else(|| cfi_error("DW_CFA_def_cfa_sf overflows"))?;
            }
            0x13 => {
                row.cfa_offset = reader
                    .sleb()?
                    .checked_mul(cie.data_align)
                    .ok_or_else(|| cfi_error("DW_CFA_def_cfa_offset_sf overflows"))?;
            }
            0x2e => {
                // DW_CFA_GNU_args_size: no effect on the rows.
                reader.uleb()?;
            }
            other => {
                return Err(cfi_error(format!(
                    "call-frame instruction {other:#04x} is outside the admitted set (no expressions, set_loc, val_offset or return-address signing)"
                )));
            }
        }
    }
    Ok(loc)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A zR CIE (CFA = SP + 0, data alignment -8, RA = X30, pcrel|sdata4
    /// FDE pointers) and one FDE describing `stp x29, x30, [sp, #-16]!;
    /// mov x29, sp`.
    fn section() -> Vec<u8> {
        section_with(b"zR")
    }

    /// [`section`] with another augmentation string over the same `R` data.
    fn section_with(augmentation: &[u8]) -> Vec<u8> {
        let mut cie = vec![0, 0, 0, 0, 1];
        cie.extend_from_slice(augmentation);
        cie.extend_from_slice(&[0, 4, 0x78, 30, 1, 0x1b]);
        cie.extend_from_slice(&[0x0c, 31, 0]);
        while !(cie.len() + 4).is_multiple_of(8) {
            cie.push(0);
        }
        let mut out = (cie.len() as u32).to_le_bytes().to_vec();
        out.extend_from_slice(&cie);
        let fde_start = out.len();
        let mut fde = Vec::new();
        fde.extend_from_slice(&((fde_start + 4) as u32).to_le_bytes());
        fde.extend_from_slice(&0i32.to_le_bytes()); // pc_begin (resolver)
        fde.extend_from_slice(&16u32.to_le_bytes());
        fde.push(0); // augmentation data
        // advance 1; def_cfa_offset 16; offset x30 1; offset x29 2;
        // advance 1; def_cfa x29 16
        fde.extend_from_slice(&[0x41, 0x0e, 16, 0x9e, 1, 0x9d, 2, 0x41, 0x0c, 29, 16]);
        while !(fde.len() + 4).is_multiple_of(8) {
            fde.push(0);
        }
        out.extend_from_slice(&(fde.len() as u32).to_le_bytes());
        out.extend_from_slice(&fde);
        out
    }

    #[test]
    fn programs_run_to_the_rows_an_unwinder_uses() {
        let bytes = section();
        let resolver = |_: usize, encoding: u8| -> Result<(Term, usize), Violation> {
            Ok((Term::Address(0x1000), pointer_width(encoding)?))
        };
        let frame = EhFrame::decode(&bytes, &resolver).expect("decodes");
        assert_eq!((frame.cies.len(), frame.fdes.len()), (1, 1));
        let fde = &frame.fdes[0];
        assert_eq!(
            (fde.pc_begin.clone(), fde.pc_range),
            (Term::Address(0x1000), 16)
        );
        let rows = run(&frame.cies[fde.cie], fde).expect("runs");
        let entry = rows.at(0).expect("row at entry");
        assert_eq!((entry.cfa_register, entry.cfa_offset), (31, 0));
        assert!(entry.rules.is_empty());
        let after_store = rows.at(4).expect("row after the store");
        assert_eq!((after_store.cfa_register, after_store.cfa_offset), (31, 16));
        assert_eq!(after_store.rules.get(&30), Some(&Rule::Offset(-8)));
        assert_eq!(after_store.rules.get(&29), Some(&Rule::Offset(-16)));
        let body = rows.at(12).expect("row in the body");
        assert_eq!((body.cfa_register, body.cfa_offset), (29, 16));
    }

    #[test]
    fn signal_frame_augmentation_is_refused() {
        let resolver = |_: usize, encoding: u8| -> Result<(Term, usize), Violation> {
            Ok((Term::Address(0x1000), pointer_width(encoding)?))
        };
        let error = EhFrame::decode(&section_with(b"zRS"), &resolver).expect_err("'S'");
        assert_eq!(error.kind, EhObligationKind::CfiStructure);
        assert!(error.detail.contains("signal frames"), "{error}");
    }

    #[test]
    fn expressions_are_refused() {
        let mut bytes = section();
        // Replace the final def_cfa with DW_CFA_def_cfa_expression.
        let at = bytes
            .windows(3)
            .rposition(|window| window == [0x0c, 29, 16])
            .expect("def_cfa");
        bytes[at] = 0x0f;
        let resolver = |_: usize, encoding: u8| -> Result<(Term, usize), Violation> {
            Ok((Term::Address(0x1000), pointer_width(encoding)?))
        };
        let frame = EhFrame::decode(&bytes, &resolver).expect("decodes");
        let error = run(&frame.cies[0], &frame.fdes[0]).expect_err("expression");
        assert_eq!(error.kind, EhObligationKind::CfiStructure);
    }
}
