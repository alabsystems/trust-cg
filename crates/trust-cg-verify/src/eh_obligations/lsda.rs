// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! A clean-room LSDA (`__gcc_except_tab`) decoder.
//!
//! Written from the Itanium C++ ABI exception-handling tables and the way
//! the two personalities read them (libc++abi `scan_eh_table`, Rust std's
//! `find_eh_action`), not from trust-cg's builder
//! (`trust-cg-codegen/src/exception_handling.rs`). It decodes the header,
//! the call-site records, the action chains and the type-table slots a chain
//! names; every read is bounded by the region the caller hands it.

use super::{EhObligationKind, Violation};

/// `DW_EH_PE_omit`.
pub(crate) const DW_EH_PE_OMIT: u8 = 0xff;
/// `DW_EH_PE_indirect | DW_EH_PE_pcrel | DW_EH_PE_sdata4`, the only type
/// table encoding admitted.
pub(crate) const DW_EH_PE_INDIRECT_PCREL_SDATA4: u8 = 0x9b;

fn structure(detail: impl Into<String>) -> Violation {
    Violation::object(EhObligationKind::LsdaStructure, detail)
}

pub(crate) struct Reader<'a> {
    bytes: &'a [u8],
    pub(crate) pos: usize,
}

impl<'a> Reader<'a> {
    pub(crate) fn new(bytes: &'a [u8], pos: usize) -> Self {
        Self { bytes, pos }
    }

    pub(crate) fn u8(&mut self) -> Result<u8, Violation> {
        let byte = *self
            .bytes
            .get(self.pos)
            .ok_or_else(|| structure(format!("read past the LSDA region at {}", self.pos)))?;
        self.pos += 1;
        Ok(byte)
    }

    pub(crate) fn fixed(&mut self, width: usize) -> Result<u64, Violation> {
        let slice = self
            .bytes
            .get(self.pos..self.pos.saturating_add(width))
            .ok_or_else(|| {
                structure(format!("{width}-byte read past the region at {}", self.pos))
            })?;
        self.pos += width;
        let mut value = 0u64;
        for (i, byte) in slice.iter().enumerate() {
            value |= u64::from(*byte) << (8 * i);
        }
        Ok(value)
    }

    pub(crate) fn uleb(&mut self) -> Result<u64, Violation> {
        let mut value = 0u64;
        let mut shift = 0u32;
        loop {
            let byte = self.u8()?;
            if shift >= 64 || (shift == 63 && byte & 0x7e != 0) {
                return Err(structure(format!(
                    "ULEB128 overflows 64 bits at {}",
                    self.pos
                )));
            }
            value |= u64::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                return Ok(value);
            }
        }
    }

    pub(crate) fn sleb(&mut self) -> Result<i64, Violation> {
        let mut value = 0i64;
        let mut shift = 0u32;
        loop {
            let byte = self.u8()?;
            if shift >= 64 {
                return Err(structure(format!(
                    "SLEB128 overflows 64 bits at {}",
                    self.pos
                )));
            }
            value |= i64::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                if shift < 64 && byte & 0x40 != 0 {
                    value |= -1i64 << shift;
                }
                return Ok(value);
            }
        }
    }

    /// A call-site table field under encoding `encoding`.
    fn call_site_field(&mut self, encoding: u8) -> Result<u64, Violation> {
        match encoding {
            0x01 => self.uleb(),
            0x02 => self.fixed(2),
            0x03 => self.fixed(4),
            0x04 => self.fixed(8),
            other => Err(structure(format!(
                "call-site encoding {other:#04x} is outside the admitted unsigned forms"
            ))),
        }
    }
}

/// One call-site record, offsets relative to the function start (LPStart is
/// omitted, so the landing-pad base is the function start too).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CallSite {
    pub(crate) start: u64,
    pub(crate) len: u64,
    pub(crate) landing_pad: u64,
    /// 0, or a 1-based byte offset into the action table.
    pub(crate) action: u64,
}

impl CallSite {
    pub(crate) fn end(&self) -> u64 {
        self.start.saturating_add(self.len)
    }
}

/// One action of a decoded chain, as the personality interprets it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Action {
    /// A positive filter: the type-table slot it names holds `typeinfo`
    /// (`None` is a NULL slot: catch-all).
    Catch {
        filter: i64,
        typeinfo: Option<String>,
    },
    /// Filter 0: run the landing pad as cleanup.
    Cleanup,
    /// A negative filter: an exception specification listing these slots.
    Filter { filter: i64, slots: Vec<u64> },
}

/// How the caller resolves a type-table slot at an LSDA-region offset:
/// `Ok(Some(symbol))` for a typeinfo bound through the GOT, `Ok(None)` for a
/// NULL slot.
pub(crate) type SlotResolver<'r> = dyn Fn(usize) -> Result<Option<String>, Violation> + 'r;

/// A decoded LSDA.
#[derive(Debug, Clone)]
pub(crate) struct Lsda {
    pub(crate) call_sites: Vec<CallSite>,
    /// Region offset of the first action record.
    actions_start: usize,
    /// Region offset one past the last byte an action may occupy.
    actions_end: usize,
    /// Region offset of the type-table base, when a type table is present.
    ttype_base: Option<usize>,
}

impl Lsda {
    /// Decode the LSDA at the start of `region`.
    pub(crate) fn decode(region: &[u8]) -> Result<Self, Violation> {
        let mut reader = Reader::new(region, 0);
        let lpstart_encoding = reader.u8()?;
        if lpstart_encoding != DW_EH_PE_OMIT {
            return Err(structure(format!(
                "LPStart encoding {lpstart_encoding:#04x} is not DW_EH_PE_omit: landing pads would not be function-relative"
            )));
        }
        let ttype_encoding = reader.u8()?;
        let ttype_base = if ttype_encoding == DW_EH_PE_OMIT {
            None
        } else {
            if ttype_encoding != DW_EH_PE_INDIRECT_PCREL_SDATA4 {
                return Err(structure(format!(
                    "TType encoding {ttype_encoding:#04x} is not indirect|pcrel|sdata4"
                )));
            }
            let offset = reader.uleb()?;
            let base = usize::try_from(offset)
                .ok()
                .and_then(|offset| reader.pos.checked_add(offset))
                .filter(|&base| base <= region.len())
                .ok_or_else(|| {
                    structure(format!("TType base offset {offset} leaves the region"))
                })?;
            Some(base)
        };
        let call_site_encoding = reader.u8()?;
        let call_site_len = reader.uleb()?;
        let call_site_start = reader.pos;
        let call_site_end = usize::try_from(call_site_len)
            .ok()
            .and_then(|len| call_site_start.checked_add(len))
            .filter(|&end| end <= region.len())
            .ok_or_else(|| {
                structure(format!(
                    "call-site table length {call_site_len} leaves the region"
                ))
            })?;
        let mut call_sites = Vec::new();
        while reader.pos < call_site_end {
            let start = reader.call_site_field(call_site_encoding)?;
            let len = reader.call_site_field(call_site_encoding)?;
            let landing_pad = reader.call_site_field(call_site_encoding)?;
            let action = reader.uleb()?;
            if reader.pos > call_site_end {
                return Err(structure("a call-site record straddles the table end"));
            }
            call_sites.push(CallSite {
                start,
                len,
                landing_pad,
                action,
            });
        }
        let actions_start = call_site_end;
        let actions_end = ttype_base.unwrap_or(region.len());
        Ok(Self {
            call_sites,
            actions_start,
            actions_end,
            ttype_base,
        })
    }

    /// The action chain that starts at 1-based byte offset `action`, read the
    /// way the personalities read it: a filter SLEB128, then a displacement
    /// SLEB128 measured from the displacement field itself (0 ends).
    pub(crate) fn chain(
        &self,
        region: &[u8],
        action: u64,
        slot: &SlotResolver<'_>,
    ) -> Result<Vec<Action>, Violation> {
        if action == 0 {
            return Ok(Vec::new());
        }
        let mut position = usize::try_from(action - 1)
            .ok()
            .and_then(|offset| self.actions_start.checked_add(offset))
            .ok_or_else(|| structure(format!("action index {action} overflows")))?;
        let mut chain = Vec::new();
        let mut visited = std::collections::BTreeSet::new();
        loop {
            if position < self.actions_start || position >= self.actions_end {
                return Err(structure(format!(
                    "action record at region offset {position} is outside the action table [{}, {})",
                    self.actions_start, self.actions_end
                )));
            }
            if !visited.insert(position) {
                return Err(structure(format!(
                    "action chain from index {action} loops at region offset {position}"
                )));
            }
            let mut reader = Reader::new(&region[..self.actions_end], position);
            let filter = reader.sleb()?;
            let displacement_at = reader.pos;
            let displacement = reader.sleb()?;
            chain.push(self.action(region, filter, slot)?);
            if displacement == 0 {
                return Ok(chain);
            }
            let next = (displacement_at as i128) + i128::from(displacement);
            position = usize::try_from(next).map_err(|_| {
                structure(format!(
                    "action displacement {displacement} leaves the region"
                ))
            })?;
        }
    }

    fn action(
        &self,
        region: &[u8],
        filter: i64,
        slot: &SlotResolver<'_>,
    ) -> Result<Action, Violation> {
        if filter == 0 {
            return Ok(Action::Cleanup);
        }
        let base = self.ttype_base.ok_or_else(|| {
            structure(format!(
                "action filter {filter} names a type table the LSDA omits"
            ))
        })?;
        if filter > 0 {
            let offset = u64::try_from(filter)
                .ok()
                .and_then(|slot| slot.checked_mul(4))
                .and_then(|bytes| usize::try_from(bytes).ok())
                .and_then(|bytes| base.checked_sub(bytes))
                .filter(|&offset| offset >= self.actions_start)
                .ok_or_else(|| {
                    structure(format!(
                        "type-table slot {filter} lies before the action table"
                    ))
                })?;
            if region.get(offset..offset + 4).is_none() {
                return Err(structure(format!(
                    "type-table slot {filter} leaves the region"
                )));
            }
            return Ok(Action::Catch {
                filter,
                typeinfo: slot(offset)?,
            });
        }
        // An exception specification: a ULEB128 list of slots after the
        // base, at byte `-filter - 1`, terminated by 0.
        let start = filter
            .checked_neg()
            .and_then(|value| value.checked_sub(1))
            .and_then(|value| usize::try_from(value).ok())
            .and_then(|value| base.checked_add(value))
            .ok_or_else(|| structure(format!("filter {filter} leaves the region")))?;
        let mut reader = Reader::new(region, start);
        let mut slots = Vec::new();
        loop {
            let index = reader.uleb()?;
            if index == 0 {
                break;
            }
            slots.push(index);
            if slots.len() > 4096 {
                return Err(structure(format!(
                    "filter {filter} list does not terminate"
                )));
            }
        }
        Ok(Action::Filter { filter, slots })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An LSDA with a two-slot type table (slot 1 bound, slot 2 NULL), two
    /// records (an invoke whose chain is catch 1, catch-all 2, cleanup; a
    /// no-handler record) and the Rust empty filter at the base.
    fn sample() -> Vec<u8> {
        let mut lsda = vec![0xff, 0x9b];
        // TType base offset, patched below.
        lsda.push(0);
        let base_field = lsda.len() - 1;
        lsda.push(0x01); // ULEB128 call sites
        let records: [u8; 8] = [0x08, 0x04, 0x20, 0x01, 0x0c, 0x10, 0x00, 0x00];
        lsda.push(records.len() as u8);
        lsda.extend_from_slice(&records);
        // Actions: [1, +1] [2, +1] [0, 0]
        lsda.extend_from_slice(&[0x01, 0x01, 0x02, 0x01, 0x00, 0x00]);
        while !lsda.len().is_multiple_of(4) {
            lsda.push(0);
        }
        lsda.extend_from_slice(&[0; 8]); // slot 2, slot 1
        let base = lsda.len();
        lsda.push(0); // empty filter list
        lsda[base_field] = (base - (base_field + 1)) as u8;
        lsda
    }

    #[test]
    fn records_and_chains_decode_as_the_personalities_read_them() {
        let region = sample();
        let lsda = Lsda::decode(&region).expect("decodes");
        assert_eq!(
            lsda.call_sites,
            [
                CallSite {
                    start: 8,
                    len: 4,
                    landing_pad: 0x20,
                    action: 1
                },
                CallSite {
                    start: 12,
                    len: 16,
                    landing_pad: 0,
                    action: 0
                }
            ]
        );
        let base = region.len() - 1;
        let slot = |offset: usize| -> Result<Option<String>, Violation> {
            Ok((offset == base - 4).then(|| "__ZTIi".to_string()))
        };
        assert_eq!(
            lsda.chain(&region, 1, &slot).expect("chain"),
            [
                Action::Catch {
                    filter: 1,
                    typeinfo: Some("__ZTIi".to_string())
                },
                Action::Catch {
                    filter: 2,
                    typeinfo: None
                },
                Action::Cleanup
            ]
        );
        assert_eq!(lsda.chain(&region, 0, &slot).expect("empty"), []);
    }

    #[test]
    fn malformed_tables_are_refused() {
        let mut region = sample();
        region[0] = 0x00; // LPStart present
        assert_eq!(
            Lsda::decode(&region).expect_err("LPStart").kind,
            EhObligationKind::LsdaStructure
        );
        let region = sample();
        let lsda = Lsda::decode(&region).expect("decodes");
        let slot = |_: usize| -> Result<Option<String>, Violation> { Ok(None) };
        // An action index past the table.
        assert!(lsda.chain(&region, 40, &slot).is_err());
        // A chain that loops: [1, 0x7f (-1)] points back at its own filter.
        // The first action's displacement (byte 14) becomes -1: back to its
        // own filter at byte 13.
        let mut looping = sample();
        looping[14] = 0x7f;
        let lsda = Lsda::decode(&looping).expect("decodes");
        assert!(lsda.chain(&looping, 1, &slot).is_err());
    }
}
