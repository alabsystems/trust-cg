// Copyright 2026 Andrew Yates | License: Apache-2.0
// Compiled only by export_vt_tables.py beside exact, committed aterm sources.
// No copied transition constants or replacement character-width algorithm.

#[path = "aterm/state.rs"]
mod state;
#[path = "aterm/table/mod.rs"]
mod table;
#[path = "aterm/width.rs"]
mod width;

use std::io::{self, Write};

fn island_width(cp: u32) -> io::Result<usize> {
    // Surrogates are not Rust chars; the island contract assigns them width 1.
    let value = char::from_u32(cp).map_or(1, width::char_width);
    if value > 2 {
        return Err(io::Error::other("aterm returned a width outside 0..=2"));
    }
    Ok(value)
}

fn main() -> io::Result<()> {
    let commit = std::env::args()
        .nth(1)
        .ok_or_else(|| io::Error::other("missing source commit"))?;
    if !matches!(commit.len(), 40 | 64) || !commit.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(io::Error::other("invalid source commit"));
    }
    if state::State::COUNT != 14 || table::TRANSITIONS.len() != 14 {
        return Err(io::Error::other("VT schema requires exactly 14 states"));
    }
    let mut out = io::BufWriter::new(io::stdout().lock());
    write!(
        out,
        "{{\"schema\":\"aterm.vt-islands.tables\",\"version\":1,\"aterm_commit\":\"{commit}\",\"vt\":["
    )?;
    for (row_index, row) in table::TRANSITIONS.iter().enumerate() {
        if row.len() != 256 {
            return Err(io::Error::other("VT schema requires 256 bytes per state"));
        }
        if row_index != 0 {
            write!(out, ",")?;
        }
        write!(out, "[")?;
        for (byte, transition) in row.iter().enumerate() {
            // Validate before narrowing: a future wider enum must not wrap a
            // discriminant such as 256 into an apparently valid byte value.
            let next = transition.next_state as u128;
            let action = transition.action as u128;
            if next >= 14 || action > 255 {
                return Err(io::Error::other("VT transition is out of range"));
            }
            if byte != 0 {
                write!(out, ",")?;
            }
            write!(out, "[{next},{action}]")?;
        }
        write!(out, "]")?;
    }
    write!(out, "],\"width_runs\":[")?;
    let mut start = 0;
    let mut previous = island_width(0)?;
    let mut first = true;
    for cp in 1..=0x10ffff {
        let current = island_width(cp)?;
        if current != previous {
            if !first {
                write!(out, ",")?;
            }
            write!(out, "[{start},{},{previous}]", cp - 1)?;
            first = false;
            start = cp;
            previous = current;
        }
    }
    if !first {
        write!(out, ",")?;
    }
    writeln!(out, "[{start},1114111,{previous}]]}}")?;
    out.flush()
}
