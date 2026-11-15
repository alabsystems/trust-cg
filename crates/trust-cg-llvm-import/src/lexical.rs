// trust-cg-llvm-import / lexical.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// LLVM's lexer, run once over the whole module before the line reader, and
// the refusals of every spelling that reader would read differently from
// LLVM.

use crate::{Error, Result};

/// The kind of one token, as LLVM's lexer (`LLLexer.cpp`) splits it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// A keyword or an integer type: LLVM ends a keyword at the first byte
    /// that is not a letter, digit or `_`, and an `iN` type at the first
    /// non-digit after the `i`.
    Word,
    /// A label: `name:`, `"quoted":`, `0:`, `$name:`.
    Label,
    /// `@name`, `@"name"`, `@0`.
    Global,
    /// `%name`, `%"name"`, `%0`.
    Local,
    /// `$name`, `$"name"`.
    Comdat,
    /// `!name` (a `!` followed by anything else is [`Kind::Punct`]).
    MetadataName,
    /// `#0`.
    AttrGroup,
    /// `#dbg_value` and the other debug-record keywords.
    DbgRecord,
    /// `^0`.
    Summary,
    /// `"..."`.
    Str,
    /// An integer or floating-point literal.
    Number,
    /// `...`.
    Ellipsis,
    /// One punctuation byte: `= , * ( ) [ ] { } < > ! | :`.
    Punct(u8),
}

/// One token of the module text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Token {
    pub(crate) kind: Kind,
    /// Byte range in the lexed text.
    pub(crate) start: usize,
    pub(crate) end: usize,
    /// 1-based line (lines end at `\n`).
    pub(crate) line: usize,
    /// No whitespace or comment separates it from the token before it.
    pub(crate) glued: bool,
    /// The first token on its line.
    pub(crate) line_first: bool,
}

impl Token {
    pub(crate) fn text<'a>(&self, text: &'a str) -> &'a str {
        &text[self.start..self.end]
    }

    fn is_word(&self, text: &str, word: &str) -> bool {
        self.kind == Kind::Word && self.text(text) == word
    }
}

fn refuse<T>(line: usize, what: impl std::fmt::Display) -> Result<T> {
    Err(Error::Unsupported(format!("line {line}: {what}")))
}

/// A byte LLVM reads inside a name (`[-a-zA-Z$._0-9]`).
fn is_name_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'-' | b'$' | b'.' | b'_')
}

/// The end of a label tail starting at `from` (LLVM's `isLabelTail`): name
/// bytes up to a `:`, with the offset after the colon, or `None`.
fn label_tail(bytes: &[u8], from: usize) -> Option<usize> {
    let mut at = from;
    loop {
        match bytes.get(at) {
            Some(b':') => return Some(at + 1),
            Some(&b) if is_name_byte(b) => at += 1,
            _ => return None,
        }
    }
}

/// Name a byte for a diagnostic.
fn describe_byte(b: u8) -> String {
    match b {
        0 => "a NUL byte".to_string(),
        b'\r' => "a carriage return that does not end a line".to_string(),
        0x0b => "a vertical tab".to_string(),
        0x0c => "a form feed".to_string(),
        0x80..=0xff => format!("the non-ASCII byte 0x{b:02x}"),
        _ if b.is_ascii_control() => format!("the control byte 0x{b:02x}"),
        _ => format!("`{}`", b as char),
    }
}

/// Lex `text` (the module's lines joined by `\n`) as LLVM's lexer does.
///
/// The whitespace LLVM reads is space, tab, line feed, carriage return and
/// NUL. Outside strings and comments this importer admits only the first
/// three: a NUL or a carriage return that does not end a line (each `\r\n`
/// was already split by `str::lines`) is whitespace to LLVM but not to the
/// line reader, which would read `hidden\0` as an unknown word and a line
/// holding `\r` as one line. Every other control byte and every non-ASCII
/// byte is a lexer error in LLVM. Each is refused by name. A tab is read
/// as a space ([`blank_tabs`]).
///
/// LLVM reads a numbered ID (`%0`, `@0`, `#0`, `!0`, `^0`, a label `0:`)
/// and an integer type (`i64`) by the value of its digits; this importer
/// matches them by spelling. A spelling with a leading zero (`#00`, `i064`)
/// is refused by name ([`refuse_leading_zero`]).
///
/// The caller has already run `check_module_lexically`, so every string
/// closes on its own line and there is no block comment.
pub(crate) fn lex(text: &str) -> Result<Vec<Token>> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut line = 1usize;
    let mut line_first = true;
    let mut glued = false;
    let mut index = 0usize;
    while index < bytes.len() {
        let b = bytes[index];
        let start = index;
        let kind = match b {
            b'\n' => {
                line += 1;
                line_first = true;
                glued = false;
                index += 1;
                continue;
            }
            b' ' | b'\t' => {
                glued = false;
                index += 1;
                continue;
            }
            b';' => {
                // A comment runs to the line feed: `check_module_lexically`
                // refused a carriage return inside one with text after it.
                index = bytes[index..]
                    .iter()
                    .position(|&b| b == b'\n')
                    .map_or(bytes.len(), |at| index + at);
                glued = false;
                continue;
            }
            b'"' => {
                let close = quoted_end(bytes, index, line)?;
                index = close;
                if bytes.get(index) == Some(&b':') {
                    refuse_nul_in_name(bytes, start, close, line)?;
                    index += 1;
                    Kind::Label
                } else {
                    Kind::Str
                }
            }
            b'@' | b'%' => {
                let kind = if b == b'@' { Kind::Global } else { Kind::Local };
                index = sigil_name_end(bytes, index + 1, line, true)?.ok_or_else(|| {
                    Error::Unsupported(format!(
                        "line {line}: `{}` without a name (LLVM's lexer rejects it)",
                        b as char
                    ))
                })?;
                refuse_leading_zero(
                    &bytes[start + 1..index],
                    line,
                    "value ID",
                    &(b as char).to_string(),
                )?;
                kind
            }
            b'$' => {
                if let Some(end) = label_tail(bytes, index) {
                    index = end;
                    Kind::Label
                } else {
                    index = sigil_name_end(bytes, index + 1, line, false)?.ok_or_else(|| {
                        Error::Unsupported(format!(
                            "line {line}: `$` without a name (LLVM's lexer rejects it)"
                        ))
                    })?;
                    Kind::Comdat
                }
            }
            b'!' => {
                let next = bytes.get(index + 1).copied().unwrap_or(b' ');
                if next.is_ascii_alphabetic() || matches!(next, b'-' | b'$' | b'.' | b'_' | b'\\') {
                    index += 2;
                    while bytes
                        .get(index)
                        .is_some_and(|&b| is_name_byte(b) || b == b'\\')
                    {
                        index += 1;
                    }
                    Kind::MetadataName
                } else {
                    // `!0`: LLVM lexes `!` and then the number, whose value
                    // (not spelling) names the node.
                    let digits = bytes[index + 1..]
                        .iter()
                        .take_while(|b| b.is_ascii_digit())
                        .count();
                    refuse_leading_zero(
                        &bytes[index + 1..index + 1 + digits],
                        line,
                        "metadata ID",
                        "!",
                    )?;
                    index += 1;
                    Kind::Punct(b'!')
                }
            }
            b'#' => {
                index += 1;
                if bytes.get(index).is_some_and(u8::is_ascii_digit) {
                    while bytes.get(index).is_some_and(u8::is_ascii_digit) {
                        index += 1;
                    }
                    refuse_leading_zero(&bytes[start + 1..index], line, "attribute group ID", "#")?;
                    Kind::AttrGroup
                } else if bytes.get(index).is_some_and(u8::is_ascii_alphabetic) {
                    while bytes
                        .get(index)
                        .is_some_and(|&b| b.is_ascii_alphabetic() || b == b'_')
                    {
                        index += 1;
                    }
                    Kind::DbgRecord
                } else {
                    return refuse(line, "`#` without a group number (LLVM's lexer rejects it)");
                }
            }
            b'^' => {
                index += 1;
                if !bytes.get(index).is_some_and(u8::is_ascii_digit) {
                    return refuse(
                        line,
                        "`^` without a summary number (LLVM's lexer rejects it)",
                    );
                }
                while bytes.get(index).is_some_and(u8::is_ascii_digit) {
                    index += 1;
                }
                refuse_leading_zero(&bytes[start + 1..index], line, "summary ID", "^")?;
                Kind::Summary
            }
            b'.' => {
                if bytes[index..].starts_with(b"...") {
                    index += 3;
                    Kind::Ellipsis
                } else if let Some(end) = label_tail(bytes, index + 1) {
                    index = end;
                    Kind::Label
                } else {
                    return refuse(line, "`.` that starts no label (LLVM's lexer rejects it)");
                }
            }
            b'0'..=b'9' | b'-' | b'+' => {
                let (end, kind) = number_or_label(bytes, index, line)?;
                index = end;
                kind
            }
            _ if b.is_ascii_alphabetic() || b == b'_' => {
                let (end, kind) = identifier(bytes, index);
                if kind == Kind::Word && b == b'i' {
                    refuse_leading_zero(&bytes[index + 1..end], line, "integer type", "i")?;
                }
                index = end;
                kind
            }
            b'=' | b',' | b'*' | b'(' | b')' | b'[' | b']' | b'{' | b'}' | b'<' | b'>' | b'|'
            | b':' => {
                index += 1;
                Kind::Punct(b)
            }
            _ => {
                return refuse(
                    line,
                    format!(
                        "{} outside a string or comment ({})",
                        describe_byte(b),
                        match b {
                            0 => {
                                "LLVM reads it as whitespace; this importer would read it as \
                                 part of a word, so a keyword glued to it would be lost"
                            }
                            b'\r' => {
                                "LLVM reads it as whitespace; this importer splits lines only at \
                                 line feeds, so it would read two lines as one"
                            }
                            _ => "LLVM's lexer rejects it",
                        }
                    ),
                );
            }
        };
        tokens.push(Token {
            kind,
            start,
            end: index,
            line,
            glued,
            line_first,
        });
        line_first = false;
        glued = true;
    }
    Ok(tokens)
}

/// The offset after the `"` closing the string opened at `open`.
fn quoted_end(bytes: &[u8], open: usize, line: usize) -> Result<usize> {
    bytes[open + 1..]
        .iter()
        .position(|&b| b == b'"')
        .map(|at| open + 1 + at + 1)
        .ok_or_else(|| Error::Unsupported(format!("line {line}: a string that is never closed")))
}

/// LLVM refuses a raw NUL inside a quoted name or label ("NUL character is
/// not allowed in names").
fn refuse_nul_in_name(bytes: &[u8], open: usize, close: usize, line: usize) -> Result<()> {
    if bytes[open..close].contains(&0) {
        return refuse(
            line,
            "a NUL byte inside a quoted name (LLVM's lexer rejects it: \"NUL character is not \
             allowed in names\")",
        );
    }
    Ok(())
}

/// LLVM reads a numbered ID (`%00`, `@01`, `#00`, `!00`, `^00`, a label
/// `00:`) and an integer type (`i064`) by the VALUE of its digits, so `#00`
/// is attribute group 0 and `i064` is `i64`. This importer matches IDs and
/// types by spelling, so `#00` would miss the group `#0` defines (a lost
/// `sspstrong`) and `i064` would be no type at all. `digits` is the text
/// after the sigil; a spelling with a leading zero is refused by name. A
/// non-digit `digits` (a named value, a keyword) is not an ID.
fn refuse_leading_zero(digits: &[u8], line: usize, what: &str, sigil: &str) -> Result<()> {
    if digits.len() > 1 && digits[0] == b'0' && digits.iter().all(u8::is_ascii_digit) {
        let spelled = String::from_utf8_lossy(digits);
        let value = spelled.trim_start_matches('0');
        let value = if value.is_empty() { "0" } else { value };
        return refuse(
            line,
            format!(
                "{what} `{sigil}{spelled}` with a leading zero (LLVM reads it by value, as \
                 `{sigil}{value}`; this importer matches it by spelling)"
            ),
        );
    }
    Ok(())
}

/// The end of the name after a sigil at `from`: a quoted name, a
/// `[-a-zA-Z$._][-a-zA-Z$._0-9]*` name, or (`numbered`) a `[0-9]+` ID.
fn sigil_name_end(bytes: &[u8], from: usize, line: usize, numbered: bool) -> Result<Option<usize>> {
    match bytes.get(from) {
        Some(b'"') => {
            let close = quoted_end(bytes, from, line)?;
            refuse_nul_in_name(bytes, from, close, line)?;
            Ok(Some(close))
        }
        Some(&b) if is_name_byte(b) && !b.is_ascii_digit() => {
            let mut at = from + 1;
            while bytes.get(at).is_some_and(|&b| is_name_byte(b)) {
                at += 1;
            }
            Ok(Some(at))
        }
        Some(b) if numbered && b.is_ascii_digit() => {
            let mut at = from + 1;
            while bytes.get(at).is_some_and(u8::is_ascii_digit) {
                at += 1;
            }
            Ok(Some(at))
        }
        _ => Ok(None),
    }
}

/// LLVM's `LexDigitOrNegative` / `LexPositive`: an integer, a hexadecimal
/// or decimal floating-point literal, or a label (`0:`, `-name:`).
fn number_or_label(bytes: &[u8], start: usize, line: usize) -> Result<(usize, Kind)> {
    let first = bytes[start];
    let mut at = start + 1;
    let digit_at = |at: usize| bytes.get(at).is_some_and(u8::is_ascii_digit);
    if first != b'+' && !first.is_ascii_digit() && !digit_at(at) {
        // `-` not followed by a digit: a label such as `-name:`.
        return label_tail(bytes, at)
            .map(|end| (end, Kind::Label))
            .ok_or_else(|| {
                Error::Unsupported(format!(
                    "line {line}: `-` that starts no number or label (LLVM's lexer rejects it)"
                ))
            });
    }
    if first == b'+' && !digit_at(at) {
        return refuse(line, "`+` that starts no number (LLVM's lexer rejects it)");
    }
    while digit_at(at) {
        at += 1;
    }
    if first.is_ascii_digit() && bytes.get(at) == Some(&b':') {
        refuse_leading_zero(&bytes[start..at], line, "block label ID", "")?;
        return Ok((at + 1, Kind::Label));
    }
    if bytes.get(at).is_some_and(|&b| is_name_byte(b) || b == b':')
        && let Some(end) = label_tail(bytes, at)
    {
        return Ok((end, Kind::Label));
    }
    if bytes.get(at) == Some(&b'.') {
        at += 1;
        while digit_at(at) {
            at += 1;
        }
        if matches!(bytes.get(at), Some(b'e' | b'E'))
            && (digit_at(at + 1)
                || (matches!(bytes.get(at + 1), Some(b'-' | b'+')) && digit_at(at + 2)))
        {
            at += 2;
            while digit_at(at) {
                at += 1;
            }
        }
        return Ok((at, Kind::Number));
    }
    if first == b'0' && bytes.get(start + 1) == Some(&b'x') && at == start + 1 {
        // `0x...`, with LLVM's `K`/`L`/`M`/`H`/`R` float-format prefixes.
        at = start + 2;
        if matches!(bytes.get(at), Some(b'K' | b'L' | b'M' | b'H' | b'R')) {
            at += 1;
        }
        while bytes.get(at).is_some_and(u8::is_ascii_hexdigit) {
            at += 1;
        }
        return Ok((at, Kind::Number));
    }
    if first == b'+' {
        return refuse(
            line,
            "`+` that starts no floating-point number (LLVM's lexer rejects it)",
        );
    }
    Ok((at, Kind::Number))
}

/// LLVM's `LexIdentifier`: a label when the name bytes end at `:`, else an
/// `iN` integer type (ending at the first non-digit) or a keyword (ending at
/// the first byte that is not a letter, digit or `_`). `ccN` is the keyword
/// `cc` followed by the number `N`.
fn identifier(bytes: &[u8], start: usize) -> (usize, Kind) {
    if let Some(end) = label_tail(bytes, start) {
        return (end, Kind::Label);
    }
    let mut at = start + 1;
    if bytes[start] == b'i' && bytes.get(at).is_some_and(u8::is_ascii_digit) {
        while bytes.get(at).is_some_and(u8::is_ascii_digit) {
            at += 1;
        }
        return (at, Kind::Word);
    }
    while bytes
        .get(at)
        .is_some_and(|&b| b.is_ascii_alphanumeric() || b == b'_')
    {
        at += 1;
    }
    let word = &bytes[start..at];
    if word.len() > 2 && word.starts_with(b"cc") && word[2..].iter().all(u8::is_ascii_digit) {
        return (start + 2, Kind::Word);
    }
    (at, Kind::Word)
}

/// `text` with every tab outside strings and comments replaced by a space.
/// LLVM reads both as whitespace; the line reader's spelled patterns
/// (`align `, `section "`, ` global `) expect a space, so a tab there would
/// make a clause disappear (`, align\t8` was dropped).
pub(crate) fn blank_tabs(text: &str, tokens: &[Token]) -> String {
    let mut bytes = text.as_bytes().to_vec();
    let mut previous_end = 0;
    let blank = |from: usize, to: usize, bytes: &mut Vec<u8>| {
        // Between two tokens: whitespace and at most one comment, which
        // runs from its `;` to the line feed.
        let mut in_comment = false;
        for byte in &mut bytes[from..to] {
            match *byte {
                b';' => in_comment = true,
                b'\n' => in_comment = false,
                b'\t' if !in_comment => *byte = b' ',
                _ => {}
            }
        }
    };
    for token in tokens {
        blank(previous_end, token.start, &mut bytes);
        previous_end = token.end;
    }
    blank(previous_end, bytes.len(), &mut bytes);
    // Only ASCII tabs were replaced by ASCII spaces.
    String::from_utf8(bytes).unwrap_or_else(|_| text.to_string())
}

// --------------------------------------------------------------------------
// Escapes
// --------------------------------------------------------------------------

/// Decode the body of an LLVM string, quoted name or metadata name exactly as
/// LLVM's `UnEscapeLexed` (`LLLexer.cpp`) does, left to right:
///
/// * `\\` (two backslashes) is one backslash, and is recognized before a hex
///   escape, so `\\41` is a backslash followed by `4` and `1`;
/// * `\` followed by two ASCII hex digits (either case) is that byte;
/// * any other backslash (before a non-hex byte, or with fewer than two bytes
///   after it) is kept as itself.
///
/// LLVM decodes every string constant (`"..."`, `c"..."`, `!"..."`, an
/// attribute's key and value), every quoted name (`@"..."`, `%"..."`,
/// `$"..."`, a `"label":`) and every metadata name (`!\65xclude` is
/// `!exclude`) this way before it reads it. This is the importer's one
/// decoder: [`canonicalize`] applies it to every name before any reader runs,
/// and every reader of a string's content applies it through
/// [`string_value`].
pub(crate) fn decode_escapes(body: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(body.len());
    let mut i = 0;
    while i < body.len() {
        if body[i] == b'\\' {
            if body.get(i + 1) == Some(&b'\\') {
                out.push(b'\\');
                i += 2;
                continue;
            }
            if let (Some(hi), Some(lo)) = (
                body.get(i + 1).and_then(|b| (*b as char).to_digit(16)),
                body.get(i + 2).and_then(|b| (*b as char).to_digit(16)),
            ) {
                out.push(((hi << 4) | lo) as u8);
                i += 3;
                continue;
            }
        }
        out.push(body[i]);
        i += 1;
    }
    out
}

/// The decoded content of the string token spelled `spelled` (its quotes
/// included), as LLVM reads it ([`decode_escapes`]).
pub(crate) fn string_value(spelled: &str) -> Vec<u8> {
    let body = spelled
        .strip_prefix('"')
        .and_then(|body| body.strip_suffix('"'))
        .unwrap_or(spelled);
    decode_escapes(body.as_bytes())
}

/// [`string_value`] as UTF-8 text, or `None` when the decoded bytes are not
/// UTF-8 (no key or value this importer reads is).
pub(crate) fn string_text(spelled: &str) -> Option<String> {
    String::from_utf8(string_value(spelled)).ok()
}

/// A name LLVM spells without quotes (`[-a-zA-Z$._][-a-zA-Z$._0-9]*`).
pub(crate) fn is_bare_name(name: &[u8]) -> bool {
    name.first()
        .is_some_and(|&first| is_name_byte(first) && !first.is_ascii_digit())
        && name.iter().all(|&b| is_name_byte(b))
}

/// The canonical quoted spelling of a decoded name that has none without
/// quotes: every byte outside `[-a-zA-Z$._0-9]` as `\XX`, so the spelling
/// holds no space, comma, bracket or quote for a line reader to split on, and
/// two spellings of one name are one spelling.
fn quoted_name(name: &[u8]) -> String {
    let mut out = String::from("\"");
    for &b in name {
        if is_name_byte(b) {
            out.push(b as char);
        } else {
            out.push_str(&format!("\\{b:02X}"));
        }
    }
    out.push('"');
    out
}

/// The canonical spelling of a decoded metadata name, as LLVM's printer
/// writes it (`printMetadataIdentifier`): letters, `-`, `$`, `.` and `_`
/// (and digits after the first byte) as themselves, every other byte as
/// `\XX`.
fn metadata_identifier(name: &[u8]) -> String {
    let mut out = String::new();
    for (index, &b) in name.iter().enumerate() {
        let plain = b.is_ascii_alphabetic()
            || matches!(b, b'-' | b'$' | b'.' | b'_')
            || (index > 0 && b.is_ascii_digit());
        if plain {
            out.push(b as char);
        } else {
            out.push_str(&format!("\\{b:02X}"));
        }
    }
    out
}

/// The canonical spelling of `token`, when LLVM decodes it to a name the
/// importer must not read by its raw spelling: a quoted name or label, or a
/// metadata name holding a backslash. `None` for every other token, which
/// stays as spelled.
fn canonical_spelling(text: &str, token: &Token) -> Result<Option<String>> {
    let spelled = token.text(text);
    let (sigil, body, label) = match token.kind {
        Kind::Global | Kind::Local | Kind::Comdat if spelled.as_bytes().get(1) == Some(&b'"') => {
            (&spelled[..1], &spelled[2..spelled.len() - 1], false)
        }
        Kind::Label if spelled.starts_with('"') => ("", &spelled[1..spelled.len() - 2], true),
        Kind::MetadataName if spelled.contains('\\') => {
            let decoded = decode_escapes(&spelled.as_bytes()[1..]);
            return Ok(Some(format!("!{}", metadata_identifier(&decoded))));
        }
        _ => return Ok(None),
    };
    let decoded = decode_escapes(body.as_bytes());
    if decoded.contains(&0) {
        return refuse(
            token.line,
            format!(
                "the quoted name {spelled} decodes to a NUL byte (LLVM's lexer rejects it: \
                 \"NUL character is not allowed in names\")"
            ),
        );
    }
    if decoded.is_empty() {
        return refuse(
            token.line,
            format!(
                "the empty quoted name {spelled} (LLVM numbers such a value as unnamed; this \
                 importer reads names by spelling)"
            ),
        );
    }
    let colon = if label { ":" } else { "" };
    if is_bare_name(&decoded) {
        // Only name bytes: ASCII.
        let name = String::from_utf8_lossy(&decoded);
        return Ok(Some(format!("{sigil}{name}{colon}")));
    }
    // Otherwise the canonical quoted spelling. A `\01` asm label keeps its
    // `"\01..."` spelling for the symbol readers (`split_asm_label`), which
    // carry the name after `\01_` as this function spells that name alone:
    // plainly when it is a plain name, and otherwise in this quoted
    // spelling; the importer carries a quoted symbol name only as the name
    // of an internal or private definition (`refuse_quoted_symbol_names` in
    // the parser).
    Ok(Some(format!("{sigil}{}{colon}", quoted_name(&decoded))))
}

/// The name LLVM decodes a canonical quoted spelling (`"a\20b"`, quotes
/// included) to, for a diagnostic.
pub(crate) fn describe_quoted_name(spelled: &str) -> String {
    String::from_utf8_lossy(&string_value(spelled))
        .escape_debug()
        .to_string()
}

/// `text` (lexed as `tokens`) with every name rewritten to the one spelling
/// LLVM's decoded name has, before any reader runs.
///
/// LLVM decodes the `\XX` and `\\` escapes of every quoted name and every
/// metadata name ([`decode_escapes`]), so `@"\66oo"`, `@"foo"` and `@foo`
/// are one global, `%"x"` and `%x` one value, `!\65xclude` the `!exclude`
/// kind and `!llvm\2Emodule.flags` the module flags. The readers after this
/// pass match names by spelling, so each name is rewritten to its canonical
/// spelling: the plain one when the decoded name is a plain LLVM name;
/// otherwise a quoted one with every byte outside `[-a-zA-Z$._0-9]`
/// escaped (a `\01` asm label is such a name: `@"\01_a b"` is
/// `@"\01_a\20b"`); for a metadata name, the spelling LLVM's printer
/// writes. A name that decodes to a NUL byte (which LLVM rejects) and an
/// empty quoted name are refused by name. The importer carries a quoted
/// symbol name, the name after a `\01_` asm label that is no plain name
/// included, only for an internal or private definition
/// (`refuse_quoted_symbol_names` in the parser).
///
/// String constants keep their spelling: the line readers rely on their
/// escapes to hide punctuation, and every reader of a string's content
/// decodes it with [`string_value`].
///
/// A space is inserted where a rewritten name would otherwise run into the
/// token after it (`@"g"addrspace(0)`): LLVM reads two tokens there either
/// way.
pub(crate) fn canonicalize(text: &str, tokens: &[Token]) -> Result<String> {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut copied = 0;
    for token in tokens {
        let Some(replacement) = canonical_spelling(text, token)? else {
            continue;
        };
        if replacement == token.text(text) {
            continue;
        }
        out.push_str(&text[copied..token.start]);
        let first = replacement.as_bytes()[0];
        if is_name_byte(first)
            && token
                .start
                .checked_sub(1)
                .is_some_and(|before| is_name_byte(bytes[before]))
        {
            out.push(' ');
        }
        out.push_str(&replacement);
        let last = replacement.as_bytes()[replacement.len() - 1];
        if is_name_byte(last) && bytes.get(token.end).is_some_and(|&b| is_name_byte(b)) {
            out.push(' ');
        }
        copied = token.end;
    }
    out.push_str(&text[copied..]);
    Ok(out)
}

// --------------------------------------------------------------------------
// Keyword tables
// --------------------------------------------------------------------------

/// The words that start a top-level entity.
const TOP_LEVEL_KEYWORDS: [&str; 8] = [
    "define",
    "declare",
    "attributes",
    "target",
    "source_filename",
    "module",
    "uselistorder",
    "uselistorder_bb",
];

/// Every instruction opcode of LLVM 22, and the call markers that start
/// one (`tail call`).
const OPCODES: [&str; 70] = [
    "ret",
    "br",
    "switch",
    "indirectbr",
    "invoke",
    "resume",
    "unreachable",
    "cleanupret",
    "catchret",
    "catchswitch",
    "catchpad",
    "cleanuppad",
    "callbr",
    "fneg",
    "add",
    "fadd",
    "sub",
    "fsub",
    "mul",
    "fmul",
    "udiv",
    "sdiv",
    "fdiv",
    "urem",
    "srem",
    "frem",
    "shl",
    "lshr",
    "ashr",
    "and",
    "or",
    "xor",
    "extractelement",
    "insertelement",
    "shufflevector",
    "extractvalue",
    "insertvalue",
    "alloca",
    "load",
    "store",
    "fence",
    "cmpxchg",
    "atomicrmw",
    "getelementptr",
    "trunc",
    "zext",
    "sext",
    "fptrunc",
    "fpext",
    "fptoui",
    "fptosi",
    "uitofp",
    "sitofp",
    "ptrtoint",
    "ptrtoaddr",
    "inttoptr",
    "bitcast",
    "addrspacecast",
    "icmp",
    "fcmp",
    "phi",
    "select",
    "call",
    "va_arg",
    "landingpad",
    "freeze",
    "tail",
    "musttail",
    "notail",
    "uselistorder",
];

/// Flag keywords that may stand between a constant-expression operator and
/// its `(`.
const CONSTANT_EXPRESSION_FLAGS: [&str; 7] = [
    "inbounds", "nuw", "nsw", "nusw", "exact", "disjoint", "inrange",
];

/// The calling conventions LLVM 22 spells by keyword (`LLLexer.cpp`), and
/// `cc` (`cc N`). The importer models `ccc` and `fastcc` only
/// ([`modeled_calling_convention`]).
pub(crate) const CALLING_CONVENTION_KEYWORDS: [&str; 58] = [
    "ccc",
    "fastcc",
    "coldcc",
    "cc",
    "cfguard_checkcc",
    "x86_stdcallcc",
    "x86_fastcallcc",
    "x86_thiscallcc",
    "x86_vectorcallcc",
    "x86_regcallcc",
    "x86_intrcc",
    "x86_64_sysvcc",
    "win64cc",
    "arm_apcscc",
    "arm_aapcscc",
    "arm_aapcs_vfpcc",
    "aarch64_vector_pcs",
    "aarch64_sve_vector_pcs",
    "aarch64_sme_preservemost_from_x0",
    "aarch64_sme_preservemost_from_x1",
    "aarch64_sme_preservemost_from_x2",
    "msp430_intrcc",
    "avr_intrcc",
    "avr_signalcc",
    "ptx_kernel",
    "ptx_device",
    "spir_kernel",
    "spir_func",
    "intel_ocl_bicc",
    "swiftcc",
    "swifttailcc",
    "anyregcc",
    "preserve_mostcc",
    "preserve_allcc",
    "preserve_nonecc",
    "ghccc",
    "hhvmcc",
    "hhvm_ccc",
    "cxx_fast_tlscc",
    "tailcc",
    "m68k_rtdcc",
    "graalcc",
    "riscv_vector_cc",
    "riscv_vls_cc",
    "webkit_jscc",
    "amdgpu_vs",
    "amdgpu_ls",
    "amdgpu_hs",
    "amdgpu_es",
    "amdgpu_gs",
    "amdgpu_ps",
    "amdgpu_cs",
    "amdgpu_cs_chain",
    "amdgpu_cs_chain_preserve",
    "amdgpu_kernel",
    "amdgpu_gfx",
    "amdgpu_gfx_whole_wave",
    "x86_64_win64cc",
];

/// What llc does with a metadata attachment of kind `kind` that changes
/// the object it writes, or `None` for a kind it reads only as an
/// optimization fact or hint (`!range`, `!prof`, `!tbaa`, `!llvm.loop`),
/// as debug information (`!dbg`), for link-time passes (`!type`) or not at
/// all (a kind LLVM does not define).
fn codegen_metadata_kind(kind: &str) -> Option<&'static str> {
    Some(match kind {
        "associated" => "llc links the global's section to another's (`SHF_LINK_ORDER`)",
        "exclude" => "llc marks the global's section excluded from the link (`SHF_EXCLUDE`)",
        "section_prefix" => "llc adds the prefix to the section name (`.data.hot.`)",
        "absolute_symbol" => "llc addresses the symbol as an absolute value in the stated range",
        "func_sanitize" => "llc emits the UBSan function signature words before the function",
        "kcfi_type" => "llc emits the KCFI type hash before the function",
        "pcsections" => "llc emits the PC-section entries it names",
        "implicit.ref" => "llc emits a reference that keeps another symbol in the link",
        // `SSPLayoutAnalysis` skips an alloca marked `!{i32 0}` (and reads
        // the operand of any other value), so llc may build no canary where
        // the importer's `ssp` policy protects the array.
        "stack-protector" => "llc's stack protector leaves an alloca marked `!{i32 0}` unprotected",
        _ => return None,
    })
}

/// Whether `word` is one of LLVM's calling-convention keywords.
pub(crate) fn is_calling_convention_keyword(word: &str) -> bool {
    CALLING_CONVENTION_KEYWORDS.contains(&word)
}

/// The calling conventions the importer models, both as trust-ir's C
/// convention: `ccc` is C, and LLVM lowers `fastcc` like C unless
/// `-tailcallopt` is given, which no object path here passes. On AArch64,
/// `CCAssignFnForCall` assigns `Fast` with the C tables (AAPCS64 and
/// DarwinPCS); the AArch64 Linux llc differential calls twelve-argument
/// `fastcc` functions each way between llc and imported objects at O0-O3.
/// On x86-64 System V, `CC_X86_64` has no `Fast` case; that leg rests on
/// LLVM's tables and is not executed here. On RISC-V `fastcc` is not C
/// (`CC_RISCV_FastCC` passes integer arguments 9 to 12 in `x28`-`x31`), so
/// the parser refuses it for a RISC-V compile target and when none is
/// known (`Parser::parse`, after this check, once the target is read).
pub(crate) fn modeled_calling_convention(word: &str) -> bool {
    matches!(word, "ccc" | "fastcc")
}

// --------------------------------------------------------------------------
// Module-level checks
// --------------------------------------------------------------------------

/// Refuse by name every module the line reader would read differently from
/// LLVM's token-based parser (see [`lex`] for the bytes):
///
/// * a calling-convention keyword other than `ccc`/`fastcc`, anywhere (on a
///   `define`, a `declare` or a call): the importer would lower the function
///   or the call with the C convention;
/// * two tokens LLVM splits but the line reader, which splits on
///   whitespace, would read as one: a keyword, number, name or string glued
///   to a following string, name, number, keyword or `[`/`{`/`<`/`!`
///   (`section"x"`, `prologue[2 x i32]`, `ptr@g`, `i64-1`, `global[4 x i8]`).
///   Admitted: `c"..."`, and a glued `addrspace`, which
///   `check_module_lexically` reads;
/// * a second top-level entity on a line (`attributes #0 = { } declare
///   hidden ...`), or a top-level entity continued on a later line;
/// * a function header continued on a later line (only its `{` may start
///   the next line), a body starting on the header line, and a closing `}`
///   that shares its line with anything;
/// * a second instruction on a line, a label sharing a line, and an
///   instruction continued on a later line (only a `switch` case list may
///   span lines), or one whose brackets do not balance;
/// * a metadata attachment whose kind llc's code generator or object writer
///   reads ([`codegen_metadata_kind`]), on a global, a function or an
///   instruction. `text` is canonical ([`canonicalize`]), so the kind is
///   read as LLVM decodes it (`!\65xclude` is `!exclude`).
///
/// It reads tokens and lines only. The readers that run after it read the
/// tokens of each line (`crate::attributes`, `parse_function_clauses`,
/// `parse_global_clauses`, the call readers) and refuse by name what they
/// do not read.
pub(crate) fn check_module(text: &str, tokens: &[Token]) -> Result<()> {
    check_tokens(text, tokens)?;
    check_structure(text, tokens)
}

fn check_tokens(text: &str, tokens: &[Token]) -> Result<()> {
    for (index, token) in tokens.iter().enumerate() {
        let spelled = token.text(text);
        if token.kind == Kind::Word && is_calling_convention_keyword(spelled) {
            if spelled == "cc" {
                return refuse(
                    token.line,
                    "numbered calling convention `cc N` (the importer models only `ccc` and \
                     `fastcc`, both as the C convention)",
                );
            }
            if !modeled_calling_convention(spelled) {
                return refuse(
                    token.line,
                    format!(
                        "calling convention `{spelled}` (the importer models only `ccc` and \
                         `fastcc`, both as the C convention; lowering this one as C would not \
                         follow its argument, result or preserved-register rules)"
                    ),
                );
            }
        }
        // `musttail call` GUARANTEES a tail call: a recursion that relies on it
        // runs in constant stack under LLVM. The backend lowers it as a plain
        // call, so a deep recursion would overflow where LLVM's build completes.
        // `tail` and `notail` are hints and stay admitted.
        if token.kind == Kind::Word && spelled == "musttail" {
            return refuse(
                token.line,
                "`musttail call` (a guaranteed tail call; this backend lowers it as a plain \
                 call and does not guarantee the tail call, so a recursion relying on it could \
                 overflow the stack)",
            );
        }
        // A metadata attachment (never the first token of its line; a named
        // metadata definition is) whose kind llc's code generator or object
        // writer reads. The importer reads no metadata.
        if token.kind == Kind::MetadataName
            && !token.line_first
            && let Some(why) = codegen_metadata_kind(&spelled[1..])
        {
            return refuse(
                token.line,
                format!(
                    "metadata attachment `{spelled}` ({why}; this importer reads no metadata, \
                     so it would drop it)"
                ),
            );
        }
        if !token.glued || index == 0 {
            continue;
        }
        let previous = tokens[index - 1];
        let previous_text = previous.text(text);
        let previous_is_operand = matches!(
            previous.kind,
            Kind::Word
                | Kind::Number
                | Kind::Global
                | Kind::Local
                | Kind::Comdat
                | Kind::MetadataName
                | Kind::AttrGroup
                | Kind::Summary
                | Kind::Str
        );
        let opens_a_token = matches!(
            token.kind,
            Kind::Word
                | Kind::Number
                | Kind::Global
                | Kind::Local
                | Kind::Comdat
                | Kind::MetadataName
                | Kind::AttrGroup
                | Kind::DbgRecord
                | Kind::Summary
                | Kind::Str
                | Kind::Ellipsis
                | Kind::Punct(b'[' | b'{' | b'<' | b'!')
        );
        if !previous_is_operand || !opens_a_token {
            continue;
        }
        let admitted = (previous.is_word(text, "c") && token.kind == Kind::Str)
            || token.is_word(text, "addrspace");
        if admitted {
            continue;
        }
        return refuse(
            token.line,
            format!(
                "`{previous_text}` glued to `{}` (LLVM's lexer reads two tokens there; this \
                 importer splits on whitespace and would read one)",
                token.text(text)
            ),
        );
    }
    Ok(())
}

/// Whether the token at `index` starts a top-level entity.
fn starts_entity(text: &str, tokens: &[Token], index: usize) -> bool {
    let token = tokens[index];
    let next_is_equal = tokens
        .get(index + 1)
        .is_some_and(|next| next.kind == Kind::Punct(b'='));
    match token.kind {
        Kind::Word => TOP_LEVEL_KEYWORDS.contains(&token.text(text)),
        Kind::Global | Kind::Local | Kind::Comdat | Kind::MetadataName | Kind::Summary => {
            next_is_equal
        }
        // `!0 = ...`
        Kind::Punct(b'!') => {
            tokens
                .get(index + 1)
                .is_some_and(|number| number.kind == Kind::Number)
                && tokens
                    .get(index + 2)
                    .is_some_and(|equal| equal.kind == Kind::Punct(b'='))
        }
        _ => false,
    }
}

fn describe(text: &str, token: &Token) -> String {
    format!("`{}`", token.text(text))
}

fn check_structure(text: &str, tokens: &[Token]) -> Result<()> {
    let mut index = 0;
    while index < tokens.len() {
        let token = tokens[index];
        if !starts_entity(text, tokens, index) {
            return refuse(
                token.line,
                format!(
                    "{} continues a top-level entity from an earlier line or starts none \
                     (LLVM reads an entity across lines; this importer reads one entity per \
                     line)",
                    describe(text, &token)
                ),
            );
        }
        if !token.line_first {
            return refuse(
                token.line,
                format!(
                    "a second top-level entity on one line ({} starts it; this importer reads \
                     one entity per line and would drop it)",
                    describe(text, &token)
                ),
            );
        }
        if token.is_word(text, "define") {
            index = check_function(text, tokens, index)?;
            continue;
        }
        // Any other entity: the rest of its line, and nothing after it.
        index += 1;
        while index < tokens.len() && !tokens[index].line_first {
            if starts_entity(text, tokens, index) {
                return refuse(
                    tokens[index].line,
                    format!(
                        "a second top-level entity on one line ({} starts it; this importer \
                         reads one entity per line and would drop it)",
                        describe(text, &tokens[index])
                    ),
                );
            }
            index += 1;
        }
    }
    Ok(())
}

/// Bracket depth change of one token.
fn depth_step(token: &Token) -> i32 {
    match token.kind {
        Kind::Punct(b'(' | b'[' | b'{' | b'<') => 1,
        Kind::Punct(b')' | b']' | b'}' | b'>') => -1,
        _ => 0,
    }
}

/// Check one `define` (its header at `start`) and return the index after
/// its closing `}`.
fn check_function(text: &str, tokens: &[Token], start: usize) -> Result<usize> {
    let header_line = tokens[start].line;
    // The header: every token on the `define` line. Its last token is the
    // body's `{` (the line reader cuts the header at its last `{`), or the
    // `{` is the only token of a later line.
    let mut end = start + 1;
    while end < tokens.len() && !tokens[end].line_first {
        end += 1;
    }
    if end == start + 1 {
        // `define` alone on its line, or the module's last token.
        return refuse(
            header_line,
            "`define` ends its line (LLVM reads the header from the next line; this importer \
             reads a header on one line, and only its `{` may start the next line, alone)",
        );
    }
    let last = tokens[end - 1];
    let mut depth = 0i32;
    for token in &tokens[start + 1..end - 1] {
        depth += depth_step(token);
    }
    let body_open = if last.kind == Kind::Punct(b'{') && depth == 0 {
        end - 1
    } else {
        depth += depth_step(&last);
        if let Some(open) = body_brace_on_header_line(text, tokens, start, end) {
            return refuse(
                tokens[open].line,
                "a function body that starts on its header line (LLVM reads the instructions \
                 after `{`; this importer reads the body from the next line)",
            );
        }
        match tokens.get(end) {
            Some(open)
                if open.kind == Kind::Punct(b'{')
                    && depth == 0
                    && tokens.get(end + 1).is_none_or(|next| next.line_first) =>
            {
                end
            }
            Some(next) => {
                return refuse(
                    next.line,
                    format!(
                        "the header of the function on line {header_line} continues on this \
                         line ({}; this importer reads a header on one line, and only its `{{` \
                         may start the next line, alone)",
                        describe(text, next)
                    ),
                );
            }
            None => {
                return refuse(header_line, "a function definition without a body");
            }
        }
    };
    check_body(text, tokens, body_open)
}

/// The first `{` at bracket depth 0 after the parameter list of the
/// `define` whose header line is `tokens[start..end]`: a body brace with
/// tokens after it on the line. A `{` before the name (a struct return type)
/// or inside the parameter list is part of the header, and one after a
/// `prefix`/`prologue` word is that clause's constant, which the header
/// reader refuses by name.
fn body_brace_on_header_line(
    text: &str,
    tokens: &[Token],
    start: usize,
    end: usize,
) -> Option<usize> {
    let name = tokens[start..end]
        .iter()
        .position(|token| token.kind == Kind::Global)
        .map(|at| start + at)?;
    let mut depth = 0i32;
    let mut closed_params = false;
    for (index, token) in tokens.iter().enumerate().take(end).skip(name + 1) {
        if closed_params && depth == 0 {
            if token.kind == Kind::Word && matches!(token.text(text), "prefix" | "prologue") {
                return None;
            }
            if token.kind == Kind::Punct(b'{') {
                return Some(index);
            }
        }
        depth += depth_step(token);
        if depth == 0 && token.kind == Kind::Punct(b')') {
            closed_params = true;
        }
    }
    None
}

/// Check the body opened by the `{` at `open`; return the index after its
/// closing `}`.
fn check_body(text: &str, tokens: &[Token], open: usize) -> Result<usize> {
    let mut index = open + 1;
    while index < tokens.len() {
        let token = tokens[index];
        if !token.line_first {
            // Tokens after the `{` on a later line holding only it, which
            // `check_function` excluded, or after an instruction's end.
            return refuse(
                token.line,
                format!(
                    "{} follows the function's `{{` on its line (this importer reads the body \
                     from the next line)",
                    describe(text, &token)
                ),
            );
        }
        match token.kind {
            Kind::Punct(b'}') => {
                if let Some(next) = tokens.get(index + 1)
                    && !next.line_first
                {
                    return refuse(
                        next.line,
                        format!(
                            "{} after the function's closing `}}` on its line (this importer \
                             reads a line holding only `}}` as the end of the body)",
                            describe(text, next)
                        ),
                    );
                }
                return Ok(index + 1);
            }
            Kind::Label => {
                if let Some(next) = tokens.get(index + 1)
                    && !next.line_first
                {
                    return refuse(
                        next.line,
                        format!(
                            "the block label {} shares its line with {} (this importer reads \
                             a label only on a line of its own)",
                            describe(text, &token),
                            describe(text, next)
                        ),
                    );
                }
                index += 1;
            }
            _ => index = check_instruction(text, tokens, index)?,
        }
    }
    refuse(
        tokens[open].line,
        "a function body that is never closed (no `}`)",
    )
}

/// Whether the opcode word at `index` stands in operand position: a
/// constant-expression operator (followed, after its flags, by `(`), the
/// operation of an `atomicrmw`, or the `call` of a `tail call`.
fn opcode_is_an_operand(text: &str, tokens: &[Token], index: usize) -> bool {
    let previous = index.checked_sub(1).map(|at| tokens[at].text(text));
    if matches!(previous, Some("atomicrmw"))
        || (matches!(previous, Some("volatile"))
            && index >= 2
            && tokens[index - 2].is_word(text, "atomicrmw"))
    {
        return true;
    }
    if tokens[index].is_word(text, "call")
        && matches!(previous, Some("tail" | "musttail" | "notail"))
    {
        return true;
    }
    let mut at = index + 1;
    while let Some(token) = tokens.get(at) {
        if token.kind == Kind::Word && CONSTANT_EXPRESSION_FLAGS.contains(&token.text(text)) {
            at += 1;
            // `inrange(a, b)`
            if tokens.get(at).is_some_and(|t| t.kind == Kind::Punct(b'(')) && !token.glued {
                // A spaced `(` after a flag is the operand list itself.
                return true;
            }
            if tokens.get(at).is_some_and(|t| t.kind == Kind::Punct(b'(')) {
                let mut depth = 0;
                while let Some(t) = tokens.get(at) {
                    depth += depth_step(t);
                    at += 1;
                    if depth == 0 {
                        break;
                    }
                }
            }
            continue;
        }
        return token.kind == Kind::Punct(b'(');
    }
    false
}

/// Check the instruction starting the line at `start`; return the index of
/// the first token of the next line after it.
fn check_instruction(text: &str, tokens: &[Token], start: usize) -> Result<usize> {
    let first = tokens[start];
    let spelled = first.text(text);
    let assigns = matches!(first.kind, Kind::Local)
        && tokens
            .get(start + 1)
            .is_some_and(|equal| equal.kind == Kind::Punct(b'=') && !equal.line_first);
    let opcode_at = if assigns { start + 2 } else { start };
    let starts_instruction = assigns
        || first.kind == Kind::DbgRecord
        || (first.kind == Kind::Word && OPCODES.contains(&spelled));
    if !starts_instruction {
        return refuse(
            first.line,
            format!(
                "{} starts no instruction: it continues one from an earlier line (LLVM reads \
                 an instruction across lines; this importer reads one instruction per line, \
                 except a `switch` case list)",
                describe(text, &first)
            ),
        );
    }
    let is_switch = tokens
        .get(opcode_at)
        .is_some_and(|opcode| opcode.is_word(text, "switch"));
    let second = |token: &Token, why: &str| {
        refuse::<usize>(
            token.line,
            format!(
                "a second instruction or entity on one line ({} {why}; this importer reads one \
                 instruction per line and would drop the rest)",
                describe(text, token)
            ),
        )
    };
    let mut depth = 0i32;
    let mut index = start;
    loop {
        index += 1;
        let Some(token) = tokens.get(index) else {
            break;
        };
        if token.line_first {
            if depth == 0 {
                break;
            }
            if !(is_switch && depth > 0) {
                return refuse(
                    token.line,
                    "an instruction continued on this line (LLVM reads an instruction across \
                     lines; this importer reads one instruction per line, except a `switch` \
                     case list)",
                );
            }
        }
        if depth == 0 {
            match token.kind {
                Kind::Punct(b'=')
                    if !(assigns && index == start + 1) && tokens[index - 1].kind != Kind::Str =>
                {
                    let target = tokens[index - 1];
                    return refuse(
                        token.line,
                        format!(
                            "a second instruction or entity on one line (`{} =` assigns a \
                             second value; this importer reads one instruction per line and \
                             would drop the rest)",
                            target.text(text)
                        ),
                    );
                }
                Kind::Label => return second(token, "is a block label"),
                Kind::DbgRecord => return second(token, "is a debug record"),
                Kind::Punct(b'}') => {
                    return refuse(
                        token.line,
                        "the function's closing `}` shares its line with an instruction (this \
                         importer reads a line holding only `}` as the end of the body)",
                    );
                }
                Kind::Word
                    if index != opcode_at
                        && OPCODES.contains(&token.text(text))
                        && !opcode_is_an_operand(text, tokens, index) =>
                {
                    return second(token, "starts a second instruction");
                }
                _ => {}
            }
        }
        depth += depth_step(token);
        if depth < 0 {
            return refuse(
                token.line,
                format!(
                    "unbalanced {} in an instruction (LLVM's parser rejects it)",
                    describe(text, token)
                ),
            );
        }
    }
    if depth != 0 {
        return refuse(
            first.line,
            "an instruction whose brackets are never closed (LLVM's parser rejects it)",
        );
    }
    Ok(index)
}
