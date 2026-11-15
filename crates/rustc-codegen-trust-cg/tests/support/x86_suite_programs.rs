//! Read the whole-program tables of the x86-64 bridge feature suites.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! The feature suites (`tests/*_x86*.rs`: iterators, closures, dyn dispatch,
//! enums and niches, drops, collections, formatting, std `fn main`, ...)
//! spell most of their programs as table literals:
//!
//! ```text
//! let shapes: &[(&str, &str, i32)] = &[ ("name", "fn main() { .. }", 42), .. ];
//! let cases: &[(&str, &str)] = &[ ("name", r#"fn main() { .. }"#), .. ];
//! ```
//!
//! Those suites compile for x86-64 and run only on an x86-64 host. This
//! module reads the tables out of a suite's source text so an AArch64 lane can
//! run the same programs natively, without a copy that drifts. It lexes Rust
//! string literals (escapes, line continuations, raw strings), integer
//! literals and comments; a row is harvested only when it is exactly
//! `(string, string, integer)` or `(string, string)` and its second string is
//! a whole program (it defines `fn main`). Every other row (a fragment the
//! suite wraps in its own preamble, a source built by a macro or a constant)
//! is counted, never guessed at.
#![allow(dead_code)]

/// One harvested program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuiteProgram {
    /// The suite file's stem, e.g. `closures_x86`.
    pub suite: String,
    /// The row's name, unique within its suite once prefixed by the table.
    pub name: String,
    /// The whole program.
    pub src: String,
    /// The exit code the suite pins, for a `(&str, &str, i32)` row.
    pub expected: Option<i32>,
}

/// What one suite's tables yielded.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Harvest {
    pub programs: Vec<SuiteProgram>,
    /// Table rows that are not a whole literal program.
    pub other_rows: usize,
    /// Tables of a harvested shape.
    pub tables: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Shape {
    /// `(&str, &str, i32)`: a program, its name and its pinned exit code.
    Exit,
    /// `(&str, &str)`: a program and its name.
    Pair,
    /// `(&str, &str, bool)`: a program, its name and a suite policy flag.
    Flag,
}

const TABLES: [(&str, Shape); 3] = [
    ("&[(&str, &str, i32)] = &[", Shape::Exit),
    ("&[(&str, &str)] = &[", Shape::Pair),
    ("&[(&str, &str, bool)] = &[", Shape::Flag),
];

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Str(String),
    Int(i64),
    Open,
    Close,
    Comma,
    Other,
}

/// Lex one Rust string literal whose opening quote is at `text[at]`; return
/// the value and the index after the closing quote.
fn lex_string(text: &[u8], at: usize) -> Result<(String, usize), String> {
    let mut out = Vec::new();
    let mut i = at + 1;
    loop {
        let Some(&byte) = text.get(i) else {
            return Err("unterminated string literal".to_owned());
        };
        match byte {
            b'"' => break,
            b'\\' => {
                let escape = *text.get(i + 1).ok_or("unterminated escape")?;
                i += 2;
                match escape {
                    b'\n' | b'\r' => {
                        while text.get(i).is_some_and(|b| b" \t\n\r".contains(b)) {
                            i += 1;
                        }
                    }
                    b'n' => out.push(b'\n'),
                    b'r' => out.push(b'\r'),
                    b't' => out.push(b'\t'),
                    b'0' => out.push(0),
                    b'\\' | b'"' | b'\'' => out.push(escape),
                    b'x' => {
                        let hex =
                            std::str::from_utf8(text.get(i..i + 2).ok_or("short \\x escape")?)
                                .map_err(|_| "non-ASCII \\x escape")?;
                        out.push(u8::from_str_radix(hex, 16).map_err(|_| "bad \\x escape")?);
                        i += 2;
                    }
                    b'u' => {
                        let close = text[i..]
                            .iter()
                            .position(|b| *b == b'}')
                            .ok_or("unterminated \\u escape")?;
                        let hex = std::str::from_utf8(&text[i + 1..i + close])
                            .map_err(|_| "non-ASCII \\u escape")?;
                        let scalar = u32::from_str_radix(hex, 16).map_err(|_| "bad \\u escape")?;
                        let ch = char::from_u32(scalar).ok_or("\\u escape is not a scalar")?;
                        let mut buf = [0u8; 4];
                        out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                        i += close + 1;
                    }
                    other => return Err(format!("unknown escape \\{}", other as char)),
                }
            }
            _ => {
                out.push(byte);
                i += 1;
            }
        }
    }
    let value = String::from_utf8(out).map_err(|_| "string literal is not UTF-8")?;
    Ok((value, i + 1))
}

/// Lex a raw string `r"..."` / `r#"..."#` starting at `text[at] == b'r'`.
fn lex_raw_string(text: &[u8], at: usize) -> Option<(String, usize)> {
    let mut i = at + 1;
    let mut hashes = 0;
    while text.get(i) == Some(&b'#') {
        hashes += 1;
        i += 1;
    }
    if text.get(i) != Some(&b'"') {
        return None;
    }
    let start = i + 1;
    let mut close = Vec::with_capacity(hashes + 1);
    close.push(b'"');
    close.extend(std::iter::repeat_n(b'#', hashes));
    let len = text[start..]
        .windows(close.len())
        .position(|window| window == close.as_slice())?;
    let value = String::from_utf8(text[start..start + len].to_vec()).ok()?;
    Some((value, start + len + close.len()))
}

/// Tokens from `text[at..]` up to the `]` that closes the table.
fn lex_table(text: &str, at: usize) -> Result<Vec<Token>, String> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut depth = 0usize;
    let mut i = at;
    while let Some(&byte) = bytes.get(i) {
        match byte {
            b' ' | b'\t' | b'\n' | b'\r' => i += 1,
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                i = text[i..].find('\n').map_or(bytes.len(), |n| i + n);
            }
            b'/' if bytes.get(i + 1) == Some(&b'*') => {
                i = text[i..]
                    .find("*/")
                    .map(|n| i + n + 2)
                    .ok_or("unterminated block comment")?;
            }
            // A char literal ('x', '\'', '"') or a lifetime: never a string.
            b'\'' => {
                i += match (bytes.get(i + 1), bytes.get(i + 2)) {
                    (Some(b'\\'), _) => text[i + 3..].find('\'').map_or(bytes.len() - i, |n| n + 4),
                    (Some(_), Some(b'\'')) => 3,
                    _ => 1,
                };
            }
            b'"' => {
                let (value, next) = lex_string(bytes, i)?;
                tokens.push(Token::Str(value));
                i = next;
            }
            b'r' if matches!(bytes.get(i + 1), Some(b'"') | Some(b'#')) => {
                let (value, next) = lex_raw_string(bytes, i).ok_or("malformed raw string")?;
                tokens.push(Token::Str(value));
                i = next;
            }
            b'(' | b'[' | b'{' => {
                depth += 1;
                tokens.push(if byte == b'(' {
                    Token::Open
                } else {
                    Token::Other
                });
                i += 1;
            }
            b']' if depth == 0 => return Ok(tokens),
            b')' | b']' | b'}' => {
                depth = depth.checked_sub(1).ok_or("unbalanced table")?;
                tokens.push(if byte == b')' {
                    Token::Close
                } else {
                    Token::Other
                });
                i += 1;
            }
            b',' => {
                tokens.push(Token::Comma);
                i += 1;
            }
            b'-' | b'0'..=b'9' => {
                let start = i;
                i += 1;
                while bytes
                    .get(i)
                    .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
                {
                    i += 1;
                }
                let spelled: String = text[start..i].chars().filter(|c| *c != '_').collect();
                let spelled = ["i32", "i64", "u8", "u32", "usize"]
                    .iter()
                    .find_map(|suffix| spelled.strip_suffix(suffix))
                    .unwrap_or(&spelled);
                let (negative, digits) = match spelled.strip_prefix('-') {
                    Some(digits) => (true, digits),
                    None => (false, spelled),
                };
                let value = match digits.strip_prefix("0x") {
                    Some(hex) => i64::from_str_radix(hex, 16).ok(),
                    None => digits.parse::<i64>().ok(),
                };
                tokens.push(match value {
                    Some(value) if negative => Token::Int(-value),
                    Some(value) => Token::Int(value),
                    None => Token::Other,
                });
            }
            // An identifier or keyword (`true`, `concat`, a constant) is one token.
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                while bytes
                    .get(i)
                    .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_')
                {
                    i += 1;
                }
                tokens.push(Token::Other);
            }
            _ => {
                tokens.push(Token::Other);
                i += text[i..].chars().next().map_or(1, char::len_utf8);
            }
        }
    }
    Err("table has no closing `]`".to_owned())
}

/// The depth-one tuples of a table's tokens; `None` marks a row that is not a
/// flat tuple of literals.
fn rows(tokens: &[Token]) -> Vec<Option<Vec<Token>>> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut row: Vec<Token> = Vec::new();
    let mut flat = true;
    for token in tokens {
        match token {
            Token::Open => {
                depth += 1;
                if depth == 1 {
                    row.clear();
                    flat = true;
                } else {
                    flat = false;
                }
            }
            Token::Close => {
                if depth == 1 {
                    out.push(flat.then(|| row.clone()));
                }
                depth = depth.saturating_sub(1);
            }
            Token::Comma if depth == 1 => {}
            _ if depth == 1 => row.push(token.clone()),
            _ if depth > 1 => {}
            // A top-level token outside any tuple is not a row.
            _ => {}
        }
    }
    out
}

fn is_program(src: &str) -> bool {
    src.contains("fn main")
}

/// A row's name as a census-safe word: ASCII letters and digits kept, every
/// other character `_`, at most 64 characters.
fn spell_name(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .take(64)
        .collect()
}

/// The `const NAME: &str = "...";` items of `text` that the suite prepends to
/// its programs (`format!("{NAME}{..}")`), as `(offset, value)`.
fn preambles(text: &str) -> Result<Vec<(usize, String)>, String> {
    let mut out = Vec::new();
    for (at, _) in text.match_indices("const ") {
        let rest = &text[at + "const ".len()..];
        let name_len = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        let name = &rest[..name_len];
        let Some(value_at) = rest[name_len..].strip_prefix(": &str = ") else {
            continue;
        };
        if name.is_empty() || !text.contains(&format!("format!(\"{{{name}}}{{")) {
            continue;
        }
        let offset = text.len() - value_at.len();
        let bytes = text.as_bytes();
        let value = match bytes.get(offset) {
            Some(b'"') => lex_string(bytes, offset)?.0,
            Some(b'r') => {
                lex_raw_string(bytes, offset)
                    .ok_or("malformed raw preamble")?
                    .0
            }
            _ => continue,
        };
        out.push((at, value));
    }
    Ok(out)
}

/// Every whole program of `suite`'s harvested tables, in source order. The
/// program is whichever of the row's two strings defines `fn main` (suites
/// spell `(name, program, ..)` and `(program, name, ..)`); a row where both
/// or neither does is counted, not harvested. A table's programs get the
/// preamble the suite prepends to them: a `const NAME: &str` defined after
/// the previous table and before this one and spliced as `format!("{NAME}..")`.
/// A repeated name within a table gets a `~<n>` suffix.
pub fn harvest(suite: &str, text: &str) -> Result<Harvest, String> {
    let mut found: Vec<(usize, Shape)> = Vec::new();
    for (header, shape) in TABLES {
        found.extend(
            text.match_indices(header)
                .map(|(at, _)| (at + header.len(), shape)),
        );
    }
    found.sort_unstable();
    let preambles = preambles(text).map_err(|error| format!("{suite}: {error}"))?;
    let mut harvest = Harvest::default();
    let mut previous_table = 0usize;
    for (table_index, (at, shape)) in found.into_iter().enumerate() {
        harvest.tables += 1;
        let local: Vec<&String> = preambles
            .iter()
            .filter(|(offset, _)| *offset >= previous_table && *offset < at)
            .map(|(_, value)| value)
            .collect();
        previous_table = at;
        let preamble = match local.as_slice() {
            [] => "",
            [one] => one.as_str(),
            _ => {
                return Err(format!(
                    "{suite} table {table_index}: more than one preamble"
                ));
            }
        };
        let tokens =
            lex_table(text, at).map_err(|error| format!("{suite} table {table_index}: {error}"))?;
        let mut seen = std::collections::BTreeMap::<String, usize>::new();
        for row in rows(&tokens) {
            let fields = match (row.as_deref(), shape) {
                (Some([Token::Str(a), Token::Str(b), Token::Int(code)]), Shape::Exit) => {
                    i32::try_from(*code).ok().map(|code| (a, b, Some(code)))
                }
                (Some([Token::Str(a), Token::Str(b)]), Shape::Pair) => Some((a, b, None)),
                (Some([Token::Str(a), Token::Str(b), Token::Other]), Shape::Flag) => {
                    Some((a, b, None))
                }
                _ => None,
            };
            let program =
                fields.and_then(|(a, b, expected)| match (is_program(a), is_program(b)) {
                    (false, true) => Some((a, b, expected)),
                    (true, false) => Some((b, a, expected)),
                    _ => None,
                });
            let Some((name, src, expected)) = program else {
                harvest.other_rows += 1;
                continue;
            };
            let base = format!("t{table_index}_{}", spell_name(name));
            let count = seen.entry(base.clone()).or_insert(0);
            *count += 1;
            let name = if *count == 1 {
                base
            } else {
                format!("{base}~{count}")
            };
            harvest.programs.push(SuiteProgram {
                suite: suite.to_owned(),
                name,
                src: format!("{preamble}{src}"),
                expected,
            });
        }
    }
    Ok(harvest)
}

/// Panic unless the lexer reads a fixed sample exactly: escapes, a line
/// continuation, a comment, a fragment row, a negative code and a raw string.
/// The AArch64 lane calls this before it trusts a harvest.
pub fn self_check() {
    let text = concat!(
        "let shapes: &[(&str, &str, i32)] = &[\n",
        "    // a comment (\"not a row\", \"x\", 1)\n",
        "    (\"a\", \"fn main() { \\\n         std::process::exit(\\\"7\\\".len() as i32 + 4); }\", 7),\n",
        "    (\"frag\", \"let x = '\\\"'; \", 1),\n",
        "    (\"neg\", \"fn main(){}\", -3),\n",
        "];\n",
        "let cases: &[(&str, &str)] = &[(\"r\", r#\"fn main(){ println!(\"hi\"); }\"#)];\n",
        "const PRE: &str = \"fn two() -> i32 { 2 } \";\n",
        "let more: &[(&str, &str)] = &[(\"p\", \"fn main(){ std::process::exit(two()); }\")];\n",
        "let src = format!(\"{PRE}{body}\");\n",
    );
    let harvest = harvest("demo", text).expect("the lexer self-check sample must harvest");
    assert_eq!(harvest.tables, 3, "self-check: tables");
    assert_eq!(harvest.other_rows, 1, "self-check: fragment rows");
    let names: Vec<&str> = harvest.programs.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(
        names,
        ["t0_a", "t0_neg", "t1_r", "t2_p"],
        "self-check: names"
    );
    assert_eq!(
        harvest.programs[0].src, "fn main() { std::process::exit(\"7\".len() as i32 + 4); }",
        "self-check: escapes and line continuation"
    );
    assert_eq!(
        harvest.programs[0].expected,
        Some(7),
        "self-check: exit code"
    );
    assert_eq!(
        harvest.programs[1].expected,
        Some(-3),
        "self-check: negative code"
    );
    assert_eq!(
        harvest.programs[2].src, "fn main(){ println!(\"hi\"); }",
        "self-check: raw string"
    );
    assert_eq!(harvest.programs[2].expected, None, "self-check: pair row");
    assert_eq!(
        harvest.programs[3].src, "fn two() -> i32 { 2 } fn main(){ std::process::exit(two()); }",
        "self-check: preamble"
    );
}
