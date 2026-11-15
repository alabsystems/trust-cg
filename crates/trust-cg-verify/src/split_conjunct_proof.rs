// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Re-derive the conjuncts a SPLIT producer spelling assumed from the ORIGINAL
//! conjunction, so that its proof replays against the original problem.
//!
//! [`crate::ay_bridge`]'s `and_pos` retry hands AY the query's one conjunctive
//! `(assert (and ...))` written as one `(assert C)` per conjunct, because AY
//! 0.26.0 build 9624 refuses to publish its own proof of the conjunction
//! (`invalid surface proof step t1: and_pos indexed conjunct is absent from its
//! effective source`) and publishes a checkable proof of the split script. The
//! independent checker receives ONLY the original script, whose one premise is
//! the conjunction, so every top-level `(assume t C)` of the split proof is
//! unmatched there (Carcara: `could not match term to any of the original
//! problem premises`) and the retry could never certify.
//!
//! This module rewrites the proof, never the problem:
//!
//! ```text
//! (assume tcg_split_and0 <the original conjunction, verbatim>)
//! (step tcg_split_andK (cl <nested and>) :rule and :premises (<parent>) :args (<i>))
//! (step t (cl C) :rule and :premises (<parent>) :args (<i>))   ; was (assume t C)
//! ```
//!
//! Alethe's `and` rule derives the `i`-th argument of a conjunction premise;
//! every other command passes through byte for byte, and the rewritten
//! assumption keeps its identifier, so every later premise reference still
//! resolves. The text carries NO authority: the identity-pinned checker either
//! accepts it against the original script or it is discarded, so a wrong index,
//! a term that is not a conjunct, or a forged premise is a checker rejection,
//! never credit. Anything this module cannot map with certainty (not exactly one
//! conjunctive assert, an assumed term that is not an argument of the
//! conjunction, an unbalanced or unterminated command, an identifier clash)
//! declines, and the retry keeps the original refusal.

use std::collections::HashMap;
use std::ops::Range;

/// Prefix of the identifiers this module introduces. A proof that already uses
/// it is declined rather than renamed.
const ID_PREFIX: &str = "tcg_split_and";

/// The most conjunction nodes (the root and every nested `and`) re-derived.
const MAX_AND_NODES: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Token {
    Open,
    Close,
    Atom,
}

/// SMT-LIB / Alethe lexer over `text`: parentheses, atoms (symbols, `|quoted|`
/// symbols, `"strings"`, keywords, literals) and `;` comments, yielding each
/// token's byte range. An unterminated quoted symbol or string is an error.
struct Lexer<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Lexer<'a> {
    fn new(text: &'a str) -> Self {
        Self {
            bytes: text.as_bytes(),
            at: 0,
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<(Token, Range<usize>), String>;

    fn next(&mut self) -> Option<Self::Item> {
        let bytes = self.bytes;
        loop {
            let byte = *bytes.get(self.at)?;
            match byte {
                b'(' | b')' => {
                    let start = self.at;
                    self.at += 1;
                    let token = if byte == b'(' {
                        Token::Open
                    } else {
                        Token::Close
                    };
                    return Some(Ok((token, start..self.at)));
                }
                b';' => {
                    while self.at < bytes.len() && bytes[self.at] != b'\n' {
                        self.at += 1;
                    }
                }
                _ if byte.is_ascii_whitespace() => self.at += 1,
                _ => {
                    let start = self.at;
                    while let Some(&byte) = bytes.get(self.at) {
                        match byte {
                            b'|' => {
                                self.at += 1;
                                while bytes.get(self.at).is_some_and(|&b| b != b'|') {
                                    self.at += 1;
                                }
                                if self.at == bytes.len() {
                                    return Some(Err("unterminated quoted symbol".into()));
                                }
                                self.at += 1;
                            }
                            b'"' => {
                                self.at += 1;
                                loop {
                                    match bytes.get(self.at) {
                                        None => {
                                            return Some(Err("unterminated string".into()));
                                        }
                                        Some(b'"') if bytes.get(self.at + 1) == Some(&b'"') => {
                                            self.at += 2;
                                        }
                                        Some(b'"') => {
                                            self.at += 1;
                                            break;
                                        }
                                        Some(_) => self.at += 1,
                                    }
                                }
                            }
                            b'(' | b')' | b';' => break,
                            _ if byte.is_ascii_whitespace() => break,
                            _ => self.at += 1,
                        }
                    }
                    return Some(Ok((Token::Atom, start..self.at)));
                }
            }
        }
    }
}

/// The top-level commands of `text`, each one balanced list, in order.
fn top_level_commands(text: &str) -> Result<Vec<&str>, String> {
    let mut commands = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for token in Lexer::new(text) {
        let (token, range) = token?;
        match token {
            Token::Open => {
                if depth == 0 {
                    start = range.start;
                }
                depth += 1;
            }
            Token::Close => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| "unbalanced `)`".to_string())?;
                if depth == 0 {
                    commands.push(&text[start..range.end]);
                }
            }
            Token::Atom if depth == 0 => {
                return Err(format!("stray top-level atom `{}`", &text[range]));
            }
            Token::Atom => {}
        }
    }
    if depth != 0 {
        return Err("unbalanced `(`".into());
    }
    Ok(commands)
}

/// The immediate items of `list`, which must be exactly one balanced list
/// (surrounding whitespace aside), as sub-slices of it.
fn list_items(list: &str) -> Result<Vec<&str>, String> {
    let list = list.trim();
    let mut items = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    let mut closed = false;
    for token in Lexer::new(list) {
        let (token, range) = token?;
        if closed {
            return Err("trailing text after a list".into());
        }
        match token {
            Token::Open => {
                if depth == 1 {
                    start = range.start;
                }
                depth += 1;
            }
            Token::Close => {
                depth = depth
                    .checked_sub(1)
                    .ok_or_else(|| "unbalanced `)`".to_string())?;
                match depth {
                    0 => closed = true,
                    1 => items.push(&list[start..range.end]),
                    _ => {}
                }
            }
            Token::Atom => match depth {
                0 => return Err("an atom, not a list".into()),
                1 => items.push(&list[range]),
                _ => {}
            },
        }
    }
    if !closed {
        return Err("not one balanced list".into());
    }
    Ok(items)
}

/// `term`'s tokens joined by single spaces: equal for two spellings of one
/// term that differ only in whitespace or comments.
fn normalized(term: &str) -> Result<String, String> {
    let mut out = String::with_capacity(term.len());
    for token in Lexer::new(term) {
        let (_, range) = token?;
        if !out.is_empty() {
            out.push(' ');
        }
        out.push_str(&term[range]);
    }
    Ok(out)
}

/// The arguments of `term` when it is an `(and ...)` application.
fn and_arguments(term: &str) -> Result<Option<Vec<&str>>, String> {
    if !term.trim_start().starts_with('(') {
        return Ok(None);
    }
    let items = list_items(term)?;
    Ok(match items.split_first() {
        Some((head, arguments)) if *head == "and" && !arguments.is_empty() => {
            Some(arguments.to_vec())
        }
        _ => None,
    })
}

/// The one conjunctive assertion of `original`, as written: the term of the
/// only `(assert (and ...))` command, which is exactly the shape
/// `split_assert_conjuncts` rewrites.
fn the_conjunction(original: &str) -> Result<&str, String> {
    let mut found = None;
    for command in top_level_commands(original)? {
        let items = list_items(command)?;
        let [head, term] = items.as_slice() else {
            continue;
        };
        if *head != "assert" || and_arguments(term)?.is_none() {
            continue;
        }
        if found.replace(*term).is_some() {
            return Err("more than one conjunctive assert".into());
        }
    }
    found.ok_or_else(|| "no conjunctive assert".into())
}

/// Rewrite `split_proof`, a proof AY emitted for `split_assert_conjuncts(original)`,
/// into a proof of `original`: assume the original conjunction, re-derive each
/// nested conjunction and each assumed conjunct with Alethe `and` steps, and
/// pass every other command through unchanged. The result has no authority of
/// its own; the independent checker decides it against `original`.
pub(crate) fn bridge_split_conjunct_proof(
    original: &str,
    split_proof: &str,
) -> Result<String, String> {
    let commands = top_level_commands(split_proof)?;
    let conjunction = the_conjunction(original)?;

    // Every argument of every conjunction node, keyed by its normalized text,
    // maps to the first (premise, index) that derives it. Nodes are numbered in
    // the order their deriving steps are written, so each premise precedes its
    // uses.
    let root = format!("{ID_PREFIX}0");
    let mut lines = vec![format!("(assume {root} {conjunction})")];
    let mut derives: HashMap<String, (String, usize)> = HashMap::new();
    let mut pending = vec![(root, conjunction)];
    let mut nodes = 1usize;
    while let Some((premise, term)) = pending.pop() {
        let arguments = and_arguments(term)?.ok_or("a conjunction node is not an `and`")?;
        for (index, argument) in arguments.into_iter().enumerate() {
            derives
                .entry(normalized(argument)?)
                .or_insert_with(|| (premise.clone(), index));
            if and_arguments(argument)?.is_some() {
                if nodes == MAX_AND_NODES {
                    return Err(format!("more than {MAX_AND_NODES} conjunction nodes"));
                }
                let node = format!("{ID_PREFIX}{nodes}");
                nodes += 1;
                lines.push(format!(
                    "(step {node} (cl {argument}) :rule and :premises ({premise}) :args ({index}))"
                ));
                pending.push((node, argument));
            }
        }
    }

    let mut anchors: Vec<&str> = Vec::new();
    for command in commands {
        let items = list_items(command)?;
        let head = items.first().copied().unwrap_or("");
        let id = match head {
            "anchor" => items
                .iter()
                .position(|item| *item == ":step")
                .and_then(|at| items.get(at + 1).copied()),
            "assume" | "step" => items.get(1).copied(),
            _ => None,
        };
        if id.is_some_and(|id| id.starts_with(ID_PREFIX)) {
            return Err(format!(
                "the proof already uses the identifier prefix {ID_PREFIX}"
            ));
        }
        match (head, id) {
            ("anchor", Some(id)) => {
                anchors.push(id);
                lines.push(command.to_string());
            }
            ("anchor", None) => return Err("an anchor without `:step`".into()),
            ("step", Some(id)) => {
                if anchors.last() == Some(&id) {
                    anchors.pop();
                }
                lines.push(command.to_string());
            }
            // A subproof's local assumption is discharged inside it.
            ("assume", Some(_)) if !anchors.is_empty() => lines.push(command.to_string()),
            ("assume", Some(id)) => {
                let [_, _, term] = items.as_slice() else {
                    return Err(format!("assumption {id} is not `(assume id term)`"));
                };
                let (premise, index) = derives.get(&normalized(term)?).ok_or_else(|| {
                    format!("assumption {id} is not an argument of the original conjunction")
                })?;
                lines.push(format!(
                    "(step {id} (cl {term}) :rule and :premises ({premise}) :args ({index}))"
                ));
            }
            _ => lines.push(command.to_string()),
        }
    }
    if !anchors.is_empty() {
        return Err("an unclosed anchor".into());
    }
    let mut proof = lines.join("\n");
    proof.push('\n');
    Ok(proof)
}

#[cfg(test)]
#[path = "split_conjunct_proof_tests.rs"]
pub(crate) mod tests;
