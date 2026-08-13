// trust-cg-jit-matrix/src/dimacs.rs - DIMACS CNF parser producing BcpState input shape.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

#[derive(Debug, Clone)]
pub struct DimacsCnf {
    pub num_vars: usize,
    pub num_clauses_declared: usize,
    pub clauses: Vec<Vec<i32>>,
}

pub enum DimacsError {
    MissingHeader,
    MalformedHeader(String),
    DuplicateHeader,
    ClauseBeforeHeader,
    ClauseTerminatorMissing,
    InvalidLiteral(String),
    VariableOutOfRange { lit: i32, num_vars: usize },
    ZeroLiteral,
    IoError(io::Error),
}

impl fmt::Display for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DimacsError::MissingHeader => write!(f, "missing DIMACS `p cnf` header"),
            DimacsError::MalformedHeader(s) => write!(f, "malformed DIMACS header: {s}"),
            DimacsError::DuplicateHeader => write!(f, "duplicate DIMACS `p cnf` header"),
            DimacsError::ClauseBeforeHeader => {
                write!(f, "clause literal encountered before `p cnf` header")
            }
            DimacsError::ClauseTerminatorMissing => {
                write!(f, "final clause is missing the `0` terminator")
            }
            DimacsError::InvalidLiteral(s) => write!(f, "invalid literal token: {s}"),
            DimacsError::VariableOutOfRange { lit, num_vars } => write!(
                f,
                "literal {lit} references a variable outside the declared range 1..={num_vars}"
            ),
            DimacsError::ZeroLiteral => write!(f, "zero literal encountered where unexpected"),
            DimacsError::IoError(e) => write!(f, "I/O error: {e}"),
        }
    }
}

impl fmt::Debug for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl std::error::Error for DimacsError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DimacsError::IoError(e) => Some(e),
            _ => None,
        }
    }
}

impl From<io::Error> for DimacsError {
    fn from(e: io::Error) -> Self {
        DimacsError::IoError(e)
    }
}

pub fn parse_dimacs_cnf(input: &str) -> Result<DimacsCnf, DimacsError> {
    let mut num_vars: Option<usize> = None;
    let mut num_clauses_declared: Option<usize> = None;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut current: Vec<i32> = Vec::new();
    let mut in_clause = false;

    'outer: for raw_line in input.lines() {
        let line = raw_line.trim_end_matches(['\r']).trim();

        if line.is_empty() {
            continue;
        }

        // `%` is a legacy SAT-Comp end-of-file sentinel; benchmarks from older
        // competitions often append `%\n0\n` after the last clause. Treat any
        // line beginning with `%` as end-of-input.
        if line.starts_with('%') {
            break;
        }

        let first_char = line.as_bytes()[0];

        if first_char == b'c' {
            continue;
        }

        if first_char == b'p' {
            if num_vars.is_some() {
                return Err(DimacsError::DuplicateHeader);
            }
            let mut parts = line.split_ascii_whitespace();
            let p = parts.next().unwrap_or("");
            if p != "p" {
                return Err(DimacsError::MalformedHeader(line.to_string()));
            }
            let fmt_tag = parts
                .next()
                .ok_or_else(|| DimacsError::MalformedHeader(line.to_string()))?;
            if fmt_tag != "cnf" {
                return Err(DimacsError::MalformedHeader(line.to_string()));
            }
            let nv_tok = parts
                .next()
                .ok_or_else(|| DimacsError::MalformedHeader(line.to_string()))?;
            let nc_tok = parts
                .next()
                .ok_or_else(|| DimacsError::MalformedHeader(line.to_string()))?;
            if parts.next().is_some() {
                return Err(DimacsError::MalformedHeader(line.to_string()));
            }
            let nv: usize = nv_tok
                .parse()
                .map_err(|_| DimacsError::MalformedHeader(line.to_string()))?;
            let nc: usize = nc_tok
                .parse()
                .map_err(|_| DimacsError::MalformedHeader(line.to_string()))?;
            num_vars = Some(nv);
            num_clauses_declared = Some(nc);
            continue;
        }

        let nv = match num_vars {
            Some(nv) => nv,
            None => return Err(DimacsError::ClauseBeforeHeader),
        };

        for tok in line.split_ascii_whitespace() {
            if tok.starts_with('%') {
                break 'outer;
            }
            let lit: i32 = tok
                .parse()
                .map_err(|_| DimacsError::InvalidLiteral(tok.to_string()))?;
            if lit == 0 {
                clauses.push(std::mem::take(&mut current));
                in_clause = false;
            } else {
                let var = lit.unsigned_abs() as usize;
                if var > nv {
                    return Err(DimacsError::VariableOutOfRange { lit, num_vars: nv });
                }
                current.push(lit);
                in_clause = true;
            }
        }
    }

    if num_vars.is_none() {
        return Err(DimacsError::MissingHeader);
    }

    if in_clause {
        return Err(DimacsError::ClauseTerminatorMissing);
    }

    Ok(DimacsCnf {
        num_vars: num_vars.unwrap_or(0),
        num_clauses_declared: num_clauses_declared.unwrap_or(0),
        clauses,
    })
}

pub fn read_dimacs_cnf_file(path: &Path) -> Result<DimacsCnf, DimacsError> {
    let text = fs::read_to_string(path)?;
    parse_dimacs_cnf(&text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bcp_baseline::BcpState;

    #[test]
    fn minimal_three_var_two_clause() {
        let input = "p cnf 3 2\n1 -3 0\n2 3 0\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.num_vars, 3);
        assert_eq!(cnf.num_clauses_declared, 2);
        assert_eq!(cnf.clauses, vec![vec![1, -3], vec![2, 3]]);
    }

    #[test]
    fn comments_and_blank_lines() {
        let input = "c header comment\n\nc another\np cnf 2 1\nc inline comment\n\n1 -2 0\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.num_vars, 2);
        assert_eq!(cnf.clauses, vec![vec![1, -2]]);
    }

    #[test]
    fn clauses_spanning_multiple_lines() {
        let input = "p cnf 4 2\n1 -2\n3 0\n-1\n2 -4 0\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.clauses, vec![vec![1, -2, 3], vec![-1, 2, -4]]);
    }

    #[test]
    fn windows_line_endings() {
        let input = "c hi\r\np cnf 3 2\r\n1 -3 0\r\n2 3 0\r\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.num_vars, 3);
        assert_eq!(cnf.clauses, vec![vec![1, -3], vec![2, 3]]);
    }

    #[test]
    fn percent_eof_marker_terminates_input() {
        let input = "p cnf 3 2\n1 -3 0\n2 3 0\n%\n0\ngarbage 99 -99 0\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.clauses, vec![vec![1, -3], vec![2, 3]]);
    }

    #[test]
    fn percent_inline_terminates_input() {
        let input = "p cnf 2 1\n1 -2 0\n2 -1 0 % trailing\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.clauses, vec![vec![1, -2], vec![2, -1]]);
    }

    #[test]
    fn missing_header_is_rejected() {
        let input = "1 -2 0\n";
        match parse_dimacs_cnf(input) {
            Err(DimacsError::ClauseBeforeHeader) => {}
            other => panic!("expected ClauseBeforeHeader, got {other:?}"),
        }
    }

    #[test]
    fn comments_only_then_missing_header() {
        let input = "c only a comment\nc and another\n";
        match parse_dimacs_cnf(input) {
            Err(DimacsError::MissingHeader) => {}
            other => panic!("expected MissingHeader, got {other:?}"),
        }
    }

    #[test]
    fn variable_out_of_range_is_rejected() {
        let input = "p cnf 3 1\n1 -4 0\n";
        match parse_dimacs_cnf(input) {
            Err(DimacsError::VariableOutOfRange { lit, num_vars }) => {
                assert_eq!(lit, -4);
                assert_eq!(num_vars, 3);
            }
            other => panic!("expected VariableOutOfRange, got {other:?}"),
        }
    }

    #[test]
    fn missing_terminator_is_rejected() {
        let input = "p cnf 3 1\n1 -2 3\n";
        match parse_dimacs_cnf(input) {
            Err(DimacsError::ClauseTerminatorMissing) => {}
            other => panic!("expected ClauseTerminatorMissing, got {other:?}"),
        }
    }

    #[test]
    fn invalid_literal_token_is_rejected() {
        let input = "p cnf 3 1\n1 foo -2 0\n";
        match parse_dimacs_cnf(input) {
            Err(DimacsError::InvalidLiteral(tok)) => assert_eq!(tok, "foo"),
            other => panic!("expected InvalidLiteral, got {other:?}"),
        }
    }

    #[test]
    fn duplicate_header_is_rejected() {
        let input = "p cnf 3 1\np cnf 3 1\n1 0\n";
        match parse_dimacs_cnf(input) {
            Err(DimacsError::DuplicateHeader) => {}
            other => panic!("expected DuplicateHeader, got {other:?}"),
        }
    }

    #[test]
    fn malformed_header_wrong_format_tag() {
        let input = "p sat 3 1\n1 0\n";
        match parse_dimacs_cnf(input) {
            Err(DimacsError::MalformedHeader(_)) => {}
            other => panic!("expected MalformedHeader, got {other:?}"),
        }
    }

    #[test]
    fn round_trip_into_bcp_state() {
        let input = "p cnf 3 3\n1 2 3 0\n-1 0\n-2 0\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        let mut state = BcpState::new(cnf.num_vars, cnf.clauses);
        let _ = state.propagate();
    }

    #[test]
    fn five_var_eight_clause_unsat_cascades_to_conflict() {
        let input = "\
c small UNSAT formula
c (x1 v x2) ^ (x2 v x3) ^ (-x1 v x3) ^ (-x3) ^ (x4 v x5) ^ (-x4 v -x5) ^ (x4) ^ (x5)
p cnf 5 8
1 2 0
2 3 0
-1 3 0
-3 0
4 5 0
-4 -5 0
4 0
5 0
";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.num_vars, 5);
        assert_eq!(cnf.num_clauses_declared, 8);
        assert_eq!(cnf.clauses.len(), 8);
        let mut state = BcpState::new(cnf.num_vars, cnf.clauses);
        let conflict = state.propagate();
        assert!(
            conflict.is_some(),
            "expected unit-clause cascade to derive a conflict"
        );
    }

    #[test]
    fn file_round_trip_via_tempfile() {
        let input = "p cnf 2 2\n1 -2 0\n-1 2 0\n";
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("formula.cnf");
        std::fs::write(&path, input).expect("write");
        let cnf = read_dimacs_cnf_file(&path).expect("read");
        assert_eq!(cnf.num_vars, 2);
        assert_eq!(cnf.clauses, vec![vec![1, -2], vec![-1, 2]]);
    }

    #[test]
    fn tabs_as_separators() {
        let input = "p cnf 3 1\n1\t-2\t3\t0\n";
        let cnf = parse_dimacs_cnf(input).expect("parse");
        assert_eq!(cnf.clauses, vec![vec![1, -2, 3]]);
    }
}
