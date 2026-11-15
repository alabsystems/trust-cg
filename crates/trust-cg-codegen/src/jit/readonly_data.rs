// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Physical input custody for a future checked pointer entry. This owner grants
//! no executable permission, Core claim, machine summary, or callable entry.
//! In particular, numeric logical addresses cannot manufacture this borrow.

use super::entry_stack::{EntryStackError, OwnedEntryStack};

/// A live, initialized, aligned eight-byte row borrowed immutably from Rust.
///
/// The reference, rather than an address/digest, retains the allocation's
/// lifetime and excludes safe mutation for the duration of this borrow. Unsafe
/// foreign mutation remains part of the host language's ordinary obligations.
/// This is not evidence of a particular source value or logical memory model.
#[derive(Debug)]
pub struct ReadonlyEightBorrow<'a> {
    word: &'a u64,
}

/// A physical row did not match the requested logical input or stack extent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum ReadonlyEightBorrowError {
    #[error("readonly row address differs from the checked logical input")]
    Address,
    #[error("readonly row word differs from the checked logical input")]
    Word,
    #[error("readonly row extent is not representable")]
    Extent,
    #[error("readonly row overlaps the owned stack mapping")]
    StackOverlap,
}

impl<'a> ReadonlyEightBorrow<'a> {
    /// Borrow exactly one actual initialized word. No raw-pointer constructor
    /// or caller-supplied permission flag is provided.
    pub fn new(word: &'a u64) -> Self {
        Self { word }
    }

    /// Logical address observation only; it is not a callable pointer export.
    pub fn address(&self) -> Result<u64, ReadonlyEightBorrowError> {
        u64::try_from(std::ptr::from_ref(self.word).addr())
            .map_err(|_| ReadonlyEightBorrowError::Extent)
    }

    /// Actual loaded host word, retained by the same immutable borrow.
    pub fn word(&self) -> u64 {
        *self.word
    }

    /// Bind both coordinates to a separately checked logical read. Matching
    /// coordinates does not itself admit that logical read or a native call.
    pub fn check_input(&self, address: u64, word: u64) -> Result<(), ReadonlyEightBorrowError> {
        if self.address()? != address {
            return Err(ReadonlyEightBorrowError::Address);
        }
        if self.word() != word {
            return Err(ReadonlyEightBorrowError::Word);
        }
        Ok(())
    }

    /// Check disjointness from the entire actual mapping, including adapter
    /// header/page surplus. This observation does not loan or publish the stack.
    pub fn check_stack(&self, stack: &OwnedEntryStack) -> Result<(), EntryStackError> {
        stack.check_readonly_eight(self)
    }

    pub(super) fn extent(&self) -> Result<(usize, usize), ReadonlyEightBorrowError> {
        let start = std::ptr::from_ref(self.word).addr();
        let end = start
            .checked_add(8)
            .ok_or(ReadonlyEightBorrowError::Extent)?;
        Ok((start, end))
    }
}

pub(super) fn check_disjoint(
    row: (usize, usize),
    stack: (usize, usize),
) -> Result<(), ReadonlyEightBorrowError> {
    if row.0 >= row.1 || stack.0 >= stack.1 {
        return Err(ReadonlyEightBorrowError::Extent);
    }
    if row.0 < stack.1 && stack.0 < row.1 {
        return Err(ReadonlyEightBorrowError::StackOverlap);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn readonly_eight_borrow_binds_actual_address_and_word() {
        let word = 0x0102_0304_0506_0708;
        let other = word;
        let borrow = ReadonlyEightBorrow::new(&word);
        let address = borrow.address().unwrap();
        assert_eq!(borrow.check_input(address, word), Ok(()));
        assert_eq!(borrow.word().to_le_bytes(), [8, 7, 6, 5, 4, 3, 2, 1]);
        assert_eq!(
            borrow.check_input(address, word ^ 1),
            Err(ReadonlyEightBorrowError::Word)
        );
        assert_eq!(
            borrow.check_input(ReadonlyEightBorrow::new(&other).address().unwrap(), word),
            Err(ReadonlyEightBorrowError::Address)
        );
        assert_eq!(borrow.extent().unwrap().1 - borrow.extent().unwrap().0, 8);
    }

    #[test]
    fn readonly_eight_disjointness_includes_header_and_partial_overlap() {
        assert_eq!(check_disjoint((8, 16), (16, 64)), Ok(()));
        assert_eq!(check_disjoint((64, 72), (16, 64)), Ok(()));
        for row in [(8, 17), (16, 24), (56, 64), (63, 71), (8, 72)] {
            assert_eq!(
                check_disjoint(row, (16, 64)),
                Err(ReadonlyEightBorrowError::StackOverlap)
            );
        }
        assert_eq!(
            check_disjoint((usize::MAX, usize::MAX), (16, 64)),
            Err(ReadonlyEightBorrowError::Extent)
        );
    }
}
