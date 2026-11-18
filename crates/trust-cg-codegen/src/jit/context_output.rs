// Copyright 2026 Andrew Yates | Apache-2.0

//! Initialized, move-only storage for a checked context/output entry.
//!
//! These owners establish host allocation and Rust borrow facts only. They do
//! not identify a source pointee, discharge a compiler relation, authorize a
//! runtime provider, or expose an executable pointer. In particular, owning a
//! Rust `T` does not permit native code to read its padding or reinterpret its
//! representation as words. Only the separate word constructor records that
//! every byte belongs to initialized `u64` storage.

use super::entry_stack::EntryStackError;

/// A stable, initialized context allocation retained through an exclusive call.
/// There is no raw-pointer, deserialization or permission-flag constructor.
pub struct OwnedEntryContext<T: ?Sized> {
    value: Box<T>,
    #[cfg(any(feature = "source-defined-call", test))]
    initialized_words: Option<usize>,
}

impl<T> OwnedEntryContext<T> {
    /// Own a Rust context without making any claim about its native layout.
    /// A checked entry may pass this object opaquely; a separate typed provider
    /// contract is required before any native dereference of an arbitrary `T`.
    pub fn new(value: T) -> Result<Self, EntryStackError> {
        if std::mem::size_of::<T>() == 0 {
            return Err(EntryStackError::Extent);
        }
        Ok(Self {
            value: Box::new(value),
            #[cfg(any(feature = "source-defined-call", test))]
            initialized_words: None,
        })
    }
}

impl OwnedEntryContext<[u64]> {
    /// Move actual initialized words, preserving their values and exact extent.
    /// This does not choose the function's logical context or input memory.
    pub fn from_words(words: Vec<u64>) -> Result<Self, EntryStackError> {
        word_bytes(words.len())?;
        #[cfg(any(feature = "source-defined-call", test))]
        let count = words.len();
        Ok(Self {
            value: words.into_boxed_slice(),
            #[cfg(any(feature = "source-defined-call", test))]
            initialized_words: Some(count),
        })
    }
}

impl<T: ?Sized> OwnedEntryContext<T> {
    /// Inspect the retained Rust value, without exporting a native pointer.
    pub fn value(&self) -> &T {
        &self.value
    }

    /// Mutate the value under the owner's exclusive Rust borrow.
    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }

    #[cfg(any(feature = "source-defined-call", test))]
    pub(crate) fn extent(&self) -> Result<(usize, usize), EntryStackError> {
        let start = std::ptr::from_ref::<T>(&self.value).cast::<u8>().addr();
        let bytes = std::mem::size_of_val::<T>(&self.value);
        extent(start, bytes)
    }

    #[cfg(any(feature = "source-defined-call", test))]
    pub(crate) fn initialized_words(&self) -> Option<usize> {
        self.initialized_words
    }
}

/// Exclusive initialized output words. Native writes of admitted 64-bit bit
/// patterns preserve the Rust element representation. Capacity is never an
/// independent claim about a particular module's output layout or footprint.
pub struct OwnedEntryOutput {
    words: Box<[u64]>,
}

impl OwnedEntryOutput {
    /// Allocate actual zero-initialized output, refusing empty/overflowing sizes.
    pub fn allocate_words(count: usize) -> Result<Self, EntryStackError> {
        word_bytes(count)?;
        let mut words = Vec::new();
        words
            .try_reserve_exact(count)
            .map_err(|error| EntryStackError::Allocate(std::io::Error::other(error.to_string())))?;
        words.resize(count, 0);
        Ok(Self {
            words: words.into_boxed_slice(),
        })
    }

    /// Inspect initialized words after the exclusive native borrow has ended.
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    /// Initialize or update words without changing the allocation's extent.
    pub fn words_mut(&mut self) -> &mut [u64] {
        &mut self.words
    }

    #[cfg(any(feature = "source-defined-call", test))]
    pub(crate) fn extent(&self) -> Result<(usize, usize), EntryStackError> {
        extent(self.words.as_ptr().addr(), word_bytes(self.words.len())?)
    }
}

fn word_bytes(count: usize) -> Result<usize, EntryStackError> {
    count
        .checked_mul(std::mem::size_of::<u64>())
        .filter(|&bytes| bytes != 0)
        .ok_or(EntryStackError::Extent)
}

#[cfg(any(feature = "source-defined-call", test))]
fn extent(start: usize, bytes: usize) -> Result<(usize, usize), EntryStackError> {
    let end = start
        .checked_add(bytes)
        .filter(|&end| start != 0 && start < end)
        .ok_or(EntryStackError::Extent)?;
    Ok((start, end))
}

/// Check complete half-open extents, including containment and partial overlap.
/// Private arithmetic only: this cannot manufacture an allocation or a borrow.
#[cfg(any(feature = "source-defined-call", test))]
pub(crate) fn disjoint(left: (usize, usize), right: (usize, usize)) -> Result<(), EntryStackError> {
    if left.0 >= left.1 || right.0 >= right.1 {
        return Err(EntryStackError::Extent);
    }
    if left.0 < right.1 && right.0 < left.1 {
        return Err(EntryStackError::AliasedStorage);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn real_context_and_output_preserve_initialization_and_distinct_allocations() {
        let context = OwnedEntryContext::from_words(vec![41, u64::MAX]).unwrap();
        let mut output = OwnedEntryOutput::allocate_words(5).unwrap();
        assert_eq!(context.value(), &[41, u64::MAX]);
        assert_eq!(context.initialized_words(), Some(2));
        assert_eq!(output.words(), &[0; 5]);
        output.words_mut()[4] = 42;
        assert_eq!(output.words(), &[0, 0, 0, 0, 42]);
        let input_extent = context.extent().unwrap();
        let output_extent = output.extent().unwrap();
        assert_eq!(input_extent.1 - input_extent.0, 16);
        assert_eq!(output_extent.1 - output_extent.0, 40);
        assert_eq!(input_extent.0 % std::mem::align_of::<u64>(), 0);
        assert_eq!(output_extent.0 % std::mem::align_of::<u64>(), 0);
        disjoint(input_extent, output_extent).unwrap();
    }

    #[test]
    fn arbitrary_rust_context_never_claims_word_initialization_or_layout() {
        #[repr(C)]
        struct Context {
            small: u8,
            wide: u64,
        }
        let mut context = OwnedEntryContext::new(Context { small: 7, wide: 42 }).unwrap();
        assert_eq!(context.initialized_words(), None);
        context.value_mut().small = 8;
        assert_eq!(context.value().wide, 42);
        let actual = context.extent().unwrap();
        assert_eq!(actual.1 - actual.0, std::mem::size_of::<Context>());
    }

    #[test]
    fn empty_overflowing_or_overlapping_storage_is_refused() {
        assert!(OwnedEntryContext::new(()).is_err());
        assert!(OwnedEntryContext::from_words(vec![]).is_err());
        assert!(OwnedEntryOutput::allocate_words(0).is_err());
        assert!(OwnedEntryOutput::allocate_words(usize::MAX).is_err());
        assert!(extent(usize::MAX - 1, 8).is_err());
        for overlapping in [(8, 17), (16, 24), (63, 71), (8, 72)] {
            assert!(matches!(
                disjoint(overlapping, (16, 64)),
                Err(EntryStackError::AliasedStorage)
            ));
        }
        disjoint((8, 16), (16, 64)).unwrap();
        disjoint((64, 72), (16, 64)).unwrap();
    }
}
