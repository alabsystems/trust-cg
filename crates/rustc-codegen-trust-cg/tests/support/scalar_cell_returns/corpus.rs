#![no_std]
use core::cell::Cell;

#[inline(never)]
fn inspect<T>(value: &T, present: bool) -> Option<&T> {
    if present { Some(value) } else { None }
}

// The immutable local is placed directly in MIR's return place before the
// shared borrow. A reference-bearing call result gives it a scalar cell.
macro_rules! returning {
    ($name:ident, $wrapper:ident, $ty:ty) => {
        #[repr(transparent)]
        pub struct $wrapper(pub $ty);
        #[unsafe(no_mangle)]
        pub fn $name(value: $ty, present: bool) -> $wrapper {
            let result = $wrapper(value);
            assert_eq!(inspect(&result, present).is_some(), present);
            result
        }
    };
}
returning!(cell_word, Word, u64);
returning!(cell_signed, Signed, i32);
returning!(cell_wide, Wide, u128);
returning!(cell_float32, Float32, f32);
returning!(cell_float64, Float64, f64);
returning!(cell_bool, Flag, bool);
returning!(cell_char, Character, char);
returning!(cell_pointer, Address, *mut u8);

#[repr(transparent)]
pub struct CellWord(pub Cell<u64>);
#[inline(never)]
fn mutate(value: &CellWord, delta: u64) -> &CellWord {
    value.0.set(value.0.get().wrapping_add(delta));
    value
}
#[unsafe(no_mangle)]
pub fn cell_mutated(value: u64, delta: u64, branch: bool) -> CellWord {
    let result = CellWord(Cell::new(value));
    let alias = if branch {
        mutate(&result, delta)
    } else {
        mutate(&result, delta.rotate_left(17))
    };
    let change = if branch { delta } else { delta.rotate_left(17) };
    assert_eq!(alias.0.get(), value.wrapping_add(change));
    result
}
