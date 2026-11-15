extern crate cleanup_cell_transport_provider as provider;

struct ReferenceGuard<'a, 'b>(&'a &'b u64);
impl Drop for ReferenceGuard<'_, '_> {
    fn drop(&mut self) {
        provider::record_reference_drop(self.0);
    }
}

struct ScalarGuard<'a>(&'a u64);
impl Drop for ScalarGuard<'_> {
    fn drop(&mut self) {
        provider::record_value_drop(self.0);
    }
}

#[derive(Clone, Copy)]
struct Word(u64);

// MIR retains ownership cleanup for generic T even when this instance's Word
// is Copy. This tuple return uses memory-backed transport and is a positive
// neighbor of the local scalar-cell packing regression.
#[inline(never)]
fn generic_nested_tuple<T>(make: fn(u64) -> T, input: u64, do_panic: bool) -> (T, u64) {
    let value = make(input);
    (value, provider::tuple_tail(do_panic))
}

#[inline(never)]
fn make_word(input: u64) -> Word {
    Word(input)
}

#[inline(never)]
pub fn reference_copy<'a>(a: &'a u64, b: &'a u64, choose_b: bool, do_panic: bool) -> u64 {
    let mut current = if choose_b { b } else { a };
    provider::replace_reference(&mut current, b);
    let guard = ReferenceGuard(&current);
    let copied = current;
    provider::observe(copied);
    provider::may_unwind(do_panic);
    let result = *copied;
    drop(guard);
    result
}

#[inline(never)]
pub fn nested_scalar_tuple(input: u64, replacement: u64, do_panic: bool) -> u64 {
    let mut word = Word(input);
    provider::replace_value(&mut word.0, replacement);
    let guard = ScalarGuard(&word.0);
    // Observe the original aliased scalar independently of the tuple result.
    provider::observe(&word.0);
    let pair = generic_nested_tuple(make_word, word.0, do_panic);
    let result = pair.0.0 + pair.1;
    drop(guard);
    result
}
