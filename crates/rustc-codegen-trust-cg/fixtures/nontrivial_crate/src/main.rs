struct Packed {
    left: u64,
    right: u64,
}

enum Choice {
    Packed(u64),
    Raw,
}

union ScalarSlot {
    bits: u64,
    alias: u64,
}

#[cfg(feature = "cargo-dependency-fixture")]
use rustc_codegen_trust_cg_fixture_dep::dependency_mix;

#[inline(never)]
fn pick<T: Copy>(left: T, right: T, choose_left: bool) -> T {
    if choose_left {
        left
    } else {
        right
    }
}

#[inline(never)]
fn borrow_identity<T>(value: &T) -> &T {
    value
}

#[inline(never)]
fn make_scalar_slot(bits: u64) -> ScalarSlot {
    ScalarSlot { bits }
}

#[inline(never)]
fn read_scalar_slot(slot: ScalarSlot) -> u64 {
    unsafe { slot.alias }
}

#[inline(never)]
fn adjust(total: u64, input: u64) -> u64 {
    let narrowed = (input as u8) as u64;
    let checked = total + narrowed;
    let packed = Packed {
        left: checked,
        right: narrowed,
    };
    let mut packed_copy = packed;
    packed_copy = Packed {
        left: packed_copy.right,
        right: packed_copy.left,
    };
    let pair = (packed_copy.left, packed_copy.right);
    let mut pair_copy = pair;
    pair_copy = (pair_copy.1, pair_copy.0);
    let mut cells = [pair_copy.0, pair_copy.1, total];
    let cells_copy = cells;
    cells = [cells_copy[2], cells_copy[1], cells_copy[0]];
    let mixed = cells[0] ^ cells[1] ^ cells[2];
    let inverted = !mixed;
    let scaled = (inverted & 15) ^ 7;
    let mut choice = Choice::Packed(scaled);
    choice = Choice::Packed(match choice {
        Choice::Packed(delta) => delta ^ 1,
        Choice::Raw => total,
    });
    let choice_copy = choice;
    let selected = match choice_copy {
        Choice::Packed(delta) => delta,
        Choice::Raw => total,
    };
    let selected_ref = &selected;
    let selected_identity_ref = borrow_identity(selected_ref);
    let selected_by_ref = *selected_identity_ref;
    let right_ref = &packed_copy.right;
    let right_by_ref = *right_ref;
    let mut mutable_mix = selected_by_ref ^ right_by_ref;
    let mutable_ref = &mut mutable_mix;
    *mutable_ref = (*mutable_ref ^ 2) & 7;
    let right_mut = &mut packed_copy.right;
    *right_mut = *right_mut ^ mutable_mix;
    let right_after_mut = packed_copy.right;
    let repeat_mask = (selected_by_ref ^ right_after_mut ^ mutable_mix) & 3;
    let repeated = [repeat_mask; 3];
    let repeated_mix = repeated[0] ^ repeated[1] ^ repeated[2];
    let cells_len = cells.len() as u64;
    let repeated_len = repeated.len() as u64;
    let length_mix = cells_len | repeated_len;
    let slot = make_scalar_slot(length_mix ^ repeated_mix);
    let union_mix = read_scalar_slot(slot) & 7;
    let float_seed = ((selected_by_ref ^ union_mix) & 7) as f64;
    let widened_u32 = 16_777_217u32 as f64;
    let widened_i32_seed = 16_777_217i32;
    let widened_i32 = (-widened_i32_seed) as f64;
    let widened_u8 = 100u8 as f32;
    let high_bit_u64 = pick(0x8000_0000_0000_0000u64, widened_u32 as u64, true);
    let all_bits_u64 = high_bit_u64 | 0x7fff_ffff_ffff_ffffu64;
    let high_const_mix =
        ((high_bit_u64 >> 63) & 1) ^ ((all_bits_u64 ^ 0xffff_ffff_ffff_ffffu64) & 1);
    let high_bit_f32 = high_bit_u64 as f32;
    let all_bits_f32 = all_bits_u64 as f32;
    let signed_i64_f32 = (widened_i32_seed as i64) as f32;
    let int_to_f32_width_bit = if (high_bit_f32 < all_bits_f32) == (signed_i64_f32 > 0.0f32) {
        1u64
    } else {
        0u64
    };
    let signed_width_bit = if (widened_i32 as i64) < 0 { 1u64 } else { 0u64 };
    let int_to_float_width_mix =
        ((widened_u32 as u64) & 7)
            ^ ((widened_u8 as u64) & 7)
            ^ signed_width_bit
            ^ high_const_mix
            ^ int_to_f32_width_bit;
    let float_narrow = float_seed as f32;
    let float_narrow_sum = float_narrow + 1.0f32;
    let f32_sub = float_narrow_sum - 0.25f32;
    let f32_product = f32_sub * 2.0f32;
    let f32_ratio = f32_product / 2.0f32;
    let f32_eq = f32_ratio == f32_sub;
    let f32_lt = f32_sub < float_narrow_sum;
    let f32_le = f32_sub <= f32_ratio;
    let f32_gt = float_narrow_sum > f32_sub;
    let f32_guard = f32_eq == (f32_lt == (f32_le == f32_gt));
    let float_sum = float_seed + 3.0f64;
    let float_product = float_sum * 2.0f64;
    let float_delta = float_product - float_seed;
    let float_ratio = float_delta / 2.0f64;
    let float_ordered = float_ratio >= 3.0f64;
    let float_ne = float_ratio != 0.0f64;
    let float_guard = (float_ordered == float_ne) == f32_guard;
    let float_mix =
        (f32_ratio as u64) ^ ((float_ratio as u64) & 7) ^ union_mix ^ int_to_float_width_mix;
    let signed_seed = 7i64;
    let negated = -signed_seed;
    let signed_roundtrip = (negated as f64) as i64;
    let signed_low = signed_roundtrip < 0;
    let low = !(selected_by_ref > 8) == float_guard;
    let generic_selected = pick(
        selected_by_ref ^ union_mix ^ float_mix,
        repeated_mix ^ length_mix,
        low,
    );
    #[cfg(feature = "cargo-dependency-fixture")]
    let dependency_selected = dependency_mix(generic_selected, total);
    #[cfg(not(feature = "cargo-dependency-fixture"))]
    let dependency_selected = generic_selected;
    if low == signed_low {
        total | (dependency_selected ^ repeated_mix ^ length_mix)
    } else {
        total ^ (dependency_selected | repeated_mix | length_mix)
    }
}

fn main() {
    let seed = 2u64;
    let first = 5u64;
    let second = 9u64;
    let subtotal = adjust(seed, first);
    let _answer = adjust(subtotal, second);
}
