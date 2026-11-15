#![no_std]
#[unsafe(no_mangle)]
pub fn maximal_suffix(arr: &[u8], order_greater: bool) -> (usize, usize) {
    let mut left = 0; // Corresponds to i in the paper
    let mut right = 1; // Corresponds to j in the paper
    let mut offset = 0; // Corresponds to k in the paper, but starting at 0
    // to match 0-based indexing.
    let mut period = 1; // Corresponds to p in the paper

    while let Some(&a) = arr.get(right + offset) {
        // `left` will be inbounds when `right` is.
        let b = arr[left + offset];
        if (a < b && !order_greater) || (a > b && order_greater) {
            // Suffix is smaller, period is entire prefix so far.
            right += offset + 1;
            offset = 0;
            period = right - left;
        } else if a == b {
            // Advance through repetition of the current period.
            if offset + 1 == period {
                right += offset + 1;
                offset = 0;
            } else {
                offset += 1;
            }
        } else {
            // Suffix is larger, start over from current location.
            left = right;
            right += 1;
            offset = 0;
            period = 1;
        }
    }
    (left, period)
}
