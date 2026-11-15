#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn scalar_payload_guard(code: i32, present: bool, guard: bool) -> i32 {
    let value = if present { Some(code) } else { None };
    match value {
        Some(selected @ (3 | 7 | 11 | 19 | 23)) if guard => selected + 1000,
        Some(selected) => selected - 1000,
        None => -3000,
    }
}
