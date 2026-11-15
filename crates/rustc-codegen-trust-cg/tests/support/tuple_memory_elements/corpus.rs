#![no_std]
#[inline(never)]
fn map_fold<T, B, Acc, R, Map, Fold>(mut map: Map, mut fold: Fold) -> impl FnMut(Acc, T) -> R
where
    Map: FnMut(T) -> B,
    Fold: FnMut(Acc, B) -> R,
{
    move |acc, input| fold(acc, map(input))
}
#[inline(never)]
fn apply<F: FnMut(usize, char) -> usize>(mut f: F, c: char) -> usize {
    f(0, c)
}
#[inline(never)]
fn apply_unit<F: FnMut((), char) -> usize>(mut f: F, c: char) -> usize {
    f((), c)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn escape_chars(value: u32, mode: u32, out: *mut u32) -> usize {
    let Some(c) = char::from_u32(value) else {
        return 0;
    };
    if mode >= 3 {
        return match mode {
            3 => apply_unit(
                map_fold(char::escape_default, |(), e: core::char::EscapeDefault| {
                    let mut count = 0;
                    for x in e {
                        unsafe {
                            out.add(count).write(x as u32);
                        }
                        count += 1;
                    }
                    count
                }),
                c,
            ),
            4 => apply_unit(
                map_fold(char::escape_debug, |(), e: core::char::EscapeDebug| {
                    let mut count = 0;
                    for x in e {
                        unsafe {
                            out.add(count).write(x as u32);
                        }
                        count += 1;
                    }
                    count
                }),
                c,
            ),
            _ => apply_unit(
                map_fold(char::escape_unicode, |(), e: core::char::EscapeUnicode| {
                    let mut count = 0;
                    for x in e {
                        unsafe {
                            out.add(count).write(x as u32);
                        }
                        count += 1;
                    }
                    count
                }),
                c,
            ),
        };
    }
    match mode {
        0 => apply(
            map_fold(
                char::escape_default,
                |mut count, e: core::char::EscapeDefault| {
                    for x in e {
                        unsafe {
                            out.add(count).write(x as u32);
                        }
                        count += 1;
                    }
                    count
                },
            ),
            c,
        ),
        1 => apply(
            map_fold(
                char::escape_debug,
                |mut count, e: core::char::EscapeDebug| {
                    for x in e {
                        unsafe {
                            out.add(count).write(x as u32);
                        }
                        count += 1;
                    }
                    count
                },
            ),
            c,
        ),
        _ => apply(
            map_fold(
                char::escape_unicode,
                |mut count, e: core::char::EscapeUnicode| {
                    for x in e {
                        unsafe {
                            out.add(count).write(x as u32);
                        }
                        count += 1;
                    }
                    count
                },
            ),
            c,
        ),
    }
}
