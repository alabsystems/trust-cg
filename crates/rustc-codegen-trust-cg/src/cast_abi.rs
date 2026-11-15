// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Borrow the complete cast target and preserve its number of leading i32
//! arguments. Only the legacy boolean API limits that number to zero or one.

use rustc_target::callconv::{CastTarget, PassMode};

#[derive(Clone, Copy, Debug)]
pub(super) struct Cast<'a> {
    pub(super) target: &'a CastTarget,
    pub(super) padding_words: u8,
}

impl Cast<'_> {
    pub(super) fn has_padding(self) -> bool {
        self.padding_words != 0
    }

    /// The bridge does not emit leading dummy arguments. Preserve the original
    /// one-word refusal and state the full count for the modern larger cases.
    pub(super) fn padding_refusal(self) -> Option<String> {
        match self.padding_words {
            0 => None,
            1 => Some("`PassMode::Cast` with a `pad_i32` padding register".to_owned()),
            count => Some(format!(
                "`PassMode::Cast` with {count} `pad_i32` padding registers"
            )),
        }
    }
}

pub(super) fn view(mode: &PassMode) -> Option<Cast<'_>> {
    match mode {
        #[cfg(rustc_cast_pad_count)]
        PassMode::Cast {
            cast,
            pad_i32_count,
        } => Some(Cast {
            target: cast.as_ref(),
            padding_words: *pad_i32_count,
        }),
        #[cfg(not(rustc_cast_pad_count))]
        PassMode::Cast { cast, pad_i32 } => Some(Cast {
            target: cast.as_ref(),
            padding_words: u8::from(*pad_i32),
        }),
        _ => None,
    }
}

/// Existing unit inputs use the legacy zero/one geometry. This constructor is
/// not a conversion from arbitrary modern counts or a production fallback.
#[cfg(test)]
pub(super) fn fixture(target: CastTarget, padded: bool) -> PassMode {
    #[cfg(rustc_cast_pad_count)]
    {
        PassMode::Cast {
            cast: Box::new(target),
            pad_i32_count: u8::from(padded),
        }
    }
    #[cfg(not(rustc_cast_pad_count))]
    {
        PassMode::Cast {
            cast: Box::new(target),
            pad_i32: padded,
        }
    }
}

#[cfg(test)]
pub(super) fn fixture_padding(mode: &mut PassMode, padded: bool) {
    match mode {
        #[cfg(rustc_cast_pad_count)]
        PassMode::Cast {
            cast: _,
            pad_i32_count,
        } => *pad_i32_count = u8::from(padded),
        #[cfg(not(rustc_cast_pad_count))]
        PassMode::Cast { cast: _, pad_i32 } => *pad_i32 = padded,
        _ => panic!("padding fixture requires a cast mode"),
    }
}
