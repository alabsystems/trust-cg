#![no_std]
use core::fmt;
#[derive(Clone, Copy)]
pub enum Error {
    InteriorNul { position: usize },
    NotNulTerminated,
}
#[unsafe(no_mangle)]
pub fn format_error_reference(value: &Error, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match value {
        Error::InteriorNul { position } => write!(
            f,
            "data provided contains an interior nul byte at byte position {position}"
        ),
        Error::NotNulTerminated => write!(f, "data provided is not nul terminated"),
    }
}
