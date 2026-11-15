use std::fmt::{self, Write};
#[derive(Clone, Copy)]
pub enum Error {
    InteriorNul { position: usize },
    NotNulTerminated,
}
unsafe extern "Rust" {
    fn format_error_reference(value: &Error, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}
struct Shim<'a>(&'a Error);
impl fmt::Display for Shim<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe { format_error_reference(self.0, f) }
    }
}
struct Limited {
    limit: usize,
    s: String,
}
impl fmt::Write for Limited {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if self.s.len() + s.len() > self.limit {
            return Err(fmt::Error);
        }
        self.s.push_str(s);
        Ok(())
    }
}
fn main() {
    let mut checks = 0;
    for i in 0..256usize {
        for value in [
            Error::InteriorNul {
                position: i.wrapping_mul(137),
            },
            Error::NotNulTerminated,
        ] {
            let expected = match value {
                Error::InteriorNul { position } => format!(
                    "data provided contains an interior nul byte at byte position {position}"
                ),
                Error::NotNulTerminated => "data provided is not nul terminated".to_owned(),
            };
            assert_eq!(format!("{}", Shim(&value)), expected);
            checks += 1;
            for limit in [0, 1, 17, expected.len(), expected.len() + 1] {
                let mut w = Limited {
                    limit,
                    s: String::new(),
                };
                let result = write!(w, "{}", Shim(&value));
                assert_eq!(result.is_ok(), limit >= expected.len());
                if result.is_ok() {
                    assert_eq!(w.s, expected)
                }
                checks += 1;
            }
        }
    }
    println!("PASS format_error_reference checks={checks}");
}
