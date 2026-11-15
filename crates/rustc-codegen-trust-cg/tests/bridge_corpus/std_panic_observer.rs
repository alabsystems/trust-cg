// CORPUS FIXTURE (library) — the panic OBSERVER the std-panic differential
// links into both lanes' binaries. It is compiled once per panic strategy by
// the LLVM backend, so the hook that reads the payload is the same code under
// both backends: what differs between the lanes is only the panic the program
// raised. It prints the payload's TYPE (`&str` for std's `&'static str`
// payload of a literal message, `String` for a formatted one) and TEXT, and
// the Location the hook receives.
use std::io::Write;

pub fn install() {
    std::panic::set_hook(Box::new(|info| {
        let payload = info.payload();
        let payload = if let Some(text) = payload.downcast_ref::<&str>() {
            format!("&str:{text:?}")
        } else if let Some(text) = payload.downcast_ref::<String>() {
            format!("String:{text:?}")
        } else {
            "other".to_owned()
        };
        let location = match info.location() {
            Some(l) => format!("{}:{}:{}", l.file(), l.line(), l.column()),
            None => "none".to_owned(),
        };
        let mut out = std::io::stdout().lock();
        let _ = writeln!(out, "hook {payload} @ {location}");
        let _ = out.flush();
    }));
}
