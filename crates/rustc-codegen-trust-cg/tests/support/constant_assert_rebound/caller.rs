extern crate assert_rebound_callee as callee;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 3);
    let case = args[1].clone();
    let index = core::hint::black_box(args[2].parse::<usize>().unwrap());
    let hook_case = case.clone();
    std::panic::set_hook(Box::new(move |info| {
        let message = if let Some(s) = info.payload().downcast_ref::<String>() {
            s.as_str()
        } else if let Some(s) = info.payload().downcast_ref::<&str>() {
            s
        } else {
            std::process::exit(75);
        };
        if message != "index out of bounds: the len is 2 but the index is 2" {
            std::process::exit(75);
        }
        println!("ASSERT_REBOUND|case={hook_case}|hook=1|kind=bounds|len=2|index=2");
        std::process::exit(73);
    }));
    let value = match case.as_str() {
        "rebound-safe" | "rebound-panic" => callee::rebinding_bounds(index),
        "dynamic-panic" => callee::dynamic_bounds(index),
        "local-constant" => callee::immutable_local_constant(),
        _ => std::process::exit(76),
    };
    match (case.as_str(), value) {
        ("rebound-safe", 11) | ("local-constant", 18) => {
            println!("ASSERT_REBOUND|case={case}|value={value}|hook=0");
        }
        _ => std::process::exit(74),
    }
}
