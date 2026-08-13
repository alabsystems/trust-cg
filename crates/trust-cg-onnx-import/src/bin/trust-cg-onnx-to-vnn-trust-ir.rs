// trust-cg-onnx-to-vnn-trust-ir
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
use std::process;

fn main() {
    let mut args = std::env::args_os().skip(1);
    let Some(input) = args.next() else {
        eprintln!("usage: trust-cg-onnx-to-vnn-trust-ir <model.onnx.json> [-o output.json]");
        process::exit(2);
    };

    let mut output = None;
    while let Some(arg) = args.next() {
        if arg == std::ffi::OsStr::new("-o") {
            output = args.next().map(PathBuf::from);
        } else {
            eprintln!("unexpected argument: {}", arg.to_string_lossy());
            process::exit(2);
        }
    }

    let input = PathBuf::from(input);
    let module = match trust_cg_onnx_import::import_path(&input) {
        Ok(module) => module,
        Err(trust_cg_onnx_import::Error::Unsupported(message)) => {
            eprintln!("unsupported: {message}");
            process::exit(3);
        }
        Err(err) => {
            eprintln!("error: {err}");
            process::exit(1);
        }
    };

    let json = match serde_json::to_string_pretty(&module) {
        Ok(json) => json,
        Err(err) => {
            eprintln!("error: failed to serialize VNN trust_ir: {err}");
            process::exit(1);
        }
    };

    if let Some(output) = output {
        if let Err(err) = std::fs::write(&output, format!("{json}\n")) {
            eprintln!("error: failed to write {}: {err}", output.display());
            process::exit(1);
        }
    } else {
        println!("{json}");
    }
}
