// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Execute the production identity/prototype helper against real compiler types.
// Stop after analysis: these are query checks, not CG memory-operation execution.
#![feature(rustc_private)]

extern crate rustc_abi;
#[cfg(rustc_attr_ir_lang_items)]
extern crate rustc_attr_ir;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

#[path = "../../../src/lang_items.rs"]
mod lang_items;
#[path = "../../../src/memory_runtime.rs"]
mod memory_runtime;

use memory_runtime::MemoryLibcall;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;

#[cfg(rustc_canonical_memory_symbols)]
static FAULT: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

/// Deliberately corrupt one entry at the compiler-query boundary. The other
/// entries are copied from actual local/dependency canonical metadata.
#[cfg(rustc_canonical_memory_symbols)]
fn faulty_symbols(tcx: TyCtxt<'_>, (): ()) -> rustc_attr_ir::CanonicalSymbols {
    use rustc_span::{Symbol, def_id::LOCAL_CRATE};
    use std::sync::atomic::Ordering;
    let fault = FAULT.load(Ordering::SeqCst);
    let _ = tcx.hir_crate_items(());
    let mut result = rustc_attr_ir::CanonicalSymbols::new();
    for cnum in tcx
        .crates(())
        .iter()
        .copied()
        .chain(std::iter::once(LOCAL_CRATE))
    {
        for entry in tcx.canonical_symbols(cnum).iter() {
            let mut did = entry.def_id;
            if entry.symbol == Symbol::intern("memcpy") {
                match fault {
                    1 => continue,
                    2 => {
                        did = tcx
                            .hir_crate_items(())
                            .foreign_items()
                            .map(|item| item.owner_id.to_def_id())
                            .find(|did| {
                                tcx.def_kind(*did) == DefKind::Fn
                                    && tcx.item_name(*did).as_str() == "valid_copy"
                            })
                            .expect("local foreign copy declaration");
                    }
                    3 => did = tcx.lang_items().sized_trait().expect("core trait"),
                    4 => {
                        did = tcx
                            .canonical_symbols(entry.def_id.krate)
                            .iter()
                            .find(|item| item.symbol == Symbol::intern("memset"))
                            .expect("actual core memset")
                            .def_id;
                    }
                    _ => panic!("unrecognized controlled query fault"),
                }
            }
            assert!(
                result.set(entry.symbol, did).is_none(),
                "controlled fault table retains unique symbols"
            );
        }
    }
    result
}

struct Audit {
    fault: u8,
}

impl Callbacks for Audit {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        #[cfg(rustc_canonical_memory_symbols)]
        if self.fault != 0 {
            FAULT.store(self.fault, std::sync::atomic::Ordering::SeqCst);
            config.override_queries = Some(|_, providers| {
                providers.queries.all_canonical_symbols = faulty_symbols;
            });
        }
        #[cfg(not(rustc_canonical_memory_symbols))]
        {
            let _ = config;
            assert_eq!(self.fault, 0, "canonical query faults need the actual API");
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let sized = tcx
            .lang_items()
            .get(lang_items::LangItem::Sized)
            .expect("genuine core Sized");
        assert_eq!(Some(sized), tcx.lang_items().sized_trait());
        let core = sized.krate;
        if self.fault != 0 {
            let why = MemoryLibcall::Copy
                .definition(tcx)
                .expect_err("corrupted compiler authority must refuse");
            let expected = match self.fault {
                1 => "missing genuine runtime canonical symbol memcpy",
                2 => "unsupported genuine MemCpy owner",
                3 => "unsupported genuine MemCpy foreign function",
                4 => "unsupported genuine MemCpy prototype",
                _ => panic!("unknown fault mode"),
            };
            assert!(why.starts_with("[TCG-MEM-LIBCALL-ABI]"));
            assert!(why.contains(expected), "wrong named refusal: {why}");
            println!("MEMORY_AUTHORITY_REFUSED fault={} reason={why}", self.fault);
            return Compilation::Stop;
        }
        for kind in MemoryLibcall::ALL {
            let did = kind.definition(tcx).expect("actual core memory authority");
            assert_eq!(did.krate, core);
            assert_eq!(tcx.def_kind(did), DefKind::Fn);
            assert!(tcx.is_foreign_item(did));
            println!(
                "MEMORY_AUTHORITY kind={kind:?} def={did:?} path={}",
                tcx.def_path_str(did)
            );
        }
        // These local declarations test only kind/prototype validation. They
        // deliberately supply no core-owner authority and cannot declare a callee.
        use MemoryLibcall::{Copy, Move, Set};
        let cases = [
            ("valid_copy", Copy, true),
            ("valid_move", Move, true),
            ("valid_set", Set, true),
            ("too_few", Copy, false),
            ("too_many", Copy, false),
            ("const_destination", Copy, false),
            ("scalar_destination", Copy, false),
            ("mutable_source", Copy, false),
            ("scalar_source", Copy, false),
            ("wide_fill", Set, false),
            ("unsigned_fill", Set, false),
            ("wrong_length", Copy, false),
            ("void_result", Copy, false),
            ("different_result", Copy, false),
            ("variadic_copy", Copy, false),
            ("unwinding_copy", Copy, false),
            ("defined_function", Copy, false),
            ("NotAFunction", Copy, false),
            ("NOT_A_FUNCTION", Copy, false),
        ];
        let defs: Vec<_> = tcx
            .iter_local_def_id()
            .map(|did| did.to_def_id())
            .filter(|did| {
                matches!(
                    tcx.def_kind(*did),
                    DefKind::Fn | DefKind::Struct | DefKind::Static { .. }
                )
            })
            .collect();
        let mut admitted = 0;
        let mut refused = 0;
        for (name, kind, expected) in cases {
            let ids: Vec<_> = defs
                .iter()
                .copied()
                .filter(|did| tcx.item_name(*did).as_str() == name)
                .collect();
            assert_eq!(ids.len(), 1, "one exact fixture declaration for {name}");
            let result = kind.validate_declaration(tcx, ids[0]);
            assert_eq!(
                result.is_ok(),
                expected,
                "prototype case {name}: {result:?}"
            );
            if let Err(why) = result {
                assert!(why.starts_with("[TCG-MEM-LIBCALL-ABI]"), "{name}: {why}");
                refused += 1;
            } else {
                admitted += 1;
            }
        }
        assert_eq!((admitted, refused), (3, 16));
        println!("MEMORY_PROTOTYPES cases=19 admitted=3 refused=16 authorities=3");
        Compilation::Stop
    }
}

fn main() {
    let mut args: Vec<_> = std::env::args().collect();
    let fault = if let Some(index) = args
        .iter()
        .position(|arg| arg.starts_with("--memory-query-fault="))
    {
        args.remove(index)
            .strip_prefix("--memory-query-fault=")
            .unwrap()
            .parse()
            .expect("numeric controlled fault")
    } else {
        0
    };
    rustc_driver::run_compiler(&args, &mut Audit { fault });
}
