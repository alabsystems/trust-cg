
    /// Survey (temporary, not committed): run the `.eh_frame` check over the
    /// ELF images listed one per line in `$TCG_EH_SURVEY_LIST` and write, per
    /// image, its verdict and every FDE the section walk decodes to
    /// `$TCG_EH_SURVEY_OUT` for comparison with `readelf --debug-dump=frames`.
    #[test]
    #[ignore = "host survey"]
    fn survey_eh_frame_check_over_host_images() {
        use std::io::Write as _;
        let list = std::fs::read_to_string(std::env::var("TCG_EH_SURVEY_LIST").unwrap()).unwrap();
        let mut out = std::fs::File::create(std::env::var("TCG_EH_SURVEY_OUT").unwrap()).unwrap();
        for path in list.lines().filter(|line| !line.is_empty()) {
            let Ok(bytes) = std::fs::read(path) else {
                writeln!(out, "IMAGE {path}\nSKIP unreadable").unwrap();
                continue;
            };
            let check = eh_frame_check(&bytes);
            let request = LinkRequest::executable(linux(), vec![], PathBuf::from(path));
            let diagnostics = eh_frame_diagnostics(&request, &Ok(bytes.clone()));
            writeln!(
                out,
                "IMAGE {path}\nVERDICT fdes={} outside_code={} outside_memory={} table={} unproven={}",
                check.fdes,
                check.outside_code.len(),
                check.outside_memory.len(),
                check.table.as_ref().map_or("none".to_string(), |t| format!("{}:{}", t.count, t.problems.len())),
                check.unproven.clone().unwrap_or_default()
            )
            .unwrap();
            for diagnostic in &diagnostics {
                writeln!(out, "DIAG {}", diagnostic.line).unwrap();
            }
            // Independent listing of the section walk's FDEs.
            let (Ok(Some(headers)), Ok(kind)) = (elf_section_headers(&bytes), elf_linked_kind(&bytes))
            else {
                continue;
            };
            let bases = EhBases {
                datarel: None,
                absolute: kind == ElfLinkedKind::Executable,
            };
            for section in headers
                .iter()
                .filter(|s| s.name == ".eh_frame" && s.flags & SHF_ALLOC != 0 && s.kind != 8)
            {
                let memory = EhMemory::section(&bytes, section);
                let end = section.address + section.size;
                let mut at = section.address;
                let mut cies = std::collections::HashMap::new();
                while at + 4 <= end {
                    let Ok(record) = eh_record(&memory, at) else {
                        writeln!(out, "WALKERR {at:#x}").unwrap();
                        break;
                    };
                    let Some((cursor, id)) = record else {
                        at += 4;
                        continue;
                    };
                    let next = cursor.end;
                    if id != 0 {
                        let cie_at = (at + 4).wrapping_sub(u64::from(id));
                        if !cies.contains_key(&cie_at) {
                            match eh_cie(&memory, cie_at, bases) {
                                Ok(cie) => {
                                    cies.insert(cie_at, cie);
                                }
                                Err(why) => {
                                    writeln!(out, "WALKERR {why}").unwrap();
                                    break;
                                }
                            }
                        }
                        match eh_fde(at, cursor, &cies[&cie_at], bases) {
                            Ok(fde) => writeln!(
                                out,
                                "FDE {:x} {:x} {:x}",
                                fde.address - section.address,
                                fde.pc_begin.resolved,
                                fde.pc_begin.resolved.wrapping_add(fde.range)
                            )
                            .unwrap(),
                            Err(why) => {
                                writeln!(out, "WALKERR {why}").unwrap();
                                break;
                            }
                        }
                    }
                    at = next;
                }
            }
        }
    }
}
