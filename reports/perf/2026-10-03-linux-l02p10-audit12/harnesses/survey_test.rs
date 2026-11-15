
    /// Survey (temporary, not committed): the thread-local template rule
    /// over the ELF images listed one per line in `$L02P10_SURVEY_LIST`, and,
    /// as a proxy, the read and execute rule with each image's allocated
    /// sections taken as trust-cg's (each needs `R`, and `E` when it is
    /// code, as `own_section_needs` reads an object), verdicts to
    /// `$L02P10_SURVEY_OUT`.
    #[test]
    #[ignore = "host survey"]
    fn survey_tls_template_and_permissions_over_host_images() {
        use std::io::Write as _;
        const SHF_EXECINSTR: u64 = 0x4;
        let list = std::fs::read_to_string(std::env::var("L02P10_SURVEY_LIST").unwrap()).unwrap();
        let mut out = std::fs::File::create(std::env::var("L02P10_SURVEY_OUT").unwrap()).unwrap();
        for path in list.lines().filter(|line| !line.is_empty()) {
            let Ok(bytes) = std::fs::read(path) else {
                writeln!(out, "IMAGE {path}\nUNREADABLE").unwrap();
                continue;
            };
            let image = ImageBytes::Whole(&bytes);
            let tls = tls_template_disagreement(image);
            let permissions = (|| -> Result<Option<String>, String> {
                let Some(headers) = elf_section_headers(image)? else {
                    return Ok(None);
                };
                let own: Vec<MapInputSection> = headers
                    .iter()
                    .filter(|section| section.flags & SHF_ALLOC != 0 && section.size != 0)
                    .map(|section| MapInputSection {
                        file: "image".to_string(),
                        section: section.name.clone(),
                        address: section.address,
                        size: section.size,
                    })
                    .collect();
                let needs = |input: &MapInputSection| {
                    headers
                        .iter()
                        .filter(|section| {
                            section.name == input.section && section.address == input.address
                        })
                        .fold(0, |needs, section| {
                            let readable = if section.kind == SHT_NOBITS
                                && section.flags & SHF_TLS != 0
                            {
                                0
                            } else {
                                SEGMENT_PF_R
                            };
                            let executable = if section.flags & SHF_EXECINSTR != 0 {
                                SEGMENT_PF_X
                            } else {
                                0
                            };
                            needs | readable | executable
                        })
                };
                segment_permission_disagreement(image, &own, &needs)
            })();
            let has_tls = elf_segments(image)
                .map(|segments| segments.iter().any(|segment| segment.kind == PT_TLS))
                .unwrap_or(false);
            writeln!(
                out,
                "IMAGE {path}\nHAS_TLS {has_tls}\nTLS {tls:?}\nPERM {permissions:?}"
            )
            .unwrap();
        }
    }
