# Payload inventory

This record follows the durable evidence policy
(docs/linux-aarch64-completion.md).
A dated record keeps its Markdown narrative and its reproducer sources in
tree, and its payloads (logs, census outputs, objects, bridges) out of tree.
These payloads were never committed. They are held on the measuring host (the
x86_64 Mac of the README) under `~/tcg-scratch`, at the paths below, and are
bound here by size and SHA-256.

- **A directory's row** gives its total bytes over its top-level files and the
  SHA-256 of its manifest. The manifest has one line `<sha256>  <name>` per
  file, sorted by name.
- **Regenerating.** `lane/payloads_o2.py` regenerates the table.
- **The numbers.** The README states the numbers each payload carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
| `o2-design/README.md` (the O2 diagnosis and ranked route (first O2 measurement)) | 19840 | `6c82913826595b4fe9ce12f7fc364813201caac87c6378d04c4e3a3c6bdf8f57` |
| `s24a-design/README.md` (the slice 24a design (the merged-chain quotient)) | 66779 | `670a3fbef2b237560a22a00d3ee679fb499a3b88e777104813197bb26029b302` |
| `runs/chain-7ee0.log` (the bridge-and-census chain log for 7ee0def54) | 1419 | `a9994ec3c83e85a194c4b96cb1a4e0e9538bc7f941dcce4e5cf8ac6e4bf188dd` |
| `runs/o2-7ee0.dylib` (the bridge, 7ee0def54) | 145420144 | `6b7998ed025efde4fb8f2f27093ec5d827e60531670f7082040e720e6dc497e9` |
| `runs/knobs.dylib` (the bridge, 85d236b37 (the knob lane)) | 145425168 | `1d2d1941d9675b12fb69cacec9b60bd2ab2faf8db3c9ea601c8ee95848f5a78d` |
| `runs/gates-knobs.log` (the knob lane gates (lane/gates_knobs.sh)) | 803 | `d77cecc82e32f379b0cccf4bb85372ffac115e9baa76915beff267fc85501379` |
| `runs/tippy-knobs.log` (check_tippy.sh on this host (frontend unavailable)) | 2169 | `de55573cf11018bfdd6dbe831f1e9ad160a66464d9a18f02a00cec24c1c2fc73` |
| `runs/chain-attrib.log` (the attribution chain log) | 3611 | `e2c1f6aa083f152981be355a83a635cebbc4da964097d1905f29a00fa864074d` |
| `runs/chain-attrib2.log` (the second attribution chain log) | 2375 | `8ac6d38d9449ce5da1753e8bb2d07c3ba03ebd4efea445fd3925fc1a47b9b87f` |
| `runs/census-o0-7ee0.out` (census o0-7ee0: summary) | 1717 | `6fcc57543279fa29c73bafa2b3d68961cb942d786ebdfbfed2b49a13d995aebf` |
| `runs/census-o0-7ee0/failed_roots.jsonl` (census o0-7ee0: failed roots) | 18382 | `c955ebddbeb010528ad9348b830714f1a3a5fb37856b24bffb29cbd06e7e03bd` |
| `runs/census-o0-7ee0/stderr.log` (census o0-7ee0: body trace) | 1306738 | `894d648c3e98c21df9a6ce775077d2023920f9286ca06970cc2adf3621890434` |
| `runs/census-o0-7ee0/obj/` (census o0-7ee0: emitted objects) (3426 files) | 4682079 | `a194e6359bd623470f590fd77b47f1d3e6690ea04bcb91123b22627db1f0c334` (manifest) |
| `runs/census-o2-7ee0.out` (census o2-7ee0: summary) | 1718 | `262d73b433f94db6d591c03020be6332f8e7ee150864a2235cd401dc82ba0fcd` |
| `runs/census-o2-7ee0/failed_roots.jsonl` (census o2-7ee0: failed roots) | 726708 | `e95b7735e775ef38b20d339224d0a6b2d461b0d89c08b6a080eb4858d8d0ed61` |
| `runs/census-o2-7ee0/stderr.log` (census o2-7ee0: body trace) | 4468423 | `319592755b8b940f95c183fbfe3bab78bf8835777945d967ab5f4a5ae9391028` |
| `runs/census-o2-7ee0/obj/` (census o2-7ee0: emitted objects) (706 files) | 630542 | `3cff751cf0eaa99fb3313b8168477e70164f873a6c0beac4d5e3e90aafec0e26` (manifest) |
| `runs/census-o2k-plain.out` (census o2k-plain: summary) | 1728 | `51628b8e0df6d2eca28dc15c0a19ff6c503a08b5dd112debff96fe33f3b573b8` |
| `runs/census-o2k-plain/failed_roots.jsonl` (census o2k-plain: failed roots) | 726708 | `e95b7735e775ef38b20d339224d0a6b2d461b0d89c08b6a080eb4858d8d0ed61` |
| `runs/census-o2k-plain/stderr.log` (census o2k-plain: body trace) | 4468405 | `77cba7f6a21594f6d48293fd1dd0183d821766f8751bb8b9d5f5abf2729c5ac7` |
| `runs/census-o2k-plain/obj/` (census o2k-plain: emitted objects) (706 files) | 630542 | `3cff751cf0eaa99fb3313b8168477e70164f873a6c0beac4d5e3e90aafec0e26` (manifest) |
| `runs/census-o2k-nbm.out` (census o2k-nbm: summary) | 1756 | `91b15c3eaa82166e85ed2d2a527d4c9ba9ba65e7f8585a3a511e8455089a6f50` |
| `runs/census-o2k-nbm/failed_roots.jsonl` (census o2k-nbm: failed roots) | 476267 | `32ab5324b2f9ee5846084fa6146f658ebef94ec14eac170dda802472b40ef890` |
| `runs/census-o2k-nbm/stderr.log` (census o2k-nbm: body trace) | 3205172 | `5b1790a172a7643c17d1e0f3d3d6f622c646d9befaa7c8fafe0906c21945a27a` |
| `runs/census-o2k-nbm/obj/` (census o2k-nbm: emitted objects) (910 files) | 1073706 | `67aa74696501245fa98eeab09a32f144800b6d2e4c6f618fc852eea71921d296` (manifest) |
| `runs/census-o2k-nrot.out` (census o2k-nrot: summary) | 1761 | `f1a96f49823ecb9f79a2d9cc2fe13a641acd9b233a09cab0737970d3e31728a3` |
| `runs/census-o2k-nrot/failed_roots.jsonl` (census o2k-nrot: failed roots) | 726707 | `cd3269bfcf5fda212e42fe8828f7e9e63d8f709427b8a0d6039268c0d163f355` |
| `runs/census-o2k-nrot/stderr.log` (census o2k-nrot: body trace) | 4468565 | `6ed2613e405d64296a0ab0e29f978128c5998d75426792b1cf9c8d3360e07e2c` |
| `runs/census-o2k-nrot/obj/` (census o2k-nrot: emitted objects) (706 files) | 630542 | `3cff751cf0eaa99fb3313b8168477e70164f873a6c0beac4d5e3e90aafec0e26` (manifest) |
| `runs/census-o2k-nifc.out` (census o2k-nifc: summary) | 1795 | `3b860fab88340a68273cfbfb8c0da15bf911bd7b4116fa8f4e6cc2ed6c2847e3` |
| `runs/census-o2k-nifc/failed_roots.jsonl` (census o2k-nifc: failed roots) | 722915 | `afb92208ac03b6a77df5e73c6c750c17fedba07665460a1a273b0a5f925838ba` |
| `runs/census-o2k-nifc/stderr.log` (census o2k-nifc: body trace) | 4451100 | `7d15798ecf48a04bb20bc1b996010fdefe59b29524c52a622b28a0109b02ae3c` |
| `runs/census-o2k-nifc/obj/` (census o2k-nifc: emitted objects) (709 files) | 632183 | `9424f8878a7e5773d54af7f4179cda1c09e8aeab5f6a818f648ce1bbee4f6118` (manifest) |
| `runs/census-o2k-nall.out` (census o2k-nall: summary) | 1974 | `3c8fd8789a795188280630b67741ba11634d3afd0652ed01062c124d5d1e2671` |
| `runs/census-o2k-nall/failed_roots.jsonl` (census o2k-nall: failed roots) | 426210 | `c3e0906cf3ec5a81233dfcd8c821c33f6103def007f0d8ebdb8e0d55382f1c7d` |
| `runs/census-o2k-nall/stderr.log` (census o2k-nall: body trace) | 2925678 | `77a490771f80b9afe108fa9bf76c410f696f8766eb36c4553e6b244bfb80b3ea` |
| `runs/census-o2k-nall/obj/` (census o2k-nall: emitted objects) (954 files) | 1186986 | `36d9c8b155831c4c777908b5da50aacf49e71390db545afb5ae55bf0d33fe687` (manifest) |
| `runs/census-o2k-b0.out` (census o2k-b0: summary) | 1743 | `7349ef1f14eb9d9710225cb96ffe313fa3188be398d9c79079afc75a512e4208` |
| `runs/census-o2k-b0/failed_roots.jsonl` (census o2k-b0: failed roots) | 39110 | `b1a5f6b44b10986f7bf3cf09546b3043575679c66618f719630fc66817ff41be` |
| `runs/census-o2k-b0/stderr.log` (census o2k-b0: body trace) | 724609 | `89defe7afc563b51ce7fe143644697f439ff44b327a28c472fbb1034e6a7c3c6` |
| `runs/census-o2k-b0/obj/` (census o2k-b0: emitted objects) (1254 files) | 2175809 | `6da46c624584252ea9226d2598eb31ce5427ccf26439658465fc91a5340f388c` (manifest) |
| `runs/census-o2k-b1.out` (census o2k-b1: summary) | 1744 | `37c7110c78099d37b84f5ec8d7825d365c3729f2bc663641ac30adf518bcc02c` |
| `runs/census-o2k-b1/failed_roots.jsonl` (census o2k-b1: failed roots) | 488598 | `3a6ec8114028dbeb3cdd9d3d72d07a52d562488e44220a2c03d05e880f1a0266` |
| `runs/census-o2k-b1/stderr.log` (census o2k-b1: body trace) | 3307225 | `a8aded77d2a394f01d40e5bef473a3238626939490416aca13e70b981a688008` |
| `runs/census-o2k-b1/obj/` (census o2k-b1: emitted objects) (900 files) | 1026966 | `12d61d522e245147fbdcb7b8c6316a5b70ccd1586dc13ff53033bdb81db58c1d` (manifest) |
| `runs/census-o2k-nmax.out` (census o2k-nmax: summary) | 2247 | `bb451e0ea629e667298b023be4b83a6e36e8d5a100518358bd62268eb315b91f` |
| `runs/census-o2k-nmax/failed_roots.jsonl` (census o2k-nmax: failed roots) | 423765 | `5f4d0652add75f60e3a403d695cd8229e0e45c59e216db789ab213a377e80724` |
| `runs/census-o2k-nmax/stderr.log` (census o2k-nmax: body trace) | 2911840 | `1f04156e53367a5145be22b00f48d030ee671d93be430af7e2707b55ffa492ac` |
| `runs/census-o2k-nmax/obj/` (census o2k-nmax: emitted objects) (956 files) | 1193062 | `8ee0759b818db1694798c8f563562c7597abe144d64abee37a1ecb4155eef10a` (manifest) |
| `runs/cmp-o2-4d65-7ee0/` (census_compare.py output (cmp-o2-4d65-7ee0)) (4 files) | 921 | `1b4dd3621eae8e275daa39ef5221e8762833a941984731c4ee2e39c10b453d14` (manifest) |
| `runs/cmp-o2k-plain/` (census_compare.py output (cmp-o2k-plain)) (4 files) | 319 | `9620374d3b8b738cadb68b60340792c695c05e4adead1e16b744f7cec28197dc` (manifest) |
| `runs/cmp-o2k-nbm/` (census_compare.py output (cmp-o2k-nbm)) (4 files) | 23197 | `dbf87c6d02b425d572178c4ea83fe457cf3b87cda2361b655c57b4bcc8ed4b3b` (manifest) |
| `runs/cmp-o2k-nrot/` (census_compare.py output (cmp-o2k-nrot)) (4 files) | 319 | `9620374d3b8b738cadb68b60340792c695c05e4adead1e16b744f7cec28197dc` (manifest) |
| `runs/cmp-o2k-nifc/` (census_compare.py output (cmp-o2k-nifc)) (4 files) | 997 | `36e08f0399d24ff32cab7e003606b48fa45386d1e38b80e2b82e893b87a6b943` (manifest) |
| `runs/cmp-o2k-nall/` (census_compare.py output (cmp-o2k-nall)) (4 files) | 27038 | `13bf47546b2656c58807d3ceaa9919321ead802ad915148587b36dd4fb9df3a9` (manifest) |
| `runs/cmp-o2k-b0/` (census_compare.py output (cmp-o2k-b0)) (4 files) | 62588 | `e49d52eed5d731fcbac9eaa8cb8772f10a6245b28da05193703e8c6aab521b95` (manifest) |
| `runs/cmp-o2k-b1/` (census_compare.py output (cmp-o2k-b1)) (4 files) | 23676 | `c700bf8f1458255d578cd0e0fe9eff6d3a03b1d129070872ffa3747e3944d8db` (manifest) |
| `runs/cmp-o2k-nmax/` (census_compare.py output (cmp-o2k-nmax)) (4 files) | 27214 | `6f897c1e13d22d66d8fe8088c8ad79764bface47e22f3f6715a50b33af4f4176` (manifest) |
