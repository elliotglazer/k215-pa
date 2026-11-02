# tools/

`link/` is the separate-compilation link checker that checked the PA proofs of Theorems 2, 3 and G2
(receipts `receipt/thm23-g2/pa` (C-059) and `receipt/thm23-g2/pa-g2` (C-054)): each module is compiled with
`mm0-rs` against pruned interfaces of its imports, the binaries are linked by name, and `mm0-c` checks the
joined binary against the joined specification (plus an axiom check and a false-statement control). It is the
exact snapshot those runs used: `link/SNAPSHOT.sha256` (sha256 `c5595a8c...`, the value in the receipts) lists
every file. `link_job.py` is the host driver (sha256 `cc66dd87...`, also in the receipts). Usage and design:
`link/README.md`. Like the compiler, this tooling is untrusted: only `mm0-c` and the specification are.

`gen7/` is the reflection compiler ("gen7": MM0 proof over `peano.mm0` -> PA-internal derivation, plus the stub
linker) that produced and linked the generic-framework runs C-081 / C-084 / C-091 / C-092 (`generic/`): the exact
host snapshot, listed with every pinned file in `gen7/HOST-MANIFEST.sha256` (sha256 `3c00eca4...`, the
`gen7_manifest_sha256` in those runs' `status.json`); its `pa-mm0/` entries are the module versions of the snapshot
(in git or in the releases). `gen7_job.py` is the host driver (sha256 `c572bdff...`, `gen7_job_sha256` in the
receipts). Pipeline and usage: `generic/README.md` section 3. Untrusted, like `link/`.
