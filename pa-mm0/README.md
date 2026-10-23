# pa-mm0: the theorem-1 sources

Every `.mm0` / `.mm1` file of the import closure of `k215_final_thm1`, at exactly the SHA-256 hashes listed under
`"sources"` in [`../receipt/thm1/report.json`](../receipt/thm1/report.json). A few large generated `.mm1` proof files
are not stored in git; [`../scripts/fetch_large_inputs.sh`](../scripts/fetch_large_inputs.sh) downloads them from the
release `thm1-inputs-v1`.

- [`targets/final.mm0`](targets/final.mm0): the frozen statement. Theorem 1 is
  `K215_halts_iff_ZFC_inconsistent: $ k215LiteralHalts <-> zfcInconsistent $`.
- [`k215_final_thm1.mm0`](k215_final_thm1.mm0): the module that was checked. It states
  `K215_halts_iff_ZFC_inconsistent_final` with exactly theorem 1's binders and statement.
- `*.mm0`: specification (definitions and theorem statements). This is what a reader audits; the closure of
  `targets/final.mm0` is listed in [`../manifests/final-spec-closure.sha256`](../manifests/final-spec-closure.sha256).
- `*.mm1`: proofs. They are compiled by `mm0-rs` and verified by `mm0-c` against the `.mm0` spec, so they need not be
  trusted.
- [`check.py`](check.py): the pinned driver that closes the import graph, compiles, joins the spec, runs `mm0-c`, and
  runs the false-conclusion control. It refuses any project file containing `axiom`.

Comments inside the sources are development notes; they are part of the hashed files and were left unchanged.
