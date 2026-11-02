# manifests: hashes of the spec and of the release inputs

- [`final-spec-closure.sha256`](final-spec-closure.sha256): `sha256sum` format, one line per file of the `.mm0` import
  closure of `pa-mm0/targets/final.mm0` (the definitions behind the statement). `checker/r0_check.py` checks that the
  receipt used exactly these files.
- [`thm1-inputs.json`](thm1-inputs.json): the receipt sources that are not stored in git, as `name`, `sha256` and
  `bytes`, plus the release tag. They are published as assets of the release `thm1-inputs-v1`;
  `scripts/fetch_large_inputs.sh` checks every downloaded file against this list.
- [`thm23-g2-spec-closure.sha256`](thm23-g2-spec-closure.sha256): the same for Theorems 2, 3, G2 and the Pi2 forms:
  the `.mm0` import closures of `pa-mm0/targets/thm23.mm0`, `pa-mm0/targets/incompleteness.mm0`, `pa-mm0/b4_sigma.mm0`,
  `pa-mm0/b4b_bb.mm0` and `pa-mm0/b4g2_final.mm0`, plus the four files that state the proved forms. Every
  `pa-mm0/` entry outside `targets/` has the hash that `receipt/thm23-g2/pa/report.json` lists.
- [`thm23-g2-inputs.json`](thm23-g2-inputs.json): the sources of `receipt/thm23-g2/pa/report.json` that are not in the
  Theorem 1 publication (1,864 files), published as assets of the release `thm23-g2-inputs-v1`;
  `sh scripts/fetch_large_inputs.sh thm23-g2-inputs-v1` checks every downloaded file against this list.
