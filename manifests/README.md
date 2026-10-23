# manifests: hashes of the spec and of the release inputs

- [`final-spec-closure.sha256`](final-spec-closure.sha256): `sha256sum` format, one line per file of the `.mm0` import
  closure of `pa-mm0/targets/final.mm0` (the definitions behind the statement). `checker/r0_check.py` checks that the
  receipt used exactly these files.
- [`thm1-inputs.json`](thm1-inputs.json): the receipt sources that are not stored in git, as `name`, `sha256` and
  `bytes`, plus the release tag. They are published as assets of the release `thm1-inputs-v1`;
  `scripts/fetch_large_inputs.sh` checks every downloaded file against this list.
