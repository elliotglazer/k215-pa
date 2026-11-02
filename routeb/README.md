# Route B: the PA -> HA translator (exact snapshot used for the archived HA proof)

`src/` is the translator snapshot that produced the HA proof archived at
[doi:10.5281/zenodo.23872595](https://doi.org/10.5281/zenodo.23872595) (`b6-out.mmb`, sha256
`636804b4f6f465d09934c88cf0263569dd8409694323c6eed962afab56082fe0`). Every file is listed with its sha256 in
`MANIFEST.sha256` (manifest sha256 `91e5db56a6d2ad659eb7cd88336ac057b9be8edfcae367cbaecc179b56b6f641`, the value
recorded by the run).

Nothing here needs to be trusted to accept the HA result: `mm0-c` checks the HA binary against `b6-out.mm0`,
whose axioms are `src/foundation/hpeano.mm0` verbatim. The translator is untrusted; a bug in it can only make
that check fail. It is here so the HA binary can be rebuilt from the PA binary, and other PA proofs of Pi2
sentences translated.

## Contents

- `src/translator/`: `.mmb` reader / writer and the combined negative + Friedman (A-) translation
  (`negtrans.py`): every PA theorem is translated once, with the Friedman formula as an extra argument.
- `src/b5/`: recovery of the plain Pi2 statement from its translation (decidability of the bounded matrix,
  Friedman's argument), and its HA-side library sources.
- `src/b6/b6.py`: the driver. It reads the PA `.mmb`, translates it, adds the recovery proofs, writes the HA
  `.mmb` and its spec (`hpeano.mm0` verbatim + the bounded definitions + the approved statements), runs `mm0-c`,
  and runs a control in which one statement is replaced by falsity (it must be rejected).
  `src/b6/b6-lib*.mmb` are the precompiled HA-side libraries (pinned; `--rebuild-lib` regenerates them).
- `src/foundation/`: `hpeano.mm0` (Heyting arithmetic) and `peano.mm0` (PA).
- `src/b4/`: the approved Pi2 statements (approved by the owner on 2026-10-24 for `b4b`; the header line "DRAFT (NOT
  approved ...)" in `b4b_statements.mm0` predates that approval and is kept because the file is pinned by hash) (`b4_statements.mm0`, `b4b_statements.mm0`) and their bounded
  definitions (`bd_certs.mm0`, `bd_certs_b4b.mm0`), which `b6.py` pins by sha256.

## Rebuilding the archived HA proof

Pure-stdlib Python 3 (the run used CPython 3.14 on Windows). From the archive, decompress `b4b_final.mmb.zst`
(the PA proof, sha256 `25b7a4d5...`). Build `mm0-c` with the capacity3 patches (recipe in the archive: hypothesis
and unification stacks 4096 instead of 256) and put it in a directory `TOOLS`. Then

    python3 -B -I src/b6/b6.py --src b4b_final.mmb --out OUT --tools TOOLS --limits capacity3

(`--set b4b` is chosen from the input name). The archived run took 3.6 h of translation and 74 GB of memory;
the `mm0-c` check of the 18.46 GB output took 81 s and 17.8 GB. `OUT/report.json` records the hashes; compare
`OUT/b6-out.mm0` and `OUT/b6-out.mmb` with the archive.
