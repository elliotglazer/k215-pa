# receipt/thm1: the report of the theorem-1 check

- [`report.json`](report.json): written by `pa-mm0/check.py`. Module `k215_final_thm1`, status `PASSED`, no new project
  axioms, closed dependency graph; the SHA-256 of every source file (2156 `.mm0` + 2156 `.mm1`), of the joined spec,
  the proof input and the `.mmb` binary; the list of checked theorems, including
  `K215_halts_iff_ZFC_inconsistent_final`; and the pinned tool hashes.
- [`status.json`](status.json): the run itself: the `capacity2` `mm0-c` build, exit code 0, no timeout,
  2026-10-23 11:43-15:28 UTC, compile peak commit 459 GB, check peak 7.0 GB, a 4.6 GB `.mmb`.
- [`reject-false.log`](reject-false.log): the control. The same `.mmb` with the last theorem's statement replaced by `F.`
  is rejected by `mm0-c` with a unify failure at that theorem, which shows the checker really compares proofs with
  statements.

`python3 -I checker/r0_check.py receipt/thm1/report.json` checks this receipt against the statement and prints
`R0 OK`. The `*_proved: false` fields in `report.json` are constants that `check.py` writes into every report.
