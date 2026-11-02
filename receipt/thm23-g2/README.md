# receipt/thm23-g2: the reports of the Theorem 2 / 3 / G2 checks

| folder | run | what it checked |
| --- | --- | --- |
| [`pa/`](pa/) | link-check of `b4b_final` (2026-11-01) | status `PASSED`, 26 axioms (those of `peano.mm0`), no new project axioms, closed dependency graph; 6,176 sources (3,088 `.mm0` + 3,088 `.mm1`) with their sha256; joined spec `6d79aac00163704465d3ef258e919f8e17804f2fcf479ba326d74b178780428b`, identical to the spec the linked binary carries; binary `25b7a4d54ab8393ddc281385334851dba8b231b366b087884946444ba14e1f18` (9,695,267,856 bytes, the PA binary on Zenodo). The spec contains every theorem of the closure, among them Theorems 1, 2, 3, the G2 theorems and the 7 Pi2 forms; the report's `checked_theorems` names the 4 stated in `b4b_final.mm0` itself |
| [`pa-g2/`](pa-g2/) | link-check of `zfc_incompleteness_root` (2026-10-31) | status `PASSED`, 26 axioms, no new project axioms; 6,056 sources (a subset of `pa/`'s, same hashes); joined spec `f02b3e623ecb4f88c34a491fc195698ead914cd3feeaec22ecf8b958bc2cb393`; the 16 `*_inc` theorems of G2 |
| [`ha/`](ha/) | translation of the `pa/` binary to HA and its check (2026-11-01) | result `PASS`: 0 failed theorems or definitions, no unmapped axioms; output `b6-out.mmb` sha256 `636804b4f6f465d09934c88cf0263569dd8409694323c6eed962afab56082fe0` (the HA binary on Zenodo) accepted by `mm0-c` (`capacity3` build, sha256 `faae0333...`) against [`b6-out.mm0`](ha/b6-out.mm0); the 7 public theorems have exactly the approved text (`final_public_theorems`) |

Each folder has `report.json` (written by the checking tool), `status.json` (the run: exit code, times, peak memory,
tool hashes) and the false-conclusion control: `reject-false.log` for `pa/` and `pa-g2/` (the binary with the last
theorem's statement replaced by `F.` is rejected by `mm0-c`), `control.log` for `ha/` (`b6-out.mm0` with
`K215_G2_pi2` replaced by `F.` is rejected).

[`MANIFEST.json`](MANIFEST.json) lists every file with its bytes and sha256, and the sha256 of the file as the runner
wrote it. For publication, the host-specific keys (host name, slot, cache and work folders, free disk) were removed
from `status.json`, and in `pa/report.json` and `ha/report.json` the absolute host paths were replaced by their last
component (for example `b4b_final.mmb`); nothing else was changed.

To check that the sources in `pa-mm0/` are exactly the ones these runs used (after
`sh scripts/fetch_large_inputs.sh all`):

    python3 -I scripts/check_sources.py receipt/thm23-g2/pa/report.json
    python3 -I scripts/check_sources.py receipt/thm23-g2/pa-g2/report.json
