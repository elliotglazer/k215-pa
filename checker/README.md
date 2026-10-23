# checker: acceptance and verification tools

| file | what it does |
| --- | --- |
| [`r0_check.py`](r0_check.py) | Checks the theorem-1 receipt against the statement: `python3 -I checker/r0_check.py receipt/thm1/report.json` prints `R0 OK` only if the report is `PASSED` with the pinned tools and the false-conclusion control, the spec closure matches the report and the manifest, and the checked theorem states exactly theorem 1 of `targets/final.mm0`. It does not re-run the proof checker. |
| [`mm0_join.py`](mm0_join.py) | A byte-exact, independent replica of `mm0-rs join`, so the joined spec hash in the report can be reproduced without trusting `mm0-rs`. |
| [`final_spec_verify.py`](final_spec_verify.py) | Verifies that an acceptance copy of a frozen spec (such as `targets/final.mm0`) checks exactly the frozen statements and changes nothing `mm0-c` reads. |
| [`mm0-c-capacity.patch`](mm0-c-capacity.patch) | The patch applied to upstream `mm0-c`: larger, heap-allocated name tables and a fix for files over 2 GiB on Windows. It does not touch the proof-checking logic. |
| [`synth_mmb.py`](synth_mmb.py) | Writes a synthetic spec and `.mmb` binary to stress-test the patched `mm0-c` name tables (with `false`, one that must be rejected). |
