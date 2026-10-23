# scripts: fetch the large inputs and compare runs

| file | what it does |
| --- | --- |
| [`fetch_large_inputs.sh`](fetch_large_inputs.sh) | `sh scripts/fetch_large_inputs.sh [TAG]` (default `thm1-inputs-v1`): downloads the release parts, checks them against `SHA256SUMS`, unpacks into `pa-mm0/`, and checks every file against `manifests/thm1-inputs.json` and the receipt, both of which are in git. Downloads go to `.large-inputs/TAG`; delete it afterwards. |
| [`check_sources.py`](check_sources.py) | `python3 -I scripts/check_sources.py`: checks that every source the receipt lists is in `pa-mm0/` with the listed hash; the last line says whether the closure is complete. |
| [`compare_report.py`](compare_report.py) | `python3 -I scripts/compare_report.py pa-mm0/artifacts/report.json`: compares the report of your own `check.py` run with the published receipt. Module, status, sources, joined spec, theorem list and control must be equal; tool and binary hashes are informational. |
