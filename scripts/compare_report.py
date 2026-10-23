"""Compare a report.json from your own run of pa-mm0/check.py with the published theorem-1 receipt.

    python3 -I scripts/compare_report.py pa-mm0/artifacts/report.json [receipt/thm1/report.json]

The fields that fix what was checked (module, status, sources, joined spec, proof input, theorem list, the
false-conclusion control, vendor hashes) must be equal. Tool and binary hashes are informational: a checker
built on another platform has another hash, and the .mmb depends on the mm0-rs build.
"""
import json, sys

mine = json.load(open(sys.argv[1], encoding='utf-8-sig'))
ref = json.load(open(sys.argv[2] if len(sys.argv) > 2 else 'receipt/thm1/report.json', encoding='utf-8-sig'))
MUST = ['status', 'module', 'new_project_axioms', 'sources', 'dependency_graph_closed', 'spec_sha256', 'proof_input_mode',
        'proof_input_sha256', 'proof_module_order', 'checked_theorems', 'wrong_conclusion_rejected', 'wrong_conclusion_control',
        'vendor']
INFO = ['binary_sha256', 'binary_bytes', 'checker_sha256', 'compiler_sha256']
bad = 0
for k in MUST:
    same = mine.get(k) == ref.get(k)
    bad += not same
    print('%-26s %s' % (k, 'equal' if same else 'DIFFERS'))
for k in INFO:
    print('%-26s %s (informational)' % (k, 'equal' if mine.get(k) == ref.get(k) else 'differs'))
print('MATCH: your run checked exactly what the receipt covers' if not bad else '%d required fields differ' % bad)
sys.exit(1 if bad else 0)
