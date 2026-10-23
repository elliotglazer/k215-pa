"""Check the proof sources in pa-mm0/ against the theorem-1 receipt.

    python3 -I scripts/check_sources.py [receipt/thm1/report.json]

Every file the receipt lists under "sources" (the complete .mm0/.mm1 import closure of k215_final_thm1) must be in
pa-mm0/ with the SHA-256 the receipt lists. Files of manifests/thm1-inputs.json (the release assets) may still be
missing before scripts/fetch_large_inputs.sh has run; any other missing file or any mismatch is an error.
Exit 0 when nothing is wrong; the last line says whether the closure is complete.
"""
import hashlib, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
rep = json.load(open(sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'receipt/thm1/report.json'), encoding='utf-8-sig'))
large = {f['name'] for f in json.load(open(os.path.join(ROOT, 'manifests/thm1-inputs.json')))['files']}
ok = missing_large = 0
bad = []
for name, want in sorted(rep['sources'].items()):
    p = os.path.join(ROOT, 'pa-mm0', name)
    if not os.path.isfile(p):
        if name in large:
            missing_large += 1
        else:
            bad.append('MISSING ' + name)
        continue
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 24), b''):
            h.update(chunk)
    if h.hexdigest() == want:
        ok += 1
    else:
        bad.append('MISMATCH ' + name)
for b in bad:
    print(b)
print('%d of %d receipt sources present with the receipt hash; %d large inputs not fetched yet; %d errors; closure %s'
      % (ok, len(rep['sources']), missing_large, len(bad), 'COMPLETE' if ok == len(rep['sources']) else 'incomplete'))
sys.exit(1 if bad else 0)
