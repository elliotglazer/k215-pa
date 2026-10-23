#!/bin/sh
# Download the large proof inputs of the theorem-1 receipt (receipt sources that are not stored in git) from the GitHub
# release TAG, check every part against the release's SHA256SUMS, unpack into pa-mm0/, and check every unpacked file
# against manifests/thm1-inputs.json and receipt/thm1/report.json (both tracked in git, so a modified release asset is
# detected even if its SHA256SUMS was modified too). Needs curl, sha256sum, tar, python3. Run from the repository root.
#   sh scripts/fetch_large_inputs.sh [TAG]          (default tag: thm1-inputs-v1)
# Downloads go to .large-inputs/TAG (resumable; delete it afterwards to free the space).
set -eu
REPO=elliotglazer/k215-pa
TAG=${1:-thm1-inputs-v1}
case "$TAG" in *[!A-Za-z0-9._-]*|'') echo "bad tag: $TAG" >&2; exit 1;; esac
[ -f manifests/thm1-inputs.json ] && [ -d pa-mm0 ] || { echo "run this from the repository root" >&2; exit 1; }
BASE=${K215_INPUTS_BASE:-https://github.com/$REPO/releases/download/$TAG}
DL=.large-inputs/$TAG
mkdir -p "$DL"
curl -fsSL -o "$DL/SHA256SUMS" "$BASE/SHA256SUMS"
while read -r sum name; do
  case "$name" in *[!A-Za-z0-9._-]*|'') echo "bad part name: $name" >&2; exit 1;; esac
  if [ ! -f "$DL/$name" ] || [ "$(sha256sum "$DL/$name" | cut -d' ' -f1)" != "$sum" ]; then
    echo "downloading $name"
    curl -fL -# --retry 5 -C - -o "$DL/$name" "$BASE/$name" || curl -fL -# --retry 5 -o "$DL/$name" "$BASE/$name"
  fi
done < "$DL/SHA256SUMS"
(cd "$DL" && sha256sum -c SHA256SUMS)
# The parts are one gzip'd tar cut into pieces; it holds only regular files pa-mm0/<name>.
cut -d' ' -f3 "$DL/SHA256SUMS" | while read -r name; do cat "$DL/$name"; done | tar -tzf - > "$DL/listing.txt"
if grep -v -E '^pa-mm0/[A-Za-z0-9_.-]+\.mm[01]$' "$DL/listing.txt" >/dev/null; then
  echo "unexpected path in the archive:" >&2; grep -v -E '^pa-mm0/[A-Za-z0-9_.-]+\.mm[01]$' "$DL/listing.txt" >&2; exit 1
fi
cut -d' ' -f3 "$DL/SHA256SUMS" | while read -r name; do cat "$DL/$name"; done | tar -xzf - --no-same-owner
python3 -I - <<'EOF'
import hashlib, json, sys
man = json.load(open('manifests/thm1-inputs.json'))['files']
src = json.load(open('receipt/thm1/report.json', encoding='utf-8-sig'))['sources']
bad = 0
for f in man:
    h = hashlib.sha256()
    try:
        with open('pa-mm0/' + f['name'], 'rb') as g:
            for chunk in iter(lambda: g.read(1 << 24), b''): h.update(chunk)
    except FileNotFoundError:
        print('MISSING pa-mm0/' + f['name']); bad += 1; continue
    if h.hexdigest() != f['sha256'] or src.get(f['name']) != f['sha256']:
        print('MISMATCH pa-mm0/' + f['name']); bad += 1
print('%d large inputs unpacked, %s' % (len(man), 'all hashes match the receipt' if not bad else '%d MISMATCHES' % bad))
sys.exit(1 if bad else 0)
EOF
