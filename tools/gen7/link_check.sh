#!/bin/sh
# Link a hand module into a reflection output and check the result (route T linker, lanes/D3CHECK.md section 8).
#   sh tools/gen7/link_check.sh R.mmb H.mmb H-joined.mm0 OUTDIR
# OUTDIR/linked.mmb, OUTDIR/linked.mm0; exit 0 iff link ok, mm0-c rc 0, only peano's axioms, false control rejected.
set -e
G=$(cd "$(dirname "$0")" && pwd); TOOLS=${MM0TOOLS:-/home/user/mm0-pa-ha/tools}
mkdir -p "$4"; O=$(cd "$4" && pwd)
python3 "$G/link.py" "$1" "$2" "$3" "$O/linked.mmb" "$O/linked.mm0"
"$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.mm0" && echo "mm0-c rc 0"
python3 "$G/axioms.py" "$O/linked.mmb" "$O/linked.mm0"
python3 - "$O/linked.mm0" "$O/linked.false.mm0" <<'PY'
import re, sys
t = open(sys.argv[1]).read().rstrip("\n").split("\n")
k = max(i for i, l in enumerate(t) if l.startswith("theorem "))
j = k
while not t[j].rstrip().endswith("$;"):
    j += 1
st = "\n".join(t[k:j + 1])
st2 = re.sub(r"\$[^$]*\$;\s*$", "$ F. $;", st)
assert st2 != st, "false control: no conclusion replaced"
t[k:j + 1] = [st2]
open(sys.argv[2], "w").write("\n".join(t) + "\n")
PY
if "$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.false.mm0" > /dev/null 2>&1; then echo "FALSE CONTROL ACCEPTED"; exit 1; fi
echo "false control rejected"
