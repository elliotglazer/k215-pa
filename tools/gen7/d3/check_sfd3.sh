#!/bin/bash
# Route T, set side: local check of the sfThPr_D3 assembly (g2sfThPrL_D3, gen_sfd3.py). Run from the repo root.
#   tools/gen7/d3/check_sfd3.sh WORKDIR        (WORKDIR ~1 GB; peak RAM ~9 GB; an OOM-killed compile is retried)
# 1. TEST ONLY reflection source gen7/d3_rsrcD (= d3_rsrcG + GEN2 g2_generic_sf_code + image formula; compiled with the
#    d3_szdefs host shim, i.e. GEN2's real g2_generic_sz_rec), reflection RMD (roots_D.txt = roots_g.txt + d3sD_root).
# 2. Compile the TEST wrapper d3_sfd3t (core d3_sfcore + GEN2 / L05 stand-in axioms) against RMD's stubs.
# 3. Link with RMD, minimal spec with every def body, mm0-c, false control (g2sfThPrL_D3 := F.). Kept axioms must be
#    exactly keep_sfd3t.txt: d3r_D3S_R (host reflection of d3_adqsrcS) + the stand-ins of GEN2's g2sfThPrL_formula,
#    g2sfPrAt_fwd / _bwd and L05's 19 K_b bounds (the host wrapper d3_sfd3 imports the real ones).
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); ROOT=$(pwd); G=$ROOT/tools/gen7; D=$G/d3; TOOLS=${MM0TOOLS:-/home/user/mm0-pa-ha/tools}
export PYTHONPATH=${MM0PAHA:-/home/user/mm0-pa-ha}
NFR=paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons
lc() {  # lc GEN7_SRC OUT MODULE
  for t in $(seq 1 30); do
    out=$(cd "$ROOT/pa-mm0" && GEN7_SRC="$1" LCHECK_OUT="$2" python3 ../tools/gen7/lcheck.py "$3" 2>&1 || true)
    echo "$out" | grep -q "rc -9" || break; echo "  ($3: killed for memory, retry $t)"; sleep 60
  done
  echo "$out" | grep -E '^compile rc'; echo "$out" | grep -q '^compile rc 0' || { echo "$out" | head -20; exit 1; }
}
mkdir -p "$W/shim/gen7"; cp $D/host/gen7/d3_szdefs.mm1 $D/host/gen7/d3_szdefs.mm0 "$W/shim/gen7/"
python3 $D/mm0of.py pa-mm0/gen7/d3_rsrcD.mm1 > pa-mm0/gen7/d3_rsrcD.mm0
if [ ! -f "$W/RMD/out.mmb" ]; then
  lc "$W/shim" "$W/lc" gen7/d3_rsrcD
  python3 $G/refl_lib.py "$W/lc/gen7/d3_rsrcD/d3_rsrcD.mmb" "$W/RMD" --roots $D/roots_D.txt --cone --nfr $NFR \
    | grep -v '^  *[0-9A-F]*:' | tail -4
fi
cp $D/host/gen7/d3_szdefs.mm1 $D/host/gen7/d3_szdefs.mm0 "$W/RMD/gen7/"
python3 $D/gen_sfd3.py
for m in d3_sfcore d3_sfd3t; do python3 $D/mm0of.py pa-mm0/gen7/$m.mm1 > pa-mm0/gen7/$m.mm0; done
lc "$W/RMD" "$W/lce" gen7/d3_sfd3t
KEEP=$(cat $D/keep_sfd3t.txt)
python3 $D/minspec.py "$W/lce/gen7/d3_sfd3t/d3_sfd3t-joined.mm0" $KEEP,g2sfThPrL_D3 --bodies ALL > "$W/sfd3spec.mm0"
O=$W/linksfd3; mkdir -p "$O"
python3 $G/link.py "$W/RMD/out.mmb" "$W/lce/gen7/d3_sfd3t/d3_sfd3t.mmb" "$W/sfd3spec.mm0" "$O/linked.mmb" "$O/linked.mm0" --keep-axiom "$KEEP"
"$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.mm0" > "$O/mm0c.log" 2>&1 && echo "mm0-c rc 0" || { echo "mm0-c FAILED"; grep -v '^  [0-9A-F]*:' "$O/mm0c.log" | head; exit 1; }
python3 - "$O/linked.mmb" "$KEEP" <<'PY'
import os, re, sys
sys.path.insert(0, os.environ.get("MM0PAHA", "/home/user/mm0-pa-ha"))
from translator.mmb_reader import read_mmb
m = read_mmb(sys.argv[1])
pax = set(re.findall(r"^\s*axiom\s+([A-Za-z0-9_.]+)", open("lean-mm0/vendor/peano.mm0").read(), re.M))
ax = [m.thms[s.ref].name for s in m.iter_stmts() if s.kind == "axiom"]
extra = sorted(a for a in ax if a not in pax); want = sorted(sys.argv[2].split(","))
ok = extra == want and len(ax) - len(extra) == len(pax)
print("axioms: %d peano + %d kept (%s)" % (len(ax) - len(extra), len(extra), "exactly keep_sfd3t.txt" if ok else "UNEXPECTED %r" % extra))
sys.exit(0 if ok else 1)
PY
python3 - "$O/linked.mm0" "$O/linked.false.mm0" <<'PY'
import re, sys
t = open(sys.argv[1]).read()
i = t.index("theorem g2sfThPrL_D3 "); j = t.index("$;", i) + 2
open(sys.argv[2], "w").write(t[:i] + re.sub(r"\$[^$]*\$;$", "$ F. $;", t[i:j]) + t[j:])
PY
if "$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.false.mm0" > /dev/null 2>&1; then echo "FALSE CONTROL ACCEPTED"; exit 1; fi
echo "false control (g2sfThPrL_D3 := F.) rejected"
echo "check_sfd3: PASS"
