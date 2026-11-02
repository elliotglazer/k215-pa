#!/bin/sh
# Route T: local end-to-end check of the paThPr_D3 assembly (lanes/D3CHECK.md section 8). Run from the repo root.
#   tools/gen7/d3/check_d3.sh WORKDIR [--no-rm]       (WORKDIR ~0.6 GB; peak RAM ~13 GB in the reflection, ~6 GB after)
# 1. local master reflection RM3 of d3_rsrc2 (= d3_rsrc + the TEST ONLY S6 stand-ins), roots = roots_m + d3r_ql +
#    d3s6_root + the probe d3p_u;
# 2. regenerate d3_ev (stubs verbatim from RM3) and the .mm0 of the hand modules;
# 3. compile the TEST wrapper d3_pad3t (closure: d3_ev .. d3_s6, d3_un, d3_final; GEN3's five facts as TEST axioms);
# 4. link with RM3, keeping as axioms only what the local reflection cannot provide: d3r_adq_R (host reflection of
#    d3_adqsrc's d3r_adq) and GEN3's five facts; minimal spec with every def body (--bodies ALL); mm0-c; axioms.py
#    must list exactly those six; false control.
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); D=tools/gen7/d3
KEEP=d3r_adq_R,g2paThCode_bound,g2paThCode_class,g2paAxCode_bound,g2s1NCode_bound,g2s1SubCode_bound
if [ "$2" != "--no-rm" ]; then
  (cd pa-mm0 && LCHECK_OUT="$W/lc3" python3 ../tools/gen7/lcheck.py gen7/d3_rsrc2 | grep -E '^(compile|check|LOCAL)')
  (cat $D/roots_m.txt; echo d3r_ql; echo d3s6_root; echo d3p_u) > "$W/roots_m3.txt"
  PYTHONPATH=${MM0PAHA:-/home/user/mm0-pa-ha} python3 tools/gen7/refl_lib.py "$W/lc3/gen7/d3_rsrc2/d3_rsrc2.mmb" "$W/RM3" \
    --roots "$W/roots_m3.txt" --cone \
    --nfr paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons \
    | grep -v '^  *[0-9A-F]*:' | tail -12
fi
grep -q '^theorem d3p_u_R (v0: nat) (v1: nat): ' "$W/RM3/out.mm0" && echo "probe d3p_u_R: no side hypotheses"
python3 $D/gen_ev.py "$W/RM3/out.mm0"
for m in d3_ev2 d3_u3 d3_evn d3_s2h d3_s5 d3_un d3_final d3_pad3 d3_pad3t; do python3 $D/mm0of.py pa-mm0/gen7/$m.mm1 > pa-mm0/gen7/$m.mm0; done
(cd pa-mm0 && GEN7_SRC="$W/RM3" LCHECK_OUT="$W/lcf" python3 ../tools/gen7/lcheck.py gen7/d3_pad3t | grep -E '^compile rc')
J="$W/lcf/gen7/d3_pad3t/d3_pad3t-joined.mm0"
python3 $D/minspec.py "$J" g2paThCode_D3,d3_D3core,d3_UNa,d3_UNb,$KEEP --bodies ALL > "$W/d3spec.mm0"
O="$W/linkd3"; mkdir -p "$O"; G=tools/gen7; TOOLS=${MM0TOOLS:-/home/user/mm0-pa-ha/tools}
python3 $G/link.py "$W/RM3/out.mmb" "$W/lcf/gen7/d3_pad3t/d3_pad3t.mmb" "$W/d3spec.mm0" "$O/linked.mmb" "$O/linked.mm0" --keep-axiom $KEEP
"$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.mm0" > "$O/mm0c.log" 2>&1 && echo "mm0-c rc 0" || { echo "mm0-c FAILED"; grep -v '^  [0-9A-F]*:' "$O/mm0c.log" | head; exit 1; }
python3 $G/axioms.py "$O/linked.mmb" "$O/linked.mm0" | tail -1 || true
python3 - "$O/linked.mmb" "$KEEP" <<'PY'
import os, re, sys
sys.path.insert(0, os.environ.get("MM0PAHA", "/home/user/mm0-pa-ha"))
from translator.mmb_reader import read_mmb
m = read_mmb(sys.argv[1])
pax = set(re.findall(r"^\s*axiom\s+([A-Za-z0-9_.]+)", open("lean-mm0/vendor/peano.mm0").read(), re.M))
extra = sorted(m.thms[s.ref].name for s in m.iter_stmts() if s.kind == "axiom" and m.thms[s.ref].name not in pax)
want = sorted(sys.argv[2].split(","))
print("non-peano axioms:", extra, "(expected exactly the kept ones)" if extra == want else "UNEXPECTED")
sys.exit(0 if extra == want else 1)
PY
python3 - "$O/linked.mm0" "$O/linked.false.mm0" <<'PY'
import re, sys
t = open(sys.argv[1]).read()
i = t.index("theorem g2paThCode_D3 ")
j = t.index("$;", i) + 2
open(sys.argv[2], "w").write(t[:i] + re.sub(r"\$[^$]*\$;$", "$ F. $;", t[i:j]) + t[j:])
PY
if "$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.false.mm0" > /dev/null 2>&1; then echo "FALSE CONTROL ACCEPTED"; exit 1; fi
echo "false control (g2paThCode_D3 := F.) rejected"
