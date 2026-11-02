#!/bin/sh
# G2GEN PA front end: local check of the (B-PA) headline assembly (lanes/G2GEN.md "PA FRONT END"). Run from the repo root.
#   tools/gen7/d3/check_pahead.sh WORKDIR          (WORKDIR ~60 MB; peak RAM ~1.7 GB)
# 1. generate g2pa_head / g2pa_headt / g2pa_spec (gen_pahead.py; checks the spec-text defs against g2_generic_defs.mm0);
# 2. compile g2pa_bb (the real general-predicate core, no stub) and g2pa_inst (T = PA instance; imports g2pa_spec) with g2pa_head replaced by a shim importing
#    the TEST module g2pa_headt (GEN3 / route T / C5 facts as stub axioms, statements copied from their .mm0);
# 3. minimal spec with every def body (minspec --bodies ALL) for the three spec theorems (text verbatim from
#    targets/g2_generic.mm0, compared below), the L forms, the core and the kept stubs; mm0-c; the non-peano axioms must be
#    exactly the seven stubs; false control on BB_generic_pa_thm3. (link.py with R = peano only reorders the spec.)
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); D=tools/gen7/d3; G=tools/gen7; TOOLS=${MM0TOOLS:-/home/user/mm0-pa-ha/tools}
KEEP=g2paAxSet_value,g2paThCode_bound,g2paThCode_D1,g2paThCode_fixed_point,g2paThCode_D2,g2paThCode_D3,tm_run_cut
python3 $D/gen_pahead.py
for m in g2pa_bb g2pa_head g2pa_headt g2pa_spec g2pa_inst; do python3 $D/mm0of.py pa-mm0/gen7/$m.mm1 > pa-mm0/gen7/$m.mm0; done
mkdir -p "$W/shim/gen7"
echo 'import "g2pa_headt.mm1";' > "$W/shim/gen7/g2pa_head.mm1"; echo 'import "g2pa_headt.mm0";' > "$W/shim/gen7/g2pa_head.mm0"
(cd pa-mm0 && LCHECK_OUT="$W/lc" python3 ../tools/gen7/lcheck.py gen7/g2pa_bb | grep -E '^(compile|check|false|LOCAL)')
(cd pa-mm0 && GEN7_SRC="$W/shim" LCHECK_OUT="$W/lc" python3 ../tools/gen7/lcheck.py gen7/g2pa_inst | grep -E '^(compile|LOCAL)')
J="$W/lc/gen7/g2pa_inst/g2pa_inst-joined.mm0"; B="$W/lc/gen7/g2pa_inst/g2pa_inst.mmb"
THMS=G2_generic_pa,BB_generic_pa_thm2,BB_generic_pa_thm3,g2pi_rec,g2pi_prov,g2pi_inc,g2pi_hT1,G2_pa,BB_pa_thm2,BB_pa_thm3,G2_generic_paL,BB_generic_pa_thm2L,BB_generic_pa_thm3L,g2pb_thm2_P,g2pb_thm3_P
python3 $D/minspec.py "$J" $THMS,$KEEP --bodies ALL > "$W/paspec.mm0"
# order the spec as the .mmb (link.py with R = peano alone; the stubs stay axioms: --keep-axiom, local test only)
"$TOOLS/mm0-rs" compile lean-mm0/vendor/peano.mm1 "$W/peano.mmb" > /dev/null
python3 $G/link.py "$W/peano.mmb" "$B" "$W/paspec.mm0" "$W/linked.mmb" "$W/linked.mm0" --keep-axiom $KEEP | tail -1
B="$W/linked.mmb"
"$TOOLS/mm0-c" "$B" < "$W/linked.mm0" > "$W/mm0c.log" 2>&1 && echo "mm0-c rc 0 (minimal spec, every def body)" || { echo "mm0-c FAILED"; head "$W/mm0c.log"; exit 1; }
python3 - "$B" "$KEEP" "$W/linked.mm0" pa-mm0/targets/g2_generic.mm0 <<'PY'
import os, re, sys
sys.path.insert(0, os.environ.get("MM0PAHA", "/home/user/mm0-pa-ha"))
from translator.mmb_reader import read_mmb
m = read_mmb(sys.argv[1])
pax = set(re.findall(r"^\s*axiom\s+([A-Za-z0-9_.]+)", open("lean-mm0/vendor/peano.mm0").read(), re.M))
extra = sorted(m.thms[s.ref].name for s in m.iter_stmts() if s.kind == "axiom" and m.thms[s.ref].name not in pax)
want = sorted(sys.argv[2].split(","))
print("non-peano axioms:", extra, "(exactly the kept stubs)" if extra == want else "UNEXPECTED")
def st(path, n):
    t = open(path).read(); i = re.search(r"(?m)^theorem %s\b" % n, t).start(); return " ".join(t[i:t.index("$;", i)].split())
ok = all(st(sys.argv[3], n) == st(sys.argv[4], n) for n in ("G2_generic_pa", "BB_generic_pa_thm2", "BB_generic_pa_thm3"))
print("checked statements of G2_generic_pa / BB_generic_pa_thm2 / _thm3 identical to targets/g2_generic.mm0:", ok)
sys.exit(0 if extra == want and ok else 1)
PY
python3 - "$W/linked.mm0" "$W/linked.false.mm0" <<'PY'
import re, sys
t = open(sys.argv[1]).read(); i = t.index("theorem BB_generic_pa_thm3 "); j = t.index("$;", i) + 2
open(sys.argv[2], "w").write(t[:i] + re.sub(r"\$[^$]*\$;$", "$ F. $;", t[i:j], flags=re.S) + t[j:])
PY
if "$TOOLS/mm0-c" "$B" < "$W/linked.false.mm0" > /dev/null 2>&1; then echo "FALSE CONTROL ACCEPTED"; exit 1; fi
echo "false control (BB_generic_pa_thm3 := F.) rejected"
# 4. sample machine: the statements-only pre-check elaborates against the spec; negative control (ill-typed variant) rejected
(cd pa-mm0/gen7 && "$TOOLS/mm0-rs" compile g2pa_sample.mm0 2>&1 | tail -1)
sed 's/m_PA <= n/m_PA <= M_PA M_PA/' pa-mm0/gen7/g2pa_sample.mm0 > pa-mm0/gen7/g2pa_sample_neg.mm0
if (cd pa-mm0/gen7 && "$TOOLS/mm0-rs" compile g2pa_sample_neg.mm0 > /dev/null 2>&1); then rm -f pa-mm0/gen7/g2pa_sample_neg.mm0; echo "NEGATIVE CONTROL ACCEPTED"; exit 1; fi
rm -f pa-mm0/gen7/g2pa_sample_neg.mm0; echo "sample: elaborates; negative control rejected"
