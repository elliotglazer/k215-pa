#!/bin/bash
# GEN7 C5 / G2GEN: kernel-check the tmh glue (g7_reflTmHalts_codeL, C5's reflTmHalts_code at the draft literal body) and
# its use in the C5 bridges. Run from the repo root.   tools/gen7/c2/check_tmh.sh WORKDIR [--no-staged]
# Peak RAM ~9 GB per step (gen7_tmh is 24 MB of proofs); a step killed for memory (rc -9) is retried.
#  A. standalone (no stubs left): compile g7src_tmh, reflect it (RT, GEN7_NEED=pf:ctmHalts), regenerate the glue
#     (mkglue.py tmh; must equal the committed pa-mm0/gen7/g7c5_glue_tmh / g7_tmhglue: the stub g7src_tmh_flat_R is
#     verbatim the reflected statement), compile g7_tmhglue against RT, link: g7_reflTmHalts_codeL with every def
#     body, mm0-c rc 0, peano's 26 axioms only, false control rejected.
#  B. staged, as on the host but with C5's local stand-ins: one reflection RI of g7_incsrc_t + g7src_tmh (roots_inc_t
#     + g7src_tmh_flat), stage 1 = link(RI, g7_tmhglue), stage 2 = link(stage 1, g7_incTsf), stage 3 = link(stage 1,
#     g7_incTpa); in 2 / 3 g7_reflTmHalts_codeL is resolved from stage 1 and the only axioms kept are C5's stand-ins.
#     (The host module g7_incH imports g7_tmhglue directly; locally both closures do not fit in RAM together.)
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); ROOT=$(pwd); G=$ROOT/tools/gen7; TOOLS=${MM0TOOLS:-/home/user/mm0-pa-ha/tools}
export PYTHONPATH=${MM0PAHA:-/home/user/mm0-pa-ha}
NFR=paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons
lc() {  # lc GEN7_SRC OUT MODULE : lcheck with retries on OOM kill
  for t in $(seq 1 30); do
    out=$(cd "$ROOT/pa-mm0" && GEN7_SRC="$1" LCHECK_OUT="$2" python3 ../tools/gen7/lcheck.py "$3" 2>&1 || true)
    echo "$out" | grep -q "rc -9" || break; echo "  ($3: killed for memory, retry $t)"; sleep 60
  done
  echo "$out" | grep -E '^compile rc' ; echo "$out" | grep -q '^compile rc 0' || { echo "$out" | head -20; exit 1; }
}
klink() {  # klink R.mmb H.mmb SPEC OUTDIR LASTTHM KEEP(comma list or -)
  O=$4; mkdir -p "$O"; K=(); [ "$6" = "-" ] || K=(--keep-axiom "$6")
  python3 $G/link.py "$1" "$2" "$3" "$O/linked.mmb" "$O/linked.mm0" "${K[@]}"
  "$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.mm0" > "$O/mm0c.log" 2>&1 && echo "mm0-c rc 0" || { echo "mm0-c FAILED"; grep -v '^  [0-9A-F]*:' "$O/mm0c.log" | head; exit 1; }
  python3 - "$O/linked.mmb" "$6" <<'PY'
import os, re, sys
sys.path.insert(0, os.environ.get("MM0PAHA", "/home/user/mm0-pa-ha"))
from translator.mmb_reader import read_mmb
m = read_mmb(sys.argv[1])
pax = set(re.findall(r"^\s*axiom\s+([A-Za-z0-9_.]+)", open("lean-mm0/vendor/peano.mm0").read(), re.M))
ax = [m.thms[s.ref].name for s in m.iter_stmts() if s.kind == "axiom"]
extra = sorted(a for a in ax if a not in pax)
want = [] if sys.argv[2] == "-" else sorted(sys.argv[2].split(","))
print("axioms: %d peano + non-peano %s" % (len(ax) - len(extra), extra), "(as expected)" if extra == want and len(ax) - len(extra) == len(pax) else "UNEXPECTED")
sys.exit(0 if extra == want and len(ax) - len(extra) == len(pax) else 1)
PY
  python3 - "$O/linked.mm0" "$O/linked.false.mm0" "$5" <<'PY'
import re, sys
t = open(sys.argv[1]).read()
i = t.index("theorem %s " % sys.argv[3]); j = t.index("$;", i) + 2
open(sys.argv[2], "w").write(t[:i] + re.sub(r"\$[^$]*\$;$", "$ F. $;", t[i:j]) + t[j:])
PY
  if "$TOOLS/mm0-c" "$O/linked.mmb" < "$O/linked.false.mm0" > /dev/null 2>&1; then echo "FALSE CONTROL ACCEPTED"; exit 1; fi
  echo "false control ($5 := F.) rejected"
}
echo "== A. standalone tmh glue"
python3 $G/d3/mm0of.py pa-mm0/g7src_tmh.mm1 > pa-mm0/g7src_tmh.mm0
lc "" "$W/lc" g7src_tmh
[ -f "$W/RT/out.mmb" ] || GEN7_NEED=pf:ctmHalts python3 $G/refl_lib.py "$W/lc/g7src_tmh/g7src_tmh.mmb" "$W/RT" \
  --roots $G/c2/roots_tmh.txt --cone --nfr $NFR | grep -v '^  *[0-9A-F]*:' | tail -4
mkdir -p "$W/G/gen7"; python3 $G/c2/mkglue.py tmh "$W/RT/out.mm0" "$W/G"
for f in g7c5_glue_tmh g7_tmhglue; do for e in mm1 mm0; do cmp "$W/G/gen7/$f.$e" pa-mm0/gen7/$f.$e || { echo "pa-mm0/gen7/$f.$e is stale (regenerate)"; exit 1; }; done; done
echo "glue modules equal the committed ones"
lc "$W/RT" "$W/lce" gen7/g7_tmhglue
python3 $G/d3/minspec.py "$W/lce/gen7/g7_tmhglue/g7_tmhglue-joined.mm0" g7_reflTmHalts_codeL --bodies ALL > "$W/tspec.mm0"
klink "$W/RT/out.mmb" "$W/lce/gen7/g7_tmhglue/g7_tmhglue.mmb" "$W/tspec.mm0" "$W/linkT" g7_reflTmHalts_codeL -
[ "$2" = "--no-staged" ] && exit 0
echo "== B. staged: C5 bridges with the tmh glue, one reflection"
mkdir -p "$W/cx/gen7"
printf 'import "g7_incsrc_t.mm1";\nimport "../g7src_tmh.mm1";\n\n-- TEST ONLY (check_tmh.sh): C5 local stand-in source + the tmh flat adequacy in one reflection (as d3_adqsrcS on the host).\npub theorem g7_incsrc_tt_final: $ 0 = 0 $ = (named (quote eqid));\n' > "$W/cx/gen7/g7_incsrc_tt.mm1"
printf 'import "g7_incsrc_t.mm0";\nimport "../g7src_tmh.mm0";\ntheorem g7_incsrc_tt_final: $ 0 = 0 $;\n' > "$W/cx/gen7/g7_incsrc_tt.mm0"
lc "$W/cx" "$W/cx/lc" gen7/g7_incsrc_tt
(cat $G/c2/roots_inc_t.txt; echo g7src_tmh_flat) > "$W/cx/roots.txt"
[ -f "$W/cx/RI/out.mmb" ] || GEN7_NEED=pf:ctmHalts,nf:cpaThProvable,nf:cg2paAxSet,nf:csfTheoryProvable,nf:cg2sfAxSet \
  python3 $G/refl_lib.py "$W/cx/lc/gen7/g7_incsrc_tt/g7_incsrc_tt.mmb" "$W/cx/RI" --roots "$W/cx/roots.txt" --cone --nfr $NFR \
  | grep -v '^  *[0-9A-F]*:' | tail -4
lc "$W/cx/RI" "$W/cx/lce" gen7/g7_tmhglue
python3 $G/d3/minspec.py "$W/cx/lce/gen7/g7_tmhglue/g7_tmhglue-joined.mm0" g7_reflTmHalts_codeL --bodies ALL > "$W/cx/s1spec.mm0"
klink "$W/cx/RI/out.mmb" "$W/cx/lce/gen7/g7_tmhglue/g7_tmhglue.mmb" "$W/cx/s1spec.mm0" "$W/cx/s1" g7_reflTmHalts_codeL -
lc "$W/cx/RI" "$W/cx/lce" gen7/g7_incTsf
KS=g7t_fwd
python3 $G/d3/minspec.py "$W/cx/lce/gen7/g7_incTsf/g7_incTsf-joined.mm0" $KS,g7_reflThInc_prL,g7_bridge_of_reflL --bodies ALL > "$W/cx/s2spec.mm0"
klink "$W/cx/s1/linked.mmb" "$W/cx/lce/gen7/g7_incTsf/g7_incTsf.mmb" "$W/cx/s2spec.mm0" "$W/cx/s2" g7_bridge_of_reflL $KS
rm -rf "$W/cx/lce/gen7/g7_incTsf"
lc "$W/cx/RI" "$W/cx/lce" gen7/g7_incTpa
KP=g2paAxCode_bound,g2paThCode_bound,g2paThCode_class,g2s1NCode_bound,g2s1SubCode_bound,g7r_painc_R
python3 $G/d3/minspec.py "$W/cx/lce/gen7/g7_incTpa/g7_incTpa-joined.mm0" $KP,g7_reflPaThInc_prL,g7_bridge_of_refl_paL --bodies ALL > "$W/cx/s3spec.mm0"
klink "$W/cx/s1/linked.mmb" "$W/cx/lce/gen7/g7_incTpa/g7_incTpa.mmb" "$W/cx/s3spec.mm0" "$W/cx/s3" g7_bridge_of_refl_paL $KP
echo "check_tmh: PASS"
