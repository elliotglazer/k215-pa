#!/bin/bash
# G2GEN PA front end: kernel-check the CLOSED-TERM EVALUATION glue on the toy Theorem-1 input (lanes/G2GEN.md
# "CLOSED-TERM EVALUATION"). Run from the repo root.   tools/gen7/c2/check_closed.sh WORKDIR
# ~3.6 GB RAM (perdef), ~3 min, ~150 MB disk in WORKDIR. Every mm0-rs / mm0-c child is time-limited, logs are capped.
#  1. compile the toy source gen7/g7ev_toy (machine g7toy_m / g7toy_M, forward Theorem 1 in variable form g7toy_fwd)
#  2. reflect it: roots tools/gen7/c2/roots_ev.txt (g7ev_src's five facts) + g7toy_fwd, --cone,
#     GEN7_NEED nf:cpaThProvable,nf:cg2paAxSet,nf:ctmHalts (closedness of the hRefl formula)
#  3. regenerate the glue (gen_closed.py): must equal the committed pa-mm0/gen7/g7toy_ev / g7toy_hb
#  4. link g7toy_ev with the reflection: g7toy_hRefl (C5's hRefl at cNum paFormulaFalse, cNum g7toy_m, cNum g7toy_M)
#     with every def body, mm0-c rc 0, peano's 26 axioms ONLY (the stubs g7toy_fwd_R, g7ev_*_R resolve), false control
#  5. link g7toy_hb: hB = g7_bridge_of_refl_paL (iani ..) g7toy_hRefl; the only non-peano axiom kept is that bridge
#     (local TEST stub; proved in g7_incH on the host), false control
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); ROOT=$(pwd); G=$ROOT/tools/gen7; TOOLS=${MM0TOOLS:-/home/user/mm0-pa-ha/tools}
export PYTHONPATH=${MM0PAHA:-/home/user/mm0-pa-ha}
NFR=paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons
lc() {  # lc GEN7_SRC OUT MODULE
  out=$(cd "$ROOT/pa-mm0" && GEN7_SRC="$1" LCHECK_OUT="$2" timeout 1800 python3 ../tools/gen7/lcheck.py "$3" 2>&1 | head -c 20000 || true)
  echo "$out" | grep -E '^compile rc' ; echo "$out" | grep -q '^compile rc 0' || { echo "$out" | head -20; exit 1; }
}
mmc() {  # mmc MMB MM0 -> rc of mm0-c, output capped
  timeout 1800 "$TOOLS/mm0-c" "$1" < "$2" 2>&1 | head -c 4000 > "$3"; return ${PIPESTATUS[0]}
}
klink() {  # klink R.mmb H.mmb SPEC OUTDIR LASTTHM KEEP(comma list or -)
  O=$4; mkdir -p "$O"; K=(); [ "$6" = "-" ] || K=(--keep-axiom "$6")
  timeout 1800 python3 $G/link.py "$1" "$2" "$3" "$O/linked.mmb" "$O/linked.mm0" "${K[@]}" 2>&1 | tail -3
  if mmc "$O/linked.mmb" "$O/linked.mm0" "$O/mm0c.log"; then echo "mm0-c rc 0"; else echo "mm0-c FAILED"; head -c 1500 "$O/mm0c.log"; exit 1; fi
  python3 - "$O/linked.mmb" "$6" <<'PY'
import os, re, sys
sys.path.insert(0, os.environ.get("MM0PAHA", "/home/user/mm0-pa-ha"))
from translator.mmb_reader import read_mmb
m = read_mmb(sys.argv[1])
pax = set(re.findall(r"^\s*axiom\s+([A-Za-z0-9_.]+)", open("lean-mm0/vendor/peano.mm0").read(), re.M))
ax = [m.thms[s.ref].name for s in m.iter_stmts() if s.kind == "axiom"]
extra = sorted(a for a in ax if a not in pax)
want = [] if sys.argv[2] == "-" else sorted(sys.argv[2].split(","))
ok = extra == want and len(ax) - len(extra) == len(pax)
print("axioms: %d peano + non-peano %s" % (len(ax) - len(extra), extra), "(as expected)" if ok else "UNEXPECTED")
sys.exit(0 if ok else 1)
PY
  python3 - "$O/linked.mm0" "$O/linked.false.mm0" "$5" <<'PY'
import re, sys
t = open(sys.argv[1]).read()
i = t.index("theorem %s:" % sys.argv[3]) if ("theorem %s:" % sys.argv[3]) in t else t.index("theorem %s " % sys.argv[3])
j = t.index("$;", i) + 2
open(sys.argv[2], "w").write(t[:i] + re.sub(r"\$[^$]*\$;$", "$ F. $;", t[i:j]) + t[j:])
PY
  if mmc "$O/linked.mmb" "$O/linked.false.mm0" "$O/false.log"; then echo "FALSE CONTROL ACCEPTED"; exit 1; fi
  echo "false control ($5 := F.) rejected"
  rm -f "$O/linked.mmb"
}
echo "== 1. toy source"
lc "" "$W/lc" gen7/g7ev_toy
echo "== 2. reflection RE"
(cat $G/c2/roots_ev.txt; echo g7toy_fwd) > "$W/roots.txt"
[ -f "$W/RE/out.mmb" ] || GEN7_NEED=nf:cpaThProvable,nf:cg2paAxSet,nf:ctmHalts timeout 3600 \
  python3 $G/refl_lib.py "$W/lc/gen7/g7ev_toy/g7ev_toy.mmb" "$W/RE" --roots "$W/roots.txt" --cone --nfr $NFR 2>&1 \
  | grep -v '^  *[0-9A-F]*:' | tail -6 | cut -c1-300
grep -q '^theorem g7toy_fwd_R ' "$W/RE/out.mm0" || { echo "reflection failed"; exit 1; }
echo "== 3. generate the glue"
mkdir -p "$W/G/gen7"
python3 $G/c2/gen_closed.py "$W/RE/out.mm0" "$W/RE/gen7/perdef.mm1" "$W/G" --thm g7toy_fwd_R --name g7toy --src gen7/g7ev_toy --bridge stub
for f in g7toy_ev g7toy_hb; do for e in mm1 mm0; do cmp "$W/G/gen7/$f.$e" pa-mm0/gen7/$f.$e || { echo "pa-mm0/gen7/$f.$e is stale (regenerate)"; exit 1; }; done; done
echo "glue modules equal the committed ones"
echo "== 4. hRefl: no stub left"
lc "$W/RE" "$W/lce" gen7/g7toy_ev
python3 $G/d3/minspec.py "$W/lce/gen7/g7toy_ev/g7toy_ev-joined.mm0" g7toy_hRefl --bodies ALL > "$W/espec.mm0"
klink "$W/RE/out.mmb" "$W/lce/gen7/g7toy_ev/g7toy_ev.mmb" "$W/espec.mm0" "$W/linkE" g7toy_hRefl -
echo "== 5. hB = bridge_of_reflection_pa (literal reading) at the toy machine"
lc "$W/RE" "$W/lcb" gen7/g7toy_hb
python3 $G/d3/minspec.py "$W/lcb/gen7/g7toy_hb/g7toy_hb-joined.mm0" g7_bridge_of_refl_paL,g7toy_hB --bodies ALL > "$W/bspec.mm0"
klink "$W/RE/out.mmb" "$W/lcb/gen7/g7toy_hb/g7toy_hb.mmb" "$W/bspec.mm0" "$W/linkB" g7toy_hB g7_bridge_of_refl_paL
rm -rf "$W/lce/gen7/perdef" "$W/lcb/gen7/perdef"
echo "CLOSED-TERM EVALUATION: PASS"
