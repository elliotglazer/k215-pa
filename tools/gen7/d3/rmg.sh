#!/bin/sh
# Route T, set side: master reflection RMG of the d3_rsrcG closure (= d3_rsrcS + rename laws + Gsr closure), roots
# roots_g.txt (= roots_s.txt + roots_gnew.txt + d3g_root). A superset of rms.sh's RMS.
#   tools/gen7/d3/rmg.sh WORKDIR      (run from the repo root)
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); D=$(pwd)/tools/gen7/d3
(cd pa-mm0 && LCHECK_OUT="$W/lcg" python3 ../tools/gen7/lcheck.py gen7/d3_rsrcG | grep -E '^(compile|check|LOCAL)')
PYTHONPATH=${MM0PAHA:-/home/user/mm0-pa-ha} python3 tools/gen7/refl_lib.py "$W/lcg/gen7/d3_rsrcG/d3_rsrcG.mmb" "$W/RMG" \
  --roots "$D/roots_g.txt" --cone \
  --nfr paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons \
  | grep -v '^  *[0-9A-F]*:' | tail -12
