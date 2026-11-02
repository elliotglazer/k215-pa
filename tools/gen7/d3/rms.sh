#!/bin/sh
# Route T, set side: master reflection RMS of the d3_rsrcS closure (= d3_rsrc + paFormulaSource / sfRename laws),
# roots roots_s.txt (= roots_m.txt + the EVS laws). A superset of rm.sh's RM (same statements for roots_m).
#   tools/gen7/d3/rms.sh WORKDIR      (run from the repo root; ~5 GB RAM, ~2 min)
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); D=$(pwd)/tools/gen7/d3
(cd pa-mm0 && LCHECK_OUT="$W/lcs" python3 ../tools/gen7/lcheck.py gen7/d3_rsrcS | grep -E '^(compile|check|LOCAL)')
PYTHONPATH=${MM0PAHA:-/home/user/mm0-pa-ha} python3 tools/gen7/refl_lib.py "$W/lcs/gen7/d3_rsrcS/d3_rsrcS.mmb" "$W/RMS" \
  --roots "$D/roots_s.txt" --cone \
  --nfr paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons \
  | grep -v '^  *[0-9A-F]*:' | tail -12
