#!/bin/sh
# Route T: build the master reflection RM of the d3_rsrc closure (stubs for d3_r / d3_u3 come from RM/out.mm0).
#   tools/gen7/d3/rm.sh WORKDIR      (run from the repo root; needs ~0.5 GB in WORKDIR, ~5 GB RAM)
set -e
W=${1:?workdir}; R=$(pwd); D=$R/tools/gen7/d3
mkdir -p "$W"
(cd pa-mm0 && LCHECK_OUT="$W/lc" python3 ../tools/gen7/lcheck.py gen7/d3_rsrc)
PYTHONPATH=${MM0PAHA:-/home/user/mm0-pa-ha} python3 tools/gen7/refl_lib.py "$W/lc/gen7/d3_rsrc/d3_rsrc.mmb" "$W/RM" \
  --roots "$D/roots_m.txt" --cone \
  --nfr paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons
