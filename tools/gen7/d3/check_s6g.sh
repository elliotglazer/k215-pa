#!/bin/sh
# Route T, set side: build and kernel-check S6 for Gsr end to end (run from the repo root; WORKDIR ~1 GB, peak RAM ~6 GB).
#   [SZMM0DIR=..] tools/gen7/d3/check_s6g.sh WORKDIR MM0DIR [--no-rm]   (SZMM0DIR: see check_s3h.sh)
# MM0DIR: the .mm0 files of bb215_derivability_l3p_imp's closure (def bodies and K_b bounds; pa-mm0 in a full checkout).
# 1. TEST ONLY stand-in d3_gsrdefs (Gsr's 290 defs) and master reflection RMG of gen7/d3_rsrcG (rmg.sh), 2. regenerate
# d3_g0 / d3_s6g from RMG's statements (stubs verbatim), 3. compile d3_s6g (closure d3_evs, d3_g0, d3_frn) against the
# stubs, 4. link with RMG (stubs -> RMG's proofs), minimal spec (peano.mm0 + every def with its body + the statements below),
# mm0-c, axioms = peano's 26, false control (last statement := F.).
set -e
W=${1:?workdir}; M=${2:?mm0dir}; mkdir -p "$W"; W=$(cd "$W" && pwd); D=tools/gen7/d3
if [ "$3" != "--no-rm" ]; then
  python3 $D/gen_s6g.py "$M" --standin
  [ -z "$SZMM0DIR" ] || python3 $D/gen_s3h.py "$SZMM0DIR" --standin
  for m in d3_gsrdefs d3_szdefs d3_rsrcG; do python3 $D/mm0of.py pa-mm0/gen7/$m.mm1 > pa-mm0/gen7/$m.mm0; done
  sh $D/rmg.sh "$W"
fi
python3 $D/gen_s6g.py "$M" "$W/RMG/out.mm0"
for m in d3_g0 d3_frn d3_s6g; do python3 $D/mm0of.py pa-mm0/gen7/$m.mm1 > pa-mm0/gen7/$m.mm0; done
(cd pa-mm0 && GEN7_SRC="$W/RMG" LCHECK_OUT="$W/lce" python3 ../tools/gen7/lcheck.py gen7/d3_s6g | grep -E '^compile rc')
python3 $D/minspec.py "$W/lce/gen7/d3_s6g/d3_s6g-joined.mm0" d3g_hCons,d3g_hDM,d3g_TR,d3g_FR,d3g_FR0,d3_S6g --bodies ALL > "$W/s6gspec.mm0"
sh tools/gen7/link_check.sh "$W/RMG/out.mmb" "$W/lce/gen7/d3_s6g/d3_s6g.mmb" "$W/s6gspec.mm0" "$W/links6g" | grep -v '^linked'
