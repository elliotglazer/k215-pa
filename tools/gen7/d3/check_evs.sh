#!/bin/sh
# Route T, set side: build and kernel-check EVS end to end (run from the repo root; WORKDIR ~1 GB, peak RAM ~5.5 GB).
#   tools/gen7/d3/check_evs.sh WORKDIR [--no-rm]
# 1. master reflection RMS of gen7/d3_rsrcS (rms.sh), 2. regenerate d3_ev / d3_evs0 / d3_evc from RMS's statements (stubs
# verbatim), 3. compile d3_evs (closure d3_ev .. d3_evn, d3_evs0, d3_evc) against the stubs, 4. link with RMS (stubs ->
# RMS's proofs), minimal spec (peano.mm0 + abstract defs + d3_EVS, d3_EVSt, d3s_RN), mm0-c, axioms = peano's 26, false control.
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd); D=tools/gen7/d3
[ "$2" = "--no-rm" ] || sh $D/rms.sh "$W"
python3 $D/gen_ev.py "$W/RMS/out.mm0"
python3 $D/gen_evs.py "$W/RMS/out.mm0"
for m in d3_ev2 d3_u3 d3_evn d3_evs0 d3_evc d3_evs; do python3 $D/mm0of.py pa-mm0/gen7/$m.mm1 > pa-mm0/gen7/$m.mm0; done
(cd pa-mm0 && GEN7_SRC="$W/RMS" LCHECK_OUT="$W/lce" python3 ../tools/gen7/lcheck.py gen7/d3_evs | grep -E '^compile rc')
python3 $D/minspec.py "$W/lce/gen7/d3_evs/d3_evs-joined.mm0" d3s_RN,d3_EVSt,d3_EVS > "$W/evsspec.mm0"
sh tools/gen7/link_check.sh "$W/RMS/out.mmb" "$W/lce/gen7/d3_evs/d3_evs.mmb" "$W/evsspec.mm0" "$W/linkevs" | grep -v '^linked'
