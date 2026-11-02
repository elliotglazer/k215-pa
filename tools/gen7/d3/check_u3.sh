#!/bin/sh
# Route T: build and kernel-check U3 end to end (run from the repo root; WORKDIR needs ~1 GB, peak RAM ~5.5 GB).
#   tools/gen7/d3/check_u3.sh WORKDIR [--no-rm]
# 1. master reflection RM of the d3_rsrc closure (rm.sh), 2. regenerate d3_ev from RM's statements (stubs verbatim),
# 3. compile d3_evn (closure d3_ev, d3_ev2, d3_u3, d3_evn over d3_r / d3_fi / perdef) against the stubs,
# 4. link with RM (stubs -> RM's proofs), minimal spec (peano.mm0 + abstract defs + d3_U3h, d3_U3f, d3_EVNt, d3_EVN), mm0-c,
#    axioms = peano's 26, false control.
set -e
W=${1:?workdir}; mkdir -p "$W"; W=$(cd "$W" && pwd)
[ "$2" = "--no-rm" ] || tools/gen7/d3/rm.sh "$W"
python3 tools/gen7/d3/gen_ev.py "$W/RM/out.mm0"
for m in d3_ev2 d3_u3 d3_evn d3_s2h d3_s5; do python3 tools/gen7/d3/mm0of.py pa-mm0/gen7/$m.mm1 > pa-mm0/gen7/$m.mm0; done
(cd pa-mm0 && GEN7_SRC="$W/RM" LCHECK_OUT="$W/lcm" python3 ../tools/gen7/lcheck.py gen7/d3_s5 | grep -E '^(compile|check) rc')
python3 tools/gen7/d3/minspec.py "$W/lcm/gen7/d3_s5/d3_s5-joined.mm0" d3_U3h,d3_U3f,d3_EVNt,d3_EVN,d3_S2h,d3_S5 > "$W/u3spec.mm0"
sh tools/gen7/link_check.sh "$W/RM/out.mmb" "$W/lcm/gen7/d3_s5/d3_s5.mmb" "$W/u3spec.mm0" "$W/linku3" | grep -v '^linked'
