#!/bin/sh
# Route T, set side: build and kernel-check S3h end to end (run from the repo root after check_s6g.sh, which builds the
# reflection RMG in WORKDIR; peak RAM ~6 GB).   tools/gen7/d3/check_s3h.sh WORKDIR SZMM0DIR
# SZMM0DIR: the .mm0 files of g2_generic_sz_rec's closure (pa-mm0 in a full checkout). The TEST ONLY stand-in
# d3_szdefs is part of RMG's source (d3_rsrcG); regenerate it with gen_s3h.py SZMM0DIR --standin before rmg.sh.
# Compiles d3_s3h (closure d3_un + d3_szdefs) against RMG's stubs, links with RMG, minimal spec with every def body,
# mm0-c, axioms = peano's 26, false control (d3_S3h := F.).
set -e
W=${1:?workdir}; M=${2:?mm0dir}; W=$(cd "$W" && pwd); D=tools/gen7/d3
python3 $D/gen_s3h.py "$M"
python3 $D/mm0of.py pa-mm0/gen7/d3_s3h.mm1 > pa-mm0/gen7/d3_s3h.mm0
(cd pa-mm0 && GEN7_SRC="$W/RMG" LCHECK_OUT="$W/lce" python3 ../tools/gen7/lcheck.py gen7/d3_s3h | grep -E '^compile rc')
python3 $D/minspec.py "$W/lce/gen7/d3_s3h/d3_s3h-joined.mm0" d3_S3h --bodies ALL > "$W/s3hspec.mm0"
sh tools/gen7/link_check.sh "$W/RMG/out.mmb" "$W/lce/gen7/d3_s3h/d3_s3h.mmb" "$W/s3hspec.mm0" "$W/links3h" | grep -v '^linked'
