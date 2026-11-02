#!/bin/sh
# D3CHECK GO/STOP test (lanes/D3CHECK.md section 7). From the repo root:  sh tools/gen7/d3t/run.sh OUTDIR
# 1. compile the g2_generic_s1_tarski closure; 2. reflect the cone of roots.txt (refl_lib --cone; mm0-c on the
# reflection); 3. check that every stub axiom of d3t.mm0 is a reflected statement of R4/out.mm0, verbatim;
# 4. compile + check d3t (the U3 Ex / And cases and the TQ All case) over the reflection's code defs.
set -e
ROOT=$(pwd); OUT=$(realpath -m "$1"); D=$ROOT/tools/gen7/d3t
export PYTHONPATH=${PYTHONPATH:-/home/user/mm0-pa-ha}
cd "$ROOT/pa-mm0"
LCHECK_OUT=$OUT/lc python3 ../tools/gen7/lcheck.py g2_generic_s1_tarski | tail -1
python3 ../tools/gen7/refl_lib.py "$OUT/lc/g2_generic_s1_tarski/g2_generic_s1_tarski.mmb" "$OUT/R4" --roots "$D/roots.txt" --cone
grep '^axiom ' "$D/d3t.mm0" | sed 's/^axiom /theorem /' | while IFS= read -r l; do
  grep -qxF "$l" "$OUT/R4/out.mm0" || { echo "STUB NOT REFLECTED: $l"; exit 1; }; done
echo "stubs: all reflected verbatim"
cp "$D/d3t.mm1" "$D/d3t.mm0" "$OUT/R4/gen7/"
GEN7_SRC=$OUT/R4 LCHECK_OUT=$OUT/lcd python3 ../tools/gen7/lcheck.py gen7/d3t
# 5. link: replace the stubs by R4's reflected proofs; mm0-c on the linked file, peano axioms only, false control
sh ../tools/gen7/link_check.sh "$OUT/R4/out.mmb" "$OUT/lcd/gen7/d3t/d3t.mmb" "$OUT/lcd/gen7/d3t/d3t-joined.mm0" "$OUT/linked"
# 6. control: a stub stronger than the reflected statement must make the linked file fail mm0-c
cp "$D/d3bad.mm1" "$D/d3bad.mm0" "$OUT/R4/gen7/"
GEN7_SRC=$OUT/R4 LCHECK_OUT=$OUT/lcd python3 ../tools/gen7/lcheck.py gen7/d3bad | grep 'compile rc'
if sh ../tools/gen7/link_check.sh "$OUT/R4/out.mmb" "$OUT/lcd/gen7/d3bad/d3bad.mmb" "$OUT/lcd/gen7/d3bad/d3bad-joined.mm0" "$OUT/linkbad" > "$OUT/linkbad.log" 2>&1; then
  echo "BAD STUB ACCEPTED"; exit 1; fi
echo "bad-stub control rejected"
