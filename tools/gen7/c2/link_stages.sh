#!/bin/bash
# staged link: R(i+1) = link(R(i), H) for each module H (compiled alone, KEEP), one at a time.
# usage: stage.sh RIN.mmb OUTDIR MOD1 [MOD2 ..]   (MOD: path relative to pa-mm0 without extension; gen7/... or top level)
S=/tmp/claude-0/-home-user/7eb09a65-9e55-590d-84fa-50c66f314974/scratchpad/g7c2
R=$1; O=$2; shift 2
mkdir -p $O
export GEN7_SRC=$S/d2/rl
export LCHECK_OUT=$S/lc
cd /home/user/k215-pa-mm0/.claude/worktrees/agent-adc913e38b309817b/pa-mm0
i=0
for M in "$@"; do
  i=$((i+1)); B=$(basename $M)
  for t in 1 2 3 4 5 6 7 8 9 10; do
    out=$(python3 ../tools/gen7/lcheck.py $M 2>&1)
    echo "$out" | grep -q "rc -9" || break
    sleep 90
  done
  echo "== $M: $(echo "$out" | grep -v '^ *$' | head -2 | tr '\n' ' ')"
  D=$LCHECK_OUT/$M
  [ -f $D/$B.mmb ] || { echo "no mmb for $M"; exit 1; }
  lo=$(sh $S/lk/tools/gen7/link_check.sh $R $D/$B.mmb $D/$B-joined.mm0 $O/s$i 2>&1); echo "$lo" | tail -5
  echo "$lo" | grep -q "^mm0-c rc 0" && echo "$lo" | grep -q "not in peano.mm0: \[\]" && echo "$lo" | grep -q "^false control rejected" || { echo "stage $i FAILED"; exit 1; }
  [ $i -gt 1 ] && rm -f $R
  R=$O/s$i/linked.mmb
  rm -rf $D
done
echo "final: $R"
