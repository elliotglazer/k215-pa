#!/bin/bash
# Regenerate the generated GEN7 C2 modules (run from anywhere).
set -e
D=$(cd "$(dirname "$0")" && pwd)
python3 "$D/gen_tf.py"
python3 "$D/gen_eq.py"
python3 "$D/gen_conv.py"
python3 "$D/gen_tf2.py"
python3 "$D/gen_tg.py"
python3 "$D/gen_ax4.py"
python3 "$D/gen_ax5.py"
python3 "$D/gen_ax6.py"
python3 "$D/gen_bx1.py"
python3 "$D/gen_bx2.py"
python3 "$D/gen_bx3.py"
python3 "$D/gen_bx4.py"
python3 "$D/gen_bx5.py"
python3 "$D/gen_bx6.py"
python3 "$D/gen_numg.py"
python3 "$D/gen_tsch.py"   # also writes tsch_cores.pkl (read by gen_tmh.py)
python3 "$D/gen_tsch_inst.py" tmh
python3 "$D/gen_tsch_inst.py" tval
python3 "$D/gen_tsch_inst.py" hle
python3 "$D/gen_tsch_inst.py" hpos
python3 "$D/gen_hle.py"
python3 "$D/gen_l0.py"
