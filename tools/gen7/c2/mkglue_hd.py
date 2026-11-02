"""GEN7 C5 glue for hD (GEN4's internal padding, deduction form) from the reflected padding lemma.

  python3 mkglue_hd.py OUT.mm0 GLUEDIR

OUT.mm0 / GLUEDIR: refl_lib output of pa-mm0/g7src_hd.mm1 (roots tmPad_halts_d, g7src_{tmh,tval,hle,hpos}_flat;
GEN7_NEED=pf:ctmHalts,pf:ctmValid,pf:cle,pf:clt,pf:ctmPadOf). Writes GLUEDIR/gen7/g7c5_glue_hd.mm1/.mm0 (the glue
lemma g7_hD_of: the reflected statements at numeral codes enter as hypotheses hR*, and two meta inputs:
hV = g7_valid_pa_imp (gen7_hv) and hP = the tmPadOf hypothesis completeness) and the SCRATCH stub test
g7c5_gluetest_hd (reflected statements as stub axioms, applied at numeral codes)."""
import re, sys
sys.path.insert(0, '/home/user/k215-pa-mm0/.claude/worktrees/agent-adc913e38b309817b/pa-mm0')
import bb215_l3_engine as eng
spec, gd = sys.argv[1], sys.argv[2]
S = open(spec).read()

def J(c): return '(trJ (trPA %s))' % c
def num(v): return '(cNum %s)' % v
Vc = '(ctmValid %s %s)' % (num('m'), num('M'))
Pc = '(ctmPadOf %s %s %s %s)' % (num('m'), num('n'), num('M'), num('T'))
Lc = '(cle %s %s)' % (num('m'), num('n'))
Zc = '(clt c0 %s)' % num('m')
Hm = '(ctmHalts %s %s)' % (num('m'), num('M'))
Hn = '(ctmHalts %s %s)' % (num('n'), num('T'))
H4 = '(can (can (can %s %s) %s) %s)' % (Vc, Pc, Lc, Zc)
IFF = '(ciff %s %s)' % (Hn, Hm)
FN = '(g7_nfr_fresh nfr_cNum)'
FR = {'V': '(g7pfc_ctmValid %s %s)' % (FN, FN), 'P': '(g7pfc_ctmPadOf %s %s %s %s)' % (FN, FN, FN, FN),
      'L': '(g7pfc_cle %s %s)' % (FN, FN), 'Z': '(g7pfc_clt (g7_nfr_fresh nfr_c0) %s)' % FN,
      'Hm': '(g7pfc_ctmHalts %s %s)' % (FN, FN), 'Hn': '(g7pfc_ctmHalts %s %s)' % (FN, FN)}
B = {k: '(g7_closed_Jt %s)' % v for k, v in FR.items()}
def BI(a, b): return '(mpbir paFormulaBound_imp (iani %s %s))' % (a, b)
def BN(a): return BI(a, 'paFormulaBound_false')
JC = '(eqtr g7_J_can (trNoteq (paFormulaImpeq (eqtr g7_J_can (trNoteq (paFormulaImpeq g7_J_can eqid))) eqid)))'
bH4 = '(mpbir (paFormulaBoundeq2 %s) %s)' % (JC, BN(BI(BN(BI(BN(BI(B['V'], BN(B['P']))), BN(B['L']))), BN(B['Z']))))
JIFF = '(eqtr g7_J_can (trNoteq (paFormulaImpeq g7_J_cIm (trNoteq g7_J_cIm))))'
bIFF = '(mpbir (paFormulaBoundeq2 %s) %s)' % (JIFF, BN(BI(BI(B['Hn'], B['Hm']), BN(BI(B['Hm'], B['Hn'])))))
EQ4 = '(paFormulaImpeq eqid (paFormulaImpeq eqid (paFormulaImpeq eqid (paFormulaImpeq eqid %s))))' % JC
AND4 = '(mpbir (paProvableeq2 %s) (g7_and4_0 %s %s %s %s))' % (EQ4, B['V'], B['P'], B['L'], B['Z'])
RPAD = '(mpbi (paProvableeq2 trPA_cIm) (mpbi (g7_cpr_iff (mpbir (paFormulaBoundeq2 trPA_cIm) %s)) hRpad))' % BI(bH4, bIFF)
IFFR = '(mpbir (paProvableeq2 (paFormulaImpeq %s eqid)) (g7_iffr_0 %s %s))' % (JIFF, B['Hn'], B['Hm'])
B1 = '(g7_tmh_bridge_rev hRhm %s)' % FR['Hm']
B2 = '(g7_tmh_bridge hRhn %s)' % FR['Hn']
K = '(bb215D2_mp %s (bb215D2_mp %s (g7_comp_0 (anl (bi1 paFormulaBound_imp (paProvable_bound %s))) %s %s (anr (bi1 paFormulaBound_imp (paProvable_bound %s))))))' % (
    B2, B1, B1, B['Hm'], B['Hn'], B2)
FV = '(syl (syl (com12 bb215D2_mp (g7_tval_bridge_rev hRv %s)) hV) an3l)' % FR['V']
FP = '(syl hP anllr)'
FZ = '(syl (syl (com12 bb215D2_mp (g7_hpos_bridge_rev hRz %s)) g7_pos_pa) anlr)' % FR['Z']
FL = '(syl (syl (com12 bb215D2_mp (g7_hle_bridge_rev hRl %s)) g7_le_pa) anr)' % FR['L']
H4p = '(sylc bb215D2_mp %s (sylc bb215D2_mp %s (sylc bb215D2_mp %s (sylc bb215D2_mp %s (a1i %s)))))' % (FZ, FL, FP, FV, AND4)
IFFp = '(sylc bb215D2_mp %s (a1i %s))' % (H4p, RPAD)
YX = '(sylc bb215D2_mp %s (a1i %s))' % (IFFp, IFFR)
FINAL = '(sylc bb215D2_mp %s (a1i %s))' % (YX, K)

HYPS = [('hRpad', 'cPr (cIm %s %s)' % (H4, IFF)),
        ('hRhm', 'cPr (ciff (g7tmhCode m M) %s)' % Hm), ('hRhn', 'cPr (ciff (g7tmhCode n T) %s)' % Hn),
        ('hRv', 'cPr (ciff (g7tvalCode m M) %s)' % Vc), ('hRl', 'cPr (ciff (g7hleCode m n) %s)' % Lc),
        ('hRz', 'cPr (ciff (g7hposCode m) %s)' % Zc),
        ('hV', 'tmValid m M -> paProvable 0 (paFormulaSubst 0 (paTermNumeral M) (tmgTableArithmeticValidCode m))'),
        ('hP', 'tmPadOf m n M T -> paProvable 0 %s' % J(Pc))]
CONCL = 'tmValid m M -> tmPadOf m n M T -> 0 < m -> m <= n -> paProvable 0 (paFormulaImp (tmHaltsPA m M) (tmHaltsPA n T))'
hs = '\n  '.join('(%s: $ %s $)' % h for h in HYPS)
imps = ['g7c5_slim']
import subprocess
_PD = gd + '/gen7/perdef.mm1'
_W = ['g7_tmh_bridge:gen7/gen7_tmh.mm0', 'g7_tmh_bridge_rev:gen7/gen7_tmh.mm0', 'g7_tval_bridge_rev:gen7/gen7_tval.mm0',
      'g7_tpad_bridge_rev:gen7/gen7_tpad.mm0', 'g7_tpad_vsplit:gen7/gen7_tpad.mm0', 'g7_hle_bridge_rev:gen7/gen7_thle.mm0',
      'g7_hpos_bridge_rev:gen7/gen7_thpos.mm0', 'g7_valid_pa_imp:gen7/gen7_hv.mm0', 'g7_pad_pa:g7_pad_pa.mm0'] + \
     ['g7pfc_%s:%s' % (c, _PD) for c in ('ctmValid', 'ctmPadOf', 'cle', 'clt', 'ctmHalts')]
subprocess.run([sys.executable, '/home/user/k215-pa-mm0/.claude/worktrees/agent-adc913e38b309817b/tools/gen7/c2/mkslim.py', gd, ','.join(_W)], check=True)
_pp = open('/home/user/k215-pa-mm0/.claude/worktrees/agent-adc913e38b309817b/pa-mm0/g7_pad_pa.mm0').read()
_i = _pp.index('theorem g7_pad_pa '); _j = _pp.index('$;', _i)
HPADS = _pp[_pp.index('$', _i) + 1:_j].strip()                       # (A. qq A. bb ...) -> paProvable 0 PAD
PADF = HPADS[HPADS.index('-> paProvable 0 ') + len('-> paProvable 0 '):]
HPRE = HPADS[:HPADS.index(') -> paProvable 0 ') + 1]
VN = 'paFormulaSubst 0 (paTermNumeral T) (tmgTableArithmeticValidCode n)'
BRP = '(g7_tpad_bridge_rev hRp %s)' % FR['P']
BFULL = '(mpbi (paFormulaBoundeq2 g7_tpad_vsplit) (anl (bi1 paFormulaBound_imp (paProvable_bound %s))))' % BRP
AND2 = '(g7_and2_0 (anl (bi1 paFormulaBound_and %s)) (anr (bi1 paFormulaBound_and %s)))' % (BFULL, BFULL)
PX = '(syl (bi2 (paProvableeq2 g7_tpad_vsplit)) (sylc bb215D2_mp (syl hPP anr) (sylc bb215D2_mp (syl hVn anl) (a1i %s))))' % AND2
HP_PROOF = '(syl (com12 bb215D2_mp %s) %s)' % (BRP, PX)
HPHYPS = [('hRp', 'cPr (ciff (g7tpadCode m n M T) %s)' % Pc), ('hVn', 'tmValid n T -> paProvable 0 (%s)' % VN), ('hPP', HPADS)]
HPTHM = 'pub theorem g7_hP_of (m n M T: nat) {x qq bb: nat}\n  %s:\n  $ tmPadOf m n M T -> paProvable 0 %s $' % (
    '\n  '.join('(%s: $ %s $)' % h for h in HPHYPS), J(Pc))
thm = 'pub theorem g7_hD_of (m n M T: nat) {x: nat}\n  %s:\n  $ %s $' % (hs, CONCL)
open(gd + '/gen7/g7c5_glue_hd.mm1', 'w').write(''.join('import "%s.mm1";\n\n' % i for i in imps) +
    '-- G7 C5 glue (generated by tools/gen7/c2/mkglue_hd.py): hD from the reflected padding lemma.\n' +
    "%s =\n(named '(exp (exp (exp %s))));\n\n%s =\n(named '%s);\n" % (thm, FINAL, HPTHM, HP_PROOF))
open(gd + '/gen7/g7c5_glue_hd.mm0', 'w').write(''.join('import "%s.mm0";\n\n' % i for i in imps) + thm[4:] + ';\n\n' + HPTHM[4:] + ';\n')

# ---- scratch stub test
def stub(name):
    i = S.index('theorem %s ' % name)
    j = S.index('$;', S.index('$ cPr', i)) + 2
    return S[i:j]
def sides(stmt, na):
    out = []
    for h, kind, a, b in re.findall(r'\(h(\d+): \$ (nfr|nne) v(\d+) v(\d+) \$\)', stmt):
        a, b = int(a), int(b)
        if kind == 'nfr': out.append('nfr_cNum')
        else:
            x, y = a - na, b - na
            out.append('(ltnei %s)' % eng.lt(x, y) if x < y else '(ltneri %s)' % eng.lt(y, x))
    return ' '.join(out)
st = {k: stub(k) for k in ['tmPad_halts_d_R', 'g7src_tmh_flat_R', 'g7src_tval_flat_R', 'g7src_hle_flat_R', 'g7src_hpos_flat_R', 'g7src_pad_flat_R']}
axs = '\n'.join('axiom ' + v[len('theorem '):] for v in st.values())
call = '(g7_hD_of tmPad_halts_d_R (g7src_tmh_flat_R %s) (g7src_tmh_flat_R %s) (g7src_tval_flat_R %s) (g7src_hle_flat_R %s) (g7src_hpos_flat_R %s) g7_valid_pa_imp (g7_hP_of (g7src_pad_flat_R %s) g7_valid_pa_imp g7_pad_pa))' % (
    sides(st['g7src_tmh_flat_R'], 2), sides(st['g7src_tmh_flat_R'], 2), sides(st['g7src_tval_flat_R'], 2),
    sides(st['g7src_hle_flat_R'], 2), sides(st['g7src_hpos_flat_R'], 1), sides(st['g7src_pad_flat_R'], 4))
tst = 'theorem g7_hD (m n M T: nat):\n  $ %s $' % CONCL
open(gd + '/gen7/g7c5_gluetest_hd.mm1', 'w').write('import "g7c5_glue_hd.mm1";\n\n-- SCRATCH ONLY: reflected statements as stub axioms.\n%s\n\npub %s =\n(named \'%s);\n' % (axs, tst, call))
open(gd + '/gen7/g7c5_gluetest_hd.mm0', 'w').write('import "g7c5_glue_hd.mm0";\n\n%s\n\n%s;\n' % (axs, tst))
print('ok')
