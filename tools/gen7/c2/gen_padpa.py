r"""GEN7 C5: PA proves the padding part of g7PadFullCode at numerals whenever the padding relation holds
(implication form, uniform in m n M T). Writes pa-mm0/g7_pad_pa.mm1 / .mm0.

    g7_pad_pa (m n M T): A. q A. b ((q < m /\ b < 2) -> tmAct T q b = tmRename m n (tmAct M q b))
                         -> paProvable 0 PAD(m, n, M, T)

PAD = A. q A. b ((Work_m(q) /\ (b = 0 \/ b = 1)) -> A. i A. v A. w ((Pair(q, b, i) /\ Nth(i, T, v)) /\ Nth(i, M, w)
       -> Stored(v, w))),   Stored(v, w) = E. a E. c ((Pred(v, a) /\ Pred(w, c)) /\ Ren(a, c)),
Ren(a, c) = E. x E. r (Pair(x, r, c) /\ E. y E. t (Pair(y, t, r) /\ E. s (Pair(x, s, a) /\
            ((t = m /\ Pair(y, n, s)) \/ (~ t = m /\ Pair(y, t, s)))))),
the second conjunct of g7PadFullCode (pa-mm0/gen7/gen7_tpad.mm1; checked against these builders).
Argument (the one of bb215_source_value_valid_build.py, lane L06): for numerals q0 < m and b0 in {0, 1}, Pair and
Nth are functional (i = (q0, b0), v = nth i T, w = nth i M) and Stored(nth i T, nth i M) is a true closed Sigma1
sentence: its witnesses are explicit numeral terms (a = v - 1, c = w - 1, x = fst c, r = snd c, y = fst r,
t = snd r, s = snd a) and its QF pieces are closed QF completeness; the disjunction splits on t = m (meta).
The b guard is an or-elimination, the q guard L07's enumeration paD0_cut_enum over the m numerals.
"""
import os, re, sys
from pathlib import Path
PAD = '/home/user/k215-pa-mm0/.claude/worktrees/agent-adc913e38b309817b/pa-mm0'
sys.path.insert(0, PAD)
os.chdir(PAD)
sys.setrecursionlimit(200000)
_vb = (Path(PAD) / 'bb215_source_value_valid_build.py').read_text(encoding='utf8')
_vb = _vb.split('# ---------------------------------------------------------------- HV at a numeral', 1)[0]
_vb = _vb.replace("HERE = os.path.dirname(os.path.abspath(__file__))", "HERE = %r" % PAD, 1)

VB = {'__name__': 'g7_pad_builders', '__file__': str(Path(PAD) / 'bb215_source_value_valid_build.py')}
exec(compile(_vb, '<valid builders>', 'exec'), VB)
globals().update({k: v for k, v in VB.items() if not k.startswith('__')})
qf_false = L6['qf_false']

NM_, NN_, NMt, NTt = Nm('m'), Nm('n'), Nm('M'), Nm('T')

def workm(q): return Ex(Eq(A(sh(q), S(v(0))), NM_))
def ren(a, c):
    inner = Or(And(Eq(v(1), NM_), pair(v(2), NN_, v(0))), And(Not(Eq(v(1), NM_)), pair(v(2), v(1), v(0))))
    return Ex(Ex(And(pair(v(1), v(0), sh_(c, 2)), Ex(Ex(And(pair(v(1), v(0), v(2)), Ex(And(pair(v(4), v(0), sh_(a, 5)), inner))))))))
def stored(w1, w2): return Ex(Ex(And(And(pred(sh_(w1, 2), v(1)), pred(sh_(w2, 2), v(0))), ren(v(1), v(0)))))
def entry(q, b):
    return All(All(All(Imp(And(And(pair(sh_(q, 3), sh_(b, 3), v(2)), nthF(v(2), sh_(NTt, 3), v(1))), nthF(v(2), sh_(NMt, 3), v(0))),
                           stored(v(1), v(0))))))
def PADF(): return All(All(Imp(And(workm(v(1)), binF(v(0))), entry(v(1), v(0)))))

# ---- the frozen code: second conjunct of g7PadFullCode (as printed in gen7_tpad.mm1)
txt = (Path(PAD) / 'gen7' / 'gen7_tpad.mm1').read_text()
i = txt.index('def g7PadFullCode'); j = txt.index('$', i); k = txt.index('$', j + 1)
toks = txt[j + 1:k].replace('(', ' ( ').replace(')', ' ) ').split()
pos = [0]
def sx():
    t = toks[pos[0]]; pos[0] += 1
    if t != '(': return t
    o = []
    while toks[pos[0]] != ')': o.append(sx())
    pos[0] += 1
    return o
def natv(x):
    if isinstance(x, str): return int(x)
    if len(x) == 1: return natv(x[0])
    return natv(x[1]) + 1
def conv(x):
    if isinstance(x, str): return {'paTermZero': Z, 'paFormulaFalse': F}[x]
    if len(x) == 1: return conv(x[0])
    h = x[0]
    if h == 'paTermVariable': return v(natv(x[1]))
    if h == 'paTermNumeral': return ('n', x[1])
    un = {'paTermSuccessor': S, 'paFormulaAll': All, 'paFormulaEx': Ex}
    bi = {'paTermAddition': A, 'paTermMultiplication': M, 'paFormulaEqual': Eq, 'paFormulaAnd': And, 'paFormulaOr': Or, 'paFormulaImp': Imp}
    if h in un: return un[h](conv(x[1]))
    return bi[h](conv(x[1]), conv(x[2]))
FULL = conv(sx())
need(FULL[0] == 'and', 'full shape')
need(FULL[2] == PADF(), 'frozen pad code = builders')
PADSTMT = fm(PADF())

spec, proof = [], []
def th_(name, args, stmt, prf, pub=False):
    s = 'theorem ' + name + args + ': $ ' + stmt + ' $'
    if pub: spec.append(s + ';')
    proof.append(('pub ' if pub else '') + s + " = (named '" + prf + ');')
P = 'g7PP'
HPAD = 'A. qq A. bb ((qq < m /\\ bb < 2) -> tmAct T qq bb = tmRename m n (tmAct M qq bb))'

# ---------------------------------------------------------------- Stored at numerals from the meta relation
# context: h: vv - 1 = tmRename m n (ww - 1)  (vv, ww numerals); witnesses as numeral terms
VV, WW = Nm('vv'), Nm('ww')
wa, wc = '(vv - 1)', '(ww - 1)'
wx, wr = '(fst %s)' % wc, '(snd %s)' % wc
wy, wt = '(fst %s)' % wr, '(snd %s)' % wr
ws = '(snd %s)' % wa
Wa, Wc, Wx, Wr, Wy, Wt, Ws = (Nm(e) for e in (wa, wc, wx, wr, wy, wt, ws))
ST = stored(VV, WW)
# the chain of instances
b_a = ST[1]; i_a = subst_f(0, Wa, b_a)[0]          # E. c (...)
b_c = i_a[1]; i_c = subst_f(0, Wc, b_c)[0]          # (Pv /\ Pw) /\ Ren(a, c)
PREDS, RENi = i_c[1], i_c[2]
b_x = RENi[1]; i_x = subst_f(0, Wx, b_x)[0]
b_r = i_x[1]; i_r = subst_f(0, Wr, b_r)[0]          # Pair(x, r, c) /\ E y E t ...
P1, EY = i_r[1], i_r[2]
b_y = EY[1]; i_y = subst_f(0, Wy, b_y)[0]
b_t = i_y[1]; i_t = subst_f(0, Wt, b_t)[0]          # Pair(y, t, r) /\ E s ...
P2, ES = i_t[1], i_t[2]
b_s = ES[1]; i_s = subst_f(0, Ws, b_s)[0]           # Pair(x, s, a) /\ OR
P3, ORF = i_s[1], i_s[2]
need(PREDS == And(pred(VV, Wa), pred(WW, Wc)), 'preds')
need(ORF == Or(And(Eq(Wt, NM_), pair(Wy, NN_, Ws)), And(Not(Eq(Wt, NM_)), pair(Wy, Wt, Ws))), 'or piece')
PRED_A = '(a1i (bi2 bb215ArithmeticFormulaPredecessorGraph_correct eqid))'
L_PREDS = qf_true(to_l6(PREDS), '(iand %s %s)' % (PRED_A, PRED_A))
L_P1 = qf_true(to_l6(P1), pair_fact('(a1i (eqcom fstsnd))'))
L_P2 = qf_true(to_l6(P2), pair_fact('(a1i (eqcom fstsnd))'))
# a = (fst c, snd a): fst a = fst c from h (fst of tmRename)
FSTA = '(eqtr4d (a1i (eqcom fstsnd)) (preq1d (eqcomd (eqtrd (syl fsteq id) (a1i fstpr)))))'
L_P3 = qf_true(to_l6(P3), pair_fact(FSTA))
# snd a = (y, if (t = m) n t) from h
SNDA = '(eqtrd (syl sndeq id) (a1i sndpr))'
OR_L = Thm(0, Imp(And(Eq(Wt, NM_), pair(Wy, NN_, Ws)), ORF), or_left_ax(0, ORF[1], ORF[2]).proof)
OR_R = Thm(0, Imp(And(Not(Eq(Wt, NM_)), pair(Wy, Wt, Ws)), ORF), or_right_ax(0, ORF[1], ORF[2]).proof)
AND1 = and_intro_ax(0, Eq(Wt, NM_), pair(Wy, NN_, Ws))
AND2 = and_intro_ax(0, Not(Eq(Wt, NM_)), pair(Wy, Wt, Ws))
# branch t = m (context h /\ t = m)
B1 = MPC(OR_L.proof, MPC2(AND1.proof, qf_true(to_l6(Eq(Wt, NM_)), 'anr'),
         qf_true(to_l6(pair(Wy, NN_, Ws)), pair_fact('(eqtrd (syl %s anl) (preq2d (syl ifpos anr)))' % SNDA))))
B2 = MPC(OR_R.proof, MPC2(AND2.proof, qf_false(to_l6(Eq(Wt, NM_)), 'anr'),
         qf_true(to_l6(pair(Wy, Wt, Ws)), pair_fact('(eqtrd (syl %s anl) (preq2d (syl ifneg anr)))' % SNDA))))
L_OR = '(casesda %s %s)' % (B1, B2)
AND3 = and_intro_ax(0, P3, ORF)
L_S = MPC2(AND3.proof, L_P3, L_OR)
e_s = ex_intro_imp(0, b_s, Ws)
AND4 = and_intro_ax(0, P2, ES)
L_T = MPC2(AND4.proof, L_P2, MPC(e_s.proof, L_S))
e_t = ex_intro_imp(0, b_t, Wt); e_y = ex_intro_imp(0, b_y, Wy)
AND5 = and_intro_ax(0, P1, EY)
L_R = MPC2(AND5.proof, L_P1, MPC(e_y.proof, MPC(e_t.proof, L_T)))
e_r = ex_intro_imp(0, b_r, Wr); e_x = ex_intro_imp(0, b_x, Wx)
AND6 = and_intro_ax(0, PREDS, RENi)
L_C = MPC2(AND6.proof, L_PREDS, MPC(e_x.proof, MPC(e_r.proof, L_R)))
e_c = ex_intro_imp(0, b_c, Wc); e_a = ex_intro_imp(0, b_a, Wa)
need(e_a.f[2] == ST, 'stored witness')
L_ST = MPC(e_a.proof, MPC(e_c.proof, L_C))
th_(P + '_st', ' (m n vv ww: nat)', 'vv - 1 = tmRename m n (ww - 1) -> paProvable 0 ' + fm(ST), L_ST)

# ---------------------------------------------------------------- one table row: Hpad -> q < m -> Prov R(q, b0)
NQ = Nm('q')
th_(P + '_inst', ' (m n M T q b: nat) {qq bb: nat}',
    '(%s) -> (q < m /\\ b < 2) -> tmAct T q b = tmRename m n (tmAct M q b)' % HPAD, '(syl {(!! eale bb ,eqtac) : $ (A. bb ((q < m /\\ bb < 2) -> tmAct T q bb = tmRename m n (tmAct M q bb))) -> ((q < m /\\ b < 2) -> tmAct T q b = tmRename m n (tmAct M q b)) $} (!! eale qq ,eqtac))')
def rF2(q, b):
    return entry(q, b)
for b0, bt, blt in (('0', Z, 'lt01S'), ('1', one, 'ltsucid')):
    I0 = '(q, ' + b0 + ')'
    XT, XM = '(nth (q, ' + b0 + ') T)', '(nth (q, ' + b0 + ') M)'
    PAIRQB = Thm(0, pair(NQ, bt, Nm(I0)), '(trud ' + qf_true(to_l6(pair(NQ, bt, Nm(I0))), pair_fact('(a1i eqid)')) + ')')
    HNT = Thm(0, nthF(Nm(I0), NTt, Nm(XT)), '(mpbi (paProvableeq2 bb215NC_inst_exact) bb215NthNumeral_complete)')
    HNM = Thm(0, nthF(Nm(I0), NMt, Nm(XM)), '(mpbi (paProvableeq2 bb215NC_inst_exact) bb215NthNumeral_complete)')
    R2 = rF2(NQ, bt)
    STQ = stored(Nm(XT), Nm(XM))
    Ck = Ctx(3, [STQ, And(And(pair(NQ, bt, v(2)), nthF(v(2), NTt, v(1))), nthF(v(2), NMt, v(0)))])
    hb = Ck.hyp(1)
    ie = mps(Ck, Ck.law(PF, [NQ, bt, v(2), Nm(I0)]), Ck.and_left(Ck.and_left(hb)), Ck.thm(raise0(PAIRQB, 3)))      # i = i0
    nT = Ck.transport(nthF(v(0), NTt, v(2)), ie, Ck.and_right(Ck.and_left(hb)))                                     # Nth(i0, T, v)
    nM = Ck.transport(nthF(v(0), NMt, v(1)), ie, Ck.and_right(hb))                                                  # Nth(i0, M, w)
    veT = mps(Ck, Ck.law(NTH_FUNC, [Nm(I0), NTt, v(1), Nm(XT)]), nT, Ck.thm(raise0(HNT, 3)))                       # v = xT
    veM = mps(Ck, Ck.law(NTH_FUNC, [Nm(I0), NMt, v(0), Nm(XM)]), nM, Ck.thm(raise0(HNM, 3)))                       # w = xM
    s1 = Ck.transport(stored(v(0), Nm(XM)), Ck.sym(veT), Ck.hyp(0))                                               # Stored(v, xM)
    s2 = Ck.transport(stored(v(2), v(0)), Ck.sym(veM), s1)                                                        # Stored(v, w)
    k2 = export(s2)
    k1 = all_intro_hyp(2, STQ, k2); k0a = all_intro_hyp(1, STQ, k1); k0 = all_intro_hyp(0, STQ, k0a)
    need(k0.f == Imp(STQ, R2), 'row K shape')
    # meta: Hpad /\ q < m -> nth (q, b0) T - 1 = tmRename m n (nth (q, b0) M - 1)
    INST = '(syl %s_inst anl)' % P
    REL = '(mpd (iand anr (a1i %s)) %s)' % (blt, INST)
    ROW = MPC(k0.proof, '(syl %s_st %s)' % (P, REL))
    th_(P + '_row' + b0, ' (m n M T q: nat) {qq bb: nat}', '(%s) /\\ q < m -> paProvable 0 %s' % (HPAD, fm(R2)), ROW)

# ---------------------------------------------------------------- the b guard: Hpad /\ q < m -> Prov A. b (Bin(b) -> R(q, b))
R0, R1 = rF2(NQ, Z), rF2(NQ, one)
FBQ = All(Imp(binF(v(0)), rF2(NQ, v(0))))
Cj = Ctx(1, [R0, R1, binF(v(0))])
def j0(Ca): return Ca.transport(rF2(NQ, v(0)), Ca.sym(Ca.hyp(3)), Ca.hyp(0))
def j1(Ca): return Ca.transport(rF2(NQ, v(0)), Ca.sym(Ca.hyp(3)), Ca.hyp(1))
jb = Cj.cases(Cj.hyp(2), j0, j1)
jb = export(export(jb))
Cq = Ctx(1, [R0, R1])
jj = Cq.mp(Cq.mp(Cq.thm(jb), Cq.hyp(0)), Cq.hyp(1))
jg = all_intro_hyp(0, And(R0, R1), jj)
J = export(jg)
need(J.f == Imp(R0, Imp(R1, FBQ)), 'J shape')
th_(P + '_fb', ' (m n M T q: nat) {qq bb: nat}', '(%s) /\\ q < m -> paProvable 0 %s' % (HPAD, fm(FBQ)),
    MPC2(J.proof, P + '_row0', P + '_row1'))

# ---------------------------------------------------------------- the q guard and the rearrangement
FQ = All(Imp(binF(v(0)), rF2(v(1), v(0))))
FQi, SUBEQ = subst_f(0, Nm('i'), FQ)
need(FQi == All(Imp(binF(v(0)), rF2(Nm('i'), v(0)))), 'Subst 0 (num i) FQ')
# Hpad -> A. i (i < m -> Prov FQ[i])
INSTQ = '(!! iald i (exp (syl (bi2 (paProvableeq2 %s)) %s_fb)))' % (SUBEQ, P)
CUTF = Imp(work(v(0)), FQ) if False else Imp(workm(v(0)), FQ)
CUT_D = '(syl (paD0_cut_enum %s) %s)' % (fbound(1, FQ), INSTQ)                 # Hpad -> Prov_1 (Cutoff(m) -> FQ)
need(fm(workm(v(0))) == '(paFormulaEx (paFormulaEqual (paTermAddition (paTermVariable 1) (paTermSuccessor (paTermVariable 0))) (paTermNumeral m)))', 'work = cutoff shape')
# closed internal rearrangement: |- A. (Work(q) -> FQ) -> PAD
GC = All(CUTF)
C0 = Ctx(0, [GC])
def body_q(cl):
    def body_b(cl2):
        c3 = cl2.push(And(workm(v(1)), binF(v(0))))
        fq = c3.mp(allE(c3, c3.hyp(0), v(1)), c3.and_left(c3.hyp(1)))
        rr = c3.mp(allE(c3, fq, v(0)), c3.and_right(c3.hyp(1)))
        return cl2.intro(rr)
    return all_in(cl, body_b)
def all_in(c, fn):
    cl = c.lifted()
    th = fn(cl)
    return all_intro_hyp(c.n, c.G, Thm(cl.n, Imp(lift_f(c.G)[0], th.f[2]), th.proof))
RE = all_in(C0, body_q)
need(RE.f == Imp(GC, PADF()), 'rearrangement shape')
FINAL = '(sylc bb215D2_mp (syl bb215D2_gen %s) (a1i %s))' % (CUT_D, RE.proof)
th_('g7_pad_pa', ' (m n M T: nat) {qq bb: nat}', '(%s) -> paProvable 0 %s' % (HPAD, PADSTMT), FINAL, pub=True)

IMPORTS = ['pa_source_interpretation_formula_eqd_support', 'bb215_internal_bridge_nth_complete', 'bb215_internal_bridge_stepfunc',
           'bb215_provability_delta0_enum', 'g7_pad_graph']
HDR = ('-- GEN7 C5 (generated by tools/gen7/c2/gen_padpa.py): PA proves the padding part of g7PadFullCode at\n'
       '-- numerals whenever the padding relation holds (implication form).')
m0 = ['import "%s.mm0";' % i for i in IMPORTS] + [HDR] + spec
m1 = ['import "%s.mm1";' % i for i in IMPORTS] + ['do { (set-timeout 60000) };', HDR] + proof
for ext_, rows in (('.mm0', m0), ('.mm1', m1)):
    (Path(PAD) / ('g7_pad_pa' + ext_)).write_text('\n\n'.join(rows) + '\n', encoding='utf8', newline='\n')
print('pad module:', sum(len(r) for r in m1), 'bytes')
