"""Generates pa-mm0/gen7/gen7_ax4.mm1: coded peano1, peano2 (successor axioms) of L."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ga import *   # noqa

out = Out()
out.share('g7a4', HB, ['h' + x for x in NAMES])

def conv_trFun(pY, G):
    """pY: Y = fm G. Proof of paAxiomRaiseParameters (trFun Y) = fm(raise_ TFg G)."""
    r1, q1 = rename_f(1, G)
    R1 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (pY, q1)
    r2, q2 = rename_f(1, r1)
    R2 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (R1, q2)
    TFeq = '(paFormulaOreq (paFormulaAlleq (trIffeq %s eqid)) (paFormulaAndeq (trNoteq (paFormulaExeq (paFormulaAlleq (trIffeq %s eqid)))) eqid))' % (R1, R2)
    rt, q3 = rename_f(1, TFg(G))
    return '(eqtr (paFormulaRenameeq3 %s) %s)' % (TFeq, q3)

def conv_EQ(pY, G, pZ, H):
    return '(paFormulaExeq (paFormulaAndeq %s %s))' % (conv_trFun(pY, G), conv_trFun(pZ, H))

P_SUC = {k: '(paFormulaExeq (paFormulaAndeq (g7_raiseTF_E h%s) eqid))' % k for k in NAMES}   # trSucF k = fm GS(P0 k)
P_PAR = {k: '(g7_par_id h%s)' % k for k in NAMES}                                           # k = fm P0 k

def HAX(*lts):
    hs = ['(g7_trb_lt %s)' % lt for lt in lts]
    while len(hs) < 4: hs.append(hs[0])
    return ' '.join(hs)

# ---- peano1: ~ (S a = 0) ----
SA = ('S', ('A',)); SB = ('S', ('B',))
def p1_core():
    fx = Facts(out); fx.need(SA); fx.need(('Z',))
    e = EQg(build(SA), GZ)
    C = fx.ctx([e])
    def fn(c2):
        t = c2.hyp(len(c2.hyps) - 1)
        g1v = tf_out(c2, fx, SA, c2.and_left(t))
        g0v = tf_out(c2, fx, ('Z',), c2.and_right(t))
        def body(c3):
            def f5(c4):
                last = c4.hyp(len(c4.hyps) - 1)
                s = c4.trans(c4.sym(c4.and_right(last)), c4.hyp(len(c4.hyps) - 2))
                return c4.mp(c4.thm(succ_nonzero_t(c4.n, v(0))), s)
            g1 = syl(and_left_ax(c3.n, c2.G, g0v.f[2]), g1v)
            return c3.exists(g1, F, f5)
        return cut(c2, g0v, body)
    th = C.exists(C.hyp(len(C.hyps) - 1), F, fn)
    return fx.discharge(th, 1)

out.lemma('g7_p1_core', p1_core(), pub=True, binders=' ' + HB)
out.thm('g7_p1_conv ' + HB, 'trEqF (trSucF A) trZeroF = %s' % fm(EQg(build(SA), GZ)), conv_EQ(P_SUC['A'], build(SA), 'eqid', GZ), pub=True)
LT_P1 = '(lttr (lttr cArg1_lt cArg1_lt) cArg1_lt)'
out.raw('''pub theorem peano1_R (v0: nat): $ cPr (cne (cSuc v0) c0) $ =
(named '(bi2 (g7_cpr_iff g7_tr_bound) (mpbir (paProvableeq2 (eqtr trPA_cNot (trNoteq (eqtr g7_tJ_cEq (eqtr trPA_cEq
  (eqtr (trEqFeq trPA_cSuc trPA_c0) (g7_p1_conv %s)))))))
  (g7_p1_core %s))));
''' % (HAX(LT_P1), HAX(LT_P1)))

# ---- peano2: S a = S b <-> a = b, coded as ~((P -> Q) -> ~(Q -> P)) ----
def p2_dirs():
    fx = Facts(out); fx.need(SA); fx.need(SB); fx.need(('A',)); fx.need(('B',))
    P = EQg(build(SA), build(SB)); Q = EQ('A', 'B')
    C = fx.ctx([P])
    def fa(c2):
        t = c2.hyp(len(c2.hyps) - 1)
        ga = tf_out(c2, fx, SA, c2.and_left(t))
        gb = tf_out(c2, fx, SB, c2.and_right(t))
        def withgb(c3):
            ga3 = syl(and_left_ax(c3.n, c2.G, gb.f[2]), ga)
            def fu(c4):
                def fw(c5):
                    hu = c5.hyp(len(c5.hyps) - 2); hw = c5.hyp(len(c5.hyps) - 1)
                    su_sw = c5.trans(c5.sym(c5.and_right(hu)), c5.and_right(hw))
                    uw = c5.app(succ_inj_t(c5.n, v(1), v(0)), su_sw)
                    tb = c5.and_left(hw)
                    tbu = c5.transport(raise_(tb.f[2]), c5.sym(uw), tb)
                    goal5 = lift(lift(lift(Q)))
                    return c5.witness(goal5[1], v(1), c5.conj(c5.and_left(hu), tbu))
                return c4.exists(c4.hyp(len(c4.hyps) - 2), lift(lift(Q)), fw)
            return c3.exists(ga3, lift(Q), fu)
        return cut(c2, gb, withgb)
    pq = fx.discharge(C.exists(C.hyp(len(C.hyps) - 1), Q, fa), 1)
    C = fx.ctx([Q])
    def fb(c2):
        def fv(c3):
            tt = c3.hyp(len(c3.hyps) - 2); ev = c3.hyp(len(c3.hyps) - 1)
            def gs_at(G, h_tf):
                bodyv = g_at(G, int(c3.n) - 1, v(0))
                return c3.witness(bodyv[1], v(1), c3.conj(h_tf, ev))
            ta = tf_in(c3, fx, SA, gs_at(build(SA), c3.and_left(tt)))
            tb = tf_in(c3, fx, SB, gs_at(build(SB), c3.and_right(tt)))
            return c3.witness(lift(lift(P))[1], v(0), c3.conj(ta, tb))
        return c2.exists(name_term(c2, S(v(0))), lift(P), fv)
    qp = fx.discharge(C.exists(C.hyp(len(C.hyps) - 1), P, fb), 1)
    return pq, qp

pq, qp = p2_dirs()
out.lemma('g7_p2_pq', pq, binders=' ' + HB); pq = Thm(L, pq.f, '(g7_p2_pq %s)' % HCALL)
out.lemma('g7_p2_qp', qp, binders=' ' + HB); qp = Thm(L, qp.f, '(g7_p2_qp %s)' % HCALL)
P = EQg(build(SA), build(SB)); Q = EQ('A', 'B')
C = Ctx(L, [Imp(Imp(P, Q), Not(Imp(Q, P)))])
f = C.mp(C.mp(C.hyp(0), C.thm(pq)), C.thm(qp))
out.lemma('g7_p2_core', f, pub=True, binders=' ' + HB)
out.thm('g7_p2_convP ' + HB, 'trEqF (trSucF A) (trSucF B) = %s' % fm(P), conv_EQ(P_SUC['A'], build(SA), P_SUC['B'], build(SB)), pub=True)
out.thm('g7_p2_convQ ' + HB, 'trEqF A B = %s' % fm(Q), '(g7_EQ_E hA hB)', pub=True)

LTA = '(lttr (lttr cArg1_lt cArg1_lt) (lttr cArg1_lt (lttr cArg1_lt cArg1_lt)))'
out.raw('''theorem g7_tJ_cNot2 (a: nat): $ trJ (trPA (cNot a)) = trPA (cNot a) $ = (named '(g7_J_id g7_fr0_cNot));
''')
LTa = '(lttr cArg1_lt (lttr cArg2_lt (lttr cArg1_lt cArg1_lt)))'
LTb = '(lttr cArg2_lt (lttr cArg2_lt (lttr cArg1_lt cArg1_lt)))'
H2 = HAX(LTa, LTb)
EX = '(eqtr g7_tJ_cEq (eqtr trPA_cEq (eqtr (trEqFeq trPA_cSuc trPA_cSuc) (g7_p2_convP %s))))' % H2
EY = '(eqtr g7_tJ_cEq (eqtr trPA_cEq (g7_p2_convQ %s)))' % H2
IXY = '(eqtr g7_tJ_cIm (eqtr trPA_cIm (paFormulaImpeq %s %s)))' % (EX, EY)
IYX = '(eqtr g7_tJ_cIm (eqtr trPA_cIm (paFormulaImpeq %s %s)))' % (EY, EX)
NYX = '(eqtr g7_tJ_cNot2 (eqtr trPA_cNot (trNoteq %s)))' % IYX
TOP = '(eqtr trPA_cNot (trNoteq (eqtr g7_tJ_cIm (eqtr trPA_cIm (paFormulaImpeq %s %s)))))' % (IXY, NYX)
out.raw('''pub theorem peano2_R (v0: nat) (v1: nat): $ cPr (ciff (cEq (cSuc v0) (cSuc v1)) (cEq v0 v1)) $ =
(named '(bi2 (g7_cpr_iff g7_tr_bound) (mpbir (paProvableeq2 %s) (g7_p2_core %s))));
''' % (TOP, H2))

hdr = '''import "gen7_tg.mm1";

import "gen7_ax3.mm1";

-- G7 C2 (generated by tools/gen7/c2/gen_ax4.py): coded peano1, peano2.

@_ def cne (v0: nat) (v1: nat): nat = $ cNot (cEq v0 v1) $;

@_ def can (v0: nat) (v1: nat): nat = $ cNot (cIm v0 (cNot v1)) $;

@_ def ciff (v0: nat) (v1: nat): nat = $ can (cIm v0 v1) (cIm v1 v0) $;
'''
out.write(os.path.join(PA, 'gen7', 'gen7_ax4.mm1'), hdr)
print('ok')
