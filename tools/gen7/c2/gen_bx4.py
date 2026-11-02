"""Generates pa-mm0/gen7/gen7_bx4.mm1: coded peano5 (induction) of L."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ga
from gb import *   # noqa

HB1 = ('(v0 v1 z0 z1 n: nat) (hp: $ paFormulaBound (suc n) (trPA v1) $) (hx: $ v0 < n $) (hz0: $ z0 < n $) (hz1: $ z1 < n $) '
       '(h0x: $ z0 != v0 $) (h1x: $ z1 != v0 $) (hf0: $ trFr (suc z0) (trPA v1) $) (hf1: $ trFr (suc z1) (trPA v1) $)')
HC1 = 'hp hx hz0 hz1 h0x h1x hf0 hf1'
ga.HB, ga.HCALL = HB1, HC1
out = Out()
out.share('g7x4', HB1, HC1.split())
Facts.PFX[0] = 'g7f_x4'
eng.BOUND_MIN = 2000

reg_fp('v1', 'hp'); reg_zp('v1', 'v0')
fresh_fp('v1', 'z0', 'hf0'); fresh_fp('v1', 'z1', 'hf1')
fresh_zp('v1', 'v0', 'z0'); fresh_zp('v1', 'v0', 'z1')
SYMHYP.update({'v0': 'hx', 'z0': 'hz0', 'z1': 'hz1'})
NE[('z0', 'v0')] = 'h0x'; NE[('z1', 'v0')] = 'h1x'; NE[('v0', 'z1')] = '(necom h1x)'; NE[('v0', 'z0')] = '(necom h0x)'
Zs = zp('v1', 'v0')

def CSB(term, z):
    return ('Al', z, ('Im', ('Eq', ('V', z), term), ('Al', 'v0', ('Im', ('Eq', ('V', 'v0'), ('V', z)), ('zp', 'v1', 'v0')))))
code = ('Im', CSB(('Z0',), 'z0'), ('Im', ('Al', 'v0', ('Im', ('zp', 'v1', 'v0'), CSB(('Suc', ('V', 'v0')), 'z1'))),
                                   ('Al', 'v0', ('zp', 'v1', 'v0'))))
E, pE = T(code)
H0, Hs, ALLB = E[1], E[2][1], E[2][2]

a = All(Imp(Eq(v(0), v(1)), Par(Zs, 2, 0)))
a0, P0p = subst_f(0, Z, a)
ra, QR = rename_f(1, a)
NEXT, QS = subst_f(0, S(v(0)), ra)
IND = Thm(L, Imp(a0, Imp(All(Imp(a, NEXT)), All(a))),
          '(mpbi (paProvableeq2 (paFormulaImpeq %s (paFormulaImpeq (paFormulaAlleq (paFormulaImpeq eqid (eqtr (paFormulaSubsteq3 %s) %s))) eqid))) (bb215L2_ind_axiom %s))'
          % (P0p, QR, QS, fbound(Lv(2), a)))

def last(c, k=0): return c.hyp(len(c.hyps) - 1 - k)

def eq_inst(c, ex, t, p1, p2):
    """c -> ex (an EQ formula Ex(And(_, _))) with witness t."""
    body = ex[1]
    want = subst_f(0, t, body)[0]
    p = c.conj(p1, p2)
    check(p.f[2], want, 'eq_inst')
    return c.witness(body, t, p)

def csb_out(c, h, y, tf2):
    """h: c -> A. (EQ(z, s) -> A. (EQ(x, z) -> B(x))); tf2(c, D2) proves TF(s-graph)(y) from the
    conjunct formula D2 (= TF(s-graph)(w) with w := y). Returns c -> B(y)."""
    r1 = inst_at(c, h, y)
    ex = r1.f[2][1]
    want = subst_f(0, y, ex[1])[0]
    e1 = eq_inst(c, ex, y, tf_self(c, want[1]), tf2(ex[1]))
    a2 = c.mp(r1, e1)
    r2 = inst_at(c, a2, y)
    ex2 = r2.f[2][1]
    want2 = subst_f(0, y, ex2[1])[0]
    e2 = eq_inst(c, ex2, y, tf_self(c, want2[1]), tf_self(c, want2[2]))
    return c.mp(r2, e2)

def core():
    C = Ctx(L, [H0, Hs])
    def b0(cl):                                        # y = v0
        c3 = cl.push(a0[1][1])                         # y = 0
        def tf2(D):
            want2 = subst_f(0, Z, D)[0][2]
            return c3.transport(D[2], c3.sym(last(c3)), tf_self(c3, want2))
        by = csb_out(c3, c3.hyp(0), v(0), tf2)
        check(by.f[2], a0[1][2], 'b0')
        return cl.intro(by)
    A0 = all_in(C, b0)
    check(A0.f[2], a0, 'A0')
    def bs(cl):                                        # x = v0
        c3 = cl.push(a)
        bx = c3.mp(inst_at(c3, c3.hyp(2), v(0)), c3.refl(v(0)))
        R = c3.mp(inst_at(c3, c3.hyp(1), v(0)), bx)
        def withR(c3b):
            def by(cl2):                               # y = v0, x = v1
                c4 = cl2.push(NEXT[1][1])              # y = S x
                def tf2(D):
                    want2 = subst_f(0, S(v(1)), D)[0][2]
                    return c4.transport(D[2], c4.sym(last(c4)), tf_gs_var(c4, want2))
                r = csb_out(c4, c4.hyp(3), v(0), tf2)
                return cl2.intro(r)
            return all_in(c3b, by)
        return cl.intro(cut(c3, R, withR))
    AS = all_in(C, bs)
    allA = C.mp(C.mp(C.thm(IND), A0), AS)
    def fin(C2):
        def bl(cl):
            ax = inst_at(cl, cl.hyp(2), v(0))
            return cl.mp(inst_at(cl, ax, v(0)), cl.refl(v(0)))
        return all_in(C2, bl)
    th = cut(C, allA, fin)
    th = export(th)
    check(th.f, E, 'peano5 core')
    return th

out.thm('g7_p5_conv ' + HB1, 'trPA %s = %s' % (code_str(code), fm(E)), pE, pub=True)
out.lemma('g7_p5_core', core(), pub=True, binders=' ' + HB1)
# code = cIm CSB0 (cIm (cAl v0 (cIm v1 CSBS)) (cAl v0 v1))
F0 = 'nfr_fresh'
H = ' '.join([
    '(g7_trb_lt (lttr cArg2_lt (lttr cArg2_lt cArg2_lt)))',
    '(lttr cArg1_lt (lttr cArg2_lt cArg2_lt))',
    '(lttr cArg1_lt cArg1_lt)',
    '(lttr cArg1_lt (lttr cArg2_lt (lttr cArg2_lt (lttr cArg1_lt cArg2_lt))))',
    '(nfr_Vinv (nfr_tl (nfr_tr %s)))' % F0, '(nfr_Vinv (nfr_tl (nfr_tr %s)))' % F0,
    '(g7_nfr_fresh (nfr_tr (nfr_tr %s)))' % F0, '(g7_nfr_fresh (nfr_tr (nfr_tr %s)))' % F0])
out.raw('''pub theorem peano5_R (v0: nat) (v1: nat): $ cPr (cIm (csb c0 v0 v1) (cIm (cAl v0 (cIm v1 (csb (cSuc (cV v0)) v0 v1))) (cAl v0 v1))) $ =
(named '(bi2 (g7_cpr_iff g7_tr_bound) (mpbir (paProvableeq2 (g7_p5_conv %s)) (g7_p5_core %s))));
''' % (H, H))

hdr = '''import "gen7_bx3.mm1";

import "gen7_sl.mm1";

-- G7 C2 (generated by tools/gen7/c2/gen_bx4.py): coded peano5.
'''
out.write(os.path.join(PA, 'gen7', 'gen7_bx4.mm1'), hdr)
print('ok')
