"""Generates pa-mm0/gen7/gen7_bx5.mm1: coded theid (the value of a singleton class) of L."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ga
from gb import *   # noqa

TC = '(cAb v0 (cEq (cV v0) v2))'
HB1 = ('(v0 v1 v2 w n: nat) (hS: $ paFormulaBound (suc n) (trPA v1) $) (hB: $ paFormulaBound (suc n) (trPA v2) $) '
       '(hT: $ paFormulaBound (suc n) (trPA %s) $) (hx: $ v0 < n $) (hw: $ w < n $) (hfB: $ trFr (suc v0) (trPA v2) $) '
       '(hfS: $ trFr (suc w) (trPA v1) $) (hfT: $ trFr (suc w) (trPA %s) $)' % (TC, TC))
HC1 = 'hS hB hT hx hw hfB hfS hfT'
ga.HB, ga.HCALL = HB1, HC1
out = Out()
out.share('g7x5', HB1, HC1.split())
Facts.PFX[0] = 'g7f_x5'
eng.BOUND_MIN = 2000

reg_tp('v1', 'hS'); reg_tp('v2', 'hB'); reg_tp(TC, 'hT')
fresh_tp('v2', 'v0', 'hfB'); fresh_tp('v1', 'w', 'hfS'); fresh_tp(TC, 'w', 'hfT')
SYMHYP.update({'v0': 'hx', 'w': 'hw'})
Sv, Bv, Tv = tp('v1'), tp('v2'), tp(TC)

def IFF(a, b): return ('Not', ('Im', ('Im', a, b), ('Not', ('Im', b, a))))
code = ('Im', ('Al', 'w', IFF(('El', ('V', 'w'), ('tp', 'v1')), ('El', ('V', 'w'), ('tp', TC)))),
        ('Eq', ('The', ('tp', 'v1')), ('tp', 'v2')))
E, pE = T(code)
HYP, GOAL = E[1], E[2]
ET, pT = T(('Ab', 'v0', ('Eq', ('V', 'v0'), ('tp', 'v2'))))   # trPA TC = fm ET

_lc = {}
def liftn_thm(th, k):
    key = (th.proof, k)
    if key in _lc: return _lc[key]
    if k == 0: r = th
    else:
        prev = liftn_thm(th, k - 1)
        f2, p = rename_f(0, prev.f)
        r = Thm(prev.n + 1, f2, '(mpbi (paProvableeq2 %s) (g7_lift_rule %s))' % (p, prev.proof))
    _lc[key] = r
    return r
def at(c, th): return c.thm(liftn_thm(th, int(c.n) - 1))
def last(c, k=0): return c.hyp(len(c.hyps) - 1 - k)

TOTB = Thm(L, Tot(Bv), '(g7_tf_total hB)')
FUNB = Thm(L, Fun(Bv), '(g7_tf_fun hB)')
FUNS = Thm(L, Fun(Sv), '(g7_tf_fun hS)')
GS_ = TF(Sv)                                   # the graph of cThe v1
Q1S = inst_lemma('(g7_tf_q1 %s)' % fbound(L, GS_), Q1X, 'X', GS_)

def expand(c, h):
    """h: c -> Par(TT, j, s): returns c -> (ET at j, s)."""
    f = h.f[2]
    need(f[0] == 'par' and f[1] == Tv, 'expand')
    g2, p = par_conv(ET, f[2], f[3])
    return Thm(c.n, Imp(c.G, g2), '(mpbi (paProvableeq2 (paFormulaImpeq2 (eqtr (paFormulaRenameeq3 %s) %s))) %s)' % (pT, p, h.proof))

def fold(c, h, target):
    """h: c -> (ET at j, s) with target Par(TT, j, s); returns c -> target."""
    g2, p = par_conv(ET, target[2], target[3])
    check(g2, h.f[2], 'fold')
    return Thm(c.n, Imp(c.G, target), '(mpbir (paProvableeq2 (paFormulaImpeq2 (eqtr (paFormulaRenameeq3 %s) %s))) %s)' % (pT, p, h.proof))

def ciff_parts(c, h):
    """h: c -> ~((X -> Y) -> ~(Y -> X)); returns (c -> (X -> Y), c -> (Y -> X)) (classically)."""
    f = h.f[2]
    XY, NYX = f[1][1], f[1][2]
    YX = NYX[1]
    def get(target):
        em = c.lem(target)
        def ya(ca): return ca.hyp(len(ca.hyps) - 1)
        def no(cb):
            c2 = cb.push(XY)
            if target == XY:
                inner = c2.absurd(c2.mp(c2.hyp(len(c2.hyps) - 2), c2.hyp(len(c2.hyps) - 1)), NYX)
            else:
                inner = c2.hyp(len(c2.hyps) - 2)
            imp = cb.intro(inner)
            hb = syl(and_left_ax(cb.n, c.G, Not(target)), h)
            return cb.absurd(cb.mp(hb, imp), target)
        return c.cases(em, ya, no)
    return get(XY), get(YX)

def core():
    C = Ctx(L, [HYP])
    def f2(c2):                                    # v = v0
        tfb = c2.hyp(1)
        q1 = inst_at(c2, at(c2, Q1S), v(0))
        gv_t = q1.f[2][1][1]                       # TF S (v)
        alls_t = gv_t[1]                           # A. (S(u) <-> u = v)
        def bu(cl):                                # u = v0, v = v1
            iff = alls_t[1]
            hw = inst_at(cl, cl.hyp(0), v(0))
            xy, yx = ciff_parts(cl, hw)
            ElS, ElT = xy.f[2][1], xy.f[2][2]
            # S(u) -> u = v
            c3 = cl.push(iff[1][1])
            want = subst_f(0, v(0), ElS[1])[0]
            els = c3.witness(ElS[1], v(0), c3.conj(tf_self(c3, want[1]), last(c3)))
            elt = c3.mp(syl(and_left_ax(c3.n, cl.G, iff[1][1]), xy), els)
            def g4(c4):                            # u' = v0
                hh = last(c4)
                e1 = tf_var_out(c4, c4.and_left(hh))           # u' = u
                et = expand(c4, c4.and_right(hh))
                def g5(c5):                        # v' = v0
                    h5 = last(c5)
                    e2 = tf_var_out(c5, c5.and_left(h5))       # v' = u'
                    fb = fun_eq(c5, at(c5, FUNB), c5.and_right(h5), c5.hyp(1))  # v' = v
                    e1l = tf_var_out(c5, c5.and_left(c5.hyp(len(c5.hyps) - 2)))
                    return c5.trans(c5.trans(c5.sym(e1l), c5.sym(e2)), fb)
                return c4.exists(et, lift(iff[1][2]), g5)
            r1 = cl.intro(c3.exists(elt, iff[1][2], g4))
            # u = v -> S(u)
            c6 = cl.push(iff[2][1])
            body = ElT[1]
            want = subst_f(0, v(0), body)[0]
            tgtT = want[2]
            etw = par_conv(ET, tgtT[2], tgtT[3])[0]
            wv = subst_f(0, v(0), etw[1])[0]
            hole = etw[1][2]
            tb_u = c6.transport(hole, c6.sym(last(c6)), c6.hyp(1))
            ew = c6.witness(etw[1], v(0), c6.conj(tf_self(c6, wv[1]), tb_u))
            tt = fold(c6, ew, tgtT)
            elt2 = c6.witness(body, v(0), c6.conj(tf_self(c6, want[1]), tt))
            els2 = c6.mp(syl(and_left_ax(c6.n, cl.G, iff[2][1]), yx), elt2)
            def g7(c7):
                hh = last(c7)
                e = tf_var_out(c7, c7.and_left(hh))            # u' = u
                return eqsub(c7, e, c7.and_right(hh), lift(iff[2][2]))
            r2 = cl.intro(c6.exists(els2, iff[2][2], g7))
            return cl.conj(r1, r2)
        alls = all_in(c2, bu)
        check(alls.f[2], alls_t, 'alls')
        gv = c2.app(or_left_ax(c2.n, alls_t, gv_t[2]), alls)
        def withgv(c3):
            uq_t = q1.f[2][1][2]
            def bq(cl):
                c4 = cl.push(uq_t[1][1])
                return cl.intro(fun_eq(c4, at(c4, FUNS), last(c4), c4.hyp(2)))
            uq = all_in(c3, bq)
            tfv = c3.mp(syl(and_left_ax(c3.n, c2.G, gv.f[2]), q1), c3.conj(c3.hyp(2), uq))
            body = lift(GOAL)[1]
            want = subst_f(0, v(0), body)[0]
            return c3.witness(body, v(0), c3.conj(tfv, c3.hyp(1)))
        return cut(c2, gv, withgv)
    th = C.exists(C.thm(TOTB), GOAL, f2)
    check(th.f, E, 'theid core')
    return th

out.thm('g7_theid_conv ' + HB1, 'trPA %s = %s' % (code_str(code).replace('(cAl w ', '(cAl w '), fm(E)), pE, pub=True)
out.lemma('g7_theid_core', core(), pub=True, binders=' ' + HB1)
TCL = 'cArg2_lt (lttr cArg2_lt (lttr cArg1_lt (lttr cArg1_lt (lttr cArg2_lt cArg1_lt))))'
H = ' '.join([
    '(g7_trb_lt (lttr cArg1_lt (lttr cArg1_lt cArg2_lt)))',
    '(g7_trb_lt (lttr cArg2_lt cArg2_lt))',
    '(g7_trb_lt (lttr %s))' % TCL,
    '(lttr cArg1_lt (lttr %s))' % TCL,
    '(lttr cArg1_lt cArg1_lt)',
    '(g7_nfr_fresh h0)', '(g7_nfr_fresh (nfr_tl nfr_fresh))', '(g7_nfr_fresh (nfr_tr nfr_fresh))'])
out.raw('''def ceqs (v0: nat) (v1: nat): nat = $ cAl (nfresh (ctup v0 v1)) (ciff (cEl (cV (nfresh (ctup v0 v1))) v0) (cEl (cV (nfresh (ctup v0 v1))) v1)) $;
''')
out.raw('''pub theorem theid_R (v0: nat) (v1: nat) (v2: nat) (h0: $ nfr v0 v2 $): $ cPr (cIm (ceqs v1 (cAb v0 (cEq (cV v0) v2))) (cEq (cThe v1) v2)) $ =
(named '(bi2 (g7_cpr_iff g7_tr_bound) (mpbir (paProvableeq2 (g7_theid_conv %s)) (g7_theid_core %s))));
''' % (H, H))

hdr = '''import "gen7_bx4.mm1";

-- G7 C2 (generated by tools/gen7/c2/gen_bx5.py): coded theid.
'''
out.write(os.path.join(PA, 'gen7', 'gen7_bx5.mm1'), hdr)
print('ok')
