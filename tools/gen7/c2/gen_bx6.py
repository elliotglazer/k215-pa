"""Generates pa-mm0/gen7/gen7_bx6.mm1: coded the0 (no singleton: value 0) of L."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ga
from gb import *   # noqa

HB1 = ('(v0 v1 v2 w n: nat) (hS: $ paFormulaBound (suc n) (trPA v2) $) (hx: $ v0 < n $) (hy: $ v1 < n $) (hw: $ w < n $) '
       '(hxy: $ v0 != v1 $) (hwy: $ w != v1 $) (hfSy: $ trFr (suc v1) (trPA v2) $) (hfSw: $ trFr (suc w) (trPA v2) $)')
HC1 = 'hS hx hy hw hxy hwy hfSy hfSw'
ga.HB, ga.HCALL = HB1, HC1
out = Out()
out.share('g7x6', HB1, HC1.split())
Facts.PFX[0] = 'g7f_x6'
eng.BOUND_MIN = 2000

reg_tp('v2', 'hS'); fresh_tp('v2', 'v1', 'hfSy'); fresh_tp('v2', 'w', 'hfSw')
SYMHYP.update({'v0': 'hx', 'v1': 'hy', 'w': 'hw'})
NE[('v1', 'v0')] = '(necom hxy)'; NE[('v1', 'w')] = '(necom hwy)'
Sv = tp('v2')

def IFF(a, b): return ('Not', ('Im', ('Im', a, b), ('Not', ('Im', b, a))))
Tc = ('Ab', 'v0', ('Eq', ('V', 'v0'), ('V', 'v1')))
CEQS = ('Al', 'w', IFF(('El', ('V', 'w'), ('tp', 'v2')), ('El', ('V', 'w'), Tc)))
CEX = ('Not', ('Al', 'v1', ('Not', CEQS)))
code = ('Im', ('Not', CEX), ('Eq', ('The', ('tp', 'v2')), ('Z0',)))
E, pE = T(code)
HYP, GOAL = E[1], E[2]

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
def up(c, prev, th):
    """th: prev -> X, c = prev pushed with more hyps; returns c -> X."""
    k = len(c.hyps) - len(prev.hyps)
    for i in range(k):
        cc = Ctx(c.n, c.hyps[:len(prev.hyps) + i + 1])
        pc = Ctx(c.n, c.hyps[:len(prev.hyps) + i])
        th = syl(and_left_ax(c.n, pc.G, cc.hyps[-1]), th)
    return th

FUNS = Thm(L, Fun(Sv), '(g7_tf_fun hS)')
GS_ = TF(Sv)
Q1S = inst_lemma('(g7_tf_q1 %s)' % fbound(L, GS_), Q1X, 'X', GS_)

def wit(c, ex, t, p1, p2):
    body = ex[1]
    want = subst_f(0, t, body)[0]
    p = c.conj(p1, p2)
    check(p.f[2], want, 'wit')
    return c.witness(body, t, p)

def tf_at(c, ex_body_conj, t):
    """c -> TFg(Eq(v0, t))(t) given the target formula."""
    return tf_self(c, ex_body_conj)

def core():
    C = Ctx(L, [HYP])
    q1 = inst_at(C, at(C, Q1S), Z)
    gz_t = q1.f[2][1][1]
    nex_t = gz_t[2][1]
    ex_t = nex_t[1]
    c2 = C.push(ex_t)
    def f3(c3):                                        # v' = v0; alls = c3.hyp(2)
        cexf = lift(HYP[1])                            # CEX at c3
        c4 = c3.push(cexf[1])                          # A. ~CEQS
        nq = inst_at(c4, c4.hyp(3), v(0))              # ~CEQS(v')
        ceqs_t = nq.f[2][1]
        def bw(cl):                                    # w = v0, v' = v1
            iff_t = ceqs_t[1]
            XY = iff_t[1][1]
            A_, B_ = XY[1], XY[2]
            # A -> B
            c6 = cl.push(A_)
            def g7(c7):                                # u' = v0, w = v1, v' = v2
                h = last(c7)
                e = tf_var_out(c7, c7.and_left(h))                     # u' = w
                ins = inst_at(c7, c7.hyp(2), v(0))
                uv = c7.mp(c7.and_left(ins), c7.and_right(h))          # u' = v'
                wv = c7.trans(c7.sym(e), uv)                           # w = v'
                tgt = liftn(B_, 1)                                     # ElT(w)
                want = subst_f(0, v(1), tgt[1])[0]
                Tw = want[2]                                           # T(w) = Ex(...)
                wantT = subst_f(0, v(1), Tw[1])[0]
                hole = Tw[1][2]
                tvp = tf_self(c7, subst_f(0, v(2), hole)[0])
                tvw = c7.transport(hole, c7.sym(wv), tvp)
                pT = wit(c7, Tw, v(1), tf_self(c7, wantT[1]), tvw)
                return wit(c7, tgt, v(1), tf_self(c7, want[1]), pT)
            ab = cl.intro(c6.exists(last(c6), B_, g7))
            # B -> A
            c6 = cl.push(B_)
            def g8(c7):                                # u' = v0, w = v1, v' = v2
                h = last(c7)
                e1 = tf_var_out(c7, c7.and_left(h))                    # u' = w
                def g9(c8):                            # v'' = v0, u' v1, w v2, v' v3
                    h2 = last(c8)
                    e2 = tf_var_out(c8, c8.and_left(h2))               # v'' = u'
                    e3 = tf_var_out(c8, c8.and_right(h2))              # v'' = v'
                    e1l = tf_var_out(c8, c8.and_left(last(c8, 1)))      # u' = w
                    wv = c8.trans(c8.trans(c8.sym(e1l), c8.sym(e2)), e3)   # w = v'
                    ins = inst_at(c8, c8.hyp(2), v(2))
                    sw = c8.mp(c8.and_right(ins), wv)
                    tgt = liftn(A_, 2)
                    want = subst_f(0, v(2), tgt[1])[0]
                    return wit(c8, tgt, v(2), tf_self(c8, want[1]), sw)
                return c7.exists(c7.and_right(h), lift(A_), g9)
            ba = cl.intro(c6.exists(last(c6), A_, g8))
            c9 = cl.push(iff_t[1])
            f = c9.mp(c9.mp(last(c9), up(c9, cl, ab)), up(c9, cl, ba))
            return cl.intro(f)
        ceqs = all_in(c4, bw)
        ff = c4.mp(nq, ceqs)
        cex = c3.intro(ff)
        return c3.mp(c3.hyp(0), cex)
    nex = C.intro(c2.exists(last(c2), F, f3))
    gz = C.app(or_right_ax(C.n, gz_t[1], gz_t[2]), C.conj(nex, C.refl(Z)))
    def withgz(C2):
        uq_t = q1.f[2][1][2]
        def bq(cl):
            c4 = cl.push(uq_t[1][1])
            ins = inst2(c4, at(c4, FUNS), v(0), Z)
            return cl.intro(c4.mp(c4.mp(ins, last(c4)), c4.hyp(1)))
        uq = all_in(C2, bq)
        tfz = C2.mp(up(C2, C, q1), C2.conj(C2.hyp(1), uq))
        body = GOAL[1]
        want = subst_f(0, Z, body)[0]
        return C2.witness(body, Z, C2.conj(tfz, tf_self(C2, want[2])))
    th = cut(C, gz, withgz)
    check(th.f, E, 'the0 core')
    return th

out.raw('''theorem g7_ne_aux (x y w: nat): $ w = y -> w = x -> x = y $ = (named '(exp (eqtr3d anr anl)));
theorem g7_ne_wy (x y w: nat): $ nne x y -> nfr w (cAb x (cEq (cV x) (cV y))) -> nne w y $ =
(named '(con3d (exp (mpbird (a1i occ_cAb) (iand (mpd anl (syl (con3d g7_ne_aux) anr))
  (mpbird (a1i occ_cEq) (syl orr (mpbird (a1i occ_cV) anr))))))));
''')
out.thm('g7_the0_conv ' + HB1, 'trPA %s = %s' % (code_str(code), fm(E)), pE, pub=True)
out.lemma('g7_the0_core', core(), pub=True, binders=' ' + HB1)
PCEQS = 'cArg1_lt (lttr cArg2_lt (lttr cArg1_lt (lttr cArg1_lt cArg1_lt)))'
PT = 'cArg2_lt (lttr cArg2_lt (lttr cArg1_lt (lttr cArg1_lt (lttr cArg2_lt (lttr %s)))))' % PCEQS
H = ' '.join([
    '(g7_trb_lt (lttr cArg1_lt (lttr cArg1_lt cArg2_lt)))',
    '(lttr cArg1_lt (lttr %s))' % PT,
    '(lttr cArg1_lt (lttr cArg1_lt (lttr cArg1_lt cArg1_lt)))',
    '(lttr cArg1_lt (lttr %s))' % PCEQS,
    'h0', '(g7_ne_wy h0 (nfr_tr nfr_fresh))', '(g7_nfr_fresh h1)', '(g7_nfr_fresh (nfr_tl nfr_fresh))'])
out.raw('''pub theorem the0_R (v0: nat) (v1: nat) (v2: nat) (h0: $ nne v0 v1 $) (h1: $ nfr v1 v2 $): $ cPr (cIm (cNot (cex v1 (ceqs v2 (cAb v0 (cEq (cV v0) (cV v1)))))) (cEq (cThe v2) c0)) $ =
(named '(bi2 (g7_cpr_iff g7_tr_bound) (mpbir (paProvableeq2 (g7_the0_conv %s)) (g7_the0_core %s))));
''' % (H, H))

hdr = '''import "gen7_bx5.mm1";

-- G7 C2 (generated by tools/gen7/c2/gen_bx6.py): coded the0.
'''
out.write(os.path.join(PA, 'gen7', 'gen7_bx6.mm1'), hdr)
print('ok')
