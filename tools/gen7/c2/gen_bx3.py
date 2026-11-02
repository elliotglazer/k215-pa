"""Generates pa-mm0/gen7/gen7_bx3.mm1: coded elab (class membership is substitution) of L."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ga
from gb import *   # noqa

HB1 = ('(v0 v1 v2 z n: nat) (hA: $ paFormulaBound (suc n) (trPA v0) $) (hp: $ paFormulaBound (suc n) (trPA v2) $) '
       '(hx: $ v1 < n $) (hz: $ z < n $) (hzx: $ z != v1 $) (hfA: $ trFr (suc z) (trPA v0) $) (hfp: $ trFr (suc z) (trPA v2) $)')
HC1 = 'hA hp hx hz hzx hfA hfp'
ga.HB, ga.HCALL = HB1, HC1
out = Out()
out.share('g7x3', HB1, HC1.split())
Facts.PFX[0] = 'g7f_x3'
eng.BOUND_MIN = 2000

reg_tp('v0', 'hA'); fresh_tp('v0', 'z', 'hfA')
reg_fp('v2', 'hp'); reg_zp('v2', 'v1'); fresh_fp('v2', 'z', 'hfp'); fresh_zp('v2', 'v1', 'z')
SYMHYP['v1'] = 'hx'; SYMHYP['z'] = 'hz'
NE[('z', 'v1')] = 'hzx'
Av = tp('v0')

def IFF(a, b): return ('Not', ('Im', ('Im', a, b), ('Not', ('Im', b, a))))
LHc = ('El', ('tp', 'v0'), ('Ab', 'v1', ('zp', 'v2', 'v1')))
RHc = ('Al', 'z', ('Im', ('Eq', ('V', 'z'), ('tp', 'v0')), ('Al', 'v1', ('Im', ('Eq', ('V', 'v1'), ('V', 'z')), ('zp', 'v2', 'v1')))))
code = IFF(LHc, RHc)
E, pE = T(code)
P_ = E[1][1][1]; Q_ = E[1][1][2]
check(E, Not(Imp(Imp(P_, Q_), Not(Imp(Q_, P_)))), 'elab shape')

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

FUN = Thm(L, Fun(Av), '(g7_tf_fun hA)')
TOT = Thm(L, Tot(Av), '(g7_tf_total hA)')
def fun_at(c): return c.thm(liftn_thm(FUN, int(c.n) - 1))
def last(c, k=0): return c.hyp(len(c.hyps) - 1 - k)

def wit(c, ex, t, *parts):
    """c -> ex (= Ex body) with witness t; parts prove the conjuncts of body[t] (a single proof if not a conjunction)."""
    body = ex[1]
    want = subst_f(0, t, body)[0]
    p = parts[0] if len(parts) == 1 else c.conj(parts[0], parts[1])
    check(p.f[2], want, 'wit')
    return c.witness(body, t, p)

def pq():
    C = Ctx(L, [P_])
    def f2(c2):                                    # u = v0
        def bz(cl):                                # z = v0, u = v1
            tz = lift(Q_)[1]
            c3 = cl.push(tz[1])
            def bx(cl2):                           # x = v0, z = v1, u = v2
                tx = tz[2][1]
                c4 = cl2.push(tx[1])
                def f5(c5):                        # w = v0, x v1, z v2, u v3
                    hw = last(c5)
                    wz = tf_var_out(c5, c5.and_left(hw))              # w = z
                    hu = c5.hyp(1)
                    uw = fun_eq(c5, fun_at(c5), c5.and_left(hu), c5.and_right(hw))   # u = w
                    def f6(c6):                    # w' = v0, w v1, x v2, z v3, u v4
                        hw2 = last(c6)
                        e1 = tf_var_out(c6, c6.and_left(hw2))         # w' = x
                        e2 = tf_var_out(c6, c6.and_right(hw2))        # w' = z
                        wz6 = tf_var_out(c6, c6.and_left(c6.hyp(len(c6.hyps) - 2)))
                        uw6 = fun_eq(c6, fun_at(c6), c6.and_left(c6.hyp(1)), c6.and_right(c6.hyp(len(c6.hyps) - 2)))
                        ux = c6.trans(c6.trans(uw6, wz6), c6.trans(c6.sym(e2), e1))
                        zu = c6.and_right(c6.hyp(1))
                        return eqsub(c6, ux, zu, liftn(tx[2], 2))
                    return c5.exists(c5.hyp(len(c5.hyps) - 2), lift(tx[2]), f6)
                r = c4.exists(last(c4, 1) if False else c4.hyp(2), tx[2], f5)
                return cl2.intro(r)
            r = all_in(c3, bx)
            return cl.intro(r)
        return all_in(c2, bz)
    th = C.exists(C.hyp(0), Q_, f2)
    return export(th) if False else th

def qp():
    C = Ctx(L, [Q_])
    def f2(c2):                                    # u = v0
        tu = c2.hyp(1)
        r1 = inst_at(c2, c2.hyp(0), v(0))          # EQ(u, A) -> A. (EQ(x, u) -> Z(x))
        e1 = wit(c2, r1.f[2][1], v(0), tf_self(c2, subst_f(0, v(0), r1.f[2][1][1])[0][1]), tu)
        a2 = c2.mp(r1, e1)
        r2 = inst_at(c2, a2, v(0))                 # EQ(u, u) -> Z(u)
        ex = r2.f[2][1]
        want = subst_f(0, v(0), ex[1])[0]
        e2 = wit(c2, ex, v(0), tf_self(c2, want[1]), tf_self(c2, want[2]))
        zu = c2.mp(r2, e2)
        return wit(c2, lift(P_), v(0), tu, zu)
    return C.exists(C.thm(TOT), P_, f2)

def ctx_of(th, hyp):
    """th: G -> X proved in Ctx(L, [hyp]) (G = hyp); as a closed implication."""
    return th

thpq = pq(); thqp = qp()
check(thpq.f, Imp(P_, Q_), 'pq'); check(thqp.f, Imp(Q_, P_), 'qp')
out.lemma('g7_elab_pq', thpq, binders=' ' + HB1); thpq = Thm(L, thpq.f, '(g7_elab_pq %s)' % HC1)
out.lemma('g7_elab_qp', thqp, binders=' ' + HB1); thqp = Thm(L, thqp.f, '(g7_elab_qp %s)' % HC1)
C = Ctx(L, [E[1]])
core = C.mp(C.mp(C.hyp(0), C.thm(thpq)), C.thm(thqp))
check(core.f, E, 'elab core')
out.lemma('g7_elab_core', core, pub=True, binders=' ' + HB1)
out.thm('g7_elab_conv ' + HB1, 'trPA %s = %s' % (code_str(code), fm(E)), pE, pub=True)

DEF = '''def csb (v0: nat) (v1: nat) (v2: nat): nat = $ cAl (nfresh (ctup v0 (ctup (cV v1) v2))) (cIm (cEq (cV (nfresh (ctup v0 (ctup (cV v1) v2)))) v0) (cAl v1 (cIm (cEq (cV v1) (cV (nfresh (ctup v0 (ctup (cV v1) v2))))) v2))) $;
'''
out.raw(DEF)
# code = cNot (cIm (cIm L R) (cNot (cIm R L))), L = cEl v0 (cAb v1 v2), R = cAl z (...)
TOPL = 'cArg1_lt (lttr cArg1_lt cArg1_lt)'          # L < code
TOPR = 'cArg2_lt (lttr cArg1_lt cArg1_lt)'          # R < code
FR = 'nfr_fresh'
H = ' '.join([
    '(g7_trb_lt (lttr cArg1_lt (lttr %s)))' % TOPL,           # v0 in cEl v0 _
    '(g7_trb_lt (lttr cArg2_lt (lttr cArg2_lt (lttr %s))))' % TOPL,   # v2 in cAb v1 v2
    '(lttr cArg1_lt (lttr cArg2_lt (lttr %s)))' % TOPL,       # v1 in cAb v1 v2
    '(lttr cArg1_lt (lttr %s))' % TOPR,                       # z in cAl z _
    '(nfr_Vinv (nfr_tl (nfr_tr %s)))' % FR,
    '(g7_nfr_fresh (nfr_tl %s))' % FR,
    '(g7_nfr_fresh (nfr_tr (nfr_tr %s)))' % FR])
out.raw('''pub theorem elab_R (v0: nat) (v1: nat) (v2: nat): $ cPr (ciff (cEl v0 (cAb v1 v2)) (csb v0 v1 v2)) $ =
(named '(bi2 (g7_cpr_iff g7_tr_bound) (mpbir (paProvableeq2 (g7_elab_conv %s)) (g7_elab_core %s))));
''' % (H, H))

hdr = '''import "gen7_bx2.mm1";

-- G7 C2 (generated by tools/gen7/c2/gen_bx3.py): coded elab.
'''
out.write(os.path.join(PA, 'gen7', 'gen7_bx3.mm1'), hdr)
print('ok')
