"""Generates pa-mm0/gen7/gen7_tg.mm1: the term-constructor graphs (zero, successor, sum, product)
of total functional graphs are total and functional."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tg import *   # noqa

BASE[0] = '(suc n)'
L = Lv(1)
param('X', 'hX', 1); param('Y', 'hY', 1)
out = Out()
HB = '(n X Y: nat) (hX: $ paFormulaBound (suc n) X $) (hY: $ paFormulaBound (suc n) Y $)'
out.share('g7tg', HB, ['hX', 'hY'])
GX, GY = P0('X'), P0('Y')

def name_term(c, t):
    """c -> E. (v0 = lift t)."""
    body = Eq(v(0), shift_t(t, 1))
    return c.witness(body, t, c.refl(t))

def fun_from_ctx(C0, G, prove_eq):
    """C0 at L with closed hypotheses; prove C0.G -> FunP(G) from prove_eq(c) : c -> E10, where
    c = C0 lifted twice plus G(a), G(b) (a = v1, b = v0)."""
    goal = FunP(G)
    ga, gb = goal[1][1][1], goal[1][1][2][1]
    C1 = C0.lifted(); C2 = C1.lifted()
    c = C2.push(ga).push(gb)
    e = prove_eq(c)
    imp = C2.intro(C2.push(ga).intro(e))
    inner = all_intro_hyp(C1.n, C1.G, Thm(C2.n, Imp(lift(C1.G), imp.f[2]), imp.proof))
    return all_intro_hyp(C0.n, C0.G, Thm(C1.n, Imp(lift(C0.G), inner.f[2]), inner.proof))

def disch(th, *lemmas):
    """th: (h1 /\\ ... /\\ hk) -> f at level L (context of k hypotheses); lemmas prove h1..hk."""
    k = len(lemmas)
    for _ in range(k - 1): th = export(th)
    for lm in lemmas: th = mp(lm, th)
    return th

TOTX = Thm(L, Tot('X'), '(g7_tf_total hX)'); FUNX = Thm(L, Fun('X'), '(g7_tf_fun hX)')
TOTY = Thm(L, Tot('Y'), '(g7_tf_total hY)'); FUNY = Thm(L, Fun('Y'), '(g7_tf_fun hY)')

# zero
def gz_tot():
    C = Ctx(L, [TRUE])
    return mp(ident(L, F), name_term(C, Z)) if False else mp(ident(L, F), C.witness(raise_(GZ), Z, C.refl(Z)))
def gz_fun():
    C = Ctx(L, [TRUE])
    def eq(c): return c.trans(c.hyp(1), c.sym(c.hyp(2)))
    return mp(ident(L, F), fun_from_ctx(C, GZ, eq))

out.lemma('g7_gz_tot', gz_tot(), pub=True, binders=' ' + HB)
out.lemma('g7_gz_fun', gz_fun(), pub=True, binders=' ' + HB)

# successor
def gs_tot():
    G = GS(GX)
    goal = TotP(G)
    C = Ctx(L, [Tot('X')])
    def fn(c2):                      # c2: [lift Tot, TF X (u)], u = v0
        def fn2(c3):                 # c3: [.., lift TF X(u), v = S u], v = v0, u = v1
            body3 = lift(lift(goal))[1]
            want, _ = subst_f(0, v(0), body3)      # G(v)
            inner = want[1]
            p2 = c3.conj(c3.hyp(1), c3.hyp(2))
            gv = c3.witness(inner, v(1), p2)
            return c3.witness(body3, v(0), gv)
        return c2.exists(name_term(c2, S(v(0))), lift(goal), fn2)
    return disch(C.exists(C.hyp(0), goal, fn), TOTX)

def gs_fun():
    G = GS(GX)
    C0 = Ctx(L, [Fun('X')])
    def eq(c):                       # c: [llFun, G(a), G(b)]
        def fa(c1):                  # c1: [.., TF X(u) /\ a = S u]
            def fb(c2):              # c2: [.., TF X(w) /\ b = S w]
                hu, hw = c2.hyp(3), c2.hyp(4)
                inst = inst2(c2, c2.hyp(0), v(1), v(0))
                uw = c2.mp(c2.mp(inst, c2.and_left(hu)), c2.and_left(hw))
                r = c2.chain(c2.and_right(hu), c2.succ(uw), c2.sym(c2.and_right(hw)))
                return r
            return c1.exists(c1.hyp(2), lift(E10), fb)
        return c.exists(c.hyp(1), E10, fa)
    return disch(fun_from_ctx(C0, G, eq), FUNX)

out.lemma('g7_gs_tot', gs_tot(), pub=True, binders=' ' + HB)
out.lemma('g7_gs_fun', gs_fun(), pub=True, binders=' ' + HB)

def liftn(f, k):
    for _ in range(k): f = lift(f)
    return f

def gop_tot(GOP, op):
    G = GOP(GX, GY)
    goal = TotP(G)
    C = Ctx(L, [Tot('X'), Tot('Y')])
    def f1(c2):
        def f2(c3):
            def f3(c4):
                body4 = liftn(goal, 3)[1]
                want, _ = subst_f(0, v(0), body4)
                ob = want[1]
                iob, _ = subst_f(0, v(2), ob)
                ib = iob[2][1]
                p_in = c4.witness(ib, v(1), c4.conj(c4.hyp(3), c4.hyp(4)))
                gv = c4.witness(ob, v(2), c4.conj(c4.hyp(2), p_in))
                return c4.witness(body4, v(0), gv)
            return c3.exists(name_term(c3, (op, v(1), v(0))), liftn(goal, 2), f3)
        return c2.exists(c2.hyp(1), lift(goal), f2)
    return disch(C.exists(C.hyp(0), goal, f1), TOTX, TOTY)

def gop_fun(GOP, op):
    G = GOP(GX, GY)
    C0 = Ctx(L, [Fun('X'), Fun('Y')])
    def eq(c):
        def fa(c1):
            def fb(c2):
                def fc(c3):
                    def fd(c4):
                        uu = c4.mp(c4.mp(inst2(c4, c4.hyp(0), v(3), v(1)), c4.and_left(c4.hyp(4))), c4.and_left(c4.hyp(6)))
                        ww = c4.mp(c4.mp(inst2(c4, c4.hyp(1), v(2), v(0)), c4.and_left(c4.hyp(5))), c4.and_left(c4.hyp(7)))
                        return c4.chain(c4.and_right(c4.hyp(5)), c4.cong(op, uu, ww), c4.sym(c4.and_right(c4.hyp(7))))
                    return c3.exists(c3.and_right(c3.hyp(6)), liftn(E10, 3), fd)
                return c2.exists(c2.hyp(3), liftn(E10, 2), fc)
            return c1.exists(c1.and_right(c1.hyp(4)), lift(E10), fb)
        return c.exists(c.hyp(2), E10, fa)
    return disch(fun_from_ctx(C0, G, eq), FUNX, FUNY)

out.lemma('g7_ga_tot', gop_tot(GA, 'a'), pub=True, binders=' ' + HB)
out.lemma('g7_ga_fun', gop_fun(GA, 'a'), pub=True, binders=' ' + HB)
out.lemma('g7_gm_tot', gop_tot(GM, 'm'), pub=True, binders=' ' + HB)
out.lemma('g7_gm_fun', gop_fun(GM, 'm'), pub=True, binders=' ' + HB)

hdr = '''import "gen7_tf2.mm1";

-- G7 C2 (generated by tools/gen7/c2/gen_tg.py): the graphs trZeroF, trSucF, trAddF, trMulF
-- of total functional graphs are total and functional.
'''
out.write(os.path.join(PA, 'gen7', 'gen7_tg.mm1'), hdr)
print('ok')
