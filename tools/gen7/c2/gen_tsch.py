"""Generates pa-mm0/gen7/gen7_tsch.mm1: the T-scheme rules of GEN7 C5.

Internal PA lemmas (engine proofs, formula parameters) and their meta-rule wrappers, used by the
generated T-scheme instances (gen_tmh.py): a code formula c with free names translates to a PA
formula theta with the free name x as the variable x + 1, and
    paProvable (suc n) (trIff (trPA c) theta)
is proved by structure of c.
  * connectives:  g7r_imp, g7r_not, g7r_and (cNot (cIm a (cNot b))), g7r_or (cIm (cNot a) b),
    g7r_all (cAl x a), g7r_ex (cNot (cAl x (cNot a))), g7r_trans, g7r_sym;
  * terms: H(X, t) := A. v (X(v) <-> v = t) ("the graph X is the value t"); internal steps for
    successor, sum, product and equality atoms (g7t_suc, g7t_add, g7t_mul, g7t_eq), instantiated
    at concrete terms by the generator.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gb import *   # noqa

out = Out()
eng.BOUND_HOOK[0] = None; eng.EQ_HOOK[0] = None

def last(c, k=0): return c.hyp(len(c.hyps) - 1 - k)
def iff_i(c, A_, B_, fab, fba):
    return c.conj(c.intro(fab(c.push(A_))), c.intro(fba(c.push(B_))))
def iff_l(c, h, a): return c.mp(c.and_left(h), a)
def iff_r(c, h, b): return c.mp(c.and_right(h), b)
def dne(c, D, fn):
    """c -> D from fn(c + ~D) : -> F."""
    nn = c.intro(fn(c.push(Not(D))))
    return c.app(Thm(c.n, Imp(Not(Not(D)), D), '(bb215D2_dne %s)' % fbound(c.n, D)), nn)
def closed(th):
    """A context theorem TRUE -> f as a closed theorem f."""
    return mp(ident(th.n, F), th)
def inst_c(th, t):
    """closed A. body instantiated at t."""
    return mp(th, all_elim_ax(th.n, th.f[1], t))

def H(G, t): return All(Iff(raise_(G), Eq(v(0), shift_t(t, 1))))

# ---------------------------------------------------------------- parameters
for X in 'ABCD':
    param(X, 'h' + X, 1)
for X in 'PQ':
    param(X, 'h' + X, 2)
param('X', 'hX', 1); param('Y', 'hY', 1)
A_, B_, C_, D_ = P0('A'), P0('B'), P0('C'), P0('D')
P_, Q_ = P0('P'), P0('Q')

def bnd(names, lv='(suc n)'):
    return ' '.join('(h%s: $ paFormulaBound %s %s $)' % (x, lv, x) for x in names)

def emit_core(name, th, params, lvl2=()):
    b = '(n %s: nat) %s' % (' '.join(params), ' '.join(
        ['(h%s: $ paFormulaBound %s %s $)' % (x, '(suc (suc n))' if x in lvl2 else '(suc n)', x) for x in params]))
    out.lemma(name, th, pub=False, binders=' ' + b)

# ---------------------------------------------------------------- propositional cores
def core_imp():
    cx = Ctx(L, [Iff(A_, C_), Iff(B_, D_)])
    def f1(c1):
        c2 = c1.push(C_)
        a = iff_r(c2, c2.hyp(0), last(c2))
        b = c2.mp(c2.hyp(2), a)
        return c1.intro(iff_l(c2, c2.hyp(1), b))
    def g1(c1):
        c2 = c1.push(A_)
        cc = iff_l(c2, c2.hyp(0), last(c2))
        d = c2.mp(c2.hyp(2), cc)
        return c1.intro(iff_r(c2, c2.hyp(1), d))
    return export(iff_i(cx, Imp(A_, B_), Imp(C_, D_), f1, g1))

def core_not():
    cx = Ctx(L, [Iff(A_, C_)])
    def f1(c1):
        c2 = c1.push(C_)
        return c1.intro(c2.mp(c2.hyp(1), iff_r(c2, c2.hyp(0), last(c2))))
    def g1(c1):
        c2 = c1.push(A_)
        return c1.intro(c2.mp(c2.hyp(1), iff_l(c2, c2.hyp(0), last(c2))))
    return iff_i(cx, Not(A_), Not(C_), f1, g1)

def core_and():
    cx = Ctx(L, [Iff(A_, C_), Iff(B_, D_)])
    N_ = Not(Imp(A_, Not(B_)))
    def f1(c1):                                   # hyp N_
        def gc(c2):                               # ~C -> F
            c3 = c2.push(A_)
            cc = iff_l(c3, c3.hyp(0), last(c3))
            f = c3.mp(c3.hyp(3), cc)
            imp = c2.intro(c3.absurd(f, Not(B_)))
            return c2.mp(c2.hyp(2), imp)
        def gd(c2):                               # ~D -> F
            c3 = c2.push(A_)
            c4 = c3.push(B_)
            d = iff_l(c4, c4.hyp(1), last(c4))
            f = c4.mp(c4.hyp(3), d)
            imp = c2.intro(c3.intro(f))
            return c2.mp(c2.hyp(2), imp)
        return c1.conj(dne(c1, C_, gc), dne(c1, D_, gd))
    def g1(c1):                                   # hyp C /\ D
        c2 = c1.push(Imp(A_, Not(B_)))
        h = c2.hyp(2)
        a = iff_r(c2, c2.hyp(0), c2.and_left(h))
        b = iff_r(c2, c2.hyp(1), c2.and_right(h))
        return c1.intro(c2.mp(c2.mp(last(c2), a), b))
    return export(iff_i(cx, N_, And(C_, D_), f1, g1))

def core_or():
    cx = Ctx(L, [Iff(A_, C_), Iff(B_, D_)])
    O_ = Or(C_, D_)
    def f1(c1):                                   # hyp ~A -> B
        em = c1.lem(A_)
        def fa(c2):
            cc = iff_l(c2, c2.hyp(0), last(c2))
            return c2.app(or_left_ax(c2.n, C_, D_), cc)
        def fb(c2):
            b = c2.mp(c2.hyp(2), last(c2))
            d = iff_l(c2, c2.hyp(1), b)
            return c2.app(or_right_ax(c2.n, C_, D_), d)
        return c1.cases(em, fa, fb)
    def g1(c1):                                   # hyp C \/ D
        c2 = c1.push(Not(A_))
        def fa(c3):
            a = iff_r(c3, c3.hyp(0), last(c3))
            return c3.absurd(c3.mp(c3.hyp(3), a), B_)
        def fb(c3):
            return iff_r(c3, c3.hyp(1), last(c3))
        return c1.intro(c2.cases(c2.hyp(2), fa, fb))
    return export(iff_i(cx, Imp(Not(A_), B_), O_, f1, g1))

def core_trans():
    cx = Ctx(L, [Iff(A_, B_), Iff(B_, C_)])
    def f1(c1): return iff_l(c1, c1.hyp(1), iff_l(c1, c1.hyp(0), last(c1)))
    def g1(c1): return iff_r(c1, c1.hyp(0), iff_r(c1, c1.hyp(1), last(c1)))
    return export(iff_i(cx, A_, C_, f1, g1))

def core_sym():
    cx = Ctx(L, [Iff(A_, B_)])
    def f1(c1): return iff_r(c1, c1.hyp(0), last(c1))
    def g1(c1): return iff_l(c1, c1.hyp(0), last(c1))
    return iff_i(cx, B_, A_, f1, g1)

def core_mpr():
    """~(A -> ~B) -> B (the right conjunct of a coded conjunction)."""
    cx = Ctx(L, [Not(Imp(A_, Not(B_)))])
    def g(c2):
        c3 = c2.push(A_)
        return c2.mp(c2.hyp(0), c2.intro(c3.hyp(1)))
    return dne(cx, B_, g)

def core_mpl():
    """~(A -> ~B) -> A (the left conjunct of a coded conjunction)."""
    cx = Ctx(L, [Not(Imp(A_, Not(B_)))])
    def g(c2):
        c3 = c2.push(A_)
        f = c3.mp(c3.hyp(1), last(c3))
        return c2.mp(c2.hyp(0), c2.intro(c3.absurd(f, Not(B_))))
    return dne(cx, A_, g)

# ---------------------------------------------------------------- quantifier cores (P, Q one level up)
def core_allc():
    cx = Ctx(L, [All(Iff(P_, Q_))])
    def f1(c1):                                   # hyp A. P
        def body(cl):
            i = inst_at(cl, cl.hyp(0), v(0))
            p = inst_at(cl, cl.hyp(1), v(0))
            return iff_l(cl, i, p)
        return all_in(c1, body)
    def g1(c1):
        def body(cl):
            i = inst_at(cl, cl.hyp(0), v(0))
            q = inst_at(cl, cl.hyp(1), v(0))
            return iff_r(cl, i, q)
        return all_in(c1, body)
    return iff_i(cx, All(P_), All(Q_), f1, g1)

def core_exc():
    cx = Ctx(L, [TRUE])
    NA = Not(All(Not(P_)))
    def f1(c1):                                   # hyp ~ A. ~P
        def g(c2):                                # ~ E. P -> F
            def body(cl):
                c3 = cl.push(lift(P_)[0] if False else subst_f(0, v(0), rename_f(1, P_)[0])[0])
                w = c3.witness(rename_f(1, P_)[0], v(0), last(c3))
                return cl.intro(c3.mp(c3.hyp(2), w))
            al = all_in(c2, body)
            return c2.mp(c2.hyp(1), al)
        return dne(c1, Ex(P_), g)
    def g1(c1):                                   # hyp E. P
        c2 = c1.push(All(Not(P_)))
        def fn(c3):
            i = inst_at(c3, c3.hyp(2), v(0))
            return c3.mp(i, last(c3))
        return c1.intro(c2.exists(c2.hyp(1), F, fn))
    return closed(iff_i(cx, NA, Ex(P_), f1, g1))

# ---------------------------------------------------------------- term graphs
def tfh_g(c, i, G, t):
    """c.hyps[i] = H(G, t) (G at c's level, t a term at c's level); c -> H(TFg(G), t)."""
    check(c.hyps[i], H(G, t), 'tfh hyp')
    target = H(TFg(G), t)
    Bt = target[1]
    PT, QT = Bt[1][1], Bt[1][2]               # TF G (v), v = t'
    tt = QT[2]
    def body(cl):
        hl = cl.hyp(i)                          # A. (G'(w) <-> w = t')  (lifted)
        def fwd(ca):                            # hyp PT
            def case1(cb):                      # A. (G(w) <-> w = v)
                h = last(cb)
                e1 = inst_at(cb, h, tt)          # G(t') <-> t' = v
                e2 = inst_at(cb, hl if False else cb.hyp(i), tt)   # G(t') <-> t' = t'
                gt = iff_r(cb, e2, cb.refl(tt))
                tv = iff_l(cb, e1, gt)
                r = cb.sym(tv)
                check(r.f[2], QT, 'tfh fwd1')
                return r
            def case2(cb):                      # ~ E. A. (G(w) <-> w = u) /\ v = 0
                h = last(cb)
                nex = cb.and_left(h)
                E_ = nex.f[2][1]
                wit = cb.witness(E_[1], tt, cb.hyp(i))
                return cb.absurd(cb.mp(nex, wit), QT)
            return ca.cases(last(ca), case1, case2)
        def bwd(ca):                            # hyp v = t'
            e = last(ca)
            left = PT[1]
            def inner(cl2):                     # w = v0, v = v1: G(w) <-> w = v
                e2 = cl2.hyp(len(ca.hyps) - 1)  # v = t' (lifted)
                hh = inst_at(cl2, cl2.hyp(i), v(0))   # G(w) <-> w = t''
                tgt = left[1]
                def f1(c3):
                    wt = iff_l(c3, hh if False else inst_at(c3, c3.hyp(i), v(0)), last(c3))
                    return c3.trans(wt, c3.sym(c3.hyp(len(ca.hyps) - 1)))
                def f2(c3):
                    wt = c3.trans(last(c3), c3.hyp(len(ca.hyps) - 1))
                    return iff_r(c3, inst_at(c3, c3.hyp(i), v(0)), wt)
                r = iff_i(cl2, tgt[1][1], tgt[1][2], f1, f2)
                check(r.f[2], tgt, 'tfh bwd inner')
                return r
            al = all_in(ca, inner)
            return ca.app(or_left_ax(ca.n, left, PT[2]), al)
        return iff_i(cl, PT, QT, fwd, bwd)
    r = all_in(c, body)
    check(r.f[2], target, 'tfh')
    return r

def with_tf(c, specs, fn):
    """specs: list of (hyp index, G, t); pushes H(TFg G, t) for each, then fn(c')."""
    if not specs: return fn(c)
    i, G, t = specs[0]
    th = tfh_g(c, i, G, t)
    return cut(c, th, lambda c2: with_tf(c2, specs[1:], fn))

GX, GY = P0('X'), P0('Y')

def core_suc():
    cx = Ctx(L, [TRUE])
    def body(cl):
        G = raise_(GX); u = v(0)
        c2 = cl.push(H(G, u))
        target = H(GS(G), S(u))
        def fn(c3):                              # hyps: TRUE, H(G,u), H(TF G, u)
            k = len(c3.hyps) - 1
            def b2(cl3):
                Bt = target[1]
                PT, QT = Bt[1][1], Bt[1][2]
                def fwd(ca):
                    def f4(c4):                  # a = v0 (TF G(a) /\ v = S a)
                        h = last(c4)
                        hk = inst_at(c4, c4.hyp(k), v(0))
                        au = iff_l(c4, hk, c4.and_left(h))
                        return c4.trans(c4.and_right(h), c4.succ(au))
                    return ca.exists(last(ca), QT, f4)
                def bwd(ca):
                    e = last(ca)
                    tu = QT[2][1]               # u at this level
                    hk = inst_at(ca, ca.hyp(k), tu)
                    tf = iff_r(ca, hk, ca.refl(tu))
                    ob = PT[1]
                    return ca.witness(ob, tu, ca.conj(tf, e))
                return iff_i(cl3, PT, QT, fwd, bwd)
            r = all_in(c3, b2)
            check(r.f[2], target, 'suc target')
            return r
        r = with_tf(c2, [(1, G, u)], fn)
        return cl.intro(r)
    th = closed(all_in(cx, body))
    return th

def core_op(op):
    cx = Ctx(L, [TRUE])
    def body(cl1):
        def body2(cl):
            G1, G2 = raise_(raise_(GX)), raise_(raise_(GY))
            a, b = v(1), v(0)
            c2 = cl.push(H(G1, a)).push(H(G2, b))
            if op == 'eq':
                target = Iff(EQg(G1, G2), Eq(a, b))
            else:
                target = H((GA if op == 'a' else GM)(G1, G2), (A if op == 'a' else M)(a, b))
            def fn(c3):
                ka, kb = len(c3.hyps) - 2, len(c3.hyps) - 1
                if op == 'eq':
                    PT, QT = target[1][1], target[1][2]
                    def fwd(ca):
                        def f4(c4):
                            h = last(c4)
                            xa = iff_l(c4, inst_at(c4, c4.hyp(ka), v(0)), c4.and_left(h))
                            xb = iff_l(c4, inst_at(c4, c4.hyp(kb), v(0)), c4.and_right(h))
                            return c4.trans(c4.sym(xa), xb)
                        return ca.exists(last(ca), QT, f4)
                    def bwd(ca):
                        e = last(ca)
                        ta = QT[1]
                        tfa = iff_r(ca, inst_at(ca, ca.hyp(ka), ta), ca.refl(ta))
                        tfb = iff_r(ca, inst_at(ca, ca.hyp(kb), ta), e)
                        return ca.witness(PT[1], ta, ca.conj(tfa, tfb))
                    r = iff_i(c3, PT, QT, fwd, bwd)
                    check(r.f[2], target, 'eq target')
                    return r
                def b2(cl3):
                    Bt = target[1]
                    PT, QT = Bt[1][1], Bt[1][2]
                    def fwd(ca):
                        def f4(c4):                      # x: TF G1(x) /\ E. y (...)
                            h = last(c4)
                            xa = iff_l(c4, inst_at(c4, c4.hyp(ka), v(0)), c4.and_left(h))
                            inner = c4.and_right(h)
                            QT4 = lift(QT)
                            def f5(c5):
                                h5 = last(c5)
                                yb = iff_l(c5, inst_at(c5, c5.hyp(kb), v(0)), c5.and_left(h5))
                                xa5 = c5.hyp(len(c4.hyps) - 1)
                                # xa lives in c4 as a proof, re-derive at c5 from the lifted hyp
                                xa5 = iff_l(c5, inst_at(c5, c5.hyp(ka), v(1)), c5.and_left(c5.hyp(len(c4.hyps) - 1)))
                                eq = c5.and_right(h5)
                                return c5.trans(eq, c5.cong(op, xa5, yb))
                            return c4.exists(inner, QT4, f5)
                        return ca.exists(last(ca), QT, f4)
                    def bwd(ca):
                        e = last(ca)
                        sa, sb = QT[2][1], QT[2][2]
                        tfa = iff_r(ca, inst_at(ca, ca.hyp(ka), sa), ca.refl(sa))
                        tfb = iff_r(ca, inst_at(ca, ca.hyp(kb), sb), ca.refl(sb))
                        ob = PT[1]
                        ib = subst_f(0, sa, ob)[0][2][1]
                        pin = ca.witness(ib, sb, ca.conj(tfb, e))
                        return ca.witness(ob, sa, ca.conj(tfa, pin))
                    return iff_i(cl3, PT, QT, fwd, bwd)
                r = all_in(c3, b2)
                check(r.f[2], target, 'op target')
                return r
            r = with_tf(c2, [(1, G1, a), (2, G2, b)], fn)
            r = cl.push(H(G1, a)).intro(r) if False else r
            # discharge the two pushed hypotheses
            c1 = cl.push(H(G1, a))
            return cl.intro(c1.intro(r))
        return all_in(cl1, body2)
    return closed(all_in(cx, body))


cores = {}
def add(name, th, params, lvl2=()):
    emit_core(name, th, params, lvl2)
    cores[name] = th

add('g7rc_imp', core_imp(), 'ABCD')
add('g7rc_not', core_not(), 'AC')
add('g7rc_and', core_and(), 'ABCD')
add('g7rc_or', core_or(), 'ABCD')
add('g7rc_trans', core_trans(), 'ABC')
add('g7rc_sym', core_sym(), 'AB')
add('g7rc_mpr', core_mpr(), 'AB')
add('g7rc_mpl', core_mpl(), 'AB')
add('g7rc_allc', core_allc(), 'PQ', 'PQ')
add('g7rc_exc', core_exc(), 'P', 'P')
add('g7t_suc', core_suc(), 'X')
add('g7t_add', core_op('a'), 'XY')
add('g7t_mul', core_op('m'), 'XY')
add('g7t_eq', core_op('eq'), 'XY')

# ---------------------------------------------------------------- meta-rule wrappers
_EQN3 = {'and': 'And', 'or': 'Or', 'imp': 'Imp', 'all': 'All', 'ex': 'Ex'}
def eqconv(f, hb):
    """proof of RAW = fm f, RAW = f with each Par(X, 0, 0) printed as X; hb: X -> bound proof."""
    c = f[0]
    if c == 'par':
        assert f[2] == 0 and f[3] == 0, f
        return '(g7_par_id %s)' % hb[f[1]]
    if c in ('and', 'or', 'imp'):
        return '(paFormula%seq %s %s)' % (_EQN3[c], eqconv(f[1], hb), eqconv(f[2], hb))
    if c in ('all', 'ex'):
        return '(paFormula%seq %s)' % (_EQN3[c], eqconv(f[1], hb))
    return 'eqid'

def BL(h): return '(anl (bi1 paFormulaBound_imp (anl (bi1 paFormulaBound_and (paProvable_bound %s)))))' % h
def BR(h): return '(anr (bi1 paFormulaBound_imp (anl (bi1 paFormulaBound_and (paProvable_bound %s)))))' % h
def PB(h): return '(paProvable_bound %s)' % h

def wrap(name, binders, hyps, concl, core, hb, mps):
    th = cores[core]
    call = '(%s %s)' % (core, ' '.join(hb[x] for x in sorted(hb)))
    p = '(mpbir (paProvableeq2 %s) %s)' % (eqconv(th.f, hb), call)
    for h in mps:
        p = '(bb215D2_mp %s %s)' % (h, p)
    out.raw("pub theorem %s %s %s:\n  $ %s $ =\n(named '%s);\n" % (name, binders, ' '.join(hyps), concl, p))

def Pv(s): return 'paProvable (suc n) (%s)' % s
wrap('g7r_imp', '(n A B C D: nat)', ['(h1: $ %s $)' % Pv('trIff A C'), '(h2: $ %s $)' % Pv('trIff B D')],
     Pv('trIff (paFormulaImp A B) (paFormulaImp C D)'), 'g7rc_imp',
     {'A': BL('h1'), 'C': BR('h1'), 'B': BL('h2'), 'D': BR('h2')}, ['h1', 'h2'])
wrap('g7r_not', '(n A C: nat)', ['(h1: $ %s $)' % Pv('trIff A C')],
     Pv('trIff (trNot A) (trNot C)'), 'g7rc_not', {'A': BL('h1'), 'C': BR('h1')}, ['h1'])
wrap('g7r_and', '(n A B C D: nat)', ['(h1: $ %s $)' % Pv('trIff A C'), '(h2: $ %s $)' % Pv('trIff B D')],
     Pv('trIff (trNot (paFormulaImp A (trNot B))) (paFormulaAnd C D)'), 'g7rc_and',
     {'A': BL('h1'), 'C': BR('h1'), 'B': BL('h2'), 'D': BR('h2')}, ['h1', 'h2'])
wrap('g7r_or', '(n A B C D: nat)', ['(h1: $ %s $)' % Pv('trIff A C'), '(h2: $ %s $)' % Pv('trIff B D')],
     Pv('trIff (paFormulaImp (trNot A) B) (paFormulaOr C D)'), 'g7rc_or',
     {'A': BL('h1'), 'C': BR('h1'), 'B': BL('h2'), 'D': BR('h2')}, ['h1', 'h2'])
wrap('g7r_trans', '(n A B C: nat)', ['(h1: $ %s $)' % Pv('trIff A B'), '(h2: $ %s $)' % Pv('trIff B C')],
     Pv('trIff A C'), 'g7rc_trans', {'A': BL('h1'), 'B': BR('h1'), 'C': BR('h2')}, ['h1', 'h2'])
wrap('g7r_sym', '(n A B: nat)', ['(h1: $ %s $)' % Pv('trIff A B')],
     Pv('trIff B A'), 'g7rc_sym', {'A': BL('h1'), 'B': BR('h1')}, ['h1'])
_nb = '(bi1 paFormulaBound_imp (anl (bi1 paFormulaBound_imp (paProvable_bound h1))))'
wrap('g7r_mpr', '(n A B: nat)', ['(h1: $ %s $)' % Pv('trNot (paFormulaImp A (trNot B))')],
     Pv('B'), 'g7rc_mpr', {'A': '(anl %s)' % _nb, 'B': '(anl (bi1 paFormulaBound_imp (anr %s)))' % _nb}, ['h1'])
wrap('g7r_mpl', '(n A B: nat)', ['(h1: $ %s $)' % Pv('trNot (paFormulaImp A (trNot B))')],
     Pv('A'), 'g7rc_mpl', {'A': '(anl %s)' % _nb, 'B': '(anl (bi1 paFormulaBound_imp (anr %s)))' % _nb}, ['h1'])
# quantifier rules
_ab = lambda g, h: '(g7_abs_bound %s)' % h
out.raw("""pub theorem g7r_all (n x A B: nat) (h1: $ %s $):
  $ %s $ =
(named '(bb215D2_mp (bb215D2_gen (mpbi (paProvableeq2 (eqtr paFormulaRename_and (paFormulaAndeq paFormulaRename_imp paFormulaRename_imp)))
    (g7_rr (ax_gen g7_abs_lt) h1 (paProvable_bound h1))))
  (mpbir (paProvableeq2 %s) (g7rc_allc (g7_abs_bound %s) (g7_abs_bound %s)))));
""" % (Pv('trIff A B'), Pv('trIff (paFormulaAll (trAbs (suc x) A)) (paFormulaAll (trAbs (suc x) B))'),
       eqconv(cores['g7rc_allc'].f, {'P': '(g7_abs_bound %s)' % BL('h1'), 'Q': '(g7_abs_bound %s)' % BR('h1')}), BL('h1'), BR('h1')))
_rn = '(eqtr paFormulaRename_imp (paFormulaImpeq eqid paFormulaRename_false))'
out.raw("""pub theorem g7r_ex (n x A B: nat) (h1: $ %s $):
  $ %s $ =
(named '(g7r_trans (g7r_not (mpbi (paProvableeq2 (trIffeq eqid (paFormulaAlleq %s))) (g7r_all (g7r_not h1))))
  (mpbir (paProvableeq2 %s) (g7rc_exc (g7_abs_bound %s)))));
""" % (Pv('trIff A B'), Pv('trIff (trNot (paFormulaAll (trAbs (suc x) (trNot A)))) (paFormulaEx (trAbs (suc x) B))'), _rn,
       eqconv(cores['g7rc_exc'].f, {'P': '(g7_abs_bound %s)' % BR('h1')}), BR('h1')))

hdr = '''import "gen7_numg.mm1";

import "gen7_sl.mm1";

-- (slim closure: no C2 axiom modules; the one fact of gen7_abs the instances use, under its own name)
theorem g7x_abs_miss (k j: nat) (h: $ j != k $): $ trAbsMap k @ j = suc j $ = (named '(eqtr g7_abs_value (ifneg h)));

-- G7 C5 (generated by tools/gen7/c2/gen_tsch.py): the T-scheme rules (see the generator's docstring).
'''
out.write(os.path.join(PA, 'gen7', 'gen7_tsch.mm1'), hdr)
import pickle
pickle.dump({k: (int(v.n), v.f) for k, v in cores.items()}, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tsch_cores.pkl'), 'wb'))
print('ok')
