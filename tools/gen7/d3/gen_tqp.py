"""Route T (lanes/D3CHECK.md): generates pa-mm0/gen7/d3_tqp.mm1 / .mm0, the propositional and quantifier lemmas
of TQ (hand PA formula vs trPA of its named code) at level suc n, formula parameters bound by suc n.
Uses the GEN7 C2 natural-deduction engine (tools/gen7/c2/g7nd.py over L05's bb215_l3_nd)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'c2'))
from g7nd import *   # noqa
import bb215_l3_engine as eng

BASE[0] = '(suc n)'
L = Lv(1)
NAMES = ['X', 'Y', 'Z', 'U']
for x in NAMES:
    param(x, 'h' + x, 1)
def P(x): return Par(x, 0, 0)

def plain(f):
    """(MM0 text with plain parameters, proof that it equals fm(f))."""
    c = f[0]
    if c == 'par':
        assert f[2] == 0 and f[3] == 0
        return f[1], '(g7_par_id h%s)' % f[1]
    if c in ('and', 'or', 'imp'):
        a, pa = plain(f[1]); b, pb = plain(f[2])
        nm = {'and': 'And', 'or': 'Or', 'imp': 'Imp'}[c]
        return '(paFormula%s %s %s)' % (nm, a, b), '(paFormula%seq %s %s)' % (nm, pa, pb)
    if c in ('all', 'ex'):
        a, pa = plain(f[1]); nm = {'all': 'All', 'ex': 'Ex'}[c]
        return '(paFormula%s %s)' % (nm, a), '(paFormula%seq %s)' % (nm, pa)
    return fm(f), 'eqid'

def dne(n, a): return Thm(n, Imp(Not(Not(a)), a), '(bb215D2_dne %s)' % fbound(n, a))

def iff_intro(c, A, B, fab, fba):
    """G -> Iff(A, B) from fab(ctx + A) : -> B and fba(ctx + B) : -> A."""
    return c.conj(c.intro(fab(c.push(A))), c.intro(fba(c.push(B))))

def fwd(c, i, a):   # G -> X from G -> Y? no: use hyp i = Iff(X, Y): from G -> X get G -> Y
    return c.mp(c.and_left(c.hyp(i)), a)
def bwd(c, i, b):
    return c.mp(c.and_right(c.hyp(i)), b)

items, specs = [], []
def emit(name, hyps, goal, core):
    """core: Ctx(L, hyps) proof G -> goal. Emits name_c (engine form) and name (plain, hypotheses)."""
    th = core
    for _ in range(len(hyps) - 1):
        th = export(th)
    binders = '(n %s: nat) %s' % (' '.join(NAMES), ' '.join('(h%s: $ paFormulaBound (suc n) %s $)' % (x, x) for x in NAMES))
    items.append("theorem %s_c %s: $ paProvable %s %s $ =\n'%s;\n" % (name, binders, num(th.n), fm(th.f), th.proof))
    # plain wrapper: hypotheses hk: paProvable (suc n) plain(hyp_k); conclusion plain(goal)
    hs, call = [], '(%s_c %s)' % (name, ' '.join('h' + x for x in NAMES))
    for k, h in enumerate(hyps):
        ht, hp = plain(h)
        hs.append('(e%d: $ paProvable (suc n) %s $)' % (k, ht))
        call = '(bb215D2_mp (mpbi (paProvableeq2 %s) e%d) %s)' % (hp, k, call)
    gt, gp = plain(goal)
    stmt = 'theorem %s %s %s: $ paProvable (suc n) %s $' % (name, binders, ' '.join(hs), gt)
    items.append("pub %s =\n'(mpbir (paProvableeq2 %s) %s);\n" % (stmt, gp, call))
    specs.append(stmt + ';')

X, Y, Zf, U = P('X'), P('Y'), P('Z'), P('U')

# iff_trans: (X <-> Y) -> (Y <-> Z) -> (X <-> Z)
hy = [Iff(X, Y), Iff(Y, Zf)]
c = Ctx(L, hy)
emit('d3p_trans', hy, Iff(X, Zf), iff_intro(c, X, Zf,
     lambda d: fwd(d, 1, fwd(d, 0, d.hyp(2))), lambda d: bwd(d, 0, bwd(d, 1, d.hyp(2)))))
# iff_sym
hy = [Iff(X, Y)]; c = Ctx(L, hy)
emit('d3p_sym', hy, Iff(Y, X), iff_intro(c, Y, X, lambda d: bwd(d, 0, d.hyp(1)), lambda d: fwd(d, 0, d.hyp(1))))
# not congruence: (X <-> Y) -> (~X <-> ~Y)
hy = [Iff(X, Y)]; c = Ctx(L, hy)
emit('d3p_not', hy, Iff(Not(X), Not(Y)), iff_intro(c, Not(X), Not(Y),
     lambda d: d.intro((lambda e: e.mp(e.hyp(1), bwd(e, 0, e.hyp(2))))(d.push(Y))),
     lambda d: d.intro((lambda e: e.mp(e.hyp(1), fwd(e, 0, e.hyp(2))))(d.push(X)))))
# imp congruence: (X <-> Y) -> (Z <-> U) -> ((X -> Z) <-> (Y -> U))
hy = [Iff(X, Y), Iff(Zf, U)]; c = Ctx(L, hy)
emit('d3p_imp', hy, Iff(Imp(X, Zf), Imp(Y, U)), iff_intro(c, Imp(X, Zf), Imp(Y, U),
     lambda d: d.intro((lambda e: fwd(e, 1, e.mp(e.hyp(2), bwd(e, 0, e.hyp(3)))))(d.push(Y))),
     lambda d: d.intro((lambda e: bwd(e, 1, e.mp(e.hyp(2), fwd(e, 0, e.hyp(3)))))(d.push(X)))))
# and: (X <-> Y) -> (Z <-> U) -> (~(X -> ~Z) <-> (Y /\ U))
def and_fwd(d):          # d = G + N, N = ~(X -> ~Z); prove Y /\ U
    N = d.hyp(2)
    def get(a, other_imp):
        # ~~a by: push ~a, derive (X -> ~Z), then N gives F
        e = d.push(Not(a))
        imp = other_imp(e)
        nn = d.intro(e.mp(N if False else e.hyp(2), imp))
        return d.app(dne(L, a), nn)
    def imp_from_notX(e):     # e = G + N + ~X : G -> (X -> ~Z)
        f = e.push(X)
        return e.intro(f.absurd(f.mp(f.hyp(3), f.hyp(4)), Not(Zf)))
    def imp_from_notZ(e):     # e = G + N + ~Z : G -> (X -> ~Z)
        f = e.push(X)
        return e.intro(f.hyp(3))
    x = get(X, imp_from_notX)
    z = get(Zf, imp_from_notZ)
    return d.conj(fwd(d, 0, x), fwd(d, 1, z))
def and_bwd(d):          # d = G + (Y /\ U); prove ~(X -> ~Z)
    e = d.push(Imp(X, Not(Zf)))
    x = bwd(e, 0, e.and_left(e.hyp(2)))
    z = bwd(e, 1, e.and_right(e.hyp(2)))
    return d.intro(e.mp(e.mp(e.hyp(3), x), z))
hy = [Iff(X, Y), Iff(Zf, U)]; c = Ctx(L, hy)
emit('d3p_and', hy, Iff(Not(Imp(X, Not(Zf))), And(Y, U)), iff_intro(c, Not(Imp(X, Not(Zf))), And(Y, U), and_fwd, and_bwd))
# or: (X <-> Y) -> (Z <-> U) -> ((~X -> Z) <-> (Y \/ U))
def or_fwd(d):           # d = G + (~X -> Z)
    def ca(e):  # e = d + X
        return e.app(or_left_ax(L, Y, U), fwd(e, 0, e.hyp(3)))
    def cb(e):  # e = d + ~X
        return e.app(or_right_ax(L, Y, U), fwd(e, 1, e.mp(e.hyp(2), e.hyp(3))))
    return d.cases(d.lem(X), ca, cb)
def or_bwd(d):           # d = G + (Y \/ U); prove ~X -> Z
    e = d.push(Not(X))
    def ca(f):  # f = e + Y
        return f.absurd(f.mp(f.hyp(3), bwd(f, 0, f.hyp(4))), Zf)
    def cb(f):  # f = e + U
        return bwd(f, 1, f.hyp(4))
    return d.intro(e.cases(e.hyp(2), ca, cb))
hy = [Iff(X, Y), Iff(Zf, U)]; c = Ctx(L, hy)
emit('d3p_or', hy, Iff(Imp(Not(X), Zf), Or(Y, U)), iff_intro(c, Imp(Not(X), Zf), Or(Y, U), or_fwd, or_bwd))
# false: ~(F -> F) <-> F   (one dummy hypothesis X <-> X to keep the wrapper shape)
hy = [Iff(X, X)]; c = Ctx(L, hy)
emit('d3p_false', hy, Iff(Not(Imp(F, F)), F), iff_intro(c, Not(Imp(F, F)), F,
     lambda d: d.mp(d.hyp(1), d.thm(ident(L, F))), lambda d: d.absurd(d.hyp(1), Not(Imp(F, F)))))

# ---- congruences with hypotheses at other levels (closed engine theorems; hypotheses as MM1 hypotheses) ----
def emit_h(name, plv, hyps, build):
    """plv: {param: level b}; hyps: [(level k, engine formula)]; build(list of Thm hyps) -> Thm (engine form)."""
    for x, b in plv.items():
        PARAMS[x] = ('h' + x, b)
    hs = [Thm(Lv(k), f, 'e%d' % i) for i, (k, f) in enumerate(hyps)]
    th = build(hs)
    xs = sorted(plv)
    binders = '(n %s: nat) %s' % (' '.join(xs), ' '.join('(h%s: $ paFormulaBound %s %s $)' % (x, lvstr(plv[x]), x) for x in xs))
    hb = ' '.join('(e%d: $ paProvable %s %s $)' % (i, lvstr(k), fm(f)) for i, (k, f) in enumerate(hyps))
    items.append("theorem %s_c %s %s: $ paProvable %s %s $ =\n'%s;\n" % (name, binders, hb, lvstr(int(th.n)), fm(th.f), th.proof))
    call = '(%s_c %s' % (name, ' '.join('h' + x for x in xs))
    hp = []
    for i, (k, f) in enumerate(hyps):
        ht, pp = plain(f)
        hp.append('(e%d: $ paProvable %s %s $)' % (i, lvstr(k), ht))
        call += ' (mpbi (paProvableeq2 %s) e%d)' % (pp, i)
    call += ')'
    gt, gp = plain(th.f)
    stmt = 'theorem %s %s %s: $ paProvable %s %s $' % (name, binders, ' '.join(hp), lvstr(int(th.n)), gt)
    items.append("pub %s =\n'(mpbir (paProvableeq2 %s) %s);\n" % (stmt, gp, call))
    specs.append(stmt + ';')
    for x in NAMES: PARAMS[x] = ('h' + x, 1)

def ex_mono(h):      # h: Lv(k+1) |- X -> Y  =>  Lv(k) |- E. X -> E. Y
    k = int(h.n) - 1
    Xf, Yf = h.f[1], h.f[2]
    lY, _ = lift_f(Ex(Yf))
    w = ex_intro_imp(h.n, lY[1], v(0))          # Lv(k+1): (lY body)[v0] -> lift(E. Y)
    need(w.f[1] == Yf, 'ex_mono: witness form')
    return ex_elim(Lv(k), Xf, Ex(Yf), syl(h, w))

def iff_split(h):
    return mp(h, and_left_ax(h.n, h.f[1], h.f[2])), mp(h, and_right_ax(h.n, h.f[1], h.f[2]))
def iff_join(a, b):
    return and_intro(a, b)

X2, Y2 = Par('X', 0, 0), Par('Y', 0, 0)
# E. congruence: (X <-> Y) at suc (suc n)  =>  (E. X <-> E. Y) at suc n
emit_h('d3p_exc', {'X': 2, 'Y': 2}, [(2, Iff(X2, Y2))],
       lambda hs: (lambda ab: iff_join(ex_mono(ab[0]), ex_mono(ab[1])))(iff_split(hs[0])))
# A. congruence via bb215L2_all_mono (= paD0_all_mono_imp shape)
def all_mono(h):
    k = int(h.n) - 1
    return Thm(Lv(k), Imp(All(h.f[1]), All(h.f[2])), '(paD0_all_mono_imp %s %s %s)' % (fbound(h.n, h.f[1]), fbound(h.n, h.f[2]), h.proof))
emit_h('d3p_allc', {'X': 2, 'Y': 2}, [(2, Iff(X2, Y2))],
       lambda hs: (lambda ab: iff_join(all_mono(ab[0]), all_mono(ab[1])))(iff_split(hs[0])))
# hand /\, \/, <-> congruences and iff reflexivity at suc n
def cong2(mk):
    def b(hs):
        c = Ctx(L, [TRUE])
        return None
    return b
X1, Y1, Z1, U1 = P('X'), P('Y'), P('Z'), P('U')
hy = [Iff(X1, Y1), Iff(Z1, U1)]; c = Ctx(L, hy)
emit('d3p_andc', hy, Iff(And(X1, Z1), And(Y1, U1)), iff_intro(c, And(X1, Z1), And(Y1, U1),
     lambda d: d.conj(fwd(d, 0, d.and_left(d.hyp(2))), fwd(d, 1, d.and_right(d.hyp(2)))),
     lambda d: d.conj(bwd(d, 0, d.and_left(d.hyp(2))), bwd(d, 1, d.and_right(d.hyp(2))))))
def or_c(d, i_l, i_r, fw):
    def ca(e): return e.app(or_left_ax(L, Y1 if fw else X1, U1 if fw else Z1), (fwd if fw else bwd)(e, 0, e.hyp(3)))
    def cb(e): return e.app(or_right_ax(L, Y1 if fw else X1, U1 if fw else Z1), (fwd if fw else bwd)(e, 1, e.hyp(3)))
    return d.cases(d.hyp(2), ca, cb)
hy = [Iff(X1, Y1), Iff(Z1, U1)]; c = Ctx(L, hy)
emit('d3p_orc', hy, Iff(Or(X1, Z1), Or(Y1, U1)), iff_intro(c, Or(X1, Z1), Or(Y1, U1),
     lambda d: or_c(d, 0, 1, True), lambda d: or_c(d, 0, 1, False)))
hy = [Iff(X1, Y1), Iff(Z1, U1)]; c = Ctx(L, hy)
def iffc(d, fw):     # d = G + Iff(A,B); produce Iff(A',B')
    A_, B_ = (Y1, U1) if fw else (X1, Z1)
    def ab(e):   # e: ... + A'  -> B'
        a0 = (bwd if fw else fwd)(e, 0, e.hyp(3))
        b0 = e.mp(e.and_left(e.hyp(2)), a0)
        return (fwd if fw else bwd)(e, 1, b0)
    def ba(e):
        b0 = (bwd if fw else fwd)(e, 1, e.hyp(3))
        a0 = e.mp(e.and_right(e.hyp(2)), b0)
        return (fwd if fw else bwd)(e, 0, a0)
    return d.conj(d.intro(ab(d.push(A_))), d.intro(ba(d.push(B_))))
emit('d3p_iffc', hy, Iff(Iff(X1, Z1), Iff(Y1, U1)), iff_intro(c, Iff(X1, Z1), Iff(Y1, U1),
     lambda d: iffc(d, True), lambda d: iffc(d, False)))

hdr = '''import "gen7_tf.mm1";

-- Route T (lanes/D3CHECK.md), TQ: propositional lemmas, generated by tools/gen7/d3/gen_tqp.py (do not edit).
'''
PA = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'pa-mm0'))
txt = hdr + '\n' + '\n'.join(items)
open(os.path.join(PA, 'gen7', 'd3_tqp.mm1'), 'w').write(txt.replace('bb215L3g_', 'g7L3g_'))
open(os.path.join(PA, 'gen7', 'd3_tqp.mm0'), 'w').write('import "gen7_tf.mm0";\n\n' + '\n'.join(specs) + '\n')
print('ok', len(items))
