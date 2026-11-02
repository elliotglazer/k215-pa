"""Term-graph vocabulary for the GEN7 C2 generators (engine formulas mirroring gen7_trpa's defs)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from g7nd import *   # noqa

TRUE = Imp(F, F)
E01 = Eq(v(0), v(1))
E10 = Eq(v(1), v(0))

def raise_(f): return rename_f(1, f)[0]
def lift(f): return rename_f(0, f)[0]

def P0(X): return Par(X, 0, 0)

def TFg(G):
    """trFun G for an engine graph G (slot 0)."""
    return Or(All(Iff(raise_(G), E01)), And(Not(Ex(All(Iff(raise_(raise_(G)), E01)))), Eq(v(0), Z)))

def TF(X): return TFg(P0(X))

def TotP(G): return Ex(raise_(G))
def FunP(G): return All(All(Imp(lift(raise_(G)), Imp(raise_(raise_(G)), E10))))
def Tot(X): return TotP(TF(X))
def Fun(X): return FunP(TF(X))
def TotG(G): return TotP(TFg(G))
def FunG(G): return FunP(TFg(G))

def Q1stmt(G):
    xv = raise_(G); xu = raise_(raise_(G))
    return All(Imp(And(xv, All(Imp(xu, E01))), raise_(TFg(G))))
def Q2stmt(G):
    return Imp(TotP(G), Imp(FunP(G), All(Imp(raise_(TFg(G)), raise_(G)))))

def EQg(G, H): return Ex(And(raise_(TFg(G)), raise_(TFg(H))))
def EQ(A, B): return EQg(P0(A), P0(B))
def EL(A, S): return Ex(And(raise_(TF(A)), Par(S, 1, 0)))

# term-constructor graphs (gen7_trpa: trZeroF, trSucF, trAddF, trMulF), arguments are graphs
GZ = Eq(v(0), Z)
def GS(G): return Ex(And(raise_(TFg(G)), Eq(v(1), S(v(0)))))
def GA(G, H): return Ex(And(raise_(TFg(G)), Ex(And(raise_(raise_(TFg(H))), Eq(v(2), A(v(1), v(0)))))))
def GM(G, H): return Ex(And(raise_(TFg(G)), Ex(And(raise_(raise_(TFg(H))), Eq(v(2), M(v(1), v(0)))))))

def check(a, b, msg):
    if a != b:
        raise NDError('%s:\n  %s\n  %s' % (msg, fm(a), fm(b)))

def inst2(c, h, t1, t2):
    """h: c.G -> A. A. body; instantiate the outer quantifier with t1, then the next with t2."""
    n = c.n
    r = c.app(all_elim_ax(n, h.f[2][1], t1), h)
    return c.app(all_elim_ax(n, r.f[2][1], t2), r)

# ---- instances of parameter lemmas at composite graphs ----
def par_conv(G, j, s):
    """(G', proof of paFormulaRename (g7F j s) 0 (fm G) = fm G') for an engine graph G at level Lv(1)."""
    assert s <= j, (j, s)
    hb = fbound(Lv(1), G)
    cur, p = G, '(eqcom (g7_par_id %s))' % hb
    jj, ss = 0, 0
    def step(e):
        nonlocal cur, p, jj, ss
        s2 = ss if ss < e else ss + 1
        nxt, q = rename_f(e, cur)
        lift_eq = '(g7_par_lift %s %s %s)' % (eng.rename_index(e, ss), numle(e, jj + 1), hb)
        p = '(eqtr (eqcom %s) (eqtr (paFormulaRenameeq3 %s) %s))' % (lift_eq, p, q)
        cur, jj, ss = nxt, jj + 1, s2
    for _ in range(j - s): step(1)
    for _ in range(s): step(0)
    assert (jj, ss) == (j, s)
    return cur, p

_EQN = {'and': 'And', 'or': 'Or', 'imp': 'Imp', 'all': 'All', 'ex': 'Ex'}
def subst_param(f, X, G):
    """f mentions Par(X, j, s). Returns (f1, f2, proof of fm f1 = fm f2) where f1 has Par(fm G, j, s)
    (the literal instance of a lemma about X) and f2 has G expanded."""
    c = f[0]
    if c == 'par':
        if f[1] != X: return f, f, 'eqid'
        g2, p = par_conv(G, f[2], f[3])
        return Par(fm(G), f[2], f[3]), g2, p
    if c in ('and', 'or', 'imp'):
        a1, a2, pa = subst_param(f[1], X, G); b1, b2, pb = subst_param(f[2], X, G)
        return (c, a1, b1), (c, a2, b2), '(paFormula%seq %s %s)' % (_EQN[c], pa, pb)
    if c in ('all', 'ex'):
        a1, a2, pa = subst_param(f[1], X, G)
        return (c, a1), (c, a2), '(paFormula%seq %s)' % (_EQN[c], pa)
    return f, f, 'eqid'

def inst_lemma(call, f, X, G):
    """call: MM1 term proving paProvable Lv(1) (f with X := fm G); returns Thm with G expanded.
    `call` must take the bound proof of G for the parameter X (see inst_call)."""
    f1, f2, p = subst_param(f, X, G)
    PARAMS.setdefault(fm(G), (fbound(Lv(1), G), 1))
    return Thm(Lv(1), f2, '(mpbi (paProvableeq2 %s) %s)' % (p, call))
