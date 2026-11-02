"""Binder support for the GEN7 C2 generators: symbolic name variables (Sym), the binding renames
trAbs (suc x) / trCls (suc x) pushed through engine formulas (gen7_abs), and the conversion of a
named code to its engine formula with a proof  trPA code = fm E  (gen7_trpa equations)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ga import *   # noqa

TPB = {}     # code var -> proof of paFormulaBound (suc n) (trPA v)
FRESH = {}   # (param string, var name) -> proof of trFr (suc var) param
NE = {}      # (y, x) -> proof of y != x
_EQN2 = {'and': 'And', 'or': 'Or', 'imp': 'Imp', 'all': 'All', 'ex': 'Ex'}


def bind_index(kind, x, d, i):
    """(i', proof of sfRenameIndex (MAP (suc x)) d i = i'), MAP = trAbsMap / trClsMap."""
    if not isinstance(i, Sym):
        assert i < d, (i, d)
        return i, '(sfRenameIndex_bound %s)' % eng.lt(i, d)
    assert i.off >= d + 1, (i, d)
    if d > 0:
        r, p = bind_index(kind, x, d - 1, i - 1)
        return r + 1, '(eqtr sfRenameIndex_lift (suceq %s))' % p
    if i.name == x:
        assert i.off == 1, i
        return 0, '(eqtr sfRenameIndex_zero g7_%s_hit)' % kind
    assert i.off == 1, i
    ne = '(g7_sucne %s)' % NE[(i.name, x)]
    if kind == 'abs': return i + 1, '(eqtr sfRenameIndex_zero (g7_abs_miss %s))' % ne
    return i, '(eqtr sfRenameIndex_zero (g7_cls_miss %s))' % ne


def bind_t(kind, x, d, u):
    c = u[0]
    if c == 'num': return u, 'bb215ArithmeticSentenceNumeral_rename'
    if c == 'v':
        r, p = bind_index(kind, x, d, u[1])
        return v(r), '(eqtr paTermRename_variable (paTermVariableeq (eqtr sfRenameDepthMap_value %s)))' % p
    if c == 'z': return u, 'paTermRename_zero'
    if c == 's':
        r, p = bind_t(kind, x, d, u[1]); return S(r), '(eqtr paTermRename_successor (paTermSuccessoreq %s))' % p
    r1, p1 = bind_t(kind, x, d, u[1]); r2, p2 = bind_t(kind, x, d, u[2])
    if c == 'a': return A(r1, r2), '(eqtr paTermRename_addition (paTermAdditioneq %s %s))' % (p1, p2)
    return M(r1, r2), '(eqtr paTermRename_multiplication (paTermMultiplicationeq %s %s))' % (p1, p2)


def bind_f(kind, x, d, f):
    """(f', proof of paFormulaRename (MAP (suc x)) d (fm f) = fm f')."""
    c = f[0]
    if c == 'eq':
        r1, p1 = bind_t(kind, x, d, f[1]); r2, p2 = bind_t(kind, x, d, f[2])
        return Eq(r1, r2), '(eqtr paFormulaRename_equal (paFormulaEqualeq %s %s))' % (p1, p2)
    if c in ('or', 'and', 'imp'):
        r1, p1 = bind_f(kind, x, d, f[1]); r2, p2 = bind_f(kind, x, d, f[2])
        return (c, r1, r2), '(eqtr paFormulaRename_%s (paFormula%seq %s %s))' % (c, _EQN2[c], p1, p2)
    if c in ('all', 'ex'):
        r, p = bind_f(kind, x, d + 1, f[1])
        return (c, r), '(eqtr paFormulaRename_%s (paFormula%seq %s))' % (c, _EQN2[c], p)
    if c == 'f': return f, 'paFormulaRename_false'
    if c == 'par':
        X, j, s = f[1], f[2], f[3]
        assert j == d, (f, d)
        s2, ps = bind_index(kind, x, d, s)
        hX = PARAMS[X][0]
        fr = FRESH[(X, x)]
        if kind == 'abs': return Par(X, j + 1, s2), '(g7_abs_par %s %s %s)' % (ps, hX, fr)
        return Par(X, j, s2), '(g7_cls_par %s %s %s)' % (ps, hX, fr)
    raise ValueError(f)


# ---- codes ----
# ('Im', a, b) ('Not', a) ('Al', x, a) ('Eq', a, b) ('El', a, s) ('Ab', x, a) ('V', x) ('Z0',)
# ('Suc', a) ('The', a) ('Add', a, b) ('Mul', a, b) ('Tru',)
# ('tp', code-var)          a term / class code variable  (param string (trPA v))
# ('fp', code-var)          a formula code variable       (param string (trJ (trPA v)))
# ('zp', code-var, x)       a formula code variable used through its class at name x
def code_str(c):
    k = c[0]
    if k in ('tp', 'fp', 'zp'): return c[1]
    if k == 'V': return '(cV %s)' % c[1]
    if k == 'Z0': return 'c0'
    if k == 'Tru': return 'cTru'
    if k in ('Al', 'Ab'): return '(c%s %s %s)' % (k, c[1], code_str(c[2]))
    return '(c%s %s)' % (k, ' '.join(code_str(a) for a in c[1:]))

def tp(v): return '(trPA %s)' % v
def fp(v): return '(trJ (trPA %s))' % v
def zp(v, x): return '(trCls (suc %s) (trJ (trPA %s)))' % (x, v)

def TFfm(pY, G):
    """pY: Y = fm G. Proof of trFun Y = fm (TFg G)."""
    r1, q1 = rename_f(1, G)
    R1 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (pY, q1)
    r2, q2 = rename_f(1, r1)
    R2 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (R1, q2)
    return '(paFormulaOreq (paFormulaAlleq (trIffeq %s eqid)) (paFormulaAndeq (trNoteq (paFormulaExeq (paFormulaAlleq (trIffeq %s eqid)))) eqid))' % (R1, R2)

TJ_LEM = {'Im': 'g7_tJ_cIm', 'Not': 'g7_tJ_cNot', 'Al': 'g7_tJ_cAl', 'Eq': 'g7_tJ_cEq', 'El': 'g7_tJ_cEl'}

def TJ(c):
    """(E, proof of trJ (trPA c) = fm E) for a code in formula position."""
    k = c[0]
    if k == 'fp': return P0(fp(c[1])), '(g7_par_id %s)' % PARAMS[fp(c[1])][0]
    if k == 'zp':
        Zs = zp(c[1], c[2]); P = fp(c[1])
        return Par(Zs, 0, Sym(c[2], 1)), '(g7_ZP (g7_fr_J0 %s) %s)' % (TPB[c[1]], PARAMS[P][0])
    E, p = T(c)
    return E, '(eqtr %s %s)' % (TJ_LEM[k], p)

def T(c):
    """(E, proof of trPA c = fm E)."""
    k = c[0]
    if k == 'tp': return P0(tp(c[1])), '(g7_par_id %s)' % PARAMS[tp(c[1])][0]
    if k == 'Im':
        a, pa = TJ(c[1]); b, pb = TJ(c[2])
        return Imp(a, b), '(eqtr trPA_cIm (paFormulaImpeq %s %s))' % (pa, pb)
    if k == 'Not':
        a, pa = TJ(c[1])
        return Not(a), '(eqtr trPA_cNot (trNoteq %s))' % pa
    if k == 'Tru': return Imp(F, F), 'trPA_cTru'
    if k == 'Al':
        a, pa = TJ(c[2])
        b, pb = bind_f('abs', c[1], 0, a)
        return All(b), '(eqtr trPA_cAl (paFormulaAlleq (eqtr (paFormulaRenameeq3 %s) %s)))' % (pa, pb)
    if k == 'Ab':
        a, pa = TJ(c[2])
        b, pb = bind_f('cls', c[1], 0, a)
        return b, '(eqtr trPA_cAb (eqtr (paFormulaRenameeq3 %s) %s))' % (pa, pb)
    if k == 'Eq':
        a, pa = T(c[1]); b, pb = T(c[2])
        return EQg(a, b), '(eqtr trPA_cEq (paFormulaExeq (paFormulaAndeq %s %s)))' % (conv_trFun(pa, a), conv_trFun(pb, b))
    if k == 'El':
        a, pa = T(c[1]); s, ps = T(c[2])
        rs, qs = rename_f(1, s)
        return Ex(And(raise_(TFg(a)), rs)), '(eqtr trPA_cEl (paFormulaExeq (paFormulaAndeq %s (eqtr (paFormulaRenameeq3 %s) %s))))' % (
            conv_trFun(pa, a), ps, qs)
    if k == 'V': return Eq(v(0), v(Sym(c[1], 1))), 'trPA_cV'
    if k == 'Z0': return GZ, 'trPA_c0'
    if k == 'Suc':
        a, pa = T(c[1])
        return GS(a), '(eqtr trPA_cSuc (paFormulaExeq (paFormulaAndeq %s eqid)))' % conv_trFun(pa, a)
    if k == 'The':
        a, pa = T(c[1])
        return TFg(a), '(eqtr trPA_cThe %s)' % TFfm(pa, a)
    if k in ('Add', 'Mul'):
        a, pa = T(c[1]); b, pb = T(c[2])
        rt2 = conv_trFun(pb, b)
        rr, q = rename_f(1, raise_(TFg(b)))
        rrt2 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (rt2, q)
        G = GA(a, b) if k == 'Add' else GM(a, b)
        return G, '(eqtr trPA_c%s (paFormulaExeq (paFormulaAndeq %s (paFormulaExeq (paFormulaAndeq %s eqid)))))' % (
            k, conv_trFun(pa, a), rrt2)
    raise ValueError(c)


# ---- registration of code parameters ----
def reg_tp(vv, hyp):
    TPB[vv] = hyp
    param(tp(vv), hyp, 1)
def reg_fp(vv, hyp):
    TPB[vv] = hyp
    param(fp(vv), '(g7_J_bound %s)' % hyp, 1)
def reg_zp(vv, x):
    P = fp(vv); hP = PARAMS[P][0]
    param(zp(vv, x), '(g7_cls_bound %s)' % hP, 1)
    FRESH[(zp(vv, x), x)] = '(g7_fr_cls_self %s)' % hP
def fresh_tp(vv, x, hyp): FRESH[(tp(vv), x)] = hyp
def fresh_fp(vv, x, hyp):
    """hyp: trFr (suc x) (trPA vv)."""
    FRESH[(fp(vv), x)] = '(g7_fr_J %s %s)' % (TPB[vv], hyp)
def fresh_zp(vv, y, x):
    """class of vv at y, fresh for x (needs FRESH[(fp vv, x)])."""
    FRESH[(zp(vv, y), x)] = '(g7_fr_cls %s %s)' % (PARAMS[fp(vv)][0], FRESH[(fp(vv), x)])


# ---- engine helpers ----
def all_in(c, fn):
    """c -> A. phi from fn(c.lifted()) : lifted -> phi."""
    cl = c.lifted()
    th = fn(cl)
    return all_intro_hyp(c.n, c.G, Thm(cl.n, Imp(lift(c.G), th.f[2]), th.proof))

def all_iff_refl(c, target):
    """c -> target, target = A. (X <-> X)."""
    body = target[1]
    need(target[0] == 'all' and body[0] == 'and' and body[1][1] == body[1][2] and body[2] == body[1], 'all_iff_refl %s' % fm(target))
    i = ident(c.n + 1, body[1][1])
    return c.thm(gen(and_intro(i, i)))

def tf_self(c, target):
    """c -> TFg(Eq(v0, t))(t) (left disjunct)."""
    need(target[0] == 'or', 'tf_self')
    return c.app(or_left_ax(c.n, target[1], target[2]), all_iff_refl(c, target[1]))

def tf_var_out(c, h):
    """h: c -> TFg(Eq(v0, t))(w); returns c -> w = t."""
    f = h.f[2]
    need(f[0] == 'or', 'tf_var_out')
    t = shift_t(f[1][1][1][1][2], -1)
    w = f[2][2][1]
    goal = Eq(w, t)
    def fa(ca):
        r = inst_at(ca, ca.hyp(len(ca.hyps) - 1), t)
        tw = ca.mp(ca.and_left(r), ca.refl(t))
        res = ca.sym(tw)
        check(res.f[2], goal, 'tf_var_out a')
        return res
    def fb(cb):
        nex = cb.and_left(cb.hyp(len(cb.hyps) - 1))
        B = nex.f[2][1][1]
        inst = subst_f(0, t, B)[0]
        wit = cb.witness(B, t, all_iff_refl(cb, inst))
        return cb.absurd(cb.mp(nex, wit), goal)
    return c.cases(h, fa, fb)

def fun_eq(c, fun, h1, h2):
    """fun: c -> A. A. (G(v1) -> G(v0) -> v1 = v0); h1: c -> G(s), h2: c -> G(t); c -> s = t."""
    for i in range(int(c.n) + 4):
        for j in range(int(c.n) + 4):
            try:
                ins = inst2(c, fun, v(i), v(j))
            except Exception:
                continue
            if ins.f[2][1] == h1.f[2] and ins.f[2][2][1] == h2.f[2]:
                return c.mp(c.mp(ins, h1), h2)
    ins = inst2(c, fun, v(0), v(1))
    raise NDError("fun_eq: no instance\n%s\n%s\n%s\n%s" % (fm(h1.f[2]), fm(h2.f[2]), fm(ins.f[2][1]), fm(ins.f[2][2][1])))

def eqsub(c, eq, h, target):
    """eq: c -> b = d; h: c -> Par(Z, j, b); target Par(Z, j, d)."""
    hf = h.f[2]
    need(hf[0] == 'par' and target[0] == 'par' and hf[1] == target[1] and hf[2] == target[2], 'eqsub shape')
    a = Par(hf[1], hf[2] + 1, 0)
    b, d = eq.f[2][1], eq.f[2][2]
    th = eqsubst_ax(c.n, a, b, d)
    check(th.f[2][1], hf, 'eqsub a[b]'); check(th.f[2][2], target, 'eqsub a[d]')
    return c.mp(c.mp(c.thm(th), eq), h)


def tf_gs_var(c, target):
    """c -> TFg(GS(Eq(v0, x)))(S x) (left disjunct)."""
    need(target[0] == 'or', 'tf_gs_var')
    left = target[1]
    phi = left[1]
    Gw, eqw = phi[1][1], phi[1][2]
    xt = eqw[2][1]
    def body(cl):
        c1 = cl.push(Gw)
        def f(c2):
            h = c2.hyp(len(c2.hyps) - 1)
            e = tf_var_out(c2, c2.and_left(h))
            r = c2.trans(c2.and_right(h), c2.succ(e))
            check(r.f[2], lift(eqw), 'tf_gs_var 1')
            return r
        i1 = cl.intro(c1.exists(c1.hyp(len(c1.hyps) - 1), eqw, f))
        c3 = cl.push(eqw)
        B = Gw[1]
        want = subst_f(0, xt, B)[0]
        p = c3.conj(tf_self(c3, want[1]), c3.hyp(len(c3.hyps) - 1))
        check(p.f[2], want, 'tf_gs_var 2')
        i2 = cl.intro(c3.witness(B, xt, p))
        return cl.conj(i1, i2)
    a = all_in(c, body)
    return c.app(or_left_ax(c.n, left, target[2]), a)
