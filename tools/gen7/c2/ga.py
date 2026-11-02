"""Graph algebra for the GEN7 C2 arithmetic generators: graph specs, their facts (as hypotheses of a
root context, discharged by the lemmas of gen7_tf / gen7_tf2 / gen7_tg), and ND helpers."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tg import *   # noqa

BASE[0] = '(suc n)'
L = Lv(1)
NAMES = ['A', 'B', 'C', 'D']
for X in NAMES + ['X', 'Y']:
    param(X, 'h' + X, 1)
HB = '(n A B C D: nat) ' + ' '.join('(h%s: $ paFormulaBound (suc n) %s $)' % (x, x) for x in NAMES)
HCALL = ' '.join('h' + x for x in NAMES)

# lemma templates over parameters X, Y (built before any proof sharing is switched on)
GX, GY = P0('X'), P0('Y')
TEMPL = {
    ('Z', 'tot'): ('g7_gz_tot', TotP(GZ)), ('Z', 'fun'): ('g7_gz_fun', FunP(GZ)),
    ('S', 'tot'): ('g7_gs_tot', TotP(GS(GX))), ('S', 'fun'): ('g7_gs_fun', FunP(GS(GX))),
    ('+', 'tot'): ('g7_ga_tot', TotP(GA(GX, GY))), ('+', 'fun'): ('g7_ga_fun', FunP(GA(GX, GY))),
    ('*', 'tot'): ('g7_gm_tot', TotP(GM(GX, GY))), ('*', 'fun'): ('g7_gm_fun', FunP(GM(GX, GY))),
}
Q1X, Q2X = Q1stmt(GX), Q2stmt(GX)

def build(sp):
    k = sp[0]
    if k == 'Z': return GZ
    if k == 'S': return GS(build(sp[1]))
    if k == '+': return GA(build(sp[1]), build(sp[2]))
    if k == '*': return GM(build(sp[1]), build(sp[2]))
    return P0(k)

def rename_param(f, X, A):
    c = f[0]
    if c == 'par': return Par(A, f[2], f[3]) if f[1] == X else f
    if c in ('and', 'or', 'imp'): return (c, rename_param(f[1], X, A), rename_param(f[2], X, A))
    if c in ('all', 'ex'): return (c, rename_param(f[1], X, A))
    return f

def inst_template(name, f, args):
    """Instance of lemma `name` (params X, Y) at graph specs args = [sx, sy]."""
    hyps, form, convs = [], f, []
    for X, sp in zip(['X', 'Y'], args):
        if sp is None:
            hyps.append('hA'); continue
        if sp[0] in NAMES:
            hyps.append('h' + sp[0]); form = rename_param(form, X, sp[0]); continue
        G = build(sp)
        hyps.append(fbound(L, G))
        convs.append((X, G))
    proof = '(%s %s)' % (name, ' '.join(hyps))
    for X, G in convs:
        f1, f2, p = subst_param(form, X, G)
        proof = '(mpbi (paProvableeq2 %s) %s)' % (p, proof)
        form = f2
    return Thm(L, form, proof)

class Facts:
    """Closed facts at level L (for a parameter graph: Tot / Fun of its trFun; for a composite graph G:
    Q2'(G): A. v (trFun G (v) -> G(v)), Q1(G) and FunP(G)), lifted on demand to the level of a
    context by the rename rule (g7_lift_rule), so contexts stay small."""
    K = [0]
    PFX = ['g7fact']
    def __init__(self, out=None):
        self.thms, self.cache, self.out = {}, {}, out
    def _share(self, th):
        if self.out is None or len(th.proof) < 1500: return th
        Facts.K[0] += 1
        name = '%s_%d' % (Facts.PFX[0], Facts.K[0])
        self.out.lemma(name, th, binders=' ' + HB)
        return Thm(th.n, th.f, '(%s %s)' % (name, HCALL))
    def add(self, key, th):
        if key not in self.thms: self.thms[key] = self._share(th)
    def need(self, sp):
        k = sp[0]
        if k in NAMES:
            self.add(('tot', sp), Thm(L, Tot(k), '(g7_tf_total h%s)' % k))
            self.add(('fun', sp), Thm(L, Fun(k), '(g7_tf_fun h%s)' % k))
            return
        args = list(sp[1:]) + [None] * (3 - len(sp))
        T = inst_template(TEMPL[(k, 'tot')][0], TEMPL[(k, 'tot')][1], args[:2])
        U = inst_template(TEMPL[(k, 'fun')][0], TEMPL[(k, 'fun')][1], args[:2])
        G = build(sp)
        check(T.f, TotP(G), 'facts tot'); check(U.f, FunP(G), 'facts fun')
        T = self._share(T); U = self._share(U)
        q2 = inst_lemma('(g7_tf_q2 %s)' % fbound(L, G), Q2X, 'X', G)
        q2 = mp(U, mp(T, q2))
        q1 = inst_lemma('(g7_tf_q1 %s)' % fbound(L, G), Q1X, 'X', G)
        self.add(('q2', sp), q2); self.add(('q1', sp), q1); self.add(('fun', sp), U); self.add(('tot', sp), T)
    def at(self, key, n):
        k = int(n)
        if (key, k) in self.cache: return self.cache[(key, k)]
        if k == 1: th = self.thms[key]
        else:
            prev = self.at(key, Lv(k - 1))
            f2, p = rename_f(0, prev.f)
            th = self._share(Thm(Lv(k), f2, '(mpbi (paProvableeq2 %s) (g7_lift_rule %s))' % (p, prev.proof)))
        self.cache[(key, k)] = th
        return th
    def h(self, c, key): return c.thm(self.at(key, c.n))
    def ctx(self, extra):
        return Ctx(L, list(extra) if extra else [TRUE])
    def discharge(self, th, nextra):
        if nextra == 0: return mp(ident(L, F), th)
        for _ in range(nextra - 1): th = export(th)
        return th

def inst_at(c, h, t):
    return c.app(all_elim_ax(c.n, h.f[2][1], t), h)

def inst_match(c, h, ante):
    """h: c.G -> A. (P -> Q); find the variable t with P[t] = ante; return c.G -> (ante -> Q[t])."""
    for i in range(int(c.n) - 1 + 4):
        try:
            r = inst_at(c, h, v(i))
        except Exception:
            continue
        if r.f[2][1] == ante: return r
    raise NDError('inst_match: no instance for %s' % fm(ante))

def cut(c, th, fn):
    c2 = c.push(th.f[2])
    return c.mp(c.intro(fn(c2)), th)

def name_term(c, t):
    return c.witness(Eq(v(0), shift_t(t, 1)), t, c.refl(t))

def tf_out(c, fx, sp, h_tf):
    """From c -> trFun G (t) infer c -> G(t)  (G composite)."""
    q2 = fx.h(c, ('q2', sp))
    r = inst_match(c, q2, h_tf.f[2])
    return c.mp(r, h_tf)

def tf_in(c, fx, sp, h_g):
    """From c -> G(t) infer c -> trFun G (t)  (G composite)."""
    q1 = fx.h(c, ('q1', sp))
    def body(cc):
        gt = cc.hyp(len(cc.hyps) - 1)
        # find t with Q1 instance antecedent's left part = G(t)
        for i in range(int(cc.n) - 1 + 4):
            try:
                r = inst_at(cc, fx.h(cc, ('q1', sp)), v(i))
            except Exception:
                continue
            if r.f[2][1][1] == gt.f[2]: break
        else:
            raise NDError('tf_in: no instance')
        uniq = r.f[2][1][2]                      # A. (G(u) -> u = t')
        cl = cc.lifted()
        gu = uniq[1][1]
        c2 = cl.push(gu)
        fun = fx.h(c2, ('fun', sp))
        e = None
        for j in range(int(c2.n) - 1 + 4):
            try:
                ins = inst2(c2, fun, v(0), v(j))
            except Exception:
                continue
            if ins.f[2][1] == gu and ins.f[2][2][1] == c2.hyp(len(cc.hyps) - 1).f[2]:
                e = c2.mp(c2.mp(ins, c2.hyp(len(c2.hyps) - 1)), c2.hyp(len(cc.hyps) - 1))
                break
        if e is None: raise NDError('tf_in: fun instance')
        bd = cl.intro(e)
        un = all_intro_hyp(cc.n, cc.G, Thm(cl.n, Imp(lift(cc.G), bd.f[2]), bd.proof))
        check(un.f[2], uniq, 'tf_in uniq')
        return cc.mp(r, cc.conj(gt, un))
    return cut(c, h_g, body)

def g_at(G, k, t):
    """G (a graph at level L) at level L + k with its slot := variable t."""
    for _ in range(k): G = raise_(G)
    return subst_f(0, t, raise_(G))[0]


def mk_gs(c, G, t, tu, u, eq):
    """c -> G(t) for G = GS(_): witness u with tu: TF(u) and eq: t = S u."""
    outer = g_at(G, int(c.n) - 1, v(t))
    return c.witness(outer[1], v(u), c.conj(tu, eq))

def mk_gop(c, G, t, tu, u, tw, w, eq):
    """c -> G(t) for G = GA/GM(_, _): witnesses u, w with tu, tw and eq: t = u op w."""
    outer = g_at(G, int(c.n) - 1, v(t))
    ob = outer[1]
    iob = subst_f(0, v(u), ob)[0]
    ib = iob[2][1]
    p_in = c.witness(ib, v(w), c.conj(tw, eq))
    return c.witness(ob, v(u), c.conj(tu, p_in))

def liftn(f, k):
    for _ in range(k): f = lift(f)
    return f

# ---- conversions: official expressions (gen7_trpa defs over parameters) -> generator form ----
def conv_trFun(pY, G):
    """pY: Y = fm G. Proof of paAxiomRaiseParameters (trFun Y) = fm(raise_ TFg G)."""
    r1, q1 = rename_f(1, G)
    R1 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (pY, q1)
    r2, q2 = rename_f(1, r1)
    R2 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (R1, q2)
    TFeq = '(paFormulaOreq (paFormulaAlleq (trIffeq %s eqid)) (paFormulaAndeq (trNoteq (paFormulaExeq (paFormulaAlleq (trIffeq %s eqid)))) eqid))' % (R1, R2)
    rt, q3 = rename_f(1, TFg(G))
    return '(eqtr (paFormulaRenameeq3 %s) %s)' % (TFeq, q3)

def conv(sp):
    """(official expression, engine graph, proof official = fm graph)."""
    k = sp[0]
    if k in NAMES: return k, P0(k), '(g7_par_id h%s)' % k
    if k == 'Z': return 'trZeroF', GZ, 'eqid'
    if k == 'S':
        o, G, p = conv(sp[1])
        return '(trSucF %s)' % o, GS(G), '(paFormulaExeq (paFormulaAndeq %s eqid))' % conv_trFun(p, G)
    o1, G1, p1 = conv(sp[1]); o2, G2, p2 = conv(sp[2])
    rt2 = conv_trFun(p2, G2)
    rr, q = rename_f(1, raise_(TFg(G2)))
    rrt2 = '(eqtr (paFormulaRenameeq3 %s) %s)' % (rt2, q)
    nm = 'trAddF' if k == '+' else 'trMulF'
    G = GA(G1, G2) if k == '+' else GM(G1, G2)
    return '(%s %s %s)' % (nm, o1, o2), G, '(paFormulaExeq (paFormulaAndeq %s (paFormulaExeq (paFormulaAndeq %s eqid))))' % (conv_trFun(p1, G1), rrt2)

def conv_EQ(s1, s2):
    """(official trEqF expression, engine EQg, proof)."""
    o1, G1, p1 = conv(s1); o2, G2, p2 = conv(s2)
    return '(trEqF %s %s)' % (o1, o2), EQg(G1, G2), '(paFormulaExeq (paFormulaAndeq %s %s))' % (conv_trFun(p1, G1), conv_trFun(p2, G2))

def code_eq(sp):
    """Proof of trPA <code> = <official expression> where the code of a parameter A is the variable
    whose translation is A (trPA vK appears literally as the parameter)."""
    k = sp[0]
    if k in NAMES: return 'eqid'
    if k == 'Z': return 'trPA_c0'
    if k == 'S': return '(eqtr trPA_cSuc (trSucFeq %s))' % code_eq(sp[1])
    nm = 'Add' if k == '+' else 'Mul'
    return '(eqtr trPA_c%s (tr%sFeq %s %s))' % (nm, nm, code_eq(sp[1]), code_eq(sp[2]))
