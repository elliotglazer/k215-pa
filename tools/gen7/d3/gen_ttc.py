"""Route T, TQ for terms: generates pa-mm0/gen7/d3_ttc.mm1 / .mm0. For a code graph X (the trPA of a named term
code) with  X <-> Y(A)  (Y(A) = (v0 = paTermLift 1 A), the hand graph), the trPA term constructors over X are
equivalent to the hand graphs of the hand terms:
  d3c_s:  (X <-> Y(A))                  ->  trSucF X    <-> Y(S A)
  d3c_a/m:(X <-> Y(A)) -> (Z <-> Y(B))  ->  trAddF X Z  <-> Y(A + B)   (trMulF, A * B)
  d3c_e:  (X <-> Y(A)) -> (Z <-> Y(B))  ->  trEqF X Z   <-> Lift 1 A = Lift 1 B
All at level suc n; X, Z bound by suc n, A, B by n."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'c2'))
sys.path.insert(0, HERE)
import tl
from tl import TL, TP
from tg import *   # noqa
import bb215_l3_engine as eng

BASE[0] = '(suc n)'
L = Lv(1)
for x in ('X', 'Z'):
    param(x, 'h' + x, 1)
for s in ('A', 'B'):
    TP[s] = 'h' + s
TRUEP = '(bb215D2_id paFormulaBound_false)'

def Y(s): return Eq(v(0), TL(s, 1))
def R(f): return rename_f(1, f)[0]

SH = {'ctx': None, 'k': 0, 'cache': {}}
def share(th, lim=1500):
    """Emit a long proof as a lemma with the current binders (SH['ctx'] = (binders, call args))."""
    if SH['ctx'] is None or len(th.proof) < lim: return th
    key = (int(th.n), th.f, th.proof)
    if key in SH['cache']: return SH['cache'][key]
    SH['k'] += 1
    binders, args = SH['ctx']
    name = 'd3cK_%d' % SH['k']
    items.append("theorem %s %s: $ paProvable %s %s $ =\n'%s;\n" % (name, binders, lvstr(int(th.n)), fm(th.f), th.proof))
    r = Thm(th.n, th.f, '(%s %s)' % (name, args))
    SH['cache'][key] = r
    return r

def rr_raise(th):
    F2, p = rename_f(1, th.f)
    return share(Thm(th.n + 1, F2, '(mpbi (paProvableeq2 %s) (d3_rr1 %s))' % (p, th.proof)))

def closed(n, fn):
    c = Ctx(n, [TRUE])
    return share(mp(Thm(n, TRUE, TRUEP), fn(c)))

def refl_iff(n, A_): return and_intro(ident(n, A_), ident(n, A_))
def split(h): return mp(h, and_left_ax(h.n, h.f[1], h.f[2])), mp(h, and_right_ax(h.n, h.f[1], h.f[2]))
def imp_c(n, p, q):       # p: A<->A', q: B<->B'  =>  (A->B) <-> (A'->B')
    A_, A2 = p.f[1][1], p.f[1][2]; B_, B2 = q.f[1][1], q.f[1][2]
    def b(c):
        P, Q = c.thm(p), c.thm(q)
        def ab(d):
            e = d.push(A2)
            a = e.mp(e.and_right(e.thm(p)), e.hyp(2))
            return d.intro(e.mp(e.and_left(e.thm(q)), e.mp(e.hyp(1), a)))
        def ba(d):
            e = d.push(A_)
            a = e.mp(e.and_left(e.thm(p)), e.hyp(2))
            return d.intro(e.mp(e.and_right(e.thm(q)), e.mp(e.hyp(1), a)))
        return c.conj(c.intro(ab(c.push(Imp(A_, B_)))), c.intro(ba(c.push(Imp(A2, B2)))))
    return closed(n, b)
def and_c(n, p, q):
    A_, A2 = p.f[1][1], p.f[1][2]; B_, B2 = q.f[1][1], q.f[1][2]
    def b(c):
        def ab(d):
            h = d.hyp(1)
            return d.conj(d.mp(d.and_left(d.thm(p)), d.and_left(h)), d.mp(d.and_left(d.thm(q)), d.and_right(h)))
        def ba(d):
            h = d.hyp(1)
            return d.conj(d.mp(d.and_right(d.thm(p)), d.and_left(h)), d.mp(d.and_right(d.thm(q)), d.and_right(h)))
        return c.conj(c.intro(ab(c.push(And(A_, B_)))), c.intro(ba(c.push(And(A2, B2)))))
    return closed(n, b)
def or_c(n, p, q):
    A_, A2 = p.f[1][1], p.f[1][2]; B_, B2 = q.f[1][1], q.f[1][2]
    def b(c):
        def ab(d):
            return d.cases(d.hyp(1),
                           lambda e: e.app(or_left_ax(n, A2, B2), e.mp(e.and_left(e.thm(p)), e.hyp(2))),
                           lambda e: e.app(or_right_ax(n, A2, B2), e.mp(e.and_left(e.thm(q)), e.hyp(2))))
        def ba(d):
            return d.cases(d.hyp(1),
                           lambda e: e.app(or_left_ax(n, A_, B_), e.mp(e.and_right(e.thm(p)), e.hyp(2))),
                           lambda e: e.app(or_right_ax(n, A_, B_), e.mp(e.and_right(e.thm(q)), e.hyp(2))))
        return c.conj(c.intro(ab(c.push(Or(A_, B_)))), c.intro(ba(c.push(Or(A2, B2)))))
    return closed(n, b)
def all_mono(h):
    return Thm(h.n - 1, Imp(All(h.f[1]), All(h.f[2])), '(paD0_all_mono_imp %s %s %s)' % (fbound(h.n, h.f[1]), fbound(h.n, h.f[2]), h.proof))
def ex_mono(h):
    k = int(h.n) - 1
    Xf, Yf = h.f[1], h.f[2]
    lY, _ = lift_f(Ex(Yf))
    w = ex_intro_imp(h.n, lY[1], v(0))
    need(w.f[1] == Yf, 'ex_mono: witness form')
    return ex_elim(Lv(k), Xf, Ex(Yf), syl(h, w))
def q_c(kind, p):         # p at n+1: A <-> A'  =>  Q A <-> Q A' at n
    a, b = split(p)
    m = all_mono if kind == 'all' else ex_mono
    return share(and_intro(m(a), m(b)))
def cong(n, A_, B_, table):
    key = (int(n), A_, B_)
    if key in table: return table[key]
    if A_ == B_: return refl_iff(n, A_)
    c = A_[0]
    need(c == B_[0], 'cong: heads differ %s / %s' % (fm(A_), fm(B_)))
    if c in ('imp', 'and', 'or'):
        p = cong(n, A_[1], B_[1], table); q = cong(n, A_[2], B_[2], table)
        r = {'imp': imp_c, 'and': and_c, 'or': or_c}[c](n, p, q)
        table[key] = r
        return r
    if c in ('all', 'ex'):
        return q_c(c, cong(n + 1, A_[1], B_[1], table))
    raise NDError('cong: no rule for %s / %s' % (fm(A_), fm(B_)))
def trans(p, q):          # A<->B, B<->C
    A_, B_ = p.f[1][1], p.f[1][2]; C_ = q.f[1][2]
    need(q.f[1][1] == B_, 'trans shape')
    def b(c):
        def ab(d): return d.mp(d.and_left(d.thm(q)), d.mp(d.and_left(d.thm(p)), d.hyp(1)))
        def ba(d): return d.mp(d.and_right(d.thm(p)), d.mp(d.and_right(d.thm(q)), d.hyp(1)))
        return c.conj(c.intro(ab(c.push(A_))), c.intro(ba(c.push(C_))))
    return closed(p.n, b)

def tf_iff(xname, s, hyp):
    """Thm L: TF(X) <-> Y(s) from hyp: L |- X <-> Y(s)."""
    X0 = P0(xname)
    r1 = rr_raise(hyp); r2 = rr_raise(r1)
    table = {(1, X0, Y(s)): hyp, (2, R(X0), R(Y(s))): r1, (3, R(R(X0)), R(R(Y(s)))): r2}
    cg = cong(L, TFg(X0), TFg(Y(s)), table)
    tfe = Thm(L, Iff(TFg(Y(s)), Y(s)), '(d3t_tfe_c h%s)' % s)
    return trans(cg, tfe)

items, specs = [], []
def emit(name, fps, tps, hyps, th, stmt_concl, conv):
    binders = '(n %s %s: nat) %s %s' % (' '.join(fps), ' '.join(tps),
        ' '.join('(h%s: $ paFormulaBound (suc n) %s $)' % (x, x) for x in fps),
        ' '.join('(h%s: $ paTermBound n %s $)' % (x, x) for x in tps))
    hb = ' '.join('(e%d: $ paProvable (suc n) %s $)' % (i, fm(f)) for i, f in enumerate(hyps))
    items.append("theorem %s_c %s %s: $ paProvable (suc n) %s $ =\n'%s;\n" % (name, binders, hb, fm(th.f), th.proof))
    # plain wrapper
    hp, call = [], '(%s_c %s' % (name, ' '.join('h' + x for x in fps + tps))
    for i, f in enumerate(hyps):
        ht = fm(f).replace(fm(P0('X')), 'X').replace(fm(P0('Z')), 'Z')
        hp.append('(e%d: $ paProvable (suc n) %s $)' % (i, ht))
        call += ' (mpbi (paProvableeq2 (trIffeq (g7_par_id h%s) eqid)) e%d)' % ('X' if i == 0 else 'Z', i)
    call += ')'
    stmt = 'theorem %s %s %s: $ paProvable (suc n) %s $' % (name, binders, ' '.join(hp), stmt_concl)
    items.append("pub %s =\n'(mpbir (paProvableeq2 %s) %s);\n" % (stmt, conv, call))
    specs.append(stmt + ';')

X0, Z0 = P0('X'), P0('Z')
YA, YB = Y('A'), Y('B')
def ctx_for(fps, tps, nh):
    binders = '(n %s %s: nat) %s %s %s' % (' '.join(fps), ' '.join(tps),
        ' '.join('(h%s: $ paFormulaBound (suc n) %s $)' % (x, x) for x in fps),
        ' '.join('(h%s: $ paTermBound n %s $)' % (x, x) for x in tps),
        ' '.join('(e%d: $ paProvable (suc n) %s $)' % (i, fm(Iff(P0(fps[i]), Y(tps[i])))) for i in range(nh)))
    args = ' '.join(['h' + x for x in fps + tps] + ['e%d' % i for i in range(nh)])
    SH['ctx'] = (binders, args); SH['cache'] = {}
eX = Thm(L, Iff(X0, YA), 'e0'); eZ = Thm(L, Iff(Z0, YB), 'e1')
ctx_for(['X'], ['A'], 1)
tX = tf_iff('X', 'A', eX)
rX = rr_raise(tX)                     # Lv2: R(TF X) <-> R(Y A)
def lift_y(s): return '(paFormulaEqual (paTermVariable 0) (paTermLift 1 %s))' % s

# succ
gs = GS(X0)
hand_s = Ex(And(R(YA), Eq(v(1), S(v(0)))))
cg = cong(L, gs, hand_s, {(2, R(TFg(X0)), R(YA)): rX})
hs = Thm(L, Iff(hand_s, Eq(v(0), S(TL('A', 1)))), '(d3t_hs_c hA)')
th = trans(cg, hs)
conv = '(trIffeq (paFormulaExeq (paFormulaAndeq (g7_raiseTF_E hX) eqid)) (paFormulaEqualeq eqid paTermRename_successor))'
emit('d3c_s', ['X'], ['A'], [Iff(X0, YA)], th, '(trIff (trSucF X) %s)' % lift_y('(paTermSuccessor A)'), conv)

ctx_for(['X', 'Z'], ['A', 'B'], 2)
tX = tf_iff('X', 'A', eX); tZ = tf_iff('Z', 'B', eZ)
rX = rr_raise(tX)
rZ = rr_raise(tZ)
rrZ = rr_raise(rZ)                    # Lv3: R(R(TF Z)) <-> R(R(Y B))
def rrtf(name):   # proof of paAxiomRaiseParameters (paAxiomRaiseParameters (trFun Z)) = fm(R(R(TFg(P0 Z))))
    rt = R(TFg(P0(name)))
    _, p = rename_f(1, rt)
    return '(eqtr (paFormulaRenameeq3 (g7_raiseTF_E h%s)) %s)' % (name, p)
for nm, op, gfun, NM, ren in (('d3c_a', 'a', GA, 'paTermAddition', 'paTermRename_addition'),
                              ('d3c_m', 'm', GM, 'paTermMultiplication', 'paTermRename_multiplication')):
    g = gfun(X0, Z0)
    hand = Ex(And(R(YA), Ex(And(R(R(YB)), Eq(v(2), (op, v(1), v(0)))))))
    cg = cong(L, g, hand, {(2, R(TFg(X0)), R(YA)): rX, (3, R(R(TFg(Z0))), R(R(YB))): rrZ})
    hh = Thm(L, Iff(hand, Eq(v(0), (op, TL('A', 1), TL('B', 1)))), '(%s_c hA hB)' % ('d3t_ha' if op == 'a' else 'd3t_hm'))
    th = trans(cg, hh)
    conv = '(trIffeq (paFormulaExeq (paFormulaAndeq (g7_raiseTF_E hX) (paFormulaExeq (paFormulaAndeq %s eqid)))) (paFormulaEqualeq eqid %s))' % (rrtf('Z'), ren)
    emit(nm, ['X', 'Z'], ['A', 'B'], [Iff(X0, YA), Iff(Z0, YB)], th,
         '(trIff (%s X Z) %s)' % ('trAddF' if op == 'a' else 'trMulF', lift_y('(%s A B)' % NM)), conv)

# equality atom
g = EQg(X0, Z0)
hand = Ex(And(R(YA), R(YB)))
cg = cong(L, g, hand, {(2, R(TFg(X0)), R(YA)): rX, (2, R(TFg(Z0)), R(YB)): rZ})
hh = Thm(L, Iff(hand, Eq(TL('A', 1), TL('B', 1))), '(d3t_he_c hA hB)')
th = trans(cg, hh)
conv = '(trIffeq (g7_EQ_E hX hZ) eqid)'
emit('d3c_e', ['X', 'Z'], ['A', 'B'], [Iff(X0, YA), Iff(Z0, YB)], th,
     '(trIff (trEqF X Z) (paFormulaEqual (paTermLift 1 A) (paTermLift 1 B)))', conv)

hdr = '''import "d3_tt.mm1";
import "gen7_conv.mm1";

-- Route T (lanes/D3CHECK.md), TQ for terms: trPA term graphs vs hand graphs. Generated by tools/gen7/d3/gen_ttc.py.
'''
PA = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'pa-mm0'))
open(os.path.join(PA, 'gen7', 'd3_ttc.mm1'), 'w').write((hdr + '\n' + '\n'.join(items)).replace('bb215L3g_', 'g7L3g_') +
    "\npub theorem d3_ttc_final: $ paFormulaBound 0 paFormulaFalse $ = 'paFormulaBound_false;\n")
open(os.path.join(PA, 'gen7', 'd3_ttc.mm0'), 'w').write('import "d3_tt.mm0";\nimport "gen7_conv.mm0";\n\n' + '\n'.join(specs) +
    '\ntheorem d3_ttc_final: $ paFormulaBound 0 paFormulaFalse $;\n')
print('ok', sum(len(x) for x in items))
