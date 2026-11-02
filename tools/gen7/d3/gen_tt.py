"""Route T (lanes/D3CHECK.md), TQ for terms: generates pa-mm0/gen7/d3_tt.mm1 / .mm0.
Hand graph of a hand term:  Y(S) = (v0 = paTermLift 1 S)  (value variable 0, S bound n, level suc n).
Lemmas (level suc n):
  d3t_tfe:  trFun Y(S) <-> Y(S)                                  (trFun is the identity on a hand graph)
  d3t_hs:   E. (raise Y(S) /\\ v1 = S v0)            <-> v0 = Lift 1 (S S)
  d3t_ha/m: E. (raise Y(A) /\\ E. (raise raise Y(B) /\\ v2 = v1 op v0)) <-> v0 = Lift 1 (A op B)
  d3t_he:   E. (raise Y(A) /\\ raise Y(B))           <-> Lift 1 A = Lift 1 B
(raise = paAxiomRaiseParameters). The trPA term graphs trSucF / trAddF / trMulF / trEqF have exactly these
shapes with trFun in front of each argument graph (gen7_trpa)."""
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
param('X', 'hX', 1)
for s in ('S', 'A', 'B'):
    TP[s] = 'h' + s

def Y(s): return Eq(v(0), TL(s, 1))
def R(f): return rename_f(1, f)[0]

def iff_intro(c, A_, B_, fab, fba):
    return c.conj(c.intro(fab(c.push(A_))), c.intro(fba(c.push(B_))))

items, specs = [], []
def emit(name, tvars, stmt_txt, th, conv):
    """th: engine Thm (closed, level L) proving fm(th.f); conv: proof of stmt_txt-formula = fm(th.f) (or None)."""
    binders = '(n %s: nat) %s' % (' '.join(tvars), ' '.join('(h%s: $ paTermBound n %s $)' % (x, x) for x in tvars))
    items.append("theorem %s_c %s: $ paProvable (suc n) %s $ =\n'%s;\n" % (name, binders, fm(th.f), th.proof))
    call = '(%s_c %s)' % (name, ' '.join('h' + x for x in tvars))
    stmt = 'theorem %s %s: $ paProvable (suc n) %s $' % (name, binders, stmt_txt)
    pr = call if conv is None else '(mpbir (paProvableeq2 %s) %s)' % (conv, call)
    items.append("pub %s =\n'%s;\n" % (stmt, pr))
    specs.append(stmt + ';')

# ---- d3t_tfe: trFun Y <-> Y ----
Ys = Y('S'); Yr = R(Ys); Yrr = R(Yr)
TFY = TFg(Ys)
def tfe():
    c = Ctx(L, [TRUE])
    def fwd_(d):     # d = G + TFY -> Ys
        def ca(e):   # All(Iff(Yr, E01))
            inst = e.app(all_elim_ax(L, Iff(Yr, E01), v(0)), e.hyp(2))      # Iff(Y, v0 = v0)
            return e.mp(e.and_right(inst), e.refl(v(0)))
        def cb(e):   # And(Not(Ex(All(Iff(Yrr, E01)))), v0 = 0)
            nx = e.and_left(e.hyp(2))
            # Lv(2): A. (v0 = Lift2 S <-> v0 = Lift2 S)   -> witness of the Ex at Lift1 S
            c2 = Ctx(Lv(2), [Eq(v(0), TL('S', 2))])
            idt = c2.hyp(0)
            body2 = Thm(Lv(2), Iff(Eq(v(0), TL('S', 2)), Eq(v(0), TL('S', 2))),
                        and_intro(ident(Lv(2), Eq(v(0), TL('S', 2))), ident(Lv(2), Eq(v(0), TL('S', 2)))).proof)
            al = gen(body2)                                                  # Lv1: A. (..)
            w = e.witness(All(Iff(Yrr, E01)), TL('S', 1), e.thm(al))
            return e.absurd(e.mp(nx, w), Ys)
        return d.cases(d.hyp(1), ca, cb)
    def bwd_(d):     # d = G + Ys -> TFY
        c2 = Ctx(Lv(2), [lift(Ys)])                                          # v1 = Lift2 S
        h = c2.hyp(0)
        def ab(e):   # e: c2 + (v0 = Lift2 S) -> v0 = v1
            return e.trans(e.hyp(1), e.sym(e.hyp(0)))
        def ba(e):   # e: c2 + (v0 = v1) -> v0 = Lift2 S
            return e.trans(e.hyp(1), e.hyp(0))
        body = iff_intro(c2, Eq(v(0), TL('S', 2)), E01, ab, ba)              # lift Ys -> Iff(Yr, E01)
        allt = all_intro_hyp(L, Ys, body)                                     # Ys -> A. Iff(Yr, E01)
        a = d.app(allt, d.hyp(1))
        return d.app(or_left_ax(L, All(Iff(Yr, E01)), TFY[2]), a)
    th = iff_intro(c, TFY, Ys, fwd_, bwd_)
    return mp(Thm(L, TRUE, '(bb215D2_id paFormulaBound_false)'), th)
th = tfe()
# statement: paProvable (suc n) (trIff (trFun Y) Y); conversion trFun Y = fm(TFY) via g7_trFun_E + subst_param
f1, f2, p = subst_param(TFg(P0('X')), 'X', Ys)
check(f2, TFY, 'tfe form')
conv = '(trIffeq (eqtr (g7_trFun_E %s) %s) %s)' % (fbound(L, Ys), p, '(eqcom (g7_par_id %s))' % fbound(L, Ys) if False else 'eqid')
emit('d3t_tfe', ['S'], '(trIff (trFun %s) %s)' % (fm(Ys), fm(Ys)), th, conv)

# ---- d3t_hs: E. (raise Y /\ v1 = S v0) <-> v0 = S (Lift1 S) ----
def hs():
    c = Ctx(L, [TRUE])
    lhs = Ex(And(Yr, Eq(v(1), S(v(0)))))
    rhs = Eq(v(0), S(TL('S', 1)))
    def fwd_(d):
        def body(e):   # lifted ctx + And(Yr, v1 = S v0) -> lift(rhs) = v1 = S (Lift2 S)
            hp = e.hyp(len(e.hyps) - 1)
            return e.trans(e.and_right(hp), e.succ(e.and_left(hp)))
        return d.exists(d.hyp(1), rhs, body)
    def bwd_(d):
        p_ = d.conj(d.refl(TL('S', 1)), d.hyp(1))
        return d.witness(And(Yr, Eq(v(1), S(v(0)))), TL('S', 1), p_)
    return mp(Thm(L, TRUE, '(bb215D2_id paFormulaBound_false)'), iff_intro(c, lhs, rhs, fwd_, bwd_))
th = hs()
emit('d3t_hs', ['S'], fm(th.f).replace(eng.tm(S(TL('S', 1))), '(paTermLift 1 (paTermSuccessor S))'), th,
     '(trIffeq eqid (paFormulaEqualeq eqid paTermRename_successor))')

# ---- d3t_ha / d3t_hm ----
def hop(op):
    c = Ctx(L, [TRUE])
    YA, YB = Y('A'), Y('B')
    YAr, YBrr = R(YA), R(R(YB))
    inner = Ex(And(YBrr, Eq(v(2), (op, v(1), v(0)))))
    lhs = Ex(And(YAr, inner))
    rhs = Eq(v(0), (op, TL('A', 1), TL('B', 1)))
    def fwd_(d):
        def b1(e):     # + And(YAr, inner)   (Lv2): goal lift(rhs) = v1 = op(A2, B2)
            h1 = e.hyp(len(e.hyps) - 1)
            goal1 = lift(rhs)
            def b2(f):   # + And(YBrr', v3? ...)  (Lv3): goal lift(goal1)
                h2 = f.hyp(len(f.hyps) - 1)
                hA = f.hyps[len(f.hyps) - 2]
                ha = f.and_left(f.hyp(len(f.hyps) - 2))          # lifted: v1 = Lift3 A
                hb = f.and_left(h2)                               # v0 = Lift3 B
                he = f.and_right(h2)                              # v2 = v1 op v0
                return f.trans(he, f.cong(op, ha, hb))
            return e.exists(e.and_right(h1), goal1, b2)
        return d.exists(d.hyp(1), rhs, b1)
    def bwd_(d):
        # witnesses Lift1 A, then Lift? B : body after first subst: And(Eq(Lift1 A, Lift1 A), Ex(And(Eq(v0, Lift2 B), Eq(v1, op(Lift1 A, v0)))))
        inner_s, _ = subst_f(0, TL('A', 1), inner)
        p_in = d.witness(inner_s[1], TL('B', 1), d.conj(d.refl(TL('B', 1)), d.hyp(1)))
        return d.witness(And(YAr, inner), TL('A', 1), d.conj(d.refl(TL('A', 1)), p_in))
    return mp(Thm(L, TRUE, '(bb215D2_id paFormulaBound_false)'), iff_intro(c, lhs, rhs, fwd_, bwd_))
for nm, op, NM in (('d3t_ha', 'a', 'paTermAddition'), ('d3t_hm', 'm', 'paTermMultiplication')):
    th = hop(op)
    emit(nm, ['A', 'B'], fm(th.f).replace(eng.tm((op, TL('A', 1), TL('B', 1))), '(paTermLift 1 (%s A B))' % NM), th,
         '(trIffeq eqid (paFormulaEqualeq eqid %s))' % ('paTermRename_addition' if op == 'a' else 'paTermRename_multiplication'))

# ---- d3t_he ----
def he():
    c = Ctx(L, [TRUE])
    YAr, YBr = R(Y('A')), R(Y('B'))
    lhs = Ex(And(YAr, YBr)); rhs = Eq(TL('A', 1), TL('B', 1))
    def fwd_(d):
        def b(e):
            h = e.hyp(len(e.hyps) - 1)
            return e.trans(e.sym(e.and_left(h)), e.and_right(h))
        return d.exists(d.hyp(1), rhs, b)
    def bwd_(d):
        return d.witness(And(YAr, YBr), TL('A', 1), d.conj(d.refl(TL('A', 1)), d.hyp(1)))
    return mp(Thm(L, TRUE, '(bb215D2_id paFormulaBound_false)'), iff_intro(c, lhs, rhs, fwd_, bwd_))
th = he()
emit('d3t_he', ['A', 'B'], fm(th.f), th, None)

hdr = '''import "d3_tl.mm1";

-- Route T (lanes/D3CHECK.md), TQ for terms: hand graphs of hand terms. Generated by tools/gen7/d3/gen_tt.py.
'''
PA = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'pa-mm0'))
open(os.path.join(PA, 'gen7', 'd3_tt.mm1'), 'w').write((hdr + '\n' + '\n'.join(items)).replace('bb215L3g_', 'g7L3g_') +
    "\npub theorem d3_tt_final: $ paFormulaBound 0 paFormulaFalse $ = 'paFormulaBound_false;\n")
open(os.path.join(PA, 'gen7', 'd3_tt.mm0'), 'w').write('import "d3_tl.mm0";\n\n' + '\n'.join(specs) +
    '\ntheorem d3_tt_final: $ paFormulaBound 0 paFormulaFalse $;\n')
print('ok')
