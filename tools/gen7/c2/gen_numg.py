"""Generates pa-mm0/gen7/gen7_numg.mm1: the graph of a numeral code is the numeral.

  g7_numS (step, internal): A. v (X(v) <-> v = k)  ->  A. v (GS X (v) <-> v = S k)   (k a numeral term)
  g7_num_graph (by induction on k): A. v (trPA (cNum k) (v) <-> v = paTermNumeral k), at every level suc n.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ga
from gb import *   # noqa

HB1 = '(n X k: nat) (hX: $ paFormulaBound (suc n) X $)'
ga.HB, ga.HCALL = HB1, 'hX'
out = Out()
out.share('g7nm', HB1, ['hX'])
eng.BOUND_MIN = 2000

G = P0('X')
NU = NUM('k')
def H(Gr, nu): return All(Iff(raise_(Gr), Eq(v(0), nu)))
Hk = H(G, NU)
GSX = GS(G)
Hs = H(GSX, S(NU))
def last(c, k=0): return c.hyp(len(c.hyps) - 1 - k)

def core():
    C = Ctx(L, [Hk])
    def hinst(c, t): return inst_at(c, c.hyp(0), t)
    def ftot(c2):                                  # u = v0 = k
        e = last(c2)
        xu = c2.mp(c2.and_right(hinst(c2, v(0))), e)
        return c2.witness(lift(TotP(G))[1], v(0), xu)
    tot = C.exists(name_term(C, NU), TotP(G), ftot)
    def fa(cl):                                    # a = v0
        def fb(cl2):                               # b = v0, a = v1
            A_ = cl2.push(lift(raise_(G)))
            B_ = A_.push(raise_(raise_(G)))
            ea = B_.mp(B_.and_left(hinst(B_, v(1))), B_.hyp(1))
            eb = B_.mp(B_.and_left(hinst(B_, v(0))), B_.hyp(2))
            r = B_.trans(ea, B_.sym(eb))
            return cl2.intro(A_.intro(r))
        return all_in(cl, fb)
    fun = all_in(C, fa)
    check(tot.f[2], TotP(G), 'tot'); check(fun.f[2], FunP(G), 'fun')
    q2 = C.mp(C.mp(C.thm(Thm(L, Q2stmt(G), '(g7_tf_q2 hX)')), tot), fun)
    q1 = C.thm(Thm(L, Q1stmt(G), '(g7_tf_q1 hX)'))
    def withq(C2):                                 # hyps: Hk, q2
        def body(cl):                              # v = v0
            tgt = Hs[1]
            c3 = cl.push(tgt[1][1])
            def f4(c4):                            # u = v0, v = v1
                h = last(c4)
                xu = c4.mp(inst_at(c4, c4.hyp(1), v(0)), c4.and_left(h))
                uk = c4.mp(c4.and_left(hinst(c4, v(0))), xu)
                return c4.trans(c4.and_right(h), c4.succ(uk))
            r1 = cl.intro(c3.exists(last(c3), tgt[1][2], f4))
            c5 = cl.push(tgt[2][1])
            def f6(c6):                            # u0 = v0, v = v1
                e = last(c6)
                xu0 = c6.mp(c6.and_right(hinst(c6, v(0))), e)
                q1i = inst_at(c6, c6.thm(Thm(c6.n, None, None)) if False else c6.thm(liftq(q1, c6)), v(0))
                def fu(cl7):                       # w = v0, u0 = v1
                    c8 = cl7.push(q1i.f[2][1][2][1][1])
                    wk = c8.mp(c8.and_left(hinst(c8, v(0))), last(c8))
                    u0k = c8.hyp(len(c6.hyps) - 1)
                    return cl7.intro(c8.trans(wk, c8.sym(u0k)))
                uq = all_in(c6, fu)
                tfu = c6.mp(q1i, c6.conj(xu0, uq))
                body6 = lift(tgt[1][1])[1] if False else tgt_lift_body(tgt[1][1], c6)
                eq = c6.trans(c6.hyp(len(c6.hyps) - 2), c6.succ(c6.sym(e)))
                return c6.witness(body6, v(0), c6.conj(tfu, eq))
            r2 = cl.intro(c5.exists(name_term(c5, NU), tgt[1][1], f6))
            return cl.conj(r1, r2)
        return all_in(C2, body)
    th = cut(C, q2, withq)
    th = Thm(L, Imp(Hk, Hs), th.proof)
    return th

_lq = {}
def liftq(q1, c):
    """the closed theorem Q1 (level L) at c's level."""
    k = int(c.n) - 1
    th = Thm(L, Q1stmt(G), '(g7_tf_q1 hX)')
    for _ in range(k):
        f2, p = rename_f(0, th.f)
        th = Thm(th.n + 1, f2, '(mpbi (paProvableeq2 %s) (g7_lift_rule %s))' % (p, th.proof))
    return th

def tgt_lift_body(A, c6):
    """A = Ex(body) at c5's level; the body one level up (as the exists target lift)."""
    return lift(A)[1]

core_th = core()
out.lemma('g7_numS', core_th, pub=True, binders=' ' + HB1)

# ---- the induction (hand-written around the generated step) ----
out.raw('''pub theorem g7_bnum (n k: nat): $ paFormulaBound (suc n) (trPA (cNum k)) $ =
(named @ induct '(ind) 'k '(mpbir (paFormulaBoundeq2 (eqtr (trPAeq cNum_0) trPA_c0)) g7_b_zeroF)
  '(mpbird (a1i (paFormulaBoundeq2 (eqtr (trPAeq cNum_S) trPA_cSuc))) g7_b_sucF));
''')
# induction (no shared lemmas: they take the step lemma's binders)
eng.BOUND_HOOK[0] = None; eng.EQ_HOOK[0] = None; eng._BCACHE.clear(); eng._ECACHE.clear()
Xs = '(trPA (cNum k))'
PARAMS[Xs] = ('g7_bnum', 1)
GX = P0(Xs)
stmt = fm(H(GX, NUM('k')))
ezero = "(eqtr paFormulaRename_equal (paFormulaEqualeq (eqtr paTermRename_variable (paTermVariableeq (eqtr sfRenameDepthMap_value (eqtr sfRenameIndex_zero g7F_zero)))) paTermRename_zero))"
EA0 = "(eqtr (paFormulaRenameeq3 (eqtr (trPAeq cNum_0) trPA_c0)) %s)" % ezero
EB0 = "(paFormulaEqualeq eqid paTermNumeral_zero)"
EQ0 = "(paFormulaAlleq (paFormulaAndeq (paFormulaImpeq %s %s) (paFormulaImpeq %s %s)))" % (EA0, EB0, EB0, EA0)
i0 = ident(L + 1, Eq(v(0), Z))
REFL = gen(and_intro(i0, i0)).proof
conv = "(eqtr (trPAeq cNum_S) (eqtr trPA_cSuc (paFormulaExeq (paFormulaAndeq %s eqid))))" % conv_trFun("(g7_par_id g7_bnum)", GX)
r1, q = rename_f(1, GS(GX))
EA = "(eqcom (eqtr (eqcom (g7_par_raise g7_bnum)) (eqtr (paFormulaRenameeq3 %s) %s)))" % (conv, q)
EB = "(paFormulaEqualeq eqid (eqcom paTermNumeral_succ))"
EQS = "(paFormulaAlleq (paFormulaAndeq (paFormulaImpeq %s %s) (paFormulaImpeq %s %s)))" % (EA, EB, EB, EA)
out.raw("""pub theorem g7_num_graph (n k: nat): $ paProvable (suc n) %s $ =
(named @ induct '(ind) 'k '(mpbir (paProvableeq2 %s) %s)
  '(syl (bi1 (paProvableeq2 %s)) (mpi (g7_numS g7_bnum) bb215D2_mp)));
""" % (stmt, EQ0, REFL, EQS))
open(os.path.join(PA, 'gen7', 'gen7_numg.mm1'), 'w').write('\n'.join([
    'import "gen7_num.mm1";\n\nimport "gen7_tg.mm1";\n',
    '-- G7 C5 (generated by tools/gen7/c2/gen_numg.py): the graph of a numeral code is the numeral.\n'] + out.items).replace('bb215L3g_', 'g7L3g_'))
print('ok')
