"""Generates pa-mm0/gen7/gen7_ax5.mm1: coded add0, addS, mul0, mulS of L."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ga import *   # noqa

out = Out()
out.share('g7a5', HB, ['h' + x for x in NAMES])
Facts.PFX[0] = 'g7f5'
eng.BOUND_MIN = 2000

A_, B_ = ('A',), ('B',)
def last(c, k=0): return c.hyp(len(c.hyps) - 1 - k)

def ax_eq(name, spL, spR, core_fn, code, lts):
    """Emit core lemma, conversion lemma and the L statement cPr (cEq L R)."""
    core = core_fn()
    out.lemma('g7_%s_core' % name, core, pub=True, binders=' ' + HB)
    off, E, p = conv_EQ(spL, spR)
    check(core.f, E, name + ' core form')
    out.thm('g7_%s_conv %s' % (name, HB), '%s = %s' % (off, fm(E)), p, pub=True)
    hs = ['(g7_trb_lt %s)' % lt for lt in lts]
    while len(hs) < 4: hs.append(hs[0])
    H = ' '.join(hs)
    out.raw('''pub theorem %s_R %s: $ cPr %s $ =
(named '(bi2 (g7_cpr_iff g7_tr_bound) (mpbir (paProvableeq2 (eqtr trPA_cEq (eqtr (trEqFeq %s %s) (g7_%s_conv %s))))
  (g7_%s_core %s))));
''' % (name, code[0], code[1], code_eq(spL), code_eq(spR), name, H, name, H))

# add0: a + 0 = a
def add0_core():
    spL = ('+', A_, ('Z',))
    fx = Facts(out); fx.need(spL); fx.need(('Z',)); fx.need(A_)
    goal = EQg(build(spL), build(A_))
    C = fx.ctx([])
    def f1(c2):
        def f2(c3):                                    # a0 = v1, w = v0
            tfz = tf_in(c3, fx, ('Z',), last(c3))
            s = c3.sym(c3.trans(c3.cong('a', c3.refl(v(1)), last(c3)), c3.thm(add_zero_t(c3.n, v(1)))))
            gl = mk_gop(c3, build(spL), 1, last(c3, 1), 1, tfz, 0, s)
            tfl = tf_in(c3, fx, spL, gl)
            return c3.witness(liftn(goal, 2)[1], v(1), c3.conj(tfl, last(c3, 1)))
        return c2.exists(name_term(c2, Z), lift(goal), f2)
    return fx.discharge(C.exists(fx.h(C, ('tot', A_)), goal, f1), 0)

ax_eq('add0', ('+', A_, ('Z',)), A_, add0_core, ('(v0: nat)', '(cEq (cAdd v0 c0) v0)'), ['(lttr cArg1_lt cArg1_lt)'])

# addS: a + S b = S (a + b)
def addS_core():
    spSB = ('S', B_); spAB = ('+', A_, B_)
    spL = ('+', A_, spSB); spR = ('S', spAB)
    fx = Facts(out)
    for sp in (spL, spR, spSB, spAB, A_, B_): fx.need(sp)
    goal = EQg(build(spL), build(spR))
    C = fx.ctx([])
    def fa(c2):                                        # a0
        def fb(c3):                                    # b0
            def fs(c4):                                # s0 = S b0     [a0 v2, b0 v1, s0 v0]
                tfs = tf_in(c4, fx, spSB, mk_gs(c4, build(spSB), 0, last(c4, 1), 1, last(c4)))
                def withs(c5):                         # + tfs
                    def fv(c6):                        # v = a0 + s0   [a0 v3, b0 v2, s0 v1, v v0]
                        gl = mk_gop(c6, build(spL), 0, c6.hyp(1), 3, c6.hyp(4), 1, c6.hyp(5))
                        tfl = tf_in(c6, fx, spL, gl)
                        def withl(c7):
                            def fc(c8):                # c0 = a0 + b0  [a0 v4, b0 v3, s0 v2, v v1, c0 v0]
                                ta, tb, es, ev, tl, ec = last(c8, 5), last(c8, 4), last(c8, 3), last(c8, 1), last(c8, 1), last(c8)
                                ta = c8.hyp(1); tb = c8.hyp(2); es = c8.hyp(3); ev = c8.hyp(5); tlh = c8.hyp(6); ec = c8.hyp(7)
                                gab = mk_gop(c8, build(spAB), 0, ta, 4, tb, 3, ec)
                                tfab = tf_in(c8, fx, spAB, gab)
                                eq = c8.chain(ev, c8.cong('a', c8.refl(v(4)), es), c8.thm(add_succ_t(c8.n, v(4), v(3))), c8.succ(c8.sym(ec)))
                                gr = mk_gs(c8, build(spR), 1, tfab, 0, eq)
                                tfr = tf_in(c8, fx, spR, gr)
                                return c8.witness(liftn(goal, 5)[1], v(1), c8.conj(tlh, tfr))
                            return c7.exists(name_term(c7, A(v(3), v(2))), liftn(goal, 4), fc)
                        return cut(c6, tfl, withl)
                    return c5.exists(name_term(c5, A(v(2), v(0))), liftn(goal, 3), fv)
                return cut(c4, tfs, withs)
            return c3.exists(name_term(c3, S(v(0))), liftn(goal, 2), fs)
        return c2.exists(fx.h(c2, ('tot', B_)), lift(goal), fb)
    return fx.discharge(C.exists(fx.h(C, ('tot', A_)), goal, fa), 0)

ax_eq('addS', ('+', A_, ('S', B_)), ('S', ('+', A_, B_)), addS_core,
      ('(v0: nat) (v1: nat)', '(cEq (cAdd v0 (cSuc v1)) (cSuc (cAdd v0 v1)))'),
      ['(lttr cArg1_lt cArg1_lt)', '(lttr (lttr cArg1_lt cArg2_lt) cArg1_lt)'])

# mul0: a * 0 = 0
def mul0_core():
    spL = ('*', A_, ('Z',))
    fx = Facts(out); fx.need(spL); fx.need(('Z',)); fx.need(A_)
    goal = EQg(build(spL), GZ)
    C = fx.ctx([])
    def f1(c2):
        def f2(c3):                                    # a0 v1, w v0
            tfz = tf_in(c3, fx, ('Z',), c3.hyp(2))
            def withz(c4):
                def f3(c5):                            # a0 v2, w v1, v v0
                    gl = mk_gop(c5, build(spL), 0, c5.hyp(1), 2, c5.hyp(3), 1, c5.hyp(4))
                    tfl = tf_in(c5, fx, spL, gl)
                    z = c5.chain(c5.hyp(4), c5.cong('m', c5.refl(v(2)), c5.hyp(2)), c5.thm(mul_zero_t(c5.n, v(2))))
                    tfr = tf_in(c5, fx, ('Z',), z)
                    return c5.witness(liftn(goal, 3)[1], v(0), c5.conj(tfl, tfr))
                return c4.exists(name_term(c4, M(v(1), v(0))), liftn(goal, 2), f3)
            return cut(c3, tfz, withz)
        return c2.exists(name_term(c2, Z), lift(goal), f2)
    return fx.discharge(C.exists(fx.h(C, ('tot', A_)), goal, f1), 0)

ax_eq('mul0', ('*', A_, ('Z',)), ('Z',), mul0_core, ('(v0: nat)', '(cEq (cMul v0 c0) c0)'), ['(lttr cArg1_lt cArg1_lt)'])

# mulS: a * S b = a * b + a
def mulS_core():
    spSB = ('S', B_); spAB = ('*', A_, B_)
    spL = ('*', A_, spSB); spR = ('+', spAB, A_)
    fx = Facts(out)
    for sp in (spL, spR, spSB, spAB, A_, B_): fx.need(sp)
    goal = EQg(build(spL), build(spR))
    C = fx.ctx([])
    def fa(c2):
        def fb(c3):
            def fs(c4):                                # a0 v2, b0 v1, s0 v0
                tfs = tf_in(c4, fx, spSB, mk_gs(c4, build(spSB), 0, c4.hyp(2), 1, c4.hyp(3)))
                def withs(c5):
                    def fv(c6):                        # a0 v3, b0 v2, s0 v1, v v0
                        gl = mk_gop(c6, build(spL), 0, c6.hyp(1), 3, c6.hyp(4), 1, c6.hyp(5))
                        tfl = tf_in(c6, fx, spL, gl)
                        def withl(c7):
                            def fc(c8):                # a0 v4, b0 v3, s0 v2, v v1, c0 v0
                                ta = c8.hyp(1); tb = c8.hyp(2); es = c8.hyp(3); ev = c8.hyp(5); tlh = c8.hyp(6); ec = c8.hyp(7)
                                gab = mk_gop(c8, build(spAB), 0, ta, 4, tb, 3, ec)
                                tfab = tf_in(c8, fx, spAB, gab)
                                eq = c8.chain(ev, c8.cong('m', c8.refl(v(4)), es), c8.thm(mul_succ_t(c8.n, v(4), v(3))),
                                              c8.cong('a', c8.sym(ec), c8.refl(v(4))))
                                gr = mk_gop(c8, build(spR), 1, tfab, 0, ta, 4, eq)
                                tfr = tf_in(c8, fx, spR, gr)
                                return c8.witness(liftn(goal, 5)[1], v(1), c8.conj(tlh, tfr))
                            return c7.exists(name_term(c7, M(v(3), v(2))), liftn(goal, 4), fc)
                        return cut(c6, tfl, withl)
                    return c5.exists(name_term(c5, M(v(2), v(0))), liftn(goal, 3), fv)
                return cut(c4, tfs, withs)
            return c3.exists(name_term(c3, S(v(0))), liftn(goal, 2), fs)
        return c2.exists(fx.h(c2, ('tot', B_)), lift(goal), fb)
    return fx.discharge(C.exists(fx.h(C, ('tot', A_)), goal, fa), 0)

ax_eq('mulS', ('*', A_, ('S', B_)), ('+', ('*', A_, B_), A_), mulS_core,
      ('(v0: nat) (v1: nat)', '(cEq (cMul v0 (cSuc v1)) (cAdd (cMul v0 v1) v0))'),
      ['(lttr cArg1_lt cArg1_lt)', '(lttr (lttr cArg1_lt cArg2_lt) cArg1_lt)'])

hdr = '''import "gen7_ax4.mm1";

-- G7 C2 (generated by tools/gen7/c2/gen_ax5.py): coded add0, addS, mul0, mulS.
'''
out.write(os.path.join(PA, 'gen7', 'gen7_ax5.mm1'), hdr)
print('ok')
