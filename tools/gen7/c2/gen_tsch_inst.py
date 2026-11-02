"""GEN7 C5: generic T-scheme instance generator for a fixed family of PA codes with numeral parameters.

A CONFIG names: an MM0 graph def G (its fully unfolded gen7 code, written by unf2.py from a reflection, one
name per binder; A0 A1 .. are G's arguments), the parameters (A_i := cNum p_i), and the PA code it mirrors
(TARGET: paFormulaSubst 0 (paTermNumeral p) (D q ..) for a def D in a .mm0 file, or D q .. itself).  Binders are
renamed by depth (the binder at depth d gets the name d).  The generator proves by structure, with the rules
of gen7_tsch (one small theorem per subformula / term node):

  THM_core (p..):  paProvable N (trIff (trPA (CODE p..)) TARGET)
  THM_bridge     (T p..) {x} (h1: cPr (ciff (CODE p..) T)) (h2: trFr (suc x) (trPA T)): |- trJ (trPA T) -> TARGET
  THM_bridge_rev (same):                                                                 |- TARGET -> trJ (trPA T)

and writes the source theorem pa-mm0/SRC.mm1: (the same formula over peano, binders x0 ..) <-> RHS, proved by
the MM0 correctness theorem of G; its reflection at numeral codes gives h1 (T := the compiler's code of RHS).

  python3 gen_tsch_inst.py tmh | tval
"""
import os, re, sys, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
HERE = os.path.dirname(os.path.abspath(__file__))
from gb import *   # noqa
import ga

CONFIGS = {
    'tmh': dict(psi='tmh_psi.txt', args=['k', 'M'], pfx='g7m', code='g7tmhCode', thm='g7_tmh',
                tfile='g2_generic_bb_codes.mm0', tdef='tmHaltsOpenPA', tformal={'n': 'k'}, tsub='M',
                texpr='tmHaltsPA k M', module='gen7_tmh', imports=['../g2_generic_tm_defs.mm1'],
                src='g7src_tmh', srcthm='g7src_tmh_flat', srcimp='g2_generic_bbsem_arithmetic_formula_value.mm1',
                rhs='tmHalts k M', correct='tmgArithmeticFormulaHaltsGraph_correct'),
    'tval': dict(psi='tval_psi.txt', args=['nst', 'T'], pfx='g7v', code='g7tvalCode', thm='g7_tval',
                 tfile='g2_generic_bbsem_table_arithmetic_valid_code.mm0', tdef='tmgTableArithmeticValidCode',
                 tformal={'nst': 'nst'}, tsub='T',
                 texpr='paFormulaSubst 0 (paTermNumeral T) (tmgTableArithmeticValidCode nst)', module='gen7_tval',
                 imports=['../g2_generic_bbsem_table_arithmetic_valid_code.mm1'],
                 src='g7src_tval', srcthm='g7src_tval_flat', srcimp='g2_generic_bbsem_table_arithmetic_valid_universal.mm1',
                 rhs='tmValid nst T', correct='tmgTableArithmeticValidPolynomial_correct'),
    'tpad': dict(psi='tpad_psik.txt', args=['m', 'n', 'M', 'T'], pfx='g7q', code='g7tpadCode', thm='g7_tpad', derive=True,
                 tdef='g7PadFullCode', texpr='g7PadFullCode m n M T', module='gen7_tpad',
                 vsplit=('g2_generic_bbsem_table_arithmetic_valid_code.mm0', 'tmgTableArithmeticValidCode', 'T'),
                 vformal={'nst': 'n'}, vnst='n',
                 imports=['../g2_generic_tm_defs.mm1', '../g2_generic_bbsem_table_arithmetic_valid_code.mm1'],
                 src='g7src_pad', srcthm='g7src_pad_flat', srcimp='g7_pad_graph.mm1',
                 rhs='tmPadOf m n M T', correct='g7PadFull_correct'),
    'hle': dict(psi='hle_psi.txt', args=['m', 'n'], pfx='g7l', code='g7hleCode', thm='g7_hle',
                tfile='gen7/gen7_hle.mm0', tdef='g7LeCode', tformal={'a': 'm', 'b': 'n'}, tsub=None,
                texpr='g7LeCode m n', module='gen7_thle', imports=['gen7_hle.mm1'],
                src='g7src_hle', srcthm='g7src_hle_flat', srcimp='../lean-mm0/vendor/peano.mm1',
                rhs='m <= n', correct='biid'),
    'hpos': dict(psi='hpos_psi.txt', args=['m'], pfx='g7p', code='g7hposCode', thm='g7_hpos',
                 tfile='gen7/gen7_hle.mm0', tdef='g7PosCode', tformal={'b': 'm'}, tsub=None,
                 texpr='g7PosCode m', module='gen7_thpos', imports=['gen7_hle.mm1'],
                 src='g7src_hpos', srcthm='g7src_hpos_flat', srcimp='../lean-mm0/vendor/peano.mm1',
                 rhs='0 < m', correct='biid'),
}
CFG = CONFIGS[sys.argv[1]]
PFX = CFG['pfx']
VARS = '(%s: nat)' % ' '.join(CFG['args'])
VS = ' '.join(CFG['args'])
BASE[0] = '(suc 0)'

# ---------------------------------------------------------------- parse the code
src = open(os.path.join(HERE, CFG['psi'])).read()
toks = re.findall(r'\(|\)|[^\s()]+', src)
pos = [0]
def parse():
    t = toks[pos[0]]; pos[0] += 1
    if t == '(':
        h = toks[pos[0]]; pos[0] += 1; args = []
        while toks[pos[0]] != ')': args.append(parse())
        pos[0] += 1
        return (h, args)
    return (t, [])
code0 = parse()

def rename(e, env, d):
    h, a = e
    if h in ('cAl', 'cex'):
        nm = a[0][0]
        return (h, [d, rename(a[1], dict(env, **{nm: d}), d + 1)])
    if h == 'cV':
        return ('cV', [env[a[0][0]]])
    if re.match(r'A\d+$', h): return ('cNum', [CFG['args'][int(h[1:])]])
    return (h, [rename(x, env, d) for x in a])
code_t = rename(code0, {}, 0)
def expand(e):
    """the kept codes of an / or / ex (unf.py --keep) to constructors."""
    h, a = e
    if h == 'can': return ('cNot', [('cIm', [expand(a[0]), ('cNot', [expand(a[1])])])])
    if h == 'cor': return ('cIm', [('cNot', [expand(a[0])]), expand(a[1])])
    if h == 'cex': return ('cNot', [('cAl', [a[0], ('cNot', [expand(a[1])])])])
    if h == 'cAl': return ('cAl', [a[0], expand(a[1])])
    if h in ('cV', 'cNum'): return e
    return (h, [expand(x) for x in a])
def guide(e):
    h, a = e
    if h == 'can': return ('and', guide(a[0]), guide(a[1]))
    if h == 'cor': return ('or', guide(a[0]), guide(a[1]))
    if h == 'cex': return ('ex', guide(a[1]))
    if h == 'cAl': return ('all', guide(a[1]))
    if h == 'cIm': return ('imp', guide(a[0]), guide(a[1]))
    if h == 'cNot': return ('not', guide(a[0]))
    if h == 'cEq': return ('eq',)
    raise ValueError(h)
code = expand(code_t)
def qdepth(e):
    h, a = e
    if h == 'cAl': return 1 + qdepth(a[1])
    return max([qdepth(x) for x in a if isinstance(x, tuple)], default=0)
NV = qdepth(code)       # names 0 .. NV - 1
N0 = NV
L = Lv(N0 + 1)          # absolute levels: Lv(k) is the numeral k

def cstr(e):
    h, a = e
    if h == 'cV': return '(cV %s)' % num(a[0])
    if h == 'cAl': return '(cAl %s %s)' % (num(a[0]), cstr(a[1]))
    if h == 'cNum': return '(cNum %s)' % a[0]
    if not a: return h
    return '(%s %s)' % (h, ' '.join(cstr(x) for x in a))

# ---------------------------------------------------------------- the target formula
if not CFG.get('derive'):
  bb = open(os.path.join(PA, CFG['tfile'])).read()
  m = re.search(r'def %s \([^)]*\): nat = \$(.*?)\$;' % CFG['tdef'], bb, re.S)
  ptoks = re.findall(r'\(|\)|[^\s()]+', '(' + m.group(1) + ')')
pp = [0]
def pparse():
    t = ptoks[pp[0]]; pp[0] += 1
    if t == '(':
        h = ptoks[pp[0]]; pp[0] += 1; args = []
        while ptoks[pp[0]] != ')': args.append(pparse())
        pp[0] += 1
        return (h, args)
    return (t, [])
def numval(e):
    h, a = e
    if h == 'suc': return numval(a[0]) + 1
    return int(h)
def to_eng(e):
    h, a = e
    if h == 'paFormulaEx': return Ex(to_eng(a[0]))
    if h == 'paFormulaAll': return All(to_eng(a[0]))
    if h == 'paFormulaAnd': return And(to_eng(a[0]), to_eng(a[1]))
    if h == 'paFormulaOr': return Or(to_eng(a[0]), to_eng(a[1]))
    if h == 'paFormulaImp': return Imp(to_eng(a[0]), to_eng(a[1]))
    if h == 'paFormulaEqual': return Eq(to_eng(a[0]), to_eng(a[1]))
    if h == 'paTermZero': return Z
    if h == 'paTermSuccessor': return S(to_eng(a[0]))
    if h == 'paTermAddition': return A(to_eng(a[0]), to_eng(a[1]))
    if h == 'paTermMultiplication': return M(to_eng(a[0]), to_eng(a[1]))
    if h == 'paTermVariable': return v(numval(a[0]))
    if h == 'paTermNumeral':
        return NUM(CFG['tformal'][a[0][0]])
    if h == 'paFormulaFalse': return F
    raise ValueError(h)
if CFG.get('derive'):
    E_tgt, EQ_tgt = None, 'eqid'
else:
  E_open = to_eng(pparse())
  if CFG['tsub']:
    E_tgt, EQ_tgt = subst_f(0, NUM(CFG['tsub']), E_open)    # paFormulaSubst 0 (num p) (fm E_open) = fm E_tgt
  else:
    E_tgt, EQ_tgt = E_open, 'eqid'

# ---------------------------------------------------------------- output
out = Out()
eng.BOUND_MIN = 1500
out.share(PFX + 'h', VARS, [])
_kb = [0]
def _emit(stmt, p):
    _kb[0] += 1
    name = '%sh_b%d' % (PFX, _kb[0])
    out.items.append("theorem %s%s: $ %s $ =\n(named '%s);\n" % (name, binders_for(stmt), stmt, p))
    return name
def _bhook(kind, n, obj, p):
    stmt = ('paTermBound %s %s' % (num(n), eng.tm(obj))) if kind == 't' else ('paFormulaBound %s %s' % (num(n), fm(obj)))
    return _emit(stmt, p)
eng.BOUND_HOOK[0] = _bhook
eng.EQ_HOOK[0] = _emit
cores = pickle.load(open(os.path.join(HERE, 'tsch_cores.pkl'), 'rb'))
def core(name, subst):
    n, f = cores[name]
    for X, P in subst.items():
        f = ga.rename_param(f, X, P)
    return f

K = [0]
def binders_for(stmt):
    """only the parameters the statement mentions: an unused binder of a lemma becomes a fresh dummy at every
    use, and mm0 allows at most 55 bound variables per theorem."""
    used = [a for a in CFG['args'] if re.search(r'(?<![A-Za-z0-9_])%s(?![A-Za-z0-9_])' % re.escape(a), stmt)]
    return ' (%s: nat)' % ' '.join(used) if used else ''
def lemma(prefix, stmt, proof):
    K[0] += 1
    name = '%s_%d' % (prefix, K[0])
    out.raw("theorem %s%s: $ %s $ =\n(named '%s);\n" % (name, binders_for(stmt), stmt, proof))
    return name

def Pv(s): return 'paProvable %s (%s)' % (num(L), s)

def par_conv(G, j, s):
    """(G', proof of paFormulaRename (g7F j s) 0 (fm G) = fm G') for an engine graph G at level L."""
    hb = fbound(L, G)
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
    return cur, p

# ---------------------------------------------------------------- term graphs
def H(G, t): return All(Iff(raise_(G), Eq(v(0), shift_t(t, 1))))
TB = {}
def tbnd(c):
    """registers the parameter (trPA c) with its bound proof at level N."""
    s = cstr(c)
    P = '(trPA %s)' % s
    if P in TB: return P
    h, a = c
    if h == 'cV': p = '(mpbir (paFormulaBoundeq2 trPA_cV) (g7_b_varF %s))' % eng.lt(a[0], N0)
    elif h == 'c0': p = '(mpbir (paFormulaBoundeq2 trPA_c0) g7_b_zeroF)'
    elif h == 'cNum': p = 'g7_bnum'
    elif h == 'cSuc': p = '(mpbir (paFormulaBoundeq2 trPA_cSuc) (g7_b_sucF %s))' % TB[tbnd(a[0])]
    elif h == 'cAdd': p = '(mpbir (paFormulaBoundeq2 trPA_cAdd) (g7_b_addF %s %s))' % (TB[tbnd(a[0])], TB[tbnd(a[1])])
    elif h == 'cMul': p = '(mpbir (paFormulaBoundeq2 trPA_cMul) (g7_b_mulF %s %s))' % (TB[tbnd(a[0])], TB[tbnd(a[1])])
    else: raise ValueError(h)
    name = lemma(PFX + 'b', 'paFormulaBound %s %s' % (num(L), P), p)
    TB[P] = name
    param(P, name, int(L))
    return P

def heq(e):
    """proof of fm(H(P0 X, t)) = fm(H(G, t)) from e: paFormulaRename (g7F 1 0) 0 X = fm(raise_ G)."""
    return '(paFormulaAlleq (paFormulaAndeq (paFormulaImpeq %s eqid) (paFormulaImpeq eqid %s)))' % (e, e)

CTL, CT2L = {}, {}
def CT(P):
    """lemma: paAxiomRaiseParameters (trFun P) = fm (raise_ (TFg (P0 P)))."""
    if P not in CTL:
        G = P0(P)
        CTL[P] = lemma(PFX + 'c', 'paAxiomRaiseParameters (trFun %s) = %s' % (P, fm(raise_(TFg(G)))), conv_trFun('(g7_par_id %s)' % TB[P], G))
    return CTL[P]
def CT2(P):
    """lemma: paAxiomRaiseParameters (paAxiomRaiseParameters (trFun P)) = fm (raise_ (raise_ (TFg (P0 P))))."""
    if P not in CT2L:
        rr, q = rename_f(1, raise_(TFg(P0(P))))
        CT2L[P] = lemma(PFX + 'c', 'paAxiomRaiseParameters (paAxiomRaiseParameters (trFun %s)) = %s' % (P, fm(rr)), '(eqtr (paFormulaRenameeq3 %s) %s)' % (CT(P), q))
    return CT2L[P]
def PCL(G):
    rg, pc = par_conv(G, 1, 0)
    return lemma(PFX + 'p', 'paFormulaRename (g7F 1 0) 0 %s = %s' % (fm(G), fm(rg)), pc)

HF = {}
def hfact(c):
    """(term tau, lemma proving paProvable N (H(P0 (trPA c), tau)))."""
    s = cstr(c)
    if s in HF: return HF[s]
    P = tbnd(c)
    h, a = c
    if h == 'cNum':
        tau = NUM(a[0]); r = (tau, 'g7_num_graph')
        HF[s] = r; return r
    if h in ('cV', 'c0'):
        tau = v(a[0] + 1) if h == 'cV' else Z
        G = Eq(v(0), tau)
        i = ident(L + 1, raise_(G)[1] if False else raise_(G))
        refl = gen(and_intro(i, i))
        th = H(G, tau)
        check(refl.f, th, 'var refl')
        rg, pc = par_conv(G, 1, 0)
        e = '(eqtr (paFormulaRenameeq3 %s) %s)' % ('trPA_cV' if h == 'cV' else 'trPA_c0', pc)
        stmt = H(P0(P), tau)
        name = lemma(PFX + 'h', Pv(fm(stmt)), '(mpbir (paProvableeq2 %s) %s)' % (heq(e), refl.proof))
        r = (tau, name); HF[s] = r; return r
    subs = [hfact(x) for x in a]
    Ps = [tbnd(x) for x in a]
    if h == 'cSuc':
        f = core('g7t_suc', {'X': Ps[0]})
        th = Thm(L, f, '(g7t_suc %s)' % TB[Ps[0]])
        th = mp(th, all_elim_ax(L, th.f[1], subs[0][0]))
        th = mp(Thm(L, th.f[1], subs[0][1]), th)
        tau = S(subs[0][0])
        G = GS(P0(Ps[0]))
        conv = '(eqtr trPA_cSuc (paFormulaExeq (paFormulaAndeq %s eqid)))' % CT(Ps[0])
    else:
        nm = {'cAdd': 'g7t_add', 'cMul': 'g7t_mul'}[h]
        f = core(nm, {'X': Ps[0], 'Y': Ps[1]})
        th = Thm(L, f, '(%s %s %s)' % (nm, TB[Ps[0]], TB[Ps[1]]))
        th = mp(th, all_elim_ax(L, th.f[1], subs[0][0]))
        th = mp(th, all_elim_ax(L, th.f[1], subs[1][0]))
        th = mp(Thm(L, th.f[1], subs[0][1]), th)
        th = mp(Thm(L, th.f[1], subs[1][1]), th)
        tau = (A if h == 'cAdd' else M)(subs[0][0], subs[1][0])
        G = (GA if h == 'cAdd' else GM)(P0(Ps[0]), P0(Ps[1]))
        rrt2 = CT2(Ps[1])
        conv = '(eqtr trPA_c%s (paFormulaExeq (paFormulaAndeq %s (paFormulaExeq (paFormulaAndeq %s eqid)))))' % (
            h[1:], CT(Ps[0]), rrt2)
    check(th.f, H(G, tau), 'hfact %s' % h)
    conv = lemma(PFX + 't', 'trPA %s = %s' % (s, fm(G)), conv)
    pc = PCL(G)
    e = '(eqtr (paFormulaRenameeq3 %s) %s)' % (conv, pc)
    ni = lemma(PFX + 'i', Pv(fm(th.f)), th.proof)
    ne_ = lemma(PFX + 'e', '%s = %s' % (fm(H(P0(P), tau)), fm(th.f)), heq(e))
    name = lemma(PFX + 'h', Pv(fm(H(P0(P), tau))), '(mpbir (paProvableeq2 %s) %s)' % (ne_, ni))
    r = (tau, name); HF[s] = r; return r

# ---------------------------------------------------------------- binding a concrete name (trAbs (suc x))
def ne_num(i, j):
    return '(ltnei %s)' % eng.lt(i, j) if i < j else '(ltneri %s)' % eng.lt(j, i)
def abs_idx(x, d, i):
    if i < d: return i, '(sfRenameIndex_bound %s)' % eng.lt(i, d)
    if d > 0:
        r, p = abs_idx(x, d - 1, i - 1)
        return r + 1, '(eqtr sfRenameIndex_lift (suceq %s))' % p
    if i == x + 1: return 0, '(eqtr sfRenameIndex_zero (eqtr g7_abs_value (ifpos eqid)))'
    return i + 1, '(eqtr sfRenameIndex_zero (g7x_abs_miss %s))' % ne_num(i, x + 1)
def abs_t(x, d, u):
    c = u[0]
    if c == 'num': return u, 'bb215ArithmeticSentenceNumeral_rename'
    if c == 'v':
        r, p = abs_idx(x, d, u[1])
        return v(r), '(eqtr paTermRename_variable (paTermVariableeq (eqtr sfRenameDepthMap_value %s)))' % p
    if c == 'z': return u, 'paTermRename_zero'
    if c == 's':
        r, p = abs_t(x, d, u[1]); return S(r), '(eqtr paTermRename_successor (paTermSuccessoreq %s))' % p
    r1, p1 = abs_t(x, d, u[1]); r2, p2 = abs_t(x, d, u[2])
    if c == 'a': return A(r1, r2), '(eqtr paTermRename_addition (paTermAdditioneq %s %s))' % (p1, p2)
    return M(r1, r2), '(eqtr paTermRename_multiplication (paTermMultiplicationeq %s %s))' % (p1, p2)
_EQN2 = {'and': 'And', 'or': 'Or', 'imp': 'Imp', 'all': 'All', 'ex': 'Ex'}
def abs_f(x, d, f):
    c = f[0]
    if c == 'eq':
        r1, p1 = abs_t(x, d, f[1]); r2, p2 = abs_t(x, d, f[2])
        return Eq(r1, r2), '(eqtr paFormulaRename_equal (paFormulaEqualeq %s %s))' % (p1, p2)
    if c in ('or', 'and', 'imp'):
        r1, p1 = abs_f(x, d, f[1]); r2, p2 = abs_f(x, d, f[2])
        return (c, r1, r2), '(eqtr paFormulaRename_%s (paFormula%seq %s %s))' % (c, _EQN2[c], p1, p2)
    if c in ('all', 'ex'):
        r, p = abs_f(x, d + 1, f[1])
        return (c, r), '(eqtr paFormulaRename_%s (paFormula%seq %s))' % (c, _EQN2[c], p)
    if c == 'f': return f, 'paFormulaRename_false'
    raise ValueError(f)
_AC = {}
def abs_top(x, f):
    """(f', proof of trAbs (suc x) (fm f) = fm f'), shared as a lemma when long."""
    r, p = abs_f(x, 0, f)
    if len(p) > 3000:
        p = lemma(PFX + 'a', 'trAbs (suc %s) %s = %s' % (num(x), fm(f), fm(r)), p)
    return r, p

# ---------------------------------------------------------------- formulas
TJL = {'cIm': 'g7_tJ_cIm', 'cNot': 'g7_tJ_cNot', 'cAl': 'g7_tJ_cAl', 'cEq': 'g7_tJ_cEq'}
def tj(c): return TJL[c[0]]
def is_(c, h): return c[0] == h
def F_(c, t):
    """(theta, lemma proving paProvable N (trIff (trPA c) (fm theta))); t: the target (shape guide)."""
    k = t[0]
    def emit(theta, eqL, eqR, proof):
        stmt = Pv('trIff (trPA %s) %s' % (cstr(c), fm(theta)))
        p = proof
        if eqL != 'eqid' or eqR != 'eqid':
            p = '(mpbir (paProvableeq2 (trIffeq %s %s)) %s)' % (eqL, eqR, proof)
        return theta, lemma(PFX + 'f', stmt, p)
    if k == 'eq':
        need(is_(c, 'cEq'), 'atom %s' % c[0])
        a, b = c[1]
        (ta, ha), (tb, hb) = hfact(a), hfact(b)
        Pa, Pb = tbnd(a), tbnd(b)
        f = core('g7t_eq', {'X': Pa, 'Y': Pb})
        th = Thm(L, f, '(g7t_eq %s %s)' % (TB[Pa], TB[Pb]))
        th = mp(th, all_elim_ax(L, th.f[1], ta))
        th = mp(th, all_elim_ax(L, th.f[1], tb))
        th = mp(Thm(L, th.f[1], ha), th)
        th = mp(Thm(L, th.f[1], hb), th)
        G1, G2 = P0(Pa), P0(Pb)
        theta = Eq(ta, tb)
        check(th.f, Iff(EQg(G1, G2), theta), 'atom')
        eqL = '(eqtr trPA_cEq (paFormulaExeq (paFormulaAndeq %s %s)))' % (
            CT(Pa), CT(Pb))
        stmt = Pv('trIff (trPA %s) %s' % (cstr(c), fm(theta)))
        return theta, lemma(PFX + 'f', stmt, '(mpbir (paProvableeq2 (trIffeq %s eqid)) %s)' % (eqL, th.proof))
    if k == 'and':
        need(is_(c, 'cNot') and is_(c[1][0], 'cIm') and is_(c[1][0][1][1], 'cNot'), 'and shape')
        a, b = c[1][0][1][0], c[1][0][1][1][1][0]
        A1, pa = F_(a, t[1]); B1, pb = F_(b, t[2])
        eqL = '(eqtr trPA_cNot (trNoteq (eqtr g7_tJ_cIm (eqtr trPA_cIm (paFormulaImpeq %s (eqtr g7_tJ_cNot (eqtr trPA_cNot (trNoteq %s))))))))' % (tj(a), tj(b))
        return emit(And(A1, B1), eqL, 'eqid', '(g7r_and %s %s)' % (pa, pb))
    if k == 'or':
        need(is_(c, 'cIm') and is_(c[1][0], 'cNot'), 'or shape')
        a, b = c[1][0][1][0], c[1][1]
        A1, pa = F_(a, t[1]); B1, pb = F_(b, t[2])
        eqL = '(eqtr trPA_cIm (paFormulaImpeq (eqtr g7_tJ_cNot (eqtr trPA_cNot (trNoteq %s))) %s))' % (tj(a), tj(b))
        return emit(Or(A1, B1), eqL, 'eqid', '(g7r_or %s %s)' % (pa, pb))
    if k == 'imp':
        need(is_(c, 'cIm'), 'imp shape')
        a, b = c[1]
        A1, pa = F_(a, t[1]); B1, pb = F_(b, t[2])
        eqL = '(eqtr trPA_cIm (paFormulaImpeq %s %s))' % (tj(a), tj(b))
        return emit(Imp(A1, B1), eqL, 'eqid', '(g7r_imp %s %s)' % (pa, pb))
    if k == 'all':
        need(is_(c, 'cAl'), 'all shape')
        x, a = c[1][0], c[1][1]
        A1, pa = F_(a, t[1])
        r, pr = abs_top(x, A1)
        eqL = '(eqtr trPA_cAl (paFormulaAlleq (paFormulaRenameeq3 %s)))' % tj(a)
        return emit(All(r), eqL, '(paFormulaAlleq (eqcom %s))' % pr, '(g7r_all %s)' % pa)
    if k == 'ex':
        need(is_(c, 'cNot') and is_(c[1][0], 'cAl') and is_(c[1][0][1][1], 'cNot'), 'ex shape')
        x, a = c[1][0][1][0], c[1][0][1][1][1][0]
        A1, pa = F_(a, t[1])
        r, pr = abs_top(x, A1)
        eqL = '(eqtr trPA_cNot (trNoteq (eqtr g7_tJ_cAl (eqtr trPA_cAl (paFormulaAlleq (paFormulaRenameeq3 (eqtr g7_tJ_cNot (eqtr trPA_cNot (trNoteq %s)))))))))' % tj(a)
        return emit(Ex(r), eqL, '(paFormulaExeq (eqcom %s))' % pr, '(g7r_ex %s)' % pa)
    if k == 'not':
        need(is_(c, 'cNot'), 'not shape')
        a = c[1][0]
        A1, pa = F_(a, t[1])
        eqL = '(eqtr trPA_cNot (trNoteq %s))' % tj(a)
        return emit(Not(A1), eqL, 'eqid', '(g7r_not %s)' % pa)
    raise NDError('target %s' % k)

def derive(c):
    """the shape guide of the PA formula a code denotes (when no hand PA code is given)."""
    h, a = c
    if h == 'cEq': return ('eq',)
    if h == 'cAl': return ('all', derive(a[1]))
    if h == 'cNot':
        x = a[0]
        if x[0] == 'cAl' and x[1][1][0] == 'cNot': return ('ex', derive(x[1][1][1][0]))
        if x[0] == 'cIm' and x[1][1][0] == 'cNot': return ('and', derive(x[1][0]), derive(x[1][1][1][0]))
        return ('not', derive(x))
    if h == 'cIm':
        if a[0][0] == 'cNot': return ('or', derive(a[0][1][0]), derive(a[1]))
        return ('imp', derive(a[0]), derive(a[1]))
    raise NDError('derive %s' % h)

# the code as a structure with the binder field as an int: adapt F_ (c = (head, [args]))
def norm(e):
    h, a = e
    if h == 'cAl': return ('cAl', [a[0], norm(a[1])])
    if h in ('cV',): return e
    if h == 'cNum': return e
    return (h, [norm(x) for x in a])
codeN = norm(code)
# F_ indexes c[1][..]: convert to the (head, args) access used above
if CFG.get('derive'):
    theta, top = F_(codeN, guide(code_t))
    E_tgt = theta
    out.raw("-- the PA formula the code denotes (derived from the code, connectives read off its shape)\ndef %s %s: nat = $ %s $;\n" % (CFG['tdef'], VARS, fm(theta)))
else:
    theta, top = F_(codeN, E_tgt)
    check(theta, E_tgt, 'final theta')

PSI = cstr(codeN)
CODE, THM, TX = CFG['code'], CFG['thm'], CFG['texpr']
out.raw("""-- the code (binder at depth d named d; A_i := cNum of the i-th parameter)
def %s %s: nat = $ %s $;

pub theorem %s_core %s: $ %s $ =
(named '(mpbi (paProvableeq2 (trIffeq eqid (eqcom %s))) %s));
""" % (CODE, VARS, PSI, THM, VARS, Pv('trIff (trPA (%s %s)) (%s)' % (CODE, VS, TX)), EQ_tgt, top))

def BI(a, b): return '(mpbir paFormulaBound_imp (iani %s %s))' % (a, b)
def BN(a): return BI(a, 'paFormulaBound_false')
CORE = THM + '_core'
bP = '(anl (bi1 paFormulaBound_imp (anl (bi1 paFormulaBound_and (paProvable_bound %s)))))' % CORE
bEN = '(anr (bi1 paFormulaBound_imp (anl (bi1 paFormulaBound_and (paProvable_bound %s)))))' % CORE
bTN = '(paFormulaBound_mono le01 (g7_closed_Jt h2))'
EQC = ('(eqtr trPA_cNot (trNoteq (eqtr g7_tJ_cIm (eqtr trPA_cIm (paFormulaImpeq (eqtr g7_tJ_cIm (eqtr trPA_cIm (paFormulaImpeq %s eqid)))'
       ' (eqtr g7_tJ_cNot (eqtr trPA_cNot (trNoteq (eqtr g7_tJ_cIm (eqtr trPA_cIm (paFormulaImpeq eqid %s)))))))))))') % (tj(codeN), tj(codeN))
BC = '(mpbir (paFormulaBoundeq2 %s) %s)' % (EQC, BN(BI(BI(bP, bTN), BN(BI(bTN, bP)))))
bE0 = '(mpbir (paFormulaBoundeq2 %s) %s)' % (EQ_tgt, fbound(0, E_tgt))
HYP = "(Qc %s: nat) {x: nat} (h1: $ cPr (ciff (%s %s) Qc) $) (h2: $ trFr (suc x) (trPA Qc) $)" % (VS, CODE, VS)
IFF = '(mpbi (paProvableeq2 %s) (mpbi (g7_cpr_iff %s) h1))' % (EQC, BC)
out.raw("""-- the bridges: a code T with no free name (semantic freshness) whose reflected iff with the code is provable
pub theorem %s_bridge %s:
  $ paProvable 0 (paFormulaImp (trJ (trPA Qc)) (%s)) $ =
(named '(g7_vac %s (g7_clgen (bb215D2_syl %s (g7r_mpr %s) (bb215D2_and_left %s)))));

pub theorem %s_bridge_rev %s:
  $ paProvable 0 (paFormulaImp (%s) (trJ (trPA Qc))) $ =
(named '(g7_vac %s (g7_clgen (bb215D2_syl %s (bb215D2_and_right %s) (g7r_mpl %s)))));
""" % (THM, HYP, TX, BI('(g7_closed_Jt h2)', bE0), bTN, IFF, CORE,
       THM, HYP, TX, BI(bE0, '(g7_closed_Jt h2)'), bEN, CORE, IFF))

if CFG.get('vsplit'):
    # the first conjunct of the derived code is the valid code of (n, T) (the generator of tval checks the same shape)
    vf, vd, vsub = CFG['vsplit']
    vt = open(os.path.join(PA, vf)).read()
    vm = re.search(r'def %s \([^)]*\): nat = \$(.*?)\$;' % vd, vt, re.S)
    vtoks = re.findall(r'\(|\)|[^\s()]+', '(' + vm.group(1) + ')')
    vp = [0]
    def vparse():
        t = vtoks[vp[0]]; vp[0] += 1
        if t == '(':
            h = vtoks[vp[0]]; vp[0] += 1; args = []
            while vtoks[vp[0]] != ')': args.append(vparse())
            vp[0] += 1
            return (h, args)
        return (t, [])
    CFG['tformal'] = CFG['vformal']
    EV, PV = subst_f(0, NUM(vsub), to_eng(vparse()))
    check(EV, theta[1], 'valid conjunct')
    out.raw("""-- the derived code splits as (the valid code of n T) /\\ (the padding part)
pub theorem %s_vsplit %s: $ %s %s = paFormulaAnd (paFormulaSubst 0 (paTermNumeral %s) (%s %s)) %s $ =
(named '(paFormulaAndeq (eqcom %s) eqid));
""" % (THM, VARS, CFG['tdef'], VS, vsub, vd, CFG['vnst'], fm(theta[2]), PV))

hdr = 'import "gen7_tsch.mm1";\n\nimport "gen7_closed.mm1";\n\n' + ''.join('import "%s";\n\n' % m for m in CFG['imports']) + \
      '-- G7 C5 (generated by tools/gen7/c2/gen_tsch_inst.py %s): T-scheme instance for %s (see the generator).\n' % (sys.argv[1], TX)
out.write(os.path.join(PA, 'gen7', CFG['module'] + '.mm1'), hdr)

# ---------------------------------------------------------------- the source theorem (over peano)
def mstr(e):
    h, a = e
    if h == 'cNot': return '(~ %s)' % mstr(a[0])
    if h == 'cIm': return '(%s -> %s)' % (mstr(a[0]), mstr(a[1]))
    if h == 'cAl': return '(A. x%d %s)' % (a[0], mstr(a[1]))
    if h == 'cEq': return '(%s = %s)' % (mstr(a[0]), mstr(a[1]))
    if h == 'cAdd': return '(%s + %s)' % (mstr(a[0]), mstr(a[1]))
    if h == 'cMul': return '(%s * %s)' % (mstr(a[0]), mstr(a[1]))
    if h == 'cSuc': return '(suc %s)' % mstr(a[0])
    if h == 'c0': return '0'
    if h == 'cV': return 'x%d' % a[0]
    if h == 'cNum': return a[0]
    raise ValueError(h)
bv = ' '.join('x%d' % i for i in range(NV))
open(os.path.join(PA, CFG['src'] + '.mm1'), 'w').write("""import "%s";

-- GEN7 C5 (generated by tools/gen7/c2/gen_tsch_inst.py %s): %s as one explicit formula over peano (the unfolded
-- graph, binders x0 .. by depth). Reflected, its conclusion at numeral codes is cPr (ciff (%s ..) (code of %s)).
pub theorem %s %s {%s: nat}: $ %s <-> %s $ =
(named '%s);
""" % (CFG['srcimp'], sys.argv[1], CFG['rhs'], CODE, CFG['rhs'], CFG['srcthm'], VARS, bv, mstr(codeN), CFG['rhs'], CFG['correct']))
print('ok', K[0], 'lemmas', 'N =', N0 + 1)
