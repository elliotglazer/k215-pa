"""GEN7 C2: natural-deduction generator for internal PA derivations at a symbolic level.

Extends L05's bb215_l3_engine / bb215_l3_nd (imported, never edited):
  * levels are Lv objects: Lv(k) prints as suc^(k-1) BASE, where BASE is an MM0 expression of the
    form (suc _) (so variable 0 is always in range);
  * formula parameters ('par', X, j, s) print as paFormulaRename (g7F j s) 0 X (gen7_par.mm1); X is
    registered with a proof that it is bound by Lv(b). Lifts and substitutions of a variable are
    computed (g7_par_lift / g7_par_subst), bounds by g7_par_bound.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
PA = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'pa-mm0'))
sys.path.insert(0, PA)
import bb215_l3_engine as eng
import bb215_l3_nd as nd
from bb215_l3_nd import *   # noqa

BASE = ['(suc n)']           # MM0 expression of Lv(1); set per module
nd.GENERIC[0] = True         # generic axiom wrappers (bb215_derivability_l3b_cop): no formulas in proofs


class Lv(int):
    def __new__(cls, k):
        return int.__new__(cls, k)
    def __add__(self, o): return Lv(int(self) + int(o))
    __radd__ = __add__
    def __sub__(self, o): return Lv(int(self) - int(o))
    def __repr__(self): return 'Lv(%d)' % int(self)


def lvstr(k):
    if int(k) == 0:
        b = BASE[0]
        assert b.startswith('(suc ') and b.endswith(')')
        return b[5:-1]
    s = BASE[0]
    for _ in range(int(k) - 1): s = '(suc %s)' % s
    return s


class Sym:
    """A symbolic variable index suc^off name (name a free MM0 variable with a hypothesis
    SYMHYP[name]: name < n, where Lv(1) = suc n)."""
    def __init__(self, name, off): self.name, self.off = name, off
    def __repr__(self): return 'Sym(%s,%d)' % (self.name, self.off)
    def __eq__(self, o): return isinstance(o, Sym) and (o.name, o.off) == (self.name, self.off)
    def __ne__(self, o): return not self.__eq__(o)
    def __hash__(self): return hash(('sym', self.name, self.off))
    def __add__(self, k):
        assert isinstance(k, int) and not isinstance(k, Sym)
        return Sym(self.name, self.off + k)
    __radd__ = __add__
    def __sub__(self, k):
        assert self.off >= k, (self, k)
        return Sym(self.name, self.off - k)
    def _cmp_int(self, o):
        """-1 if self < o, +1 if self > o (o int); Lv(m): self < Lv(m) iff off <= m."""
        if isinstance(o, Sym): raise NDError('Sym compare %r %r' % (self, o))
        if isinstance(o, Lv): return -1 if self.off <= int(o) else (_ for _ in ()).throw(NDError('Sym vs Lv %r %r' % (self, o)))
        if self.off >= o: return 1
        raise NDError('Sym vs int %r %r' % (self, o))
    def __lt__(self, o): return self._cmp_int(o) < 0
    def __le__(self, o): return self._cmp_int(o) < 0
    def __gt__(self, o): return self._cmp_int(o) > 0
    def __ge__(self, o): return self._cmp_int(o) > 0

SYMHYP = {}

def symstr(x):
    s = x.name
    for _ in range(x.off): s = '(suc %s)' % s
    return s


_num0 = eng.num
def num(k):
    if isinstance(k, Lv): return lvstr(k)
    if isinstance(k, Sym): return symstr(k)
    return _num0(k)
eng.num = num
nd.num = num

PARAMS = {}   # X -> (proof of paFormulaBound Lv(b) X, b)

def param(X, hX, b=1):
    PARAMS[X] = (hX, b)

def Par(X, j=0, s=0): return ('par', X, j, s)

def numle(a, b):
    """Proof of a <= b for numerals."""
    assert a <= b, (a, b)
    if a == 0: return 'le01'
    return '(mpbi lesuc %s)' % numle(a - 1, b - 1)

def lv_le(a, m):
    """Proof of Lv(a) <= Lv(m)."""
    assert a <= m
    if a == m: return 'leid'
    return '(letr %s lesucid)' % lv_le(a, m - 1)

def lv_add(b, j):
    """Proof of Lv(b) + j = Lv(b + j)."""
    if j == 0: return 'add0'
    return '(eqtr addS (suceq %s))' % lv_add(b, j - 1)

_lt0 = eng.lt
def lt(a, b):
    if isinstance(a, Sym):
        if a.off == 0:
            m = int(b)
            p = 'leid'
            for _ in range(m): p = '(letr %s lesucid)' % p
            return '(ltletr %s %s)' % (SYMHYP[a.name], p)
        return '(mpbi ltsuc %s)' % lt(a - 1, b - 1)
    if isinstance(b, Sym):
        assert a < b.off, (a, b)
        return 'lt01S' if a == 0 else '(mpbi ltsuc %s)' % lt(a - 1, b - 1)
    return _lt0(a, b)
eng.lt = lt

_numadd0 = eng.numadd
def numadd(d, j):
    if isinstance(j, Sym) and not isinstance(d, Sym) and j.off == 0:
        if d == 0: return 'add01'
        return '(eqtr addcom %s)' % _numadd0(j, d)
    return _numadd0(d, j)
eng.numadd = numadd

_fm0, _fb0, _sub0, _ren0 = eng.fm, eng.fbound, eng._subst_f_raw, eng._rename_f_raw

def _fm(f):
    if f[0] == 'par': return '(paFormulaRename (g7F %s %s) 0 %s)' % (_num0(f[2]), num(f[3]), f[1])
    return _fm0(f)

def _fbound(n, f):
    if f[0] == 'par':
        X, j, s = f[1], f[2], f[3]
        hX, b = PARAMS[X]
        assert isinstance(n, Lv) and b + j <= int(n) and s < n, (f, n)
        return '(g7_par_bound %s %s (mpbir (leeq1 %s) %s))' % (hX, eng.lt(s, n), lv_add(b, j), lv_le(b + j, int(n)))
    return _fb0(n, f)

def _sidx(d, t, j):
    if j < d: return j, '(sfSubstIndex_bound %s)' % eng.lt(j, d)
    if j == d: return t + d, '(eqtr sfSubstIndex_hit %s)' % eng.numadd(t, d)
    return j - 1, '(eqtr (sfSubstIndex_above %s) sucsub1)' % eng.lt(d, j)

def _subst(d, t, f):
    if f[0] == 'par':
        X, j, s = f[1], f[2], f[3]
        assert j >= 1 and d <= j, (f, d)
        if t[0] != 'v':
            if s == d: raise NDError('par: substitution of a non-variable term at the slot')
            s2 = s if s < d else s - 1
            return Par(X, j - 1, s2), '(g7_par_subst_t %s %s %s)' % (eng.rename_index(d, s2), numle(d, j), PARAMS[X][0])
        v2, p = _sidx(d, t[1], s)
        return Par(X, j - 1, v2), '(g7_par_subst %s %s %s)' % (p, numle(d, j), PARAMS[X][0])
    return _sub0(d, t, f)

def _ren(d, f):
    if f[0] == 'par':
        X, j, s = f[1], f[2], f[3]
        assert d <= j + 1, (f, d)
        s2 = s if s < d else s + 1
        return Par(X, j + 1, s2), '(g7_par_lift %s %s %s)' % (eng.rename_index(d, s), numle(d, j + 1), PARAMS[X][0])
    return _ren0(d, f)

eng.fm, eng.fbound, eng._subst_f_raw, eng._rename_f_raw = _fm, _fbound, _subst, _ren
nd.fm, nd.fbound = _fm, _fbound
fm, fbound = _fm, _fbound


# ---- closed numeral terms ('num', expr): paTermNumeral expr (bound everywhere, fixed by renames/substs) ----
def NUM(expr): return ('num', expr)

def _wrap_t():
    o_tm, o_tb, o_sh, o_lift, o_sub, o_ren = eng.tm, eng.tbound, eng.shift_t, eng.lift_t, eng.subst_t, eng.rename_t
    def tm(t):
        return '(paTermNumeral %s)' % t[1] if t[0] == 'num' else o_tm(t)
    def tbound(n, t):
        return 'paNatTermNumeral_bound' if t[0] == 'num' else o_tb(n, t)
    def shift_t(t, k, cut=0):
        return t if t[0] == 'num' else o_sh(t, k, cut)
    def lift_t(k, t):
        return (t, 'paProofNumeral_lift') if t[0] == 'num' else o_lift(k, t)
    def subst_t(d, t, u):
        return (u, 'paProofNumeral_substitution') if u[0] == 'num' else o_sub(d, t, u)
    def rename_t(d, u):
        return (u, 'bb215ArithmeticSentenceNumeral_rename') if u[0] == 'num' else o_ren(d, u)
    for mod in (eng, nd):
        mod.tm, mod.tbound, mod.shift_t, mod.lift_t, mod.subst_t, mod.rename_t = tm, tbound, shift_t, lift_t, subst_t, rename_t
    return tm, tbound, shift_t, lift_t, subst_t, rename_t
tm, tbound, shift_t, lift_t, subst_t, rename_t = _wrap_t()


def Iff(a, b): return And(Imp(a, b), Imp(b, a))


class Out:
    """Collects theorems of one module."""
    def __init__(self):
        self.items = []
    def thm(self, name, stmt, proof, pub=False):
        self.items.append('%stheorem %s: $ %s $ =\n(named \'%s);\n' % ('pub ' if pub else '', name, stmt, proof))
    def raw(self, txt): self.items.append(txt)
    def lemma(self, name, th, pub=False, binders=''):
        self.items.append("%stheorem %s%s: $ paProvable %s %s $ =\n(named '%s);\n"
                          % ('pub ' if pub else '', name, binders, num(th.n), fm(th.f), th.proof))
        return Thm(th.n, th.f, name)
    def share(self, prefix, binders, hyps):
        """Emit long bound / substitution-equation proofs once as lemmas with the module binders."""
        self.kb = 0
        call = '(%%s %s)' % ' '.join(hyps) if hyps else '%s'
        def emit(stmt, p):
            self.kb += 1
            name = '%s_b%d' % (prefix, self.kb)
            self.items.append("theorem %s %s: $ %s $ =\n(named '%s);\n" % (name, binders, stmt, p))
            return call % name
        def bhook(kind, n, obj, p):
            stmt = ('paTermBound %s %s' % (num(n), eng.tm(obj))) if kind == 't' else ('paFormulaBound %s %s' % (num(n), fm(obj)))
            return emit(stmt, p)
        eng.BOUND_HOOK[0] = bhook
        eng.EQ_HOOK[0] = emit
        eng._BCACHE.clear(); eng._ECACHE.clear()
    def write(self, path, header):
        txt = header + '\n' + '\n'.join(self.items)
        open(path, 'w').write(txt.replace('bb215L3g_', 'g7L3g_'))
