"""Route T: term parameters for the GEN7 C2 natural-deduction engine.
('tl', S, k) is the hand term paTermLift k S, where S is an MM0 variable with a hypothesis
paTermBound n S (n = Lv(0)); renaming and substitution of it are d3_rl / d3_sl (pa-mm0/gen7/d3_tl.mm1)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'c2'))
from g7nd import *   # noqa
import g7nd
import bb215_l3_engine as eng
import bb215_l3_nd as nd

TP = {}          # S -> name of its hypothesis paTermBound n S

def TL(S, k): return ('tl', S, k)

_tm0, _tb0, _st0, _rt0, _lt0 = eng.tm, eng.tbound, eng.subst_t, eng.rename_t, eng.lift_t

def _tm(t):
    if t[0] == 'tl': return '(paTermLift %s %s)' % (_num(t[2]), t[1])
    if t[0] in ('s',): return '(paTermSuccessor %s)' % _tm(t[1])
    if t[0] in ('a', 'm'):
        return '(paTerm%s %s %s)' % ('Addition' if t[0] == 'a' else 'Multiplication', _tm(t[1]), _tm(t[2]))
    return _tm0(t)

def _num(k): return g7nd._num0(k)

def _tbound(n, t):
    if t[0] == 'tl':
        S, k = t[1], t[2]
        assert int(n) >= k, (n, t)
        return '(paTermBound_mono %s (mpbi (paTermBoundeq1 (eqtr addcom %s)) (paTermLift_bound %s)))' % (
            lv_le(k, int(n)), lv_add(0, k), TP[S])
    c = t[0]
    if c == 's': return '(mpbir paTermBound_successor %s)' % _tbound(n, t[1])
    if c in ('a', 'm'):
        nm = 'addition' if c == 'a' else 'multiplication'
        return '(mpbir paTermBound_%s (iani %s %s))' % (nm, _tbound(n, t[1]), _tbound(n, t[2]))
    return _tb0(n, t)

def _subst_t(d, t, u):
    c = u[0]
    if c == 'tl':
        S, k = u[1], u[2]
        assert d < k, (d, u)
        return TL(S, k - 1), '(d3_sl %s %s)' % (TP[S], g7nd.numle(d, k - 1))
    if c == 's':
        r, p = _subst_t(d, t, u[1]); return S_(r), '(eqtr paTermSubst_successor (paTermSuccessoreq %s))' % p
    if c in ('a', 'm'):
        r1, p1 = _subst_t(d, t, u[1]); r2, p2 = _subst_t(d, t, u[2])
        nm = 'addition' if c == 'a' else 'multiplication'; NM = 'Addition' if c == 'a' else 'Multiplication'
        return (c, r1, r2), '(eqtr paTermSubst_%s (paTerm%seq %s %s))' % (nm, NM, p1, p2)
    return _st0(d, t, u)

def _rename_t(d, u):
    c = u[0]
    if c == 'tl':
        S, k = u[1], u[2]
        assert d <= k, (d, u)
        return TL(S, k + 1), '(d3_rl %s %s)' % (TP[S], g7nd.numle(d, k))
    if c == 's':
        r, p = _rename_t(d, u[1]); return S_(r), '(eqtr paTermRename_successor (paTermSuccessoreq %s))' % p
    if c in ('a', 'm'):
        r1, p1 = _rename_t(d, u[1]); r2, p2 = _rename_t(d, u[2])
        nm = 'addition' if c == 'a' else 'multiplication'; NM = 'Addition' if c == 'a' else 'Multiplication'
        return (c, r1, r2), '(eqtr paTermRename_%s (paTerm%seq %s %s))' % (nm, NM, p1, p2)
    return _rt0(d, u)

def S_(t): return ('s', t)

def _lift_t(k, t):
    if t[0] == 'tl':
        S, j = t[1], t[2]
        return TL(S, k + j), '(eqtr (d3_ll %s) (paTermLifteq1 %s))' % (TP[S], eng.numadd(k, j) if k and j else ('add01' if k == 0 else 'add0'))
    c = t[0]
    if c == 's':
        r, p = _lift_t(k, t[1]); return S_(r), '(eqtr paTermRename_successor (paTermSuccessoreq %s))' % p
    if c in ('a', 'm'):
        r1, p1 = _lift_t(k, t[1]); r2, p2 = _lift_t(k, t[2])
        nm = 'addition' if c == 'a' else 'multiplication'; NM = 'Addition' if c == 'a' else 'Multiplication'
        return (c, r1, r2), '(eqtr paTermRename_%s (paTerm%seq %s %s))' % (nm, NM, p1, p2)
    return _lt0(k, t)
eng.lift_t = _lift_t

eng.tm, eng.tbound, eng.subst_t, eng.rename_t = _tm, _tbound, _subst_t, _rename_t
nd.tm, nd.tbound = _tm, _tbound
