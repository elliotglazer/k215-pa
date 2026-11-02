"""Route T, S6: generated normal-form lemmas for the PA front end's provability code (lanes/D3CHECK.md).
  python3 gen_s6.py MM0DIR [--standin] [--stubs OUT.mm0]   (stub d3r_ql_R copied from the reflection's out.mm0)
MM0DIR holds the .mm0 files of g2_generic_pa_thfinal's closure (for the def bodies). Writes
  pa-mm0/gen7/d3_s6.mm1 / .mm0   for every def D of g2paThCode's closure (except g2paQLCode and its bound wrappers):
      d3s6_D (p..): cD (r p) .. = r (D p ..)     (a META equality: cD's body is the code of D's body; r = d3r for
                                                  formula positions, d3rt for term positions, d3cn for raw numerals)
    proved by unfolding both sides and the d3r / d3rt equations, node by node (size ~ the def bodies, not their
    expansion), then
      d3_S6 (R): paFormulaBound 1 (g2paAxCode R) -> paFormulaBound 2 g2s1NCode -> paFormulaBound 4 g2s1SubCode ->
                 cPr (cEq (cg2paThCode (d3r R)) (d3r (g2paThCode R)))
    using the reflected d3r_ql_R (g2paQLCode without its three bound wrappers) and coded bounds (d3_EVfb).
--standin also writes pa-mm0/gen7/d3_s6defs.mm1 (the defs alone, copied from MM0DIR) for a local test; the host
version imports GEN3's modules instead (see lanes/D3CHECK.md, HOST NEEDED)."""
import glob, os, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.dirname(HERE))
from refl_lib import mm0_statements

FCON = {'paFormulaFalse': ([], 'd3r_false'), 'paFormulaEqual': (['T', 'T'], 'd3r_equal'), 'paFormulaAnd': (['F', 'F'], 'd3r_and'),
        'paFormulaOr': (['F', 'F'], 'd3r_or'), 'paFormulaImp': (['F', 'F'], 'd3r_imp'), 'paFormulaAll': (['F'], 'd3r_all'),
        'paFormulaEx': (['F'], 'd3r_ex')}
TCON = {'paTermZero': ([], 'd3rt_zero'), 'paTermVariable': (['N'], 'd3rt_var'), 'paTermSuccessor': (['T'], 'd3rt_succ'),
        'paTermAddition': (['T', 'T'], 'd3rt_add'), 'paTermMultiplication': (['T', 'T'], 'd3rt_mul')}
CON = dict(FCON); CON.update(TCON)
RR = {'F': 'd3r', 'T': 'd3rt', 'N': 'd3cn'}
SKIP = {'g2paQLCode', 'g2paB1', 'g2paB2', 'g2paB4'}

def toks(s): return re.findall(r'\(|\)|[^\s()]+', s)
def parse(s):
    t = toks(s); p = [0]
    def e():
        x = t[p[0]]; p[0] += 1
        if x == '(':
            l = []
            while t[p[0]] != ')':
                l.append(e())
            p[0] += 1
            return l[0] if len(l) == 1 else l
        return x
    r = e()
    assert p[0] == len(t), s[:200]
    return r
def unparse(e): return e if isinstance(e, str) else '(' + ' '.join(unparse(x) for x in e) + ')'

def load(d):
    defs, texts = {}, {}
    for f in glob.glob(os.path.join(d, '*.mm0')):
        for kw, nm, txt in mm0_statements(open(f).read()):
            if kw == 'def' and '$' in txt:
                n = nm.rstrip(':;')
                hdr, body = txt.split('=', 1)
                vs = [v for g in re.findall(r'\(([^)]*):', hdr) for v in g.split() if not v.startswith('.')]
                defs[n] = (vs, parse('(' + body.strip().rstrip(';').strip().strip('$').strip() + ')'))
                texts[n] = txt
    return defs, texts

def heads(e, out):
    if isinstance(e, str): out.add(e); return
    for x in e: heads(x, out)

def closure(defs, roots):
    seen, order = set(), []
    def visit(d):
        if d in seen or d not in defs: return
        seen.add(d)
        s = set(); heads(defs[d][1], s)
        for h in sorted(s):
            if h in defs and h not in defs[d][0]: visit(h)
        order.append(d)
    for r in roots: visit(r)
    return order

def infer(defs, order):
    """sort of every def (F / T) and of every parameter (F / T / N)."""
    dsort, psort = {}, {d: {} for d in order}
    changed = True
    def esort(e, d):
        h = e if isinstance(e, str) else e[0]
        if h in FCON: return 'F'
        if h in TCON: return 'T'
        if h in dsort: return dsort[h]
        if h in psort[d]: return psort[d][h]
        return None
    def walk(e, d, want):
        nonlocal changed
        if isinstance(e, str):
            if e in defs[d][0] and want and psort[d].get(e) != want:
                assert e not in psort[d], (d, e, psort[d].get(e), want)
                psort[d][e] = want; changed = True
            return
        h, args = e[0], e[1:]
        if h in CON:
            for a, w in zip(args, CON[h][0]): walk(a, d, w)
        elif h in psort:
            for a, p in zip(args, defs[h][0]): walk(a, d, psort[h].get(p))
        elif h == 'suc':
            for a in args: walk(a, d, 'N')
        else:
            for a in args: walk(a, d, None)
    while changed:
        changed = False
        for d in order:
            walk(defs[d][1], d, dsort.get(d))
            s = esort(defs[d][1], d)
            if s and dsort.get(d) != s:
                dsort[d] = s; changed = True
    return dsort, psort

def num_proof(e, d, psort):
    """proof of code(e) = d3cn e for a raw numeral expression."""
    if isinstance(e, str):
        if e in psort[d]: return 'eqid'
        if e == '0': return '(eqcom d3cn_0)'
        if re.fullmatch(r'\d+', e): return '(eqcom d3e_cn%s)' % e
        raise ValueError(e)
    assert e[0] == 'suc', e
    return '(eqtr (cSuceq %s) (eqcom d3cn_S))' % num_proof(e[1], d, psort)

def proof(e, d, defs, dsort, psort, want):
    """proof of code(e) = RR[want] e."""
    if want == 'N': return num_proof(e, d, psort)
    if isinstance(e, str):
        if e in psort[d]: return 'eqid'
        if e in CON: return '(eqcom %s)' % CON[e][1]
        if e in defs: return 'd3s6_' + e
        raise ValueError(e)
    h, args = e[0], e[1:]
    if h in CON:
        ps = [proof(a, d, defs, dsort, psort, w) for a, w in zip(args, CON[h][0])]
        return '(eqtr (c%seq %s) (eqcom %s))' % (h, ' '.join(ps), CON[h][1])
    if h in defs:
        ps = [proof(a, d, defs, dsort, psort, psort[h].get(p, 'F')) for a, p in zip(args, defs[h][0])]
        return '(eqtr (c%seq %s) d3s6_%s)' % (h, ' '.join(ps), h)
    raise ValueError(h)

def main(mm0dir, standin=False):
    defs, texts = load(mm0dir)
    order = closure(defs, ['g2paThCode'])
    lem = [d for d in closure(defs, ['g2paAxCode', 'g2s1NCode', 'g2s1SubCode']) if d not in SKIP]
    dsort, psort = infer(defs, lem)
    nums = set()
    for d in lem:
        heads(defs[d][1], nums)
    kmax = max([int(x) for x in nums if re.fullmatch(r'\d+', x)] + [10])
    out = ['import "d3_s5.mm1";', 'import "d3_s6defs.mm1";' if standin else 'import "../g2_generic_pa_thfinal.mm1";',
           'import "../d3_adqsrc.mm1";' if not standin else 'import "d3_s6ql.mm1";', '',
           '-- Route T S6 (lanes/D3CHECK.md), generated by tools/gen7/d3/gen_s6.py: normal forms of the code of g2paThCode R.',
           'do {']
    for d in order:
        out.append("  (if (def? (get-decl 'c%seqd)) () (default-annotate 'c%s))" % (d, d))  # guarded: shared cg2s1* (g7_s6sf, d3_s3h)
    out.append('};')
    if STUB_SRC:
        out.insert(4, subprocess.check_output([sys.executable, os.path.join(HERE, 'stubs.py'), STUB_SRC, STUB_ROOTS], universal_newlines=True))
    for k in range(9, kmax + 1):
        out.append("theorem d3e_cn%d: $ d3cn %d = cd%d $ = '(eqtr d3cn_S (cSuceq d3e_cn%d));" % (k, k, k, k - 1))
    for d in lem:
        vs = defs[d][0]
        bind = ' (%s: nat)' % ' '.join(vs) if vs else ''
        lhs = 'c%s%s' % (d, ''.join(' (%s %s)' % (RR[psort[d].get(v, 'F')], v) for v in vs)) if vs else 'c' + d
        rhs = '%s %s' % (RR[dsort[d]], '(%s %s)' % (d, ' '.join(vs)) if vs else d)
        out.append("theorem d3s6_%s%s: $ %s = %s $ =\n'%s;" % (d, bind, lhs, rhs, proof(defs[d][1], d, defs, dsort, psort, dsort[d])))
    # the if-free QL body at r-codes
    ql = defs['g2paQLCode']
    from gen_adqsrc import noif
    psq = {'g2paQLCode': {v: 'F' for v in ql[0]}}
    out.append("theorem d3s6_QL (%s: nat): $ %s = d3r %s $ =\n'%s;" % (
        ' '.join(ql[0]),
        code_txt(noif(ql[1]), ql[0]),
        unparse(noif(ql[1])),
        proof(noif(ql[1]), 'g2paQLCode', defs, dsort, psq, 'F')))
    out.append(r'''pub theorem d3_S6 (R: nat): $ paFormulaBound 1 (g2paAxCode R) -> paFormulaBound 2 g2s1NCode -> paFormulaBound 4 g2s1SubCode ->
  cPr (cEq (cg2paThCode (d3r R)) (d3r (g2paThCode R))) $ =
'(exp (exp (mpbird (syl cPreq (cEqeqd (a1i (cg2paQLCodeeq d3s6_g2paAxCode d3s6_g2s1NCode d3s6_g2s1SubCode))
    (d3reqd (mpd anr (sylc d3r_ql (syl anl anl) (syl anr anl))))))
  (mpbird (a1i (cPreq (cEqeq eqid (eqcom d3s6_QL))))
    (sylc d3_cmp (sylc d3_cmp (sylc d3_cmp (a1i d3r_ql_R)
      (mpbid (a1i (cPreq (cpaFormulaBoundeq d3e_cn1 eqid))) (syl d3_EVfb (syl anl anl))))
      (mpbid (a1i (cPreq (cpaFormulaBoundeq d3e_cn2 eqid))) (syl d3_EVfb (syl anr anl))))
      (mpbid (a1i (cPreq (cpaFormulaBoundeq d3e_cn4 eqid))) (syl d3_EVfb anr)))))));''')
    out.append("pub theorem d3_s6_final: $ paFormulaBound 0 paFormulaFalse $ = 'paFormulaBound_false;")
    p = os.path.join(ROOT, 'pa-mm0', 'gen7', 'd3_s6.mm1')
    open(p, 'w').write('\n'.join(out) + '\n')
    print('defs in closure', len(order), 'lemmas', len(lem), 'bytes', os.path.getsize(p))
    if standin:
        sd = ['import "../g2_generic_s1_class.mm1";', '', '-- TEST ONLY stand-in: the defs of g2paThCode\'s closure, copied from GEN3\'s .mm0.']
        for d in order:
            sd.append(texts[d].replace('def ', '@_ def ', 1) if not texts[d].startswith('@_') else texts[d])
        sd.append("pub theorem d3s6_root (R: nat): $ g2paThCode R = g2paThCode R $ = 'eqid;")
        sd.append("pub theorem d3_s6defs_final: $ paFormulaBound 0 paFormulaFalse $ = 'paFormulaBound_false;")
        open(os.path.join(ROOT, 'pa-mm0', 'gen7', 'd3_s6defs.mm1'), 'w').write('\n'.join(sd) + '\n')

def code_txt(e, params):
    """the code term of e with params as code variables (r p substituted): matches cg2paQLCode's unfolding."""
    if isinstance(e, str):
        if e in params: return '(d3r %s)' % e
        if e in CON: return 'c' + e
        if e == '0': return 'c0'
        if re.fullmatch(r'\d+', e): return 'cd' + e
        return 'c' + e
    h, args = e[0], e[1:]
    if h == 'suc': return '(cSuc %s)' % code_txt(args[0], params)
    return '(c%s %s)' % (h, ' '.join(code_txt(a, params) for a in args))

STUB_SRC = None
STUB_ROOTS = os.path.join(HERE, 'roots_s6.txt')
if __name__ == '__main__':
    sys.path.insert(0, HERE)
    a = sys.argv[1:]
    if '--stubs' in a:
        i = a.index('--stubs'); STUB_SRC = a[i + 1]; del a[i:i + 2]
    main(a[0], '--standin' in a)
