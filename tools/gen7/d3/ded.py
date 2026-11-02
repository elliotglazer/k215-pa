r"""Route T: weak deduction theorem wrappers. From a hypothesis-form MM1 lemma, an implication-form version:
  H1 -> ... -> Hk -> C
by substituting each primed variable v by  (if H v default)  (H = H1 /\ ... /\ Hk, left-nested), proving every
Hj at the substituted values by cases on H, applying the lemma, and rewriting back under H."""
import re

SETHEADS = {'d3Lv', 'd3W', 'd3L0', 'trAbsMap', 'sfRenameDepthMap', 'paTermLiftMap', 'g7F', 'paTermShiftMap'}
SETVARS = {'M'}
ANNOT = False   # annotate the primed hypotheses / conclusion (needed when the call does not fix every primed value)

def tok(s):
    return re.findall(r'\(|\)|[^\s()]+', s)

def parse(s):
    t = tok(s); pos = [0]
    def p():
        x = t[pos[0]]; pos[0] += 1
        if x == '(':
            items = []
            while t[pos[0]] != ')':
                items.append(p())
            pos[0] += 1
            return items
        return x
    r = p()
    assert pos[0] == len(t), s
    return r

def unparse(e):
    return e if isinstance(e, str) else '(' + ' '.join(unparse(x) for x in e) + ')'

def has(e, vs):
    return (e in vs) if isinstance(e, str) else any(has(x, vs) for x in e)

def eqd(e, pv):
    """Proof of G -> e[primed] = e (pv: var -> proof of G -> v' = v)."""
    if isinstance(e, str):
        return pv[e] if e in pv else '(a1i eqid)'
    if not has(e, pv):
        return '(a1i eqid)'
    f, args = e[0], e[1:]
    ps = []
    for a in args:
        if (isinstance(a, str) and a in SETVARS) or (isinstance(a, list) and a and a[0] in SETHEADS):
            assert not has(a, pv)
            ps.append('eqsidd')
        else:
            ps.append(eqd(a, pv))
    return '(%seqd %s)' % (f, ' '.join(ps))

def subst(e, m):
    if isinstance(e, str): return m.get(e, e)
    return [subst(x, m) for x in e]

def wff_cong(w, pv):
    """w: a wff 'head A B ...' (prefix, top-level) or 'X = Y'. Returns proof of G -> (w[primed] <-> w)."""
    if ' = ' in w and not w.strip().startswith('('):
        l, r = w.split(' = ')
        return '(eqeqd %s %s)' % (eqd(parse('(' + l + ')'), pv), eqd(parse('(' + r + ')'), pv))
    e = parse('(' + w + ')')
    head = e[0]
    k = len(e) - 1
    # congruence in the last argument only (the others carry no primed variable)
    for a in e[1:-1]:
        assert not has(a, pv), (w, a)
    if k == 1:
        return '(syl %seq %s)' % (head, eqd(e[-1], pv))
    return '(syl %seq%d %s)' % (head, k, eqd(e[-1], pv))

def conj_proj(k, j):
    """Proof of H -> Hj for H = ((H1 /\\ H2) /\\ ...) /\\ Hk (k hyps, j 0-based)."""
    if k == 1: return 'id'
    if j == k - 1: return 'anr'
    p = conj_proj(k - 1, j)
    return 'anl' if p == 'id' else '(syl %s anl)' % p

def wrapper(name, binders, hyps, concl, primed, dflt_proofs, call):
    """hyps: wff texts over the plain variables; concl: wff text; primed: list of (var, default text);
    dflt_proofs: proofs of hyp_j[defaults] (texts); call: lemma application with {h0}.. for the proofs of
    hyp_j[primed]. Returns MM1 theorem text."""
    k = len(hyps)
    H = '(%s)' % hyps[0] if k == 1 else None
    Hs = hyps[0]
    for h in hyps[1:]:
        Hs = '(%s) /\\ (%s)' % (Hs, h) if False else '%s /\\ %s' % ('(' + Hs + ')' if '/\\' in Hs or '->' in Hs else Hs, h)
    # primed value terms
    Htxt = ' /\\ '.join('(%s)' % h for h in hyps) if k > 1 else hyps[0]
    # left-nested conjunction text
    acc = '(%s)' % hyps[0]
    for h in hyps[1:]:
        acc = '(%s /\\ (%s))' % (acc, h)
    Htxt = acc
    m = {v: parse('(if %s %s %s)' % (Htxt, v, d)) for v, d in primed}
    pv = {v: 'ifpos' for v, _ in primed}
    pn = {v: 'ifneg' for v, _ in primed}
    dm = {v: parse(d) if d.startswith('(') else d for v, d in primed}
    hp = []
    for j, h in enumerate(hyps):
        c1 = '(mpbird %s %s)' % (wff_cong(h, pv), conj_proj(k, j))
        # under ~H the primed values are the defaults: proof of h[defaults] then rewrite
        c2 = '(mpbird %s (a1i %s))' % (wff_cong_to(h, pn, dm), dflt_proofs[j])
        hp.append('(cases %s %s)' % (c1, c2))
    def primed_txt(w):
        return re.sub(r'[A-Za-z_][A-Za-z0-9_]*', lambda mm: unparse(m[mm.group(0)]) if mm.group(0) in m else mm.group(0), w)
    if ANNOT:
        hp = ['{%s : $ %s $}' % (hp[j], primed_txt(hyps[j])) for j in range(k)]
    app = call.format(**{'h%d' % j: hp[j] for j in range(k)})
    if ANNOT:
        app = '{%s : $ %s $}' % (app, primed_txt(concl))
    main = '(mpbid %s (a1i %s))' % (wff_cong(concl, pv), app)
    for _ in range(k - 1):
        main = '(exp %s)' % main
    stmt = 'theorem %s %s: $ %s $' % (name, binders, ' -> '.join(hyps + [concl]))
    return stmt + " =\n'" + main + ";\n"

def wff_cong_to(w, pn, dm):
    """Proof of ~H -> (w[primed] <-> w[defaults])."""
    if ' = ' in w and not w.strip().startswith('('):
        l, r = w.split(' = ')
        return '(eqeqd %s %s)' % (eqd_to(parse('(' + l + ')'), pn, dm), eqd_to(parse('(' + r + ')'), pn, dm))
    e = parse('(' + w + ')')
    for a in e[1:-1]:
        assert not has(a, pn), (w, a)
    if len(e) == 2:
        return '(syl %seq %s)' % (e[0], eqd_to(e[-1], pn, dm))
    return '(syl %seq%d %s)' % (e[0], len(e) - 1, eqd_to(e[-1], pn, dm))

def eqd_to(e, pn, dm):
    """Proof of ~H -> e[primed] = e[defaults]."""
    if isinstance(e, str):
        return pn[e] if e in pn else '(a1i eqid)'
    if not has(e, pn):
        return '(a1i eqid)'
    f, args = e[0], e[1:]
    ps = []
    for a in args:
        if (isinstance(a, str) and a in SETVARS) or (isinstance(a, list) and a and a[0] in SETHEADS):
            ps.append('eqsidd')
        else:
            ps.append(eqd_to(a, pn, dm))
    return '(%seqd %s)' % (f, ' '.join(ps))
