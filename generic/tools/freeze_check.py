r"""G2GEN freeze: the approved spec targets/g2_generic.mm0 with its abstract defs at the literal readings of the two
host-checked links, and the check that the freeze is exactly that.
  python3 tools/gen7/freeze_check.py [--write] [--ref origin/main] [--pa LINKED.mm0] [--sf LINKED.mm0]   (repo root)
Linked files (default: read with `git show REF:<path>`, nothing is checked out):
  PA  results/00000-C-084-gen7-g2pa_inst/linked.mm0   (G2_generic_pa, BB_generic_pa_thm2, BB_generic_pa_thm3)
  SET results/00000-C-092-gen7-g2sf_spec/linked.mm0   (G2_generic_set, BB_generic_set_thm2 / _thm3 / _thm2_P / _thm3_P)
Frozen files (pa-mm0/; --write regenerates them, deterministically, from the approved files and the linked files):
  targets/g2_generic_frozen.mm0      = targets/g2_generic.mm0, import of g2_generic_defs -> g2_generic_defs_frozen
  g2_generic_defs_frozen.mm0         = g2_generic_defs.mm0, 6 abstract defs with bodies, zfc_std_defs -> _frozen
  zfc_std_defs_frozen.mm0            = zfc_std_defs.mm0, 2 abstract defs with bodies, + import of the support file
  g2_generic_freeze_support.mm0      the defs the frozen bodies use that the approved spec does not define (g2paThCode,
                                     g2szRz, g2sf*Code, paS1Class, paS1Holds and their closure), copied verbatim from
                                     the linked files (identical in both where both have them), dependency order.
Checks (all must hold; PASS / FAIL per item):
  (a) every frozen def and every support def equals (full statement, whitespace-normalized) its statement in each linked
      file that contains it, and occurs in at least one; paSigma1 / paSigma1True occur in both;
  (b) every frozen file equals its approved file line by line except: the frozen abstract-def lines, the renamed import
      lines and the one added support import (regenerated in memory and compared byte for byte, and diffed);
  (c) the headline theorems of both linked files equal the frozen spec's text;
  (d) EVERY statement of each linked file (sorts, terms, defs, axioms, theorems, notations) occurs in the frozen spec
      closure with the identical text, except the PA link's G2_pa / BB_pa_thm2 / BB_pa_thm3 (approved separately,
      gen7/g2pa_inst); the linked axioms are exactly peano's 26; the defs left abstract occur in neither link."""
import argparse, difflib, hashlib, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PA = os.path.join(ROOT, 'pa-mm0')
LINKED = {'pa': 'results/00000-C-084-gen7-g2pa_inst/linked.mm0', 'sf': 'results/00000-C-092-gen7-g2sf_spec/linked.mm0'}
HEAD = {'pa': ['G2_generic_pa', 'BB_generic_pa_thm2', 'BB_generic_pa_thm3'],
        'sf': ['G2_generic_set', 'BB_generic_set_thm2', 'BB_generic_set_thm3', 'BB_generic_set_thm2_P',
               'BB_generic_set_thm3_P']}
EXTRA = {'pa': {'G2_pa', 'BB_pa_thm2', 'BB_pa_thm3'}, 'sf': set()}
# approved file -> (frozen file, abstract defs frozen in it, import renames, added import or None)
FILES = [
    ('targets/g2_generic.mm0', 'targets/g2_generic_frozen.mm0', [],
     {'../g2_generic_defs.mm0': '../g2_generic_defs_frozen.mm0'}, None),
    ('g2_generic_defs.mm0', 'g2_generic_defs_frozen.mm0',
     ['paSigma1', 'paSigma1True', 'zfcStdAxRecognizer', 'sfThMemCode', 'sfThClosedCode', 'paThCode'],
     {'zfc_std_defs.mm0': 'zfc_std_defs_frozen.mm0'}, None),
    ('zfc_std_defs.mm0', 'zfc_std_defs_frozen.mm0', ['zfcStdValidCode', 'zfcStdGoalCode'], {},
     'g2_generic_freeze_support.mm0'),
]
SUPPORT = 'g2_generic_freeze_support.mm0'
SPEC, FROZEN = 'targets/g2_generic.mm0', 'targets/g2_generic_frozen.mm0'

# ---------------------------------------------------------------------------------------------------------------------
def statements(text):
    """Top-level statements (comments outside math strings dropped)."""
    out, buf, i, n = [], [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith('--', i):
            j = text.find('\n', i); i = n if j < 0 else j; continue
        if c == '$':
            j = text.index('$', i + 1); buf.append(text[i:j + 1]); i = j + 1; continue
        if c == ';':
            buf.append(';'); out.append(''.join(buf).strip()); buf = []; i += 1; continue
        buf.append(c); i += 1
    assert not ''.join(buf).strip(), 'trailing text'
    return out

def norm(s):
    return ' '.join(s.replace('$', ' $ ').split()).replace(' ;', ';')

KW = re.compile(r'^((?:(?:pure|strict|provable|free) )*sort|term|def|axiom|theorem|notation|infixl|infixr|prefix|'
                r'coercion|delimiter|import|input|output)\b\s*([^\s:(;{$]*)')

def key(st):
    m = KW.match(st)
    if not m: raise SystemExit('unparsed statement: ' + st[:80])
    k, nm = m.group(1), m.group(2)
    if k.endswith('sort'): k = 'sort'
    if k == 'delimiter': nm = norm(st)
    if k == 'import': nm = st.split('"')[1]
    return k, nm

def closure(path, seen=None, acc=None):
    if seen is None: seen, acc = set(), []
    path = os.path.normpath(path)
    if path in seen: return acc
    seen.add(path)
    for st in statements(open(path).read()):
        k, nm = key(st)
        if k == 'import': closure(os.path.join(os.path.dirname(path), nm), seen, acc)
        else: acc.append((path, k, nm, st))
    return acc

def is_abstract(st):
    return st.startswith('def') and '$' not in st

def idents(st):
    body = st[st.index('$'):] if '$' in st else ''
    return set(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', body))

def linked_text(args, side):
    p = getattr(args, side)
    if p: return open(p).read()
    return subprocess.run(['git', '-C', ROOT, 'show', '%s:%s' % (args.ref, LINKED[side])], check=True,
                          capture_output=True, text=True).stdout

def linked_map(text):
    d, order = {}, []
    for st in statements(text):
        kn = key(st)
        assert kn not in d, ('duplicate in link', kn)
        d[kn] = st; order.append(kn)
    return d, order

# ---------------------------------------------------------------------------------------------------------------------
def build(L):
    """The frozen files' texts from the approved files and the linked maps L = {'pa': (map, order), 'sf': ...}."""
    approved = {k for _, k_, n, _ in closure(os.path.join(PA, SPEC)) for k in [(k_, n)]}
    frozen_names = [n for _, _, names, _, _ in FILES for n in names]
    def linked_def(nm):
        for side in ('pa', 'sf'):
            st = L[side][0].get(('def', nm))
            if st is not None: return st
        raise SystemExit('FAIL: def %s in neither link' % nm)
    # support closure: defs used by the frozen bodies that the approved spec does not define
    sup, todo = {}, list(frozen_names)
    while todo:
        nm = todo.pop()
        for t in idents(linked_def(nm)):
            if ('def', t) not in approved and ('term', t) not in approved and t not in sup and t != nm and \
               any(('def', t) in L[s][0] for s in L):
                sup[t] = linked_def(t); todo.append(t)
    # dependency order: DFS over the PA link order, then the set link order
    out, done = [], set()
    def emit(nm, stack=()):
        if nm in done: return
        assert nm not in stack, ('cycle', nm)
        for t in sorted(idents(sup[nm])):
            if t in sup and t != nm: emit(t, stack + (nm,))
        done.add(nm); out.append(sup[nm])
    for side in ('pa', 'sf'):
        for k, nm in L[side][1]:
            if k == 'def' and nm in sup: emit(nm)
    imps = sorted({os.path.relpath(f, PA).replace(os.sep, '/') for f, k, nm, st in closure(os.path.join(PA, SPEC))
                   if k in ('def', 'term') and any(nm in idents(s) for s in sup.values())})
    texts = {SUPPORT: ''.join('import "%s";\n' % i for i in imps if not i.startswith('..')) +
             '\n-- GENERATED by tools/gen7/freeze_check.py --write (lane G2GEN freeze). Do not edit.\n'
             '-- The defs used by the frozen bodies of g2_generic_defs_frozen.mm0 / zfc_std_defs_frozen.mm0 that the\n'
             '-- approved spec does not define, copied verbatim from the host-checked links (C-084, C-092).\n' +
             ''.join(st + '\n' for st in out)}
    changed = {}
    for src, dst, names, ren, add in FILES:
        lines = open(os.path.join(PA, src)).read().split('\n')
        new, ch = [], []
        for i, ln in enumerate(lines):
            m = re.match(r'^def (\w+)\b[^$;]*;\s*$', ln)
            if m and m.group(1) in names:
                st = linked_def(m.group(1))
                h = ln.rstrip()[:-1]
                assert norm(st).startswith(norm(h) + ' ='), ('header differs', ln, st[:120])
                ln = h + ' = ' + st[st.index('$'):]
                ch.append((i, 'def ' + m.group(1)))
            m = re.match(r'^import "([^"]+)";$', ln)
            if m and m.group(1) in ren:
                ln = 'import "%s";' % ren[m.group(1)]; ch.append((i, 'import'))
            new.append(ln)
            if add and i == max(j for j, x in enumerate(lines) if x.startswith('import ')):
                new.append('import "%s";' % add); ch.append((i, 'added import'))
        got = {n for _, n in ch if n.startswith('def ')}
        assert got == {'def ' + n for n in names}, ('missing frozen def line', src, got)
        texts[dst] = '\n'.join(new); changed[dst] = (src, ch)
    return texts, changed, sorted(sup)

# ---------------------------------------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--write', action='store_true'); ap.add_argument('--ref', default='origin/main')
    ap.add_argument('--pa'); ap.add_argument('--sf')
    args = ap.parse_args()
    L = {s: linked_map(linked_text(args, s)) for s in ('pa', 'sf')}
    texts, changed, sup = build(L)
    if args.write:
        for f, t in texts.items():
            open(os.path.join(PA, f), 'w', newline='\n').write(t)
        print('wrote', ', '.join(sorted(texts)))
    ok = True
    def res(tag, good, msg):
        nonlocal ok
        ok &= good
        print('%s %s: %s' % ('PASS' if good else 'FAIL', tag, msg))
    fcl = closure(os.path.join(PA, FROZEN))
    fmap = {}
    for f, k, nm, st in fcl:
        assert (k, nm) not in fmap or k in ('import',), ('duplicate in frozen closure', k, nm)
        fmap[(k, nm)] = st
    frozen_names = [n for _, _, names, _, _ in FILES for n in names]
    # (a)
    bad = []
    for nm in frozen_names + sup:
        st = fmap.get(('def', nm))
        hits = [s for s in L if ('def', nm) in L[s][0]]
        if st is None or is_abstract(st) or not hits: bad.append(nm); continue
        bad += [nm + '@' + s for s in hits if norm(L[s][0][('def', nm)]) != norm(st)]
    bad += [n for n in ('paSigma1', 'paSigma1True') if not all(('def', n) in L[s][0] for s in L)]
    res('(a) frozen + support def bodies = linked bodies', not bad,
        '%d frozen defs, %d support defs%s' % (len(frozen_names), len(sup), (', bad: %s' % bad) if bad else ''))
    # (b)
    bad = []
    for dst, t in texts.items():
        if open(os.path.join(PA, dst)).read() != t: bad.append(dst + ' (not as generated)')
    for dst, (src, ch) in changed.items():
        a = open(os.path.join(PA, src)).read().split('\n'); b = open(os.path.join(PA, dst)).read().split('\n')
        allowed = {n for _, _, names, _, _ in FILES for n in names}
        for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
            if op == 'equal': continue
            for ln in a[i1:i2]:
                m = re.match(r'^(def (\w+)\b|import ")', ln)
                if not m or (m.group(2) and m.group(2) not in allowed): bad.append('%s: -%s' % (dst, ln[:60]))
            for ln in b[j1:j2]:
                m = re.match(r'^(def (\w+)\b|import ")', ln)
                if not m or (m.group(2) and m.group(2) not in allowed): bad.append('%s: +%s' % (dst, ln[:60]))
    res('(b) frozen files = approved files outside the frozen def / import lines', not bad,
        '; '.join('%s: %d lines changed' % (d, len(c)) for d, (s, c) in changed.items()) + (' bad: %s' % bad if bad else ''))
    # (c)
    bad = []
    for s in L:
        for nm in HEAD[s]:
            a, b = L[s][0].get(('theorem', nm)), fmap.get(('theorem', nm))
            if a is None or b is None or norm(a) != norm(b): bad.append(nm)
    res('(c) headline theorems of both links = frozen spec text', not bad,
        '%s%s' % (', '.join(HEAD['pa'] + HEAD['sf']), (' bad: %s' % bad) if bad else ''))
    # (d)
    bad, peano = [], [kn for kn in fmap if kn[0] == 'axiom']
    for s in L:
        for kn, st in L[s][0].items():
            if kn[0] == 'theorem' and kn[1] in EXTRA[s]: continue
            if kn not in fmap or norm(fmap[kn]) != norm(st): bad.append('%s:%s %s' % (s, kn[0], kn[1]))
        ax = sorted(n for k, n in L[s][0] if k == 'axiom')
        if len(ax) != 26 or any(os.path.basename(f) != 'peano.mm0' for f, k, n, _ in fcl if k == 'axiom' and n in ax):
            bad.append('%s: axioms %d' % (s, len(ax)))
    still = sorted(n for (k, n), st in fmap.items() if k == 'def' and is_abstract(st))
    used = [n for n in still if any(('def', n) in L[s][0] and not is_abstract(L[s][0][('def', n)]) for s in L)]
    bad += ['abstract def with a body in a link: ' + n for n in used]
    res('(d) every linked statement is in the frozen closure verbatim; axioms = peano 26', not bad,
        'pa %d / sf %d statements; extra (approved separately): %s%s' % (
            len(L['pa'][0]), len(L['sf'][0]), ', '.join(sorted(EXTRA['pa'])), (' bad: %s' % bad[:20]) if bad else ''))
    nonpeano = [n for n in still if os.path.basename(next(f for f, k, m, _ in fcl if k == 'def' and m == n)) != 'peano.mm0']
    print('left abstract (no host-checked statement uses them; not in either link):', ', '.join(nonpeano))
    for f in [FROZEN] + [d for _, d, _, _, _ in FILES[1:]] + [SUPPORT]:
        print('sha256 %s  pa-mm0/%s' % (hashlib.sha256(open(os.path.join(PA, f), 'rb').read()).hexdigest(), f))
    print('FREEZE CHECK', 'PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
