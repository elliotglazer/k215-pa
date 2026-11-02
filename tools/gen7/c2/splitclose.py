"""GEN7 C5: split a module's import closure into K chunks for the staged link (memory: one compile per chunk).

  python3 splitclose.py MODULE OUTDIR BUDGET_MB [PREFIX]

MODULE relative to pa-mm0 (as for tools/gen7/lcheck.py). Writes OUTDIR/gen7/PREFIX<i>.mm1 / .mm0 (i = 1..K, default
PREFIX rc): chunk i = the closure's modules in lcheck's (topological) order, cut at BUDGET_MB of source, flattened (imports removed),
preceded by the earlier chunks with every theorem that chunk i names turned into a STUB axiom (statement text unchanged, proof dropped;
defs, notations and do-blocks kept). Linking chunk 1, 2, .. in order onto R (tools/gen7/link.py) replaces every stub by
the theorem that the earlier chunk proved, so mm0-c checks the result against the real statements."""
import os, re, sys
sys.argv, args = sys.argv[:1], sys.argv[1:]
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
src = open(os.path.join(os.path.dirname(HERE), 'lcheck.py')).read().replace('\nmain()', '\n')
L = {'__file__': os.path.join(os.path.dirname(HERE), 'lcheck.py'), '__name__': 'lcheck'}
exec(compile(src, 'lcheck.py', 'exec'), L)
mod, od, BUDGET = args[0], args[1], int(float(args[2]) * 1e6)
pre = args[3] if len(args) > 3 else 'rc'
IMPORT = L['IMPORT']


def statements(txt):
    """split MM1/MM0 text into top-level statements (each ends with ';' outside comments, strings, math, brackets)."""
    out, i, n, st, depth = [], 0, len(txt), 0, 0
    while i < n:
        c = txt[i]
        if c == '-' and txt.startswith('--', i):
            j = txt.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c == '"':
            i += 1
            while i < n and txt[i] != '"':
                i += 2 if txt[i] == '\\' else 1
            i += 1
            continue
        if c == '$':
            j = txt.index('$', i + 1)
            i = j + 1
            continue
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif c == ';' and depth == 0:
            out.append(txt[st:i + 1])
            st = i + 1
        i += 1
    if txt[st:].strip():
        out.append(txt[st:])
    return out


def proof_eq(s):
    """index of the '=' that starts the proof of a theorem statement (depth 0, outside math/comments), or -1."""
    i, n, depth = 0, len(s), 0
    while i < n:
        c = s[i]
        if c == '-' and s.startswith('--', i):
            j = s.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c == '$':
            i = s.index('$', i + 1) + 1
            continue
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif c == '=' and depth == 0:
            return i
        i += 1
    return -1


THM = re.compile(r'^(\s*(?:--[^\n]*\n\s*)*)(?:(?:pub|local)\s+)?theorem\b')


ID = re.compile(r'[A-Za-z_][A-Za-z0-9_.]*')
DO = re.compile(r'^\s*(?:--[^\n]*\n\s*)*do\b')


MOD = re.compile(r'^(\s*(?:--[^\n]*\n\s*)*)(@_\s+)?(abstract\s+)?(?:(?:pub|local)\s+)?(?=def\b|term\b)')


NOTA = re.compile(r'^\s*(?:--[^\n]*\n\s*)*(?:notation|infixl|infixr|prefix|coercion)\s+([A-Za-z_][A-Za-z0-9_.]*)')
DEF = re.compile(r'def\s+([A-Za-z_][A-Za-z0-9_.]*)')


def classify(txt):
    """MM1 text -> [(kind, name, statement)]: kind thm / def / do / nota / other."""
    out = []
    for s in statements(txt):
        m = THM.match(s)
        if m:
            out.append(('thm', ID.match(s[m.end():].lstrip()).group(0), s))
            continue
        m = MOD.match(s)
        if m and s[m.end():].startswith('def'):
            out.append(('def', DEF.match(s[m.end():]).group(1), s))
            continue
        if DO.match(s):
            out.append(('do', None, s))
            continue
        m = NOTA.match(s)
        out.append(('nota', m.group(1), s) if m else ('other', None, s))
    return out


def stub(kind, s, mm0):
    """an earlier chunk's kept statement as stub text: theorem -> axiom (proof dropped); local def -> public def
    (so the spec can state the stubs that mention it); the .mm0 drops do-blocks and the MM1-only def modifiers."""
    if kind == 'thm':
        m = THM.match(s)
        head = m.group(1) + 'axiom' + s[m.end():]
        k = proof_eq(head)
        if k < 0:
            raise SystemExit('no proof in: ' + s[:200])
        return head[:k].rstrip() + ';'
    if kind == 'do':
        return '' if mm0 else s
    if kind == 'def':
        return MOD.sub(r'\1' if mm0 else r'\1\2\3', s, count=1)
    return s


m1, m0 = [], []
L['closure'](mod + '.mm1', m1, set())
L['closure'](mod + '.mm0', m0, set())
chunk, acc, K = {}, 0, 1
for rel, p, t in m1:
    if acc and acc + len(t) > BUDGET:
        K, acc = K + 1, 0
    chunk[rel[:-4]] = K
    acc += len(t)
T0 = {rel[:-4]: t for rel, p, t in m0}
if set(T0) != set(chunk):
    raise SystemExit('mm0 / mm1 closures differ: %s' % sorted(set(T0) ^ set(chunk))[:10])
os.makedirs(os.path.join(od, 'gen7'), exist_ok=True)
hdr = '-- SCRATCH (staged link): closure chunk %d/%d of %s, generated by tools/gen7/c2/splitclose.py.\n'
CL = {rel[:-4]: classify(IMPORT.sub('', t)) for rel, p, t in m1 if chunk[rel[:-4]] < K}
for i in range(1, K + 1):
    # needed names: the chunk's own text, the earlier do-blocks and notations, then backwards through kept statements
    need = set()
    earlier = [rel[:-4] for rel, p, t in m1 if chunk[rel[:-4]] < i]
    for rel, p, t in m1:
        if chunk[rel[:-4]] == i:
            need.update(ID.findall(t))
            need.update(ID.findall(T0[rel[:-4]]))
    for r in earlier:
        for kind, nm, st in CL[r]:
            if kind in ('do', 'other'):
                need.update(ID.findall(st))
            elif kind == 'nota':
                need.add(nm)
    keep = {}
    for r in reversed(earlier):
        ks = []
        for kind, nm, st in reversed(CL[r]):
            if kind in ('thm', 'def') and nm not in need:
                continue
            if kind == 'thm':
                need.update(ID.findall(st[:proof_eq(st)]))
            elif kind == 'def':
                need.update(ID.findall(st))
            ks.append((kind, st))
        keep[r] = ks[::-1]
    for ext in ('mm1', 'mm0'):
        parts = [hdr % (i, K, mod)]
        if ext == 'mm1':
            parts.append('do { (set-timeout 0) };\n')
        # both files in the .mm1 closure order (= the .mmb order); stubs are made from the .mm1 text
        for rel, p, t in m1:
            r, c = rel[:-4], chunk[rel[:-4]]
            if c > i:
                continue
            parts.append('\n-- %s module: %s\n' % ('stub' if c < i else 'proof', rel))
            if c < i:
                parts.append(''.join(stub(k, st, ext == 'mm0') for k, st in keep[r]))
            else:
                parts.append(IMPORT.sub('', T0[r] if ext == 'mm0' else t))
        open(os.path.join(od, 'gen7', '%s%d.%s' % (pre, i, ext)), 'w').write(''.join(parts))
    print(i, sum(1 for v in chunk.values() if v == i), 'modules', sum(len(v) for v in keep.values()), 'stub statements')
