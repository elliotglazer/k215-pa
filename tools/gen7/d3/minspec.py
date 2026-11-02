"""Route T: a minimal .mm0 spec for linking: peano.mm0 + the defs the chosen theorems mention + those theorems.
  python3 minspec.py JOINED.mm0 THM1,THM2,... [--bodies DEF1,DEF2,...] > SPEC.mm0
JOINED.mm0 is lcheck's joined spec of the hand module (peano.mm0 first). Every def a kept statement mentions is kept,
abstract (no body), except the defs named in --bodies, which keep their body (and pull in the defs the body mentions);
--bodies ALL keeps the body of every kept def. Axiom names may be listed like theorems (kept axioms, linker --keep-axiom).
A spec def without a body is checked by mm0-c only for its signature, so the kept theorems are checked against
exactly the definitions shown. (The full joined spec overflows mm0-c's name trie.)"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from refl_lib import mm0_statements

def main(joined, thms, bodies=()):
    text = open(joined).read()
    items = mm0_statements(text)
    # peano part: everything up to the last peano axiom (the joined spec starts with peano.mm0)
    pk = len(PEANO_ITEMS)
    assert [nm for _, nm, _ in items[:pk]] == [nm for _, nm, _ in PEANO_ITEMS], 'joined spec does not start with peano.mm0'
    head = items[:pk]
    rest = items[pk:]
    defs = {nm.rstrip(':;'): txt for kw, nm, txt in rest if kw in ('def', 'term')}
    want = set(thms)
    keepdef, todo = set(), []
    def scan(txt):
        for tok in re.findall(r'[A-Za-z_][A-Za-z0-9_]*', txt):
            if tok in defs and tok not in keepdef:
                keepdef.add(tok); todo.append(tok)
    thm_txt = {}
    for kw, nm, txt in rest:
        n = nm.rstrip(':;')
        if kw in ('theorem', 'axiom') and n in want:
            thm_txt[n] = txt
            scan(re.sub(r'^.*?:', '', txt, count=1, flags=re.S))
    missing = want - set(thm_txt)
    if missing:
        raise SystemExit('not in spec: %s' % sorted(missing))
    while todo:
        d = todo.pop()
        if bodies == 'all' or d in bodies:
            scan(defs[d].split('=', 1)[1] if '=' in defs[d] else '')
    out = [t for _, _, t in head]
    for kw, nm, txt in rest:
        n = nm.rstrip(':;')
        if kw in ('def', 'term') and n in keepdef:
            if bodies == 'all' or n in bodies or kw == 'term':
                out.append(txt)
            else:
                sig = txt.split('=', 1)[0].rstrip() if '$' in txt else txt.rstrip(';')
                def nodots(m):                                     # dummies only exist with a body
                    inner = m.group(1); vs, _, ty = inner.partition(':')
                    vs = [v for v in vs.split() if not v.startswith('.')]
                    return '(%s:%s)' % (' '.join(vs), ty) if vs else ''
                sig = re.sub(r'\(([^()]*)\)', nodots, sig)
                sig = re.sub(r'\{([^{}]*)\}', lambda m: '' if all(v.startswith('.') for v in m.group(1).partition(':')[0].split()) else m.group(0), sig)
                out.append(sig.rstrip() + ';')
        elif kw in ('theorem', 'axiom') and n in want:
            out.append(txt)
    print('\n'.join(out))

PEANO_ITEMS = []

if __name__ == '__main__':
    a = sys.argv[1:]
    bodies = ()
    if '--bodies' in a:
        i = a.index('--bodies'); bodies = 'all' if a[i + 1] == 'ALL' else set(a[i + 1].split(',')); del a[i:i + 2]
    peano = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))), 'lean-mm0', 'vendor', 'peano.mm0')
    PEANO_ITEMS.extend(mm0_statements(open(peano).read()))
    main(a[0], a[1].split(','), bodies)
