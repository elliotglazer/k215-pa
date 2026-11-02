"""The .mm0 of a route-T .mm1 module: imports (mm1 -> mm0), defs (abstract: without body), pub theorems
(statement only), axioms. Private theorems are left out.  python3 mm0of.py X.mm1 > X.mm0"""
import re, sys

def items(t):
    """Top-level items, split at the start of lines beginning a declaration."""
    starts = [m.start() for m in re.finditer(r'^(import|pub theorem|theorem|def|@_ def|@_ abstract def|abstract def|axiom|do|--)', t, re.M)]
    starts.append(len(t))
    for a, b in zip(starts, starts[1:]):
        yield t[a:b].rstrip()

def stmt_end(s):
    m = re.search(r"\$\s*=\s*(\(named|'|\(focus|\(\s*named)", s)
    return s[:m.start() + 1] if m else None

def main(path):
    out = []
    for it in items(open(path).read()):
        if it.startswith('import'):
            out.append(it.replace('.mm1"', '.mm0"'))
        elif it.startswith('pub theorem'):
            out.append('theorem' + stmt_end(it)[len('pub theorem'):] + ';')
        elif it.startswith('axiom'):
            out.append(it)
        elif re.match(r'(@_ )?abstract def', it):
            s = re.sub(r'^(@_ )?abstract ', '', it)
            out.append(s[:s.index(' = $')] + ';' if ' = $' in s else s)
        elif re.match(r'(@_ )?def', it):
            out.append(re.sub(r'^@_ ', '', it))
    print('\n'.join(out))

main(sys.argv[1])
