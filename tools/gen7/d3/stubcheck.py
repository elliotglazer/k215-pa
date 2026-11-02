#!/usr/bin/env python3
"""Route T: compare the stub axioms of a hand module's closure with a reflection's statements.
  python3 stubcheck.py OUT.mm0 MODULE [MODULE ..]      (MODULE relative to pa-mm0, e.g. gen7/d3_hostall)
For every `axiom NAME ...` in the .mm1 import closure of the modules (pa-mm0/gen7 files only) whose NAME is a theorem
of OUT.mm0 (the refl_lib spec), the statement texts must agree up to whitespace (link.py maps the stub to that
theorem, and mm0-c rejects any use of a stub that differs). Stubs with no theorem in OUT.mm0 are listed as unresolved
(the host link then fails unless they are peano axioms). Exit 0 iff every stub resolves and agrees."""
import os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PA = os.path.join(ROOT, 'pa-mm0')
IMP = re.compile(r'^\s*import\s+"([^"]+)"\s*;', re.M)


def closure(rel, seen, out):
    rel = os.path.normpath(rel)
    if rel in seen:
        return
    seen.add(rel)
    p = os.path.join(PA, rel)
    if not os.path.exists(p):
        return
    t = open(p).read()
    for c in IMP.findall(t):
        closure(os.path.join(os.path.dirname(rel), c), seen, out)
    if rel.startswith('gen7' + os.sep):
        out.append((rel, t))


def stmts(text, kw):
    d = {}
    for m in re.finditer(r'^%s ([A-Za-z0-9_.]+)\b' % kw, text, re.M):
        i = m.start()
        j = text.index('$;', text.index('$', text.index(':', i))) + 2
        while text[i:j].count('$') % 2:
            j = text.index('$;', j) + 2
        d[m.group(1)] = ' '.join(text[i + len(kw):j].split())
    return d


def main():
    out = open(sys.argv[1]).read()
    th = stmts(out, 'theorem')
    mods = []
    seen = set()
    for m in sys.argv[2:]:
        closure(m + '.mm1', seen, mods)
    bad = unres = ok = 0
    for rel, t in mods:
        for nm, st in stmts(t, 'axiom').items():
            if nm not in th:
                print('unresolved stub %s (%s)' % (nm, rel)); unres += 1
            elif th[nm] != st:
                print('DIFFERS %s (%s)\n  stub: %s\n  refl: %s' % (nm, rel, st[:300], th[nm][:300])); bad += 1
            else:
                ok += 1
    print('stubs: %d agree, %d differ, %d unresolved' % (ok, bad, unres))
    sys.exit(0 if not bad and not unres else 1)


if __name__ == '__main__':
    main()
