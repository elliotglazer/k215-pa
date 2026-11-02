"""Route T: stub axioms for a hand module, copied verbatim from a reflection's out.mm0.
  python3 stubs.py OUT.mm0 ROOTS.txt  -> prints `axiom X_R ...;` for every root X (statement text unchanged)."""
import re, sys

def main(out_mm0, roots):
    txt = open(out_mm0).read()
    st = {}
    for m in re.finditer(r'^theorem (\S+) (.*?\$;)$', txt, re.M | re.S):
        st[m.group(1)] = m.group(2)
    for r in (l.strip() for l in open(roots)):
        if r and not r.startswith('#'):
            n = r + '_R'
            if n not in st:
                raise SystemExit('no statement for ' + n)
            print('axiom %s %s' % (n, st[n]))

if __name__ == '__main__':
    main(*sys.argv[1:])
