"""Check that an output's axioms are exactly peano.mm0's axioms, by statement text.

  python3 axioms.py OUT.mmb OUT.mm0 [peano.mm0]

mm0-c checks every axiom of OUT.mmb against the axiom of the same position in OUT.mm0, so it is
enough that (1) OUT.mmb has as many axioms as OUT.mm0, and (2) every axiom statement of OUT.mm0
is, up to whitespace, an axiom statement of peano.mm0 (and every peano axiom occurs).
Exit 0 iff both hold.
"""
import os, re, sys
sys.path.insert(0, os.environ.get("ROUTEB", "/home/user/mm0-pa-ha"))
from translator.mmb_reader import read_mmb  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def axiom_texts(text):
    out = []
    i, n, start, math = 0, len(text), 0, False
    while i < n:
        c = text[i]
        if not math and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            text = text[:i] + " " * (j - i) + text[j:]
            continue
        if c == "$":
            math = not math
        elif c == ";" and not math:
            st = " ".join(text[start:i + 1].split())
            if re.match(r"axiom\b", st):
                out.append(st)
            start = i + 1
        i += 1
    return out


def main():
    mmb, spec = sys.argv[1], sys.argv[2]
    peano = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, "..", "..", "lean-mm0", "vendor", "peano.mm0")
    m = read_mmb(mmb)
    n_mmb = sum(1 for st in m.iter_stmts() if st.kind == "axiom")
    sp = axiom_texts(open(spec).read())
    pa = axiom_texts(open(peano).read())
    extra = [a for a in sp if a not in set(pa)]
    missing = [a for a in pa if a not in set(sp)]
    print("axioms: mmb %d, spec %d, peano.mm0 %d; spec axioms not in peano.mm0: %d; peano axioms missing: %d"
          % (n_mmb, len(sp), len(pa), len(extra), len(missing)))
    for a in extra[:5]:
        print("  extra:", a[:200])
    ok = n_mmb == len(sp) and not extra and not missing and len(sp) == len(pa)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
