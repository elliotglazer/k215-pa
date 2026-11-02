"""Interface of one pa-mm0 module: everything an importer can use, with every proof removed.

  python3 mkiface.py MODULE [--out FILE.mm1]      # print or write the interface as MM1 text

An importer of X.mm1 sees all of X's declarations, public or not (experiment: tools/link/README.md section 2):
private theorems, local defs, defs and the theorems their annotation derives (`@_` = derive-eq: *eqd, *eq,
*eqNd, *eqN), Lisp definitions and registrations made by `do` blocks (register-eqd, eqd-map), notations.
The interface keeps, in source order and verbatim (comments removed):
  def / term / sort / notation statements with their annotations and exact bodies, and every `do` block;
and replaces each theorem `[@a] [pub] theorem N BIS: TYPE = PROOF;` by the stub `axiom N BIS: TYPE;`.
Imports are dropped (compile_one.py concatenates the interfaces of the whole closure in check.py order).

Each item is (kind, name, text): kind = stub | def | do | nota | other. Annotations on defs are kept, so the
derived equality theorems are re-derived (with proofs) when an importer is compiled; the linker identifies
them by name with the originals.
"""
import json
import os
import sys
import threading

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mm1lib as L  # noqa: E402

NOTA = ("notation", "infixl", "infixr", "prefix", "coercion", "delimiter")


def items(module, pa=L.PA):
    out = []
    for kw, name, s in L.statements(L.read_text(os.path.join(pa, module + ".mm1"))):
        if kw == "import":
            continue
        if kw == "theorem":
            out.append(("stub", name, L.stub_text(s)))
        elif kw in ("def", "term", "sort"):
            out.append(("def", name, s))
        elif kw == "do":
            out.append(("do", None, s))
        elif kw in NOTA:
            out.append(("nota", name, s))
        elif kw == "axiom":
            raise ValueError("%s: project source declares axiom %s" % (module, name))
        else:
            out.append(("other", name, s))
    return out


def cached_items(module, cache_dir, pa=L.PA):
    """items(module), cached in cache_dir/<module>.iface.json keyed by the source sha256."""
    src = os.path.join(pa, module + ".mm1")
    digest = L.sha256(src)
    path = os.path.join(cache_dir, module + ".iface.json")
    try:
        with open(path, encoding="utf-8") as f:
            d = json.load(f)
        if d["source_sha256"] == digest:
            return d["items"]
    except (OSError, ValueError, KeyError):
        pass
    it = [list(x) for x in items(module, pa)]
    os.makedirs(cache_dir, exist_ok=True)
    tmp = "%s.%d.%d.tmp" % (path, os.getpid(), threading.get_ident())
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump({"module": module, "source_sha256": digest, "items": it}, f)
    os.replace(tmp, path)
    return it


def main():
    a = sys.argv[1:]
    out = None
    if "--out" in a:
        i = a.index("--out"); out = a[i + 1]; del a[i:i + 2]
    text = "\n".join(t for _, _, t in items(a[0])) + "\n"
    if out:
        with open(out, "w", newline="\n", encoding="utf-8") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
