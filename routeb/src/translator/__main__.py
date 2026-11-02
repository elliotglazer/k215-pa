"""Command line: python3 -m translator {stats,roundtrip,dump} ...

  stats FILE.mmb                  counts of sorts/terms/defs/thms and proof commands
  roundtrip IN.mmb OUT.mmb [--index preserve|rebuild|none] [--reencode]
  dump FILE.mmb NAME              statement, unify stream and proof DAG of one decl
"""

import argparse
import collections
import sys

from .mmb_format import PROOF_NAMES, UNIFY_NAMES
from .mmb_reader import read_mmb, binder_str
from .mmb_writer import write_mmb
from .proof_dag import build_stmt_dag, decode_unify


def stats(mmb):
    kinds = collections.Counter()
    ops = collections.Counter()
    for st in mmb.iter_stmts():
        kinds[st.kind] += 1
        for op, _ in st.cmds():
            ops[op] += 1
    uops = collections.Counter()
    for d in mmb.terms + mmb.thms:
        for op, _ in (d.unify or ()):
            uops[op] += 1
    return {
        "sorts": len(mmb.sorts),
        "terms": sum(1 for t in mmb.terms if not t.is_def),
        "defs": sum(1 for t in mmb.terms if t.is_def),
        "axioms": kinds["axiom"],
        "theorems": kinds["thm"] + kinds["local_thm"],
        "stmt_kinds": dict(kinds),
        "proof_cmds": {PROOF_NAMES.get(k, hex(k)): v for k, v in sorted(ops.items())},
        "proof_cmds_total": sum(ops.values()),
        "unify_cmds": {UNIFY_NAMES.get(k, hex(k)): v for k, v in sorted(uops.items())},
    }


def main(argv=None):
    ap = argparse.ArgumentParser(prog="translator")
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("stats"); a.add_argument("file")
    a = sub.add_parser("roundtrip"); a.add_argument("inp"); a.add_argument("out")
    a.add_argument("--index", default="preserve", choices=["preserve", "rebuild", "none"])
    a.add_argument("--reencode", action="store_true")
    a = sub.add_parser("dump"); a.add_argument("file"); a.add_argument("name")
    ns = ap.parse_args(argv)
    if ns.cmd == "stats":
        s = stats(read_mmb(ns.file))
        for k, v in s.items():
            print("%-17s %s" % (k, v))
    elif ns.cmd == "roundtrip":
        mmb = read_mmb(ns.inp)
        write_mmb(mmb, ns.out, index=ns.index, reencode=ns.reencode)
        same = open(ns.inp, "rb").read() == open(ns.out, "rb").read()
        print("byte-identical" if same else "differs (semantic rewrite)")
    elif ns.cmd == "dump":
        mmb = read_mmb(ns.file)
        stmts = {(s.kind in ("sort",), s.ref, s.kind): s for s in mmb.iter_stmts()}
        for d in mmb.terms + mmb.thms:
            if d.name != ns.name:
                continue
            is_term = d in mmb.terms
            print(d, " ".join(binder_str(b, mmb.sorts) for b in d.args),
                  "vars=%s" % d.var_names)
            if d.unify:
                nodes, root, hyps = decode_unify(mmb, d)
                from .proof_dag import ProofDAG
                v = ProofDAG(nodes, [], None, hyps, 0)
                print(" stmt:", v.show(root, mmb), "hyps:", [v.show(h, mmb) for h in hyps])
            st = next(s for s in mmb.iter_stmts() if s.ref == d.id and
                      (s.kind in ("term", "def", "local_def")) == is_term)
            print(" stream:", [(PROOF_NAMES.get(o, o), x) for o, x in st.cmds()][:60])
            if len(st.body):
                dag = build_stmt_dag(mmb, st)
                print(" dag:", dag, "result:", dag.result)
            return 0
        print("not found", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
