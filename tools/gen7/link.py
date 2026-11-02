"""GEN7 linker (route T, lanes/D3CHECK.md): splice a hand-proved module into a reflection output.

  python3 link.py R.mmb H.mmb SPEC.mm0 OUT.mmb OUT.mm0 [--peano peano.mm0] [--keep-axiom A1,A2,...]

--keep-axiom (LOCAL TESTS ONLY): the named axioms of H are not stubs; they stay axioms of OUT and of OUT.mm0 (the
spec must state them), so axioms.py reports them. Route T uses it to check the paThPr_D3 assembly locally while
the reflection of the host-only theorem d3r_adq is outside the local reflection.

R.mmb   a reflection output (tools/gen7/refl_lib.py OUTDIR/out.mmb): peano + the gen7 library + the per-def
        lemmas + the reflected theorems X_R (local).
H.mmb   the hand module compiled by mm0-rs from its flattened closure. Besides peano's axioms it may contain
        STUB axioms; every stub must be named like a theorem of R (a reflected X_R or a library theorem). Every
        non-peano axiom of H is a stub; the spec need not state them.
SPEC.mm0  the joined .mm0 of the hand module (peano.mm0 + its closure), stub axioms included or not.

OUT.mmb = R's statements (same order, same proofs) followed by H's statements that R does not already contain,
with term / theorem ids renumbered. Every use of a stub becomes a use of R's theorem of that name, so a stub
whose text differs from R's statement makes mm0-c reject the proof that uses it. Each statement is mapped by
name: an H term or theorem whose name R has is identified with R's (mm0-c then checks every use against R's
version). Visibility is set from the spec: a def / theorem is public iff the spec states it. Everything else
is local, so R's reflected theorems stay local.
OUT.mm0 = SPEC.mm0 without the stub axioms, reordered to the output order (notations follow their term).

The result is checked by mm0-c OUT.mmb < OUT.mm0. Only peano.mm0's 26 axioms may remain (checked here and by
axioms.py). Exit status 0 iff linking succeeded. The caller runs mm0-c and the false control (link_check.sh).
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.environ.get("MM0PAHA", "/home/user/mm0-pa-ha"))
from translator.mmb_reader import read_mmb, Term, Thm                       # noqa: E402
from translator.mmb_writer import MMBWriter                                # noqa: E402
from translator.mmb_format import (PROOF_TERM, PROOF_TERM_SAVE, PROOF_THM, PROOF_THM_SAVE,  # noqa: E402
                                   UNIFY_TERM, UNIFY_TERM_SAVE, STMT_DEF, STMT_LOCAL_DEF,
                                   STMT_AXIOM, STMT_THM, STMT_LOCAL_THM, STMT_SORT)
from refl_lib import mm0_statements                                        # noqa: E402

NOTA = ("prefix", "infixl", "infixr", "notation", "coercion")


class LinkError(Exception):
    pass


def peano_axioms(path):
    return [nm.rstrip(";:") for kw, nm, _ in mm0_statements(open(path).read()) if kw == "axiom"]


def link(r_path, h_path, spec_path, out_mmb, out_mm0, peano0, keep=()):
    R, H = read_mmb(r_path), read_mmb(h_path)
    pax = set(peano_axioms(peano0))
    if [s.name for s in R.sorts] != [s.name for s in H.sorts]:
        raise LinkError("sorts differ")
    rterm = {t.name: t.id for t in R.terms}
    rthm = {t.name: t.id for t in R.thms}
    # --- spec: drop stub axioms, keep the rest; visibility sets ---
    items = [(kw, nm.rstrip(";:"), txt) for kw, nm, txt in mm0_statements(open(spec_path).read())]
    stubs, spec = set(), []
    for kw, nm, txt in items:
        if kw == "axiom" and nm not in pax and nm not in keep:
            stubs.add(nm)
            continue
        spec.append((kw, nm, txt))
    pub_def = {nm for kw, nm, _ in spec if kw in ("def", "term")}
    pub_thm = {nm for kw, nm, _ in spec if kw == "theorem"}
    # --- id maps H -> out ---
    tmap, new_terms = {}, []
    for t in H.terms:
        if t.name in rterm:
            rt = R.terms[rterm[t.name]]
            if len(rt.args) != len(t.args) or rt.ret != t.ret or rt.is_def != t.is_def:
                raise LinkError("term %s: signature differs between R and H" % t.name)
            tmap[t.id] = rt.id
        else:
            tmap[t.id] = len(R.terms) + len(new_terms)
            new_terms.append(t)
    hthm_kind = {}
    for st in H.iter_stmts():
        if st.kind in ("axiom", "thm", "local_thm"):
            hthm_kind[st.ref] = st.kind
    smap, new_thms = {}, []
    for t in H.thms:
        k = hthm_kind[t.id]
        if k == "axiom" and t.name not in pax and t.name not in keep:
            stubs.add(t.name)              # a stub of H (it need not be in the spec)
            if t.name not in rthm:
                raise LinkError("stub %s has no theorem of that name in R" % t.name)
            smap[t.id] = rthm[t.name]
        elif t.name in rthm:
            smap[t.id] = rthm[t.name]
        else:
            smap[t.id] = len(R.thms) + len(new_thms)
            new_thms.append(t)
    unmatched = {nm for nm in stubs if nm not in {t.name for t in H.thms}}
    if unmatched:
        raise LinkError("spec stubs not in H: %s" % sorted(unmatched))

    def ru(unify):
        return [(op, tmap[d] if op in (UNIFY_TERM, UNIFY_TERM_SAVE) else d) for op, d in unify]

    def rp(cmds):
        out = []
        for op, d in cmds:
            if op in (PROOF_TERM, PROOF_TERM_SAVE):
                d = tmap[d]
            elif op in (PROOF_THM, PROOF_THM_SAVE):
                d = smap[d]
            out.append((op, d))
        return out
    # --- write ---
    w = MMBWriter(out_mmb, os.path.dirname(os.path.abspath(out_mmb)))
    for s in R.sorts:
        w.add_sort(s.mods, s.name)
    for t in R.terms:
        w.add_term(t)
    for t in new_terms:
        w.add_term(Term(tmap[t.id], t.sort, t.is_def, t.args, t.ret, ru(t.unify) if t.is_def else None,
                        t.name, t.var_names, None))
    for t in R.thms:
        w.add_thm(t)
    for t in new_thms:
        nt = Thm(smap[t.id], t.args, ru(t.unify), t.name, t.var_names, t.hyp_names, None)
        w.add_thm(nt)
    order = []                      # output order of named statements, for the spec
    nax = 0
    for st in R.iter_stmts():
        op = st.op
        if st.kind in ("def", "local_def"):
            nm = R.terms[st.ref].name
            op = STMT_DEF if nm in pub_def else STMT_LOCAL_DEF
            order.append(('t', nm))
        elif st.kind == "term":
            order.append(('t', R.terms[st.ref].name))
        elif st.kind in ("thm", "local_thm"):
            nm = R.thms[st.ref].name
            op = STMT_THM if nm in pub_thm else STMT_LOCAL_THM
            order.append(('h', nm))
        elif st.kind == "axiom":
            nm = R.thms[st.ref].name
            if nm not in pax:
                raise LinkError("R has a non-peano axiom " + nm)
            nax += 1
            order.append(('h', nm))
        elif st.kind == "sort":
            order.append(('s', R.sorts[st.ref].name))
        w.add_stmt(op, body=bytes(st.body))
    newt = {t.id for t in new_terms}
    newh = {t.id for t in new_thms}
    for st in H.iter_stmts():
        if st.kind in ("def", "local_def", "term") and st.ref in newt:
            if st.kind == "term":
                raise LinkError("H introduces a primitive term " + H.terms[st.ref].name)
            nm = H.terms[st.ref].name
            w.add_stmt(STMT_DEF if nm in pub_def else STMT_LOCAL_DEF, cmds=rp(st.cmds()))
            order.append(('t', nm))
        elif st.kind in ("thm", "local_thm") and st.ref in newh:
            nm = H.thms[st.ref].name
            w.add_stmt(STMT_THM if nm in pub_thm else STMT_LOCAL_THM, cmds=rp(st.cmds()))
            order.append(('h', nm))
        elif st.kind == "axiom" and st.ref in newh:
            nm = H.thms[st.ref].name
            if nm not in keep:
                raise LinkError("unmapped axiom " + nm)
            w.add_stmt(STMT_AXIOM, cmds=rp(st.cmds()))     # --keep-axiom: stays an axiom (reported by axioms.py)
            order.append(('h', nm))
            nax += 1
    w.finish("rebuild")
    # --- spec in output order ---
    pos = {nm: i for i, nm in enumerate(order)}
    head, body, last, byname = [], [], None, {}
    for kw, nm, txt in spec:
        if kw in ("sort", "term", "def", "axiom", "theorem"):
            key = ({"sort": "s", "term": "t", "def": "t"}.get(kw, "h"), nm)
            if key not in pos:
                raise LinkError("spec statement %s %s not in the output" % (kw, nm))
            body.append([pos[key], txt, []])
            last = body[-1]
            if kw in ("term", "def"):
                byname[nm] = last
        elif kw in NOTA and nm in byname:
            byname[nm][2].append(txt)
        else:                       # delimiter etc., or a notation for a name we do not know
            (last[2] if last else head).append(txt)
    body.sort(key=lambda b: b[0])
    with open(out_mm0, "w", newline="\n") as f:
        f.write("\n".join(head) + "\n")
        for _, txt, extra in body:
            f.write(txt + "\n")
            for e in extra:
                f.write(e + "\n")
    return dict(r_terms=len(R.terms), r_thms=len(R.thms), new_terms=len(new_terms), new_thms=len(new_thms),
                stubs=sorted(stubs), axioms=nax)


def main():
    a = sys.argv[1:]
    peano0 = os.path.join(os.path.dirname(os.path.dirname(HERE)), "lean-mm0", "vendor", "peano.mm0")
    if "--peano" in a:
        i = a.index("--peano"); peano0 = a[i + 1]; del a[i:i + 2]
    keep = ()
    if "--keep-axiom" in a:
        i = a.index("--keep-axiom"); keep = set(a[i + 1].split(",")); del a[i:i + 2]
    if len(a) != 5:
        raise SystemExit(__doc__)
    try:
        info = link(*a, peano0=peano0, keep=keep)
    except LinkError as e:
        print("LINK ERROR:", e)
        return 1
    print("linked: R %d terms / %d thms, + %d terms / %d thms from H; %d stubs replaced: %s; %d axioms" % (
        info["r_terms"], info["r_thms"], info["new_terms"], info["new_thms"], len(info["stubs"]),
        " ".join(info["stubs"]), info["axioms"]))
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    sys.exit(main())
