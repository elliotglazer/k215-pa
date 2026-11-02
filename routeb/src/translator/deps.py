"""Dependency statistics for route B (spike): which defs/theorems of an .mmb
depend, transitively, on the description operator `the` (and theid/the0) or
on the classical axiom ax_3.

  python3 -m translator.deps build/peano.mmb [--list]

Per def: `the` nesting depth and occurrence count of the fully unfolded body
(with multiplicity, i.e. tree size, not DAG size) and def-chain distance.
Per theorem: statement uses a `the`-def; proof (transitively) uses a
`the`-def / theid,the0 / ax_3.
"""

import collections
import sys

from .mmb_format import (PROOF_TERM, PROOF_TERM_SAVE, PROOF_THM, PROOF_THM_SAVE,
                         PROOF_UNFOLD, UNIFY_TERM, UNIFY_TERM_SAVE)
from .mmb_reader import read_mmb
from .proof_dag import decode_unify


def unify_terms(decl):
    return {d for op, d in (decl.unify or ()) if op in (UNIFY_TERM, UNIFY_TERM_SAVE)}


def analyse(mmb):
    terms, thms = mmb.terms, mmb.thms
    the = mmb.term_by_name("the").id
    # ---- defs ----
    the_def = [False] * len(terms)       # body depends (transitively) on `the`
    dist = [None] * len(terms)          # def-chain distance to `the`
    depth = [0] * len(terms)            # max nesting of `the` in unfolded body
    count = [0] * len(terms)            # occurrences of `the` in unfolded body
    for t in terms:
        if t.id == the:
            the_def[t.id], dist[t.id], depth[t.id], count[t.id] = True, 0, 1, 1
            continue
        if not t.is_def or not t.unify:      # primitive (or abstract) term
            continue
        nodes, root, _ = decode_unify(mmb, t)
        memo = {}

        def go(n):
            if n in memo:
                return memo[n]
            nd = nodes[n]
            if nd[0] != "app":
                r = (0, 0)
            else:
                ch = [go(a) for a in nd[2]]
                cd = max([c[0] for c in ch] + [0])
                cc = sum(c[1] for c in ch)
                f = nd[1]
                if f == the:
                    r = (cd + 1, cc + 1)
                elif terms[f].is_def and count[f]:
                    # def args substituted into the unfolded body: approximate
                    # nesting by depth(f)+child depth, count by count(f)+children
                    r = (depth[f] + cd, count[f] + cc)
                else:
                    r = (cd, cc)
            memo[n] = r
            return r
        depth[t.id], count[t.id] = go(root)
        used = unify_terms(t)
        ds = [dist[u] for u in used if dist[u] is not None]
        if ds:
            the_def[t.id], dist[t.id] = True, 1 + min(ds)
    # ---- theorems ----
    ax3 = mmb.thm_by_name("ax_3").id
    thetax = {mmb.thm_by_name("theid").id, mmb.thm_by_name("the0").id}
    st_the = [False] * len(thms)       # statement mentions a the-dependent term
    pf_the = [False] * len(thms)       # proof (transitively) touches a the-term
    uses_thetax = [False] * len(thms)
    uses_ax3 = [False] * len(thms)
    uses_ax = [frozenset()] * len(thms)
    ax3_depth = [None] * len(thms)      # proof-chain distance to ax_3
    for st in mmb.iter_stmts():
        if st.kind not in ("axiom", "thm", "local_thm"):
            continue
        i = st.ref
        t = thms[i]
        st_the[i] = any(the_def[u] for u in unify_terms(t))
        if st.kind == "axiom":
            uses_ax[i] = frozenset([i])
            if i == ax3:
                uses_ax3[i], ax3_depth[i] = True, 0
            if i in thetax:
                uses_thetax[i] = True
            pf_the[i] = st_the[i]
            continue
        pt, axs, a3, tx, d3 = st_the[i], set(), False, False, []
        for op, d in st.cmds():
            if op in (PROOF_TERM, PROOF_TERM_SAVE, PROOF_UNFOLD):
                pt = pt or the_def[d]
            elif op in (PROOF_THM, PROOF_THM_SAVE):
                pt = pt or pf_the[d]
                axs |= uses_ax[d]
                a3 = a3 or uses_ax3[d]
                tx = tx or uses_thetax[d]
                if ax3_depth[d] is not None:
                    d3.append(ax3_depth[d])
        pf_the[i], uses_ax[i], uses_ax3[i], uses_thetax[i] = pt, frozenset(axs), a3, tx
        ax3_depth[i] = 1 + min(d3) if d3 else None
    return dict(the_def=the_def, dist=dist, depth=depth, count=count,
                st_the=st_the, pf_the=pf_the, uses_thetax=uses_thetax,
                uses_ax3=uses_ax3, uses_ax=uses_ax, ax3_depth=ax3_depth)


def report(mmb, r, listing=False):
    terms, thms = mmb.terms, mmb.thms
    defs = [t for t in terms if t.is_def]
    td = [t for t in defs if r["the_def"][t.id]]
    print("defs: %d, depending on `the`: %d (wff-valued %d, nat %d, set %d)" % (
        len(defs), len(td),
        *[sum(1 for t in td if mmb.sorts[t.sort].name == s) for s in ("wff", "nat", "set")]))
    print("  def-chain distance to `the`:", dict(sorted(collections.Counter(
        r["dist"][t.id] for t in td).items())))
    print("  `the` nesting depth (unfolded):", dict(sorted(collections.Counter(
        r["depth"][t.id] for t in td).items())))
    cs = sorted(r["count"][t.id] for t in td)
    print("  `the` occurrences in unfolded body: median %d, max %d (%s)" % (
        cs[len(cs) // 2], cs[-1], max(td, key=lambda t: r["count"][t.id]).name))
    print("  the-free defs:", " ".join(t.name for t in defs if not r["the_def"][t.id]))
    th = [t for t in thms if t.kind != "axiom"]
    n = len(th)
    def c(k):
        return sum(1 for t in th if r[k][t.id])
    print("theorems: %d" % n)
    print("  statement mentions a the-def: %d" % c("st_the"))
    print("  proof touches a the-def (transitively): %d" % c("pf_the"))
    print("  uses theid/the0 (transitively): %d" % c("uses_thetax"))
    print("  uses ax_3 (transitively): %d" % c("uses_ax3"))
    free = [t for t in th if not r["pf_the"][t.id]]
    print("  the-free (stmt+proof+all deps): %d; of those ax_3-free: %d" % (
        len(free), sum(1 for t in free if not r["uses_ax3"][t.id])))
    print("  ax_3 proof-chain distance:", dict(sorted(collections.Counter(
        r["ax3_depth"][t.id] for t in th if r["ax3_depth"][t.id] is not None).items())))
    axn = collections.Counter()
    for t in free:
        for a in r["uses_ax"][t.id]:
            axn[thms[a].name] += 1
    print("  axioms used by the-free theorems:", dict(axn.most_common()))
    # first index (stream order) where a theorem becomes the-dependent
    first = next((t for t in th if r["pf_the"][t.id]), None)
    print("  first the-dependent theorem: #%d %s" % (th.index(first), first.name))
    if listing:
        for t in td:
            print("THEDEF", t.name, r["dist"][t.id], r["depth"][t.id], r["count"][t.id])


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    mmb = read_mmb(argv[0])
    list(mmb.iter_stmts())
    report(mmb, analyse(mmb), "--list" in argv)


if __name__ == "__main__":
    main()
