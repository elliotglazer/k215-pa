"""G7 spike: reflection compiler prototype (option (a) of lanes/G2GEN.md).

  python3 refl.py SRC.mmb OUT.mmb OUT.mm0 [--pub all|pub|none] [--max N]

Turns every theorem T of an MM0 proof over peano.mm0 into ONE schematic lemma
T_R about coded derivability, DAG-shared (each lemma once, never re-proved per
instance), over the scratch output foundation built here (see lanes/GEN7.md):

  sorts      wff (provable), nat (codes and names)
  cPr c      "the coded MM0 formula c is PA-provable" (one-time: cPr c :=
             paProvable 0 (closure (trPA c)), trPA = graph translation of `the`,
             named -> de Bruijn); nfr x c "name x not free in c"; nne x y;
             aeq c d "alpha-equivalent"
  codes      one constructor per peano primitive (cIm cNot cTru cAl cEq cAb cEl
             c0 cSuc cThe cAdd cMul) + cV (a bound variable used as a term);
             bound variables are NAMES (nat values), so instantiating T_R is plain
             MM0 substitution: the code of an instance is the instance of the code
  defs       each source def D gets ONE code def cD whose body is the code of D's
             body (definitional unfolding maps 1:1); D's dummies get canonical
             names w_0 = nfresh(tuple of the args), w_(k+1) = nfresh(cV w_k) (increasing,
             each larger than every name in the args)
  library L  structural axioms (nfr_*, nne_sym, aeq_*, cPr_aeq, nfresh/ctup) and one
             coded axiom per peano axiom with its freshness side conditions. In the
             spike L and the per-def lemmas (nfr_D, aeq_D, alpha_D) are AXIOMS of the
             scratch spec; in the compiler phase L is proved once over paProvable and
             the per-def lemmas get generated proofs (size ~ the def body, counted).

Per theorem the output proof is the source DAG with: expressions coded 1:1
(bound variable in term position -> cV x), theorem steps 1:1 plus freshness side
proofs (nfr/nne, structural, memoised per (name, node)), conversions 1:1 except
an unfolding of a def with dummies, which becomes an alpha step (aeq + cPr_aeq).
Proof dummies get names nfresh(...) chained over the statement's leaves.
Everything is checked by mm0-c against OUT.mm0.
"""

import os
import struct
import sys
import time

sys.path.insert(0, os.environ.get("ROUTEB", "/home/user/mm0-pa-ha"))

from translator.mmb_format import (  # noqa: E402
    MMBError, STMT_AXIOM, STMT_DEF, STMT_LOCAL_DEF, STMT_LOCAL_THM, STMT_THM, STMT_SORT,
    STMT_TERM, type_word, type_bound, type_sort, type_deps,
)
from translator.mmb_reader import read_mmb, Term, Thm, Sort  # noqa: E402
from translator.mmb_writer import MMBWriter  # noqa: E402
from translator.proof_dag import build_stmt_dag, decode_unify  # noqa: E402
from translator.negtrans import Ctx, NegTrans, LIMITS, Untranslatable  # noqa: E402

WFF, NAT = 0, 1
NATW = type_word(False, NAT, 0)

PRIM = {  # peano primitive term -> code constructor
    "im": "cIm", "not": "cNot", "tru": "cTru", "al": "cAl", "eq": "cEq", "ab": "cAb",
    "el": "cEl", "d0": "c0", "suc": "cSuc", "the": "cThe", "add": "cAdd", "mul": "cMul",
}
# coded peano axioms: semantically needed side conditions (name arg i, code arg k)
AXSIDE = {
    "ax_5": [("nfr", 0, 1)], "ax_6": [("nfr", 1, 0)], "ax_12": [("nfr", 0, 1)],
    "theid": [("nfr", 0, 2)], "the0": [("nne", 0, 1), ("nfr", 1, 2)],
}

# reasons why the MM0-implied side conditions that AXSIDE leaves out are sound to omit
# (filled below after listing them; checked in tr_axiom)
SIDE_OMIT_SOUND = {
    # each omitted condition is never needed: the coded axiom is proved (pa-mm0/gen7) without it
    "ax_11": "nne x y: A.x A.y p -> A.y A.x p also holds when x = y (ax_11_R, gen7_ax2)",
    "elab": "nfr x a: a occurs only outside the binders on x (elab_R, gen7_bx3)",
    "theid": "nfr x A: A is not under the class binder on x (theid_R, gen7_bx5)",
    "the0": "nfr x A: A is not under the class binder on x (the0_R, gen7_bx6)",
}


def full_side(t):
    """Every side condition MM0 itself imposes on uses of axiom t (from its binder deps):
    nfr x k for each name arg x and code arg k not depending on x, nne x y for distinct names."""
    kinds, deps, _ = src_info(t)
    nb = [i for i in range(len(t.args)) if kinds[i] == "n"]
    return [("nfr", i, k) for i in nb for k in range(len(t.args)) if kinds[k] == "c" and i not in deps[k]] + \
           [("nne", i, j) for i in nb for j in nb if i < j]


class Info:
    """Binder structure of an output term: kind per arg ('n' name / 'c' code),
    deps per code arg (set of name-arg indices), retdeps (name-arg indices)."""
    __slots__ = ("kinds", "deps", "retdeps", "ndum", "tpl")

    def __init__(self, kinds, deps, retdeps, ndum=0, tpl=None):
        self.kinds, self.deps, self.retdeps, self.ndum, self.tpl = kinds, deps, retdeps, ndum, tpl


def src_info(t):
    """Info of a source term/def from its binder words."""
    bl = [i for i, w in enumerate(t.args) if type_bound(w)]
    kinds = ["n" if type_bound(w) else "c" for w in t.args]
    deps = {}
    for i, w in enumerate(t.args):
        if not type_bound(w):
            d = type_deps(w)
            deps[i] = {bl[k] for k in range(len(bl)) if d >> k & 1}
    rd = type_deps(t.ret) if hasattr(t, "ret") else 0
    return kinds, deps, {bl[k] for k in range(len(bl)) if rd >> k & 1}


class Refl(NegTrans):
    def __init__(self, src):                                   # noqa: C901
        self.src = src

        class L:
            sorts = [Sort(0, 4, "wff"), Sort(1, 0, "nat")]
        self.lib = L
        self.terms, self.thms = [], []
        self.tname, self.hname = {}, {}
        self.names, self.renamed = set(), []
        self.out_stmts = []
        self.w = None
        self.spec = ["delimiter $ ( ) $;", "provable sort wff;", "sort nat;"]
        self.stats = dict(defs=0, thms=0, in_bytes=0, out_bytes=0, in_cmds=0, out_cmds=0,
                          lib_axioms=0, gen_lemmas=0, gen_lemma_est_cmds=0, alpha_steps=0,
                          side_nodes=0, main_nodes=0, side_hyps=0, conv_alpha=0)
        self.usage = {k: (0, None) for k in LIMITS}
        self.ratio = {"heap": (0.0, None), "store": (0.0, None)}
        self.src_usage = {"heap": (0, None), "store": (0, None)}
        self.limit_fail = []
        self.info = {}          # out term id -> Info
        self.tmap = {}          # src term id -> out term id
        self.hmap = {}          # src thm id -> (out thm id, side list)
        self.why = {}
        self.side_omitted = {}
        self.tpl = {}           # out thm id -> (nodes, root, hyps) template cache
        self.lem = {}           # (kind, tid, variant) -> out thm id
        self.decls = []         # (op, body, kind, ref, spec_line or None) in order
        # library terms
        for nm, n, srt in [("cPr", 1, WFF), ("nfr", 2, WFF), ("nne", 2, WFF), ("aeq", 2, WFF),
                           ("cnil", 0, NAT), ("ctup", 2, NAT), ("nfresh", 1, NAT), ("cV", 1, NAT)]:
            self.add_term(nm, n, srt)
        self.info[self.tname["cV"]] = Info(["n"], {}, {0})
        for t in src.terms:
            if t.name in PRIM and not t.is_def:
                tid = self.add_term(PRIM[t.name], len(t.args), NAT)
                self.tmap[t.id] = tid
                self.info[tid] = Info(*src_info(t))
        T = self.tname
        self.cPr, self.nfr, self.nne, self.aeq = T["cPr"], T["nfr"], T["nne"], T["aeq"]
        self.cnil, self.ctup, self.nfresh, self.cV = T["cnil"], T["ctup"], T["nfresh"], T["cV"]
        # structural library axioms
        A = self.libax
        A("nne_sym", 2, [("nne", 0, 1)], ("nne", 1, 0))
        A("nfr_Vinv", 2, [("nfr", 0, ("cV", 1))], ("nne", 0, 1))
        A("nfr_fresh", 1, [], ("nfr", ("nfresh", 0), 0))
        A("nfr_tl", 3, [("nfr", 0, ("ctup", 1, 2))], ("nfr", 0, 1))
        A("nfr_tr", 3, [("nfr", 0, ("ctup", 1, 2))], ("nfr", 0, 2))
        A("aeq_refl", 1, [], ("aeq", 0, 0))
        A("aeq_sym", 2, [("aeq", 0, 1)], ("aeq", 1, 0))
        A("aeq_trans", 3, [("aeq", 0, 1), ("aeq", 1, 2)], ("aeq", 0, 2))
        A("cPr_aeq", 2, [("cPr", 0), ("aeq", 0, 1)], ("cPr", 1))

    # ---------------- declarations ----------------
    def add_term(self, name, n, sort):
        t = Term(len(self.terms), sort, False, [NATW] * n, type_word(False, sort, 0), None, name=name)
        t.var_names = ["v%d" % i for i in range(n)]
        self.terms.append(t)
        self.tname[name] = t.id
        self.names.add(name)
        self.decls.append((STMT_TERM, b"", "term", t.id,
                           "term %s%s: %s;" % (name, "".join(" (v%d: nat)" % i for i in range(n)),
                                               "wff" if sort == WFF else "nat")))
        return t.id

    def sx(self, cx, s):
        """Build an expression from a tiny s-expression (ints = vars)."""
        if isinstance(s, int):
            return cx.mk("var", s)
        return cx.mk("app", self.tname[s[0]], tuple(self.sx(cx, a) for a in s[1:]))

    def libax(self, name, n, hyps, concl):
        cx = Ctx()
        for i in range(n):
            cx.mk("var", i)
        return self.add_axiom(name, n, cx, [self.sx(cx, h) for h in hyps], self.sx(cx, concl), "lib")

    def add_axiom(self, name, n, cx, hyps, concl, cat):
        name = self.uniq(name)
        uni, ud, uh = self.unify_of(cx, [concl] + list(reversed(hyps)), n)
        body_b, _ = self.emit(cx, n, hyps, concl)
        th = Thm(len(self.thms), [NATW] * n, uni, name=name)
        th.var_names = ["v%d" % i for i in range(n)]
        th.hyp_names = ["h%d" % i for i in range(len(hyps))]
        self.thms.append(th)
        self.hname[name] = th.id
        line = self.print_decl(th, False).replace("theorem ", "axiom ", 1)
        self.decls.append((STMT_AXIOM, body_b + b"\0", "axiom", th.id, line))
        self.stats["lib_axioms" if cat == "lib" else "gen_lemmas"] += 1
        return th.id

    def template(self, oid):
        r = self.tpl.get(oid)
        if r is None:
            class M:
                terms = self.terms
            r = self.tpl[oid] = decode_unify(M, self.thms[oid])
        return r

    def inst(self, cx, nodes, root, args, memo=None):
        """Copy template expression `root` into cx with var i -> args[i]."""
        memo = {} if memo is None else memo
        st = [(root, False)]
        while st:
            n, ex = st.pop()
            if n in memo:
                continue
            nd = nodes[n]
            if nd[0] == "var":
                memo[n] = args[nd[1]]
            elif nd[0] == "app":
                if not ex:
                    st.append((n, True))
                    st.extend((a, False) for a in nd[2] if a not in memo)
                    continue
                memo[n] = cx.mk("app", nd[1], tuple(memo[a] for a in nd[2]))
            else:
                raise MMBError("template dummy")
        return memo[root]

    def app_thm(self, cx, oid, args, hyps):
        nodes, root, _ = self.template(oid)
        return cx.mk("thm", oid, tuple(args), tuple(hyps), self.inst(cx, nodes, root, args))

    def P(self, cx, name, args, hyps=()):
        return self.app_thm(cx, self.hname[name], args, hyps)

    # ---------------- per-term lemmas (lib for primitives, generated for defs) -----
    def lemma(self, kind, tid, var=None):
        key = (kind, tid, var)
        r = self.lem.get(key)
        if r is not None:
            return r
        inf = self.info[tid]
        n = len(inf.kinds)
        cx = Ctx()
        a = [cx.mk("var", i) for i in range(n)]
        code = [i for i in range(n) if inf.kinds[i] == "c"]
        nm = self.terms[tid].name
        mk = cx.mk
        if kind == "nfr":
            if var is None:
                x = mk("var", n)
                hyps = [mk("app", self.nfr, (x, a[i])) for i in code] + \
                       [mk("app", self.nne, (x, a[j])) for j in sorted(inf.retdeps)]
                concl = mk("app", self.nfr, (x, mk("app", tid, tuple(a))))
                nargs, lname = n + 1, "nfr_" + nm
            else:
                x = a[var]
                hyps = [mk("app", self.nfr, (x, a[i])) for i in code if var not in inf.deps[i]] + \
                       [mk("app", self.nne, (x, a[j])) for j in sorted(inf.retdeps) if j != var]
                concl = mk("app", self.nfr, (x, mk("app", tid, tuple(a))))
                nargs, lname = n, "nfr_%s_%d" % (nm, var)
        elif kind == "aeq":
            b = list(a)
            for k, i in enumerate(code):
                b[i] = mk("var", n + k)
            hyps = [mk("app", self.aeq, (a[i], b[i])) for i in code]
            concl = mk("app", self.aeq, (mk("app", tid, tuple(a)), mk("app", tid, tuple(b))))
            nargs, lname = n + len(code), "aeq_" + nm
        else:   # alpha: rename the canonical dummy names of def tid to Z_1..Z_m
            m = inf.ndum
            z = [mk("var", n + k) for k in range(m)]
            hyps = []
            for k in range(m):
                hyps += [mk("app", self.nfr, (z[k], a[i])) for i in code]
                hyps += [mk("app", self.nne, (z[k], a[j])) for j in range(n) if inf.kinds[j] == "n"]
                hyps += [mk("app", self.nne, (z[k], z[l])) for l in range(k + 1, m)]
            tnodes, troot, tdum = inf.tpl
            memo = {}
            for k, dn in enumerate(tdum):
                memo[dn] = z[k]
            body = self.inst(cx, tnodes, troot, a, memo)
            concl = mk("app", self.aeq, (mk("app", tid, tuple(a)), body))
            nargs, lname = n + m, "alpha_" + nm
        cat = "lib" if not self.terms[tid].is_def else "gen"
        r = self.add_axiom(lname, nargs, cx, hyps, concl, cat)
        if cat == "gen":    # estimated generated proof size ~ a few cmds per body node
            self.stats["gen_lemma_est_cmds"] += 4 * (len(inf.tpl[0]) if inf.tpl else 1) + 4 * len(hyps)
        self.lem[key] = r
        return r

    # ---------------- expressions ----------------
    def tr_expr(self, cx, sn, n, sargs, memo, names, name_pos=False, dum_args=()):
        """Code of source expression node n. `names(node)` gives the output name
        node of a source dummy; bound vars are their own (var i) nodes, except those in
        dum_args, which are named like proof dummies (names(("arg", i)))."""
        top = (n, name_pos)
        r = memo.get(top)
        if r is not None:
            return r
        stack = [(n, name_pos, False)]
        srcterms, tmap = self.src.terms, self.tmap
        while stack:
            m, b, ex = stack.pop()
            key = (m, b)
            if key in memo:
                continue
            nd = sn[m]
            k = nd[0]
            if k == "var" or k == "dummy":
                if k == "var" and nd[1] in dum_args:
                    nm = names(("arg", nd[1]))
                elif k == "var":
                    w = sargs[nd[1]]
                    nm = cx.mk("var", nd[1])
                    if not type_bound(w):
                        if b:
                            raise Untranslatable("regular var in binder position")
                        memo[key] = nm
                        continue
                else:
                    nm = names(m)
                memo[key] = nm if b else cx.mk("app", self.cV, (nm,))
                continue
            tid = nd[1]
            ot = tmap.get(tid)
            if ot is None:
                raise Untranslatable("term " + srcterms[tid].name)
            if b:
                raise Untranslatable("term in binder position")
            kinds = self.info[ot].kinds
            ch = nd[2]
            if not ex:
                stack.append((m, b, True))
                for j in range(len(ch) - 1, -1, -1):
                    if (ch[j], kinds[j] == "n") not in memo:
                        stack.append((ch[j], kinds[j] == "n", False))
                continue
            memo[key] = cx.mk("app", ot, tuple(memo[(a, kinds[j] == "n")] for j, a in enumerate(ch)))
        return memo[top]

    def bal(self, cx, xs, path, pre):
        if not xs:
            return cx.mk("app", self.cnil, ())
        if len(xs) == 1:
            path.setdefault(xs[0], pre)
            return xs[0]
        h = len(xs) // 2
        l = self.bal(cx, xs[:h], path, pre + "L")
        r = self.bal(cx, xs[h:], path, pre + "R")
        return cx.mk("app", self.ctup, (l, r))

    # ---------------- defs ----------------
    def tr_def(self, t):
        if not t.unify:
            tid = self.add_term("c" + t.name, len(t.args), NAT)
            self.info[tid] = Info(*src_info(t))
            self.tmap[t.id] = tid
            return
        class M:
            terms = self.src.terms
        sn, root, _ = decode_unify(M, t)
        cx = Ctx()
        n = len(t.args)
        for i in range(n):
            cx.mk("var", i)
        leaves = [cx.mk("app", self.cV, (cx.mk("var", i),)) if type_bound(w) else cx.mk("var", i)
                  for i, w in enumerate(t.args)]
        dnodes = [i for i, nd in enumerate(sn) if nd[0] == "dummy"]
        dname = {}
        T = self.bal(cx, leaves, {}, "")
        z = None
        for d in dnodes:
            # linear canonical names (perdef.chain): w_0 = nfresh T, w_(k+1) = nfresh (cV w_k); the earlier
            # w_(k+1) = nfresh (ctup (cV w_k) T_k) doubled the printed body per dummy
            z = cx.mk("app", self.nfresh, (T if z is None else cx.mk("app", self.cV, (z,)),))
            dname[d] = z
        body = self.tr_expr(cx, sn, root, t.args, {}, lambda m: dname[m])
        uni, ud, uh = self.unify_of(cx, [body], n)
        body_b, _ = self.emit(cx, n, [], body, is_def=True)
        name = self.uniq("c" + t.name)
        nt = Term(len(self.terms), NAT, True, [NATW] * n, NATW, uni, name=name)
        nt.var_names = ["v%d" % i for i in range(n)]
        self.terms.append(nt)
        self.tname[name] = nt.id
        self.decls.append((STMT_DEF, body_b + b"\0", "def", nt.id, self.print_decl(nt, True)))
        kinds, deps, rd = src_info(t)
        # template for alpha lemmas: body with canonical names; dummies = their name nodes
        self.info[nt.id] = Info(kinds, deps, rd, len(dnodes),
                                (cx.nodes, body, [dname[d] for d in dnodes]))
        self.tmap[t.id] = nt.id
        self.stats["defs"] += 1

    # ---------------- axioms ----------------
    def tr_axiom(self, st):
        t = self.src.thms[st.ref]
        side = AXSIDE.get(t.name, [])
        full = full_side(t)
        # self-check: the minimal list never adds a condition MM0 does not impose
        bad = [c for c in side if c not in full]
        if bad:
            raise AssertionError("AXSIDE[%s] has %r, not implied by the binder deps %r" % (t.name, bad, full))
        omit = [c for c in full if c not in side]
        if omit:
            self.side_omitted[t.name] = omit
            if t.name not in SIDE_OMIT_SOUND:
                raise AssertionError("axiom %s: omitted side conditions %r have no recorded reason" % (t.name, omit))
        if os.environ.get("REFL_FULLSIDE"):     # robustness variant: every MM0-implied condition
            side = full
        class M:
            terms = self.src.terms
        un, uroot, uhyps = decode_unify(M, t)
        cx = Ctx()
        n = len(t.args)
        for i in range(n):
            cx.mk("var", i)
        memo = {}

        def nm(m):
            raise Untranslatable("dummy in axiom")
        hyps = [cx.mk("app", self.cPr, (self.tr_expr(cx, un, h, t.args, memo, nm),)) for h in uhyps]
        hyps += [cx.mk("app", self.nfr if k == "nfr" else self.nne, (cx.mk("var", i), cx.mk("var", j)))
                 for k, i, j in side]
        concl = cx.mk("app", self.cPr, (self.tr_expr(cx, un, uroot, t.args, memo, nm),))
        oid = self.add_axiom(t.name + "_R", n, cx, hyps, concl, "lib")
        self.hmap[t.id] = (oid, side)

    # ---------------- theorems ----------------
    def tr_thm(self, st, dum_free=False):                       # noqa: C901
        """dum_free: the bound args that occur neither in the statement nor in a regular arg's
        dependencies (MM1 header binders used only by the proof) are named like proof dummies
        inside the proof, so they need no nfr / nne side hypotheses. Used only when the plain
        translation has more than mm0-c's LIMITS["hyps"] hypotheses (GEN3's g2paAxCC_* list 31
        proof-only bound names in the header: 282 side hypotheses), so every other statement
        keeps its shape (hand stubs copy reflected statements verbatim)."""
        src = self.src
        t = src.thms[st.ref]
        dag = build_stmt_dag(src, st)
        sn = dag.nodes
        n = len(t.args)
        sargs = t.args
        kinds, deps, _ = src_info(t)
        free = ()
        if dum_free:
            class M0:
                terms = src.terms
            un0, ur0, uh0 = decode_unify(M0, t)
            occ, seen, todo = set(), set(), [ur0] + list(uh0)
            while todo:
                x = todo.pop()
                if x in seen:
                    continue
                seen.add(x)
                nd = un0[x]
                if nd[0] == "var":
                    occ.add(nd[1])
                elif nd[0] == "app":
                    todo.extend(nd[2])
            used = set(occ).union(*deps.values()) if deps else set(occ)
            free = frozenset(i for i in range(n) if kinds[i] == "n" and i not in used)
        cx = Ctx()
        for i in range(n):
            cx.mk("var", i)
        mk = cx.mk
        P = self.P
        # proof-dummy names: Z_j = nfresh(T_j), T_1 = balanced tuple of statement leaves
        zst = {"T": None, "path": {}, "chain": [], "of": {}}

        def names(m):
            z = zst["of"].get(m)
            if z is not None:
                return z
            if zst["T"] is None:
                leaves = [mk("app", self.cV, (mk("var", i),)) if kinds[i] == "n" else mk("var", i)
                          for i in range(n)]
                zst["T"] = self.bal(cx, leaves, zst["path"], "")
                zst["Tcur"] = zst["T"]
            T = zst["Tcur"]
            z = mk("app", self.nfresh, (T,))
            zst["chain"].append((z, T))
            zst["of"][m] = z
            zst["Tcur"] = mk("app", self.ctup, (mk("app", self.cV, (z,)), T))
            return z
        zidx = {}

        emem = {}

        def E(x, b=False):
            r = emem.get((x, b))
            return r if r is not None else self.tr_expr(cx, sn, x, sargs, emem, names, b, free)
        need = set()
        fmemo = {}

        def is_stmt_name(y):
            nd = cx.nodes[y]
            return nd[0] == "var"

        def zinfo(y):
            for j, (z, T) in enumerate(zst["chain"]):
                if z == y:
                    return j, T
            raise MMBError("not a dummy name")

        def proj(y, T, path):
            """(proof of nfr y X, X) for X the subtuple of T at path; base nfr_fresh."""
            key = ("proj", y, path)
            r = fmemo.get(key)
            if r is not None:
                return r
            if not path:
                r = (P(cx, "nfr_fresh", [T]), T)
            else:
                pf, tup = proj(y, T, path[:-1])
                l, rr = cx.nodes[tup][2]
                left = path[-1] == "L"
                r = (P(cx, "nfr_tl" if left else "nfr_tr", [y, l, rr], [pf]), l if left else rr)
            fmemo[key] = r
            return r

        def chain_fr(y, leaf):
            """nfr Z_j leaf, leaf a statement leaf or cV(Z_i), i < j."""
            j, T = zinfo(y)
            path = ""
            for i in range(j - 1, -1, -1):
                if leaf == mk("app", self.cV, (zst["chain"][i][0],)):
                    return proj(y, T, path + "L")[0]
                path += "R"
            p = zst["path"].get(leaf)
            if p is None:
                raise MMBError("leaf not in name base")
            return proj(y, T, path + p)[0]

        def NE(y, w):
            key = ("ne", y, w)
            r = fmemo.get(key)
            if r is not None:
                return r
            if y == w:
                raise Untranslatable("name not distinct")
            sy, sw = is_stmt_name(y), is_stmt_name(w)
            if sy and sw:
                i, k = cx.nodes[y][1], cx.nodes[w][1]
                if i < k:
                    need.add(("nne", i, k))
                    r = mk("sidehyp", ("nne", i, k))
                else:
                    r = P(cx, "nne_sym", [w, y], [NE(w, y)])
            elif not sy and (sw or zinfo(w)[0] < zinfo(y)[0]):
                cw = mk("app", self.cV, (w,))
                r = P(cx, "nfr_Vinv", [y, w], [chain_fr(y, cw)])
            else:
                r = P(cx, "nne_sym", [w, y], [NE(w, y)])
            fmemo[key] = r
            return r

        def FR(y, e):
            """Proof of nfr y e (iterative over e)."""
            top = ("fr", y, e)
            if top in fmemo:
                return fmemo[top]
            stack = [(e, False)]
            while stack:
                x, ex = stack.pop()
                key = ("fr", y, x)
                if key in fmemo:
                    continue
                nd = cx.nodes[x]
                if nd[0] == "var":
                    if is_stmt_name(y):
                        i, k = cx.nodes[y][1], nd[1]
                        if i in deps.get(k, ()) or kinds[k] == "n":
                            raise Untranslatable("freshness of %d in %d fails" % (i, k))
                        need.add(("nfr", i, k))
                        fmemo[key] = mk("sidehyp", ("nfr", i, k))
                    else:
                        fmemo[key] = chain_fr(y, x)
                    continue
                if nd[0] != "app":
                    raise MMBError("bad code node")
                tid, a = nd[1], nd[2]
                inf = self.info.get(tid)
                if inf is None:
                    raise MMBError("no info for " + self.terms[tid].name)
                var = None
                for j, kd in enumerate(inf.kinds):
                    if kd == "n" and a[j] == y:
                        var = j
                        break
                if var is not None and var in inf.retdeps:
                    raise Untranslatable("name occurs free")
                if var is None:
                    subs = [("fr", a[i]) for i in range(len(a)) if inf.kinds[i] == "c"] + \
                           [("ne", a[j]) for j in sorted(inf.retdeps)]
                else:
                    subs = [("fr", a[i]) for i in range(len(a))
                            if inf.kinds[i] == "c" and var not in inf.deps[i]] + \
                           [("ne", a[j]) for j in sorted(inf.retdeps) if j != var]
                todo = [s for s in subs if s[0] == "fr" and ("fr", y, s[1]) not in fmemo]
                if todo and not ex:
                    stack.append((x, True))
                    stack.extend((s[1], False) for s in todo)
                    continue
                hs = [fmemo[("fr", y, s[1])] if s[0] == "fr" else NE(y, s[1]) for s in subs]
                if var is None:
                    fmemo[key] = self.app_thm(cx, self.lemma("nfr", tid), list(a) + [y], hs)
                else:
                    fmemo[key] = self.app_thm(cx, self.lemma("nfr", tid, var), list(a), hs)
            return fmemo[top]

        def side(kind, y, e):
            return FR(y, e) if kind == "nfr" else NE(y, e)

        # ---- conversions: (mode, node, l, r): 'p' MM0 conv l = r, 'a' proof of aeq l r
        cmemo = {}

        def toA(res):
            mode, nd, l, r = res
            if mode == "a":
                return nd
            p0 = P(cx, "aeq_refl", [l])
            e1 = mk("app", self.aeq, (l, r))
            c = mk("cong", self.aeq, (mk("refl", l), mk("symm", nd)))
            return mk("conv", e1, p0, c)

        def trans(a1, a2, l, m_, r):
            return P(cx, "aeq_trans", [l, m_, r], [a1, a2])

        def CV(c, b):
            key = (c, b)
            if key in cmemo:
                return cmemo[key]
            nd = sn[c]
            k = nd[0]
            if k == "refl":
                e = E(nd[1], b)
                res = ("p", mk("refl", e), e, e)
            elif k in ("cut", "cref"):
                res = CV(nd[1], b)
            elif k == "symm":
                mode, x, l, r = CV(nd[1], b)
                res = ("p", mk("symm", x), r, l) if mode == "p" else \
                    ("a", P(cx, "aeq_sym", [l, r], [x]), r, l)
            elif k == "cong":
                ot = self.tmap.get(nd[1])
                if ot is None:
                    raise Untranslatable("term " + self.src.terms[nd[1]].name)
                inf = self.info[ot]
                subs = [CV(x, inf.kinds[j] == "n") for j, x in enumerate(nd[2])]
                l = mk("app", ot, tuple(s[2] for s in subs))
                r = mk("app", ot, tuple(s[3] for s in subs))
                if all(s[0] == "p" for s in subs):
                    res = ("p", mk("cong", ot, tuple(s[1] for s in subs)), l, r)
                else:
                    self.stats["conv_alpha"] += 1
                    code = [j for j in range(len(subs)) if inf.kinds[j] == "c"]
                    args = [s[2] for s in subs] + [subs[j][3] for j in code]
                    res = ("a", self.app_thm(cx, self.lemma("aeq", ot), args,
                                             [toA(subs[j]) for j in code]), l, r)
            elif k == "unfold":
                ot = self.tmap.get(nd[1])
                if ot is None or not self.terms[ot].is_def:
                    raise Untranslatable("unfold")
                inf = self.info[ot]
                L = E(nd[2])
                Eo = E(nd[3])
                sub = CV(nd[4], False)
                if inf.ndum == 0:
                    if sub[0] == "p":
                        res = ("p", mk("unfold", ot, L, Eo, sub[1]), L, sub[3])
                    else:
                        u = toA(("p", mk("unfold", ot, L, Eo, mk("refl", Eo)), L, Eo))
                        res = ("a", trans(u, sub[1], L, Eo, sub[3]), L, sub[3])
                else:
                    self.stats["alpha_steps"] += 1
                    # match the def template against the source instance to find Z_k
                    zs = self.match_dummies(ot, cx, L, Eo)
                    a = list(cx.nodes[L][2])
                    hyps = []
                    for zk in range(len(zs)):
                        hyps += [FR(zs[zk], a[i]) for i in range(len(a)) if inf.kinds[i] == "c"]
                        hyps += [NE(zs[zk], a[j]) for j in range(len(a)) if inf.kinds[j] == "n"]
                        hyps += [NE(zs[zk], zs[l]) for l in range(zk + 1, len(zs))]
                    al = self.app_thm(cx, self.lemma("alpha", ot), a + zs, hyps)
                    got = cx.nodes[al][4]
                    if cx.nodes[got][2][1] != Eo:
                        raise MMBError("alpha template mismatch")
                    if sub[0] == "p" and cx.nodes[sub[1]][0] == "refl":
                        res = ("a", al, L, Eo)
                    else:
                        res = ("a", trans(al, toA(sub), L, Eo, sub[3]), L, sub[3])
            else:
                raise Untranslatable("conv node " + k)
            cmemo[key] = res
            return res

        pmemo = {}
        stack = [(dag.result[1], False)]
        while stack:
            x, ex = stack.pop()
            if x in pmemo:
                continue
            nd = sn[x]
            k = nd[0]
            if k == "hyp":
                pmemo[x] = mk("hyp", nd[1])
            elif k == "thm":
                if nd[1] not in self.hmap:
                    raise Untranslatable("uses " + src.thms[nd[1]].name)
                todo = [h for h in nd[3] if h not in pmemo]
                if todo and not ex:
                    stack.append((x, True))
                    stack.extend((h, False) for h in reversed(todo))
                    continue
                oid, sl = self.hmap[nd[1]]
                ca = src.thms[nd[1]].args
                args = [E(a, type_bound(ca[j])) for j, a in enumerate(nd[2])]
                hs = [pmemo[h] for h in nd[3]] + [side(kd, args[i], args[j]) for kd, i, j in sl]
                pmemo[x] = mk("thm", oid, tuple(args), tuple(hs), mk("app", self.cPr, (E(nd[4]),)))
            elif k == "conv":
                if nd[2] not in pmemo and not ex:
                    stack.append((x, True))
                    stack.append((nd[2], False))
                    continue
                mode, c, l, r = CV(nd[3], False)
                p2 = pmemo[nd[2]]
                if mode == "p":
                    pmemo[x] = mk("conv", mk("app", self.cPr, (l,)), p2, mk("cong", self.cPr, (c,)))
                else:
                    pmemo[x] = P(cx, "cPr_aeq", [r, l], [p2, P(cx, "aeq_sym", [l, r], [c])])
            else:
                raise Untranslatable("proof node " + k)
        root = pmemo[dag.result[1]]
        class M:
            terms = self.src.terms
        un, uroot, uhyps = decode_unify(M, t)
        umemo = {}

        def nonm(m):
            raise MMBError("dummy in statement")
        concl = mk("app", self.cPr, (self.tr_expr(cx, un, uroot, sargs, umemo, nonm),))
        hyps = [mk("app", self.cPr, (self.tr_expr(cx, un, h, sargs, umemo, nonm),)) for h in uhyps]
        needed = sorted(need)
        root = self.resolve_sidehyps(cx, root, needed, len(hyps))
        hyps += [mk("app", self.nfr if kd == "nfr" else self.nne, (mk("var", i), mk("var", j)))
                 for kd, i, j in needed]
        if not dum_free and len(hyps) > LIMITS["hyps"]:
            return self.tr_thm(st, dum_free=True)
        pub = self.thm_pub == "all" or (self.thm_pub == "pub" and t.kind == "thm") or \
            (isinstance(self.thm_pub, (set, frozenset)) and t.name in self.thm_pub)
        oid, blen = self.add_thm_r(t.name + "_R", n, cx, concl, hyps, root, pub)
        # categories of the theorem steps reachable from the root
        seen, todo = set(), [root]
        cat = self.stats.setdefault("steps", {"main": 0, "side": 0, "alpha": 0})
        while todo:
            x = todo.pop()
            if x in seen:
                continue
            seen.add(x)
            nd = cx.nodes[x]
            if nd[0] == "thm":
                nm = self.thms[nd[1]].name
                cat["side" if nm.startswith(("nfr", "nne")) else
                    "alpha" if nm.startswith(("alpha_", "aeq_", "cPr_aeq")) else "main"] += 1
                todo.extend(nd[3])
            elif nd[0] == "conv":
                todo.append(nd[2])
        sh = len(dag.heap)
        if sh >= 1000:
            rr = self.last_use["heap"] / sh
            if rr > self.ratio["heap"][0]:
                self.ratio["heap"] = (rr, t.name)
        src_steps = sum(1 for nd in sn if nd[0] == "thm")
        self.stats["src_steps"] = self.stats.get("src_steps", 0) + src_steps
        self.hmap[t.id] = (oid, needed)
        self.stats["thms"] += 1
        self.stats["side_hyps"] += len(needed)
        self.stats["in_bytes"] += len(st.body)
        self.stats["in_cmds"] += dag.ncmds
        self.stats["out_bytes"] += blen

    def match_dummies(self, ot, cx, L, Eo):
        """Proof names Z_k that the source unfolding used for def ot's dummies."""
        inf = self.info[ot]
        tnodes, troot, tdum = inf.tpl
        a = cx.nodes[L][2]
        pos = {d: k for k, d in enumerate(tdum)}
        zs = [None] * len(tdum)
        st = [(troot, Eo)]
        seen = set()
        while st:
            tn, on = st.pop()
            if (tn, on) in seen:
                continue
            seen.add((tn, on))
            if tn in pos:
                zs[pos[tn]] = on
                continue
            nd = tnodes[tn]
            if nd[0] == "var":
                continue
            od = cx.nodes[on]
            if od[0] != "app" or od[1] != nd[1]:
                raise MMBError("unfold instance mismatch")
            st.extend(zip(nd[2], od[2]))
        if any(z is None for z in zs):
            raise Untranslatable("unused def dummy")
        return zs

    def add_thm_r(self, name, n, cx, concl, hyps, root, pub):
        name = name if pub and name not in self.names else self.uniq(name)
        self.names.add(name)
        uni, ud, uh = self.unify_of(cx, [concl] + list(reversed(hyps)), n)
        body_b, ncmd = self.emit(cx, n, hyps, root)
        use = dict(self.last_use, ustack=ud, uheap=uh, bv=0)
        self.check_limits(name, use)
        th = Thm(len(self.thms), [NATW] * n, uni, name=name)
        th.var_names = ["v%d" % i for i in range(n)]
        th.hyp_names = ["h%d" % i for i in range(len(hyps))]
        self.thms.append(th)
        self.hname[name] = th.id
        body = body_b + b"\0"
        self.decls.append((STMT_THM if pub else STMT_LOCAL_THM, body, "thm", th.id,
                           self.print_decl(th, False) if pub else None))
        self.stats["out_cmds"] += ncmd
        return th.id, len(body)

    # ---------------- driver ----------------
    def run(self, max_thms=None, thm_pub="pub", progress=None):
        self.thm_pub = thm_pub
        done = 0
        for i, st in enumerate(self.src.iter_stmts()):
            if progress and i % 20000 == 0:
                progress(i, done)
            if st.kind in ("sort",):
                continue
            if st.kind in ("term", "def", "local_def"):
                t = self.src.terms[st.ref]
                if st.ref in self.tmap:
                    continue
                if st.kind == "term":
                    raise MMBError("unknown primitive term " + str(t.name))
                try:
                    self.tr_def(t)
                except Untranslatable as e:
                    self.why[("term", st.ref)] = str(e)
                continue
            if st.kind == "axiom":
                self.tr_axiom(st)
                continue
            if max_thms is not None and done >= max_thms:
                break
            done += 1
            try:
                self.tr_thm(st)
            except Untranslatable as e:
                self.why[("thm", st.ref)] = str(e)
        return done

    def write_out(self, path, mm0):
        w = MMBWriter(path, os.path.dirname(os.path.abspath(path)))
        for s in self.lib.sorts:
            w.add_sort(s.mods, s.name)
        for t in self.terms:
            w.add_term(t)
        for t in self.thms:
            w.add_thm(t)
        spec = list(self.spec)
        for _ in self.lib.sorts:
            w.add_stmt(STMT_SORT)
        for op, body, kind, ref, line in self.decls:
            w.add_stmt(op, body=body)
            if line is not None:
                spec.append(line)
        w.finish("rebuild")
        with open(mm0, "w", newline="\n") as f:
            f.write("\n".join(spec) + "\n")


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("src"); ap.add_argument("out"); ap.add_argument("mm0")
    ap.add_argument("--max", type=int, default=None)
    ap.add_argument("--pub", default="pub")
    ns = ap.parse_args(argv)
    t0 = time.time()
    src = read_mmb(ns.src)
    r = Refl(src)
    r.run(ns.max, ns.pub, progress=lambda i, d: print("  stmt %d thms %d %.0fs" % (i, d, time.time() - t0),
                                                      file=sys.stderr, flush=True))
    r.write_out(ns.out, ns.mm0)
    s = r.stats
    fails = [(k, v) for k, v in r.why.items() if k[0] == "thm"]
    print("defs %d thms %d failed %d (time %.1fs)" % (s["defs"], s["thms"], len(fails), time.time() - t0))
    print("proof bytes in %d -> out %d (%.3fx); cmds in %d -> out %d (%.3fx)" % (
        s["in_bytes"], s["out_bytes"], s["out_bytes"] / max(1, s["in_bytes"]),
        s["in_cmds"], s["out_cmds"], s["out_cmds"] / max(1, s["in_cmds"])))
    print("lib axioms %d; generated per-def lemmas %d (est. %d cmds of generated proofs); "
          "alpha steps %d; alpha congruences %d; statement side hyps %d" % (
              s["lib_axioms"], s["gen_lemmas"], s["gen_lemma_est_cmds"], s["alpha_steps"],
              s["conv_alpha"], s["side_hyps"]))
    print("file bytes in %d -> out %d (%.3fx)" % (os.path.getsize(ns.src), os.path.getsize(ns.out),
                                                 os.path.getsize(ns.out) / os.path.getsize(ns.src)))
    print("mm0-c maxima:", r.usage)
    print("omitted MM0-implied side conditions:", sorted(r.side_omitted.items()))
    print("theorem steps: source %d; output %r; worst heap ratio (heap>=1000) %r" % (
        s.get("src_steps", 0), s.get("steps"), r.ratio["heap"]))
    import collections
    print("failure reasons:", collections.Counter(v.split(" (")[0][:40] for _, v in fails).most_common(10))
    print("first failures:", [(src.thms[k[1]].name, v) for k, v in fails][:10])
    print("defs not translated:", [(src.terms[k[1]].name, v) for k, v in r.why.items() if k[0] == "term"][:10])


if __name__ == "__main__":
    from translator.negtrans import big_stack
    sys.exit(big_stack(main))
