"""GEN7 C3: proofs of the per-def lemmas of a reflection (nfr_D, nfr_D_j, aeq_D, alpha_D).

Input: a Refl object after a run (its code defs and the per-def lemma statements it used).
Output: MM1 text over gen7_lib.mm1: the code defs, private helper lemmas and the per-def
lemmas as public theorems, each proved once from the gen7 library:

  g7nfi_D(_j)  nfr through cD (curried; deduction over the body, binder cases by g7nf_cAl)
  g7pfr_D(_j)  the same for the semantic freshness trFr (suc x) (trPA (cD a))
  g7evr_D      equivariance: renaming names by g7sw p q renames trPA (cD a) by g7Sw p q
  g7pal_D      renaming the canonical dummy names of D to any fresh names keeps trPA
  aeq_D   = g7evr_D at p = q (the identity);  alpha_D = g7pal_D;  nfr_D(_j) = g7nfi_D(_j).

Expressions are trees: ('lit', text) | ('app', name, [children]) ; templates use
('arg', i) and ('dum', k) leaves.
"""

import os

BIN = {"cIm", "cEq", "cEl", "cAdd", "cMul"}
# Freshness proofs (g7nfc_D / g7pfc_D) are split into helper lemmas at subterms of the def body whose
# unsplit size reaches this many nodes. mm0-rs's elaborator recurses about linearly in the size of one
# proof: the 24,100-node body of g2paAxK172 overflowed the 1 MB main-thread stack of mm0-rs on Windows
# (host job 00000-C-031) and needs more than 4 MB on Linux; with the split every proof stays small.
SPLIT = int(os.environ.get("GEN7_PERDEF_SPLIT", "1000"))
UN = {"cNot", "cSuc", "cThe"}
CONST = {"cTru", "c0"}
BINDER = {"cAl", "cAb"}


class GenError(Exception):
    pass


def pr(e):
    if e[0] == "lit":
        return e[1]
    if not e[2]:
        return e[1]
    return "(%s %s)" % (e[1], " ".join(pr(c) for c in e[2]))


def lit(s): return ("lit", s)
def app(n, *ch): return ("app", n, list(ch))
def cv(y): return app("cV", y)


def bal(xs):
    if not xs:
        return app("cnil")
    if len(xs) == 1:
        return xs[0]
    h = len(xs) // 2
    return app("ctup", bal(xs[:h]), bal(xs[h:]))


def tuple_path(T, target):
    """Path ('l'/'r' steps) to a leaf equal to target inside nested ctup T, or None."""
    if T == target:
        return []
    if T[0] == "app" and T[1] == "ctup":
        for s, c in (("l", T[2][0]), ("r", T[2][1])):
            p = tuple_path(c, target)
            if p is not None:
                return [s] + p
    return None


def fresh_path(u, target):
    """Proof of nfr u target when u = nfresh T and target is a leaf of T."""
    if not (u[0] == "app" and u[1] == "nfresh"):
        return None
    p = tuple_path(u[2][0], target)
    if p is None:
        return None
    s = "nfr_fresh"
    for st in p:
        s = "(nfr_%s %s)" % ("tl" if st == "l" else "tr", s)
    return s


def chain(T, m):
    """m canonical names above T, linear in size: w_0 = nfresh T, w_(k+1) = nfresh (cV w_k) (increasing, so
    pairwise distinct and not free in T; facts by order, ord_le / ord_lt). Returns the names and a term above all
    of them (ctup (cV w_last) T)."""
    W = []
    for k in range(m):
        W.append(app("nfresh", T if k == 0 else cv(W[-1])))
    return W, (app("ctup", cv(W[-1]), T) if W else T)


def ord_le(x, t):
    """proof of x <= t when x is a subterm of t through ctup / cV / nfresh, or None."""
    if x == t:
        return "leid"
    if t[0] != "app":
        return None
    h, ch = t[1], t[2]
    if h == "nfresh":
        p = ord_le(x, ch[0])
        return p and "(g7_le_fr %s)" % p
    if h == "cV":
        p = ord_le(x, ch[0])
        return p and "(g7_le_cV %s)" % p
    if h == "ctup":
        p = ord_le(x, ch[0])
        if p:
            return "(g7_le_tl %s)" % p
        p = ord_le(x, ch[1])
        return p and "(g7_le_tr %s)" % p
    return None


def ord_lt(x, u):
    """proof of x < u for a canonical name u = nfresh s with x below s, or None."""
    if u[0] == "app" and u[1] == "nfresh":
        p = ord_le(x, u[2][0])
        return p and "(g7_lt_fr %s)" % p
    return None


def nfr_path(u, c):
    """proof of nfr u c: c is a leaf of u's tuple (fresh_path), or c is below u (nfr_gt)."""
    p = fresh_path(u, c)
    if p:
        return p
    p = ord_lt(c, u)
    return p and "(nfr_gt %s)" % p


def proj(i, n):
    if n == 1:
        return "id"
    if i == n - 1:
        return "anr"
    return "(syl %s anl)" % proj(i, n - 1)


class Oracle:
    """Closed facts available in one lemma: hypotheses and canonical-name freshness."""
    def __init__(self):
        self.ne = {}       # (u, v) -> proof of u != v
        self.frs = {}      # (x, c) -> proof of trFr (suc x) (trPA c)
        self.nfs = {}      # (x, c) -> proof of nfr x c

    def get_ne(self, u, v):
        a, b = pr(u), pr(v)
        if (a, b) in self.ne:
            return self.ne[(a, b)]
        if (b, a) in self.ne:
            return "(necom %s)" % self.ne[(b, a)]
        p = fresh_path(u, cv(v))
        if p:
            return "(nfr_Vinv %s)" % p
        p = fresh_path(v, cv(u))
        if p:
            return "(necom (nfr_Vinv %s))" % p
        p = ord_lt(v, u)
        if p:
            return "(ltner %s)" % p
        p = ord_lt(u, v)
        if p:
            return "(ltne %s)" % p
        return None

    def get_nfs(self, x, c):
        k = (pr(x), pr(c))
        if k in self.nfs:
            return self.nfs[k]
        return nfr_path(x, c)

    def get_frs(self, x, c):
        k = (pr(x), pr(c))
        if k in self.frs:
            return self.frs[k]
        p = self.get_nfs(x, c)
        return "(g7_nfr_fresh %s)" % p if p else None


class PerDef:
    def __init__(self, r):
        self.r = r
        self.out = []          # MM1 text items in dependency order
        self.done = {}         # key -> lemma name
        self.tpls = {}
        self.split = None      # gen_fr: helper-lemma state while one freshness lemma is generated

    # ---- def data ----
    def nm(self, oid): return self.r.terms[oid].name
    def info(self, oid): return self.r.info[oid]
    def is_def(self, oid): return self.r.terms[oid].is_def

    def tpl(self, oid):
        t = self.tpls.get(oid)
        if t is not None:
            return t
        inf = self.info(oid)
        nodes, root, tdum = inf.tpl
        dpos = {d: k for k, d in enumerate(tdum)}
        memo = {}

        def tr(n):
            if n in memo:
                return memo[n]
            if n in dpos:
                r = ("dum", dpos[n])
            else:
                nd = nodes[n]
                if nd[0] == "var":
                    r = ("arg", nd[1])
                else:
                    r = ("app", nd[1], [tr(a) for a in nd[2]])
            memo[n] = r
            return r
        t = self.tpls[oid] = tr(root)
        return t

    def inst(self, t, args, dums):
        k = t[0]
        if k == "arg":
            return args[t[1]]
        if k == "dum":
            return dums[t[1]]
        return ("app", self.nm(t[1]), [self.inst(c, args, dums) for c in t[2]])

    def canon(self, oid, args):
        inf = self.info(oid)
        leaves = [cv(a) if inf.kinds[i] == "n" else a for i, a in enumerate(args)]
        T = bal(leaves)
        return chain(T, inf.ndum)

    def vars(self, oid, pre="v"):
        return [lit("%s%d" % (pre, i)) for i in range(len(self.info(oid).kinds))]

    def code_idx(self, oid): return [i for i, k in enumerate(self.info(oid).kinds) if k == "c"]
    def name_idx(self, oid): return [i for i, k in enumerate(self.info(oid).kinds) if k == "n"]

    def emit(self, name, binders, hyps, concl, proof, pub=False):
        stmt = " -> ".join(hyps + [concl])
        self.out.append("%stheorem %s %s: $ %s $ =\n(named '%s);\n" % ("pub " if pub else "", name, binders, stmt, proof))

    # ---- freshness (syntactic: sem False / semantic: sem True), deduction over a context ----
    def F(self, sem, x, e): return ("trFr (suc %s) (trPA %s)" if sem else "nfr %s %s") % (pr(x), pr(e))

    def ned(self, u, v, ctx, orc):
        """G -> u != v."""
        a, b = pr(u), pr(v)
        for i, ent in enumerate(ctx):
            if ent[0] == "ne" and (ent[1], ent[2]) == (a, b):
                return proj(i, len(ctx))
            if ent[0] == "ne" and (ent[1], ent[2]) == (b, a):
                return "(syl necom %s)" % proj(i, len(ctx))
        p = orc.get_ne(u, v)
        if p is None:
            raise GenError("no proof of %s != %s" % (a, b))
        return "(a1i %s)" % p

    def bdeps(self, oid, i):
        inf = self.info(oid)
        return [j for j in sorted(inf.deps[i]) if j not in inf.retdeps]

    def ctx_text(self, sem, ctx, x):
        """The context G of frd as a formula: the entries' formulas, conjoined left-nested (as proj reads them).
        The trivial context (closed proofs, discharged by eqid) is stated as x = x."""
        ts = []
        for ent in ctx:
            if ent[0] == "triv":
                ts.append("%s = %s" % (pr(x), pr(x)))
            elif ent[0] == "ne":
                ts.append("%s != %s" % (ent[1], ent[2]))
            else:
                f = ("trFr (suc %s) (trPA %s)" if ent[0] == "fr" else "nfr %s %s") % (ent[1], ent[2])
                ts.append(" -> ".join(["%s != %s" % (ent[1], pr(y)) for y in ent[3]] + [f]))
        g = ts[0]
        for t in ts[1:]:
            g = "(%s) /\\ (%s)" % (g, t)
        return g

    def split_sizes(self, e, eff):
        """eff[id(n)] = size of n with the subterms that get their own helper lemma counted as one node."""
        if e[0] != "app":
            return 1
        n = 1
        for c in e[2]:
            k = self.split_sizes(c, eff)
            n += 1 if k >= SPLIT else k
        eff[id(e)] = n
        return n

    def frd(self, sem, x, e, ctx, orc, top=False):
        """G -> F(x, e) for a code expression e."""
        sp = self.split
        if sp is not None and not top and e[0] == "app" and sp["eff"].get(id(e), 0) >= SPLIT:
            g = self.ctx_text(sem, ctx, x)
            stmt = "%s -> %s" % (g, self.F(sem, x, e))
            nm = sp["done"].get(stmt)
            if nm is None:
                body = self.frd(sem, x, e, ctx, orc, top=True)
                nm = "%s_k%d" % (sp["name"], len(sp["done"]))
                self.out.append("theorem %s %s: $ %s $ =\n(named '%s);\n" % (nm, sp["binders"], stmt, body))
                sp["done"][stmt] = nm
            return "(%s %s)" % (nm, sp["call"]) if sp["call"] else nm
        key = "fr" if sem else "nf"
        px = pr(x)
        # print e only when the context has a hypothesis about x (pr is linear in e; calling it at every node of
        # a large def body made this quadratic)
        a = pr(e) if any(ent[0] == key and ent[1] == px for ent in ctx) else None
        for i, ent in enumerate(ctx):
            if a is not None and ent[0] == key and (ent[1], ent[2]) == (px, a):
                t = proj(i, len(ctx))
                for y in ent[3]:
                    t = "(mpd %s %s)" % (self.ned(x, y, ctx, orc), t)
                return t
        if e[0] == "lit":
            p = orc.get_frs(x, e) if sem else orc.get_nfs(x, e)
            if p is None:
                raise GenError("no freshness of %s in %s" % (pr(x), pr(e)))
            return "(a1i %s)" % p
        h = e[1]
        pre = "g7pf_" if sem else "g7nf_"
        if h == "cV":
            if sem:
                return "(syl g7pf_cV %s)" % self.ned(e[2][0], x, ctx, orc)
            return "(syl g7nf_cV %s)" % self.ned(x, e[2][0], ctx, orc)
        if h in BIN:
            return "(sylc %s%s %s %s)" % (pre, h, self.frd(sem, x, e[2][0], ctx, orc), self.frd(sem, x, e[2][1], ctx, orc))
        if h in UN:
            return "(syl %s%s %s)" % (pre, h, self.frd(sem, x, e[2][0], ctx, orc))
        if h in CONST:
            return "(a1i %s%s)" % (pre, h)
        if h in BINDER:
            y, p = e[2]
            if pr(y) == pr(x):
                return "(a1i %s)" % (("g7pf_%s0" % h) if sem else ("nfr_%s_0" % h))
            inner = self.frd(sem, x, p, ctx + [("ne", pr(x), pr(y))], orc)
            return "(syl %s%s (exp %s))" % (pre, h, inner)
        oid = self.r.tname[h]
        inf = self.info(oid)
        ch = e[2]
        lem = self.need("pf" if sem else "nf", oid)
        hp = []
        for i in self.code_idx(oid):
            ys = [ch[j] for j in self.bdeps(oid, i)]
            hit = [t for t, y in enumerate(ys) if pr(y) == pr(x)]
            if hit:
                q = "(mpi eqid absurd)"
                for _ in range(hit[0]):
                    q = "(a1i %s)" % q
                hp.append("(a1i %s)" % q)
                continue
            q = self.frd(sem, x, ch[i], ctx + [("ne", pr(x), pr(y)) for y in ys], orc)
            for _ in ys:
                q = "(exp %s)" % q
            hp.append(q)
        for j in sorted(inf.retdeps):
            hp.append(self.ned(x, ch[j], ctx, orc))
        t = "(a1i %s)" % lem
        for q in hp:
            t = "(mpd %s %s)" % (q, t)
        return t

    def fr_closed(self, sem, x, e, orc):
        """closed proof of F(x, e) (deduction under the trivial context x = x)."""
        if self.split is not None:
            self.split_sizes(e, self.split["eff"])
        return "(ax_mp %s eqid)" % self.frd(sem, x, e, [("triv",)], orc, top=True)

    def gen_fr(self, sem, oid, var=None):
        """g7pfc_D / g7nfc_D: freshness of a name x through cD, hypotheses conditional on x
        differing from the bound names each code argument depends on."""
        inf = self.info(oid)
        a = self.vars(oid)
        x = lit("x")
        name = "%s_%s" % ("g7pfc" if sem else "g7nfc", self.nm(oid))
        ctx, hyps = [], []
        for i in self.code_idx(oid):
            ys = [a[j] for j in self.bdeps(oid, i)]
            ctx.append(("fr" if sem else "nf", "x", pr(a[i]), ys))
            hyps.append("(%s)" % " -> ".join(["x != %s" % pr(y) for y in ys] + [self.F(sem, x, a[i])]))
        for j in sorted(inf.retdeps):
            ctx.append(("ne", "x", pr(a[j])))
            hyps.append("x != %s" % pr(a[j]))
        concl = self.F(sem, x, app(self.nm(oid), *a))
        body = self.inst(self.tpl(oid), a, self.canon(oid, a)[0])
        orc = Oracle()
        names = [pr(v) for v in a] + ["x"]
        eff = {}
        self.split_sizes(body, eff)
        outer, self.split = self.split, dict(name=name, binders="(%s: nat)" % " ".join(names), call="", eff=eff, done={})
        try:
            if ctx:
                p = self.frd(sem, x, body, ctx, orc, top=True)
                for _ in range(len(ctx) - 1):
                    p = "(exp %s)" % p
            else:
                p = "(ax_mp %s eqid)" % self.frd(sem, x, body, [("triv",)], orc, top=True)
        finally:
            self.split = outer     # need() inside frd generates the lemmas of inner defs recursively
        self.emit(name, "(%s: nat)" % " ".join(names), hyps, concl, p)
        return name

    # ---- equivariance ----
    def R0(self, s): return "paFormulaRename (g7Sw p q) 0 (%s)" % s

    def inv(self, t, codeiv, nameeq, dumeq):
        """proof of trPA R = R0 (trPA L) for template node t (the two instances are implicit)."""
        k = t[0]
        if k == "arg":
            return codeiv[t[1]]
        if k == "dum":
            raise GenError("dummy in code position")
        h = self.nm(t[1])
        ch = t[2]
        def ne_(c):
            if c[0] == "arg":
                return nameeq[c[1]]
            if c[0] == "dum":
                return dumeq[c[1]]
            raise GenError("name expression in template")
        if h == "cV":
            return "(g7iv_cV %s)" % ne_(ch[0])
        if h in BIN:
            return "(g7iv_%s %s %s)" % (h, self.inv(ch[0], codeiv, nameeq, dumeq), self.inv(ch[1], codeiv, nameeq, dumeq))
        if h in UN:
            return "(g7iv_%s %s)" % (h, self.inv(ch[0], codeiv, nameeq, dumeq))
        if h in CONST:
            return "g7iv_%s" % h
        if h in BINDER:
            return "(g7iv_%s %s %s)" % (h, ne_(ch[0]), self.inv(ch[1], codeiv, nameeq, dumeq))
        oid = t[1]
        lem = self.need("ev", oid)
        args = [self.inv(ch[i], codeiv, nameeq, dumeq) for i in self.code_idx(oid)] + \
               [ne_(ch[j]) for j in self.name_idx(oid)]
        return "(%s %s)" % (lem, " ".join(args)) if args else lem

    def gen_ev(self, oid):
        inf = self.info(oid)
        nmD = self.nm(oid)
        a, b = self.vars(oid, "v"), self.vars(oid, "w")
        C, N = self.code_idx(oid), self.name_idx(oid)
        hyps, hnames = [], []
        codeiv, nameeq = {}, {}
        for i in C:
            hyps.append("trPA %s = %s" % (pr(b[i]), self.R0("trPA %s" % pr(a[i]))))
            codeiv[i] = "hc%d" % i
        for j in N:
            hyps.append("%s = g7sw p q %s" % (pr(b[j]), pr(a[j])))
            nameeq[j] = "hn%d" % j
        hb = "".join(" (hc%d: $ %s $)" % (i, h) for i, h in zip(C, hyps[:len(C)])) + \
             "".join(" (hn%d: $ %s $)" % (j, h) for j, h in zip(N, hyps[len(C):]))
        binders = "(p q%s: nat)%s" % ("".join(" " + pr(v) for v in a + b), hb)
        concl = "trPA %s = %s" % (pr(app(nmD, *b)), self.R0("trPA %s" % pr(app(nmD, *a))))
        m = inf.ndum
        if m == 0:
            proof = self.inv(self.tpl(oid), codeiv, nameeq, {})
        else:
            Wa, _ = self.canon(oid, a)
            Wsw = [app("g7sw", lit("p"), lit("q"), w) for w in Wa]
            invp = self.inv(self.tpl(oid), codeiv, nameeq, {k: "eqid" for k in range(m)})
            pal = self.need("pal", oid)
            orc = Oracle()
            hp = []
            for k in range(m):
                for i in C:
                    hp.append("(mpbir (trFreq2 hc%d) (g7e_img g7_tr_bound (g7_nfr_fresh %s)))" % (i, self.need_path(Wa[k], a[i])))
                for j in N:
                    hp.append("(g7_ne_r hn%d (g7sw_ne2 %s))" % (j, self.need_ne(orc, Wa[k], a[j])))
                for l in range(k + 1, m):
                    hp.append("(g7sw_ne2 %s)" % self.need_ne(orc, Wa[k], Wa[l]))
            proof = "(eqtr (%s %s) %s)" % (pal, " ".join(hp), invp) if hp else "(eqtr %s %s)" % (pal, invp)
        name = "g7evr_" + nmD
        self.out.append("theorem %s %s: $ %s $ =\n(named '%s);\n" % (name, binders, concl, proof))
        return name

    def need_path(self, u, c):
        p = nfr_path(u, c)
        if p is None:
            raise GenError("no path")
        return p

    def need_ne(self, orc, u, v):
        p = orc.get_ne(u, v)
        if p is None:
            raise GenError("no ne %s %s" % (pr(u), pr(v)))
        return p

    # ---- alpha: rename the canonical dummies to fresh names ----
    def gen_pal(self, oid):
        inf = self.info(oid)
        nmD = self.nm(oid)
        m = inf.ndum
        a = self.vars(oid)
        z = [lit("z%d" % k) for k in range(m)]
        C, N = self.code_idx(oid), self.name_idx(oid)
        orc = Oracle()
        hyps, hb = [], []
        cnt = 0
        def hyp(stmt):
            nonlocal cnt
            h = "h%d" % cnt
            cnt += 1
            hb.append(" (%s: $ %s $)" % (h, stmt))
            return h
        for k in range(m):
            for i in C:
                orc.frs[(pr(z[k]), pr(a[i]))] = hyp("trFr (suc %s) (trPA %s)" % (pr(z[k]), pr(a[i])))
            for j in N:
                orc.ne[(pr(z[k]), pr(a[j]))] = hyp("%s != %s" % (pr(z[k]), pr(a[j])))
            for l in range(k + 1, m):
                orc.ne[(pr(z[k]), pr(z[l]))] = hyp("%s != %s" % (pr(z[k]), pr(z[l])))
        W, Tm = self.canon(oid, a)
        tp = self.tpl(oid)
        if m == 1:
            steps = [(W[0], z[0], W, z)]
        else:
            Y, _ = chain(app("ctup", Tm, bal([cv(x) for x in z])), m)
            steps = []
            cur = list(W)
            for k in range(m):
                nxt = cur[:k] + [Y[k]] + cur[k + 1:]
                steps.append((W[k], Y[k], cur, nxt))
                cur = nxt
            for k in range(m):
                nxt = cur[:k] + [z[k]] + cur[k + 1:]
                steps.append((Y[k], z[k], cur, nxt))
                cur = nxt
        name = "g7pal_" + nmD
        binders = "(%s: nat)%s" % (" ".join(pr(v) for v in a + z), "".join(hb))
        eqs = []
        # helper lemmas of the closed freshness proofs (fr_closed) take the hypotheses h0.. of this lemma
        outer, self.split = self.split, dict(name=name, binders=binders, call=" ".join("h%d" % j for j in range(cnt)),
                                             eff={}, done={})
        try:
            es = [self.step(oid, tp, a, p, q, before, after, orc) for (p, q, before, after) in steps]
        finally:
            self.split = outer
        for i, (p, q, before, after) in enumerate(steps):
            e = es[i]
            if m >= 4:
                # one lemma per renaming step: keeps each proof under mm0's 55 dummies and the elaborator fast
                sn = "%s_s%d" % (name, i)
                self.out.append("theorem %s %s: $ trPA %s = trPA %s $ =\n(named '%s);\n" % (
                    sn, binders, pr(self.inst(tp, a, before)), pr(self.inst(tp, a, after)), e))
                e = "(%s %s)" % (sn, " ".join("h%d" % j for j in range(cnt)))
            eqs.append(e)
        proof = eqs[-1]
        for e in reversed(eqs[:-1]):
            proof = "(eqtr %s %s)" % (e, proof)
        concl = "trPA %s = trPA %s" % (pr(app(nmD, *a)), pr(self.inst(tp, a, z)))
        self.out.append("theorem %s %s: $ %s $ =\n(named '%s);\n" % (name, binders, concl, proof))
        return name

    def step(self, oid, tp, a, p, q, before, after, orc):
        """trPA (body[a, before]) = trPA (body[a, after]) for the swap of the names p, q."""
        C, N = self.code_idx(oid), self.name_idx(oid)
        sp, sq = pr(p), pr(q)
        def ne(u, v):
            r = orc.get_ne(u, v)
            if r is None:
                raise GenError("step: no %s != %s" % (pr(u), pr(v)))
            return r
        def frs(x, c):
            r = orc.get_frs(x, c)
            if r is None:
                raise GenError("step: no fresh %s in %s" % (pr(x), pr(c)))
            return r
        codeiv = {i: "(g7iv_fix %s %s)" % (frs(p, a[i]), frs(q, a[i])) for i in C}
        nameeq = {j: "(eqcom (g7sw_ne %s %s))" % (ne(a[j], p), ne(a[j], q)) for j in N}
        dumeq = {}
        for l, (bl, al) in enumerate(zip(before, after)):
            if pr(bl) == sp:
                assert pr(al) == sq
                dumeq[l] = "(eqcom g7sw_p)"
            else:
                assert pr(al) == pr(bl)
                dumeq[l] = "(eqcom (g7sw_ne %s %s))" % (ne(bl, p), ne(bl, q))
        # the swap at the level of the equivariance lemmas: p q are the names p, q
        invp = self.inv_pq(tp, codeiv, nameeq, dumeq, sp, sq)
        Ib = self.inst(tp, a, before)
        fix = "(g7e_fix g7_tr_bound %s %s)" % (self.fr_closed(True, p, Ib, orc), self.fr_closed(True, q, Ib, orc))
        return "(eqtr (eqcom %s) (eqcom %s))" % (fix, invp)

    def inv_pq(self, tp, codeiv, nameeq, dumeq, sp, sq):
        return self.inv(tp, codeiv, nameeq, dumeq)

    # ---- public lemmas ----
    def need(self, kind, oid, var=None):
        key = (kind, oid, var)
        if key in self.done:
            return self.done[key]
        if kind == "nf":
            r = self.gen_fr(False, oid, var)
        elif kind == "pf":
            r = self.gen_fr(True, oid, var)
        elif kind == "ev":
            r = self.gen_ev(oid)
        elif kind == "pal":
            r = self.gen_pal(oid)
        else:
            raise ValueError(kind)
        self.done[key] = r
        return r

    def public(self, kind, oid, var, line):
        """line: the refl spec line `axiom NAME ...: $ .. $;` -> pub theorem with proof."""
        inf = self.info(oid)
        import re
        stmt = line.replace("axiom ", "pub theorem ", 1).rstrip(";")
        nh = len(re.findall(r"\(h\d+:", stmt))
        hs = " ".join("h%d" % i for i in range(nh))
        if kind == "nfr":
            lem = self.need("nf", oid)
            hp, c = [], 0
            for i in self.code_idx(oid):
                bd = self.bdeps(oid, i)
                if var is not None and var in inf.deps[i]:
                    t = bd.index(var)
                    q = "(mpi eqid absurd)"
                    for _ in range(t):
                        q = "(a1i %s)" % q
                    hp.append(q)
                    continue
                q = "h%d" % c; c += 1
                for _ in bd:
                    q = "(a1i %s)" % q
                hp.append(q)
            for j in sorted(inf.retdeps):
                if j != var:
                    hp.append("h%d" % c); c += 1
            proof = "(%s %s)" % (lem, " ".join(hp)) if hp else lem
        elif kind == "aeq":
            lem = self.need("ev", oid)
            C, N = self.code_idx(oid), self.name_idx(oid)
            hp = ["(eqtr (eqcom h%d) (eqcom (g7e_idpp g7_tr_bound)))" % k for k in range(len(C))] + \
                 ["(eqcom g7sw_pp)" for _ in N]
            n = len(inf.kinds)
            proof = "(eqcom (eqtr (! %s $ 0 $ $ 0 $ %s %s) (g7e_idpp g7_tr_bound)))" % (lem, " ".join(["_"] * (2 * n)), " ".join(hp))
        else:
            lem = self.need("pal", oid)
            m = inf.ndum
            C, N = self.code_idx(oid), self.name_idx(oid)
            hp, c = [], 0
            for k in range(m):
                for _ in C:
                    hp.append("(g7_nfr_fresh h%d)" % c); c += 1
                for _ in N:
                    hp.append("h%d" % c); c += 1
                for _ in range(k + 1, m):
                    hp.append("h%d" % c); c += 1
            proof = "(%s %s)" % (lem, " ".join(hp))
        self.out.append("%s =\n(named '%s);\n" % (stmt, proof))
