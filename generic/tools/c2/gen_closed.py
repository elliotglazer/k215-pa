#!/usr/bin/env python3
"""G2GEN PA front end: CLOSED-TERM EVALUATION generator (lanes/G2GEN.md "CLOSED-TERM EVALUATION"; mismatch 2 of
"PA FRONT END").

  python3 gen_closed.py SPEC.mm0 PERDEF.mm1 OUTDIR --thm T_R --name N --src MODULE [--bridge stub|host] [--rec PROOF]
  python3 gen_closed.py SPEC.mm0 PERDEF.mm1 OUTDIR --name N --src MODULE --terms D1,D2,..   (evaluation lemmas only)

SPEC.mm0 / PERDEF.mm1: a refl_lib output (OUT/out.mm0, OUT/gen7/perdef.mm1) of a source that contains the Theorem-1
input T in VARIABLE form (equations as antecedents),
    T (R m M ..: nat): $ R = D_R -> m = D_m -> M = D_M -> A[R, m, M] -> B[R, m, M] $
together with gen7/g7ev_src's five roots (tools/gen7/c2/roots_ev.txt). GEN7_NEED must list nf:cX for every code def
X in the conclusion A -> B (for the PA bridge: nf:cpaThProvable,nf:cg2paAxSet,nf:ctmHalts).
MODULE: the source module (relative to pa-mm0, without extension) defining D_R, D_m, D_M (imported for cNum D).

Writes OUTDIR/gen7/N_ev.mm1 / .mm0 (imports g7ev_lib and MODULE):
  - the stub T_R, VERBATIM from SPEC (resolved by link.py against the same reflection),
  - g7ev_v_D for every def D in the code closure of the D's:  PA |- [cD = cNum D]  (closed D) or the hypothesis form
    cPr (cEq x_i (cNum a_i)) .. -> cPr (cEq (cD x..) (cNum (D a..)))  (D with arguments); one lemma per def, bodies
    over 0 / suc / + / * / pairing / other such defs (anything else is refused with the reason),
  - N_hRefl:  paProvable 0 (paFormulaImp (trJ (trPA A')) (trJ (trPA B')))  with A', B' = A, B at the codes cNum D_*,
    i.e. C5's hRefl: T_R at v := cNum D, each antecedent cEq (cNum D) (cD) discharged by g7ev_sym g7ev_v_D, then
    g7ev_toimp with the closedness of A' -> B' (per-def g7nfc_ lemmas + nfr_cNum).
and, when A' = cpaThProvable (cg2paAxSet (cNum R)) cpaFormulaFalse and B' = ctmHalts (cNum m) (cNum M),
OUTDIR/gen7/N_hb.mm1 / .mm0 (lowercase: the host HAND pattern):  N_hB: bb215ProvabilityInternalBridge (g2paThCode R) (tmHaltsPA m M)
  = g7_bridge_of_refl_paL REC N_hRefl   (C5's bridge_of_reflection_pa at the literal readings).
  --bridge stub (local): g7_bridge_of_refl_paL is an axiom copied verbatim from pa-mm0/gen7/g7_incH.mm0 (with the TEST
  stand-in defs of d3_s6defs for g2paThCode); --bridge host: imports g7_incH.mm1 (host closure; no stub).
  --rec: proof of paFormulaBound 1 R /\\ paS1Class 1 R (default for R = paFormulaFalse).
"""
import argparse, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
GEN7 = os.path.join(ROOT, "pa-mm0", "gen7")
SPLIT = int(os.environ.get("GEN7_EV_SPLIT", "400"))   # helper lemma per subterm of this many nodes (mm0-rs stack)

# evaluation rule per code constructor: (rule, arity); defs get g7ev_v_<D>
RULE = {"c0": ("g7ev_z", 0), "cSuc": ("g7ev_s", 1), "cAdd": ("g7ev_a", 2), "cMul": ("g7ev_m", 2), "cpr": ("g7ev_p", 2)}
SRC = {"c0": "0", "cSuc": "suc", "cAdd": "add", "cMul": "mul", "cpr": "pr"}


class GenError(Exception):
    pass


def parse(s):
    """Prefix MM0 math (as refl prints it) -> tree: str (atom) | (head, [children])."""
    toks = re.findall(r"\(|\)|[^\s()]+", s)
    if len(toks) > 1 and toks[0] != "(":
        toks = ["("] + toks + [")"]     # a top-level application is printed without parentheses
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t != "(":
            return t
        h = toks[pos]
        pos += 1
        ch = []
        while toks[pos] != ")":
            ch.append(go())
        pos += 1
        return (h, ch)
    e = go()
    if pos != len(toks):
        raise GenError("trailing tokens in %r" % s[:80])
    return e


def pr(e):
    if isinstance(e, str):
        return e
    return "(%s %s)" % (e[0], " ".join(pr(c) for c in e[1])) if e[1] else e[0]


def head(e):
    return e if isinstance(e, str) else e[0]


def args(e):
    return [] if isinstance(e, str) else e[1]


def size(e):
    return 1 + sum(size(c) for c in args(e))


class Ev:
    def __init__(self, perdef_text, spec_text):
        self.defs = {}   # code def name -> (params, body tree)
        for m in re.finditer(r"^(?:@_ )?(?:abstract )?def (c\w+)\s*((?:\([^)]*\)\s*)*):\s*nat\s*=\s*\$(.*?)\$;", perdef_text, re.M | re.S):
            nm, bs, body = m.group(1), m.group(2), m.group(3)
            ps = re.findall(r"\((\.?)(\w+): nat\)", bs)
            self.defs[nm] = ([p for d, p in ps if not d], any(d for d, p in ps), body)
        self.perdef = perdef_text
        self.spec = spec_text
        self.lemmas = {}   # code def -> lemma name
        self.out = []      # mm1 items
        self.out0 = []     # mm0 items
        self.nhelp = 0
        self.cur = "inst"

    # ---- source term of a closed code term (the instance of a code variable) ----
    def src(self, e, env=None):
        h = head(e)
        if env is not None and isinstance(e, str) and e in env:
            return env[e]
        if h in SRC:
            if h == "c0":
                return "0"
            return "(%s %s)" % (SRC[h], " ".join(self.src(c, env) for c in args(e)))
        if h in self.defs:
            nm = h[1:]
            return "(%s %s)" % (nm, " ".join(self.src(c, env) for c in args(e))) if args(e) else nm
        raise GenError("no source reading of %s" % h)

    def closed(self, e, vs):
        return not any(isinstance(x, str) and x in vs for x in self.leaves(e))

    def leaves(self, e):
        if isinstance(e, str):
            yield e
        else:
            for c in e[1]:
                yield from self.leaves(c)

    # ---- evaluation proofs ----
    def proof(self, e, hyp):
        """Proof term of cPr (cEq e (cNum src e)); hyp: code var -> hypothesis name."""
        if isinstance(e, str) and e in hyp:
            return hyp[e]
        h = head(e)
        if h in RULE:
            rule, n = RULE[h]
            if len(args(e)) != n:
                raise GenError("arity of %s" % h)
            ps = [self.proof(c, hyp) for c in args(e)]
            return "(%s %s)" % (rule, " ".join(ps)) if ps else rule
        if h in self.defs:
            lem = self.lemma(h)
            ps = [self.proof(c, hyp) for c in args(e)]
            return "(%s %s)" % (lem, " ".join(ps)) if ps else lem
        raise GenError("cannot evaluate %s (only 0, suc, +, *, pairing and defs over them)" % h)

    def cut(self, e, hyp, env):
        """Abstract large subterms (bottom-up, every SPLIT nodes) into helper lemmas in hypothesis form: a helper's
        statement mentions its cut-out children only as variables, so statement text stays linear in the term size
        (a long cons list is cut into segments). hyp / env (code var -> proof term / source term) are extended with
        the cut variables. Returns the abstracted tree."""
        if isinstance(e, str):
            return e
        y = (e[0], [self.cut(c, hyp, env) for c in e[1]])
        if size(y) < SPLIT:
            return y
        free = []
        for u in self.leaves(y):
            if u in hyp and u not in free:
                free.append(u)
        self.nhelp += 1
        nm = "g7ev_h%d_%s" % (self.nhelp, self.cur)
        loc = {u: "k%d" % i for i, u in enumerate(free)}
        bs = " ".join(free + [loc[u] for u in free])
        hs = "".join(" (h_%s: $ cPr (cEq %s (cNum %s)) $)" % (u, u, loc[u]) for u in free)
        st = "cPr (cEq %s (cNum %s))" % (pr(y), self.src(y, loc))
        p = self.proof(y, {u: "h_" + u for u in free})
        self.out.append("theorem %s%s%s: $ %s $ =\n'%s;\n" % (nm, " (%s: nat)" % bs if bs else "", hs, st, p))
        x = "e%d" % self.nhelp
        hyp[x] = "(%s %s)" % (nm, " ".join(hyp[u] for u in free)) if free else nm
        env[x] = "(%s)" % self.src(y, env)
        return x

    def evaluate(self, e, hyp, env):
        hyp, env = dict(hyp), dict(env)
        return self.proof(self.cut(e, hyp, env), hyp)

    def lemma(self, cd):
        if cd in self.lemmas:
            return self.lemmas[cd]
        if cd not in self.defs:
            raise GenError("no code def %s in perdef" % cd)
        ps, dums, body = self.defs[cd]
        if dums:
            raise GenError("%s has dummies (binders): not a closed-term constructor" % cd)
        t = parse(body)
        nm = "g7ev_v_" + cd[1:]
        outer = getattr(self, "cur", None)
        self.cur = cd[1:]
        hyp = {p: "h%d" % i for i, p in enumerate(ps)}
        p = self.evaluate(t, hyp, {p: "a%d" % i for i, p in enumerate(ps)})   # emits inner defs' lemmas first
        self.cur = outer
        if ps:
            bs = " (%s: nat)" % " ".join(ps + ["a%d" % i for i in range(len(ps))])
            hs = "".join(" (h%d: $ cPr (cEq %s (cNum a%d)) $)" % (i, v, i) for i, v in enumerate(ps))
            st = "cPr (cEq (%s %s) (cNum (%s %s)))" % (cd, " ".join(ps), cd[1:], " ".join("a%d" % i for i in range(len(ps))))
        else:
            bs, hs, st = "", "", "cPr (cEq %s (cNum %s))" % (cd, cd[1:])
        self.out.append("theorem %s%s%s: $ %s $ =\n'%s;\n" % (nm, bs, hs, st, p))
        self.lemmas[cd] = nm
        return nm

    # ---- closedness (nfr x c) of an instantiated code term ----
    def nf(self, e):
        h = head(e)
        if h == "cNum":
            return "nfr_cNum"
        ch = [self.nf(c) for c in args(e)]
        if re.search(r"^theorem g7nfc_%s \(" % re.escape(h), self.perdef, re.M):
            lem = "g7nfc_" + h
        elif re.search(r"^theorem g7nf_%s \(" % re.escape(h), self.gen7_eqv(), re.M):
            lem = "g7nf_" + h
        else:
            raise GenError("no freshness lemma for %s (add nf:%s to GEN7_NEED)" % (h, h))
        p = lem
        for c in ch:
            p = "(ax_mp %s %s)" % (p, c)
        return p

    def gen7_eqv(self):
        if not hasattr(self, "_eqv"):
            self._eqv = open(os.path.join(GEN7, "gen7_eqv.mm0")).read()
        return self._eqv


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("spec"); ap.add_argument("perdef"); ap.add_argument("outdir")
    ap.add_argument("--thm"); ap.add_argument("--name", required=True); ap.add_argument("--src", required=True)
    ap.add_argument("--terms", default="")
    ap.add_argument("--bridge", default="stub", choices=["stub", "host", "none"])
    ap.add_argument("--rec", default=None)
    ns = ap.parse_args()
    spec, perdef = open(ns.spec).read(), open(ns.perdef).read()
    ev = Ev(perdef, spec)
    gd = os.path.join(ns.outdir, "gen7")
    os.makedirs(gd, exist_ok=True)
    srcrel = os.path.relpath(os.path.join(ROOT, "pa-mm0", ns.src), GEN7).replace(os.sep, "/")
    N = ns.name
    hdr = ["import \"g7ev_lib.mm1\";\n", "import \"%s.mm1\";\n" % srcrel,
           "-- G2GEN closed-term evaluation (generated by tools/gen7/c2/gen_closed.py; lanes/G2GEN.md \"CLOSED-TERM EVALUATION\").\n"]
    hdr0 = ["import \"g7ev_lib.mm0\";\n", "import \"%s.mm0\";\n" % srcrel]
    for t in filter(None, ns.terms.split(",")):
        if ev.defs.get("c" + t, ([],))[0]:
            raise GenError("--terms: %s has arguments (its lemma is generated when a closed term uses it)" % t)
        ev.lemma("c" + t)
    inst = None
    if ns.thm:
        st = re.search(r"^theorem %s ((?:\(v\d+: nat\) ?)*)((?:\(h\d+: \$[^$]*\$\) ?)*): \$ cPr (.*) \$;$" % re.escape(ns.thm), spec, re.M)
        if not st:
            raise GenError("reflected statement %s not found in %s" % (ns.thm, ns.spec))
        if st.group(2).strip():
            raise GenError("%s has side hypotheses (bound names in the source statement): not supported" % ns.thm)
        vs = re.findall(r"\(v(\d+): nat\)", st.group(1))
        vs = ["v" + v for v in vs]
        e = parse(st.group(3))
        val, steps = {}, []
        while head(e) == "cIm" and head(args(e)[0]) == "cEq":
            l, r = args(args(e)[0])
            if isinstance(l, str) and l in vs and l not in val and ev.closed(r, vs):
                val[l] = ev.src(r); steps.append("(g7ev_sym %s)" % ev.evaluate(r, {}, {}))
            elif isinstance(r, str) and r in vs and r not in val and ev.closed(l, vs):
                val[r] = ev.src(l); steps.append(ev.evaluate(l, {}, {}))
            else:
                break
            e = args(e)[1]
        miss = [v for v in vs if v not in val]
        if miss:
            raise GenError("code variables without an equation antecedent: %s" % miss)
        if head(e) != "cIm":
            raise GenError("conclusion after the equations is not an implication")

        def subst(x):
            if isinstance(x, str):
                return ("cNum", [val[x]]) if x in val else x
            return (x[0], [subst(c) for c in x[1]])
        A, B = (subst(c) for c in args(e))
        p = "(! %s %s)" % (ns.thm, " ".join("(cNum %s)" % val[v] for v in vs))
        for s in steps:
            p = "(ax_mp_R %s %s)" % (p, s)
        nfp = ev.nf(("cIm", [A, B]))
        stub = re.search(r"^theorem %s .*$" % re.escape(ns.thm), spec, re.M).group(0)
        concl = "paProvable 0 (paFormulaImp (trJ (trPA %s)) (trJ (trPA %s)))" % (pr(A), pr(B))
        inst = (stub, concl, "(named '(g7ev_toimp %s %s))" % (nfp, p), A, B)
    items = list(hdr)
    if inst:
        items.append("-- the reflected Theorem-1 input (stub, VERBATIM from the reflection; resolved by link.py)\naxiom %s\n"
                     % inst[0][len("theorem "):])
    items.append("-- evaluation lemmas: one per def of the closed terms' code closure\n")
    items += ev.out
    items0 = list(hdr0)
    for t in filter(None, ns.terms.split(",")):
        items.append("pub theorem %s_%s: $ cPr (cEq c%s (cNum %s)) $ = '%s;\n" % (N, t, t, t, ev.lemmas["c" + t]))
        items0.append("theorem %s_%s: $ cPr (cEq c%s (cNum %s)) $;\n" % (N, t, t, t))
    if inst:
        items.append("-- C5's hRefl for this instance\npub theorem %s_hRefl: $ %s $ =\n%s;\n" % (N, inst[1], inst[2]))
        items0.insert(2, "axiom %s\n" % inst[0][len("theorem "):])
        items0.append("theorem %s_hRefl: $ %s $;\n" % (N, inst[1]))
    open(os.path.join(gd, N + "_ev.mm1"), "w", newline="\n").write("\n".join(items))
    open(os.path.join(gd, N + "_ev.mm0"), "w", newline="\n").write("\n".join(items0))
    print("%s_ev: %d evaluation lemmas (%d helpers)%s" % (N, len(ev.lemmas), ev.nhelp, ", hRefl" if inst else ""))
    if not inst or ns.bridge == "none":
        return
    A, B = inst[3], inst[4]
    mA = re.fullmatch(r"\(cpaThProvable \(cg2paAxSet \(cNum (.*)\)\) cpaFormulaFalse\)", pr(A))
    mB = re.fullmatch(r"\(ctmHalts \(cNum (.*)\) \(cNum (.*)\)\)", pr(B))
    if not (mA and mB):
        print("conclusion is not the PA bridge's hRefl shape: no hB module")
        return
    R, m, M = mA.group(1), mB.group(1), mB.group(2)
    rec = ns.rec or ("(iani paFormulaBound_false paS1Class_false)" if R == "paFormulaFalse" else None)
    if rec is None:
        raise GenError("--rec needed for R = %s" % R)
    hB = "bb215ProvabilityInternalBridge (g2paThCode %s) (tmHaltsPA %s %s)" % (R, m, M)
    b = ["import \"%s_ev.mm1\";\n" % N]
    b0 = ["import \"%s_ev.mm0\";\n" % N]
    if ns.bridge == "host":
        b.append("import \"g7_incH.mm1\";\n")
        b0.append("import \"g7_incH.mm0\";\n")
    else:
        inc = open(os.path.join(GEN7, "g7_incH.mm0")).read()
        i = inc.index("theorem g7_bridge_of_refl_paL ")
        br = inc[i:inc.index("$;", inc.index("$ bb215", i)) + 2]
        imps = ["../bb215_provability_halting_refutation", "../g2_generic_tm_defs", "d3_s6defs"]
        b += ["import \"%s.mm1\";\n" % x for x in imps]
        b0 += ["import \"%s.mm0\";\n" % x for x in imps]
        b.append("-- TEST ONLY (local): C5's bridge (proved in g7_incH, host; local staged check g7_incTpa), statement VERBATIM from\n"
                 "-- pa-mm0/gen7/g7_incH.mm0; g2paThCode from the TEST stand-in d3_s6defs (GEN3's body).\naxiom %s\n" % br[len("theorem "):])
        b0.append("axiom %s\n" % br[len("theorem "):])
    b.append("-- hB of the spec for this machine (bridge_of_reflection_pa at the literal readings)\n"
             "pub theorem %s_hB: $ %s $ =\n'(g7_bridge_of_refl_paL %s %s_hRefl);\n" % (N, hB, rec, N))
    b0.append("theorem %s_hB: $ %s $;\n" % (N, hB))
    open(os.path.join(gd, N + "_hb.mm1"), "w", newline="\n").write("\n".join(b))
    open(os.path.join(gd, N + "_hb.mm0"), "w", newline="\n").write("\n".join(b0))
    print("%s_hB: %s (bridge %s)" % (N, hB, ns.bridge))


if __name__ == "__main__":
    try:
        main()
    except GenError as ex:
        sys.exit("gen_closed: " + str(ex))
