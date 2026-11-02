"""B5: Pi2 recovery over hpeano (generator + driver).

  python3 b5/gen_b5.py            # from the repo root: generate, compile, translate, check

Steps
 1. b5/b5-src.mm1  = peano.mm1 + the approved bd defs (b4/bd_certs.mm0) + small
    test defs/theorems (peano side); compiled to build/b5-src.mmb.
 2. Pass A: translate it with the spike library to read off the translated defs
    (or_N, le_N, lt_N, d1_N..d10_N, bd*_N, t*_N) exactly as the translator makes them.
 3. b5/b5-lib.mm1 = hpeano + the bd defs read over hpeano (verbatim text) + the
    spike graph library + those translated defs (the translator checks their
    bodies) + b5/hand.mm1t (schemas: decidable equality, bounded quantifiers,
    rel/dec closure) + per-def lemmas generated from the def bodies
    (isv_D for nat defs; rel_D, dec_D for wff defs) + recovery lemmas.
 4. Pass B: translate b5-src.mmb against b5-lib.mmb; append the recovered HA
    theorems (post-step: recovery lemma applied to the translated theorem);
    write build/b5-out.mmb + build/b5-out.mm0 and run tools/mm0-c.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, "spike"))
from lamc import compile_lam  # noqa: E402

B5 = os.path.join(ROOT, "b5")
BUILD = os.path.join(ROOT, "build")
# where write_src / write_lib put the generated .mm1 files: b5/ for the B4 set (the committed
# b5-src.mm1 / b5-lib.mm1); build/b5b/b5 for the B4b set (--b4b), next to a foundation/ copy
WDIR = B5
TOOLS = os.path.join(ROOT, "tools")

# test defs: same text on both sides (peano src uses @_ for congruence lemmas)
TEST_DEFS = r'''
--| B5 test defs (Delta0).
def tTriv (n: nat): wff = $ n <= n $;
def tGt (n m: nat): wff = $ n < m $;
def tEv (n .k: nat): wff = $ E. k (k <= n /\ k + k = n) $;
def tAll (n .k: nat): wff = $ A. k (k < n -> suc k != 0) $;
'''

TEST_THMS = r'''
--| B5 synthetic Pi2 tests, proved in peano.
theorem tsig1 {h w: nat}: $ A. h (tAll h -> E. w tEv w) $ =
  '(ax_gen @ a1i @ iexe {,eqtac : $ w = 0 -> (tEv w <-> tEv 0) $} @
    iexe {,eqtac : $ k = 0 -> (k <= 0 /\ k + k = 0 <-> 0 <= 0 /\ 0 + 0 = 0) $} @ ian le01 add0);
theorem tsig2 (h: nat) {w: nat}: $ tTriv h -> E. w tGt h w $ =
  '(a1i @ iexe {,eqtac : $ w = suc h -> (tGt h w <-> tGt h (suc h)) $} ltsucid);
--| The shapes of K215_sigma1 / K215_sigma2 (B4, approved), with the statement
--| as a hypothesis: the translation gives the translated statement.
theorem s1hyp {h w: nat} (H: $ A. h (bdK215Halt h -> E. w bdZfcBot w) $):
  $ A. h (bdK215Halt h -> E. w bdZfcBot w) $ = 'H;
theorem s2hyp {w h: nat} (H: $ A. w (bdZfcBot w -> E. h bdK215Halt h) $):
  $ A. w (bdZfcBot w -> E. h bdK215Halt h) $ = 'H;
'''

# B4b (approved, b4/b4b_statements.mm0): the five Pi2 shapes of K215 Theorems 2/3 and G2,
# with the statement as a hypothesis (only with --b4b; appended to TEST_THMS).
B4B_THMS = r'''
--| B4b shapes (b4/b4b_statements.mm0), statement as hypothesis.
theorem t2ahyp {u w: nat} (H: $ A. u (bdBB215Prf u -> E. w bdZfcBot w) $):
  $ A. u (bdBB215Prf u -> E. w bdZfcBot w) $ = 'H;
theorem t2bhyp {w u: nat} (H: $ A. w (bdZfcBot w -> E. u bdBB215Prf u) $):
  $ A. w (bdZfcBot w -> E. u bdBB215Prf u) $ = 'H;
theorem t3ahyp {h u: nat} (H: $ A. h (bdK215Halt h -> E. u bdBB215Prf u) $):
  $ A. h (bdK215Halt h -> E. u bdBB215Prf u) $ = 'H;
theorem t3bhyp {u h: nat} (H: $ A. u (bdBB215Prf u -> E. h bdK215Halt h) $):
  $ A. u (bdBB215Prf u -> E. h bdK215Halt h) $ = 'H;
theorem g2hyp {u w: nat} (H: $ A. u (bdZfcConPrf u -> E. w bdZfcBot w) $):
  $ A. u (bdZfcConPrf u -> E. w bdZfcBot w) $ = 'H;
'''
RECS_B4B = [
    ("K215_thm2_pi2a", "closedhyp", "t2ahyp", "bdBB215Prf", "bdZfcBot"),
    ("K215_thm2_pi2b", "closedhyp", "t2bhyp", "bdZfcBot", "bdBB215Prf"),
    ("K215_thm3_pi2a", "closedhyp", "t3ahyp", "bdK215Halt", "bdBB215Prf"),
    ("K215_thm3_pi2b", "closedhyp", "t3bhyp", "bdBB215Prf", "bdK215Halt"),
    ("K215_G2_pi2", "closedhyp", "g2hyp", "bdZfcConPrf", "bdZfcBot"),
]

# recovery targets: (name, kind, src theorem, D, D')
#   closed: A. h (D h -> E. w D' w)           (D' does not mention h)
#   open:   D h -> E. w D' h w  (h regular)    recovered as A. h (D h -> E. w D' h w)
RECS = [
    ("tsig1", "closed", "tsig1", "tAll", "tEv"),
    ("tsig2", "open", "tsig2", "tTriv", "tGt"),
    ("K215_sigma1", "closedhyp", "s1hyp", "bdK215Halt", "bdZfcBot"),
    ("K215_sigma2", "closedhyp", "s2hyp", "bdZfcBot", "bdK215Halt"),
]


def run(*cmd, stdin=None, quiet=False):
    with open(stdin, "rb") if stdin else open(os.devnull, "rb") as f:
        r = subprocess.run(cmd, stdin=f, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=ROOT)
    out = r.stdout.decode(errors="replace")
    if r.returncode and not quiet:
        print(out[-6000:])
    return r.returncode, out


def expand(text):
    """L{..} (whole proof) and @L{..} (inline), nested, innermost first."""
    while True:
        m = None
        for mm in re.finditer(r"@?L\{", text):
            # find innermost: a block with no L{ inside
            i = mm.end()
            d = 1
            j = i
            while d:
                c = text[j]
                d += {"{": 1, "}": -1}.get(c, 0)
                j += 1
            inner = text[i:j - 1]
            if not re.search(r"@?L\{", inner):
                m = (mm.start(), j, mm.group(0).startswith("@"), inner)
                break
        if m is None:
            return text
        s, e, inline, inner = m
        comp = compile_lam(inner)
        text = text[:s] + (comp if inline else "'" + comp) + text[e:]


# the approved bd-def files read by bd_body(), in order, with the import line each one starts
# with (dropped); "b4" = Theorem 1 (B4), "b4b" = + Theorems 2/3 and G2 (B4b, 3,217 more defs)
BD_SETS = {
    "b4": [("bd_certs.mm0", 'import "../foundation/peano.mm0";')],
    "b4b": [("bd_certs.mm0", 'import "../foundation/peano.mm0";'),
            ("bd_certs_b4b.mm0", 'import "bd_certs.mm0";')],
}
BD_SET = "b4"


def bd_body(which=None):
    out = []
    for f, imp in BD_SETS[which or BD_SET]:
        t = open(os.path.join(ROOT, "b4", f), newline="").read().replace("\r\n", "\n")
        head, sep, body = t.partition(imp)
        if not sep:
            raise SystemExit("gen_b5: %s does not contain %r" % (f, imp))
        out.append(body)
    return "".join(out)


def spike_lib_body():
    t = open(os.path.join(ROOT, "spike", "negtrans-lib.mm1")).read()
    return t.split('import "../foundation/hpeano.mm0";', 1)[1]


def write_src():
    src = ('-- b5-src.mm1 -- GENERATED by b5/gen_b5.py: peano + B4 bd defs + B5 tests (peano side).\n'
           'import "../foundation/peano.mm1";\n' + bd_body() +
           TEST_DEFS.replace("\ndef ", "\n@_ def ") + TEST_THMS + (B4B_THMS if BD_SET == "b4b" else ""))
    p = os.path.join(WDIR, "b5-src.mm1")
    open(p, "w").write(src)
    return p


def compile_mm1(path, out):
    rc, log = run(os.path.join(TOOLS, "mm0-rs"), "compile", path, out)
    bad = [l for l in log.splitlines() if "error" in l or "sorry" in l]
    if rc or bad:
        print(log[-12000:])
        raise SystemExit("compile failed: " + path)
    return log


SUPPORT = ["or", "le", "lt"] + ["d%d" % i for i in range(1, 11)]


def def_names(text):
    return re.findall(r"^\s*(?:@_ )?def (\w+)", text, re.M)


def pass_a(src_mmb):
    """Translated def texts (as `local def`) for the support, bd and test defs."""
    from translator.mmb_reader import read_mmb
    from translator.negtrans import NegTrans
    lib = os.path.join(BUILD, "negtrans-lib.mmb")
    compile_mm1(os.path.join(ROOT, "spike", "negtrans-lib.mm1"), lib)
    src = read_mmb(src_mmb)
    tr = NegTrans(src, read_mmb(lib))
    tr.run()
    want = set(SUPPORT) | set(def_names(bd_body())) | set(def_names(TEST_DEFS))
    out = []
    for t in src.terms:
        if t.name in want:
            d = tr.terms[tr.tname[t.name + "_N"]]
            out.append("local " + tr.print_decl(d, True))
    return src, out


def write_lib(tdefs, gen_text, rec_text):
    hand = expand(open(os.path.join(B5, "hand.mm1t")).read())
    lib = ('-- b5-lib.mm1 -- GENERATED by b5/gen_b5.py; do not edit.\n'
           '-- hpeano + B4 bd defs (hpeano reading) + spike graph library + translated defs\n'
           '-- + B5 recovery schemas (b5/hand.mm1t) + generated per-def lemmas + recovery lemmas.\n'
           'import "../foundation/hpeano.mm0";\n' + bd_body() + TEST_DEFS +
           "\n-- ===== spike graph library (spike/negtrans-lib.mm1) =====\n" + spike_lib_body() +
           "\n-- ===== translated defs (exactly as translator.negtrans makes them) =====\n" +
           "\n".join(tdefs) + "\n\n" + hand + "\n" + gen_text + "\n" + rec_text)
    p = os.path.join(WDIR, "b5-lib.mm1")
    open(p, "w").write(lib)
    return p


# ---------------------------------------------------------------------------
# per-def lemmas, generated from the (peano-side) def bodies
# ---------------------------------------------------------------------------
CONN = {"im", "not", "an", "or", "iff", "ex", "al", "eq", "le", "lt"}
NATOPS = {"suc": "isv_suc", "add": "isv_add", "mul": "isv_mul"}


class Gen:
    def __init__(self, src):
        from translator.proof_dag import decode_unify
        self.src = src
        self.decode = decode_unify
        self.done = {}          # def name -> 'wff' | 'nat'

    def name(self, tid):
        return self.src.terms[tid].name

    def T(self, nodes, n, ctx):
        """proof of `isv t^G t A`"""
        nd = nodes[n]
        if nd[0] == "var":
            return "h%d" % nd[1]
        if nd[0] == "dummy":
            return "isv_sg"
        f = self.name(nd[1])
        args = nd[2]
        if f == "d0":
            return "isv_sg"
        if f in NATOPS:
            return "(%s %s)" % (NATOPS[f], " ".join(self.T(nodes, a, ctx) for a in args))
        assert self.done.get(f) == "nat", f
        if not args:
            return "isv_" + f
        return "(isv_%s %s)" % (f, " ".join(self.T(nodes, a, ctx) for a in args))

    def bvar(self, n, ctx):
        if n not in ctx:
            ctx[n] = "y%d" % len(ctx)
        return ctx[n]

    def bound_of(self, nodes, body, x):
        """leftmost atom of an /\\-spine: (kind, t-node, depth) if it is x <= t / x < t"""
        d = 0
        n = body
        while nodes[n][0] == "app" and self.name(nodes[n][1]) == "an":
            n = nodes[n][2][0]
            d += 1
        nd = nodes[n]
        if nd[0] == "app" and self.name(nd[1]) in ("le", "lt") and nd[2][0] == x:
            return self.name(nd[1]), nd[2][1], d
        raise ValueError("unbounded E.")

    def R(self, nodes, n, ctx):
        """proof of `rel p p^N A`"""
        nd = nodes[n]
        f = self.name(nd[1])
        a = nd[2]
        if f == "eq":
            return "(rel_eq %s %s)" % (self.T(nodes, a[0], ctx), self.T(nodes, a[1], ctx))
        if f in ("le", "lt"):
            return "(rel_%s %s %s)" % (f, self.T(nodes, a[0], ctx), self.T(nodes, a[1], ctx))
        if f == "not":
            return "(rel_not %s %s)" % (self.R(nodes, a[0], ctx), self.D(nodes, a[0], ctx))
        if f == "im":
            return "(rel_im %s %s %s)" % (self.R(nodes, a[0], ctx), self.R(nodes, a[1], ctx), self.D(nodes, a[0], ctx))
        if f == "an":
            return "(rel_an %s %s %s %s)" % (self.R(nodes, a[0], ctx), self.R(nodes, a[1], ctx),
                                             self.D(nodes, a[0], ctx), self.D(nodes, a[1], ctx))
        if f == "or":
            return "(rel_or %s %s %s)" % (self.R(nodes, a[0], ctx), self.R(nodes, a[1], ctx), self.D(nodes, a[0], ctx))
        if f == "iff":
            rp, rq = self.R(nodes, a[0], ctx), self.R(nodes, a[1], ctx)
            dp, dq = self.D(nodes, a[0], ctx), self.D(nodes, a[1], ctx)
            return "(rel_an (rel_im %s %s %s) (rel_im %s %s %s) (dec_im %s %s) (dec_im %s %s))" % (
                rp, rq, dp, rq, rp, dq, dp, dq, dq, dp)
        if f == "ex":
            x = self.bvar(a[0], ctx)
            return "(!! rel_ex %s %s %s)" % (x, self.R(nodes, a[1], ctx), self.D(nodes, n, ctx))
        if f == "al":
            x = self.bvar(a[0], ctx)
            k, t, body = self.al_shape(nodes, a)
            return "(!! rel_al_%s %s %s %s %s)" % (k, x, self.T(nodes, t, ctx), self.R(nodes, body, ctx),
                                                  self.D(nodes, body, ctx))
        assert self.done.get(f) == "wff", f
        return "(rel_%s %s)" % (f, " ".join(self.T(nodes, x, ctx) for x in a))

    def al_shape(self, nodes, a):
        im = nodes[a[1]]
        assert im[0] == "app" and self.name(im[1]) == "im"
        at = nodes[im[2][0]]
        assert at[0] == "app" and self.name(at[1]) in ("le", "lt") and at[2][0] == a[0], "unbounded A."
        return self.name(at[1]), at[2][1], im[2][1]

    def D(self, nodes, n, ctx):
        """proof of `dec p`"""
        nd = nodes[n]
        f = self.name(nd[1])
        a = nd[2]
        if f == "eq":
            return "deceq"
        if f in ("le", "lt"):
            return "dec_" + f
        if f == "not":
            return "(dec_not %s)" % self.D(nodes, a[0], ctx)
        if f in ("im", "an", "or"):
            return "(dec_%s %s %s)" % (f, self.D(nodes, a[0], ctx), self.D(nodes, a[1], ctx))
        if f == "iff":
            dp, dq = self.D(nodes, a[0], ctx), self.D(nodes, a[1], ctx)
            return "(dec_an (dec_im %s %s) (dec_im %s %s))" % (dp, dq, dq, dp)
        if f == "ex":
            x = self.bvar(a[0], ctx)
            k, t, d = self.bound_of(nodes, a[1], a[0])
            hb = "id"
            for _ in range(d):
                hb = "anl" if hb == "id" else "(syl %s anl)" % hb
            return "(!! dec_ex_%s %s %s %s)" % (k, x, hb, self.D(nodes, a[1], ctx))
        if f == "al":
            x = self.bvar(a[0], ctx)
            k, t, body = self.al_shape(nodes, a)
            return "(!! dec_al_%s %s %s)" % (k, x, self.D(nodes, body, ctx))
        assert self.done.get(f) == "wff", f
        return "dec_" + f

    def lemmas(self, t):
        nodes, root, _ = self.decode(self.src, t)
        n = sum(1 for w in t.args if True)
        from translator.mmb_format import type_bound
        assert not any(type_bound(w) for w in t.args)
        avs = " ".join("a%d" % i for i in range(n))
        xvs = " ".join("X%d" % i for i in range(n))
        binders = ("(%s: nat) (%s: set) " % (avs, xvs) if n else "") + "(A: wff)"
        hyps = "".join(" (h%d: $ isv X%d a%d A $)" % (i, i, i) for i in range(n))
        app = "(%s %s)" % (t.name, avs) if n else t.name
        appN = "(%s_N %s A)" % (t.name, xvs) if n else "(%s_N A)" % t.name
        ctx = {}
        if t.sort == 1:     # nat
            self.done[t.name] = "nat"
            return "theorem isv_%s %s%s: $ isv %s %s A $ =\n  '%s;\n" % (
                t.name, binders, hyps, appN, app, self.T(nodes, root, ctx))
        assert t.sort == 0
        r = self.R(nodes, root, ctx)
        ctx = {}
        d = self.D(nodes, root, ctx)
        self.done[t.name] = "wff"
        out = "theorem rel_%s %s%s: $ rel %s %s A $ =\n  '%s;\n" % (t.name, binders, hyps, app, appN, r)
        out += "theorem dec_%s%s: $ dec %s $ =\n  '%s;\n" % (
            t.name, (" (%s: nat)" % avs) if n else "", app, d)
        return out

    def run(self, names):
        out = ["-- ===== generated per-def lemmas (isv_D / rel_D / dec_D) ====="]
        for t in self.src.terms:
            if t.name in names:
                out.append(self.lemmas(t))
        return "\n".join(out)


# ---------------------------------------------------------------------------
# recovery lemmas (lib side) and the post-step (output side)
# ---------------------------------------------------------------------------
HB = "(isvI ns_sg (ax_mp eqGsg2 @L{(\\ k (\\ e (k e e)))}))"


def rec_text():
    out = ["-- ===== B5 Pi2 recovery lemmas =====",
           "--| renaming lemmas: two instances of rel_D with A := (a = b -> D b)"]
    done = set()
    for name, kind, _, D, E in RECS:
        A = "(E. w %s w)" % E if kind != "open" else "(E. w %s h w)" % E
        if kind != "open" and E not in done:
            done.add(E)
            out.append("theorem ren_%s (a b: nat): $ a = b -> %s a -> %s b $ =\n"
                       "  L{(\\ e (\\ d ([ore] (\\ y y) (\\ f (f e)) ([relB (rel_%s %s)] ([relFp (rel_%s isv_sg)] d)))))};"
                       % (E, E, E, E, HB, E))
        if kind == "open" and E not in done:
            done.add(E)
            out.append("theorem ren2_%s (c a b: nat): $ a = b -> %s c a -> %s c b $ =\n"
                       "  L{(\\ e (\\ d ([ore] (\\ y y) (\\ f (f e)) ([relB (rel_%s isv_sg %s)] ([relFp (rel_%s isv_sg isv_sg)] d)))))};"
                       % (E, E, E, E, HB, E))
        if kind != "open":
            key = ("[ax_gen @L{(\\ u ([ore] (\\ y ([!! exit w @L{(\\ e ([ren_%s] ([eqcom] e)))}] y)) (\\ a a) "
                   "([relB (rel_%s isv_sg)] u)))}]" % (E, E))
            out.append(
                "--| %s: the Friedman translation of A. h (%s h -> E. w %s w) at A := E. w %s w\n"
                "--| gives the statement itself (decisions of the Delta0 matrices).\n"
                "theorem rec_%s {h w w1: nat}\n"
                "  (hT: $ A. h (%s_N (sg h) %s -> ex_N w1 (%s_N (sg w1) %s) %s) $):\n"
                "  $ A. h (%s h -> E. w %s w) $ =\n"
                "  '(ax_mp (alim @L{(\\ f (\\ d ((f ([relFp (rel_%s isv_sg)] d)) %s)))}) hT);"
                % (name, D, E, E, name, D, A, E, A, A, D, E, D, key))
        else:
            key = ("[ax_gen @L{(\\ u ([ore] (\\ y ([!! exit w @L{(\\ e ([ren2_%s] ([eqcom] e)))}] y)) (\\ a a) "
                   "([relB (rel_%s isv_sg isv_sg)] u)))}]" % (E, E))
            out.append(
                "--| %s (dependent matrix): D h -> E. w D' h w from its translation at A := E. w D' h w.\n"
                "theorem rec_%s {h w w1: nat}\n"
                "  (hT: $ %s_N (sg h) %s -> ex_N w1 (%s_N (sg h) (sg w1) %s) %s $):\n"
                "  $ %s h -> E. w %s h w $ =\n"
                "  L{(\\ d (hT ([relFp (rel_%s isv_sg)] d) %s))};"
                % (name, name, D, A, E, A, A, D, E, D, key))
    return "\n".join(out) + "\n"


def post_step(tr):
    """Append the recovered HA theorems: rec_X applied to the translated theorem."""
    from translator.negtrans import Ctx
    from translator.mmb_format import type_word
    from translator.proof_dag import decode_unify
    NAT, WFF = 1, 0

    class M:
        terms = tr.terms

    def inst(cx, thm, args):
        nodes, root, hyps = decode_unify(M, thm)
        memo = {}

        def go(n):
            if n in memo:
                return memo[n]
            nd = nodes[n]
            if nd[0] == "var":
                r = args[nd[1]]
            elif nd[0] == "app":
                r = cx.mk("app", nd[1], tuple(go(a) for a in nd[2]))
            else:
                raise ValueError("dummy in statement")
            memo[n] = r
            return r
        return go(root), [go(h) for h in hyps]

    def T(cx, name, *args):
        return cx.mk("app", tr.tname[name], tuple(args))

    def thm(cx, name_or_id, args, hyps):
        tid = tr.hname[name_or_id] if isinstance(name_or_id, str) else name_or_id
        concl, _ = inst(cx, tr.thms[tid], args)
        return cx.mk("thm", tid, tuple(args), tuple(hyps), concl), concl

    sid = {t.name: t.id for t in tr.src.thms}
    new = []
    for name, kind, srcthm, D, E in RECS:
        cx = Ctx()
        oid, needed = tr.hmap[sid[srcthm]]
        h, w = cx.mk("var", 0), cx.mk("var", 1)
        if kind == "closedhyp":
            w1 = cx.mk("var", 2)
            nargs = 3
        else:
            w1 = cx.mk("dummy", NAT, 0)
            nargs = 2
        Ew = T(cx, "ex", w, T(cx, E, w) if kind != "open" else T(cx, E, h, w))
        if kind in ("closed", "closedhyp"):
            assert not needed
            srcargs = (h, w1, Ew)
            hyps = []
            sub = []
            if kind == "closedhyp":
                _, [H] = inst(cx, tr.thms[oid], srcargs)
                hyps = [H]
                sub = [cx.mk("hyp", 0)]
            pT, _ = thm(cx, oid, srcargs, sub)
            root, concl = thm(cx, "rec_" + name, (h, w, w1), [pT])
        else:
            sgh = T(cx, "sg", h)
            srcargs = (sgh, w1, Ew)
            sides = [thm(cx, "ns_sg", (h, Ew), [])[0] for _ in needed]
            pT, _ = thm(cx, oid, srcargs, sides)
            pR, phi = thm(cx, "rec_" + name, (h, w, w1), [pT])
            root, concl = thm(cx, "ax_gen", (h, phi), [pR])
            hyps = []
        args = [type_word(True, NAT, 1 << i) for i in range(nargs)]
        nid, _ = tr.add_thm(name + "_H" if kind != "closedhyp" else name + "_H", args, cx, concl, hyps, root, nargs)
        new.append(nid)
    return new


def main(argv=None):
    """--b4b: the B4b set (bd_certs.mm0 + bd_certs_b4b.mm0, and the five B4b shapes as
    closedhyp targets), generated under build/b5b (b5/*.mm1 untouched)."""
    global BD_SET, WDIR, BUILD, RECS
    import shutil
    from translator.mmb_reader import read_mmb
    from translator.negtrans import NegTrans
    argv = sys.argv[1:] if argv is None else argv
    if "--b4b" in argv:
        BD_SET, RECS = "b4b", RECS + [r for r in RECS_B4B if r not in RECS]
        BUILD = os.path.join(ROOT, "build", "b5b")
        WDIR = os.path.join(BUILD, "b5")
        os.makedirs(WDIR, exist_ok=True)
        os.makedirs(os.path.join(BUILD, "foundation"), exist_ok=True)
        for f in ("peano.mm1", "peano.mm0", "hpeano.mm0"):
            shutil.copyfile(os.path.join(ROOT, "foundation", f), os.path.join(BUILD, "foundation", f))
    os.makedirs(BUILD, exist_ok=True)
    srcp = write_src()
    src_mmb = os.path.join(BUILD, "b5-src.mmb")
    compile_mm1(srcp, src_mmb)
    src, tdefs = pass_a(src_mmb)
    names = ["d%d" % i for i in range(1, 11)] + ["ne"] + def_names(bd_body()) + def_names(TEST_DEFS)
    gtext = Gen(src).run(set(names))
    libp = write_lib(tdefs, gtext, expand(rec_text()))
    lib_mmb = os.path.join(BUILD, "b5-lib.mmb")
    compile_mm1(libp, lib_mmb)
    spec0 = open(os.path.join(ROOT, "foundation", "hpeano.mm0")).read() + bd_body() + TEST_DEFS
    lspec = os.path.join(BUILD, "b5-lib.spec.mm0")
    open(lspec, "w").write(spec0)
    rc, _ = run(os.path.join(TOOLS, "mm0-c"), lib_mmb, stdin=lspec)
    print("mm0-c b5-lib.mmb:", rc)
    tr = NegTrans(src, read_mmb(lib_mmb))
    tr.run()
    fails = [k for k in tr.why if k[0] == "thm" and tr.src.thms[k[1]].kind != "axiom"]
    print("translated %d theorems, %d defs; failures %d" % (tr.stats["thms"], tr.stats["defs"], len(fails)))
    new = post_step(tr)
    out, spec = os.path.join(BUILD, "b5-out.mmb"), os.path.join(BUILD, "b5-out.mm0")
    tr.write(out, spec, spec0, False, extra_pub=new)
    rc2, log = run(os.path.join(TOOLS, "mm0-c"), out, stdin=spec)
    print("mm0-c b5-out.mmb:", rc2)
    for i in new:
        print(tr.print_decl(tr.thms[i], False)[:300])
    return rc or rc2


if __name__ == "__main__":
    sys.exit(main())
