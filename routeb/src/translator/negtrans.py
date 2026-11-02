"""Combined negative + Friedman translation of peano-based .mmb files into the
hpeano foundation, with nat terms translated to GRAPHS (sets), which removes
the description operator `the`.

  python3 -m translator.negtrans SRC.mmb LIB.mmb OUT.mmb [--max N] [--mm0 OUT.mm0]

LIB.mmb is a compiled HA-side library over hpeano.mm0 (spike/negtrans-lib.mm1,
or the B5/B6 library that extends it). The output is LIB followed by one
translated def per source def and one translated theorem per source theorem
(each translated ONCE, schematically). A = Friedman formula, appended as the
LAST argument of every translated def/theorem (plain Goedel-Gentzen: A := F.).

  sorts     a regular nat variable becomes a set variable (its graph); bound
            nat variables stay nat
  nat terms x |-> sg x (x bound or dummy), 0 |-> sg 0, suc/+/*/the |->
            sucG/addG/mulG/theG (.., A), nat-valued def D |-> D_N (.., A)
  formulas  im, al, ab, tru unchanged; ~p |-> ng p^ A; a = b |-> eqG a^ b^ A;
            a e. S |-> elG a^ S^ A; def D |-> D_N (args.., A) := body^
            (the lib may supply D_N itself; its body is checked)
  proofs    hyp |-> hyp; axiom ax |-> lib lemma axN; thm T |-> T_N;
            conversions map 1-1 (Cong/Unfold through the templates).
            Side proofs for each callee argument that needs one:
            wff p: stability `dn p^ A -> p^` (st_ng/st_dn/st_im/st_al/st_tru,
            lib st_eqG/st_elG, generated st_D_N); nat a: `nsing a^ A` (ns_sg,
            ns_suc/ns_add/ns_mul, ns_the, generated ns_D_N); the theorem's
            own variables become hypotheses only when actually needed.
Every output is meant to be checked: tools/mm0-c OUT.mmb < SPEC (--mm0).

Scale notes (B6): every traversal is iterative (no Python recursion, so the
depth of real proofs/expressions is unbounded); with `stream_to` the output
statements go straight to the writer's spool file instead of memory; each
emitted statement is checked against mm0-c's fixed per-statement capacities
(LIMITS) and refused with a clear reason instead of failing late in mm0-c.
"""

import struct
import sys

from .mmb_format import (
    MMBError, STMT_LOCAL_DEF, STMT_LOCAL_THM, STMT_DEF, STMT_THM,
    PROOF_TERM, PROOF_TERM_SAVE, PROOF_REF, PROOF_DUMMY, PROOF_THM,
    PROOF_THM_SAVE, PROOF_HYP, PROOF_CONV, PROOF_REFL, PROOF_SYMM, PROOF_CONG,
    PROOF_UNFOLD, PROOF_SAVE, UNIFY_TERM, UNIFY_TERM_SAVE, UNIFY_REF, UNIFY_DUMMY,
    UNIFY_HYP, type_word, type_bound, type_sort, type_deps, encode_cmds,
)
from .mmb_reader import read_mmb, Term, Thm
from .mmb_writer import MMBWriter
from .proof_dag import build_stmt_dag, decode_unify

SAME_TERMS = {"im", "al", "ab", "tru"}
GTERMS = {"not": "ng", "eq": "eqG", "el": "elG", "suc": "sucG", "add": "addG",
          "mul": "mulG", "the": "theG"}       # peano term -> lib def (A appended)
AXIOMS = {  # peano axiom -> (lib lemma, src-arg indices that need a side hypothesis)
    "ax_1": ("ax_1N", []), "ax_2": ("ax_2N", []), "ax_3": ("ax_3N", [0]),
    "ax_mp": ("ax_mpN", []), "itru": ("itruN", []), "ax_gen": ("ax_genN", []),
    "ax_4": ("ax_4N", []), "ax_5": ("ax_5N", []), "ax_6": ("ax_6N", [0]),
    "ax_7": ("ax_7N", [0]), "ax_10": ("ax_10N", []), "ax_11": ("ax_11N", []),
    "ax_12": ("ax_12N", [1, 2]), "ax_8": ("ax_8N", [0]),
    "addeq": ("addeqN", [0, 1, 2, 3]), "muleq": ("muleqN", [0, 1, 2, 3]),
    "add0": ("add0N", []), "addS": ("addSN", [0, 1]), "mul0": ("mul0N", [0]),
    "mulS": ("mulSN", [0, 1]), "peano1": ("peano1N", [0]), "peano2": ("peano2N", [0, 1]),
    "elab": ("elabN", [0, 2]), "peano5": ("peano5N", []),
    "theid": ("theidN", [2]), "the0": ("the0N", []),
}
LIB_ST = {"eqG": "st_eqG", "elG": "st_elG"}                 # lib stability lemmas
LIB_NS = {"sg": "ns_sg", "sucG": "ns_suc", "addG": "ns_add", "mulG": "ns_mul",
          "theG": "ns_the"}                                 # lib nsing lemmas
WFF, NAT, SET = 0, 1, 2
_P16 = struct.Struct("<H").pack
_P32 = struct.Struct("<I").pack

# mm0-c (upstream 0d414c0, unchanged by the K215 capacity patch) per-statement
# capacities: verifier_types.c STACK_SIZE, HEAP_SIZE, STORE_SIZE (bytes),
# HYP_STACK_SIZE, UNIFY_STACK_SIZE, UNIFY_HEAP_SIZE; 55 = bound-variable cap.
LIMITS = dict(stack=65536, heap=65536, store=1 << 26, hyps=256, ustack=256,
              uheap=65536, bv=55)


class Untranslatable(Exception):
    pass


class Ctx:
    """Hash-consed output DAG for one statement (expressions, proofs, convs)."""

    def __init__(self):
        self.nodes, self.key = [], {}

    def mk(self, *nd):
        k = self.key.get(nd)
        if k is None:
            self.nodes.append(nd)
            k = self.key[nd] = len(self.nodes) - 1
        return k


def _kids(nd):
    """Children of an output DAG node that are emitted on the proof stack."""
    k = nd[0]
    if k == "app":
        return nd[2]
    if k == "thm":
        return nd[3] + nd[2] + (nd[4],)
    if k == "conv":
        return (nd[1], nd[2])
    return ()


class NegTrans:
    def __init__(self, src, lib):
        self.src, self.lib = src, lib
        self.terms = list(lib.terms)        # output tables (start = lib)
        self.thms = list(lib.thms)
        self.tname = {t.name: t.id for t in self.terms}
        self.hname = {t.name: t.id for t in self.thms}
        self.names = set(self.tname) | set(self.hname)
        self.renamed = []                   # (wanted, used) for output name clashes
        self.out_stmts = [(st.op, bytes(st.body), st.kind, st.ref) for st in lib.iter_stmts()]
        self.w = None                       # MMBWriter when streaming (stream_to)
        self.spec = None
        self.tmap = {}     # src term id -> template
        self.hmap = {}     # src thm id -> (out thm id, needed src-arg idx list)
        self.why = {}      # src decl -> reason it was not translated
        self.side = {}     # out term id -> (lemma id, needed arg idx, perm) or None
        self.sbound = [tuple(type_bound(w) for w in t.args) for t in src.terms]
        for t in src.terms:
            n = t.name
            if n in SAME_TERMS:
                self.tmap[t.id] = ("same", self.tname[n])
            elif n in GTERMS:
                self.tmap[t.id] = ("def", self.tname[GTERMS[n]])
            elif n == "d0":
                self.tmap[t.id] = ("sg0", self.tname["d0"])
        self.sg = self.tname["sg"]
        self.im, self.al = self.tname["im"], self.tname["al"]
        self.ng, self.dn, self.tru = self.tname["ng"], self.tname["dn"], self.tname["tru"]
        self.nsing = self.tname["nsing"]
        self.st = {n: self.hname[n] for n in ("st_ng", "st_dn", "st_im", "st_al", "st_tru", "st_A")}
        for d, l in list(LIB_ST.items()) + list(LIB_NS.items()):
            tid = self.tname[d]
            self.side[tid] = (self.hname[l], self.lib_needed(tid, self.hname[l]),
                              list(range(len(self.terms[tid].args))))
        self.stats = dict(defs=0, thms=0, in_bytes=0, out_bytes=0, stdefs=0, nsdefs=0,
                          in_cmds=0, out_cmds=0)
        # per-statement mm0-c resource use: max over outputs, and the worst
        # output/source ratios (heap, store) with the theorem names
        self.usage = {k: (0, None) for k in LIMITS}
        self.ratio = {"heap": (0.0, None), "store": (0.0, None)}
        self.src_usage = {"heap": (0, None), "store": (0, None)}
        self.limit_fail = []

    def lib_needed(self, tid, lid):
        """Arg indices whose side hypothesis a lib st_/ns_ lemma takes (in order)."""
        nodes, root, hyps = decode_unify(self.lib, self.thms[lid])
        out = []
        for h in hyps:
            nd = nodes[h]           # im (dn (var i) A) (var i)  or  nsing (var i) A
            if nd[1] == self.nsing:
                out.append(nodes[nd[2][0]][1])
            else:
                out.append(nodes[nd[2][1]][1])
        return out

    def uniq(self, name):
        """An output name not used yet (clashes are renamed and recorded)."""
        if name not in self.names:
            self.names.add(name)
            return name
        k = 2
        while "%s_%d" % (name, k) in self.names:
            k += 1
        new = "%s_%d" % (name, k)
        self.names.add(new)
        self.renamed.append((name, new))
        return new

    @staticmethod
    def targs(args):
        """Translated binder words: regular nat -> set (deps kept)."""
        return [type_word(False, SET, type_deps(w)) if type_sort(w) == NAT and not type_bound(w)
                else w for w in args] + [type_word(False, WFF, 0)]

    # ---------------- expressions ----------------
    def tr_expr(self, cx, snodes, n, sargs, memo, dummies, bound=False):
        """Translate source expression node n (source DAG `snodes`); `sargs`
        are the source statement's binder words; `bound`: n is in a binder
        position (a bound nat variable stays a variable). Iterative."""
        r = memo.get((n, bound))
        if r is not None:
            return r
        A = cx.mk("var", len(sargs))
        srcterms = self.src.terms
        sbound = self.sbound
        tmap = self.tmap
        mk = cx.mk
        top = (n, bound)
        stack = [(n, bound, False)]
        while stack:
            n, b, expanded = stack.pop()
            key = (n, b)
            if key in memo:
                continue
            nd = snodes[n]
            k = nd[0]
            if k == "var":
                r = mk("var", nd[1])
                w = sargs[nd[1]]
                if not b and type_sort(w) == NAT and type_bound(w):
                    r = mk("app", self.sg, (r,))
            elif k == "dummy":
                r = dummies.get(n)
                if r is None:
                    r = dummies[n] = mk("dummy", nd[1], len(dummies))
                if not b and nd[1] == NAT:
                    r = mk("app", self.sg, (r,))
            else:
                tid = nd[1]
                tpl = tmap.get(tid)
                if tpl is None:
                    raise Untranslatable("term " + srcterms[tid].name)
                bf = sbound[tid]
                ch = nd[2]
                if not expanded:
                    stack.append((n, b, True))
                    for j in range(len(ch) - 1, -1, -1):
                        if (ch[j], bf[j]) not in memo:
                            stack.append((ch[j], bf[j], False))
                    continue
                args = tuple([memo[(a, bf[j])] for j, a in enumerate(ch)])
                if tpl[0] == "same":
                    r = mk("app", tpl[1], args)
                elif tpl[0] == "sg0":
                    r = mk("app", self.sg, (mk("app", tpl[1], ()),))
                else:
                    r = mk("app", tpl[1], args + (A,))
            memo[key] = r
        return memo[top]

    # ---------------- side proofs ----------------
    def stab_stmt(self, cx, e, A):
        return cx.mk("app", self.im, (cx.mk("app", self.dn, (e, A)), e))

    def ns_stmt(self, cx, e, A):
        return cx.mk("app", self.nsing, (e, A))

    def side_stmt(self, cx, i, w, A):
        v = cx.mk("var", i)
        return self.ns_stmt(cx, v, A) if type_sort(w) == NAT else self.stab_stmt(cx, v, A)

    def side_proof(self, cx, e, w, A, memo, need):
        """Side proof for an argument expression e of source binder type w."""
        return self.side_rec(cx, "ns" if type_sort(w) == NAT else "st", e, A, memo, need)

    def stab(self, cx, e, A, memo, need):
        """Proof node of `dn e A -> e`; `need` collects own var indices used."""
        return self.side_rec(cx, "st", e, A, memo, need)

    def ns(self, cx, e, A, memo, need):
        """Proof node of `nsing e A` for a translated nat term e."""
        return self.side_rec(cx, "ns", e, A, memo, need)

    def side_plan(self, cx, kind, e, A):
        """(children [(kind, expr)], build(child proofs) -> proof) for one node."""
        nd = cx.nodes[e]
        if kind == "st":
            concl = self.stab_stmt(cx, e, A)
            if nd[0] == "var":
                return None, concl
            if nd[0] != "app":
                raise Untranslatable("stability of a dummy")
            t, a = nd[1], nd[2]
            if t == self.ng:
                return ((), lambda hs: cx.mk("thm", self.st["st_ng"], (a[0], A), (), concl)), concl
            if t == self.dn:
                return ((), lambda hs: cx.mk("thm", self.st["st_dn"], (a[0], A), (), concl)), concl
            if t == self.im:
                return ((("st", a[1]),), lambda hs: cx.mk("thm", self.st["st_im"], (a[0], a[1], A),
                                                         hs, concl)), concl
            if t == self.al:
                return ((("st", a[1]),), lambda hs: cx.mk("thm", self.st["st_al"], (a[0], a[1], A),
                                                         hs, concl)), concl
            if t == self.tru:
                return ((), lambda hs: cx.mk("thm", self.st["st_tru"], (A,), (), concl)), concl
            if t in self.side:
                return self.side_app_plan(cx, "st", t, a, A, concl), concl
            raise Untranslatable("stability of term " + self.terms[t].name)
        concl = self.ns_stmt(cx, e, A)
        if nd[0] == "var":
            return None, concl
        if nd[0] == "app" and nd[1] in self.side:
            return self.side_app_plan(cx, "ns", nd[1], nd[2], A, concl), concl
        raise Untranslatable("nsing of " + (self.terms[nd[1]].name if nd[0] == "app" else nd[0]))

    def side_app_plan(self, cx, kind, t, a, A, concl):
        if self.side[t] is None:
            raise Untranslatable("no side lemma for " + self.terms[t].name)
        lid, needed, perm = self.side[t]
        targs = tuple(a[i] for i in perm)
        if len(self.thms[lid].args) == len(targs) + 1:     # e.g. ns_sg (a: nat) (A: wff)
            targs += (A,)
        return (tuple((kind, a[perm[j]]) for j in needed),
                lambda hs: cx.mk("thm", lid, targs, hs, concl))

    def side_rec(self, cx, kind, e, A, memo, need):
        """Iterative side proof (stability `st` / nsing `ns`) of expression e."""
        top = (kind, e)
        if top in memo:
            return memo[top]
        stack = [(top, None)]
        while stack:
            key, plan = stack.pop()
            if key in memo:
                continue
            if plan is None:
                k, x = key
                pl, concl = self.side_plan(cx, k, x, A)
                if pl is None:              # a variable
                    if k == "st" and x == A:
                        memo[key] = cx.mk("thm", self.st["st_A"], (A,), (), concl)
                    else:
                        need.add(cx.nodes[x][1])
                        memo[key] = cx.mk("sidehyp", cx.nodes[x][1])
                    continue
                kids, build = pl
                todo = [c for c in kids if c not in memo]
                if todo:
                    stack.append((key, pl))
                    for c in reversed(todo):
                        stack.append((c, None))
                    continue
                memo[key] = build(tuple(memo[c] for c in kids))
            else:
                kids, build = plan
                memo[key] = build(tuple(memo[c] for c in kids))
        return memo[top]

    # ---------------- emission ----------------
    def emit(self, cx, nargs, hyp_exprs, root, is_def=False):
        """Encode the proof stream (without End) for hyps + root (a proof, or a
        def body). Returns (bytes, number of commands); self.last_use holds
        the statement's mm0-c resource use."""
        nodes = cx.nodes
        N = len(nodes)
        cnt = [0] * N
        seen = bytearray(N)
        todo = list(hyp_exprs) + [root]
        for n in todo:
            cnt[n] += 1
        while todo:
            n = todo.pop()
            if seen[n]:
                continue
            seen[n] = 1
            nd = nodes[n]
            k = nd[0]
            if k == "app":
                ks = nd[2]
            elif k == "thm":
                ks = nd[3] + nd[2] + (nd[4],)
            elif k == "conv":
                ks = (nd[1], nd[2]) + tuple(self.conv_exprs(cx, nd[3]))
            else:
                continue
            for k in ks:
                cnt[k] += 1
                todo.append(k)
        ba = bytearray()
        bapp = ba.append
        p16, p32 = _P16, _P32

        def put(op, d):
            if d == 0:
                bapp(op)
            elif d < 0x100:
                bapp(op | 0x40)
                bapp(d)
            elif d < 0x10000:
                bapp(op | 0x80)
                ba.extend(p16(d))
            else:
                bapp(op | 0xC0)
                ba.extend(p32(d))
        heap = {}
        for i in range(nargs):
            heap[cx.mk("var", i)] = i
        hp = nargs
        ncmd = 0
        # resource accounting (mm0-c): store bytes, stack depth, dummies
        store = 12 * nargs
        depth = maxd = ndummy = 0
        # tasks: (x << 3) | kind; kind 0 go(node) 1 fin(node) 2 gc(conv node)
        # 3 Hyp (x = hyp index) 4 Conv command 5 Unfold command
        tasks = [root << 3]
        for i in range(len(hyp_exprs) - 1, -1, -1):
            tasks.append(i << 3 | 3)
            tasks.append(hyp_exprs[i] << 3)
        pop, push = tasks.pop, tasks.append
        hget = heap.get
        while tasks:
            t = pop()
            k = t & 7
            n = t >> 3
            ncmd += 1
            if k == 0:
                h = hget(n)
                if h is not None:
                    put(PROOF_REF, h)
                    depth += 1
                    if depth > maxd:
                        maxd = depth
                    continue
                nd = nodes[n]
                nk = nd[0]
                if nk == "app":
                    a = nd[2]
                    if a:
                        ncmd -= 1
                        push(n << 3 | 1)
                        for x in reversed(a):
                            push(x << 3)
                        continue
                    store += 16
                    depth += 1
                    if depth > maxd:
                        maxd = depth
                    if cnt[n] > 1:
                        put(PROOF_TERM_SAVE, nd[1])
                        heap[n] = hp
                        hp += 1
                    else:
                        put(PROOF_TERM, nd[1])
                elif nk == "thm":
                    ncmd -= 1
                    push(n << 3 | 1)
                    push(nd[4] << 3)
                    for x in reversed(nd[3] + nd[2]):
                        push(x << 3)
                elif nk == "dummy":
                    put(PROOF_DUMMY, nd[1])
                    heap[n] = hp
                    hp += 1
                    ndummy += 1
                    store += 12
                    depth += 1
                    if depth > maxd:
                        maxd = depth
                elif nk == "conv":
                    # go e1, go p2, Conv, gc c, [Save]
                    ncmd -= 1
                    push(n << 3 | 1)
                    push(nd[3] << 3 | 2)
                    push(4)
                    push(nd[2] << 3)
                    push(nd[1] << 3)
                else:
                    raise MMBError("cannot emit %r" % (nd,))
            elif k == 1:
                nd = nodes[n]
                nk = nd[0]
                if nk == "app":
                    na = len(nd[2])
                    store += 16 + 4 * na
                    depth += 1 - na
                    if cnt[n] > 1:
                        put(PROOF_TERM_SAVE, nd[1])
                        heap[n] = hp
                        hp += 1
                    else:
                        put(PROOF_TERM, nd[1])
                elif nk == "thm":
                    depth -= len(nd[2]) + len(nd[3])
                    if cnt[n] > 1:
                        put(PROOF_THM_SAVE, nd[1])
                        heap[n] = hp
                        hp += 1
                    else:
                        put(PROOF_THM, nd[1])
                else:       # conv: after Conv + conversion proof, |- e1 is on top
                    if cnt[n] > 1:
                        put(PROOF_SAVE, 0)
                        heap[n] = hp
                        hp += 1
                    else:
                        ncmd -= 1
            elif k == 2:
                nd = nodes[n]
                ck = nd[0]
                if ck == "refl":
                    bapp(PROOF_REFL)
                    depth -= 2
                elif ck == "symm":
                    bapp(PROOF_SYMM)
                    push(nd[1] << 3 | 2)
                elif ck == "cong":
                    bapp(PROOF_CONG)
                    depth += 2 * len(nd[2]) - 2
                    if depth > maxd:
                        maxd = depth
                    for x in reversed(nd[2]):
                        push(x << 3 | 2)
                elif ck == "unfold":
                    # go e, Unfold, gc c
                    ncmd -= 1
                    push(nd[4] << 3 | 2)
                    push(5)
                    push(nd[3] << 3)
                else:
                    raise MMBError("bad conv %r" % (nd,))
            elif k == 3:
                bapp(PROOF_HYP)
                depth -= 1
                heap[cx.mk("hyp", n)] = hp
                hp += 1
            elif k == 4:
                bapp(PROOF_CONV)
                depth += 1
                if depth > maxd:
                    maxd = depth
            else:
                bapp(PROOF_UNFOLD)
                depth -= 1
        self.last_use = dict(heap=hp, store=store, stack=maxd + 2, dummies=ndummy,
                             hyps=len(hyp_exprs))
        return bytes(ba), ncmd

    def conv_exprs(self, cx, c):
        out = []
        st = [c]
        while st:
            nd = cx.nodes[st.pop()]
            if nd[0] == "symm":
                st.append(nd[1])
            elif nd[0] == "cong":
                st.extend(nd[2])
            elif nd[0] == "unfold":
                out.append(nd[3]); st.append(nd[4])
        return out

    def unify_of(self, cx, exprs, nargs):
        """Unify stream for expressions (in order; the caller interleaves UHyp),
        with UTermSave/URef for subterms that occur more than once.
        Returns (cmds, max unify-stack depth, unify heap size)."""
        nodes = cx.nodes
        cnt = {}
        seen = set()
        todo = list(exprs)
        for n in todo:
            cnt[n] = cnt.get(n, 0) + 1
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            nd = nodes[n]
            if nd[0] == "app":
                for a in nd[2]:
                    cnt[a] = cnt.get(a, 0) + 1
                    todo.append(a)
        out = []
        uheap = {}
        for n in seen:
            if nodes[n][0] == "var":
                uheap[n] = nodes[n][1]
        nv = nargs
        maxd = 0
        for ei, e in enumerate(exprs):
            if ei:
                out.append((UNIFY_HYP, 0))
            st = [e]
            while st:
                d = len(st)
                if d > maxd:
                    maxd = d
                n = st.pop()
                if n in uheap:
                    out.append((UNIFY_REF, uheap[n]))
                    continue
                nd = nodes[n]
                if nd[0] == "dummy":
                    out.append((UNIFY_DUMMY, nd[1]))
                    uheap[n] = nv
                    nv += 1
                elif nd[0] == "app":
                    if cnt[n] > 1 and nd[2]:
                        out.append((UNIFY_TERM_SAVE, nd[1]))
                        uheap[n] = nv
                        nv += 1
                    else:
                        out.append((UNIFY_TERM, nd[1]))
                    for a in reversed(nd[2]):
                        st.append(a)
                    if len(st) > maxd:
                        maxd = len(st)
                else:
                    raise MMBError("bad statement node %r" % (nd,))
        return out, maxd + 1, nv

    def check_limits(self, name, use):
        """Refuse a statement that mm0-c could not hold; track maxima."""
        bad = [k for k in LIMITS if use.get(k, 0) > LIMITS[k]]
        for k in LIMITS:
            if use.get(k, 0) > self.usage[k][0]:
                self.usage[k] = (use[k], name)
        if bad:
            msg = "mm0-c limit: " + ", ".join("%s %d > %d" % (k, use[k], LIMITS[k]) for k in bad)
            self.limit_fail.append((name, msg))
            raise Untranslatable(msg)

    # ---------------- output ----------------
    def stream_to(self, path, spec_text=None, def_pub=False, thm_pub=None, spool_dir=None,
                  header="-- generated by translator.negtrans: public translated declarations"):
        """Write the output .mmb incrementally (statements go straight to the
        writer's spool). def_pub: translated defs are public (and printed in
        the spec); a set of output names: only those defs (lib local defs
        included) are public; thm_pub: None | 'pub' (translations of the source's pub
        theorems) | 'all'. Call before run(); finish with finish_stream()."""
        self.w = MMBWriter(path, spool_dir)
        for s in self.lib.sorts:
            self.w.add_sort(s.mods, s.name)
        self.def_pub, self.thm_pub = def_pub, thm_pub
        self.spec = None if spec_text is None else [
            spec_text.rstrip(), "", header]
        for op, body, kind, ref in self.out_stmts:
            self._out(op, body, kind, ref)      # with def_pub, lib local defs become public too
        self.out_stmts = None

    def _out(self, op, body, kind, ref, pub=False, spec_line=None):
        if self.w is None:
            self.out_stmts.append((op, body, kind, ref) if not pub else (op, body, kind, ref, True))
            return
        if kind == "local_def" and (self.def_pub is True or isinstance(self.def_pub, (set, frozenset))
                                    and self.terms[ref].name in self.def_pub):
            op = STMT_DEF
            if self.spec is not None:
                self.spec.append(self.print_decl(self.terms[ref], True))
        elif kind == "local_thm" and pub:
            op = STMT_THM
            if self.spec is not None:
                self.spec.append(spec_line or self.print_decl(self.thms[ref], False))
        self.w.add_stmt(op, body=body)

    def finish_stream(self, spec_path=None):
        for t in self.terms:
            self.w.add_term(t)
        for t in self.thms:
            self.w.add_thm(t)
        self.w.finish("rebuild")
        if spec_path is not None and self.spec is not None:
            with open(spec_path, "w", newline="\n") as f:
                f.write("\n".join(self.spec) + "\n")

    # ---------------- defs ----------------
    def tr_def(self, t):
        src = self.src
        if not t.unify:
            raise Untranslatable("abstract def")
        snodes, root, _ = decode_unify(src, t)
        cx = Ctx()
        n = len(t.args)
        body = self.tr_expr(cx, snodes, root, t.args, {}, {})
        name = t.name + "_N"
        args = self.targs(t.args)
        sort = SET if t.sort == NAT else t.sort
        if name in self.tname and self.tname[name] < len(self.lib.terms):
            # supplied by the library: check it
            lt = self.terms[self.tname[name]]
            lnodes, lroot, _ = decode_unify(self.lib, lt)
            cx2 = Ctx()
            ok = (self.canon(cx2, lnodes, lroot) == self.canon(cx2, cx.nodes, body)
                  and list(lt.args) == args and lt.sort == sort)
            if not ok:
                raise Untranslatable("library def %s does not match translation" % name)
            tid = lt.id
        else:
            uni, ud, uh = self.unify_of(cx, [body], n + 1)
            body_b, _ = self.emit(cx, n + 1, [], body, is_def=True)
            use = dict(self.last_use, ustack=ud, uheap=uh,
                       bv=sum(1 for w in args if type_bound(w)) + self.last_use["dummies"])
            name = self.uniq(name)
            self.check_limits(name, use)
            nt = Term(len(self.terms), sort, True, args, type_word(False, sort, type_deps(t.ret)),
                      uni, name=name)
            self.terms.append(nt)
            self.tname[name] = nt.id
            self._out(STMT_LOCAL_DEF, body_b + b"\0", "local_def", nt.id)
            tid = nt.id
            self.stats["defs"] += 1
        self.tmap[t.id] = ("def", tid)
        if t.sort in (WFF, NAT) and tid not in self.side:
            self.make_side(tid, cx, body, n, "st" if t.sort == WFF else "ns")
        return tid

    def canon(self, cx, nodes, n, memo=None):
        """Copy expression n of `nodes` into cx (dummies renumbered in
        first-visit order, left to right). Iterative."""
        memo = {} if memo is None else memo
        if n in memo:
            return memo[n]
        nd0 = [sum(1 for v in memo.values() if cx.nodes[v][0] == "dummy")]
        stack = [(n, False)]
        while stack:
            m, expanded = stack.pop()
            if m in memo:
                continue
            nd = nodes[m]
            if nd[0] == "app":
                if not expanded:
                    stack.append((m, True))
                    for a in reversed(nd[2]):
                        if a not in memo:
                            stack.append((a, False))
                    continue
                r = cx.mk("app", nd[1], tuple([memo[a] for a in nd[2]]))
            elif nd[0] == "dummy":
                r = cx.mk("dummy", nd[1], nd0[0])
                nd0[0] += 1
            else:
                r = cx.mk(*nd)
            memo[m] = r
        return memo[n]

    def make_side(self, tid, dcx, dbody, n, kind):
        """Lemma st_<D_N> / ns_<D_N>: stability (wff def) or nsing (nat def)
        of D_N(vars) from the same property of its body."""
        # binder order of the lemma: bound args first, then regular args, so
        # that every regular arg may depend on every bound arg
        targs = self.terms[tid].args
        perm = [i for i, w in enumerate(targs) if type_bound(w)] + \
               [i for i, w in enumerate(targs) if not type_bound(w)]
        pos = {i: j for j, i in enumerate(perm)}
        cx = Ctx()
        memo_c = {k: cx.mk("var", pos[nd[1]]) for k, nd in enumerate(dcx.nodes)
                  if nd is not None and nd[0] == "var"}
        body = self.canon(cx, dcx.nodes, dbody, memo_c)
        A = cx.mk("var", n)
        lhs = cx.mk("app", tid, tuple(cx.mk("var", pos[i]) for i in range(n + 1)))
        need = set()
        try:
            pb = self.side_rec(cx, kind, body, A, {}, need)
        except Untranslatable:
            self.side[tid] = None
            return
        needed = sorted(need)
        unf = cx.mk("unfold", tid, lhs, body, cx.mk("refl", body))
        if kind == "st":
            concl = self.stab_stmt(cx, lhs, A)
            conv = cx.mk("cong", self.im, (cx.mk("cong", self.dn, (unf, cx.mk("refl", A))), unf))
        else:
            concl = self.ns_stmt(cx, lhs, A)
            conv = cx.mk("cong", self.nsing, (unf, cx.mk("refl", A)))
        root = cx.mk("conv", concl, pb, conv)
        mkh = self.ns_stmt if kind == "ns" else self.stab_stmt
        hyps = [mkh(cx, cx.mk("var", j), A) for j in needed]
        root = self.resolve_sidehyps(cx, root, needed, 0)
        nb = sum(1 for w in targs if type_bound(w))
        full = (1 << nb) - 1
        args = [targs[i] if type_bound(targs[i]) else type_word(False, type_sort(targs[i]), full)
                for i in perm[:-1]] + [targs[-1]]       # A keeps no deps
        try:
            self.add_thm(kind + "_" + self.terms[tid].name, args, cx, concl, hyps, root, n + 1)
        except Untranslatable:
            self.side[tid] = None
            return
        self.side[tid] = (len(self.thms) - 1, needed, perm)
        self.stats[kind + "defs"] += 1

    def resolve_sidehyps(self, cx, root, needed, base):
        pos = {v: base + j for j, v in enumerate(needed)}
        memo = {}
        nodes = cx.nodes
        stack = [(root, False)]
        while stack:
            n, expanded = stack.pop()
            if n in memo:
                continue
            nd = nodes[n]
            k = nd[0]
            if k == "sidehyp":
                memo[n] = cx.mk("hyp", pos[nd[1]])
            elif k == "thm":
                if not expanded:
                    stack.append((n, True))
                    for h in nd[3]:
                        if h not in memo:
                            stack.append((h, False))
                    continue
                memo[n] = cx.mk("thm", nd[1], nd[2], tuple([memo[h] for h in nd[3]]), nd[4])
            elif k == "conv":
                if not expanded:
                    stack.append((n, True))
                    if nd[2] not in memo:
                        stack.append((nd[2], False))
                    continue
                memo[n] = cx.mk("conv", nd[1], memo[nd[2]], nd[3])
            else:
                memo[n] = n
        return memo[root]

    def add_thm(self, name, args, cx, concl, hyps, root, nargs, pub=False, spec_line=None):
        name = name if pub else self.uniq(name)
        if pub:
            if name in self.names:
                raise MMBError("public theorem name %s is already used" % name)
            self.names.add(name)
        uni, ud, uh = self.unify_of(cx, [concl] + list(reversed(hyps)), nargs)
        body_b, ncmd = self.emit(cx, nargs, hyps, root)
        use = dict(self.last_use, ustack=ud, uheap=uh,
                   bv=sum(1 for w in args if type_bound(w)) + self.last_use["dummies"])
        self.check_limits(name, use)
        th = Thm(len(self.thms), list(args), uni, name=name)
        self.thms.append(th)
        self.hname[name] = th.id
        body = body_b + b"\0"
        self._out(STMT_LOCAL_THM, body, "local_thm", th.id, pub, spec_line)
        self.stats["out_cmds"] += ncmd
        return th.id, len(body)

    # ---------------- theorems ----------------
    def tr_thm(self, st):
        src = self.src
        t = src.thms[st.ref]
        dag = build_stmt_dag(src, st)
        sn = dag.nodes
        n = len(t.args)
        sargs = t.args
        cx = Ctx()
        A = cx.mk("var", n)
        dmy = {}
        emem = {}
        tr_expr = self.tr_expr
        tmap = self.tmap
        srcthms, srcterms = src.thms, src.terms

        def E(x, bound=False):
            r = emem.get((x, bound))
            return r if r is not None else tr_expr(cx, sn, x, sargs, emem, dmy, bound)
        need = set()
        smemo = {}
        pmemo = {}
        cmemo = {}

        def conv_of(c, bound):
            """Iterative translation of a source conversion tree."""
            key0 = (c, bound)
            if key0 in cmemo:
                return cmemo[key0]
            stack = [(c, bound, False)]
            while stack:
                c, b, expanded = stack.pop()
                key = (c, b)
                if key in cmemo:
                    continue
                nd = sn[c]
                k = nd[0]
                if k == "refl":
                    cmemo[key] = cx.mk("refl", E(nd[1], b))
                    continue
                if k in ("symm", "cut", "cref"):
                    sub = (nd[1], b)
                    if sub not in cmemo:
                        stack.append((c, b, True))
                        stack.append((nd[1], b, False))
                        continue
                    cmemo[key] = cx.mk("symm", cmemo[sub]) if k == "symm" else cmemo[sub]
                    continue
                if k == "cong":
                    tpl = tmap.get(nd[1])
                    if tpl is None:
                        raise Untranslatable("term " + srcterms[nd[1]].name)
                    sa = srcterms[nd[1]].args
                    subs = [(x, type_bound(sa[j])) for j, x in enumerate(nd[2])]
                    todo = [s for s in subs if s not in cmemo]
                    if todo:
                        stack.append((c, b, True))
                        for s in reversed(todo):
                            stack.append((s[0], s[1], False))
                        continue
                    cs = tuple([cmemo[s] for s in subs])
                    if tpl[0] == "same":
                        r = cx.mk("cong", tpl[1], cs)
                    elif tpl[0] == "sg0":
                        r = cx.mk("cong", self.sg, (cx.mk("cong", tpl[1], ()),))
                    else:
                        r = cx.mk("cong", tpl[1], cs + (cx.mk("refl", A),))
                    cmemo[key] = r
                    continue
                if k == "unfold":
                    tpl = tmap.get(nd[1])
                    if tpl is None or tpl[0] != "def":
                        raise Untranslatable("unfold " + srcterms[nd[1]].name)
                    sub = (nd[4], False)
                    if sub not in cmemo:
                        stack.append((c, b, True))
                        stack.append((nd[4], False, False))
                        continue
                    cmemo[key] = cx.mk("unfold", tpl[1], E(nd[2]), E(nd[3]), cmemo[sub])
                    continue
                raise Untranslatable("conv node " + k)
            return cmemo[key0]

        hmap = self.hmap
        why = self.why
        side_rec = self.side_rec
        stack = [(dag.result[1], False)]
        while stack:
            x, expanded = stack.pop()
            if x in pmemo:
                continue
            nd = sn[x]
            k = nd[0]
            if k == "hyp":
                pmemo[x] = cx.mk("hyp", nd[1])
            elif k == "thm":
                if not expanded:
                    if nd[1] not in hmap:
                        raise Untranslatable("uses " + srcthms[nd[1]].name + " (" +
                                             why.get(("thm", nd[1]), "?") + ")")
                    todo = [h for h in nd[3] if h not in pmemo]
                    if todo:
                        stack.append((x, True))
                        for h in reversed(todo):
                            stack.append((h, False))
                        continue
                oid, needed = hmap[nd[1]]
                ca = srcthms[nd[1]].args
                args = tuple([E(a, type_bound(ca[j])) for j, a in enumerate(nd[2])])
                hs = tuple([pmemo[h] for h in nd[3]])
                if needed:
                    hs += tuple([side_rec(cx, "ns" if type_sort(ca[i]) == NAT else "st",
                                          args[i], A, smemo, need) for i in needed])
                pmemo[x] = cx.mk("thm", oid, args + (A,), hs, E(nd[4]))
            elif k == "conv":
                if not expanded and nd[2] not in pmemo:
                    stack.append((x, True))
                    stack.append((nd[2], False))
                    continue
                pmemo[x] = cx.mk("conv", E(nd[1]), pmemo[nd[2]], conv_of(nd[3], False))
            else:
                raise Untranslatable("proof node " + k)
        root = pmemo[dag.result[1]]
        # statement from the table (not from the stream)
        un, uroot, uhyps = decode_unify(src, t)
        umemo = {}
        concl = self.tr_expr(cx, un, uroot, sargs, umemo, {})
        hyps = [self.tr_expr(cx, un, h, sargs, umemo, {}) for h in uhyps]
        needed = sorted(need)
        root = self.resolve_sidehyps(cx, root, needed, len(hyps))
        hyps += [self.side_stmt(cx, i, sargs[i], A) for i in needed]
        args = self.targs(t.args)
        pub = self.w is not None and (self.thm_pub == "all" or
                                      self.thm_pub == "pub" and t.kind == "thm")
        oid, blen = self.add_thm(t.name + "_N", args, cx, concl, hyps, root, n + 1, pub=pub)
        self.hmap[t.id] = (oid, needed)
        self.stats["thms"] += 1
        self.stats["in_bytes"] += len(st.body)
        self.stats["in_cmds"] += dag.ncmds
        self.stats["out_bytes"] += blen
        # source resource use (as mm0-c would count it) and output/source ratios
        sheap = len(dag.heap)
        sstore = 0
        for nd in sn:
            if nd[0] == "app":
                sstore += 16 + 4 * len(nd[2])
            elif nd[0] in ("var", "dummy"):
                sstore += 12
        if sheap > self.src_usage["heap"][0]:
            self.src_usage["heap"] = (sheap, t.name)
        if sstore > self.src_usage["store"][0]:
            self.src_usage["store"] = (sstore, t.name)
        for k, s in (("heap", sheap), ("store", sstore)):
            if s >= 1000:       # ratios of small proofs are noise
                r = self.last_use[k] / s
                if r > self.ratio[k][0]:
                    self.ratio[k] = (r, t.name)
        return oid

    def check_axiom(self, st):
        """Map a peano axiom to its library lemma, checking the statement."""
        src = self.src
        t = src.thms[st.ref]
        if t.name not in AXIOMS:
            raise Untranslatable("axiom " + t.name)
        lname, needed = AXIOMS[t.name]
        lt = self.thms[self.hname[lname]]
        n = len(t.args)
        cx = Ctx()
        un, uroot, uhyps = decode_unify(src, t)
        memo = {}
        mine = [self.tr_expr(cx, un, uroot, t.args, memo, {})] + \
            [self.tr_expr(cx, un, h, t.args, memo, {}) for h in uhyps]
        A = cx.mk("var", n)
        mine += [self.side_stmt(cx, i, t.args[i], A) for i in needed]
        ln, lroot, lhyps = decode_unify(self.lib, lt)
        theirs = [self.canon(cx, ln, x) for x in [lroot] + lhyps]
        if mine != theirs or list(lt.args) != self.targs(t.args):
            raise MMBError("library lemma %s does not match the translation of %s" % (lname, t.name))
        self.hmap[t.id] = (lt.id, needed)

    def run(self, max_thms=None, progress=None):
        """Translate the source stream. `progress(stmt_index, offset)` is
        called every 50,000 statements when given."""
        done = 0
        for i, st in enumerate(self.src.iter_stmts()):
            if progress is not None and i % 50000 == 0:
                progress(i, st.offset)
            if st.kind in ("sort", "term"):
                continue
            if st.kind in ("def", "local_def"):
                t = self.src.terms[st.ref]
                if st.ref in self.tmap:
                    continue
                try:
                    self.tr_def(t)
                except Untranslatable as e:
                    self.why[("term", st.ref)] = str(e)
                continue
            if st.kind == "axiom":
                try:
                    self.check_axiom(st)
                except Untranslatable as e:
                    self.why[("thm", st.ref)] = str(e)
                continue
            if max_thms is not None and done >= max_thms:
                break
            done += 1
            try:
                self.tr_thm(st)
            except Untranslatable as e:
                self.why[("thm", st.ref)] = str(e)
        return done

    def write(self, path, mm0=None, spec_text=None, pub_all=False, extra_pub=()):
        """Write the .mmb (in-memory mode, i.e. without stream_to). With `mm0`,
        every local def is made public and the translations of the source's pub
        theorems become pub theorems, and a spec (spec_text + those defs and
        theorem statements) is written to `mm0`."""
        if self.w is not None:
            raise MMBError("write() after stream_to(): use finish_stream()")
        pub = {oid for sid, (oid, _) in self.hmap.items()
               if self.src.thms[sid].kind == "thm" or
               pub_all and self.src.thms[sid].kind == "local_thm"} if mm0 else set()
        pub |= set(extra_pub)       # e.g. B5 recovered theorems appended after the run
        w = MMBWriter(path)
        for s in self.lib.sorts:
            w.add_sort(s.mods, s.name)
        for t in self.terms:
            w.add_term(t)
        for t in self.thms:
            w.add_thm(t)
        spec = [spec_text.rstrip(), "", "-- generated by translator.negtrans: translated defs",
                "-- and the translations of the source's pub theorems"] if mm0 else []
        for ent in self.out_stmts:
            op, body, kind, ref = ent[:4]
            if mm0 and kind == "local_def":
                op = STMT_DEF
                spec.append(self.print_decl(self.terms[ref], True))
            elif kind == "local_thm" and (ref in pub or len(ent) > 4):
                op = STMT_THM
                spec.append(self.print_decl(self.thms[ref], False))
            w.add_stmt(op, body=body)
        w.finish("rebuild")
        if mm0:
            with open(mm0, "w", newline="\n") as f:
                f.write("\n".join(spec) + "\n")
        return len(pub)

    def print_decl(self, d, is_def):
        class M:
            terms = self.terms
        names, binders = [], []
        bnames = []
        for i, w in enumerate(d.args):
            srt = self.lib.sorts[type_sort(w)].name
            if type_bound(w):
                nm = "x%d" % i; bnames.append(nm)
                binders.append("{%s: %s}" % (nm, srt))
            else:
                nm = "v%d" % i
                deps = [bnames[k] for k in range(len(bnames)) if w >> k & 1]
                binders.append("(%s: %s)" % (nm, " ".join([srt] + deps)))
            names.append(nm)
        nodes, root, hyps = decode_unify(M, d)
        dnames = {}

        def pr(n0, top=False):
            out = []
            stack = [(n0, top)]
            while stack:
                n, tp = stack.pop()
                if isinstance(n, str):
                    out.append(n)
                    continue
                nd = nodes[n]
                if nd[0] == "var":
                    out.append(names[nd[1]])
                elif nd[0] == "dummy":
                    if n not in dnames:
                        dnames[n] = ("dd%d" % len(dnames), nd[1])
                    out.append(dnames[n][0])
                else:
                    t = self.terms[nd[1]]
                    if not nd[2]:
                        out.append(t.name)
                        continue
                    seq = [] if tp else ["("]
                    seq.append(t.name)
                    for a in nd[2]:
                        seq.append(" ")
                        seq.append(a)
                    if not tp:
                        seq.append(")")
                    for x in reversed(seq):
                        stack.append((x, False) if not isinstance(x, str) else (x, False))
            return "".join(out)
        if is_def:
            body = pr(root, True)
            dm = "".join(" (.%s: %s)" % (nm, self.lib.sorts[s].name) for nm, s in dnames.values())
            ret = self.lib.sorts[d.sort].name
            rdeps = [bnames[k] for k in range(len(bnames)) if d.ret >> k & 1]
            return "def %s %s%s: %s = $ %s $;" % (d.name, " ".join(binders), dm,
                                                 " ".join([ret] + rdeps), body)
        hs = "".join(" (h%d: $ %s $)" % (k, pr(h, True)) for k, h in enumerate(hyps))
        return "theorem %s %s%s: $ %s $;" % (d.name, " ".join(binders), hs, pr(root, True))


def big_stack(fn, *args, **kw):
    """Run fn in a thread with a large stack (belt and braces: the translator
    is iterative, but library code paths may still recurse)."""
    import threading
    res = {}

    def run():
        try:
            res["v"] = fn(*args, **kw)
        except BaseException as e:      # re-raised in the caller
            res["e"] = e
    old = threading.stack_size()
    try:
        threading.stack_size(256 << 20)
    except (ValueError, RuntimeError):
        pass
    t = threading.Thread(target=run)
    t.start()
    t.join()
    threading.stack_size(old)
    if "e" in res:
        raise res["e"]
    return res.get("v")


def main(argv=None):
    import argparse
    import collections
    ap = argparse.ArgumentParser(prog="translator.negtrans")
    ap.add_argument("src"); ap.add_argument("lib"); ap.add_argument("out")
    ap.add_argument("--max", type=int, default=None)
    ap.add_argument("--mm0", default=None, help="also write a spec (hpeano.mm0 + public translations)")
    ap.add_argument("--spec", default="foundation/hpeano.mm0")
    ap.add_argument("--pub-all", action="store_true",
                    help="with --mm0: make every translated theorem public")
    ns = ap.parse_args(argv)
    tr = NegTrans(read_mmb(ns.src), read_mmb(ns.lib))
    tried = tr.run(ns.max)
    npub = tr.write(ns.out, ns.mm0, open(ns.spec).read() if ns.mm0 else None,
                    ns.pub_all)
    if ns.mm0:
        print("wrote %s with %d public translated theorems" % (ns.mm0, npub))
    s = tr.stats
    fails = [(k, v) for k, v in tr.why.items() if k[0] == "thm"
             and tr.src.thms[k[1]].kind != "axiom"]
    print("theorems tried %d, translated %d, failed %d; defs translated %d, st_ lemmas %d, ns_ lemmas %d" % (
        tried, s["thms"], len(fails), s["defs"], s["stdefs"], s["nsdefs"]))
    print("proof bytes in %d -> out %d (ratio %.2f)" % (
        s["in_bytes"], s["out_bytes"], s["out_bytes"] / max(1, s["in_bytes"])))
    root = collections.Counter(v.split(" (")[0] if not v.startswith("uses") else "uses-failed"
                               for _, v in fails)
    print("failure reasons:", dict(root.most_common(12)))
    first = [(tr.src.thms[k[1]].name, v) for k, v in fails if not v.startswith("uses")][:12]
    print("first root failures:", first)
    print("defs not translated:", sorted(tr.src.terms[k[1]].name for k in tr.why if k[0] == "term")[:20])
    print("mm0-c resource maxima:", tr.usage)


if __name__ == "__main__":
    sys.exit(big_stack(main))
