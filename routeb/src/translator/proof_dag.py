"""DAG-preserving views of MMB command streams.

`build_stmt_dag` symbolically runs a statement's proof stream on the mm0-c
stack machine (without unification checks) and returns a `ProofDAG`: a flat
node table in which every heap entry (argument, dummy, Save'd term/proof/conv)
is a single node referenced by id wherever the stream Refs it. Nothing is
expanded, so the DAG is linear in the stream size.

`decode_unify` turns a term/thm table unify stream (def body, theorem
statement) into the same node format.

Node formats (tuples, or lists while holes are open):
  expressions
    ('var', i)                    i-th binder of the statement
    ('dummy', sort)               dummy (bound) variable introduced in the body
    ('app', termid, (a1..an))     term application
  proofs (each carries the proved expression node `e`)
    ('hyp', k, e)                 k-th hypothesis
    ('thm', thmid, (args), (hyp_proofs), e)
    ('conv', e1, p2, c)           |- e1 from p2 : |- e2 and c : e1 = e2
    ('sorry', e)
  conversions (c : e1 = e2)
    ('refl', e)
    ('symm', c)                   c : e2 = e1
    ('cong', termid, (c1..cn))
    ('unfold', termid, lhs, e, c) lhs = t args unfolds to e, c : e = e2
    ('cut', c)                    ConvCut: c proves it, and it was saved
    ('cref', c)                   Ref to a saved conversion node c
"""

import struct

from .mmb_format import (
    MMBError, CMD_END,
    PROOF_TERM, PROOF_TERM_SAVE, PROOF_REF, PROOF_DUMMY, PROOF_THM,
    PROOF_THM_SAVE, PROOF_HYP, PROOF_CONV, PROOF_REFL, PROOF_SYMM, PROOF_CONG,
    PROOF_UNFOLD, PROOF_CONV_CUT, PROOF_CONV_SAVE, PROOF_SAVE, PROOF_SORRY,
    UNIFY_TERM, UNIFY_TERM_SAVE, UNIFY_REF, UNIFY_DUMMY, UNIFY_HYP,
)

_U16 = struct.Struct("<H")
_U32 = struct.Struct("<I")

# stack element tags
E, P, CO, C = "E", "P", "CO", "C"


class ProofDAG:
    """nodes: list of node tuples; heap: list of stack elements
    (('E', n) | ('P', n, e) | ('C', e1, e2, n)); result: final stack element;
    hyps: node ids of hypothesis expressions in order; ncmds: commands run."""

    def __init__(self, nodes, heap, result, hyps, ncmds):
        self.nodes, self.heap, self.result, self.hyps, self.ncmds = nodes, heap, result, hyps, ncmds

    def __repr__(self):
        return "ProofDAG(%d nodes, %d heap, %d hyps)" % (
            len(self.nodes), len(self.heap), len(self.hyps))

    def show(self, n, mmb=None, depth=6):
        """Render node n as an s-expression (for debugging; expands sharing up to depth)."""
        nd = self.nodes[n]
        if depth == 0:
            return "#%d" % n
        tag = nd[0]
        if tag == "var":
            return "v%d" % nd[1]
        if tag == "dummy":
            return "d#%d" % n
        if tag == "app":
            nm = mmb.terms[nd[1]].name if mmb else "t%d" % nd[1]
            if not nd[2]:
                return nm
            return "(%s %s)" % (nm, " ".join(self.show(a, mmb, depth - 1) for a in nd[2]))
        return "<%s #%d>" % (tag, n)


def _freeze(nodes):
    return [tuple(x) if isinstance(x, list) else x for x in nodes]


def _decode(body):
    """(op, data) pairs of a proof stream up to End (End excluded); one pass,
    inlined decoding (hot path of the translator)."""
    b = bytes(body)
    out = []
    app = out.append
    i, n = 0, len(b)
    u16, u32 = _U16.unpack_from, _U32.unpack_from
    while i < n:
        c = b[i]
        w = c & 0xC0
        op = c & 0x3F
        if w == 0:
            if op == 0:
                break
            app((op, 0))
            i += 1
        elif w == 0x40:
            app((op, b[i + 1]))
            i += 2
        elif w == 0x80:
            app((op, u16(b, i + 1)[0]))
            i += 3
        else:
            app((op, u32(b, i + 1)[0]))
            i += 5
    return out


def build_stmt_dag(mmb, stmt, cmds=None):
    """Symbolically execute a def/axiom/thm statement's proof stream.

    Def and axiom streams leave ('E', expr) (the def body / the axiom's
    conclusion); theorem streams leave ('P', proof, e)."""
    if stmt.kind in ("def", "local_def"):
        decl = mmb.terms[stmt.ref]
    elif stmt.kind in ("axiom", "thm", "local_thm"):
        decl = mmb.thms[stmt.ref]
    else:
        raise MMBError("statement %r has no proof stream" % stmt.kind)
    terms, thms = mmb.terms, mmb.thms
    nodes = []
    heap = []
    for i in range(len(decl.args)):
        nodes.append(("var", i))
        heap.append((E, i))
    stack = []
    hyps = []
    ncmds = 0

    def new(x):
        nodes.append(x)
        return len(nodes) - 1

    def pop(tag):
        s = stack.pop()
        if s[0] != tag:
            raise MMBError("bad stack slot: want %s got %s" % (tag, s[0]))
        return s

    for op, data in (cmds if cmds is not None else _decode(stmt.body)):
        ncmds += 1
        if op == PROOF_REF:
            s = heap[data]
            if s[0] == C:
                _, e1, e2, h = pop(CO)
                nodes[h] = ("cref", s[3])
            else:
                stack.append(s)
        elif op == PROOF_DUMMY:
            s = (E, new(("dummy", data)))
            stack.append(s)
            heap.append(s)
        elif op in (PROOF_TERM, PROOF_TERM_SAVE):
            n = len(terms[data].args)
            args = stack[len(stack) - n:] if n else []
            del stack[len(stack) - n:]
            s = (E, new(("app", data, tuple(a[1] for a in args))))
            stack.append(s)
            if op == PROOF_TERM_SAVE:
                heap.append(s)
        elif op in (PROOF_THM, PROOF_THM_SAVE):
            t = thms[data]
            e = pop(E)[1]
            n, k = len(t.args), t.num_hyps
            args = stack[len(stack) - n:] if n else []
            del stack[len(stack) - n:]
            hp = stack[len(stack) - k:] if k else []
            del stack[len(stack) - k:]
            s = (P, new(("thm", data, tuple(a[1] for a in args),
                         tuple(h[1] for h in hp), e)), e)
            stack.append(s)
            if op == PROOF_THM_SAVE:
                heap.append(s)
        elif op == PROOF_HYP:
            e = pop(E)[1]
            heap.append((P, new(("hyp", len(hyps), e)), e))
            hyps.append(e)
        elif op == PROOF_CONV:
            _, p2, e2 = pop(P)
            e1 = pop(E)[1]
            c = new(["hole"])
            stack.append((P, new(("conv", e1, p2, c)), e1))
            stack.append((CO, e1, e2, c))
        elif op == PROOF_REFL:
            _, e1, e2, h = pop(CO)
            nodes[h] = ("refl", e1)
        elif op == PROOF_SYMM:
            _, e1, e2, h = pop(CO)
            h2 = new(["hole"])
            nodes[h] = ("symm", h2)
            stack.append((CO, e2, e1, h2))
        elif op == PROOF_CONG:
            _, e1, e2, h = pop(CO)
            a1, a2 = nodes[e1], nodes[e2]
            if a1[0] != "app" or a2[0] != "app" or a1[1] != a2[1]:
                raise MMBError("Cong on non-matching terms")
            hs = [new(["hole"]) for _ in a1[2]]
            nodes[h] = ("cong", a1[1], tuple(hs))
            for x, y, hh in reversed(list(zip(a1[2], a2[2], hs))):
                stack.append((CO, x, y, hh))
        elif op == PROOF_UNFOLD:
            e = pop(E)[1]
            _, e1, e2, h = pop(CO)
            h2 = new(["hole"])
            nodes[h] = ("unfold", nodes[e1][1], e1, e, h2)
            stack.append((CO, e, e2, h2))
        elif op == PROOF_CONV_CUT:
            _, e1, e2, h = pop(CO)
            h2 = new(["hole"])
            nodes[h] = ("cut", h2)
            stack.append((C, e1, e2, h))
            stack.append((CO, e1, e2, h2))
        elif op == PROOF_CONV_SAVE:
            heap.append(pop(C))
        elif op == PROOF_SAVE:
            s = stack[-1]
            if s[0] == CO:
                raise MMBError("Can't save proof obligation")
            heap.append(s)
        elif op == PROOF_SORRY:
            s = stack.pop()
            if s[0] == E:
                stack.append((P, new(("sorry", s[1])), s[1]))
            else:
                h = s[3]
                nodes[h] = ("sorry_conv",)
        elif op == CMD_END:
            break
        else:
            raise MMBError("unknown proof opcode %#x" % op)
    if len(stack) != 1:
        raise MMBError("stack has %d elements at end" % len(stack))
    return ProofDAG(_freeze(nodes), heap, stack[0], hyps, ncmds)


def decode_unify(mmb, decl, nodes=None):
    """Decode a term/thm table unify stream into expression nodes.

    Returns (nodes, root, hyps): for a def, root is the body and hyps = [];
    for a thm, root is the conclusion and hyps the hypotheses in order.
    Saved subterms (UTermSave) are single shared nodes."""
    terms = mmb.terms
    nodes = [] if nodes is None else nodes
    nargs = len(decl.args)
    base = len(nodes)
    uheap = []
    for i in range(nargs):
        nodes.append(("var", i))
        uheap.append(base + i)
    exprs = []          # completed top-level expressions
    frames = []         # [nodeid, termid, children, needed]

    def done(n):
        while frames:
            fr = frames[-1]
            fr[2].append(n)
            if len(fr[2]) < fr[3]:
                return
            frames.pop()
            nodes[fr[0]] = ("app", fr[1], tuple(fr[2]))
            n = fr[0]
        exprs.append(n)

    for op, data in decl.unify:
        if op == UNIFY_REF:
            done(uheap[data])
        elif op in (UNIFY_TERM, UNIFY_TERM_SAVE):
            nodes.append(None)
            nid = len(nodes) - 1
            if op == UNIFY_TERM_SAVE:
                uheap.append(nid)
            k = len(terms[data].args)
            if k == 0:
                nodes[nid] = ("app", data, ())
                done(nid)
            else:
                frames.append([nid, data, [], k])
        elif op == UNIFY_DUMMY:
            nodes.append(("dummy", data))
            uheap.append(len(nodes) - 1)
            done(len(nodes) - 1)
        elif op == UNIFY_HYP:
            if frames:
                raise MMBError("UHyp inside an expression")
        else:
            raise MMBError("unknown unify opcode %#x" % op)
    if frames or not exprs:
        raise MMBError("incomplete unify stream")
    root, hyps = exprs[0], exprs[1:][::-1]
    return nodes, root, hyps
