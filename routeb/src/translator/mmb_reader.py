"""MMB reader: data model plus a lazy, memory-mapped parser.

The model keeps everything in "MMB space": sort/term/thm ids, heap indices and
raw command streams. Nothing is expanded; the proof stream of a statement is
decoded only on request (`Stmt.cmds()` or `proof_dag.build_stmt_dag`).
"""

import mmap
import struct

from .mmb_format import (
    MM0B_MAGIC, MM0B_VERSION, MAX_SORTS, HEADER_SIZE, MMBError,
    CMD_END, STMT_AXIOM, STMT_SORT, STMT_DEF, STMT_THM, STMT_LOCAL_DEF,
    STMT_LOCAL_THM, UNIFY_HYP, INDEX_NAME, INDEX_VAR_NAME, INDEX_HYP_NAME,
    unpack_cmd, iter_cmds, type_bound, type_sort, type_deps,
)

_HDR = struct.Struct("<4sBBHIIIIIIQ")
_ENTRY = struct.Struct("<HBBI")       # term entry; thm entry uses (H, 2 pad, I)
_U64 = struct.Struct("<Q")


class Sort:
    __slots__ = ("id", "mods", "name")

    def __init__(self, id, mods, name=None):
        self.id, self.mods, self.name = id, mods, name

    def __repr__(self):
        return "Sort(%d, %r, mods=%#x)" % (self.id, self.name, self.mods)


class Term:
    """A term or def. `args` are u64 binder words, `ret` the return type word.

    For a def, `unify` is the def's unify command list (body, prefix order,
    URef i = argument/saved subterm i, UDummy s = def dummy), End excluded.
    `dummies` = sorts of the UDummy commands (the def's bound dummies)."""
    __slots__ = ("id", "sort", "is_def", "args", "ret", "unify",
                 "name", "var_names", "p_args")

    def __init__(self, id, sort, is_def, args, ret, unify=None,
                 name=None, var_names=None, p_args=None):
        self.id, self.sort, self.is_def = id, sort, is_def
        self.args, self.ret, self.unify = args, ret, unify
        self.name, self.var_names, self.p_args = name, var_names, p_args

    @property
    def num_args(self):
        return len(self.args)

    @property
    def dummies(self):
        from .mmb_format import UNIFY_DUMMY
        return [d for op, d in (self.unify or ()) if op == UNIFY_DUMMY]

    def __repr__(self):
        return "%s(%d, %r, nargs=%d)" % ("Def" if self.is_def else "Term",
                                         self.id, self.name, len(self.args))


class Thm:
    """An axiom or theorem statement. `unify` (End excluded) encodes the
    conclusion, then for each hypothesis in reverse order: UHyp, hyp expr."""
    __slots__ = ("id", "args", "unify", "name", "var_names", "hyp_names",
                 "p_args", "num_hyps", "kind")

    def __init__(self, id, args, unify, name=None, var_names=None,
                 hyp_names=None, p_args=None):
        self.id, self.args, self.unify = id, args, unify
        self.name, self.var_names, self.hyp_names = name, var_names, hyp_names
        self.p_args = p_args
        self.num_hyps = sum(1 for op, _ in unify if op == UNIFY_HYP)
        self.kind = None   # filled from the proof stream: 'axiom' / 'thm' / 'local_thm'

    @property
    def num_args(self):
        return len(self.args)

    def __repr__(self):
        return "Thm(%d, %r, nargs=%d, nhyps=%d)" % (
            self.id, self.name, len(self.args), self.num_hyps)


class Stmt:
    """One entry of the declaration (proof) stream.

    op: STMT_* opcode; kind: 'sort'|'term'|'def'|'local_def'|'axiom'|'thm'|'local_thm';
    ref: the sort/term/thm id it introduces; body: bytes after the statement
    header (the proof command stream including its End, or empty);
    new_cmds: replacement command list for the writer (None = keep body);
    offset: file offset of the statement command."""
    __slots__ = ("op", "kind", "ref", "body", "offset", "new_cmds")

    def __init__(self, op, kind, ref, body, offset=None):
        self.op, self.kind, self.ref, self.body, self.offset = op, kind, ref, body, offset
        self.new_cmds = None   # set to a list of (op, data) to replace the proof

    def cmds(self):
        """Iterate the proof commands as (op, data), End excluded."""
        for op, data in iter_cmds(self.body):
            if op == CMD_END:
                return
            yield op, data

    def __repr__(self):
        return "Stmt(%s %d, %d bytes)" % (self.kind, self.ref, len(self.body))


def binder_str(ty, sorts=None):
    s = type_sort(ty)
    sn = sorts[s].name if sorts and sorts[s].name else str(s)
    if type_bound(ty):
        return "{%s}" % sn
    deps = type_deps(ty)
    ds = [str(i) for i in range(55) if deps >> i & 1]
    return "(%s%s)" % (sn, (" " + " ".join(ds)) if ds else "")


class MMBFile:
    """A parsed .mmb file.

    Tables (sorts/terms/thms) are parsed eagerly; statements lazily via
    `iter_stmts()` (each holds a memoryview slice of the file body).
    `tail` is the raw bytes after the proof stream's final End (the debugging
    index plus padding) and `tail_offset` its file offset; the writer can
    relocate it (index='preserve')."""

    def __init__(self, data, path=None):
        self.path = path
        self.data = data
        self._parse_header()
        self._parse_tables()
        self._parse_index_names()

    @classmethod
    def open(cls, path):
        f = open(path, "rb")
        try:
            data = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
        except ValueError:          # empty file
            data = b""
        finally:
            f.close()
        return cls(data, path)

    @classmethod
    def from_bytes(cls, b):
        return cls(bytes(b))

    # -- header and tables --------------------------------------------------
    def _parse_header(self):
        d = self.data
        if len(d) < HEADER_SIZE:
            raise MMBError("file too short")
        (magic, version, nsorts, _r, nterms, nthms, p_terms, p_thms,
         p_proof, _r2, p_index) = _HDR.unpack_from(d, 0)
        if magic != MM0B_MAGIC:
            raise MMBError("bad magic %r" % magic)
        if version != MM0B_VERSION:
            raise MMBError("bad version %d" % version)
        if nsorts > MAX_SORTS:
            raise MMBError("too many sorts")
        self.version = version
        self.p_terms, self.p_thms, self.p_proof, self.p_index = p_terms, p_thms, p_proof, p_index
        self.sorts = [Sort(i, d[HEADER_SIZE + i]) for i in range(nsorts)]
        self._nterms, self._nthms = nterms, nthms

    def _read_unify(self, pos):
        out = []
        for op, data in iter_cmds(self.data, pos):
            if op == CMD_END:
                break
            out.append((op, data))
        return out

    def _parse_tables(self):
        d = self.data
        self.terms = []
        for i in range(self._nterms):
            nargs, sort, _r, p_args = _ENTRY.unpack_from(d, self.p_terms + 8 * i)
            is_def = bool(sort & 0x80)
            words = struct.unpack_from("<%dQ" % (nargs + 1), d, p_args)
            unify = self._read_unify(p_args + 8 * (nargs + 1)) if is_def else None
            self.terms.append(Term(i, sort & 0x7F, is_def, list(words[:nargs]),
                                   words[nargs], unify, p_args=p_args))
        self.thms = []
        for i in range(self._nthms):
            nargs, _r, _r2, p_args = _ENTRY.unpack_from(d, self.p_thms + 8 * i)
            words = struct.unpack_from("<%dQ" % nargs, d, p_args)
            unify = self._read_unify(p_args + 8 * nargs)
            self.thms.append(Thm(i, list(words), unify, p_args=p_args))

    # -- index ----------------------------------------------------------------
    def _cstr(self, p):
        if not p or p >= len(self.data):
            return None
        e = self.data.find(b"\0", p)
        return bytes(self.data[p:e]).decode("utf-8", "replace")

    def index_tables(self):
        """{id(bytes4): (data u32, ptr u64)} of the index header, or {}."""
        d = self.data
        if not self.p_index or self.p_index + 8 > len(d):
            return {}
        n = _U64.unpack_from(d, self.p_index)[0]
        out = {}
        for k in range(n):
            o = self.p_index + 8 + 16 * k
            ident = bytes(d[o:o + 4])
            dat, ptr = struct.unpack_from("<IQ", d, o + 4)
            out[ident] = (dat, ptr)
        return out

    def _names_list(self, p):
        n = _U64.unpack_from(self.data, p)[0]
        return [self._cstr(q) for q in struct.unpack_from("<%dQ" % n, self.data, p + 8)]

    def _parse_index_names(self):
        tabs = self.index_tables()
        ns, nt, nh = len(self.sorts), len(self.terms), len(self.thms)
        if INDEX_NAME in tabs:
            p = tabs[INDEX_NAME][1]
            ents = struct.unpack_from("<%dQ" % (2 * (ns + nt + nh)), self.data, p)
            names = [self._cstr(ents[2 * i + 1]) for i in range(ns + nt + nh)]
            for s, n in zip(self.sorts, names[:ns]):
                s.name = n
            for t, n in zip(self.terms, names[ns:ns + nt]):
                t.name = n
            for t, n in zip(self.thms, names[ns + nt:]):
                t.name = n
        if INDEX_VAR_NAME in tabs:
            p = tabs[INDEX_VAR_NAME][1]
            ptrs = struct.unpack_from("<%dQ" % (nt + nh), self.data, p)
            for t, q in zip(self.terms + self.thms, ptrs):
                t.var_names = self._names_list(q) if q else None
        if INDEX_HYP_NAME in tabs:
            p = tabs[INDEX_HYP_NAME][1]
            ptrs = struct.unpack_from("<%dQ" % nh, self.data, p)
            for t, q in zip(self.thms, ptrs):
                t.hyp_names = self._names_list(q) if q else None

    # -- statement stream -----------------------------------------------------
    def iter_stmts(self):
        """Lazily yield Stmt objects in stream order (sorts, terms, defs,
        axioms, theorems interleaved as declared). Also sets Thm.kind."""
        d = self.data
        mv = memoryview(d)
        pos = self.p_proof
        isort = iterm = ithm = 0
        while True:
            op, data, sz = unpack_cmd(d, pos)
            if op == CMD_END:
                self.tail_offset = pos + 1
                return
            if data < sz:
                raise MMBError("bad statement length at %#x" % pos)
            body = mv[pos + sz:pos + data]
            if op == STMT_SORT:
                st = Stmt(op, "sort", isort, body, pos); isort += 1
            elif op in (STMT_DEF, STMT_LOCAL_DEF):
                t = self.terms[iterm]
                kind = ("local_def" if op == STMT_LOCAL_DEF else
                        "def" if t.is_def else "term")
                st = Stmt(op, kind, iterm, body, pos); iterm += 1
            elif op in (STMT_AXIOM, STMT_THM, STMT_LOCAL_THM):
                kind = {STMT_AXIOM: "axiom", STMT_THM: "thm",
                        STMT_LOCAL_THM: "local_thm"}[op]
                self.thms[ithm].kind = kind
                st = Stmt(op, kind, ithm, body, pos); ithm += 1
            else:
                raise MMBError("bad statement opcode %#x at %#x" % (op, pos))
            yield st
            pos += data

    def stmts(self):
        return list(self.iter_stmts())

    @property
    def tail(self):
        if not hasattr(self, "tail_offset"):
            for _ in self.iter_stmts():
                pass
        return bytes(self.data[self.tail_offset:])

    # -- helpers --------------------------------------------------------------
    def term_by_name(self, name):
        for t in self.terms:
            if t.name == name:
                return t
        raise KeyError(name)

    def thm_by_name(self, name):
        for t in self.thms:
            if t.name == name:
                return t
        raise KeyError(name)


def read_mmb(path):
    return MMBFile.open(path)
