"""Byte-level MMB access for the linker: tables and statements as raw slices, ids remapped without decoding
into Python objects (translator/mmb_reader.py builds a Term/Thm object per entry, which made reading the
interface copies the linker's hotspot).

MMB layout (mm0-c types.c / mm0-rs export.rs): header "<4sBBHIIIIIIQ" (magic, version, #sorts, -, #terms,
#thms, p_terms, p_thms, p_proof, -, p_index), sort modifier bytes at 40; term entry (u16 nargs, u8 sort|0x80
if def, u8 -, u32 p_args) -> nargs+1 u64 binder words (last = return type), then for a def its unify stream
up to End; theorem entry (u16 nargs, u16 -, u32 p_args) -> nargs u64 words, then the unify stream (conclusion,
then UHyp + hypothesis per hypothesis) up to End. Commands: low 6 bits opcode, high 2 bits data width
(0/1/2/4 bytes, little-endian). Statement stream at p_proof: statement command whose data is the statement's
total length, then its proof stream up to End; a final End closes the stream.
"""
import mmap
import os
import shutil
import struct
import tempfile

HEADER_SIZE = 40
STMT_AXIOM, STMT_SORT, STMT_DEF, STMT_THM, STMT_LOCAL_DEF, STMT_LOCAL_THM = 0x02, 0x04, 0x05, 0x06, 0x0D, 0x0E


class MMBError(Exception):
    pass


def _pad8(n):
    return (-n) & 7

_HDR = struct.Struct("<4sBBHIIIIIIQ")
_ENT = struct.Struct("<HBBI")
_U64 = struct.Struct("<Q")
_U32 = struct.Struct("<I")
_U16 = struct.Struct("<H")
SIZE = [1] * 64 + [2] * 64 + [3] * 64 + [5] * 64          # command length by first byte


def remap(buf, pos, a, amap, b=None, bmap=None):
    """Re-encode the command stream starting at buf[pos] through its End. Commands with opcode in the set a
    have their data mapped by amap (list), opcode in b by bmap. Returns (bytes incl. End, end position)."""
    out = bytearray()
    run = pos
    while True:
        c = buf[pos]
        if c == 0:
            pos += 1
            break
        sz = SIZE[c]
        op = c & 0x3F
        if op in a:
            m = amap
        elif b is not None and op in b:
            m = bmap
        else:
            pos += sz
            continue
        if sz == 1:
            d = 0
        elif sz == 2:
            d = buf[pos + 1]
        elif sz == 3:
            d = buf[pos + 1] | buf[pos + 2] << 8
        else:
            d = _U32.unpack_from(buf, pos + 1)[0]
        nd = m[d]
        if nd != d:
            out += buf[run:pos]
            if nd == 0:
                out.append(op)
            elif nd < 0x100:
                out.append(op | 0x40); out.append(nd)
            elif nd < 0x10000:
                out.append(op | 0x80); out += _U16.pack(nd)
            else:
                out.append(op | 0xC0); out += _U32.pack(nd)
            run = pos + sz
        pos += sz
    out += buf[run:pos]
    return bytes(out), pos


def stream_end(buf, pos):
    while True:
        c = buf[pos]
        if c == 0:
            return pos + 1
        pos += SIZE[c]


UNIFY_T = frozenset((0x30, 0x31))
PROOF_T = frozenset((0x10, 0x11))
PROOF_H = frozenset((0x14, 0x15))


class RawMMB:
    def __init__(self, path):
        f = open(path, "rb")
        try:
            self.d = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
        finally:
            f.close()
        d = self.d
        (magic, ver, ns, _, nt, nh, self.p_terms, self.p_thms, self.p_proof, _, self.p_index) = _HDR.unpack_from(d, 0)
        if magic != b"MM0B" or ver != 1:
            raise MMBError("not an MMB v1 file: " + path)
        self.sort_mods = bytes(d[HEADER_SIZE:HEADER_SIZE + ns])
        self.nterms, self.nthms, self.nsorts = nt, nh, ns
        self.term_ent = [_ENT.unpack_from(d, self.p_terms + 8 * i) for i in range(nt)]   # (nargs, sort, -, p)
        self.thm_ent = [_ENT.unpack_from(d, self.p_thms + 8 * i) for i in range(nh)]     # (nargs, -, -, p)
        self._index()

    def _cstr(self, p):
        e = self.d.find(b"\0", p)
        return self.d[p:e].decode("utf-8", "replace")

    def _index(self):
        d = self.d
        self.tabs = {}
        if self.p_index:
            n = _U64.unpack_from(d, self.p_index)[0]
            for k in range(n):
                o = self.p_index + 8 + 16 * k
                self.tabs[bytes(d[o:o + 4])] = struct.unpack_from("<IQ", d, o + 4)[1]
        if b"Name" not in self.tabs:
            raise MMBError("MMB without a name index")
        p = self.tabs[b"Name"]
        ns, nt, nh = self.nsorts, self.nterms, self.nthms
        ents = struct.unpack_from("<%dQ" % (2 * (ns + nt + nh)), d, p)
        names = [self._cstr(ents[2 * i + 1]) for i in range(ns + nt + nh)]
        self.sort_names, self.term_names, self.thm_names = names[:ns], names[ns:ns + nt], names[ns + nt:]

    def _names_list(self, q):
        if not q:
            return None
        n = _U64.unpack_from(self.d, q)[0]
        return [self._cstr(x) for x in struct.unpack_from("<%dQ" % n, self.d, q + 8)]

    def var_names(self, kind, i):
        if b"VarN" not in self.tabs:
            return None
        j = i if kind == "t" else self.nterms + i
        return self._names_list(_U64.unpack_from(self.d, self.tabs[b"VarN"] + 8 * j)[0])

    def hyp_names(self, i):
        if b"HypN" not in self.tabs:
            return None
        return self._names_list(_U64.unpack_from(self.d, self.tabs[b"HypN"] + 8 * i)[0])

    def term(self, i, tmap):
        """(sort byte incl. def bit, nargs, binder words bytes incl. return, remapped unify bytes or b'')."""
        nargs, sort, _, p = self.term_ent[i]
        e = p + 8 * (nargs + 1)
        words = self.d[p:e]
        u = remap(self.d, e, UNIFY_T, tmap)[0] if sort & 0x80 else b""
        return sort, nargs, words, u

    def thm(self, i, tmap):
        nargs, _, _, p = self.thm_ent[i]
        e = p + 8 * nargs
        return nargs, self.d[p:e], remap(self.d, e, UNIFY_T, tmap)[0]

    def stmts(self):
        """Yield (op, kind letter 's'/'t'/'h', ref, body start, body end) in stream order."""
        d = self.d
        pos = self.p_proof
        ks = kt = kh = 0
        while True:
            c = d[pos]
            if c == 0:
                return
            sz = SIZE[c]
            op = c & 0x3F
            ln = d[pos + 1] if sz == 2 else _U16.unpack_from(d, pos + 1)[0] if sz == 3 else \
                _U32.unpack_from(d, pos + 1)[0]
            if op == 0x04:
                yield op, "s", ks, pos + sz, pos + ln; ks += 1
            elif op in (0x05, 0x0D):
                yield op, "t", kt, pos + sz, pos + ln; kt += 1
            elif op in (0x02, 0x06, 0x0E):
                yield op, "h", kh, pos + sz, pos + ln; kh += 1
            else:
                raise MMBError("bad statement opcode %#x" % op)
            pos += ln


class Entry:
    __slots__ = ("name", "var_names", "hyp_names", "args", "num_hyps", "sort", "words", "unify")

    def __init__(self, name, var_names, hyp_names, nargs, sort, words, unify):
        self.name, self.var_names, self.hyp_names = name, var_names, hyp_names
        self.args = range(nargs)
        self.num_hyps = len(hyp_names) if hyp_names else 0
        self.sort, self.words, self.unify = sort, words, unify


def encode_stmt(op, body):
    """Statement command with its total length as data (minimal width, as mm0-rs write_cmd_bytes)."""
    n = len(body)
    if n + 2 < 0x100:
        return bytes((op | 0x40, n + 2)) + body
    if n + 3 < 0x10000:
        return bytes((op | 0x80,)) + _U16.pack(n + 3) + body
    if n + 5 >= 1 << 32:
        raise MMBError("statement too large for MMB format")
    return bytes((op | 0xC0,)) + _U32.pack(n + 5) + body


class RawWriter:
    """Streaming MMB writer (layout of mm0-rs export.rs, as translator/mmb_writer.py): sorts and Entry tables in
    memory, statements spooled to a temporary file; finish() writes header + tables + stream + a name index
    (Name / VarN / HypN, empty Delm / Nota; mm0-c does not read the index)."""

    def __init__(self, path, spool_dir=None):
        self.path = path
        self.sorts, self.terms, self.thms = [], [], []
        self._spool = tempfile.TemporaryFile(dir=spool_dir)
        self._len = 0
        self._sort_off, self._term_off, self._thm_off = [], [], []

    def add_sort(self, mods, name):
        self.sorts.append((mods, name))

    def add_term(self, e):
        self.terms.append(e)

    def add_thm(self, e):
        self.thms.append(e)

    def add_stmt(self, op, body):
        {STMT_SORT: self._sort_off, STMT_DEF: self._term_off, STMT_LOCAL_DEF: self._term_off,
         STMT_AXIOM: self._thm_off, STMT_THM: self._thm_off, STMT_LOCAL_THM: self._thm_off}[op].append(self._len)
        b = encode_stmt(op, bytes(body))
        self._spool.write(b)
        self._len += len(b)

    def _tables(self):
        out = bytearray(HEADER_SIZE)
        out += bytes(m for m, _ in self.sorts)
        out += b"\0" * _pad8(len(out))
        p_terms = len(out)
        out += b"\0" * (8 * len(self.terms))
        for i, t in enumerate(self.terms):
            out += b"\0" * _pad8(len(out))
            struct.pack_into("<HBBI", out, p_terms + 8 * i, len(t.args), t.sort, 0, len(out))
            out += t.words
            out += t.unify
        out += b"\0" * _pad8(len(out))
        p_thms = len(out)
        out += b"\0" * (8 * len(self.thms))
        for i, t in enumerate(self.thms):
            out += b"\0" * _pad8(len(out))
            struct.pack_into("<HBBI", out, p_thms + 8 * i, len(t.args), 0, 0, len(out))
            out += t.words
            out += t.unify
        p_proof = len(out)
        if p_proof >= 1 << 32:
            raise MMBError("tables exceed 4GB")
        return out, p_terms, p_thms, p_proof

    def _index(self, base, p_proof):
        out = bytearray()
        pos = {}

        def s(name):
            name = name if name is not None else "_"
            if name not in pos:
                pos[name] = base + len(out)
                out.extend(name.encode("utf-8") + b"\0")
            return pos[name]
        for _, nm in self.sorts:
            s(nm)
        for d in self.terms + self.thms:
            s(d.name)
            for v in d.var_names or ():
                s(v)
        for d in self.thms:
            for v in d.hyp_names or ():
                s(v)
        out += b"\0" * _pad8(base + len(out))

        def vlist(names):
            p = base + len(out)
            out.extend(_U64.pack(len(names)))
            for v in names:
                out.extend(_U64.pack(s(v)))
            return p
        var_p = [vlist(d.var_names or ["_"] * len(d.args)) for d in self.terms + self.thms]
        hyp_p = [vlist(d.hyp_names or ["_"] * d.num_hyps) for d in self.thms]
        p_names = base + len(out)
        for (_, nm), off in zip(self.sorts, self._sort_off):
            out += struct.pack("<QQ", p_proof + off, s(nm))
        for d, off in zip(self.terms, self._term_off):
            out += struct.pack("<QQ", p_proof + off, s(d.name))
        for d, off in zip(self.thms, self._thm_off):
            out += struct.pack("<QQ", p_proof + off, s(d.name))
        p_vars = base + len(out)
        for p in var_p:
            out += _U64.pack(p)
        p_hyps = base + len(out)
        for p in hyp_p:
            out += _U64.pack(p)
        p_delm = base + len(out)
        out += b"\0\0"
        out += b"\0" * _pad8(base + len(out))
        p_nota = base + len(out)
        out += _U64.pack(p_nota + 8) + b"\0"
        out += b"\0" * _pad8(base + len(out))
        p_index = base + len(out)
        ents = [(b"Name", p_names), (b"VarN", p_vars), (b"HypN", p_hyps), (b"Delm", p_delm), (b"Nota", p_nota)]
        out += _U64.pack(len(ents))
        for ident, p in ents:
            out += ident + struct.pack("<IQ", 0, p)
        return bytes(out), p_index

    def finish(self):
        if (len(self._sort_off), len(self._term_off), len(self._thm_off)) != \
                (len(self.sorts), len(self.terms), len(self.thms)):
            raise MMBError("statement stream does not match the tables")
        head, p_terms, p_thms, p_proof = self._tables()
        idx, p_index = self._index(p_proof + self._len + 1, p_proof)
        _HDR.pack_into(head, 0, b"MM0B", 1, len(self.sorts), 0, len(self.terms), len(self.thms), p_terms, p_thms,
                       p_proof, 0, p_index)
        tmp = self.path + ".tmp"
        with open(tmp, "wb") as f:
            f.write(head)
            self._spool.seek(0)
            shutil.copyfileobj(self._spool, f, 1 << 20)
            f.write(b"\0")
            f.write(idx)
        self._spool.close()
        os.replace(tmp, self.path)
