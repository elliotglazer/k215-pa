"""MMB writer.

`MMBWriter` is streaming: sorts/term/thm table entries are kept in memory (they
are small), proof-stream statements are spooled to a temporary file as they are
added, and `finish()` assembles header + tables + stream + index. This is the
layout mm0-rs `export.rs` produces, so re-emitting a parsed file with
index='preserve' reproduces it byte for byte.

Index modes for finish():
  'rebuild'  - fresh Name/VarN/HypN tables (+ empty Delm/Nota) from the names
               attached to sorts/terms/thms (default for new files);
  'none'     - no index (p_index = 0);
  'preserve' - copy a reader's raw index tail, relocating its pointers
               (only valid when the declaration set is unchanged).
"""

import os
import shutil
import struct
import tempfile

from .mmb_format import (
    MM0B_MAGIC, MM0B_VERSION, MAX_SORTS, HEADER_SIZE, MMBError, CMD_END,
    STMT_SORT, STMT_DEF, STMT_LOCAL_DEF, STMT_AXIOM, STMT_THM, STMT_LOCAL_THM,
    INDEX_NAME, INDEX_VAR_NAME, INDEX_HYP_NAME, INDEX_DELIMITER, INDEX_NOTATION,
    encode_cmds, encode_stmt,
)

_HDR = struct.Struct("<4sBBHIIIIIIQ")
_U64 = struct.Struct("<Q")


def _pad8(n):
    return (-n) & 7


class MMBWriter:
    def __init__(self, path, spool_dir=None):
        self.path = path
        self.sorts = []          # (mods, name)
        self.terms = []          # reader.Term-like objects
        self.thms = []           # reader.Thm-like objects
        self._spool = tempfile.TemporaryFile(dir=spool_dir)
        self._stream_len = 0
        # stream-relative offsets of statements, by kind, in order
        self._sort_off, self._term_off, self._thm_off = [], [], []
        self._old_offsets = {}   # old file offset -> stream-relative new offset

    # -- declarations ---------------------------------------------------------
    def add_sort(self, mods, name=None):
        if len(self.sorts) >= MAX_SORTS:
            raise MMBError("too many sorts")
        self.sorts.append((mods, name))
        return len(self.sorts) - 1

    def add_term(self, term):
        self.terms.append(term)
        return len(self.terms) - 1

    def add_thm(self, thm):
        self.thms.append(thm)
        return len(self.thms) - 1

    # -- proof stream ---------------------------------------------------------
    def add_stmt(self, op, body=b"", cmds=None, old_offset=None):
        """Append a statement. Give either raw `body` bytes (including the
        trailing End for defs/axioms/thms) or `cmds`, a list of (op, data)
        without End (End is appended). A plain `term` has an empty body."""
        if cmds is not None:
            body = encode_cmds(cmds) + b"\0"
        off = self._stream_len
        if op == STMT_SORT:
            self._sort_off.append(off)
        elif op in (STMT_DEF, STMT_LOCAL_DEF):
            self._term_off.append(off)
        elif op in (STMT_AXIOM, STMT_THM, STMT_LOCAL_THM):
            self._thm_off.append(off)
        else:
            raise MMBError("bad statement opcode %#x" % op)
        if old_offset is not None:
            self._old_offsets[old_offset] = off
        b = encode_stmt(op, bytes(body))
        self._spool.write(b)
        self._stream_len += len(b)

    # -- assembly -------------------------------------------------------------
    def _tables(self):
        """Header+tables as a bytearray (header pointers filled except p_index)."""
        out = bytearray(HEADER_SIZE)
        out += bytes(m for m, _ in self.sorts)
        out += b"\0" * _pad8(len(out))
        p_terms = len(out)
        out += b"\0" * (8 * len(self.terms))
        for i, t in enumerate(self.terms):
            out += b"\0" * _pad8(len(out))
            p_args = len(out)
            struct.pack_into("<HBBI", out, p_terms + 8 * i, len(t.args),
                             t.sort | (0x80 if t.is_def else 0), 0, p_args)
            out += struct.pack("<%dQ" % (len(t.args) + 1), *t.args, t.ret)
            if t.is_def:
                out += encode_cmds(t.unify) + b"\0"
        out += b"\0" * _pad8(len(out))
        p_thms = len(out)
        out += b"\0" * (8 * len(self.thms))
        for i, t in enumerate(self.thms):
            out += b"\0" * _pad8(len(out))
            p_args = len(out)
            struct.pack_into("<HBBI", out, p_thms + 8 * i, len(t.args), 0, 0, p_args)
            out += struct.pack("<%dQ" % len(t.args), *t.args)
            out += encode_cmds(t.unify) + b"\0"
        p_proof = len(out)
        if p_proof >= 1 << 32:
            raise MMBError("tables exceed 4GB")
        return out, p_terms, p_thms, p_proof

    def finish(self, index="rebuild", tail=None, tail_offset=None):
        if len(self._sort_off) != len(self.sorts) or \
           len(self._term_off) != len(self.terms) or \
           len(self._thm_off) != len(self.thms):
            raise MMBError("statement stream does not match tables "
                           "(%d/%d sorts, %d/%d terms, %d/%d thms)" % (
                               len(self._sort_off), len(self.sorts),
                               len(self._term_off), len(self.terms),
                               len(self._thm_off), len(self.thms)))
        head, p_terms, p_thms, p_proof = self._tables()
        end_stream = p_proof + self._stream_len + 1      # + final End
        if index == "none":
            idx, p_index = b"\0\0\0\0", 0
        elif index == "preserve":
            delta_raw = end_stream - tail_offset
            pad = _pad8(delta_raw)
            base = end_stream + pad
            idx, p_index = self._relocate_tail(tail, tail_offset, base, p_proof)
            idx = b"\0" * pad + idx
        elif index == "rebuild":
            idx, p_index = self._build_index(end_stream, p_proof)
        else:
            raise MMBError("unknown index mode %r" % index)
        _HDR.pack_into(head, 0, MM0B_MAGIC, MM0B_VERSION, len(self.sorts), 0,
                       len(self.terms), len(self.thms), p_terms, p_thms,
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

    # -- index: preserve --------------------------------------------------------
    def _relocate_tail(self, tail, old_base, new_base, p_proof):
        """Copy the raw index tail to new_base, relocating file pointers.
        Statement pointers (Name.p_proof) are remapped via add_stmt(old_offset=)."""
        t = bytearray(tail)
        delta = new_base - old_base
        n_s, n_t, n_h = len(self.sorts), len(self.terms), len(self.thms)

        def rel(p):            # old file pointer -> offset inside t
            return p - old_base

        def fix(o):            # relocate a u64 pointer stored at t[o]
            v = _U64.unpack_from(t, o)[0]
            if v:
                _U64.pack_into(t, o, v + delta)
            return v

        hdr_p = self._old_p_index
        if not hdr_p:
            return bytes(t), 0
        h = rel(hdr_p)
        n = _U64.unpack_from(t, h)[0]
        tabs = {}
        for k in range(n):
            o = h + 8 + 16 * k
            tabs[bytes(t[o:o + 4])] = rel(fix(o + 8))
        if INDEX_NAME in tabs:
            o = tabs[INDEX_NAME]
            for i in range(n_s + n_t + n_h):
                pp = _U64.unpack_from(t, o + 16 * i)[0]
                if pp in self._old_offsets:
                    _U64.pack_into(t, o + 16 * i, p_proof + self._old_offsets[pp])
                fix(o + 16 * i + 8)
        seen = set()
        for key, cnt in ((INDEX_VAR_NAME, n_t + n_h), (INDEX_HYP_NAME, n_h)):
            if key not in tabs:
                continue
            o = tabs[key]
            for i in range(cnt):
                q = fix(o + 8 * i)
                if q and q not in seen:
                    seen.add(q)
                    lo = rel(q)
                    m = _U64.unpack_from(t, lo)[0]
                    for j in range(m):
                        fix(lo + 8 + 8 * j)
        if INDEX_NOTATION in tabs:
            fix(tabs[INDEX_NOTATION])
        return bytes(t), hdr_p + delta

    # -- index: rebuild ---------------------------------------------------------
    def _build_index(self, base, p_proof):
        out = bytearray()
        strpos = {}

        def s(name):
            name = name if name is not None else "_"
            if name not in strpos:
                strpos[name] = base + len(out)
                out.extend(name.encode("utf-8") + b"\0")
            return strpos[name]

        for _, nm in self.sorts:
            s(nm)
        for d in self.terms + self.thms:
            s(d.name)
        for d in self.terms + self.thms:
            for v in (d.var_names or ["_"] * len(d.args)):
                s(v)
        for d in self.thms:
            for v in (d.hyp_names or ["_"] * d.num_hyps):
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
        ents = [(INDEX_NAME, p_names), (INDEX_VAR_NAME, p_vars),
                (INDEX_HYP_NAME, p_hyps), (INDEX_DELIMITER, p_delm),
                (INDEX_NOTATION, p_nota)]
        out += _U64.pack(len(ents))
        for ident, p in ents:
            out += ident + struct.pack("<IQ", 0, p)
        return bytes(out), p_index


def write_mmb(mmb, path, index="preserve", reencode=False):
    """Re-emit a parsed MMBFile (possibly with modified tables/statements).

    Statements come from `mmb.iter_stmts()` unless `mmb.override_stmts` is set
    (a list of Stmt-like objects with .op and .body). Tables are re-encoded from
    the decoded model (args/ret/unify lists), not copied. With reencode=True
    every proof stream is also decoded to (op, data) and re-encoded."""
    w = MMBWriter(path)
    for srt in mmb.sorts:
        w.add_sort(srt.mods, srt.name)
    for t in mmb.terms:
        w.add_term(t)
    for t in mmb.thms:
        w.add_thm(t)
    stmts = getattr(mmb, "override_stmts", None) or mmb.iter_stmts()
    for st in stmts:
        cmds = getattr(st, "new_cmds", None)
        if cmds is None and reencode and len(st.body):
            cmds = list(st.cmds())
        if cmds is not None:
            w.add_stmt(st.op, cmds=cmds, old_offset=st.offset)
        else:
            w.add_stmt(st.op, body=st.body, old_offset=st.offset)
    if index == "preserve":
        tail = mmb.tail
        w._old_p_index = mmb.p_index
        w.finish("preserve", tail=tail, tail_offset=mmb.tail_offset)
    else:
        w.finish(index)
