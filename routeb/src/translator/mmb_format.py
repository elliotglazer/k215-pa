"""MMB binary format: constants and command encoding/decoding.

Reference: digama0/mm0 `mm0-c/types.c`, `mm0-c/verifier.c`,
`mm0-rs/components/mm0b_parser`, `mm0-rs/src/mmb/export.rs`.
All integers are little-endian.
"""

import struct

MM0B_MAGIC = b"MM0B"
MM0B_VERSION = 1
MAX_SORTS = 128
MAX_BOUND_VARS = 55
HEADER_SIZE = 40          # fixed part of the header, before the sort bytes
CMD_MAX_SIZE = 5

# sort modifiers (one byte per sort in the header)
SORT_PURE = 1
SORT_STRICT = 2
SORT_PROVABLE = 4
SORT_FREE = 8

# binder / type words (u64)
TYPE_DEPS_MASK = (1 << 55) - 1
TYPE_BOUND_MASK = 1 << 63

# command data-size field (high two bits of the opcode byte)
DATA_0, DATA_8, DATA_16, DATA_32 = 0x00, 0x40, 0x80, 0xC0
DATA_MASK = 0xC0

# statement commands
CMD_END = 0x00
STMT_AXIOM = 0x02
STMT_SORT = 0x04
STMT_TERM = 0x05          # same opcode as STMT_DEF; term vs def is the table's high sort bit
STMT_DEF = 0x05
STMT_THM = 0x06
STMT_LOCAL = 0x08
STMT_LOCAL_DEF = 0x0D
STMT_LOCAL_THM = 0x0E

# proof commands
PROOF_TERM = 0x10
PROOF_TERM_SAVE = 0x11
PROOF_REF = 0x12
PROOF_DUMMY = 0x13
PROOF_THM = 0x14
PROOF_THM_SAVE = 0x15
PROOF_HYP = 0x16
PROOF_CONV = 0x17
PROOF_REFL = 0x18
PROOF_SYMM = 0x19
PROOF_CONG = 0x1A
PROOF_UNFOLD = 0x1B
PROOF_CONV_CUT = 0x1C
PROOF_CONV_SAVE = 0x1E
PROOF_SAVE = 0x1F
PROOF_SORRY = 0x20

# unify commands
UNIFY_TERM = 0x30
UNIFY_TERM_SAVE = 0x31
UNIFY_REF = 0x32
UNIFY_DUMMY = 0x33
UNIFY_HYP = 0x36

# index table ids
INDEX_NAME = b"Name"
INDEX_VAR_NAME = b"VarN"
INDEX_HYP_NAME = b"HypN"
INDEX_NOTATION = b"Nota"
INDEX_DELIMITER = b"Delm"
INDEX_LISP = b"Lisp"
INDEX_DEP = b"Deps"

STMT_NAMES = {
    STMT_AXIOM: "axiom", STMT_SORT: "sort", STMT_DEF: "term/def",
    STMT_THM: "thm", STMT_LOCAL_DEF: "local_def", STMT_LOCAL_THM: "local_thm",
}
PROOF_NAMES = {
    PROOF_TERM: "Term", PROOF_TERM_SAVE: "TermSave", PROOF_REF: "Ref",
    PROOF_DUMMY: "Dummy", PROOF_THM: "Thm", PROOF_THM_SAVE: "ThmSave",
    PROOF_HYP: "Hyp", PROOF_CONV: "Conv", PROOF_REFL: "Refl",
    PROOF_SYMM: "Symm", PROOF_CONG: "Cong", PROOF_UNFOLD: "Unfold",
    PROOF_CONV_CUT: "ConvCut", PROOF_CONV_SAVE: "ConvSave",
    PROOF_SAVE: "Save", PROOF_SORRY: "Sorry", CMD_END: "End",
}
UNIFY_NAMES = {
    UNIFY_TERM: "UTerm", UNIFY_TERM_SAVE: "UTermSave", UNIFY_REF: "URef",
    UNIFY_DUMMY: "UDummy", UNIFY_HYP: "UHyp", CMD_END: "End",
}


class MMBError(Exception):
    pass


_U16 = struct.Struct("<H")
_U32 = struct.Struct("<I")


def unpack_cmd(buf, pos):
    """Decode one command at buf[pos]. Returns (opcode, data, size).

    opcode is the low 6 bits; data is 0 for a 0-width command."""
    b = buf[pos]
    w = b & DATA_MASK
    op = b & 0x3F
    if w == DATA_0:
        return op, 0, 1
    if w == DATA_8:
        return op, buf[pos + 1], 2
    if w == DATA_16:
        return op, _U16.unpack_from(buf, pos + 1)[0], 3
    return op, _U32.unpack_from(buf, pos + 1)[0], 5


def iter_cmds(buf, pos=0, end=None):
    """Yield (opcode, data) for a command stream up to and including End.

    Stops after the first End command (or at `end`)."""
    if end is None:
        end = len(buf)
    while pos < end:
        op, data, sz = unpack_cmd(buf, pos)
        pos += sz
        yield op, data
        if op == CMD_END:
            return


def encode_cmd(op, data, out):
    """Append a proof/unify command with minimal data width (as mm0-rs `write_cmd`)."""
    if data == 0:
        out.append(op)
    elif data < 0x100:
        out.append(op | DATA_8)
        out.append(data)
    elif data < 0x10000:
        out.append(op | DATA_16)
        out += _U16.pack(data)
    else:
        out.append(op | DATA_32)
        out += _U32.pack(data)


def encode_cmds(cmds):
    """Encode an iterable of (op, data) to bytes (caller includes the End command)."""
    out = bytearray()
    for op, data in cmds:
        encode_cmd(op, data, out)
    return bytes(out)


def encode_stmt(op, body):
    """Statement command with a forward length (as mm0-rs `write_cmd_bytes`)."""
    n = len(body)
    if n + 2 < 0x100:
        return bytes((op | DATA_8, n + 2)) + body
    if n + 3 < 0x10000:
        return bytes((op | DATA_16,)) + _U16.pack(n + 3) + body
    if n + 5 >= 1 << 32:
        raise MMBError("statement too large for MMB format")
    return bytes((op | DATA_32,)) + _U32.pack(n + 5) + body


def type_word(bound, sort, deps):
    return (TYPE_BOUND_MASK if bound else 0) | (sort << 56) | deps


def type_bound(ty):
    return bool(ty & TYPE_BOUND_MASK)


def type_sort(ty):
    return (ty >> 56) & 0x7F


def type_deps(ty):
    return ty & TYPE_DEPS_MASK
