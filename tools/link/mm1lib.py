"""Shared helpers for the separate-compilation pipeline (tools/link/README.md).

* closure_order(root): the project .mm1 import closure of a module in the exact order pa-mm0/check.py's
  flat_proof_input uses (depth-first, children in import order, post-order), without the vendor file.
* split_statements(text): top-level MM1 statements of a source file, as (start, end) spans that end with
  their ';'. Comments, strings and math strings are skipped, and ';' only ends a statement at bracket depth 0.
* parse_statement(text): (annotation, modifiers, keyword, name) of one statement.
* stub_text(text): a theorem statement turned into an axiom with the same name, binders and type.
"""
import hashlib
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
# LINK_PA / LINK_VENDOR override the module and vendor directories (used by the self-test).
PA = os.environ.get("LINK_PA") or os.path.join(REPO, "pa-mm0")
VENDOR = os.environ.get("LINK_VENDOR") or os.path.join(REPO, "lean-mm0", "vendor")
IMPORT = re.compile(r'^\s*import\s+"([^"]+)"\s*;', re.MULTILINE)
_TOK = re.compile(r'--[^\n]*|"(?:\\.|[^"\\])*"|\$[^$]*\$|[(\[{]|[)\]}]|;')
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
MODS = ("pub", "local", "abstract", "strict", "free", "pure", "provable")


def tool(tools, name):
    """Path of an mm0 tool in TOOLDIR (mm0-rs / mm0-c, with .exe on Windows)."""
    return os.path.join(tools, name + (".exe" if os.name == "nt" else ""))


def default_tools():
    return os.environ.get("MM0TOOLS", "/home/user/mm0-zflr/tools")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


_MEMO = {}


def sha256_memo(path):
    """sha256(path), memoized per process by (path, size, mtime): the tools and the peano interface are hashed for
    every module's cache key, and re-hashing a 20 MB mm0-rs.exe 3,000 times per job is pure waste."""
    st = os.stat(path)
    k = (os.path.abspath(path), st.st_size, st.st_mtime_ns)
    h = _MEMO.get(k)
    if h is None:
        h = _MEMO[k] = sha256(path)
    return h


def read_text(path):
    raw = open(path, "rb").read()
    if b"\r" in raw:
        raise ValueError("MM1 sources require LF line endings: " + path)
    return raw.decode("utf-8")


def closure_order(root, pa=PA):
    """Post-order DFS over .mm1 imports (= check.py flat_proof_input order). Returns (order, imports):
    order = module names (root last), imports = {module: [direct project imports]}. Iterative (no recursion limit;
    import chains of the final roots are hundreds deep and this also runs in worker threads)."""
    vendor = os.path.realpath(os.path.join(VENDOR, "peano.mm1"))
    rpa = os.path.realpath(pa)
    seen, order, imports = set(), [], {}

    def enter(path):
        path = os.path.realpath(path)
        if path in seen:
            return None
        seen.add(path)
        if path == vendor:
            return None
        if not path.endswith(".mm1") or os.path.dirname(path) != rpa:
            raise ValueError("unexpected project import " + path)
        kids = [os.path.realpath(os.path.join(os.path.dirname(path), c)) for c in IMPORT.findall(read_text(path))]
        return [os.path.basename(path)[:-4], kids, 0]

    stack = [enter(os.path.join(pa, root + ".mm1"))]
    while stack:
        f = stack[-1]
        if f[2] < len(f[1]):
            f[2] += 1
            g = enter(f[1][f[2] - 1])
            if g:
                stack.append(g)
        else:
            stack.pop()
            imports[f[0]] = [os.path.basename(c)[:-4] for c in f[1] if c != vendor]
            order.append(f[0])
    return order, imports


def sub_order(imports, m):
    """closure_order(m) computed from an imports map that contains m's closure (no file reads)."""
    seen, out = {m}, []
    stack = [(m, 0)]
    while stack:
        x, i = stack[-1]
        kids = imports[x]
        if i < len(kids):
            stack[-1] = (x, i + 1)
            if kids[i] not in seen:
                seen.add(kids[i])
                stack.append((kids[i], 0))
        else:
            stack.pop()
            out.append(x)
    return out


def split_statements(text):
    """Yield (start, end) of each top-level statement; end is just past its ';'."""
    depth, start = 0, None
    for m in _TOK.finditer(text):
        t = m.group()
        c = t[0]
        if c == "-" or c == '"':
            continue
        if start is None:
            start = m.start()
        if c == "$":
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ";" and depth == 0:
            yield start, m.end()
            start = None
    if start is not None and text[start:].strip():
        raise ValueError("unterminated statement at offset %d" % start)


def strip_comments(s):
    out, last = [], 0
    for m in _TOK.finditer(s):
        if m.group().startswith("--"):
            out.append(s[last:m.start()])
            last = m.end()
    out.append(s[last:])
    return "".join(out)


def statements(text):
    """[(keyword, name, stmt_text)] for a whole file; stmt_text has comments removed and is stripped."""
    out = []
    prev = 0
    for a, b in split_statements(text):
        s = strip_comments(text[prev:b]).strip()
        prev = b
        if not s:
            continue
        kw, name = parse_statement(s)[2:]
        out.append((kw, name, s))
    return out


def parse_statement(s):
    """(annotations, modifiers, keyword, name) of a comment-free statement."""
    i, ann = 0, []
    while s.startswith("@", i):
        j = i + 1
        if s[j] in "([{":
            depth = 0
            for m in _TOK.finditer(s, j):
                t = m.group()
                if t[0] in "([{":
                    depth += 1
                elif t[0] in ")]}":
                    depth -= 1
                    if depth == 0:
                        j = m.end()
                        break
        else:
            while j < len(s) and not s[j].isspace():
                j += 1
        ann.append(s[i:j])
        i = j
        while i < len(s) and s[i].isspace():
            i += 1
    rest = s[i:]
    mods = []
    m = re.match(r"\s*(\w+)", rest)
    while m and m.group(1) in MODS:
        mods.append(m.group(1))
        rest = rest[m.end():]
        m = re.match(r"\s*(\w+)", rest)
    kw = m.group(1) if m else None
    rest = rest[m.end():] if m else rest
    n = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)", rest)
    name = n.group(1) if n and kw in ("theorem", "axiom", "def", "term", "sort", "notation", "infixl",
                                       "infixr", "prefix", "coercion") else None
    return ann, mods, kw, name


def stub_text(s):
    """'[@a] [pub] theorem N BIS: TYPE = PROOF;' -> '[@a] axiom N BIS: TYPE;'. Annotations are kept: peano.mm1
    registers equality theorems by annotating them (@(register-eqd ..)), and later tactics depend on it."""
    ann, mods, kw, name = parse_statement(s)
    assert kw == "theorem", s[:80]
    k = re.search(r"\btheorem\s", s).end()
    depth = 0
    for m in re.finditer(r'"(?:\\.|[^"\\])*"|\$[^$]*\$|[(\[{]|[)\]}]|=', s[k:]):
        t = m.group()
        if t[0] in "([{":
            depth += 1
        elif t[0] in ")]}":
            depth -= 1
        elif t == "=" and depth == 0:
            return "".join(a + " " for a in ann) + "axiom " + s[k:k + m.start()].rstrip() + ";"
    raise ValueError("theorem without a proof: " + s[:120])


def idents(s):
    """Identifier-like tokens of a statement (over-approximates the names it can refer to)."""
    return set(_IDENT.findall(s))
