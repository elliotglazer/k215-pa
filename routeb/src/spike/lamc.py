"""Tiny lambda -> Hilbert (ax_1/ax_2/ax_mp) compiler for hand-written lemmas.

A lambda term is written as an s-expression string:
  (\\ x M)   abstraction (x is a proof variable for an implication antecedent)
  (M N ...)  application = modus ponens, left-assoc
  name       a proof variable, a hypothesis, or an mm1 proof leaf
  [...]      raw mm1 proof term (inserted verbatim, may not mention lambda vars)
Output: an mm1 proof term using ax_mp, ax_1, ax_2 and id.
"""


def tokenize(s):
    out, i = [], 0
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1
        elif c in "()":
            out.append(c); i += 1
        elif c == "[":
            d, j = 1, i + 1
            while d:
                d += {"[": 1, "]": -1}.get(s[j], 0); j += 1
            out.append(("raw", s[i + 1:j - 1])); i = j
        else:
            j = i
            while j < len(s) and not s[j].isspace() and s[j] not in "()[]":
                j += 1
            out.append(s[i:j]); i = j
    return out


def parse(s):
    toks = tokenize(s)
    pos = [0]

    def p():
        t = toks[pos[0]]; pos[0] += 1
        if t == "(":
            if toks[pos[0]] == "\\":
                pos[0] += 1
                v = toks[pos[0]]; pos[0] += 1
                body = p()
                assert toks[pos[0]] == ")"; pos[0] += 1
                return ("lam", v, body)
            items = []
            while toks[pos[0]] != ")":
                items.append(p())
            pos[0] += 1
            e = items[0]
            for a in items[1:]:
                e = ("app", e, a)
            return e
        if isinstance(t, tuple):
            return ("leaf", t[1])
        return ("var", t)
    e = p()
    assert pos[0] == len(toks), "trailing tokens"
    return e


# combinator terms: ("leaf", s) | ("var", x) | ("app", f, a)
def free(x, m):
    if m[0] == "var":
        return m[1] == x
    if m[0] == "app":
        return free(x, m[1]) or free(x, m[2])
    return False


def abstract(x, m):
    if m[0] == "var" and m[1] == x:
        return ("leaf", "id")
    if not free(x, m):
        return ("app", ("leaf", "ax_1"), m)
    f, a = m[1], m[2]
    if a == ("var", x) and not free(x, f):
        return f
    return ("app", ("app", ("leaf", "ax_2"), abstract(x, f)), abstract(x, a))


def comp(e):
    if e[0] == "lam":
        return abstract(e[1], comp(e[2]))
    if e[0] == "app":
        return ("app", comp(e[1]), comp(e[2]))
    return e


def show(m):
    if m[0] == "app":
        return "(ax_mp %s %s)" % (show(m[1]), show(m[2]))
    if m[0] == "var":
        return m[1]
    return ("(%s)" % m[1]) if " " in m[1] and not m[1].startswith("(") else m[1]


def compile_lam(s):
    return show(comp(parse(s)))


if __name__ == "__main__":
    import sys
    print(compile_lam(sys.argv[1]))
