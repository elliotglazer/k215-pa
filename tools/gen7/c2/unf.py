"""Unfold a reflected code def to gen7 code constructors (input of gen_tsch_inst.py).

  python3 unf.py SRC.mmb CODEDEF OUT.txt [--keep]

Reflects SRC.mmb (pass 1 only), then prints CODEDEF A0 A1 .. fully unfolded with a fresh name per binder.
With --keep the codes of peano's an / or / ex (can, cor, cex) are kept as nodes, so the generator can read the
connective structure off the code (it expands them itself)."""
import sys
sys.path.insert(0, '/home/user/k215-pa-mm0/.claude/worktrees/agent-adc913e38b309817b/tools/gen7')
sys.setrecursionlimit(100000)
import refl, refl_lib, perdef
src = refl.read_mmb(sys.argv[1])
keep = {'can', 'cor', 'cex'} if '--keep' in sys.argv else set()
r = refl_lib.ReflDry(src)
r.run(None, frozenset())
pd = perdef.PerDef(r)
name = sys.argv[2]
oid = r.tname[name]
a = [perdef.lit("A%d" % i) for i in range(len(r.info[oid].kinds))]
ctr = [0]
def unf(e):
    if e[0] == 'lit':
        return e
    h = e[1]
    if h in keep:
        return ('app', h, [unf(c) for c in e[2]])
    if h in r.tname and r.terms[r.tname[h]].is_def:
        o = r.tname[h]
        inf = r.info.get(o)
        if inf and inf.tpl:
            ch = [unf(c) for c in e[2]]
            Z = []
            for _ in range(inf.ndum):
                ctr[0] += 1
                Z.append(perdef.lit(str(ctr[0])))
            return unf(pd.inst(pd.tpl(o), ch, Z))
    return ('app', h, [unf(c) for c in e[2]])
body = unf(('app', name, a))
s = perdef.pr(body)
print(len(s), ctr[0])
open(sys.argv[3], 'w').write(s)
