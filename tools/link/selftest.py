"""Self-test of the separate-compilation pipeline on a toy project (a few seconds).

  python3 selftest.py [--tools TOOLDIR] [--vendor DIR]

Toy modules in a temporary pa-mm0-like directory (vendor peano copied in): a diamond (a <- b, a <- c, b c <- r)
using a private theorem, a derive-eq'd def and its derived *eq theorem, a Lisp definition from a `do` block, a
register-eqd registration and a local def across modules. Cases:
  ok          build + link + mm0-c pass, false control rejected, 26 axioms
  stub        a stub's statement altered in one module's input   -> linker rejects ("statement differs")
  stub-mm0c   the same with the linker's comparison disabled      -> mm0-c rejects
  def         a def body altered in one module's input, with a theorem of that module unfolding the altered
              body                                                 -> linker rejects ("body differs")
  def-mm0c    the same with the linker's comparison disabled       -> mm0-c rejects (the theorem is checked
              against the original body)
  axiom       an extra axiom in a module                           -> linker rejects
  clash       a module redeclaring a (pruned-away) private theorem of its closure -> compile_one rejects
  missing     a module not built                                   -> linker rejects
  reader      a do block reading a dependency theorem's proof with get-decl and adding a theorem (d), replayed
              by an importer (e)                                   -> build + link + mm0-c pass
Exit 0 iff every case behaves as stated.
"""
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

MODS = {
    "a": ('import "../vendor/peano.mm1";\n'
          'do { (def (toy-tac) (quote (a1i id))) };\n'
          '@_ def toyAdd (x y: nat): nat = $ x + y $;\n'
          '@_ local def toyLoc (x: nat): nat = $ x * x $;\n'
          'theorem toyPriv (p q: wff): $ q -> p -> p $ = (quote (a1i id));\n'
          'pub theorem toyPub (p q: wff): $ q -> p -> p $ = (quote toyPriv);\n'),
    "b": ('import "a.mm1";\n'
          'theorem toyB1 (p q r: wff): $ r -> q -> p -> p $ = (quote (a1i toyPriv));\n'
          'pub theorem toyB (x y z: nat): $ x = y -> toyAdd x z = toyAdd y z $ = (quote toyAddeq1);\n'),
    "c": ('import "a.mm1";\n'
          'theorem toyC1 (p q: wff): $ q -> p -> p $ = (toy-tac);\n'
          'theorem toyC (x y: nat): $ x = y -> toyLoc x = toyLoc y $ = (quote toyLoceq);\n'
          'theorem toyC2 (x: nat): $ toyLoc x = x * x $ = (quote eqid);\n'),
    "r": ('import "b.mm1";\nimport "c.mm1";\n'
          'pub theorem toyR (p q r: wff): $ r -> q -> p -> p $ = (quote toyB1);\n'),
    # proof reader (README 4.8): d's do block reads the proof of a's toyPub with get-decl and adds toyPubCopy;
    # e replays that block (do blocks are kept) and uses the generated theorem.
    "d": ('import "a.mm1";\n'
          'do { (def (toy-copy t new) (match (get-decl t) [(\'theorem _ bis hs ret _ pf) '
          '(add-thm! new bis hs ret () pf)])) };\n'
          'do (toy-copy \'toyPub \'toyPubCopy);\n'
          'theorem toyD (p q: wff): $ q -> p -> p $ = (quote toyPubCopy);\n'),
    "e": ('import "d.mm1";\n'
          'pub theorem toyE (p q: wff): $ q -> p -> p $ = (quote toyPubCopy);\n'),
}
SPECS = {
    "a": 'import "../vendor/peano.mm0";\ndef toyAdd (x y: nat): nat = $ x + y $;\n'
         'theorem toyPub (p q: wff): $ q -> p -> p $;\n',
    "b": 'import "a.mm0";\ntheorem toyB (x y z: nat): $ x = y -> toyAdd x z = toyAdd y z $;\n',
    "c": 'import "a.mm0";\n',
    "r": 'import "b.mm0";\nimport "c.mm0";\ntheorem toyR (p q r: wff): $ r -> q -> p -> p $;\n',
    "d": 'import "a.mm0";\n',
    "e": 'import "d.mm0";\ntheorem toyE (p q: wff): $ q -> p -> p $;\n',
}


# compile_one.Plan.select must give exactly what the per-module reference selection gives (run in the toy env).
PLAN_CHECK = """
import os, sys
sys.path.insert(0, %r)
import compile_one as C, mkiface, mm1lib as L
P = C.Plan("r", sys.argv[1])
for m in P.order:
    deps = L.sub_order(P.imports, m)[:-1]
    own = L.strip_comments(L.IMPORT.sub("", L.read_text(os.path.join(L.PA, m + ".mm1"))))
    ref = C.select_flat([(d, mkiface.items(d)) for d in deps], own, False)
    assert P.select(m, deps, own, False) == (ref[0], ref[1]), m
print("plan == select_flat for", len(P.order), "modules")
""" % HERE


def write(path, text):
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def main():
    a = sys.argv[1:]
    tools = a[a.index("--tools") + 1] if "--tools" in a else os.environ.get("MM0TOOLS", "/home/user/mm0-zflr/tools")
    tool = lambda n: os.path.join(tools, n + (".exe" if os.name == "nt" else ""))
    # the pinned peano files: --vendor DIR, else $LINK_VENDOR, else <repo>/lean-mm0/vendor
    src_vendor = (a[a.index("--vendor") + 1] if "--vendor" in a else
                  os.environ.get("LINK_VENDOR") or os.path.join(REPO, "lean-mm0", "vendor"))
    tmp = tempfile.mkdtemp(prefix="linktest")
    pa, vendor, bdir = os.path.join(tmp, "pa"), os.path.join(tmp, "vendor"), os.path.join(tmp, "build")
    os.makedirs(pa)
    os.makedirs(vendor)
    for ext in ("mm0", "mm1", "mmu"):
        shutil.copy(os.path.join(src_vendor, "peano." + ext), vendor)
    for m in MODS:
        write(os.path.join(pa, m + ".mm1"), MODS[m])
        write(os.path.join(pa, m + ".mm0"), SPECS[m])
    env = dict(os.environ, LINK_PA=pa, LINK_VENDOR=vendor, MM0TOOLS=tools)
    py = sys.executable

    def sh(*cmd, extra=None):
        e = dict(env, **(extra or {}))
        r = subprocess.run([py] + list(cmd), env=e, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    def recompile(m, edit):
        """Rewrite module m's assembled input with edit(text) and recompile it in place (bypassing the cache)."""
        inp = os.path.join(bdir, m, "input.mm1")
        with open(inp, encoding="utf-8") as f:
            t = f.read()
        t2 = edit(t)
        assert t2 != t, "edit did not apply"
        write(inp, t2)
        r = subprocess.run([tool("mm0-rs"), "compile", "--cache=false", "input.mm1", m + ".mmb"],
                           cwd=os.path.join(bdir, m), capture_output=True, text=True)
        assert r.returncode == 0, r.stdout + r.stderr

    def lc():
        return sh(os.path.join(HERE, "link_check.py"), "r", "--build", bdir, "--tools", tools)

    results = []

    def case(name, rc, out, want_ok, needle=None):
        good = (rc == 0) == want_ok and (needle is None or needle in out)
        results.append((name, good))
        print("%-10s %s%s" % (name, "ok" if good else "UNEXPECTED", "" if good else "\n" + out[-3000:]))

    rc, out = sh(os.path.join(HERE, "build_all.py"), "r", "--build", bdir, "-j", "2", "--keep-input")
    case("build", rc, out, True)
    rc, out = sh("-c", PLAN_CHECK, bdir)
    case("plan", rc, out, True, "plan == select_flat")
    rc, out = lc()
    case("ok", rc, out, True, '"spec_identical_to_joined": true')
    # stub altered: b's interface copy of toyPriv gets an extra hypothesis-free variant statement
    backup = os.path.join(tmp, "b.mmb")
    shutil.copy(os.path.join(bdir, "b", "b.mmb"), backup)
    alter = lambda t: t.replace("axiom toyPriv (p q: wff): $ q -> p -> p $;", "axiom toyPriv (p q: wff): $ p -> q -> q $;")
    recompile("b", alter)
    rc, out = lc()
    case("stub", rc, out, False, "statement differs")
    rc, out = sh(os.path.join(HERE, "link_check.py"), "r", "--build", bdir, "--tools", tools,
                 extra={"LINKN_TEST_NO_VERIFY": "1"})
    case("stub-mm0c", rc, out, False, "mm0-c rejected")
    shutil.copy(backup, os.path.join(bdir, "b", "b.mmb"))
    shutil.copy(os.path.join(bdir, "c", "c.mmb"), backup)
    recompile("c", lambda t: t.replace("@_ local def toyLoc (x: nat): nat = $ x * x $;",
                                       "@_ local def toyLoc (x: nat): nat = $ x + x $;").replace(
                                       "$ toyLoc x = x * x $", "$ toyLoc x = x + x $"))
    rc, out = lc()
    case("def", rc, out, False, "body differs")
    rc, out = sh(os.path.join(HERE, "link_check.py"), "r", "--build", bdir, "--tools", tools,
                 extra={"LINKN_TEST_NO_VERIFY": "1"})
    case("def-mm0c", rc, out, False, "mm0-c rejected")
    shutil.copy(backup, os.path.join(bdir, "c", "c.mmb"))
    shutil.copy(os.path.join(bdir, "r", "r.mmb"), backup)
    recompile("r", lambda t: t + "axiom toyFalse: $ F. $;\n")
    rc, out = lc()
    case("axiom", rc, out, False, "has no theorem of that name")
    shutil.copy(backup, os.path.join(bdir, "r", "r.mmb"))
    rc, out = lc()
    case("restored", rc, out, True)
    write(os.path.join(pa, "x.mm1"), 'import "b.mm1";\ntheorem toyPriv (p q: wff): $ q -> p -> p $ = '
                                     '(quote (a1i id));\n')
    rc, out = sh(os.path.join(HERE, "compile_one.py"), "--build", bdir, "x")
    case("clash", rc, out, False, "redeclares")
    os.remove(os.path.join(bdir, "c", "link.json"))
    rc, out = lc()
    case("missing", rc, out, False, "link failed")
    rc, out = sh(os.path.join(HERE, "build_all.py"), "e", "--build", bdir, "-j", "2")
    if rc == 0:
        rc, out = sh(os.path.join(HERE, "link_check.py"), "e", "--build", bdir, "--tools", tools)
    case("reader", rc, out, True, '"spec_identical_to_joined": true')
    shutil.rmtree(tmp)
    return 0 if all(g for _, g in results) else 1


if __name__ == "__main__":
    sys.exit(main())
