"""End-to-end tests on foundation/peano.mm1.

Run from the repo root:  python3 -m unittest translator.tests.test_peano -v
"""

import os
import subprocess
import unittest

from translator import read_mmb, write_mmb, build_stmt_dag, decode_unify, MMBFile
from translator.mmb_format import PROOF_THM, PROOF_THM_SAVE, PROOF_SAVE, unpack_cmd, CMD_END
from translator.__main__ import stats

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOOLS = os.path.join(ROOT, "tools")
BUILD = os.path.join(ROOT, "build")
MM1 = os.path.join(ROOT, "foundation", "peano.mm1")
MM0 = os.path.join(ROOT, "foundation", "peano.mm0")
MMB = os.path.join(BUILD, "peano.mmb")


def mm0c(path):
    with open(MM0, "rb") as f:
        r = subprocess.run([os.path.join(TOOLS, "mm0-c"), path], stdin=f,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return r.returncode, r.stderr.decode("utf-8", "replace")


def canon(nodes, n, memo):
    if n not in memo:
        nd = nodes[n]
        if nd[0] == "var":
            memo[n] = ("v", nd[1])
        elif nd[0] == "dummy":
            memo[n] = ("d", n)
        else:
            memo[n] = ("a", nd[1], tuple(canon(nodes, a, memo) for a in nd[2]))
    return memo[n]


class PeanoMMB(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        os.makedirs(BUILD, exist_ok=True)
        r = subprocess.run([os.path.join(TOOLS, "mm0-rs"), "compile", MM1, MMB],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert r.returncode == 0, r.stdout.decode()
        assert mm0c(MMB)[0] == 0
        cls.mmb = read_mmb(MMB)

    def test_counts(self):
        s = stats(self.mmb)
        print("\npeano.mmb:", s)
        self.assertEqual(s["sorts"], 3)
        self.assertEqual(s["terms"] + s["defs"], 170)
        self.assertEqual(s["axioms"] + s["theorems"], 2726)
        self.assertEqual(s["axioms"], 26)
        self.assertEqual([x.name for x in self.mmb.sorts], ["wff", "nat", "set"])

    def test_dag_matches_statements(self):
        """Proof-stream DAG conclusions/hyps equal the table unify streams."""
        m = self.mmb
        for st in m.iter_stmts():
            if st.kind in ("sort", "term"):
                self.assertEqual(len(st.body), 0)
                continue
            dag = build_stmt_dag(m, st)
            self.assertFalse(any(isinstance(n, tuple) and n[0] == "hole"
                                 for n in dag.nodes), st)
            is_def = st.kind in ("def", "local_def")
            d = m.terms[st.ref] if is_def else m.thms[st.ref]
            nodes, root, hyps = decode_unify(m, d)
            res = dag.result[1] if dag.result[0] == "E" else dag.result[2]
            if is_def:
                if d.dummies:
                    continue
            else:
                self.assertEqual(len(hyps), len(dag.hyps), d)
                for a, b in zip(hyps, dag.hyps):
                    self.assertEqual(canon(nodes, a, {}), canon(dag.nodes, b, {}), d)
            self.assertEqual(canon(nodes, root, {}), canon(dag.nodes, res, {}), d)

    def test_roundtrip_bytes(self):
        out = os.path.join(BUILD, "peano.rt.mmb")
        write_mmb(self.mmb, out, index="preserve", reencode=True)
        with open(MMB, "rb") as a, open(out, "rb") as b:
            self.assertEqual(a.read(), b.read())
        self.assertEqual(mm0c(out)[0], 0)

    def test_roundtrip_rebuilt_index(self):
        for mode in ("rebuild", "none"):
            out = os.path.join(BUILD, "peano.rt-%s.mmb" % mode)
            write_mmb(self.mmb, out, index=mode, reencode=True)
            self.assertEqual(mm0c(out)[0], 0, mode)
            m2 = read_mmb(out)
            self.assertEqual(stats(m2), stats(self.mmb))
            if mode == "rebuild":
                self.assertEqual([t.name for t in m2.thms], [t.name for t in self.mmb.thms])
                self.assertEqual([t.var_names for t in m2.terms],
                                 [t.var_names for t in self.mmb.terms])
                self.assertEqual([t.hyp_names for t in m2.thms],
                                 [t.hyp_names for t in self.mmb.thms])

    def test_preserve_index_relocation(self):
        """A size-changing but valid edit (extra Save at the end of a proof)
        keeps mm0-c happy and the relocated index still names everything."""
        m = MMBFile.open(MMB)
        stmts = m.stmts()
        for s in stmts:
            if s.kind in ("thm", "local_thm") and s.ref in (200, 201):
                s.new_cmds = list(s.cmds()) + [(PROOF_SAVE, 0)]
        m.override_stmts = stmts
        out = os.path.join(BUILD, "peano.reloc.mmb")
        write_mmb(m, out, index="preserve")
        self.assertEqual(mm0c(out)[0], 0)
        m2 = read_mmb(out)
        grow = os.path.getsize(out) - os.path.getsize(MMB)
        self.assertTrue(grow > 0 and grow % 8 == 0, grow)
        self.assertEqual([t.name for t in m2.thms], [t.name for t in self.mmb.thms])
        self.assertEqual([t.var_names for t in m2.thms], [t.var_names for t in self.mmb.thms])
        self.assertEqual([t.hyp_names for t in m2.thms], [t.hyp_names for t in self.mmb.thms])

    def _first_thm_cmd(self):
        """File offset of the data byte of a Thm command inside a theorem proof."""
        m = self.mmb
        for st in m.iter_stmts():
            if st.kind != "thm" or st.ref < 100:
                continue
            body_off = st.offset + unpack_cmd(m.data, st.offset)[2]
            pos = body_off
            while True:
                op, data, sz = unpack_cmd(m.data, pos)
                if op == CMD_END:
                    break
                if op in (PROOF_THM, PROOF_THM_SAVE) and sz == 2 and data > 10:
                    return st, pos + 1
                pos += sz

    def test_negative_corrupt_byte(self):
        st, off = self._first_thm_cmd()
        with open(MMB, "rb") as f:
            b = bytearray(f.read())
        b[off] ^= 0x01          # cite a different theorem
        out = os.path.join(BUILD, "peano.bad.mmb")
        with open(out, "wb") as f:
            f.write(b)
        rc, err = mm0c(out)
        self.assertNotEqual(rc, 0)
        print("\ncorrupted byte %#x in %s: mm0-c exit %d: %s" % (
            off, self.mmb.thms[st.ref].name, rc,
            [l for l in err.splitlines() if l.strip()][:2]))

    def test_negative_via_writer(self):
        """Dropping one command from a proof through the model is rejected."""
        m = MMBFile.open(MMB)
        stmts = m.stmts()
        victim = next(s for s in stmts if s.kind == "thm" and s.ref > 100)
        cmds = list(victim.cmds())
        victim.new_cmds = cmds[:-1]
        m.override_stmts = stmts
        out = os.path.join(BUILD, "peano.bad2.mmb")
        write_mmb(m, out, index="rebuild")
        self.assertNotEqual(mm0c(out)[0], 0)


if __name__ == "__main__":
    unittest.main()
