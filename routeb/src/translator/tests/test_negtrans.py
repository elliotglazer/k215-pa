"""SPIKE test: negative+Friedman translation of the `the`-free fragment of
peano.mm1 over the DRAFT hpeano, checked by mm0-c (experimental, not accepted).
Nat terms are translated to graphs, so all 2700 theorems (including those
using `the`) translate.

  python3 -m unittest translator.tests.test_negtrans -v      # from the repo root
"""

import os
import subprocess
import unittest

from translator.mmb_reader import read_mmb
from translator.negtrans import NegTrans

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TOOLS = os.path.join(ROOT, "tools")
BUILD = os.path.join(ROOT, "build")
SPIKE = os.path.join(ROOT, "spike")


def run(*cmd, stdin=None):
    with open(stdin, "rb") if stdin else open(os.devnull, "rb") as f:
        return subprocess.run(cmd, stdin=f, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, cwd=ROOT).returncode


class NegTransTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        os.makedirs(BUILD, exist_ok=True)
        cls.peano = os.path.join(BUILD, "peano.mmb")
        cls.lib = os.path.join(BUILD, "negtrans-lib.mmb")
        assert run(os.path.join(TOOLS, "mm0-rs"), "compile", "foundation/peano.mm1", cls.peano) == 0
        assert run(os.path.join(TOOLS, "mm0-rs"), "compile", "spike/negtrans-lib.mm1", cls.lib) == 0

    def test_lib_checks(self):
        self.assertEqual(run(os.path.join(TOOLS, "mm0-c"), self.lib,
                             stdin=os.path.join(ROOT, "foundation", "hpeano.mm0")), 0)

    def test_translate_all(self):
        tr = NegTrans(read_mmb(self.peano), read_mmb(self.lib))
        tr.run()
        self.assertEqual(tr.stats["thms"], 2700)
        self.assertFalse([k for k in tr.why if k[0] == "thm" and tr.src.thms[k[1]].kind != "axiom"])
        out, spec = os.path.join(BUILD, "negtrans.mmb"), os.path.join(BUILD, "negtrans.mm0")
        tr.write(out, spec, open(os.path.join(ROOT, "foundation", "hpeano.mm0")).read(), True)
        self.assertEqual(run(os.path.join(TOOLS, "mm0-c"), out, stdin=spec), 0)
        bad = os.path.join(BUILD, "negtrans.bad.mmb")
        data = bytearray(open(out, "rb").read())
        data[len(data) // 2] ^= 1
        open(bad, "wb").write(data)
        self.assertNotEqual(run(os.path.join(TOOLS, "mm0-c"), bad, stdin=spec), 0)


if __name__ == "__main__":
    unittest.main()
