"""B6 driver rehearsal: b6/b6.py --rehearsal on the B4 statements-stage .mmb
(real K215 material: k215_literal_tm, zfc_proofs closures, bd defs, B4 proofs).

  python3 -m unittest translator.tests.test_b6 -v     # from the repo root; needs b4/build.sh first
"""
import json
import os
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "build", "b4", "stmt", "pa-mm0", "b4_statements_check.mmb")
OUT = os.path.join(ROOT, "build", "b6-test")


@unittest.skipUnless(os.path.isfile(SRC), "run b4/build.sh first (builds %s)" % SRC)
class B6RehearsalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rc = subprocess.run([sys.executable, "-B", "-I", os.path.join(ROOT, "b6", "b6.py"),
                                 "--src", SRC, "--out", OUT, "--tools", os.path.join(ROOT, "tools"),
                                 "--rehearsal"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT).returncode
        cls.rep = json.load(open(os.path.join(OUT, "report.json")))

    def test_pass(self):
        self.assertEqual(self.rc, 0)
        self.assertEqual(self.rep["result"], "PASS")
        self.assertEqual(self.rep["mm0c"]["exit"], 0)
        self.assertTrue(self.rep["control"]["rejected"])
        self.assertEqual(self.rep["translation"]["theorems_failed"], 0)

    def test_statements(self):
        names = [p["name"] for p in self.rep["final_public_theorems"]]
        self.assertEqual(names, ["K215_sigma1", "K215_sigma2"])
        for p in self.rep["final_public_theorems"]:
            self.assertTrue(p["is_approved_text_plus_hT"])


if __name__ == "__main__":
    unittest.main()


B5_SRC = os.path.join(ROOT, "build", "b5-src.mmb")
B5_LIB = os.path.join(ROOT, "build", "b5-lib.mmb")


@unittest.skipUnless(os.path.isfile(B5_SRC) and os.path.isfile(B5_LIB), "run b5/gen_b5.py first")
class B6FinalModeTest(unittest.TestCase):
    """The final-mode path of the driver (no hypothesis, spec line = the given
    approved text verbatim) on B5's synthetic Pi2 theorem tsig1, which is
    proved in peano: A. h (tAll h -> E. w tEv w)."""

    def test_final_mode(self):
        sys.path.insert(0, os.path.join(ROOT, "b6"))
        sys.path.insert(0, os.path.join(ROOT, "b5"))
        import b6
        import gen_b5
        out = os.path.join(ROOT, "build", "b6-final-test")
        os.makedirs(out, exist_ok=True)
        spec = open(os.path.join(ROOT, "foundation", "hpeano.mm0")).read() + gen_b5.bd_body() + gen_b5.TEST_DEFS
        line = "theorem tsig1 {h w: nat}: $ A. h (tAll h -> E. w tEv w) $;"
        rep = {"tools": {"mm0-c": [None, None]}}
        rc = b6.drive(rep, lambda: None, B5_SRC, out, os.path.join(ROOT, "tools", "mm0-c"), B5_LIB, spec,
                      {"tsig1": ("--| synthetic", line)},
                      [("tsig1", "rec_tsig1", "tsig1", None, "tAll", "tEv")], False)
        self.assertEqual(rc, 0)
        self.assertEqual(rep["result"], "PASS")
        self.assertTrue(rep["control"]["rejected"])
        [p] = rep["final_public_theorems"]
        self.assertTrue(p["is_approved_text"])
        self.assertEqual(p["spec_text"], line)
        self.assertEqual(rep["limits"], "stock")
        self.assertEqual(rep["translation"]["mm0c_limits"]["hyps"], 256)

    def test_final_mode_capacity3(self):
        """--limits capacity3 only raises the translator's pre-filter (hyps, ustack 4096); the output is
        still checked by mm0-c, here the stock build, which accepts it since tsig1 is small."""
        sys.path.insert(0, os.path.join(ROOT, "b6"))
        sys.path.insert(0, os.path.join(ROOT, "b5"))
        import b6
        import gen_b5
        from translator.negtrans import LIMITS
        out = os.path.join(ROOT, "build", "b6-final-test-c3")
        os.makedirs(out, exist_ok=True)
        spec = open(os.path.join(ROOT, "foundation", "hpeano.mm0")).read() + gen_b5.bd_body() + gen_b5.TEST_DEFS
        line = "theorem tsig1 {h w: nat}: $ A. h (tAll h -> E. w tEv w) $;"
        rep = {"tools": {"mm0-c": [None, None]}}
        try:
            rc = b6.drive(rep, lambda: None, B5_SRC, out, os.path.join(ROOT, "tools", "mm0-c"), B5_LIB, spec,
                          {"tsig1": ("--| synthetic", line)},
                          [("tsig1", "rec_tsig1", "tsig1", None, "tAll", "tEv")], False, "capacity3")
        finally:
            LIMITS.update(b6.CHECKER_LIMITS["stock"])
        self.assertEqual(rc, 0)
        self.assertEqual(rep["result"], "PASS")
        self.assertEqual(rep["limits"], "capacity3")
        self.assertEqual((rep["translation"]["mm0c_limits"]["hyps"], rep["translation"]["mm0c_limits"]["ustack"]),
                         (4096, 4096))
        self.assertEqual(rep["translation"]["root_failure_kinds"], [])
