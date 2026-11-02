"""B6b (K215 Theorems 2/3 and G2): the b4b target set of b6/b6.py, its library, and B5
recovery of the five B4b shapes.

  python3 -m unittest translator.tests.test_b6b -v     # from the repo root

- ApprovedTextTest: the b4b target set reads the seven approved one-line statements
  verbatim (no build needed).
- B5ShapesTest: b5/gen_b5.py --b4b (bd_certs.mm0 + bd_certs_b4b.mm0 over hpeano, the five
  B4b shapes with the statement as hypothesis, recovered and checked by mm0-c; ~1 min).
- LinkedRehearsalTest / LinkedFinalTest (skipped unless B6B_SRC names a .mmb): b6.py --set
  b4b on a LINKED .mmb (K215 tools/link pipeline) of a root importing b4_sigma, b4b_bb and
  b4g2_final, i.e. the real B4/B4b proofs over the real K215 closure (b4/k215-drop/local/check_local.sh):
  rehearsal = all seven targets from their `_of` forms (hT kept); final = K215_thm2_pi2b,
  which b4b_bb proves unconditionally, hypothesis-free with the approved text.
"""
import json
import os
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MM0C = os.path.join(ROOT, "tools", "mm0-c")
SRC = os.environ.get("B6B_SRC", "")
sys.path.insert(0, os.path.join(ROOT, "b6"))
sys.path.insert(0, os.path.join(ROOT, "b5"))


def read(rel):
    return open(os.path.join(ROOT, rel), newline="").read()


class ApprovedTextTest(unittest.TestCase):
    def test_targets(self):
        import b6
        cfg = b6.SETS["b4b"]
        ap = b6.approved_lines("\n".join(read(r) for r in cfg["stmts"]), cfg["targets"])
        self.assertEqual(list(ap), ["K215_sigma1", "K215_sigma2", "K215_thm2_pi2a", "K215_thm2_pi2b",
                                    "K215_thm3_pi2a", "K215_thm3_pi2b", "K215_G2_pi2"])
        for name, (doc, line) in ap.items():
            self.assertTrue(doc.startswith("--| "), name)
            self.assertIn("\n" + line + "\n", "\n" + read("b4/b4_statements.mm0") + read("b4/b4b_statements.mm0"))
        self.assertEqual(ap["K215_thm2_pi2b"][1],
                         "theorem K215_thm2_pi2b {w u: nat}: $ A. w (bdZfcBot w -> E. u bdBB215Prf u) $;")
        self.assertEqual(b6.binder_names(ap["K215_thm2_pi2b"][1]), ["w", "u"])

    def test_pins(self):
        import b6
        for rel, want in b6.SETS["b4b"]["pins"].items():
            self.assertEqual(b6.sha256(os.path.join(ROOT, *rel.split("/"))), want, rel)

    def test_thm1_set_unchanged(self):
        import b6
        self.assertEqual(b6.SETS["thm1"]["targets"], b6.TARGETS)
        self.assertEqual(b6.SETS["thm1"]["pins"], b6.PINS)
        self.assertEqual([t[0] for t in b6.TARGETS], ["K215_sigma1", "K215_sigma2"])


class B5ShapesTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import gen_b5
        cls.rc = gen_b5.main(["--b4b"])
        b = os.path.join(ROOT, "build", "b5b")
        cls.out, cls.spec_path = os.path.join(b, "b5-out.mmb"), os.path.join(b, "b5-out.mm0")
        cls.spec = open(cls.spec_path).read()

    def check(self, spec_text):
        p = os.path.join(ROOT, "build", "b5b", "b5b-test.mm0")
        open(p, "w").write(spec_text)
        with open(p, "rb") as f:
            return subprocess.run([MM0C, self.out], stdin=f, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE).returncode

    def test_checks(self):
        self.assertEqual(self.rc, 0)
        self.assertEqual(self.check(self.spec), 0)
        for n in ("K215_sigma1_H", "K215_sigma2_H", "K215_thm2_pi2a_H", "K215_thm2_pi2b_H",
                  "K215_thm3_pi2a_H", "K215_thm3_pi2b_H", "K215_G2_pi2_H"):
            self.assertIn("theorem %s " % n, self.spec)

    def test_wrong_statement_rejected(self):
        i = self.spec.index("theorem K215_G2_pi2_H ")
        tail = self.spec[i:]
        bad = self.spec[:i] + tail.replace("(im (bdZfcConPrf x0) (ex x1 (bdZfcBot x1)))",
                                           "(im (bdZfcConPrf x0) (ex x1 (bdBB215Prf x1)))", 1)
        self.assertNotEqual(bad, self.spec)
        self.assertNotEqual(self.check(bad), 0)


@unittest.skipUnless(os.path.isfile(SRC), "set B6B_SRC to a linked b6b_dropcheck .mmb (b4/k215-drop/local/check_local.sh)")
class LinkedRehearsalTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        out = os.path.join(ROOT, "build", "b6b-rehearsal")
        cls.rc = subprocess.run([sys.executable, "-B", "-I", os.path.join(ROOT, "b6", "b6.py"), "--set", "b4b",
                                 "--rehearsal", "--src", SRC, "--out", out, "--tools", os.path.join(ROOT, "tools")],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT).returncode
        cls.rep = json.load(open(os.path.join(out, "report.json")))

    def test_pass(self):
        self.assertEqual(self.rc, 0)
        self.assertEqual(self.rep["result"], "PASS")
        self.assertEqual(self.rep["mm0c"]["exit"], 0)
        self.assertTrue(self.rep["control"]["rejected"])

    def test_statements(self):
        names = [p["name"] for p in self.rep["final_public_theorems"]]
        self.assertEqual(names, ["K215_sigma1", "K215_sigma2", "K215_thm2_pi2a", "K215_thm2_pi2b",
                                 "K215_thm3_pi2a", "K215_thm3_pi2b", "K215_G2_pi2"])
        for p in self.rep["final_public_theorems"]:
            self.assertTrue(p["is_approved_text_plus_hT"], p["name"])


@unittest.skipUnless(os.path.isfile(SRC), "set B6B_SRC to a linked b6b_dropcheck .mmb (b4/k215-drop/local/check_local.sh)")
class LinkedFinalTest(unittest.TestCase):
    def test_thm2_pi2b(self):
        import b6
        cfg = b6.SETS["b4b"]
        out = os.path.join(ROOT, "build", "b6b-final-thm2b")
        os.makedirs(out, exist_ok=True)
        spec = read("foundation/hpeano.mm0") + "".join(
            read(r).split(imp, 1)[1] for r, imp in cfg["bd"])
        ap = b6.approved_lines("\n".join(read(r) for r in cfg["stmts"]), cfg["targets"])
        tg = [t for t in cfg["targets"] if t[0] == "K215_thm2_pi2b"]
        rep = {"tools": {"mm0-c": [MM0C, None]}}
        rc = b6.drive(rep, lambda: None, SRC, out, MM0C, os.path.join(ROOT, *cfg["lib"].split("/")), spec,
                      ap, tg, False)
        self.assertEqual(rc, 0)
        self.assertEqual(rep["result"], "PASS")
        self.assertTrue(rep["control"]["rejected"])
        [p] = rep["final_public_theorems"]
        self.assertTrue(p["is_approved_text"])
        self.assertEqual(p["spec_text"], ap["K215_thm2_pi2b"][1])


if __name__ == "__main__":
    unittest.main()
