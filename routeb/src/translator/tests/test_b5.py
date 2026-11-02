"""B5: Pi2 recovery over hpeano, checked by mm0-c.

  python3 -m unittest translator.tests.test_b5 -v      # from the repo root (~10 s)
"""
import os
import subprocess
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BUILD = os.path.join(ROOT, "build")
MM0C = os.path.join(ROOT, "tools", "mm0-c")


def check(mmb, spec_text):
    p = os.path.join(BUILD, "b5-test.mm0")
    open(p, "w").write(spec_text)
    with open(p, "rb") as f:
        return subprocess.run([MM0C, mmb], stdin=f, stdout=subprocess.PIPE, stderr=subprocess.PIPE).returncode


class B5Test(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sys.path.insert(0, os.path.join(ROOT, "b5"))
        import gen_b5
        cls.rc = gen_b5.main()
        cls.out = os.path.join(BUILD, "b5-out.mmb")
        cls.spec = open(os.path.join(BUILD, "b5-out.mm0")).read()

    def test_checks(self):
        self.assertEqual(self.rc, 0)
        self.assertEqual(check(self.out, self.spec), 0)
        for n in ("tsig1_H", "tsig2_H", "K215_sigma1_H", "K215_sigma2_H"):
            self.assertIn("theorem %s " % n, self.spec)

    def test_wrong_statement_rejected(self):
        bad = self.spec.replace("(ex x1 (tEv x1))) $;", "(ex x1 (tAll x1))) $;", 1)
        self.assertNotEqual(bad, self.spec)
        self.assertNotEqual(check(self.out, bad), 0)

    def test_flipped_byte_rejected(self):
        from translator.mmb_reader import read_mmb
        m = read_mmb(self.out)
        for _ in m.iter_stmts():
            pass
        mid = (m.p_proof + m.tail_offset) // 2     # inside the proof stream
        del m
        data = bytearray(open(self.out, "rb").read())
        data[mid] ^= 1
        bad = os.path.join(BUILD, "b5-bad.mmb")
        open(bad, "wb").write(data)
        self.assertNotEqual(check(bad, self.spec), 0)


if __name__ == "__main__":
    unittest.main()
