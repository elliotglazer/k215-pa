"""Unit tests of gen_closed.py (generator only; the kernel check is tools/gen7/c2/check_closed.sh).

  python3 -m unittest tools/gen7/c2/test_gen_closed.py      (from the repo root)
"""
import os, re, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_closed as gc  # noqa: E402

PERDEF = """import "gen7_lib.mm1";
def cd1 : nat = $ cSuc c0 $;
def cd2 : nat = $ cSuc cd1 $;
def cdiv (v0: nat) (v1: nat): nat = $ cThe (cAb (nfresh (ctup v0 v1)) (cEq v0 v1)) $;
def cpr (v0: nat) (v1: nat): nat = $ cAdd (cdiv (cMul (cAdd v0 v1) (cSuc (cAdd v0 v1))) cd2) v1 $;
def cb0 (v0: nat): nat = $ cAdd v0 v0 $;
def ccons (v0: nat) (v1: nat): nat = $ cSuc (cpr v0 v1) $;
def cpaFormulaFalse : nat = $ c0 $;
def cT : nat = $ ccons (cSuc (cpr cd1 (cpr c0 cd2))) (ccons (cb0 cd2) c0) $;
def cBad : nat = $ cdiv cd1 cd2 $;
def cLong : nat = $ %s $;
theorem g7nfc_cpaThProvable (v0 v1 x: nat): $ (nfr x v0) -> (nfr x v1) -> nfr x (cpaThProvable v0 v1) $ = 'x;
theorem g7nfc_cg2paAxSet (v0 x: nat): $ (nfr x v0) -> nfr x (cg2paAxSet v0) $ = 'x;
theorem g7nfc_ctmHalts (v0 v1 x: nat): $ (nfr x v0) -> (nfr x v1) -> nfr x (ctmHalts v0 v1) $ = 'x;
theorem g7nfc_cpaFormulaFalse (x: nat): $ nfr x cpaFormulaFalse $ = 'x;
""" % ("ccons cd1 " + "(ccons cd1 " * 299 + "c0" + ")" * 299)

SPEC = """theorem g7x_fwd_R (v0: nat) (v1: nat) (v2: nat): $ cPr (cIm (cEq v0 cpaFormulaFalse) (cIm (cEq v1 cd1) (cIm (cEq v2 cT) (cIm (cpaThProvable (cg2paAxSet v0) cpaFormulaFalse) (ctmHalts v1 v2))))) $;
theorem g7x_bad_R (v0: nat) (v1: nat): $ cPr (cIm (cEq v0 cd1) (cIm (cEq v1 v1) (ctmHalts v0 v1))) $;
"""


class T(unittest.TestCase):
    def setUp(self):
        self.ev = gc.Ev(PERDEF, SPEC)

    def test_parse_top_level(self):
        self.assertEqual(gc.parse("cAdd c0 (cSuc c0)"), ("cAdd", ["c0", ("cSuc", ["c0"])]))
        self.assertEqual(gc.pr(gc.parse("(cAdd c0 cd1)")), "(cAdd c0 cd1)")

    def test_src_reading(self):
        self.assertEqual(self.ev.src(gc.parse("ccons (cpr cd1 c0) (cb0 cd2)")), "(cons (pr d1 0) (b0 d2))")

    def test_def_lemmas(self):
        self.assertEqual(self.ev.lemma("cT"), "g7ev_v_T")
        txt = "\n".join(self.ev.out)
        self.assertIn("theorem g7ev_v_cons (v0 v1 a0 a1: nat) (h0: $ cPr (cEq v0 (cNum a0)) $) (h1: $ cPr (cEq v1 (cNum a1)) $): "
                      "$ cPr (cEq (ccons v0 v1) (cNum (cons a0 a1))) $ =\n'(g7ev_s (g7ev_p h0 h1));", txt)
        self.assertIn("theorem g7ev_v_b0 (v0 a0: nat) (h0: $ cPr (cEq v0 (cNum a0)) $): $ cPr (cEq (cb0 v0) (cNum (b0 a0))) $ =\n'(g7ev_a h0 h0);", txt)
        self.assertIn("theorem g7ev_v_T: $ cPr (cEq cT (cNum T)) $ =\n'(g7ev_v_cons (g7ev_s (g7ev_p g7ev_v_d1 (g7ev_p g7ev_z g7ev_v_d2)))", txt)
        # dependency order: every lemma is defined before it is used
        names = [re.match(r"theorem (\w+)", it).group(1) for it in self.ev.out]
        for k, it in enumerate(self.ev.out):
            for u in re.findall(r"g7ev_v_\w+", it.split("=", 1)[1]):
                self.assertIn(u, names[:k], u)
        # pr's lemma is the hand rule, never the (binder) body of cdiv
        self.assertNotIn("g7ev_v_div", txt)
        self.assertNotIn("g7ev_v_pr ", txt)

    def test_refuses_binders(self):
        with self.assertRaises(gc.GenError) as cm:
            self.ev.lemma("cBad")
        self.assertIn("cannot evaluate cThe", str(cm.exception))

    def test_cut_linear(self):
        gc.SPLIT = 50
        try:
            self.ev.lemma("cLong")
        finally:
            gc.SPLIT = 400
        helpers = [it for it in self.ev.out if it.startswith("theorem g7ev_h")]
        self.assertGreater(len(helpers), 4)
        # each helper statement is bounded (cut children appear as variables), so the text is linear
        self.assertLess(max(len(h) for h in helpers), 8 * 50 * 12)
        self.assertRegex(helpers[1], r"^theorem g7ev_h2_Long \(e1 k0: nat\) \(h_e1: \$ cPr \(cEq e1 \(cNum k0\)\) \$\)")

    def run_main(self, *extra):
        d = tempfile.mkdtemp()
        sp, pd = os.path.join(d, "out.mm0"), os.path.join(d, "perdef.mm1")
        open(sp, "w").write(SPEC)
        open(pd, "w").write(PERDEF)
        r = subprocess.run([sys.executable, os.path.join(HERE, "gen_closed.py"), sp, pd, d, "--name", "g7x", "--src", "gen7/g7x"] + list(extra),
                           capture_output=True, text=True)
        return r, d

    def test_instance(self):
        r, d = self.run_main("--thm", "g7x_fwd_R")
        self.assertEqual(r.returncode, 0, r.stderr)
        ev = open(os.path.join(d, "gen7", "g7x_ev.mm1")).read()
        self.assertIn("pub theorem g7x_hRefl: $ paProvable 0 (paFormulaImp (trJ (trPA (cpaThProvable (cg2paAxSet (cNum paFormulaFalse)) "
                      "cpaFormulaFalse))) (trJ (trPA (ctmHalts (cNum d1) (cNum T))))) $", ev)
        self.assertIn("(! g7x_fwd_R (cNum paFormulaFalse) (cNum d1) (cNum T))", ev)
        self.assertIn("axiom g7x_fwd_R (v0: nat) (v1: nat) (v2: nat): $ cPr (cIm (cEq v0 cpaFormulaFalse)", ev)
        hb = open(os.path.join(d, "gen7", "g7x_hb.mm1")).read()
        self.assertIn("pub theorem g7x_hB: $ bb215ProvabilityInternalBridge (g2paThCode paFormulaFalse) (tmHaltsPA d1 T) $ =\n"
                      "'(g7_bridge_of_refl_paL (iani paFormulaBound_false paS1Class_false) g7x_hRefl);", hb)
        self.assertIn("axiom g7_bridge_of_refl_paL (R m M: nat)", hb)
        self.assertIn('import "g7ev_lib.mm0";', open(os.path.join(d, "gen7", "g7x_ev.mm0")).read())
        r, d = self.run_main("--thm", "g7x_fwd_R", "--bridge", "host")
        hb = open(os.path.join(d, "gen7", "g7x_hb.mm1")).read()
        self.assertIn('import "g7_incH.mm1";', hb)
        self.assertNotIn("axiom", hb)

    def test_instance_needs_all_equations(self):
        r, d = self.run_main("--thm", "g7x_bad_R")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("without an equation antecedent: ['v1']", r.stderr)


if __name__ == "__main__":
    unittest.main()
