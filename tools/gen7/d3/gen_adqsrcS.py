r"""Route T, set side: the set adequacy (ADQ) reflection source (lanes/G2GEN.md STATE, host job drafts).
  python3 gen_adqsrcS.py        writes pa-mm0/d3_adqsrcS.mm1 (HOST source: imports C5's g7_incsrc (= d3_adqsrc + GEN2
                                sf_defines + tm_defs) and g7src_tmh, GEN2's sf_pr (532 MB closure) and sz_rec, gen7/d3_rsrcS, and the
                                rename laws / roots of d3_rsrcG; one reflection then serves paThPr_D3, C5 and the set side)
                                and pa-mm0/gen7/d3_adqStest.mm1 (TEST ONLY, local: the same proof text against stand-ins
                                for GEN2's facts)
d3r_adqS (R y): hR -> [A. x (Holds g2szRz (x:0) -> Holds R (x:0))] -> paProvable 0 y -> Holds (g2sfThCodeL R) (src y : 0)
  = g2sfThL_PA_transfer (inclusion zfcAxioms C_ g2sfAxSet R from g2szRz_axioms + g2sfAxSet_el) + g2sfThCodeL_defines (<-),
  made implication-form by an if-substitution R' := if (hR /\ Z) R g2szRz (g2szRz satisfies both; g2szRz_rec).
Its second hypothesis is exactly d3_S3h's conclusion at x := name 0."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
PA = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(HERE))), 'pa-mm0')

H = '((paFormulaBound 1 R /\\ paS1Class 1 R) /\\ A. x (paS1Holds g2szRz (x : 0) -> paS1Holds R (x : 0)))'
RP = '(if %s R g2szRz)' % H
BODY2 = r'''
-- D3 core of the set side (2026-11-02): internal Sigma1 completeness at Q = g2sfThCodeL R, GEN2's g2sfPrAt_bwd, then
-- d3r_aS_core at y := PrAt (Image Gsr Q) a. Every function application of the final statement gets its own variable
-- with an equation hypothesis, so that the reflected statement is instantiated by code terms that are only PROVABLY
-- equal (S6 for Q and Gsr, EVN, EVS, S5) instead of needing coded congruences.
theorem d3r_aS_core2 (R: nat) {x: nat} (y: nat x): $ paProvable 0 y -> paS1Holds (g2sfThCodeL RP) (paFormulaSource y : 0) $ =
(named '(syl (bi2i (g2sfThCodeL_defines d3r_aS_hR)) (ax_mp d3r_aS_e (g2sfThL_PA_transfer (ax_mp d3r_aS_inc d3r_aS_Z)))));
theorem d3r_aS_QR (R: nat) {x zA zB zG zT zL zR: nat}: $ paFormulaBound 1 (g2sfThCodeL RP) /\ paS1Class 1 (g2sfThCodeL RP) $ =
'(iani (g2sfThCodeL_bound (anl d3r_aS_hR)) (!! g2sfThCodeL_class zA zB zG zT zL zR (anr d3r_aS_hR)));
theorem d3r_aS_cpl (R u: nat) {x a: nat}: $ paS1Holds (g2sfThCodeL RP) (u : 0) -> paProvable 0 (bb215PrAt (g2sfThCodeL RP) u) $ =
(named '(ax_mp {(!! eale a ,eqtac) : $ A. a (paS1Holds (g2sfThCodeL RP) (a : 0) -> paProvable 0 (bb215PrAt (g2sfThCodeL RP) a)) ->
  (paS1Holds (g2sfThCodeL RP) (u : 0) -> paProvable 0 (bb215PrAt (g2sfThCodeL RP) u)) $} (paS1True_complete d3r_aS_QR)));
theorem d3r_aS_bwd (R a: nat) {x: nat}: $ paProvable 0 (bb215PrAt (g2sfThCodeL RP) (paFormulaSource a)) ->
  paProvable 0 (bb215PrAt (bb215ProvabilityImageFormula bb215L3pGsr (g2sfThCodeL RP)) a) $ =
(named '(com12 bb215D2_mp (g2sfPrAt_bwd (anl d3r_aS_QR))));
theorem d3r_aS_D3 (R a: nat) {x: nat}: $ paS1Holds (g2sfThCodeL RP) (paFormulaSource a : 0) ->
  paS1Holds (g2sfThCodeL RP) (paFormulaSource (bb215PrAt (bb215ProvabilityImageFormula bb215L3pGsr (g2sfThCodeL RP)) a) : 0) $ =
(named '(syl d3r_aS_core2 (syl d3r_aS_bwd d3r_aS_cpl)));
theorem d3r_D3S0 (R a: nat) {x: nat}: $ paFormulaBound 1 R /\ paS1Class 1 R -> A. x (paS1Holds g2szRz (x : 0) -> paS1Holds R (x : 0)) ->
  paS1Holds (g2sfThCodeL R) (paFormulaSource a : 0) ->
  paS1Holds (g2sfThCodeL R) (paFormulaSource (bb215PrAt (bb215ProvabilityImageFormula bb215L3pGsr (g2sfThCodeL R)) a) : 0) $ =
(named '(exp (mpbid (imeqd (paS1Holdseqd (g2sfThCodeLeqd ifpos) (a1i eqid))
    (paS1Holdseqd (g2sfThCodeLeqd ifpos) (conseqd (paFormulaSourceeqd (bb215PrAteqd (bb215ProvabilityImageFormulaeqd (a1i eqid) (g2sfThCodeLeqd ifpos)) (a1i eqid))) (a1i eqid))))
  (a1i d3r_aS_D3))));
pub theorem d3r_D3S (R Q G a a2 u y y2 w: nat) {x: nat}: $ paFormulaBound 1 R /\ paS1Class 1 R ->
  A. x (paS1Holds g2szRz (x : 0) -> paS1Holds R (x : 0)) ->
  Q = g2sfThCodeL R -> G = bb215L3pGsr -> a2 = a -> u = paFormulaSource a2 ->
  y = bb215PrAt (bb215ProvabilityImageFormula G Q) a -> y2 = y -> w = paFormulaSource y2 ->
  paS1Holds Q (u : 0) -> paS1Holds Q (w : 0) $ =
(named '(exp (exp (exp (exp (exp (exp (exp (exp
  (mpbird (imeqd (paS1Holdseqd (syl anr (syl anl (syl anl (syl anl (syl anl (syl anl anl)))))) (conseqd (eqtrd (syl anr (syl anl (syl anl anl))) (paFormulaSourceeqd (syl anr (syl anl (syl anl (syl anl anl)))))) (a1i eqid))) (paS1Holdseqd (syl anr (syl anl (syl anl (syl anl (syl anl (syl anl anl)))))) (conseqd (eqtrd anr (paFormulaSourceeqd (eqtrd (syl anr anl) (eqtrd (syl anr (syl anl anl)) (bb215PrAteqd (bb215ProvabilityImageFormulaeqd (syl anr (syl anl (syl anl (syl anl (syl anl anl))))) (syl anr (syl anl (syl anl (syl anl (syl anl (syl anl anl))))))) (a1i eqid)))))) (a1i eqid))))
    (syl (imp d3r_D3S0) (syl anl (syl anl (syl anl (syl anl (syl anl (syl anl anl)))))))))))))))));
'''
BODY = r'''
theorem d3r_aS_hR (R: nat) {x: nat}: $ paFormulaBound 1 RP /\ paS1Class 1 RP $ =
'(cases (mpbird (aneqd (paFormulaBoundeqd (a1i eqid) ifpos) (paS1Classeqd (a1i eqid) ifpos)) anl)
  (mpbird (aneqd (paFormulaBoundeqd (a1i eqid) ifneg) (paS1Classeqd (a1i eqid) ifneg)) (a1i g2szRz_rec)));
theorem d3r_aS_zy (R y: nat) {x: nat}: $ paS1Holds g2szRz (y : 0) -> paS1Holds RP (y : 0) $ =
(named '(cases (mpbird (imeqd biidd (paS1Holdseqd ifpos (a1i eqid)))
    (syl {(!! eale x ,eqtac) : $ A. x (paS1Holds g2szRz (x : 0) -> paS1Holds R (x : 0)) -> (paS1Holds g2szRz (y : 0) -> paS1Holds R (y : 0)) $} anr))
  (mpbird (imeqd biidd (paS1Holdseqd ifneg (a1i eqid))) (a1i id))));
theorem d3r_aS_Z (R: nat) {x z: nat}: $ A. z (paS1Holds g2szRz (z : 0) -> paS1Holds RP (z : 0)) $ = (named '(ax_gen d3r_aS_zy));
theorem d3r_aS_inc1 (S a: nat) {z: nat}: $ A. z (paS1Holds g2szRz (z : 0) -> paS1Holds S (z : 0)) -> a e. zfcAxioms -> a e. g2sfAxSet S $ =
(named '(exp (mpbird (a1i g2sfAxSet_el) (iand (syl anl (syl (bi1i g2sfAxSet_el) (syl (bi2i g2szRz_axioms) anr)))
  (mpd (syl anr (syl (bi1i g2sfAxSet_el) (syl (bi2i g2szRz_axioms) anr)))
    (syl {(!! eale z ,eqtac) : $ A. z (paS1Holds g2szRz (z : 0) -> paS1Holds S (z : 0)) -> (paS1Holds g2szRz (a : 0) -> paS1Holds S (a : 0)) $} anl))))));
theorem d3r_aS_inc (S: nat) {a z: nat}: $ A. z (paS1Holds g2szRz (z : 0) -> paS1Holds S (z : 0)) -> A. a (a e. zfcAxioms -> a e. g2sfAxSet S) $ =
(named '(iald d3r_aS_inc1));
theorem d3r_aS_e (A: set) (y: nat) {c: nat}: $ A. c (paProvable 0 c -> sfTheoryProvable A (paFormulaSource c)) -> paProvable 0 y -> sfTheoryProvable A (paFormulaSource y) $ =
'(!! eale c ,eqtac);
theorem d3r_aS_core (R y: nat) {x: nat}: $ paProvable 0 y -> paS1Holds (g2sfThCodeL RP) (paFormulaSource y : 0) $ =
(named '(syl (bi2i (g2sfThCodeL_defines d3r_aS_hR)) (ax_mp d3r_aS_e (g2sfThL_PA_transfer (ax_mp d3r_aS_inc d3r_aS_Z)))));
pub theorem d3r_adqS (R y: nat) {x: nat}: $ paFormulaBound 1 R /\ paS1Class 1 R -> A. x (paS1Holds g2szRz (x : 0) -> paS1Holds R (x : 0)) ->
  paProvable 0 y -> paS1Holds (g2sfThCodeL R) (paFormulaSource y : 0) $ =
(named '(exp (mpbid (imeqd biidd (paS1Holdseqd (g2sfThCodeLeqd ifpos) (a1i eqid))) (a1i d3r_aS_core))));
'''.replace('RP', RP) + BODY2.replace('RP', RP)

LAWS = r'''
-- the rename laws and roots of gen7/d3_rsrcG (S6 for Gsr, S3h), here over the real modules
pub theorem d3g_cgFR (R: set) (d a b: nat): $ a = b -> paFormulaRename R d a = paFormulaRename R d b $ = '(paFormulaRenameeqd eqsidd eqidd id);
pub theorem d3g_root: $ bb215L3pGsr = bb215L3pGsr $ = 'eqid;
pub theorem d3z_root: $ g2szRz = g2szRz $ = 'eqid;
'''

def main():
    host = ['import "g7_incsrc.mm1";', 'import "g2_generic_sf_pr.mm1";', 'import "g2_generic_sf_prat.mm1";', 'import "g2_generic_sz_rec.mm1";',
            'import "gen7/d3_rsrcS.mm1";', 'import "g7src_tmh.mm1";', '',
            '-- Route T, set side: HOST master reflection source (generated by tools/gen7/d3/gen_adqsrcS.py; see its docstring).',
            '-- Roots: tools/gen7/d3/roots_adqS.txt (= C5 roots_inc + set-side EVS / rename roots + d3r_adqS, d3r_D3S + C5 tmh stage g7src_tmh_flat).',
            LAWS, BODY, "pub theorem d3_adqsrcS_final: $ paFormulaBound 0 paFormulaFalse $ = 'paFormulaBound_false;", '']
    open(os.path.join(PA, 'd3_adqsrcS.mm1'), 'w').write('\n'.join(host))
    test = ['import "d3_rsrcS.mm1";', 'import "d3_szdefs.mm1";', 'import "d3_gsrdefs.mm1";', 'import "../bb215_provability_d1.mm1";', '',
            '-- TEST ONLY (generated by tools/gen7/d3/gen_adqsrcS.py): d3r_adqS\'s proof text against stand-ins: GEN2\'s',
            '-- g2sfAxSet (real body) and g2sfAxSet_el (real proof), g2sfThCodeL (placeholder body), and the four GEN2 facts as axioms.',
            "@_ def g2sfAxSet (R .a: nat): set = $ {a | sfBound 0 a /\\ paS1Holds R (a : 0)} $;",
            "theorem g2sfAxSet_el (R a: nat): $ a e. g2sfAxSet R <-> sfBound 0 a /\\ paS1Holds R (a : 0) $ = (named '(elabe ,eqtac));",
            "@_ def g2sfThCodeL (R: nat): nat = $ R $;",
            "axiom g2szRz_axioms (a: nat): $ a e. g2sfAxSet g2szRz <-> a e. zfcAxioms $;",
            "axiom g2szRz_rec: $ paFormulaBound 1 g2szRz /\\ paS1Class 1 g2szRz $;",
            "axiom g2sfThL_PA_transfer (R: nat) {a c: nat} (hZ: $ A. a (a e. zfcAxioms -> a e. g2sfAxSet R) $): $ A. c (paProvable 0 c -> sfTheoryProvable (g2sfAxSet R) (paFormulaSource c)) $;",
            "axiom g2sfThCodeL_bound (R: nat) (hRb: $ paFormulaBound 1 R $): $ paFormulaBound 1 (g2sfThCodeL R) $;",
            "axiom g2sfThCodeL_class (R: nat) {zA zB zG zT zL zR: nat} (hRc: $ paS1Class 1 R $): $ paS1Class 1 (g2sfThCodeL R) $;",
            "axiom g2sfPrAt_bwd (Q x: nat) (hQ1: $ paFormulaBound 1 Q $): $ paProvable 0 (paFormulaImp (bb215PrAt Q (paFormulaSource x)) (bb215PrAt (bb215ProvabilityImageFormula bb215L3pGsr Q) x)) $;",
            "axiom g2sfThCodeL_defines (R y: nat) (hR: $ paFormulaBound 1 R /\\ paS1Class 1 R $): $ paS1Holds (g2sfThCodeL R) (y : 0) <-> sfTheoryProvable (g2sfAxSet R) y $;",
            BODY, "pub theorem d3_adqStest_final: $ paFormulaBound 0 paFormulaFalse $ = 'paFormulaBound_false;", '']
    open(os.path.join(PA, 'gen7', 'd3_adqStest.mm1'), 'w').write('\n'.join(test))

if __name__ == '__main__':
    main()
