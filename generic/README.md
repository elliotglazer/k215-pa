# generic/: "Theorem 1 => Theorems 2 / 3 + G2" for any T ⊇ PA and any T ⊇ ZFC

K215's Theorems 2, 3 and G2 (see the top-level [README](../README.md)) were proved for one machine and one theory. This
folder publishes the **generic framework**: meta-theorems, proved once in PA (MM0 over `peano.mm0`), that turn
*Theorem 1 for a theory T and a machine M* ("M halts iff T is inconsistent") into Theorem 2 ("T is consistent iff T
proves no value of BB(n)"), Theorem 3 and Gödel's second incompleteness theorem for T. There are two front ends:

- **PA front end**: T = PA + the axioms recognized by a Σ1 formula code R (so T ⊇ PA), stated in PA's own Hilbert
  calculus (`paThProvable`);
- **set front end**: T ⊇ ZFC, given by a Σ1 recognizer R of its axioms, stated in the set-theoretic calculus of the
  K215 project (`sfThProvable`).

Both front ends were kernel-checked end to end on the host (runs C-084 and C-092, 2026-11-02): `mm0-c` accepted the
linked binary against a spec consisting of `peano.mm0`'s 26 axioms, every definition body, and the headline
statements below; the same binary with the last statement replaced by `F.` was rejected.

## Archived linked binaries (Zenodo)

The two linked proof binaries of the generic framework (PA front end, host job C-084; ZFC front end, C-092), with their checked specifications and receipts, are archived at [doi:10.5281/zenodo.23878192](https://doi.org/10.5281/zenodo.23878192) (232 MB download, zstd-compressed; supplements the K215 record doi:10.5281/zenodo.23872595).

## 1. The statements

The specification is [`pa-mm0/targets/g2_generic_frozen.mm0`](../pa-mm0/targets/g2_generic_frozen.mm0)
(sha256 `e19dee59...`). It is the owner-approved spec [`targets/g2_generic.mm0`](../pa-mm0/targets/g2_generic.mm0)
(`df67c8b9...`) with the abstract definitions that the checked headline statements use given the literal bodies of the
two host links ("freeze", approved by the owner 2026-11-02). Its header comment ("DRAFT for owner approval, NOT
approved, NOT frozen") is part of the approved text and predates the approval: the freeze keeps every line except the
definition and import lines listed in section 1.3 byte-identical. Paths `lanes/...` named in its comments refer to the
private development repository.

### 1.1 PA front end (verbatim from `g2_generic_frozen.mm0`)

```
theorem G2_generic_pa (R: nat)
  (hR: $ thIsSigma1Rec R $):
  $ ~paThInconsistent R -> ~paThProvable (paThAxSet R) (paThCon R) $;
theorem BB_generic_pa_thm2 (R m n M: nat) {b: nat}
  (hR: $ thIsSigma1Rec R $)
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> paThInconsistent R $)
  (hB: $ bb215ProvabilityInternalBridge (paThPr R) (tmHaltsPA m M) $):
  $ ~paThInconsistent R <-> A. b ~paThProvable (paThAxSet R) (bbSentencePA n b) $;
theorem BB_generic_pa_thm3 (R m n M: nat) {b: nat}
  (hR: $ thIsSigma1Rec R $)
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> paThInconsistent R $)
  (hB: $ bb215ProvabilityInternalBridge (paThPr R) (tmHaltsPA m M) $):
  $ (~paThInconsistent R <-> ~tmHalts m M) /\
    (~tmHalts m M <-> A. b ~paThProvable (paThAxSet R) (bbSentencePA n b)) $;
```

The instance T = PA (R := `paFormulaFalse`, which recognizes no sentence), checked in the same run, from
[`pa-mm0/gen7/g2pa_inst.mm0`](../pa-mm0/gen7/g2pa_inst.mm0) (approved separately 2026-11-02):

```
theorem G2_pa: $ ~paProvable 0 paFormulaFalse -> ~paProvable 0 (paThCon paFormulaFalse) $;
theorem BB_pa_thm2 (m n M: nat) {b: nat}
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> paProvable 0 paFormulaFalse $)
  (hB: $ bb215ProvabilityInternalBridge (paThPr paFormulaFalse) (tmHaltsPA m M) $):
  $ ~paProvable 0 paFormulaFalse <-> A. b ~paProvable 0 (bbSentencePA n b) $;
theorem BB_pa_thm3 (m n M: nat) {b: nat}
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> paProvable 0 paFormulaFalse $)
  (hB: $ bb215ProvabilityInternalBridge (paThPr paFormulaFalse) (tmHaltsPA m M) $):
  $ (~paProvable 0 paFormulaFalse <-> ~tmHalts m M) /\
    (~tmHalts m M <-> A. b ~paProvable 0 (bbSentencePA n b)) $;
```

### 1.2 Set front end (verbatim from `g2_generic_frozen.mm0`)

```
theorem G2_generic_set (R: nat)
  (hR: $ thIsSigma1Rec R $) (hZ: $ thExtendsZFC R $):
  $ ~sfThInconsistent R -> ~sfThProvable R (paFormulaSource (sfThCon R)) $;
theorem BB_generic_set_thm2 (R m n M: nat) {b: nat}
  (hR: $ thIsSigma1Rec R $) (hZ: $ thExtendsZFC R $)
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> sfThInconsistent R $)
  (hB: $ bb215ProvabilityInternalBridge (sfThPr R) (tmHaltsPA m M) $):
  $ ~sfThInconsistent R <-> A. b ~sfThProvable R (bbSentenceSource n b) $;
theorem BB_generic_set_thm3 (R m n M: nat) {b: nat}
  (hR: $ thIsSigma1Rec R $) (hZ: $ thExtendsZFC R $)
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> sfThInconsistent R $)
  (hB: $ bb215ProvabilityInternalBridge (sfThPr R) (tmHaltsPA m M) $):
  $ (~sfThInconsistent R <-> ~tmHalts m M) /\
    (~tmHalts m M <-> A. b ~sfThProvable R (bbSentenceSource n b)) $;
theorem BB_generic_set_thm2_P (A: set) (P G m n M: nat) {a b c: nat}
  (hA: $ zfcAxioms C_ A $)
  (hP: $ paFormulaBound 1 P $)
  (h1: $ A. c bb215ProvabilityD1T A bb215G2ASrc P c $)
  (h2: $ A. a A. b bb215ProvabilityD2 P a b $)
  (h3: $ A. a bb215ProvabilityD3 P a $)
  (hG: $ bb215ProvabilityFixedPoint P G $)
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> sfTheoryProvable A sfBot $)
  (hB: $ bb215ProvabilityInternalBridge P (tmHaltsPA m M) $):
  $ ~sfTheoryProvable A sfBot <-> A. b ~sfTheoryProvable A (bbSentenceSource n b) $;
theorem BB_generic_set_thm3_P (A: set) (P G m n M: nat) {a b c: nat}
  (hA: $ zfcAxioms C_ A $)
  (hP: $ paFormulaBound 1 P $)
  (h1: $ A. c bb215ProvabilityD1T A bb215G2ASrc P c $)
  (h2: $ A. a A. b bb215ProvabilityD2 P a b $)
  (h3: $ A. a bb215ProvabilityD3 P a $)
  (hG: $ bb215ProvabilityFixedPoint P G $)
  (hM: $ tmValid m M $) (hmn: $ m <= n $)
  (hT1: $ tmHalts m M <-> sfTheoryProvable A sfBot $)
  (hB: $ bb215ProvabilityInternalBridge P (tmHaltsPA m M) $):
  $ (~sfTheoryProvable A sfBot <-> ~tmHalts m M) /\
    (~tmHalts m M <-> A. b ~sfTheoryProvable A (bbSentenceSource n b)) $;
```

The rest of `g2_generic_frozen.mm0` (abstract G2, the HBL package, the Π2 forms of section (E), the reflection
statements of (F), the K215 / ZFC + s / ZFC + VP instances of (G)) is **stated, not proved** by these runs.

### 1.3 The freeze: the 8 definitions that received bodies

| definition (file) | frozen body | used by |
| --- | --- | --- |
| `paSigma1 c` (`g2_generic_defs_frozen.mm0`) | `paS1Class 1 c` | both |
| `paSigma1True c a` (same) | `paS1Holds c (a : 0)` | both |
| `paThCode R` (same) | `g2paThCode R` | PA |
| `zfcStdAxRecognizer` (same) | `g2szRz` | set |
| `sfThMemCode` (same) | `g2sfMemCode` | set |
| `sfThClosedCode` (same) | `g2sfClosedCode` | set |
| `zfcStdValidCode` (`zfc_std_defs_frozen.mm0`) | `g2sfValidCode` | set |
| `zfcStdGoalCode` (same) | `g2sfGoalCode` | set |

The 241 definitions these bodies use (the Σ1 class and truth `paS1Class` / `paS1Holds`, the PA proof-predicate
code `g2paThCode` with its 176 axiom rows, the ZFC axiom recognizer `g2szRz`, the set-calculus tables) are copied
verbatim from the two linked specs into [`g2_generic_freeze_support.mm0`](../pa-mm0/g2_generic_freeze_support.mm0).
Twelve definitions that no checked statement uses stay abstract (`zfcVPRecognizer`, `bdThPrf`, `bdPaThPrf`,
`bdTmHalt`, `bdBBPrf`, `bdPaBBPrf`, `bdConPrf`, `bdPaConPrf`, `reflThInconsistent`, `reflPaThInconsistent`,
`reflTmHalts`, `zfcStdContextCode`). So `thIsSigma1Rec R` unfolds to `paFormulaBound 1 R /\ paS1Class 1 R`, and
`paThAxSet R` to the closed PA sentences `a` with `paS1Holds R (a : 0)`.

Check the freeze (no compiler needed; a few seconds):

    python3 -I generic/tools/freeze_check.py --pa generic/receipts/C-084/linked.mm0 --sf generic/receipts/C-092/linked.mm0

It prints `FREEZE CHECK PASS` only if (a) every frozen and support definition equals its statement in the linked
specs, (b) the frozen files equal the approved files except the 8 definition lines, 2 renamed imports and 1 added
import, (c) the 8 headline theorems of the links are the frozen text, and (d) every statement of both linked specs
(terms, definitions, notations, the 26 axioms, theorems) occurs verbatim in the frozen closure, except `G2_pa`,
`BB_pa_thm2`, `BB_pa_thm3` (section 1.1). [`spec-closure.sha256`](spec-closure.sha256) lists the 429 files of the
`.mm0` import closures of the frozen and the approved spec. `mm0-rs compile pa-mm0/targets/g2_generic_frozen.mm0`
elaborates it (5870 terms/defs, 5321 axioms/theorems).

## 2. What a new theory or machine must supply

For **T ⊇ PA** (PA front end):

| | what | form |
| --- | --- | --- |
| R | the Σ1 axiom recognizer of T | `hR: thIsSigma1Rec R`, i.e. `paFormulaBound 1 R /\ paS1Class 1 R` (syntactic) |
| m, M | an m-state machine table, any n >= m | `hM: tmValid m M` (by computation). M must be a **closed literal** over `0`, `suc`, `+`, `*`, pairs, `cons` (`:`), `d1`..`d10`, `b0` / `b1` and definitions whose bodies use only these; **no `if`**. Encoding as `tmHalts`: states 0..m-1, start state 0 on the blank tape, halt = reaching state m (an explicit transition target m), action `(write, (dir, target)) + 1` at list index `pair(q, b)` (gaps written as 0), dir 0 = left |
| hT1 | Theorem 1 for T, in the plain form | `tmHalts m M <-> paThInconsistent R`; for T = PA, `tmHalts m M <-> paProvable 0 paFormulaFalse` (BB_pa_thm2 / _thm3 take this form directly; `g2pi_hT1` converts it) |
| X_fwdV | the forward direction of Theorem 1, restated in variable form | see below; from Theorem 1 by rewriting |
| hB | the internal bridge `bb215ProvabilityInternalBridge (paThPr R) (tmHaltsPA m M)`, i.e. PA proves "Pr_T(F.) -> M halts" | **not hand work**: produced from X_fwdV by the reflection compiler (section 3) |

The reflected Theorem-1 input (approved form; variable form, the equations as antecedents, no bound variable, so the
reflection has no side hypotheses):

```
theorem X_fwdV (R m M: nat): $ R = paFormulaFalse -> m = m_X -> M = M_X ->
  paThProvable (g2paAxSet R) paFormulaFalse -> tmHalts m M $;
```

(`m_X`, `M_X` the machine's literal definitions; for T other than PA, R's literal in place of `paFormulaFalse`.)
A worked TEST instance is [`pa-mm0/gen7/g7ev_toy.mm0`](../pa-mm0/gen7/g7ev_toy.mm0) (`g7toy_fwd`; it defines a TEST
stand-in `g2paAxSet` and a toy machine that halts at once) with the generated
[`g7toy_ev.mm0`](../pa-mm0/gen7/g7toy_ev.mm0) (`g7toy_hRefl`) and [`g7toy_hb.mm0`](../pa-mm0/gen7/g7toy_hb.mm0)
(`g7toy_hB`). The evaluation rules used for the table are stated in [`gen7/g7ev_src.mm0`](../pa-mm0/gen7/g7ev_src.mm0)
and [`gen7/g7ev_lib.mm0`](../pa-mm0/gen7/g7ev_lib.mm0) (whose five `axiom ..._R` lines are reflection stubs that the
linker replaces by the reflected proofs; a linked binary has only `peano.mm0`'s axioms).

For **T ⊇ ZFC** (set front end): R with `hR` and `hZ: thExtendsZFC R` (e.g. `R = thZFCPlus Rx`, `Rx = thSingleton
s` for ZFC + s), M and n as above, `hT1: tmHalts m M <-> sfThInconsistent R`, and hB about `sfThPr R`. The set-side
analogue of X_fwdV and its glue generator are **not written yet** (open item), so for now a set-side hB must be
supplied as a proof, or the general form `BB_generic_set_thm2_P` used with a predicate P that has a bridge.

## 3. The reflection compiler pipeline (how hB is produced, PA side)

The compiler ("gen7", [`tools/gen7/`](../tools/gen7/)) reflects an MM0 proof over `peano.mm0` into a PA-internal
derivation: for a theorem `S` it emits a theorem `S_R: cPr [S]` ("PA proves the code of S"), with per-definition code
lemmas (`perdef.mm1`). A hand module that states such `S_R` as `axiom` stubs is compiled separately and `link.py`
replaces every stub by the reflected proof, by name and verbatim statement. The bridge `g7_bridge_of_refl_paL`
(C5) turns the reflected forward direction at numeral codes (`hRefl`) into hB. Per machine X:

1. Machine module `pa-mm0/<x>.mm1` / `.mm0`: the literal `m_X`, `M_X`, `tmValid m_X M_X` (by computation), Theorem 1,
   and `X_fwdV`; it imports `gen7/g7ev_src` and the real GEN3 `g2paAxSet` (`g2_generic_pa_axcode`).
2. Reflection source `pa-mm0/<x>_src` = `import d3_adqsrcp` + the machine module. Roots file =
   `generic/tools/d3/roots_adqP.txt` + `generic/tools/c2/roots_ev.txt` + `X_fwdV`. Host job (runner driver
   [`tools/gen7_job.py`](../tools/gen7_job.py)):

       {"action": "gen7", "module": "<x>_src", "roots": "<that file>", "cone": true,
        "nfr": "paFormulaEqual,paFormulaAnd,paFormulaOr,paFormulaImp,paFormulaAll,paFormulaEx,paTermVariable,paTermSuccessor,paTermAddition,paTermMultiplication,cons",
        "need": "pf:ctmHalts,pf:ctmValid,pf:cle,pf:clt,pf:ctmPadOf,nf:cpaThProvable,nf:cg2paAxSet,nf:ctmHalts"}

   or locally `GEN7_NEED=... python3 tools/gen7/refl_lib.py <x>_src.mmb OUT --roots FILE --cone --nfr NFR`
   (output `OUT/out.mmb`, `OUT/out.mm0`, `OUT/gen7/perdef.mm1`, `OUT/manifest.json`; the reflection is itself checked
   by `mm0-c`, 26 axioms only, false control).
3. Glue: `python3 generic/tools/c2/gen_closed.py OUT/out.mm0 OUT/gen7/perdef.mm1 pa-mm0 --thm X_fwdV_R --name <x> --src
   <x> --bridge host` writes `pa-mm0/gen7/<x>_ev` (the stub `X_fwdV_R` verbatim, one evaluation lemma
   `PA |- [code(D) = cNum D]` per definition of the table, linear and DAG-shared, and `<x>_hRefl`) and
   `pa-mm0/gen7/<x>_hb` (`<x>_hB = g7_bridge_of_refl_paL REC <x>_hRefl`; `--rec` for R other than `paFormulaFalse`).
   `python3 tools/gen7/d3/stubcheck.py OUT/out.mm0 gen7/<x>_hb` must report 0 differ / 0 unresolved.
4. Link: host job `{"action": "gen7", "module": "<x>_src", "reflect": false, "hand": "gen7/<x>_hb", "statements":
   "<x>_hB", "bodies": "ALL"}`, or one final module that applies `BB_pa_thm2` / `BB_pa_thm3` / `G2_pa` (or the generic
   `BB_generic_pa_*`) with hT1, hM := tmValid, hB := `<x>_hB`. Steps: `lcheck.py` (compile the hand module),
   `d3/minspec.py --bodies ALL` (minimal spec with every definition body), `link.py`, `mm0-c`, `axioms.py` (exactly
   `peano.mm0`'s 26), false control. Expected: every stub resolved, 26 axioms.

Local rehearsal at toy scale: `generic/tools/c2/check_closed.sh WORKDIR` (~4 GB RAM, 2 min; copy `generic/tools/c2/*`
into `tools/gen7/c2/` first, since it calls `$ROOT/tools/gen7/c2/gen_closed.py`), unit tests
`python3 -m unittest generic/tools/c2/test_gen_closed.py`. The tools read `MM0TOOLS` (directory with `mm0-rs`,
`mm0-c`) and `MM0PAHA` / `ROUTEB` (set it to `routeb/src`, which holds the `translator/mmb_reader.py` they import).
The headline runs used the host snapshot in [`tools/gen7/`](../tools/gen7/) exactly
([`HOST-MANIFEST.sha256`](../tools/gen7/HOST-MANIFEST.sha256), sha256 `3c00eca4...` = `gen7_manifest_sha256` of
C-081 / C-084 / C-091 / C-092); `generic/tools/` holds the files added on the private main branch after that snapshot
(freeze check, closed-term evaluation generator). Like the compiler, all of this is untrusted: only `mm0-c` and the
spec are.

## 4. Receipts

[`receipts/`](receipts/) has one folder per host run (results of the runner; [`MANIFEST.json`](MANIFEST.json) gives
every published file with the sha256 of the bytes the runner wrote and the transformation applied).

| run | action / module | what it checked | mm0-c build |
| --- | --- | --- | --- |
| **C-084** | gen7 hand link `gen7/g2pa_inst` against C-081 | `G2_generic_pa`, `BB_generic_pa_thm2`, `BB_generic_pa_thm3`, `G2_pa`, `BB_pa_thm2`, `BB_pa_thm3`; [`linked.mm0`](receipts/C-084/linked.mm0) sha256 `c3d21d95...` = 26 axioms + every def body + these 6; 168 stubs replaced; linked binary `db14a765...` (429,433,424 bytes); false control rejected | capacity2 |
| **C-092** | gen7 hand link `gen7/g2sf_spec` against C-091 | `G2_generic_set`, `BB_generic_set_thm2`, `_thm3`, `_thm2_P`, `_thm3_P`; [`linked.mm0`](receipts/C-092/linked.mm0) `4ccab9bb...`; linked binary `9d918fd8...` (834,446,136 bytes); false control rejected | capacity2 |
| C-080 / C-081 | check / reflection of `d3_adqsrcp` (PA reflection source: route T roots + run cut) | 988 sources; reflection 8,917 theorems, 168 public statements, 26 axioms | capacity / capacity2 |
| C-090 / C-091 | check / reflection of `d3_adqsrcs` (set side: D2, D3, C5, run cut) | 1,488 sources; reflection 127,604 theorems, 243 public statements, 26 axioms | capacity / capacity2 |
| C-074 | check `g2_generic_pa_thd2` | D2 for the PA predicate (`g2paThCode_D2`) | capacity |
| C-034 / C-035 | reflection of `d3_adqsrc` / hand link `gen7/d3_pad3` | D3 for the PA predicate (`g2paThCode_D3`), 26 axioms (earlier tool snapshot `b8439418...`) | capacity2 |
| G3-002 | check `g2_generic_pa_thfinal` | `g2paThCode`: bound, class, defines, D1, fixed point, PA transfer | capacity |
| G1-001..005 | checks of `g2_generic_s1_*` | Σ1 truth / class pieces | stock |
| GEN2-001, -003, -004, -005 | checks of `g2_generic_sf_defines`, `_sz_zfc`, `_sf_prat`, `_sf_zfc` | set-side code, ZFC recognizer, PrAt transfer, ZFC instance | stock / capacity |
| GEN4-001, -002, -004 | checks of `g2_generic_g4`, `_tm_pad`, `_tm_runcut` | BB codes closed, padding, run cut | stock / capacity |

C-084 and C-092 each compiled their whole hand closure and linked it to the reflection binary, so they do not depend
on the earlier runs; those are listed because they checked the pieces separately. Check reports (`report.json`) list
their sources with sha256; for the two hand links, [`receipts/C-084/sources.json`](receipts/C-084/sources.json) and
[`receipts/C-092/sources.json`](receipts/C-092/sources.json) (derived for publication) list the in-git closure
(1,334 and 1,722 files plus `peano.mm0` / `.mm1`): `python3 -I scripts/check_sources.py generic/receipts/C-084/sources.json`.
The files not in git or earlier releases (400 files, 239,380,702 bytes) are listed in
[`../manifests/generic-inputs.json`](../manifests/generic-inputs.json) for the release `generic-inputs-v1`
(**not yet exported**).

## 5. Re-verifying

    mm0-c linked.mmb < generic/receipts/C-084/linked.mm0     # expect rc 0
    mm0-c linked.mmb < generic/receipts/C-092/linked.mm0

with the linked binaries above (sha256 `db14a765...`, `9d918fd8...`), downloadable (zstd-compressed) from
[doi:10.5281/zenodo.23878192](https://doi.org/10.5281/zenodo.23878192). Alternatively re-run the pipeline (reflection
+ hand compile + link; C-084: ~74 GB peak commit for the hand compile, C-092: ~124 GB) from the sources and the tool
snapshot. Then check
that the linked spec's axioms are `peano.mm0`'s 26 (`tools/gen7/axioms.py linked.mmb linked.mm0`) and run the freeze
check of section 1.3, which ties the linked specs to the frozen spec.

## 6. Trust base

1. The 26 axioms of [`lean-mm0/vendor/peano.mm0`](../lean-mm0/vendor/peano.mm0) (sha256 `463a7d6e...`). The linked
   specs contain exactly these axioms (`axioms.py`: "mmb 26, spec 26, peano.mm0 26").
2. The meaning of the statements: `generic/receipts/C-084/linked.mm0` and `C-092/linked.mm0` (every definition body
   inlined), equal statement for statement to the frozen spec closure (freeze check (d)).
3. `mm0-c`, by hash: **capacity2** `bba77622e7540e3f68eb1cc0c202c1cfcdaa2c5bed01754eb0b86d143e4f6371` (all gen7 runs,
   including C-084 / C-092; upstream `0d414c0b` + [`checker/mm0-c-capacity.patch`](../checker/mm0-c-capacity.patch),
   as in the top-level README); **capacity** `d490a086c8a56e1334c476844d7d9a739c4a201a0dee92eb82f71d2f8ae72848` (the
   larger-table build used by the check runs C-074, C-080, C-090, G3-002, GEN2-004/-005, GEN4-004); **stock**
   `277d0ce0c53ba82c944c8d51ae140379a426d4a4ac64e9fcccbd40ab18fbfd1c` (G1-*, GEN2-001/-003, GEN4-001/-002).
   `mm0-rs` `c3be4fd0...` (unmodified upstream) and all Python tooling are untrusted.
