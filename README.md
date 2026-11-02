# K215 halts iff ZFC is inconsistent (Metamath Zero, PA)

This repository holds a machine-checked proof, in Peano arithmetic formalized in
[Metamath Zero](https://github.com/digama0/mm0) (MM0), of the following theorem about a fixed Turing machine K215
with 215 working states and a separate halt label:

```
theorem K215_halts_iff_ZFC_inconsistent:
  $ k215LiteralHalts <-> zfcInconsistent $;
```

The statement is copied verbatim from [`pa-mm0/targets/final.mm0`](pa-mm0/targets/final.mm0)
(sha256 `8f531d23514e962931ba6c041cb15f08045e86d6414863ac249f02f34bd26c5d`):

- `k215LiteralHalts` ([`pa-mm0/k215_literal_tm.mm0`](pa-mm0/k215_literal_tm.mm0)) is
  `E. n k215TMQ (k215TMRun n k215TMInitial) = k215Num215`: the literal K215 transition table, run from the blank
  tape, reaches the halt label 215 after some number `n` of steps.
- `zfcInconsistent` ([`pa-mm0/zfc_proofs.mm0`](pa-mm0/zfc_proofs.mm0)) is `zfcProvable sfBot`: there is a
  (numerically coded) ZFC proof of falsity.

It is proved, with no hypotheses, as `K215_halts_iff_ZFC_inconsistent_final` in
[`pa-mm0/k215_final_thm1.mm0`](pa-mm0/k215_final_thm1.mm0); its binders and statement text are exactly the ones
above.

## What is proved

Every theorem below is stated in a `.mm0` file in git and was checked by `mm0-c` against the joined specification
of its module over the 26 axioms of `peano.mm0` (PA) or of `hpeano.mm0` (HA). Theorem 1 is described in detail
above; the rest of this README (trust base, receipt, verification) is written for it, and the same steps apply to
the other receipts with the files named here.

| receipt | module | what it checked |
| --- | --- | --- |
| [`receipt/thm1/`](receipt/thm1/) | `k215_final_thm1` | Theorem 1 (PA), compiled and checked in one run |
| [`receipt/thm23-g2/pa/`](receipt/thm23-g2/pa/) | `b4b_final` | Theorems 1, 2, 3 and G2 in PA and their Pi2 forms (6,176 sources, joined spec `6d79aac0...`, binary `25b7a4d5...` = the Zenodo PA binary) |
| [`receipt/thm23-g2/pa-g2/`](receipt/thm23-g2/pa-g2/) | `zfc_incompleteness_root` | the G2 theorems below (6,056 sources, a subset of `b4b_final`'s, joined spec `f02b3e62...`) |
| [`receipt/thm23-g2/ha/`](receipt/thm23-g2/ha/) | `b6-out.mm0` | the 7 Pi2 statements in HA (binary `636804b4...` = the Zenodo HA binary, translated from the PA binary above) |

The `b4b_final` and `zfc_incompleteness_root` runs used the separate-link mode (each module compiled to its own
`.mmb`, then linked into one binary and checked against the joined spec); the false-conclusion control of each
run replaces the last theorem by `F.` and is rejected.

### In PA (classical, `peano.mm0`)

**Theorem 1** ([`pa-mm0/targets/final.mm0`](pa-mm0/targets/final.mm0); proved in
[`pa-mm0/k215_final_thm1.mm0`](pa-mm0/k215_final_thm1.mm0)):

```
theorem K215_halts_iff_ZFC_inconsistent_final:
 $ k215LiteralHalts <-> zfcInconsistent $;
```

**Theorems 2 and 3** ([`pa-mm0/targets/thm23.mm0`](pa-mm0/targets/thm23.mm0), text verbatim from the frozen target
specification; proved, with no hypotheses, in [`pa-mm0/k215_final_root.mm0`](pa-mm0/k215_final_root.mm0)).
`bb215ArithmeticSentenceSource b` is the set-theoretic translation of the PA sentence "BB(215) = b"
([`pa-mm0/bb215_arithmetic_sentence_syntax.mm0`](pa-mm0/bb215_arithmetic_sentence_syntax.mm0)):

```
theorem ZFC_consistent_iff_BB215_no_value_provable_final {b: nat}:
 $ ~zfcInconsistent <-> A. b ~zfcProvable (bb215ArithmeticSentenceSource b) $;

theorem K215_full_consistency_BB215_nonprovability_final {b: nat}:
 $ (~zfcInconsistent <-> ~k215LiteralHalts) /\ (~k215LiteralHalts <-> A. b ~zfcProvable (bb215ArithmeticSentenceSource b)) $;
```

**G2, the second incompleteness theorem for ZFC** ([`pa-mm0/targets/incompleteness.mm0`](pa-mm0/targets/incompleteness.mm0),
sha256 `3b1e616fecf77fdc854fece70d17b32622f983bd058576683e70ba98229f7f6d`, frozen; each theorem is restated verbatim
as `<name>_inc` and proved in [`pa-mm0/zfc_incompleteness_root.mm0`](pa-mm0/zfc_incompleteness_root.mm0)). Read the
comment at the top of `incompleteness.mm0` first: `zfcPr(x)` is "K215 proves F(x)" for a fixed translation F of ZFC
formulas into K215, not the standard proof predicate of ZFC; theorems (D1)-(D5) state how it relates to ZFC
provability. The headline statements:

```
theorem ZFC_second_incompleteness_K215Pr_inc:
  $ ~zfcInconsistent -> ~zfcProvable (paFormulaSource zfcConPA) $;

theorem G2_abstract_inc (T tau: set) (P G: nat) {c a b u v: nat}
  (hP: $ paFormulaBound 1 P $)
  (hI: $ A. u A. v tau @ paFormulaImp u v = sfImp (tau @ u) (tau @ v) $)
  (hF: $ tau @ paFormulaFalse = sfBot $)
  (hB: $ A. c (paFormulaBound 0 c -> sfBound 0 (tau @ c)) $)
  (hT: $ A. c (paProvable 0 c -> sfTheoryProvable T (tau @ c)) $)
  (h1: $ A. c bb215ProvabilityD1T T tau P c $)
  (h2: $ A. a A. b bb215ProvabilityD2 P a b $)
  (h3: $ A. a bb215ProvabilityD3 P a $)
  (hG: $ bb215ProvabilityFixedPoint P G $):
  $ ~sfTheoryProvable T sfBot -> ~sfTheoryProvable T (tau @ bb215ProvabilityConsistencyPA P) $;
```

and, with the same statements as in `incompleteness.mm0`: `zfcPr_formula_inc`, `zfcConPA_sentence_inc`,
`zfcPr_PA_transfer_inc`, `zfcPr_D1_inc`, `zfcPr_D2_inc`, `zfcPr_D3_inc`, `zfcPr_fixed_point_inc`, `zfcPr_to_K215_inc`,
`zfcPr_from_K215_inc`, `zfcProvK215_defines_inc`, `zfcToK215_complete_inc`, `zfcToK215_false_faithful_inc`,
`zfcConPA_true_iff_consistent_inc` and `ZFC_second_incompleteness_K215Pr_end_inc` (16 in all; the full text is in
`zfc_incompleteness_root.mm0`).

**The Pi2 forms** (proved, with no hypotheses, in [`pa-mm0/b4_final.mm0`](pa-mm0/b4_final.mm0),
[`pa-mm0/b4b_final.mm0`](pa-mm0/b4b_final.mm0) and [`pa-mm0/b4b_bb.mm0`](pa-mm0/b4b_bb.mm0)). The `bd*` predicates are
bounded (Delta0) definitions in [`pa-mm0/bd_certs.mm0`](pa-mm0/bd_certs.mm0) and
[`pa-mm0/bd_certs_b4b.mm0`](pa-mm0/bd_certs_b4b.mm0); the theorems `bdK215Halt_iff`
([`b4_k215_halt.mm0`](pa-mm0/b4_k215_halt.mm0)), `bdZfcBot_iff` ([`b4_zfc_final.mm0`](pa-mm0/b4_zfc_final.mm0)),
`bdBB215Prf_iff` ([`b4b_bb.mm0`](pa-mm0/b4b_bb.mm0)) and `bdZfcConPrf_iff` ([`b4g2_final.mm0`](pa-mm0/b4g2_final.mm0))
prove in PA that `E. h bdK215Halt h`, `E. w bdZfcBot w`, `E. u bdBB215Prf u` and `E. u bdZfcConPrf u` are equivalent
to `k215LiteralHalts`, `zfcInconsistent`, "ZFC proves BB(215) = b for some b" and "ZFC proves Con(ZFC)" (`zfcConPA`):

```
theorem K215_sigma1 {h w: nat}: $ A. h (bdK215Halt h -> E. w bdZfcBot w) $;
theorem K215_sigma2 {h w: nat}: $ A. w (bdZfcBot w -> E. h bdK215Halt h) $;
theorem K215_thm2_pi2a {u w: nat}: $ A. u (bdBB215Prf u -> E. w bdZfcBot w) $;
theorem K215_thm2_pi2b {w u: nat}: $ A. w (bdZfcBot w -> E. u bdBB215Prf u) $;
theorem K215_thm3_pi2a {h u: nat}: $ A. h (bdK215Halt h -> E. u bdBB215Prf u) $;
theorem K215_thm3_pi2b {u h: nat}: $ A. u (bdBB215Prf u -> E. h bdK215Halt h) $;
theorem K215_G2_pi2 {u w: nat}: $ A. u (bdZfcConPrf u -> E. w bdZfcBot w) $;
```

### In HA (intuitionistic, `hpeano.mm0`)

The same 7 Pi2 statements, verbatim, are the theorems of [`receipt/thm23-g2/ha/b6-out.mm0`](receipt/thm23-g2/ha/b6-out.mm0)
(sha256 `29b8a7c405c180afd21cd04ed40295a11975c45346ceb87a609590cf97176e26`, 976,658 bytes). That file is the whole
HA specification: the Heyting arithmetic foundation `hpeano.mm0` verbatim (sha256 `625beda4...`, also in
[`routeb/src/foundation/`](routeb/src/foundation/)), the `bd*` definitions of `bd_certs.mm0` and `bd_certs_b4b.mm0` verbatim (import lines dropped; the copies in
`pa-mm0/` and `routeb/src/b4/` differ only in the import path of `peano.mm0`), and the 7 theorems; nothing else is assumed. The HA proof (`b6-out.mmb` on Zenodo) was produced from the PA binary of
`b4b_final` by the certifying translator in [`routeb/`](routeb/README.md) and checked by `mm0-c` (the `capacity3`
build) against `b6-out.mm0`; the control, `K215_G2_pi2` replaced by `F.`, is rejected
([`control.log`](receipt/thm23-g2/ha/control.log)).

### The files

- Statements and the definitions behind them: the `.mm0` files listed with their sha256 in
  [`manifests/final-spec-closure.sha256`](manifests/final-spec-closure.sha256) (Theorem 1) and
  [`manifests/thm23-g2-spec-closure.sha256`](manifests/thm23-g2-spec-closure.sha256) (Theorems 2, 3, G2 and the Pi2
  forms: the import closures of `targets/thm23.mm0`, `targets/incompleteness.mm0`, `b4_sigma.mm0`, `b4b_bb.mm0` and
  `b4g2_final.mm0`, plus the files stating the proved forms), all in git and all at the hashes of the receipt.
- The complete source closure: Theorem 1's in git plus the release
  [`thm1-inputs-v1`](https://github.com/elliotglazer/k215-pa/releases/tag/thm1-inputs-v1); the 1,864 further sources of
  `b4b_final` (6.2 GB, mostly generated `.mm1` proofs) in the release
  [`thm23-g2-inputs-v1`](https://github.com/elliotglazer/k215-pa/releases/tag/thm23-g2-inputs-v1), listed in
  [`manifests/thm23-g2-inputs.json`](manifests/thm23-g2-inputs.json). To fetch and check everything:

  ```
  sh scripts/fetch_large_inputs.sh all
  python3 -I scripts/check_sources.py receipt/thm23-g2/pa/report.json      # must end with "closure COMPLETE"
  ```

  (about 8.7 GB unpacked; the compressed download of `thm23-g2-inputs-v1` is about 0.2 GB.)
- The proof binaries: [doi:10.5281/zenodo.23872595](https://doi.org/10.5281/zenodo.23872595) (below).

## What you have to trust

MM0 separates the *specification* (`.mm0` files: definitions and theorem statements, which a reader audits) from
the *proof* (`.mm1` files, compiled to a binary `.mmb` proof file that the small verifier `mm0-c` checks against
the specification). Nothing in a `.mm1` file needs to be trusted.

1. **The axioms**: the 26 `axiom` declarations of [`lean-mm0/vendor/peano.mm0`](lean-mm0/vendor/peano.mm0)
   (sha256 `463a7d6e4f4791313dedcfd737053dcf2cc07b466371e263c38a994c6fb72052`): first-order logic with equality,
   the class-abstraction axioms (`elab`, `theid`, `the0`), and Peano arithmetic (`peano1`, `peano2`, the induction
   schema `peano5`, and the recursion equations for `+` and `*`). The project sources add no axioms:
   `pa-mm0/check.py` refuses any project file containing `axiom`.
2. **The meaning of the statement**: the definitions behind `k215LiteralHalts` and `zfcInconsistent`, i.e. the
   `.mm0` import closure of `targets/final.mm0`. Its 23 files are listed with their sha256 in
   [`manifests/final-spec-closure.sha256`](manifests/final-spec-closure.sha256); `checker/r0_check.py` verifies
   that the receipt used exactly these files.
3. **The checking tools** (pinned by sha256; the receipt records these hashes):

   | tool | sha256 | what it is |
   | --- | --- | --- |
   | `mm0-c` (capacity2) | `bba77622e7540e3f68eb1cc0c202c1cfcdaa2c5bed01754eb0b86d143e4f6371` | upstream `mm0-c` at digama0/mm0 commit `0d414c0bfdaaeb7fea571895127abc1fa5a3d956` plus [`checker/mm0-c-capacity.patch`](checker/mm0-c-capacity.patch) (sha256 `1ab54bfaa54a14e2eed982255e9daf2653d396abc16955b20cd53f0eada9d48e`), Windows x64 build (see below) |
   | `mm0-rs` | `c3be4fd028d3590a384f499c1a8e1ac762bcca957f6b20fb1a44794f54479412` | unmodified upstream `mm0-rs` (compiles `.mm1` to `.mmb` and joins the `.mm0` spec) |
   | `pa-mm0/check.py` | `a708f933f94a9ac159a488cbe5b99c897593f0b78b268ac4ee84fc5c311ab750` | the driver: closes the import graph, compiles, joins, runs `mm0-c`, and runs a false-conclusion control |
   | `peano.mm0` / `.mm1` / `.mmu` | `463a7d6e...` / `13fd383a...` / `3405aa9f...` | the vendored MM0 Peano library (full hashes in `check.py`) |

   The patch to `mm0-c` only enlarges the verifier's fixed-size name tables (term and theorem tries allocated at
   startup instead of statically) and fixes a 2 GiB file-size limit on Windows; it does not touch the
   proof-checking logic. The `mm0-rs join` output that `mm0-c` reads as the spec is reproduced byte for byte by
   the independent [`checker/mm0_join.py`](checker/mm0_join.py), so `mm0-rs` does not have to be trusted for it.

## The receipt

[`receipt/thm1/`](receipt/thm1/) is the report of the run that checked the proof:

| | |
| --- | --- |
| module | `k215_final_thm1`, status `PASSED`, `new_project_axioms: false`, `dependency_graph_closed: true` |
| sources | 4312 files (2156 `.mm0` + 2156 `.mm1`), each with its sha256 in `report.json` |
| joined spec | sha256 `4abeb03cdd127a4f005ab2e911149179078533af644e9377cd05ea483362dc95` (113,454,055 bytes) |
| proof input | flat (one linearized `.mm1`), sha256 `8053c32f301f0bb4b4e8ae872a8a5ce6636e89258707aa84f94a587b5f2eb1a4` |
| proof binary | `.mmb`, 4,627,501,632 bytes, sha256 `e92e0e00cfd69b949d53a9e7c3aa40b7760b301c77788bb37c39741a7701496f` |
| checked theorems | 18, including `K215_halts_iff_ZFC_inconsistent_final` |
| control | the same `.mmb` with the last theorem's statement replaced by `F.` is rejected by `mm0-c` with a unify failure at that theorem ([`reject-false.log`](receipt/thm1/reject-false.log)) |
| tools | the pinned `mm0-c` (capacity2), `mm0-rs`, `check.py` and vendor hashes above |
| resources | `mm0-rs` compile 13,071 s with a peak commit of 459 GB (459,410,030,592 bytes); `mm0-c` check 21 s, 7.0 GB; whole run 3.75 h (2026-10-23 11:43-15:28 UTC) on a 128-vCPU Windows host with 1 TiB RAM |

The `*_proved: false` fields in `report.json` are constants that `check.py` writes into every report; they do not
describe this run. What was checked is the module's theorem list against its `.mm0` spec.

## How to verify

Python 3.9 or later is needed for the scripts.

### 1. Check the receipt against the statement (no large download, a few minutes)

```
python3 -I checker/r0_check.py receipt/thm1/report.json
```

It prints `R0 OK` only if: the report is `PASSED` with the pinned tools and the false-conclusion control; every
`.mm0` file of the closure (all of them are in git) has the hash the report lists; the `mm0-rs join` of
`k215_final_thm1.mm0`, replicated by `checker/mm0_join.py`, has the report's `spec_sha256`; `targets/final.mm0` and
its closure match `manifests/final-spec-closure.sha256` and are in the report at those hashes; and the statement
of `K215_halts_iff_ZFC_inconsistent_final` in the joined spec equals theorem 1 of `final.mm0`. This shows *what*
the receipt covers; it does not re-run the proof checker.

### 2. Re-check the proof yourself

You need about 1.6 GB of disk for the large inputs, about 500 GB of RAM plus swap/commit (the receipt's compile
peak was 459 GB) and several hours.

1. Fetch the large inputs. 184 proof files (1.53 GB in total, the largest 127 MB) are generated outputs that are
   not stored in git; they are attached to the GitHub release `thm1-inputs-v1` as parts of one `.tar.gz`. The
   script downloads them, checks the parts against `SHA256SUMS`, unpacks into `pa-mm0/`, and checks every file
   against [`manifests/thm1-inputs.json`](manifests/thm1-inputs.json) and the receipt (both in git):

   ```
   sh scripts/fetch_large_inputs.sh
   python3 -I scripts/check_sources.py          # must end with "closure COMPLETE"
   ```

2. Build the tools. `mm0-c`: take `mm0-c/` from https://github.com/digama0/mm0 at commit
   `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`, apply `checker/mm0-c-capacity.patch` (`git apply`), and build
   `gcc main.c -O2 -Wall -o mm0-c.exe` (this builds without warnings on Linux). The pinned hash is the Windows
   x64 build made with w64devkit 2.10.0 (gcc 16.2.0) by
   `gcc main.c -O2 -Wall -DWIN32 -Wl,--no-insert-timestamp -o mm0-c.exe`; other platforms give another hash.
   Source hashes (sha256) before and after the patch:

   | file | upstream | patched |
   | --- | --- | --- |
   | main.c | `ecde31379241e38ca0b375df0f40b216e9108f6cfd45952ccb282658d883de17` | `5ab37446cd6db47690d1a3f35ef244d501c8a1cc2e25a288bb2f04b9fb4b024e` |
   | parser.c | `695bf56b4fe190e6ba369a8be854cd1031b2624929fc5fda995551e7bad00c39` | `5e189061a6c7c996db28a83cc3fcd65db71f73ebc619791a058e114ea4923c44` |
   | verifier_types.c | `87a0b9470de5ae0beff5edfa565952520957a39b250591b0067ebc4786b5490e` | `f9df8170d879206295de6387309ba63b929fefe39908dc7e9173a2615d1098fa` |
   | index.c, types.c, verifier.c, verifier_debug.c | `88214d05...`, `b3fc325b...`, `71428a11...`, `6db6e3dd...` | unchanged |

   `mm0-rs`: build upstream `mm0-rs` from the same repository. `check.py` calls the tools `mm0-rs.exe` and
   `mm0-c.exe` in the `--tools` directory, also on Linux.

3. Run the check (it writes `pa-mm0/artifacts/`):

   ```
   cd pa-mm0 && python3 -B -I check.py --module k215_final_thm1 --tools /path/to/tools && cd ..
   python3 -I scripts/compare_report.py pa-mm0/artifacts/report.json
   ```

   `check.py` exits non-zero unless `mm0-c` accepts the proof and rejects the false-conclusion control.
   `compare_report.py` then checks that your run covered exactly the receipt's sources, spec, proof input and
   theorems.

## Archived proof binaries (Zenodo)

The proof binaries are archived at [doi:10.5281/zenodo.23872595](https://doi.org/10.5281/zenodo.23872595)
(4.6 GB download, zstd-compressed, with `SHA256SUMS`, `MANIFEST.json` and a README giving the verification steps):

- **PA**: `b4b_final.mmb.zst` (9.70 GB unpacked, sha256 `25b7a4d5...`), checked by `mm0-c` against its joined
  specification over the 26 axioms of `peano.mm0`, which states 4 Pi2 theorems: `K215_thm2_pi2a` (a ZFC proof
  of a value sentence for BB(215) gives a ZFC proof of falsity), `K215_thm3_pi2a` / `K215_thm3_pi2b` (K215 halts
  iff ZFC proves a value sentence for BB(215)) and `K215_G2_pi2` (a ZFC proof of Con(ZFC) gives a ZFC proof of
  falsity). The binary also contains the Theorem 1 closure of this repository.
- **HA**: `b6-out.mmb.zst` (18.46 GB unpacked, sha256 `636804b4...`), checked by `mm0-c` against `b6-out.mm0`:
  the intuitionistic foundation `hpeano.mm0` (Heyting arithmetic), the bounded definitions, and 7 hypothesis-free
  Pi2 statements: Theorem 1 in both directions (`K215_sigma1`, `K215_sigma2`), Theorem 2 in both directions
  (`K215_thm2_pi2a`, `K215_thm2_pi2b`), Theorem 3 in both directions, and `K215_G2_pi2`. It was
  produced from the PA proof by a certifying negative + Friedman (A-) translation and checked with an `mm0-c` build whose hypothesis and
  unification stacks are 4096 instead of 256 (the recipe and pinned hash are in the archive).
  The translator, as the exact snapshot that produced this binary, is in [`routeb/`](routeb/README.md).

## Repository layout

| path | contents |
| --- | --- |
| `pa-mm0/*.mm0`, `pa-mm0/*.mm1` | the specification and proof sources of the theorem-1 closure (4128 files in git; the other 184 come from the release). Many are generator output; they are published as the exact files that were checked, so no generator has to be run or trusted |
| `pa-mm0/check.py`, `pa-mm0/targets/final.mm0` | the pinned driver and the frozen statement |
| `pa-mm0/targets/thm23.mm0`, `pa-mm0/targets/incompleteness.mm0` | the statements of Theorems 2, 3 and G2; their closure (260 further `.mm0` files in `pa-mm0/`) is in `manifests/thm23-g2-spec-closure.sha256`; the rest of the `b4b_final` closure comes from the release `thm23-g2-inputs-v1` |
| `lean-mm0/vendor/` | the vendored MM0 Peano library (`peano.mm0`, `.mm1`, `.mmu`) |
| `checker/` | `r0_check.py` with `final_spec_verify.py` and `mm0_join.py`; the `mm0-c` patch and its synthetic stress test `synth_mmb.py` |
| `manifests/` | `final-spec-closure.sha256` (the frozen statement's closure), `thm1-inputs.json` (the release files: name, sha256, bytes); `thm23-g2-spec-closure.sha256` and `thm23-g2-inputs.json` likewise for Theorems 2, 3, G2 |
| `receipt/thm1/` | `report.json`, `status.json` (run metadata) and `reject-false.log` of the checking run |
| `receipt/thm23-g2/` | the reports of the `b4b_final` and `zfc_incompleteness_root` checks (PA) and of the HA translation and check, with `b6-out.mm0`; `MANIFEST.json` lists each file and what was removed for publication |
| `scripts/` | `fetch_large_inputs.sh`, `check_sources.py`, `compare_report.py` |

## License

MIT (see [LICENSE](LICENSE)). The vendored files in `lean-mm0/vendor/` are unmodified copies from the MM0
project and `checker/mm0-c-capacity.patch` is a patch to MM0's `mm0-c`; they remain under the MM0 project's terms.
