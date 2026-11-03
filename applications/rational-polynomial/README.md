# Rational polynomial application of K215

This directory contains an experimental application, constructed with Codex on
3 November 2026. It specifies a polynomial with integer coefficients whose
rational solvability is intended to characterize ZFC inconsistency.

**The rational equivalence depends on the accompanying written universality
argument. That argument has not been independently reviewed or checked by a
proof assistant.** The repository's MM0 theorem proves the K215 halting
equivalence. It does not verify the additional arithmetic argument in this
directory. Successful execution of the checks below does not establish that
argument.

## Construction

Let `U(e,n,w)` be the fixed polynomial specified in
`artifacts/universal-rational-equation.json`, after decompression. Its written
universality argument claims, for ordinary nonnegative integers `e,n`, that
`U(e,n,w)=0` has rational witnesses exactly when register program `e` halts on
input `n`.

The supplied compiler translates the literal K215 machine into 7,768
increment/decrement/test instructions on four registers. The exact program
number `e_K215` has 121,586 decimal digits and is included in
[`k215-program-code.txt`](artifacts/k215-program-code.txt). Define

```text
P(w) = U(e_K215, 0, w).
```

This substitution yields one polynomial in 878,664,928,321 variables with
integer coefficients and no remaining program or input parameters. Assuming
the stated universality property of `U`, the composition gives

```text
P has a zero in Q^878664928321
  iff the compiled register program halts on input zero
  iff K215 halts on its blank tape
  iff ZFC has a finite formal proof of contradiction.
```

The expression is a finite polynomial specification with fixed, terminating
coefficient prescriptions. The expanded monomial list and expanded values of
all coefficients are not supplied. The construction does not determine whether
ZFC is consistent.

## Read the argument

- [Specialization proof](artifacts/zfc-inconsistency-polynomial-proof.txt)
  gives the loop invariants, simulation in both directions, numerical encoding
  and composition with K215.
- [Universality argument](artifacts/universal-rational-end-to-end-proof.txt)
  describes the arithmetic construction and its dependencies, including the
  six-contact height estimate and restricted pointwise converse.
- [Universality dependency manifest](artifacts/universal-rational-proof-manifest.json)
  identifies the accompanying component arguments and computational evidence.
- [Original construction guide](artifacts/zfc-inconsistency-polynomial-readme.txt)
  describes the individual artifacts and reproduction commands.

The original files are archived byte for byte. Their references to an `outputs`
directory mean this directory's `artifacts` directory. Historical status notes
in those files do not change the proof status stated above.

## Reproduce the executable checks

Use Node.js 22 or later. No package installation or network access is required.
From the repository root, run

```sh
node applications/rational-polynomial/verify.js
```

The command checks the distribution hashes, decompresses the large generated
JSON files into ignored local files, checks both original manifests, verifies
the K215 specialization and rechecks the full assembly of `U`. It refuses to
overwrite an existing artifact whose hash differs. Allow approximately 120 MB
of disk space for the decompressed artifacts.

The specialization checks cover all 430 transitions, every encoded register
instruction, 21,500 transition executions, a 32-step blank-tape comparison,
the exact substitutions and the complete embedded source polynomial. The
universality package checks artifact identity and polynomial assembly. Neither
command checks the validity of the written arithmetic proofs.

To decompress and check file hashes alone, use `--prepare-only`. To regenerate
the K215 specialization after preparing the artifacts, run

```sh
node applications/rational-polynomial/artifacts/build-k215-specialization.js
node applications/rational-polynomial/verify.js
```

The resulting polynomial is
`artifacts/zfc-inconsistency-polynomial.json`, with SHA256
`2d6b97e7496ab8eb99f8b6e8b2f2e1792bbc8b5142ef73a6270ca6a1982e5a5e`.

## Source and verification boundary

The K215 table and theorem are pinned to repository revision
`c16fb4c751b27f03233929ec56135f32f342dfed`. The source archive includes the frozen
23-file statement closure, final theorem source, recorded MM0 receipt and
upstream license. The checks bind those files to the receipt. The full MM0
proof binary was not rerun for this application.

The arithmetic package records OpenAI math source revision
`4eaee87548250b2682affda7d05d947c05554bae`. Its written arguments and source-range
checks are included for review. This application is not an additional MM0 or
Lean theorem and is not evidence that ZFC is inconsistent.
