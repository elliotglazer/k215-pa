A universal rational Diophantine polynomial: construction and written proof
3 November 2026

The polynomial is defined by universal-rational-equation.json. For the
effective universal program numbering in universal-interpreter-spec.txt,
the written proof establishes, for ordinary nonnegative integers e,n,

  program e halts on input n
      if and only if
  U(e,n,w)=0 for some w in Q^878664928321.

U has integer coefficients. There are 878,664,928,323 total variables
including the two input parameters. This is a sufficient bound from this
construction; no minimality is claimed.

Start with universal-rational-end-to-end-proof.txt for the theorem and
its proof. universal-rational-completion-audit.txt records the exact
requirements, evidence and scope of the completed written argument.
universal-rational-proof-manifest.json binds that argument, its component
proofs, source code and computational reports to their SHA256 hashes.

Representation

The JSON file is 40,644,116 bytes, with SHA256
 be7347c439459759121cda9656eda501afd75ca48897aa0f0acf5f85f6a43b1f.

It contains reusable polynomial expressions, exact substitution rules,
fixed integer coefficient algorithms, division-polynomial recurrences,
and a finite forbidden-box product. Their finite expansion defines one
ordinary polynomial. Neither its enormous coefficients nor its expanded
monomial list have been printed. Every coefficient algorithm terminates
mathematically and is independent of the supplied e,n; practical expansion
is not claimed. No external predicate or oracle is part of its syntax.

Its top-level definition is

 U = V(A,B,v)^2 + Gamma(e,A,g_e)^2 + Gamma(n,B,g_n)^2.

V represents halting in an explicitly specified elliptic model. Gamma
connects an ordinary integer to its model code using a decidable index
accuracy relation and a rational proximity test. A and B are part of
the rational witness tuple; the user does not calculate them externally.
No exactness assertion is made for nonintegral rational input parameters.

Proof scope

This is a written mathematical construction using the cited classical
theorems and the audited restricted pointwise 2-converse argument. It is
not a Lean proof or a claim of independent expert verification. The proof
uses a SIX-contact height estimate. It does not complete the separate
theta-coordinate calculation for the original five-contact family.

The final review corrected an intermediate matrix-inverse estimate in
paired-functional-and-uniformity-proof.txt. The adjugate/geometric-series
argument gives a pole bound 4M at precision 2^M, and retains the required
clearing bound 16mM. This changed no coefficient or witness count in U.

The compiler, accuracy program, translated expression and witness scopes
have full source/artifact binding checks. The assembly auditor rejects
nine deliberate corruptions. Finite algebra checks supplement the
component proofs. These computations do not prove the quantified
arithmetic assertions by testing instances.

The generator and JSON retain historical diagnostic status text. The
polynomial is defined by its expressions and substitution semantics,
not those diagnostic strings. They were retained so the audited artifact
and its hash remain unchanged. The current proof status is in this file
and universal-rational-completion-audit.txt.

Rechecking the delivered package

With Node.js, run from this directory:
 node verify-universal-proof-package.js

This checks manifest hashes, existing source bindings, the expression's
full assembly, and agreement of the recorded counts. It does not verify
the natural-language mathematical proofs. Individual verify-*.js files
provide the finite checks described in the completion audit.

ZFC specialization

A program that enumerates finite formal ZFC proofs and halts on a proof
of 0=1 has a code e_ZFC in the stated numbering. Thus substituting
e=e_ZFC and n=0 produces an integer-coefficient multivariable polynomial
with a rational zero exactly when a formal ZFC contradiction exists.
The numerical code of that separate program has not been compiled here.
This consequence does not decide whether ZFC is consistent.
