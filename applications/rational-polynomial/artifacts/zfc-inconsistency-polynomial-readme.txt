A fixed integer polynomial for ZFC inconsistency
3 November 2026

The construction is

    P(w_1,...,w_N) = U(e_K215, 0, w_1,...,w_N),
    N = 878664928321.

Here U is the previously constructed universal rational polynomial.
The constant e_K215 is the exact 121586-digit integer in
k215-program-code.txt. It encodes a 7768-instruction, four-register
simulation of the literal K215 Turing machine at revision
c16fb4c751b27f03233929ec56135f32f342dfed of
https://github.com/elliotglazer/k215-pa.

With the mathematical inputs stated below, the claimed equivalence is

    P has a zero in Q^N  <=>  ZFC has a finite proof of contradiction.

This is a polynomial in many variables, with integer coefficients.
There are no remaining program or input parameters. Specializing U
adds no variables. This does not determine whether ZFC is consistent.

Files

zfc-inconsistency-polynomial.json
  Self-contained compact specification of the polynomial: includes
  the entire expression for U, the numerical constant e_K215, zero,
  and the precise substitution rule. Fixed coefficient prescriptions
  and finite products have the semantics documented in U. The file
  is not an expanded monomial list or a printout of every coefficient.

zfc-inconsistency-polynomial-proof.txt
  Proof of the Turing-to-register simulation, exact encoding and
  specialization; identifies the external mathematical inputs.

k215-program-code.txt and k215-program-code.hex
  The actual program constant in decimal and hexadecimal.

k215-transition-table.json and k215-register-program.json
  Extracted transition table and the full primitive register program.

k215-source-specification.json
  Pinned upstream specification files, final theorem source, receipt,
  hash manifest and license. This is not the full MM0 proof archive.

build-k215-specialization.js and verify-k215-specialization.js
  Reproducible construction and checks, using Node.js and files in this
  directory. No third-party JavaScript packages are needed.

k215-specialization-checks.json and k215-specialization-build.json
  Machine-readable verification and construction reports.

zfc-inconsistency-manifest.json
  SHA256 bindings for the new construction and its key dependencies.

Proof status

The rational equivalence uses the earlier written universality proof
for U, including its six-contact replacement and restricted pointwise
converse argument. It is not a Lean proof. The source and dependencies
are identified in universal-rational-end-to-end-proof.txt and
universal-rational-proof-manifest.json.

The K215 input is the upstream theorem
K215_halts_iff_ZFC_inconsistent_final. Its stated formula has no
hypotheses. The local checks bind the frozen specification and final
theorem to the repository's recorded successful MM0 receipt. The
4.6 GB MM0 proof binary was not downloaded and rechecked locally.

The new finite execution checks supplement the all-input simulation
proof; they are not a proof of the rational universality theorem and
do not decide whether K215 eventually halts.

Reproduce from the outputs directory

    node build-k215-specialization.js
    node verify-k215-specialization.js
    node verify-universal-proof-package.js

The first command recreates the table, register program, constant and
polynomial. The second checks the source bindings, all 430 transitions,
all encoded register instructions, finite simulation cases, and the
complete polynomial substitution. The third checks the earlier U
package's integrity and full assembly, not the validity of its prose
proofs.

Polynomial SHA256
2d6b97e7496ab8eb99f8b6e8b2f2e1792bbc8b5142ef73a6270ca6a1982e5a5e
