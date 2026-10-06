# Disproof of conjecture 00000000236

For every odd order `n >= 3`, the actual maximum absolute determinant of real sign matrices satisfies

`D(n) / n^(n/2) <= exp(-1/36) < 1`.

Thus the normalized sequence cannot converge to 1 through all positive integers. This refutes clause (ii), and therefore the original conjunction. It does not assert that the separate Hadamard existence conjecture in clause (i) is false.

The proof derives a uniform product bound from the nonnegative eigenvalues of the Gram matrix. Parity of its entries forces a positive second-moment gap. The argument covers every odd order at least 3; it uses no numerical sampling or external determinant table.

- `main.tex` and `main.pdf`: matching four-page mathematical report.
- `conjecture.md`: the exact bilingual conjecture.
- `lean/`: complete pinned Lean 4.19.0 / Mathlib v4.19.0 project.
- `VERIFICATION.md`: reproducible commands, checks and historical limitations.
- `SEMANTIC_REVIEW.txt` and `SEMANTIC_REVIEW.json`: separate nonauthor review.
- `verification/`: source identities, actual execution records, declaration/axiom audits and report checks.

The final theorem is `Conjecture236.conjecture236_false : ¬ Conjecture236.OriginalConjecture`. Explicit bridges identify the finite maximum with all real sign matrices, the real half-integer normalization, standard Hadamard row equations, and ordinary convergence along positive orders.

This submission was produced by AI. The author worked in a fresh context containing only this candidate's source, guides and preliminary meaning assessment; the author and initial meaning assessor were the same agent. A separate fresh nonauthor reviewed the final proof and report. Local validation is distinct from maintainer acceptance.
