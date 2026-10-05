# Disprove conjecture 00000000539: (x0²,x1²,x2²,x3²) has h-vector (1,4,6,4,1) with 6 > 4 > 1

- **Conjecture.** The h-vector of every quadratic monomial ideal has no three adjacent strictly decreasing terms.
- **Counterexample.** Over every field K: I = (x0², x1², x2², x3²) in K[x0..x3], a quadratic monomial ideal.
- **Objects in Lean.** (S/I)_j as the image of the degree-j homogeneous polynomials, HF(j) = finrank, the Hilbert series, and the h-polynomial (HS·(1−t)^d = h, h(1) ≠ 0).
- **General lemma.** For any monomial ideal, dim (S/I)_j = the number of standard monomials of degree j (via Mathlib's `mem_ideal_span_monomial_image`).
- **Computation.** HF(j) = C(4,j), so HS = (1+t)⁴; the h-polynomial is uniquely (1+t)⁴, and the h-vector (1,4,6,4,1) contains 6 > 4 > 1.
- **Literal reading.** For the Hilbert function of I itself (via rank-nullity), h_I = 4t² − 6t⁴ + 4t⁶ − t⁸ (unique), with 4 > 0 > −6.
- **Squarefree remark.** The edge ideal of four disjoint edges, (x0y0, …, x3y3), has the same h-vector (1,4,6,4,1); this is argued in proof.tex, not in Lean.
- **Not formalized.** The shellability clause; the conjunction fails because its universal first clause fails.
- **Main theorems.** `C539.conjecture_false`, `C539.conjecture_false_ideal_reading`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 333 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture539/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000539.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C539.conjecture_false`, `C539.conjecture_false_ideal_reading`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000539 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
