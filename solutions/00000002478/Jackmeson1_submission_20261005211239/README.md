# Prove conjecture 00000002478: the q-binomial (Gauss) expansion and its finite-field subspace-counting content

- **Expansion.** ∏_{i<n}(1 + q^i t) = Σ_k q^{k(k−1)/2}·[n k]_q·t^k, proved as a polynomial identity in q and t (valid in every commutative semiring), by induction on n: factor out (1 + t), substitute t → qt, and shift the index with q-Pascal and C(k+1,2) = C(k,2) + k.
- **Counting content.** For every finite field F with q elements, [n k]_q is the number of k-dimensional subspaces of Fⁿ; hence ∏(1 + q^i t) = Σ_k q^{k(k−1)/2}·N_q(n,k)·t^k, and the counts satisfy q-Pascal.
- **Gaussian binomial.** Defined by recursion; its equality with the textbook product formula is proved.
- **Scope.** "Closes under the Gaussian lattice" is read as q-Pascal closure; the subspace lattice's interval closure is proved in the companion package for 00000002490 and not repeated here. Wikipedia names this identity the Cauchy binomial theorem; the conjecture calls it the Gauss expansion.
- **Source.** Wikipedia, "Gaussian binomial coefficient", including its q-binomial theorem section (retrieved; quotes machine-checked).
- **Main theorem.** `C2478.conjecture_2478`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 304 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2478/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002478.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2478.conjecture_2478`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002478 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
