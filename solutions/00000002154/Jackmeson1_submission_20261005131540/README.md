# Disprove conjecture 00000002154: cycles are closed Eulerian but have nontrivial critical group

- **Claim.** Jac(G) has zero cyclic factors (Jac(G) = 0) exactly when G is a subdivision of a closed Eulerian graph.
- **Witness.** For every m ≥ 3 the cycle C_m is connected and has an Eulerian circuit, so it is (trivially) a subdivision of a closed Eulerian graph.
- **Jacobian.** φ(x) = Σ i·xᵢ mod m kills every principal divisor, because (Lf)ᵢ = 2fᵢ − f_{i−1} − f_{i+1}, and φ(δ₁ − δ₀) = 1, so Jac(C_m) maps onto ℤ/m and is nontrivial. The same holds for the reduced-Laplacian cokernel, and every direct-sum decomposition of Jac(C_m) has a nontrivial summand.
- **Objects in Lean.** Jac from `SimpleGraph.lapMatrix` in both standard forms (Div⁰/Prin and the reduced-Laplacian cokernel), the subdivision relation (repeated single-edge subdivision up to isomorphism), and closed Eulerian graphs via `Walk.IsEulerian`.
- **Scope.** The proof uses the zero-step subdivision; the converse direction (trees) is prose only.
- **Main theorems.** `C2154.not_classification`, `C2154.not_conjecture`, `C2154.jac_cycle_has_cyclic_factor`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 324 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #267 by orionsheep (closed, not merged) used the cycle C6, a subdivision of the Eulerian C3, with Jac(C6) = Z/6. The review rejected it because its Lean was vacuous: "The theorem proves 3*2 = 6 and 2 % 2 = 0 and 6 = 2*3 and 6 > 1 and 2 != 0 and 3 != 0; the C6 counterexample's decisive content (Jac(C6) = Z/6 via Matrix-Tree and Smith normal form, and that C6 subdivides the Eulerian C3) is prose- and script-only, with '6 > 1' standing in for nontriviality by fiat." This submission defines the critical group in Lean from Mathlib's `SimpleGraph.lapMatrix`, in two standard forms: Div^0/Prin, and the cokernel of the reduced Laplacian. It also defines the subdivision relation (an inductive closure of single-edge subdivisions up to isomorphism) and closed Eulerian graphs (connected, with a closed `Walk.IsEulerian`). For every cycle C_m with m >= 3, it proves that C_m is closed Eulerian, hence a subdivision of a closed Eulerian graph, and that both forms of Jac(C_m) map onto Z/m. So Jac(C_m) is nontrivial, and every direct-sum decomposition of it has a nontrivial summand. This is an infinite family, not one graph.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2154/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002154.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2154.not_classification`, `C2154.not_conjecture`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002154 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
