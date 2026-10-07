# Disprove conjecture 00000008565: Cayley graphs of ℤ/n (n ≥ 3) never have simple spectrum

- **Claim refuted.** The second of four conjoined laws: "simple spectrum (no multiplicity) is generic for cyclic generating sets of abelian groups". Refuting it refutes the conjunction.
- **Result.** For every n ≥ 3 and every S ⊆ ZMod n, the adjacency matrix of Mathlib's undirected Cayley graph `SimpleGraph.addCayley S` has an eigenspace of dimension ≥ 2 (`exists_eigenspace_finrank_ge_two`) and an eigenvalue of algebraic multiplicity ≥ 2 (`exists_charpoly_rootMultiplicity_ge_two`), hence no simple spectrum (`not_hasSimpleSpectrum`).
- **Witness eigenvectors.** χ(x) = exp(2πix/n) and its conjugate χ(−x): they share an eigenvalue because the neighbourhood of 0 is closed under negation, and they are independent because χ(1) ≠ χ(−1) for n ≥ 3.
- **Robustness.** The textbook matrix [v − u ∈ S] for any symmetric S (loops allowed) is covered (`connMatrix_not_hasSimpleSpectrum`); not generic in any sense: zero generating sets have simple spectrum, while {1} generates (`simple_spectrum_not_generic`).
- **Faithfulness.** `addCayley_adj_iff_sub_mem`: Mathlib's graph has u ~ v iff v − u ∈ S for symmetric S without 0 (Wikipedia "Cayley graph", retrieved and quoted).
- **Scope.** Undirected Cayley graphs (real symmetric adjacency operator, as in the Definition line); the directed-digraph reading is not refuted. Clauses 1, 3 and 4 and non-cyclic abelian groups are not formalized.
- **Main theorem.** `C8565.not_hasSimpleSpectrum`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 207 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8565/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008565.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C8565.not_hasSimpleSpectrum`, `C8565.simple_spectrum_not_generic`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000008565 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
