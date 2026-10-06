# Prove conjecture 00000002481: the Durfee square decomposition, its generating function q^{d²}/(q;q)_d², and its conjugation symmetry

- **Reading.** "Symmetric splicing" is not a standard term; it is read as the classical Durfee decomposition: (1) the decomposition, (2) the generating-function factorization into corner pieces, (3) conjugation symmetry. Known result, attributed (Wikipedia "Durfee square", retrieved).
- **Objects.** Partitions are Mathlib `YoungDiagram`s; `durfee` = side of the largest square inside the diagram (`isGreatest_durfee`, `isGreatest_durfee_rowLen`).
- **(1) Decomposition.** `durfeeEquiv d`: diagrams with Durfee side d ≃ (diagrams in rows < d, i.e. ≤ d parts) × (diagrams in columns < d, i.e. parts ≤ d); `durfee_decomposition` gives the cell-level splitting into square, right piece and lower piece, with |λ| = d² + |α| + |β|.
- **(3) Conjugation.** `durfee_transpose`, `durfeeEquiv_transpose`, `glue_transpose`: conjugation fixes d, swaps the two pieces (each conjugated), and (glue α β)ᵀ = glue βᵀ αᵀ.
- **(2) Generating functions.** `gf_durfee`: GF_d = q^{d²}·C_d·C'_d; `cnt_colsLt`: C'_d = C_d; `gf_rowsLt_mul_prod`: C_d·(q;q)_d = 1; `gf_durfee_mul`: GF_d·(q;q)_d² = q^{d²}; `hasSum_gf_durfee`: Σ_d GF_d = Σ_λ q^{|λ|} in ℤ[[q]].
- **Conventions.** 1/(q;q)_d is stated as "times (q;q)_d equals 1"; the empty partition (d = 0) is included; no bridge to `Nat.Partition`.
- **Main theorems.** `C2481.durfee_decomposition`, `C2481.durfeeEquiv_transpose`, `C2481.hasSum_gf_durfee`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 541 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2481/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002481.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2481.durfee_decomposition`, `C2481.durfeeEquiv_transpose`, `C2481.hasSum_gf_durfee`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002481 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
