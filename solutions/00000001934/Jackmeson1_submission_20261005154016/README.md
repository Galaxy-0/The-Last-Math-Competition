# Disprove conjecture 00000001934: SL(n,ℤ) acts analytically on S^{n−1} with infinite image

- **Claim refuted.** Clause 1: every action of SL(n,ℤ) (n ≥ 3) on an (n−1)-manifold has finite image.
- **Counterexample.** For every n ≥ 3, A·v = Av/‖Av‖ on the unit sphere S^{n−1}, a compact connected analytic (n−1)-manifold. Lean proves it is a `MulAction`, that each element acts by a C^ω map (Mathlib's sphere manifold structure), and that the transvections I + k·E₀₁ act by pairwise distinct permutations, so the image is infinite.
- **Generality.** The refuted statement `Clause1At r n` covers every regularity r (0 = continuous, …, ∞, ω) and even assumes M compact, connected, Hausdorff and boundaryless; the conjunction with clause 2 fails whatever clause 2 means (`not_conjecture`).
- **Remark.** Zimmer's conjecture concerns dim < n−1 (and volume-preserving actions); this is the standard example showing the bound is sharp. The text has no volume-preserving hypothesis.
- **Main theorems.** `C1934.not_clause1At`, `C1934.not_clause1`, `C1934.not_conjecture`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 194 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1934/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001934.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1934.not_clause1At`, `C1934.not_conjecture`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001934 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
