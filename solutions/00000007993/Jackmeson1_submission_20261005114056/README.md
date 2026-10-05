# Disprove conjecture 00000007993: the obstacle-problem singular set can have dimension n−1 > n−3

- **Reading.** The classical obstacle problem Δu = χ_{u>0}, u ≥ 0 (Figalli–Ros-Oton–Serra, arXiv:1912.00714, eq. (3.1), retrieved). Regular and singular points are defined exactly as in FRS §3: the blow-up limit is a half-space solution, or a convex 2-homogeneous polynomial with Δp ≡ 1.
- **Witness.** u(x) = x₁²/2 in the unit ball B₁ ⊂ ℝⁿ, for every n ≥ 3. It is C^∞ and u ≥ 0, Δu ≡ 1 (Mathlib Laplacian), and Δu = χ_{u>0} a.e. because {u = 0} is a Lebesgue-null hyperplane.
- **Free boundary.** FB = B₁ ∩ {x₁ = 0}. Every rescaling u(x₀+rx)/r² equals u, so every free-boundary point is singular and none is regular.
- **Refutation.** dim_H Sing = n−1 > n−3, which refutes the dimension clause; Reg = ∅ while FB ≠ ∅, which refutes "the regular part is dense in FB".
- **Literature.** Consistent with FRS: "Explicit examples show that the singular set could be in general (n−1)-dimensional"; the codimension bound holds only generically, and the conjecture has no "generic" hedge.
- **Main theorems.** `C7993.not_conjecture : ¬ (SingDimBound ∧ RegDenseInFB)`, `C7993.family` (all n ≥ 3), `C7993.witness`.
- **Scope.** Not addressed: the n = 2 clause (dimension 1 is allowed there) and the tangent-cone list clause.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 311 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7993/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007993.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7993.not_conjecture`, `C7993.family`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007993 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
