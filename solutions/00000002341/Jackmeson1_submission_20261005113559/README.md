# Disprove conjecture 00000002341: the pseudospectral area identity holds only for scalar matrices

- **Claim.** The area of the ε-pseudospectrum {z : ‖(A−zI)⁻¹‖ > 1/ε} equals πε²(1 + ‖A*A − AA*‖_HS/2), and the area grows exactly like ε².
- **Result.** For an n×n complex matrix (n ≥ 1, operator 2-norm), the identity holds for all ε > 0 iff A = cI (`areaIdentity_iff_scalar`).
- **Proof idea.** The pseudospectrum contains the ε-discs around the eigenvalues and lies in the disc of radius ‖A‖ + ε. Large ε forces the HS term to vanish (A normal); small ε forbids two distinct eigenvalues; a normal matrix with one eigenvalue is scalar (spectral radius = norm in a C*-algebra).
- **Counterexample.** diag(1,−1): claimed πε², actual ≥ 2πε² for ε ≤ 1 (`conjecture_2341_false`).
- **Exact ε² law.** If two spectral values are distinct, the area is never Kε² for all ε, in any unital Banach algebra with ‖1‖ = 1 (`no_exact_eps_sq_law`).
- **Conventions.** ‖(A−zI)⁻¹‖ = ∞ at eigenvalues; strict ">" as in the text; area = Lebesgue measure; HS norm written out.
- **Scope.** "Random matrix" is refuted pathwise (every non-scalar realization); the almost-sure and expected-area readings are argued in the report only. The asymptotic "order ε² as ε → 0" reading is not refuted.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 292 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2341/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002341.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2341.conjecture_2341_false`, `C2341.areaIdentity_iff_scalar`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002341 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
