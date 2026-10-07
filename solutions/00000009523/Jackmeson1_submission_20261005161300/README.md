# Disprove conjecture 00000009523: the dephasing qubit channel has C_E = χ = log 2

- **Claim refuted.** The first conjunct: C_E(φ) > χ(φ) strictly for every channel except the completely depolarizing one. Refuting it refutes the conjunction; the ratio clause (max C_E/χ = d) is not addressed.
- **Witness.** The completely dephasing qubit channel D(X) = diag(X₀₀, X₁₁): CPTP (Kraus form with diagonal projectors), non-constant on states, and not the depolarizing channel.
- **C_E.** For any purification ψ, (id ⊗ D)(|ψ⟩⟨ψ|) is block-diagonal with rank-one blocks whose traces are ρ_aa, so S(ω) = S(Dρ) and I(ρ, D) = S(ρ) ≤ log 2; the Bell state attains this bound.
- **χ.** The ensemble {½: |0⟩⟨0|, ½: |1⟩⟨1|} gives χ ≥ log 2, and every ensemble gives at most log 2. So C_E(D) = χ(D) = log 2.
- **Objects in Lean.** Von Neumann entropy via `Matrix.IsHermitian.eigenvalues` and `Real.negMulLog` (computed through characteristic-polynomial roots), id ⊗ Φ entrywise, complete positivity for all k, the BSST mutual information with purifications, and C_E and χ as sSup values (proved attained).
- **Main theorems.** `C9523.conjecture9523_false` (exception = depol 2), `C9523.conjecture9523_false_strong` (exception = every channel constant on states, plus χ > 0), `C9523.deph_counterexample`.
- **Consistency.** Shirokov (arXiv:1202.3449, retrieved): C_E = χ for classical-quantum channels.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 338 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture9523/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000009523.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C9523.conjecture9523_false`, `C9523.conjecture9523_false_strong`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000009523 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
