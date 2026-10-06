# Prove conjecture 00000002450: the Cantor group is a nondiscrete all-smooth Polish group

- **Claim.** A plain existential: a nondiscrete Polish group all of whose Borel-action orbit equivalence relations are smooth. This is a known fact (compact groups are all-smooth); we give a self-contained proof.
- **Witness.** G = (ℤ/2)^ℕ (`Multiplicative (ℕ → ZMod 2)`): compact Polish, and nondiscrete because it is compact and infinite; it is uncountable and has Borel actions with uncountably many orbits, so it is not a degenerate witness.
- **General theorem.** `allSmooth_of_compact`: every compact Polish group is all-smooth, for every Borel action (measurable action map; no continuity assumed) on every standard Borel space.
- **Invariant.** x ↦ (μ{g : e(g⁻¹·x) < q})_{q∈ℚ}, with μ a Haar measure and e : X → ℝ a Borel embedding; it is Borel (Fubini measurability) and invariant (left invariance of μ).
- **Separation.** Orbits are analytic; Lusin separation (`AnalyticSet.measurablySeparable`) gives a Borel set distinguishing the pushforward measures, which are determined on rational half-lines. "Smooth" = Borel reduction to equality on the Polish space ℚ → ℝ.
- **Conventions.** Polish group = `Group` + `IsTopologicalGroup` + `PolishSpace` with `BorelSpace`; the smooth target space is in `Type`.
- **Main theorem.** `C2450.exists_nondiscrete_allSmooth_polishGroup`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 152 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2450/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002450.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2450.exists_nondiscrete_allSmooth_polishGroup`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002450 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
