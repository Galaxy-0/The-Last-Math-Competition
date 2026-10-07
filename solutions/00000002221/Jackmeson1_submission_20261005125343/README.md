# Disprove conjecture 00000002221: (ZMod 2)³ has Krull dimension 0 but its Stone space has 3 > 2^(2^0) points

- **Witness.** For a field K and N ≥ 1, R = K^N is Artinian, so dim R = 0 and the claimed bound is 2^(2^0) = 2. Mathlib's `sigmaToPiHomeo` shows Spec R is a finite discrete space with N points ker(evᵢ), so every subset of Spec R is clopen and constructible (`every_subset`).
- **Stone points.** Evaluating subsets at each point gives N distinct homomorphisms B → 2, so the Stone space has at least N points (`stone_card_of_hom`).
- **Readings of "Booleanization".** (R1) the constructible Boolean algebra (Mathlib `IsConstructible`); (R2) the clopen algebra `Clopens (Spec R)`; (R3) `WithConstructibleTopology (Spec R)`; (R4) any Boolean algebra mapping onto subsets of Spec R that include all singletons.
- **Main theorems.** `C2221.conjecture_false_constructible`, `conjecture_false_clopens`, `conjecture_false_constructibleTopology`; each quantifies over all commutative rings R with `ringKrullDim R = d`, witness R = (ZMod 2)³ (`ringKrullDim_pi`).
- **Not covered.** A regular-open reading (equal to the power set here, prose only), algebras not made of subsets of Spec R, and readings restricted to local rings.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 186 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #219 by orionsheep was closed without merging. The reviewer rejected the formalization: "the Lean proves only 2^(2^0) = 2, 3 > 2, 8 > 2; the ring k³, Spec, Booleanization, Stone space, and Krull dimension appear nowhere." Its prose also said the Stone space has 2³ = 8 points. In fact 8 is the cardinality of the Boolean algebra, and the Stone space has 3 points; the conclusion survives because 3 > 2. This submission formalizes the actual objects for R = K^N (`Fin N → K`, K any field). It proves `ringKrullDim (Fin N → K) = 0`. It proves that `PrimeSpectrum R` is discrete and finite (via Mathlib's `sigmaToPiHomeo`) and that every subset of it is `IsClopen` and `IsConstructible`. It defines the Stone space as `BoundedLatticeHom B Bool` and proves it has at least N points when B is the constructible Boolean algebra (R1), `Clopens (PrimeSpectrum R)` (R2), or any Boolean algebra mapping onto a family of subsets containing all singletons (R4). It also proves that `WithConstructibleTopology (PrimeSpectrum R)` has at least N points (R3). The main theorems `conjecture_false_constructible`, `conjecture_false_clopens` and `conjecture_false_constructibleTopology` refute "for all commutative rings R with ringKrullDim R = d, #Stone ≤ 2^(2^d)", witnessed by R = (ZMod 2)³.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2221/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002221.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2221.conjecture_false_constructible`, `C2221.conjecture_false_clopens`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002221 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
