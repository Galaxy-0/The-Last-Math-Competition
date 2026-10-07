# Disprove conjecture 00000001857: the closed form gives c₃ ≈ 0.2168 < 1, so τ(G) ≁ c₃ⁿ and c₃ ≠ 1.175…

- **Closed form.** c₃ = ((√3−1)/2)²·exp(∫₀^{2π} log(3−2cos θ) dθ/4π) is computed exactly in Lean as (2−√3)/2·(1+√5)/2 ≈ 0.2168, using ∫₀^{2π} log(3−2cos θ) dθ = 2π·log((3+√5)/2) (Mathlib's circle average of log|z−a|).
- **Not 1.175….** For every integration window of length at most 4π (including [0,2π] and [−π,π]) the closed form is below 1, so it is not in [1.175, 1.176).
- **Spanning trees.** τ(G) is the number of spanning trees of a Mathlib `SimpleGraph`; every connected finite graph has τ ≥ 1.
- **Asymptotic clause.** Along every sequence of connected graphs with n → ∞, τ/c₃ⁿ → ∞, τ is not O(c₃ⁿ), and τ^{1/n} does not tend to c₃; so "τ(G) is asymptotically c₃ⁿ" fails under all three readings.
- **Random model.** For the uniform random 3-regular graph on Fin n, P(|τ/c₃ⁿ − 1| < ε) ≤ P(disconnected) for all large n; random regular graphs are a.a.s. connected (retrieved Wikipedia quote; a hypothesis in Lean), so the claim fails in probability.
- **Not refuted.** A reading that drops the formula and keeps only "τ ≈ 1.175ⁿ".
- **Main theorem.** `C1857.conjecture1857_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 315 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #236 by orionsheep ("Disproof of 00000001857: closed form evaluates to 0.2168, not the claimed 1.175") was closed without merging. Reviewer lidangzzz wrote: "the main theorem is a vacuous implication over an abstract Nat (any c2 < 1000 ≠ 2350, plus 9 > 4 ∧ 25 > 20); none of τ(G), c₃, the integral, exp, or √ appears in Lean, and the entire closed-form evaluation ≈ 0.217 vs 1.175 exists only in prose." This submission formalizes the conjecture's actual objects in Lean 4 with Mathlib. The spanning-tree count τ(G) is the number of trees T ≤ G of a `SimpleGraph`, and the Lean also shows it equals the number of spanning-tree edge subsets. The closed form c₃ is written with the real interval integral, `Real.exp` and `√`. The Lean proves that the closed form is < 1 for every integration window of length ≤ 4π, so it is not 1.175…. It also computes ∫₀^{2π} log(3 − 2cos θ) dθ = 2π·log((3+√5)/2), giving c₃ = (2−√3)/2·(1+√5)/2 ∈ (0.2167, 0.2169). It then refutes the asymptotic clause itself: along every sequence of connected finite graphs with n → ∞, τ/c₃ⁿ → ∞, τ ≠ O(c₃ⁿ) and τ^{1/n} ↛ c₃, because τ ≥ 1. For the uniform random 3-regular graph on `Fin n`, P(|τ/c₃ⁿ − 1| < ε) ≤ P(disconnected) for all large n.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1857/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001857.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C1857.conjecture1857_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001857 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
