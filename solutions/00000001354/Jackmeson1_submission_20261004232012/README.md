# Disprove conjecture 00000001354: no uniform x^{1/4+ε} bound for Σ_{p≤x} e(α√p) over 0 < α ≤ 1

The conjecture asserts `Σ_{p≤x} e(√p) ≪ x^{1/4+ε}`, and that the same bound holds **uniformly** (Chinese: 一致成立, "holds uniformly"; restated as 均匀, "uniform") after replacing `√p` by `α√p`, `0 < α ≤ 1`.

**Key fact.** Uniformity means that one constant `C` and one range `x ≥ X` serve every `α ∈ (0,1]`. Take `α = 1/(8√x)`. Every phase `2πα√p` with `p ≤ x` then lies in `[0, π/4]`, so `|S_α(x)| ≥ Re S_α(x) ≥ cos(π/4) π(x)`.

**Contradiction.** Chebyshev's lower bound `π(x) ≥ ((x−1) log 2 − log(x+2))/log x` (Mathlib's `Chebyshev.pi_ge'`), together with `log x ≤ x^η/η`, makes `π(x)` exceed `K x^{1/4+ε}` for any `K` once `x` is large. So the uniform bound fails for every `0 < ε < 3/4`, and the conjecture is false.

**Lean.** `Conjecture1354/Basic.lean` (179 lines) defines `e t = exp(2πit)` and `S α x = Σ_{p ∈ Nat.primesLE ⌊x⌋₊} e(α√p)`. It defines the clauses `AlphaOneClause`, `UniformBound ε` (∃ C X, ∀ α ∈ (0,1], ∀ x ≥ X, ‖S α x‖ ≤ C x^{1/4+ε}) and `Conjecture`. It proves `not_uniformBound (0 < ε < 3/4)` and the main theorem `conjecture1354_false : ¬ Conjecture`. The axioms are `propext`, `Classical.choice` and `Quot.sound` only.

**Scope.** The refuted reading is the uniform one, which is the literal meaning of 一致成立 / "uniformly"; a threshold `X` is allowed, which is weaker than the usual `x ≥ 2`. Neither the `α = 1` clause on its own nor a non-uniform reading with `C = C(α)` is claimed. Both are open.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1354/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001354.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture1354.conjecture1354_false`, `Conjecture1354.not_uniformBound`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000001354 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
