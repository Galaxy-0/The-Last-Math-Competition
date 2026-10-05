# Disprove conjecture 00000007665: the q-Airy series has no zeros on the negative half-axis

The conjecture defines A_q(z) = Σ_{n≥0} (−1)ⁿ q^{n(n−1)/2} zⁿ/(q;q)_n and claims, for algebraic q ∈ (0,1), that its zeros are real and simple, that the k-th zero z_k on the negative half-axis satisfies z_k = −q^{−k}(1+O(q^{k/2})), and a spacing law.
- **Key estimate.** For x ≤ 0 every term equals q^{n(n−1)/2}|x|ⁿ/(q;q)_n ≥ 0; the series converges (ratio test) and its n = 0 term is 1, so A_q(x) ≥ 1.
- **Consequence.** For every q ∈ (0,1), in particular the algebraic q = 1/2, there are no negative zeros, and the asymptotic clause fails.
- **Complex reading.** Reading the clause for arbitrary complex zeros instead also fails: the asymptotics force Re z_k < 0, contradicting "all zeros real" (`conjecture_7665_false'`).
- **Spacing clause.** Left as an arbitrary proposition in Lean; the conjunction fails regardless.
- **Remark (not used in Lean).** By Euler's identity A_q(z) = ∏_{k≥0}(1 − z q^k), with zeros q^{−k} > 0; so the first clause is true and the refutation rests on the literal sign (−1)ⁿ, which appears in both languages.
- **Main theorems.** `C7665.conjecture_7665_false`, `C7665.conjecture_7665_false'`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 193 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture7665/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000007665.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C7665.conjecture_7665_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000007665 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
