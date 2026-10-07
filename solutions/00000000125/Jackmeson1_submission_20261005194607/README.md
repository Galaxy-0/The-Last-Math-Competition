# Disprove conjecture 00000000125: the prime-trace count in SL₂(F_p) is not ~ c·p²/log p

- **Reading.** N(p) = #{A ∈ SL₂(F_p) : |lift(tr A)| is prime}, with the trace lifted to ℤ by the centred lift (`ZMod.valMinAbs`) or the [0, p) lift (`ZMod.val`); p → ∞ through the primes. Both languages state the order p²/log p.
- **Trace-2 family.** T(a, b) = [[a, b], [−(a−1)²b⁻¹, 2−a]] (a ∈ F_p, b ∈ F_p^×) has determinant 1 and trace 2, and distinct pairs give distinct matrices.
- **Bound.** Both lifts send 2 to the prime 2 for p ≥ 5, so N(p) ≥ p(p−1) and N(p)/(p²/log p) ≥ log p/2 → ∞.
- **Refutation.** N(p) is not O(p²/log p); hence for every real c, N(p) is not ~ c·p²/log p and N(p)/(c·p²/log p) does not tend to 1.
- **Remark (not formalized).** The trace fibres have p² + χ(t² − 4)·p elements, so the true order is p³/log p; under that order the Sato–Tate clause would carry no content, which is why the stated p² is taken at face value.
- **Not covered.** A lift that sends 2 to a non-prime for infinitely many p.
- **Main theorem.** `C125.conjecture125_false` (both lifts; ratio form plus failure of O(p²/log p)); general-lift theorems `not_tendsto_ratio`, `not_isEquivalent`, `not_isBigO`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 190 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture125/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000125.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C125.conjecture125_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000125 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
