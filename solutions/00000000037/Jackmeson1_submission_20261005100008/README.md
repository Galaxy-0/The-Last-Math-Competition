# Prove conjecture 00000000037: the primes up to N contain a Sidon set of size (N/log N)^{1/2−o(1)}

- **Reading.** There are Sidon sets A_N of primes ≤ N with (N/log N)^{1/2−ε} ≤ |A_N| ≤ (N/log N)^{1/2+ε} for every real ε > 0 and all large N. Equivalently, |A_N| = (N/log N)^{1/2−δ(N)} with δ(N) → 0.
- **Construction.** The Erdős–Turán Sidon set {2pk + (k² mod p) : k < p}, with p a Bertrand prime of size about √π(N/2)/4, translated by a shift b ≤ N/2 chosen by averaging. The translate keeps at least p·π(N/2)/N of its elements prime, and these primes form a Sidon set (a subset of a translate of a Sidon set).
- **Lower bound.** Chebyshev's bound (Mathlib `Chebyshev.pi_ge`) then gives |A_N| > N^{1/2−ε} for large N.
- **Upper bound.** The differences of a Sidon set are distinct, so every Sidon set of naturals ≤ N has |A|² − |A| ≤ 2N; the exponent 1/2 is optimal (`sidon_upper`).
- **Main theorems.** `C37.conjecture_37` (ε form), `C37.conjecture_37_littleO` (literal δ form), `C37.conjecture_37_firstPrimes` (first-N-primes reading), `C37.sidon_upper`.
- **Scope.** Not covered: a reading asking for one infinite Sidon set of primes with counting function ≥ (N/log N)^{1/2−o(1)}.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 418 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture37/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000037.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C37.conjecture_37`, `C37.conjecture_37_littleO`, `C37.sidon_upper`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000037 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
