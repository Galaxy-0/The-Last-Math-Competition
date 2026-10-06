# Disprove conjecture 00000000732: every unit of ℚ(ζ_m), m ≥ 3, has norm +1, so the unit index is 1, not φ(m)/2^{ω(m)}

- **Object as defined.** ε(m) = [E : E₁], with E the units of the ring of integers of `CyclotomicField m ℚ` and E₁ the kernel of the absolute norm `Algebra.norm ℚ` on them.
- **Key lemma.** `norm_nonneg_of_isTotallyComplex`: the embeddings above a complex place are φ and its conjugate, so N(x) = ∏ |φ_w(x)|² ≥ 0. Hence every unit has norm +1 and ε(m) = 1 for all m > 2 (`unitIndex_eq_one`).
- **Exact-equality clause.** At m = 7 the claim gives φ(7)/2 = 3 ≠ 1; it fails at every odd prime power q ≥ 7.
- **Supremum and asymptotics.** ε(m) ≤ 2 for every m, so a supremum over any set of conductors misses the claimed value; along products of k distinct primes ≥ 11, φ(m)/2^{ω(m)} ≥ 5^k while ε ≤ 2, so both the big-O form and the ratio → 1 form fail.
- **Other readings.** Hasse's unit index Q (Mathlib `indexRealUnits`, which is 1 or 2) is not 3; under the relative norm to the maximal real subfield the index is infinite (a fundamental unit η of K⁺ has relative norm η^{2n} ≠ 1).
- **Risk.** The object the Definition line names is identically 1 for m ≥ 3, so the statement may be read as ill-posed; other notions of "unit index" and suprema over abelian subfields of conductor m are not covered.
- **Main theorem.** `C732.conjecture732_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 368 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture732/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000732.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C732.conjecture732_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000732 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
