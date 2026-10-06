# Disprove conjecture 00000008433: no threshold in t alone makes the divisibility conditions sufficient for t-designs

- **Claim refuted.** Once v ≥ exp(exp(t)) (clause 1), or v ≥ t^{ct} with c an absolute constant (clause 2), the divisibility conditions alone decide whether a t-(v,k,λ) design exists.
- **Family.** For every m ≥ 3: t = 2, λ = 1, v = (m−1)²(m+1), k = m(m−1); every divisibility condition holds (r = m, b = m² − 1). E.g. m = 13 gives 2-(2016,156,1) with 2016 > e^{e²} ≈ 1618 (`witness_13`).
- **Non-existence.** A 2-(v,k,1) design with 2 ≤ k < v forces k(k−1) ≤ v − 1 (the λ = 1 case of Fisher's inequality, proved in Lean by two double counts, `fisher_bound`), while here v − 1 = m(k−1) and k > m (`family_no_design`, `family_no_simple_design`).
- **Conclusion.** v grows without bound along the family, so for every threshold T(t) there are admissible, non-degenerate parameters (2 ≤ t < k, k + t < v, 1 ≤ λ ≤ C(v−t, k−t)) with v > T(2) and no design (`exists_counterexample`, `threshold_fails`); both clauses fail, the second for every real c.
- **Conventions.** Designs are indexed block families (repeated blocks allowed); simple designs are refuted too. Source: Wikipedia "Block design" (retrieved).
- **Not refuted.** The reading with a threshold depending also on k and λ (Wilson's v₀(t,k,λ)); the text names thresholds in t only, with c "an absolute constant".
- **Main theorem.** `Conjecture8433.conjecture8433_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 254 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture8433/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000008433.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture8433.conjecture8433_false`, `Conjecture8433.exists_counterexample`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000008433 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
