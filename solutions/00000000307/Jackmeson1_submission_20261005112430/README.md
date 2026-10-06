# Disprove conjecture 00000000307: the weighted Bad sets are empty at (0,0) or (−3/4,−3/4), not full-dimensional

The conjecture claims that Bad(i,j), the set of pairs badly approximable with weights q^{1+i}, q^{1+j}, has full dimension for i+j = 0, and that "the intersection" has full dimension for every weighting with i+j < 0.
- **Dirichlet lemma.** A two-dimensional Dirichlet lemma is proved by pigeonhole (`dirichlet_two`): for every N ≥ 1 there are 1 ≤ q ≤ N² and integers p, r with |qx−p|, |qy−r| < 1/N.
- **Reading A (weight multiplies |x − p/q|).** BadA(i,j) is empty for all i, j ≤ 0. So dimH BadA(0,0) = 0, which refutes clause 1, and every subset of BadA(−1/2,−1/2) has dimension 0, which refutes clause 2.
- **Reading B (weight multiplies ‖qx‖).** BadB(i,j) is empty for i, j ≤ −3/4, which refutes clause 2.
- **Scope.** Clause 2 is stated for any set contained in Bad(i,j), which includes the intersection over all weightings with i+j < 0. Not refuted: clause 1 under reading B (the conjunction still fails through clause 2). The winning conjuncts are not formalized. The empty-set pattern follows the accepted solution 00000000310.
- **Main theorem.** `Conjecture307.conjecture307_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 238 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture307/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000307.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture307.conjecture307_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000307 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
