# Disprove conjecture 00000003524: two stationary subsets of ω₁ can have empty (non-stationary) intersection

- **Claim refuted.** Both languages say "the intersection of stationary sets is stationary" (平稳集的交集为平稳); the Chinese joins this with 且 ("and") to an undefined clause about reflection "bounded below closure", treated as an arbitrary conjunct.
- **Definitions.** Mathlib's own `IsClub` (closed and cofinal) and `IsStationary` (meets every club) on `(ω₁).ToType`, unchanged.
- **Ulam matrix.** For each a fix f_a injective on Iio a, and set A(n,b) = {a > b : f_a(b) = n}; each Ioi b is a countable union of these and is stationary, so some A(N(b), b) is stationary; N : ω₁ → ℕ is not injective, so two such sets are disjoint (`exists_disjoint_stationary_omega_one`).
- **Refutation.** The claim fails for two sets (`stationaryInterClaim_false`), for every nonempty family (`sInter_claim_false`) and for the family of all stationary sets (`not_isStationary_sInter_all`); `conjecture3524_false (Q : Prop)` refutes the conjunction however the second clause is read. Source: Wikipedia "Stationary set" and "Club set" (retrieved; credits Ulam and Solovay).
- **Not refuted.** The reading "club ∩ stationary is stationary", which is true and is proved as a remark (`isStationary_inter_isClub`).
- **Main theorem.** `C3524.conjecture3524_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 175 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture3524/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000003524.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C3524.conjecture3524_false`, `C3524.exists_disjoint_stationary_omega_one`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000003524 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
