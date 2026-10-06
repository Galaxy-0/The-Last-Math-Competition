# Disprove conjecture 00000000702: an algebraic p-adic number has a purely periodic Browkin expansion [1/p; 1/p, …]

- **Witness.** For every odd prime p, Hensel's lemma on pX² + X − p at 0 gives β ∈ pℤ_p; α = 1/β is a root of pX² − X − p with α − 1/p = β. α is algebraic and irrational (4p² + 1 is not a square).
- **Browkin I.** With Browkin's s-function (Capuano–Murru–Terracini, arXiv:2010.07364, retrieved and quoted), s(α) = 1/p and α₁ = α, so the expansion is [1/p; 1/p, 1/p, …]: purely periodic with constant partial quotient.
- **Browkin II.** With the second algorithm (Murru–Romeo–Santilli, arXiv:2201.12019), the partial quotients are 1/p, 1/p − 1, then (1, −1/p, −1, 1/p) repeating: eventually periodic.
- **Refutation.** Both expansions are infinite and take finitely many partial-quotient values (|b_n|_p ≤ p), so each clause (never eventually periodic; unbounded partial quotients) fails separately, for both algorithms.
- **Objects in Lean.** s and t are defined by their characterizing properties (via `Classical.epsilon`), with uniqueness proved for every prime and existence for odd p (`browkinS_spec`, `browkinT_spec`).
- **Not refuted.** A degree ≥ 3 reading (clause 1 is then known, since periodic implies quadratic) and clause 2 read as "non-periodic implies unbounded" (the conjunction still fails through clause 1).
- **Main theorem.** `C702.conjecture702_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 565 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture702/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000702.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C702.conjecture702_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000702 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
