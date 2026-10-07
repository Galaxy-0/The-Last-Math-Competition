# Disprove conjecture 00000000211: the lucky primes contain no twin pair

- **Claim refuted.** The conjunct "the intersection of lucky numbers and primes contains infinitely many twin pairs"; the conjunction fails whatever the density clause means (the theorem takes it as an arbitrary proposition).
- **Lucky sieve.** Formalized stage by stage from the positive integers (OEIS A000959, retrieved): each stage is an increasing enumeration; round k+1 deletes the 1-indexed positions m, 2m, 3m, … (`range_deleteEvery`), with sieving numbers 2, 3, 7, 9, 13, … (`sievingNumber_first_five`, `sievingNumber_eq_lucky`: every round n ≥ 2 uses the n-th lucky number, as the statement describes; the literal s₁ = 1 would delete everything, so the standard start with 2 is used).
- **Sanity checks.** The first ten lucky numbers are 1, 3, 7, 9, 13, 15, 21, 25, 31, 33 (kernel `decide`); there are infinitely many lucky numbers; 5 is not lucky.
- **Key lemma.** After rounds 1–2 the survivors are 2(j + ⌊j/2⌋) + 1, i.e. ≡ 1 or 3 (mod 6), and later rounds only delete, so every lucky number is ≡ 1 or 3 (mod 6).
- **Conclusion.** A lucky prime p with p + 2 prime must be 3, and 5 is not lucky, so no two lucky primes differ by 2 (`twinPairs_eq_empty`).
- **Scope.** Only gap-2 twin pairs are addressed; the density clause is not formalized.
- **Main theorem.** `Conjecture211.conjecture211_false`.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 278 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture211/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000211.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture211.conjecture211_false`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000211 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
