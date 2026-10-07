# Prove conjecture 00000000206: every value occurs only finitely often in Recamán's sequence

- **Sequence.** OEIS A005132: a(0) = 0; a(n) = a(n−1) − n if that is positive (Wikipedia) / nonnegative (OEIS) and new, else a(n−1) + n. Both guards are formalized and shown to give the same sequence; the sequence is constructed and unique (`isRecaman_unique`), and its first 27 terms are checked by `decide` against Wikipedia.
- **Key step.** An add step gives a(n) = a(n−1) + n ≥ n, so any occurrence of m at an index n > m is a subtract step, hence the first occurrence of m.
- **Result.** At most one index beyond m carries the value m, so {n | a n = m} is finite (`recaman_finite_occurrences`). The core lemma `finite_of_step` holds for any sequence whose steps are either +n or a fresh value.
- **Scope.** The clause "the finiteness is settled by interval covering" is read as a remark on method, not a mathematical claim, and is not formalized.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 166 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture206/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000000206.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture206.recaman_finite_occurrences`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000000206 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
