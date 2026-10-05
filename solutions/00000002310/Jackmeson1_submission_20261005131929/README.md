# Disprove conjecture 00000002310: base sizes of almost simple groups are unbounded

- **Claim.** The supremum of base sizes b over almost simple groups is 7. The text (both languages) does not restrict to non-standard actions.
- **Base size of A_n.** In the natural action of A_n, every set of at most n − 3 points misses three points that carry a 3-cycle fixing it, while the complement of any two points is a base, so b(A_n) = n − 2 (`baseSize_alternating`).
- **Almost simple.** For n ≥ 5, A_n is almost simple (a nonabelian simple normal subgroup with trivial centralizer) and acts faithfully and primitively (`isAlmostSimple_alternating`, primitivity from Mathlib).
- **Conclusion.** The supremum over finite, faithful, primitive almost simple actions is ⊤, not 7 (`conjecture_2310_false`); for example A₁₀ has b = 8 (`conjecture_2310_false_A10`).
- **Scope.** The known bound b ≤ 7 concerns non-standard actions, which the text does not specify. Only the first conjunct is refuted; the "exactly 3 groups" table is not addressed.
- **Lean.** Lean 4.33.1, Mathlib v4.33.1, 158 lines. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`.

**Previous submission and its error (README rule 2).** PR #222 by orionsheep was closed without being merged. The reviewer did not dispute the idea that the natural action of an alternating group has base size larger than 7, but rejected the formalization: "conjecture_refuted is ¬(7 ≥ 8), decide trivia with no groups in Lean, and the substantive part does not prove b = 8: seven_points_fail exhibits only ONE non-base 7-subset, whereas b ≥ 8 requires every 7-subset to fail — that universal step is verified only in reproduce.py, and S₉'s almost-simplicity is prose." This submission defines in Lean the base (trivial pointwise stabilizer), the base size (the least cardinality of a base) and almost simplicity (a nonabelian simple normal subgroup with trivial centralizer), all on actual group actions. It proves that *every* set of at most n − 3 points fails to be a base for A_n, and that the complement of any two points is a base, so `baseSize_alternating` gives b(A_n) = n − 2 for every n ≥ 2. It also proves in Lean that A_n is almost simple and acts faithfully and primitively for n ≥ 5. The main theorem `conjecture_2310_false` shows that the supremum of base sizes over finite almost simple groups in faithful primitive actions is ⊤, so it is not 7. `conjecture_2310_false_A10` shows that A₁₀ has base size 8.

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture2310/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000002310.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `C2310.conjecture_2310_false`, `C2310.conjecture_2310_false_A10`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000002310 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
