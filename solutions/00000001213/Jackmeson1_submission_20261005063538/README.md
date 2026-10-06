# Disprove conjecture 00000001213: the prime 5 is a winning first move in Sylver coinage

- **Claims:** (C1) the first player wins; (C2) every winning first move is composite; (C3) no prime first move wins, i.e. after a prime opening the second player has a winning reply.
- **Result:** we prove Hutchings' theorem in Lean: every prime p >= 5 is a winning opening. So (C1) holds, and (C2) and both phrasings of (C3) are false.
- **Frobenius step:** after a legal reply q, gcd(p,q) = 1, and t = pq - p - q is the Frobenius number (Mathlib's `frobeniusNumber_pair`). Every gap x satisfies t - x ∈ ⟨p,q⟩.
- **Strategy stealing:** the game from {p,q,t} is finite and therefore determined. The first player either names t, or names the opponent's winning reply x; the latter works because ⟨p,q,x⟩ = ⟨p,q,t,x⟩ and outcomes depend only on the closure.
- **Lean:** `conjecture_00000001213_false : ¬ Conjecture`, plus `hutchings`, `clause1_true`, `not_clause2`, `not_clause3` and `not_clause3'`. The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.
- **Credit:** the game formalization (`Legal`, `Outcome`, `not_win_and_lose`) comes from the accepted solution of 00000008869 by feiyuceng06-prog (GPL-3.0).
- **Literature:** Wikipedia, "Sylver coinage": "Hutchings's Theorem states that any of the prime numbers 5, 7, 11, 13, …, wins as a first move".

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture1213/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000001213.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Submission00000001213.conjecture_00000001213_false`, `Submission00000001213.hutchings`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-05): no solution folder for 00000001213 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
