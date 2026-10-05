# Disprove conjecture 00000004042: representation dimension is integer-valued, so its values are not dense above 3

The conjecture claims two things. First, the realizable values of repdim are dense above 3. Second, repdim = 3 is closed under derived equivalence.

**Key fact.** Auslander's representation dimension is `repdim A = inf { gl.dim End_A(M) : M a generator-cogenerator }`. It is always a natural number or ∞, because global dimension is: it is a supremum of Mathlib's `projectiveDimension`, which takes values in `WithBot ℕ∞`. So the finite realizable values form a subset of ℕ.

**First clause fails.** A subset of ℕ cannot be dense in `(3, ∞)`. The interval `(13/4, 15/4)` is a nonempty open subset of `(3, ∞)` and contains no realizable value.

**Second clause is not needed.** The conjunction fails whatever clause 2 means. The submission proves this for an arbitrary proposition `P`, and also for a concrete formalization built on Mathlib's derived categories.

**Scope.** "Dense" is read in its standard topological sense, on the real half-line the statement names. The report says explicitly that it does not address the alternative reading "every integer ≥ 3 is realizable".

## Contents

| path | content |
|---|---|
| `proof.tex`, `proof.pdf` | full report |
| `lean/` | Lean 4 project (Lean (version 4.33.1; Mathlib v4.33.1); proof in `lean/Conjecture4042/Basic.lean` |
| `lean/Axioms.lean` | axiom audit |
| `conjecture.md` | the conjecture exactly as in `conjectures/00000004042.md` |
| `SEMANTIC_REVIEW.md` | independent pre-submission semantic review |
| `verification/` | fresh-build log, axiom output, SHA-256 checksums |

## Lean

Main theorems: `Conjecture4042.conjecture_00000004042_false`, `Conjecture4042.conjecture_00000004042_false_of_any_clause2`.

No `sorry`, `admit`, `native_decide` or `axiom`; every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound` (`verification/axioms.txt`).

Reproduce:

```
cd lean
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Eligibility

Checked before opening the pull request (2026-10-04): no solution folder for 00000004042 on `main`, no open pull request for it by anyone else, and `metadata.csv` lists it as unsolved. The pull request only adds this submission folder.
