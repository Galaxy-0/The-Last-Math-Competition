# Disproof of conjecture `00000002182`

**Verdict: FALSE — plain majority already exceeds the conjectured supremum.**

## The conjecture (verbatim from `conjectures/00000002182.md`)

> Definition: The expected sensitivity of monotone Boolean functions.
> Conjecture: The supremum is (1/2)·(log n)^(1/2) (exact); the extremum is
> given by variants of majority-of-majorities families.

**Object consistency.** We attack exactly: the supremum of the average
sensitivity of monotone Boolean functions on the n-cube, claimed to be
(1/2)√(log n).

## The counterexample

The **majority function on 5 variables** (monotone!) has average sensitivity

    (number of sensitive (input, bit) pairs) / 2^5 = 60/32 = **1.875**

while the conjectured supremum at n = 5 is

    (1/2)√(log₂ 5) ≈ 0.762   (base 2)
    (1/2)√(ln 5)   ≈ 0.634   (base e)

— exceeded under both standard logarithm conventions (and every base ≥ 2,
since log_b 5 ≤ log_2 5 for b ≥ 2).

## Integer certificates

- Base 2: 60/32 > ½√(log₂ 5) ⟺ (15/4)² > log₂ 5 ⟺ 2^(225/16) > 5 ⟺
  **2^225 > 5^16** (5.4·10⁶⁷ vs 1.5·10¹¹) — `two225_gt_five16`.
- Base e: e > 2 ⟹ e^(225/16) > 2^14 = 16384 > 5 — `two14_gt_five`
  (e > 2 cited).
- The count 60: `sensCount_eq` — kernel enumeration of all 32 words × 5
  bits with majority recomputed structurally.

## Reproduce

`python3 reproduce.py` — recounts 60 sensitive pairs over the 5-cube,
computes both bound values, and verifies the squaring chain numerically.
Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 4 theorems,
all `does not depend on any axioms`.

## Boundary

n = 5 with plain majority suffices (the "majority-of-majorities extremum"
clause is thereby moot — its simplest member already breaks the bound).
Bases are restricted to the standard ones (2, e, and any b ≥ 2).
