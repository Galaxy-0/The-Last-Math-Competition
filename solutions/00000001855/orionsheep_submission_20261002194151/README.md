# Disproof of conjecture `00000001855`

**Verdict: FALSE — the claimed negative-binomial formula disagrees with the
exact count at n = 2, for every q.**

## The conjecture (verbatim from `conjectures/00000001855.md`)

> Definition: The 2-rank of a random symmetric matrix over F_q is its rank
> mod 2. Conjecture: The probability that the 2-rank equals r is
> (1−q⁻¹)·q^(−C(r,2)) / ∏(1−q^(−i)) (a negative binomial distribution),
> compatible with the MacWilliams identities.

**Object consistency.** We attack exactly the displayed formula for P(r),
at n = 2 (2×2 symmetric matrices [[a,b],[b,c]]) and r = 2 (nonsingular),
where the exact count is elementary.

## The refutation

At n = 2, r = 2 the formula telescopes:

    P_formula = (1−q⁻¹)·q⁻¹ / ((1−q⁻¹)(1−q⁻²)) = q/(q²−1),

while the exact probability is classical and elementary (singular ⟺
ac = b², giving q²·q − (q² + q(q−1)·1)... #nonsingular = q³−q²):

    P_true = 1 − 1/q.

Kernel-enumerated counts (`nonsingCount` decodes all q³ triples):

| q | exact nonsingular / total | P_true | P_formula | match? |
|---|---|---|---|---|
| 2 | **4 / 8** | 1/2 | 2/3 | no (12 ≠ 16, cross-multiplied) |
| 3 | **18 / 27** | 2/3 | 3/8 | no (144 ≠ 81) |

Moreover q/(q²−1) **decreases** in q while 1−1/q **increases**: the formula
is wrong for every q, and qualitatively so.

## Reproduce

`python3 reproduce.py` — enumerates q = 2..5, prints exact fractions, the
formula value, and the classical count q³−q². Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 5 theorems
(`q2_count`, `q3_count`, `totals`, `q2_mismatch`, `q3_mismatch`), all
`does not depend on any axioms` (determinant with q²-padding to avoid Nat
truncated subtraction).

## Boundary

The r = 2, n = 2 specialization of the displayed formula is refuted for
all q (two kernel certificates + the monotonicity argument). The
"MacWilliams compatibility" clause is not addressed.
