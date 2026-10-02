# Disproof of conjecture `00000002021`

**Verdict: FALSE (the mod-11 obstruction clause) — sums of five fifth powers
already cover every residue mod 11.**

## The conjecture (verbatim from `conjectures/00000002021.md`)

> Definition: G(k) is the smallest s such that every sufficiently large
> integer is a sum of s k-th powers. Conjecture: G(5) = 17; the currently
> known bound G(5) ≤ 17 (or on partial ranges) has 17 as the exact target;
> and **the lower bound for G(5) is guaranteed by the local density
> obstruction modulo eleven.**

**Object consistency.** We attack exactly the boldfaced clause: a local
(congruence) obstruction mod 11 that would force G(5) up.

## The refutation

The fifth powers mod 11 are exactly **{0, 1, −1}** (kernel-certified table:
the unit group has order 10, and 5 | 10). Sums of **five** elements of
{0, ±1} realize every integer in [−5, 5], and [−5, 5] mod 11 is **all of
ℤ/11**. Kernel certificate: all 3⁵ = 243 five-term sums from {0, 1, 10},
reduced mod 11, cover every residue 0..10 (`covers_all`).

A fortiori, sums of **17** fifth powers cover every residue mod 11. There is
no congruence obstruction modulo 11 — the claimed lower-bound mechanism
**does not exist**, so the clause guaranteeing the lower bound "by the local
density obstruction modulo eleven" is false.

## Boundary

This refutes the lower-bound-mechanism clause. The numeric assertion
G(5) = 17 itself is a separate claim (the true obstruction structure for
G(5) is a global density one, not a mod-11 local one); it is not needed
for this disproof.

## Reproduce

`python3 reproduce.py` — the fifth-power table mod 11, the 3⁵ sums, and the
coverage check. Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 2 theorems
(`pow5_table`, `covers_all`), both `does not depend on any axioms`.
