# Disproof of conjecture `00000002291`

**Verdict: FALSE — both clauses. (1) The bound itself fails: for the
simple group G = PSL(2,139), a generator of a non-split torus has
centralizer order (q+1)/2 = 70 and |G| = 139·(139²−1)/2 = 1342740, so
|C_G(x)|² ·64 = 313600 < 1342740 — C_G(x) ≥ (1/8)|G]^{1/2} is
violated outright (and by torus scaling the ratio → 0 as q → ∞, so no
positive constant works). (2) The claimed tightness at A₅ is doubly
false: an A₅-involution has |C| = 4 while (1/8)√60 ≈ 0.97 — strict
slack, not attainment — and no centralizer order occurring in A₅
(60, 4, 3, 5) gives equality; even the A₅ minimum ratio 3/√60 ≈ 0.387
is three times 1/8.**

## The conjecture (verbatim from `conjectures/00000002291.md`)

> Definition: The Brauer–Fowler theorem bounds centralizers of
> even-order simple groups: |C_G(x)| ≤ (|G|−1)/2 type. Conjecture: The
> exact constant in the lower bound for centralizer sizes:
> C_G(x) ≥ c·|G|^{1/2} (c = 1/8); c is tight, attained by low-order
> simple groups (e.g. involutions of A₅).

## The refutation

**The bound fails.** In PSL(2, q) (simple for q ≥ 4), a generator of a
non-split torus is semisimple with centralizer the torus itself, of
order (q+1)/2, while |PSL(2,q)| = q(q²−1)/2 ≈ q³/2. The claimed ratio
then behaves like ((q+1)/2)/(q³/2)^{1/2} ≈ √2/√q → 0. Concretely at
q = 139: |G| = 1342740, |C_G(x)| = 70 for x the image of
A = [[3,4],[2,3]] (multiplication by ζ = 3 + 2u, u² = 2, of norm 1;
order 140 in SL(2,139), A⁷⁰ = −I, so the image has order 70 in PSL),
and 64·70² = 313600 < 1342740 — the inequality
|C_G(x)| ≥ (1/8)|G|^{1/2} is false, with the arithmetic certified in
the kernel.

**A₅ attains nothing.** Brute force (60 even permutations, all
centralizers computed): the centralizer orders occurring are exactly
{60 (id), 4 (15 involutions), 3 (20 three-cycles), 5 (24
five-cycles)}. Attainment of c = 1/8 would require 64·|C|² = 60; the
values are 230400, 1024, 576, 1600 — none is 60. At the conjecture's
own example — involutions, |C| = 4 by orbit-stabilizer (60 = 4·15) —
the bound holds with strict slack: 4 > (1/8)√60 (equivalently
60 < 1024). The minimum A₅ ratio, 3/√60 ≈ 0.387, is nowhere near
1/8 = 0.125. "Tight, attained by involutions of A₅" is false on its
face.

## Verification

* `reproduce.py` — full brute force of A₅ (centralizer orders
  {60:1, 4:15, 3:20, 5:24}, all ratios > 1/8, no equality);
  |SL(2,q)| = q(q²−1) brute-verified for q = 3, 5, 7; the explicit
  torus generator A = [[3,4],[2,3]] (ζ = 3 + 2u over u² = 2) of order
  140 in SL(2,139) with A⁷⁰ = −I; the bound violation
  64·70² = 313600 < 1342740.
* Lean 4 (core, v4.33.1), `lean4/` — `A5_order`, `A5_classes`
  (orbit-stabilizer anchors), `no_attainment`, `involution_slack`,
  `order_exact`, `bound_violated`, `conjecture_refuted` — all ground
  `decide` arithmetic.  All 7 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the exact integer inequalities: the non-attainment
in A₅ (all four centralizer orders), the strict slack at the
conjecture's own example, and the outright violation at PSL(2,139).
The group-theoretic input (A₅'s class structure; |PSL(2,q)| =
q(q²−1)/2; self-centralizing non-split tori of order (q+1)/2; the
explicit generator) is classical, cited in prose and reproduced by
the script's brute force where feasible.  Both the universal bound
and its claimed tightness are refuted.
