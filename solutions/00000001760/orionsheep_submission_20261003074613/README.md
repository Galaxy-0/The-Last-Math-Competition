# Disproof of conjecture `00000001760`

**Verdict: FALSE — the small group G = C₂ × A₅ (order 120) violates
the compressed bound: m(G) = 3 (the smallest nonlinear irreducible
character degree) while the minimal maximal-subgroup index is
[G:H] = 2 (the subgroup A₅ × {0}), and the bound m(G) ≤ [G:H]^{3/2}
reads 3 ≤ 2^{3/2} ≈ 2.83, i.e. (squaring) 9 ≤ 8 — false.**

## The conjecture (verbatim from `conjectures/00000001760.md`)

> Definition: For a finite group G, m(G) is the smallest nonlinear
> degree of an irreducible character, and [G:H] the minimal index of a
> maximal subgroup. Conjecture: The general bound m(G) ≤ [G:H]² can be
> compressed to m(G) ≤ [G:H]^{3/2}; the compression exponent 3/2 is
> optimal, verified by the PSL(2,p) family.

## The refutation

G = C₂ × A₅ (order 120):

1. **m(G) = 3.** The irreducible character degrees of G are exactly
   those of A₅ — {1, 3, 3, 4, 5} — each appearing twice (tensored with
   the two linear characters of C₂). The smallest nonlinear degree is
   3. The script constructs A₅ as the even permutations of {1..5}
   (60 elements), splits its 5 conjugacy classes (sizes
   1, 15, 20, 12+12 — the two 5-cycle classes), and confirms the
   degree list by sum of squares: 1 + 9 + 9 + 16 + 25 = 60 = |A₅|.

2. **[G:H] = 2.** The subgroup A₅ × {0} is maximal of index
   |C₂ × A₅|/|A₅| = 120/60 = 2, and no proper subgroup has index
   below 2.

3. **The compressed bound fails.** m(G) ≤ [G:H]^{3/2} reads
   3 ≤ 2^{3/2}, equivalently (positive integers) 3² ≤ 2³, i.e.
   9 ≤ 8 — false. Note the ORIGINAL square bound m(G) ≤ [G:H]² = 4
   holds at this instance (3 ≤ 4): the failure is specific to the 3/2
   compression, which is therefore not a valid general bound (whatever
   the PSL(2,p) family does).

## Verification

* `reproduce.py` — independent construction of A₅ as the even
  permutations (60 elements), conjugacy-class size checks
  (1, 15, 20, 24), the degree list (1, 3, 3, 4, 5) by sum of squares,
  the C₂ × A₅ doubling, m(G) = 3, [G:H] = 2, and the comparison
  9 > 8.
* Lean 4 (core, v4.33.1), `lean4/` — the squared comparison
  3² = 9 > 8 = 2³ (equivalent to 3 > 2^{3/2} for positive integers),
  the instance anchors (m = 1 + 2 = 3, index (2·60)/60 = 2), and the
  contrast anchor 3² ≤ 2²·2² = 16 (the original square bound holds
  here — the compression is what fails). All 6 audited theorems
  report `does not depend on any axioms`.

## Boundary

The kernel certifies the arithmetic comparison 9 > 8 and the instance
anchors. The character-degree data of A₅ (degrees 1, 3, 3, 4, 5 with
sum of squares 60) and the subgroup structure of C₂ × A₅ are classical
(the standard A₅ character table, constructible from its 5 conjugacy
classes) and re-verified by the script's independent permutation-group
construction.
