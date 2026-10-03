# Disproof of conjecture `00000002913`

**Verdict: FALSE at its first instance — d = 2, q = 5 satisfies the
claimed threshold q > d² (5 > 4), yet the degree-2 map x ↦ x² on F₅
is not injective: 4² = 1² = 1 (mod 5) with 4 ≠ 1 (kernel-certified);
its image is exactly {0, 1, 4}, of size 3 < 5.  Full enumeration:
NO quadratic map (a ≠ 0) on F₅ or F₇ is injective — max image size
3 = (5+1)/2 and 4 = (7+1)/2 — while the threshold q > 4 holds for
both fields.**

## The conjecture (verbatim from `conjectures/00000002913.md`)

> Definition: finite field version of the jacobian conjecture:
> injection polynomial map on plane. Conjecture: injection spectrum:
> d-fold polynomial map in F_q on injection when q greater than d²
> and inverse in q of injection does not exceed of d by Chebyshev
> lattice gives. (injection threshold spectrum)

## The refutation

The claim "degree-d polynomial map is injective on F_q when q > d²"
fails immediately at d = 2, q = 5: the threshold 5 > 4 holds, but
x² on F₅ is far from injective — every nonzero square is ±1:
x² ∈ {0, 1, 4} for all x ∈ F₅ (0²=0, 1²=1, 2²=4, 3²=9=4, 4²=16=1),
with the collision 4² = 1² = 1 on distinct inputs 4 ≠ 1.  The image
has 3 elements, not 5.  A complete enumeration of all 100 quadratic
maps on F₅ (a ≠ 0) and all 294 on F₇ shows that NONE is injective:
a non-degenerate quadratic over F_q (q odd) has image of size at
most (q+1)/2, strictly below q.  The plane version fails identically:
(x,y) ↦ (x², y²) on F₅² has image 9 < 25 with (1,0) and (4,0)
colliding.

(For orientation: the classical finite-field injectivity results go
the other way — a polynomial of degree d over F_q with d < q can be
injective only in exceptional cases, and q > d² is nowhere near
sufficient; e.g. x² is injective on F_q only for q = 2.)

## Verification

* `reproduce.py` — the certified collision (4² = 1² = 1, image
  {0,1,4}); full enumeration of quadratic maps on F₅ (100) and F₇
  (294): all non-injective, max image size (q+1)/2; the plane
  instance (x², y²) with image 9 < 25.
* Lean 4 (core, v4.33.1), `lean4/` — `threshold_holds` (5 > 4),
  `collision` (4 ≠ 1 ∧ 4² ≡ 1² mod 5), `image_three` (all five
  inputs square into {0,1,4}, pairwise distinct, 3 < 5),
  `conjecture_refuted`.  All 4 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the exact residue arithmetic at the first
instance (threshold satisfied, collision witness, 3-element image);
the enumeration over all quadratic maps (both fields) and the plane
instance are exhaustive computations in the script.  The injectivity
threshold claim is refuted at d = 2, q = 5; no claim is made about
the conjecture's "Chebyshev/Lagrange inversion" clause, which is not
needed for the refutation.
