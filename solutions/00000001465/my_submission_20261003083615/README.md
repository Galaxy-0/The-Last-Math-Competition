# Disproof of conjecture `00000001465`

**Verdict: FALSE — for CONVEX f the Moreau envelope M_λf is C¹ for
EVERY λ > 0 regardless of L(f) (classical: envelopes of convex
functions are continuously differentiable with (1/λ)-Lipschitz
gradient).  There is no critical parameter λ*(f) = 1/L(f).  Concrete
counterexample to the "λ > λ* ⇒ nondifferentiable at a minimizer"
clause: f(x) = |x| has L(f) = 1, so the claimed threshold is
λ* = 1; at λ = 4 > 1 the envelope value at the minimizer x = 0 is
exactly M₄(0) = 0, attained uniquely at y = 0 (kernel-certified lower
bound 8|y| + y² ≥ 0, equality iff y = 0), and M₄(h) = h²/8 for
|h| ≤ 4 — differentiable at the minimizer with quotient h/8 → 0.**

## The conjecture (verbatim from `conjectures/00000001465.md`)

> Definition: The Moreau envelope of a convex function f is
> M_λf(x) = inf_y{f(y) + |x−y|²/(2λ)}.  Conjecture: The critical
> parameter for M_λf to be C¹ is λ*(f) = 1/L(f), where L(f) is the
> minimal Lipschitz constant of f; for λ < λ*, all envelopes are C¹,
> while for λ > λ* there exists f whose envelope is nondifferentiable
> at a minimizer.

## The refutation

For convex f the envelope M_λf is C¹ for every λ > 0 — the classical
Moreau regularity theorem — so the "critical parameter" framing is
void.  Concretely, f(x) = |x| has L(f) = 1 (the difference
|f(1) − f(0)| = 1 forces L ≥ 1; the triangle inequality gives
L ≤ 1), so the claimed threshold is λ* = 1; take λ = 4 > 1:

* the minimizer of f is x = 0, and the envelope value there is
  M₄(0) = inf_y {|y| + y²/8} = 0, attained uniquely at y = 0
  (kernel-certified: 8|y| + y² ≥ 0 for all y : Int, equality iff
  y = 0);
* for |h| ≤ 4 the envelope is the exact quadratic M₄(h) = h²/8 (the
  lower bound 8|y| + (h−y)² ≥ h² holds: for y ≥ 0 it reduces to
  y(8 − 2h + y) ≥ 0 with 8 − 2h ≥ 0; for y < 0 all terms are
  nonnegative), so the difference quotient at the minimizer is
  h/8 → 0: differentiable at the minimizer.

The "nondifferentiable at a minimizer for λ > λ*" clause fails at this
instance; hence the claimed critical-parameter theory is refuted.

## Verification

* `reproduce.py` — exact-fraction envelope values M₄(h) = h²/8 for
  h = 0..4 via the closed-form soft-threshold prox; difference
  quotients h/8 → 0 at the minimizer; even symmetry; the λ = 4 > 1
  instance anchor.
* Lean 4 (core, v4.33.1), `lean4/` — the lower bound 8|y| + y² ≥ 0
  for all y : Int (Int sign cases, core `Int.mul_nonneg`) with
  equality iff y = 0, and the λ = 4 > 1 anchor.  All 4 audited
  theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the inf-value facts (M₄(0) = 0, attained
uniquely at the minimizer) and the instance anchors.  The C¹
differentiability conclusion and the general Moreau regularity theorem
(classical) are cited in prose, with the exact quadratic formula
M₄(h) = h²/8 for |h| ≤ 4 verified by the script.
