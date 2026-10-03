# Disproof of conjecture `00000002043`

**Verdict: FALSE (at q = 3) — s₃(3n) = s₃(n) for EVERY n, so the count
#{n ≤ x : s₃(3n) = s₃(n)} equals x exactly (LINEAR), not
~ c·x/√(log x).**

## The conjecture (verbatim from `conjectures/00000002043.md`)

> Definition: The digit sum s_q(n) is the sum of digits of the base-q
> representation. Conjecture: #{n ≤ x : s_q(3n) = s_q(n)} ~
> c_q·x/(log x)^{1/2}; the constant c_q is explicit from the singularity
> at z = 1 of the generating function of a Stern–Brocot type bifurcation
> tree.

## The refutation at q = 3

In base 3, multiplying by 3 appends a zero trit: 3n has the base-3
digits of n followed by 0. Hence

    s₃(3n) = s₃(n) + 0 = s₃(n)   for EVERY n ≥ 0,

and the set {n ≤ x : s₃(3n) = s₃(n)} is the whole interval: the count is
exactly x (for n ∈ [0, x), all x qualify; for 1 ≤ n ≤ x, all x qualify).
A count of exactly x is not asymptotic to c·x/√(log x) for any constant
c, since the ratio

    x / (c·x/√(log x)) = √(log x)/c → ∞ ≠ 1.

The digit-sum condition imposes NO restriction at q = 3, so no
Stern–Brocot bifurcation singularity can exist: the generating function
of the indicator is ∑ xⁿ = 1/(1−x), whose only singularity is at z = 1
itself — a simple pole, not a square-root branch point.

## Verification

* `reproduce.py` — computes base-3 digit sums from scratch and checks
  s₃(3n) = s₃(n) for all n < 10⁶; counts the qualifying set for
  x = 10¹ … 10⁶ (all equal x exactly); and shows the ratio to
  x/√(log x) diverging, so no constant c fits.
* Lean 4 (core, v4.33.1, no Mathlib) — `lean4/`: a fully general
  formalization: the quotient/remainder-by-3 machine `q3` with its spec
  (all built by structural recursion, since the core Nat mod/div lemmas
  carry `propext` upstream), the fuel-independent digit sum `s3`, the
  identity `s3 (3*n) = s3 n` for every n, and the counting function
  with `cnt x = x` for every x. All 9 audited theorems report
  `does not depend on any axioms`.

## Boundary

Only q = 3 is addressed. For q ≥ 4 the congruence condition s_q(3n) =
s_q(n) is a genuine restriction and the stated ~ c_q·x/√(log x) may be
meaningful; the conjecture as displayed is refuted by its q = 3 case
(the displayed statement quantifies over no particular q).
