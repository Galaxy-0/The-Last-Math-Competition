# Disproof of conjecture `00000001464`

**Verdict: FALSE — the Legendre transform L is an INVOLUTION
(L∘L = id, Fenchel–Moreau), so L³ = L for every function: any
"period-3 point" would satisfy L³f = f, hence Lf = f — a fixed point.
No convex function of genuine period 3 exists.  The kernel certifies
this in full generality; numerically, every tested convex function
(x²/2 self-dual; |x|; max(x²/2, |x|−1); Huber-like) satisfies
L(Lf) = f with period exactly 2 (or 1).**

## The conjecture (verbatim from `conjectures/00000001464.md`)

> Definition: The Legendre transform ∇f*. Conjecture: Beyond the
> period-2 property of the quadratic Legendre iterate, there exists a
> convex function of period 3 (involution period three).

## The refutation

The Legendre–Fenchel transform on proper convex lower-semicontinuous
functions satisfies L(L g) = g for all g (Fenchel–Moreau).  Applying
this to g = Lf:

    L(L(L f)) = L f   for every f.

So if f had period 3 — L(L(L f)) = f with Lf ≠ f — the identity would
force Lf = f: a fixed point (period 1), e.g. the self-dual
f(x) = x²/2.  The period spectrum of L is exactly {1, 2}; genuine
period 3 is excluded.  (The same holds for any involution whatsoever.)

The kernel certifies this in full generality: for an abstract type α
of convex functions with an involution L (hypothesis = the
Fenchel–Moreau property), `period3_collapse` proves
L(L(Lf)) = f → Lf = f, and `no_genuine_period3` derives False from a
claimed genuine period-3 point.  `fixed_point_consistent` shows the
hypotheses are satisfiable (the identity map is an involution), so the
period spectrum is exactly {1, 2}.

## Verification

* `reproduce.py` — numerical Legendre transforms (supporting-line
  computation on a fine grid) for convex examples: x²/2 is a fixed
  point (period 1); |x|, max(x²/2, |x|−1), and the Huber-like function
  all satisfy L(Lf) = f to machine zero — period exactly 2, never 3.
  (e^x is excluded from the numeric check: its transform is unbounded
  for p ≤ 0.)
* Lean 4 (core, v4.33.1), `lean4/` — `period3_collapse`,
  `no_genuine_period3`, `fixed_point_consistent`, and the assembly
  `conjecture_refuted`.  All 4 audited theorems report `does not
  depend on any axioms`.

## Boundary

The kernel treats L abstractly with the involution property as a
hypothesis — the refutation applies to the concrete Legendre transform
via Fenchel–Moreau (classical, cited in prose).  The numeric round
trips are on bounded grids with the sup attained on-grid.
