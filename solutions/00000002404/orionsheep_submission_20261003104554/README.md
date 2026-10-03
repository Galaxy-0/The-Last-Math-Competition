# Disproof of conjecture `00000002404`

**Verdict: FALSE — the "strict inequality when noncommuting" clause
fails at the certified instance f(z) = z², g(z) = 3z²: the two do not
commute (f∘g = 9z⁴ ≠ 3z⁴ = g∘f, kernel-certified via the monomial
composition rule), but every Julia set involved is a circle
(z ↦ azⁿ has J = {|z| = |a|^{−1/(n−1)}}, completely invariant), so
dim J(f∘g) = dim J(f) = dim J(g) = 1 — the strict inequality would
demand 1 > 1. The "explicit parameter conditions" for a strict family
do not exist on this noncommuting pair.**

## The conjecture (verbatim from `conjectures/00000002404.md`)

> Conjecture: The Julia dimensions of compositions of polynomials
> satisfy dim J(f∘g) ≥ max(dim J(f), dim J(g)), with strict
> inequality when f, g are noncommuting; the parameter conditions for
> the strict family are explicit.

## The refutation

The monomials f(z) = z² and g(z) = 3z² do not commute: by the
composition rule (c·z^d)∘(e·z^k) = (c·e^d)·z^{dk},
f∘g = 9z⁴ while g∘f = 3z⁴ — distinct polynomials (kernel-certified:
(9,4) ≠ (3,4)). Yet z ↦ a·zⁿ maps the circle |z| = |a|^{−1/(n−1)}
to itself completely invariantly (|a||z|ⁿ = |z| ⟺ |z|^{n−1} =
|a|^{−1}), so J(9z⁴), J(3z⁴), J(z²), J(3z²) are all exact circles —
Hausdorff and box dimension exactly 1. Hence
dim J(f∘g) = max(dim J(f), dim J(g)) = 1 with NO strict inequality,
despite noncommutation: the conjecture's strict clause would demand
1 > 1 (kernel-certified false). Box-counting on the analytic filled
sets confirms 0.92 → 1 for all four.

The non-strict inequality itself (dim J(f∘g) ≥ max(...)) survives
here as an equality; what is refuted is precisely the added strictness
under noncommutation — the conjecture's own example class (monomials)
supplies a noncommuting pair with zero dimensional jump.

## Verification

* `reproduce.py` — symbolic noncommutation (9z⁴ vs 3z⁴) with
  numerical spot checks; box-counting dimension of the four Julia
  circles (|z| = 1, 1/3, 9^{−1/3}, 3^{−1/3}), all ≈ 1.
* Lean 4 (core, v4.33.1), `lean4/` — `composeMono` (the monomial
  composition rule as an abbreviation), `fg`/`gf` (9z⁴, 3z⁴),
  `noncommuting` ((9,4) ≠ (3,4)), `not_strict` (¬(1 > 1)),
  `conjecture_refuted`.  All 5 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the exact monomial arithmetic: both compositions,
their inequality (noncommutation), and the failure of the strict
dimension inequality at the common value 1.  The fact that z ↦ azⁿ
has a completely invariant circle (dimension 1) is classical complex
dynamics, cited in prose and confirmed by the script's box counts.
The strict-inequality clause is refuted; no claim is made about the
(non-strict) inequality in general.
