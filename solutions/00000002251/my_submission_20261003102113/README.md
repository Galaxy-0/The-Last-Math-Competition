# Disproof of conjecture `00000002251`

**Verdict: FALSE — the kernel of Δ_c f = f(z+c) − f(z) on meromorphic
functions is the space of c-periodic functions, which is
INFINITE-dimensional (it contains the pairwise non-proportional family
e^{2πikz/c}, k ∈ ℕ), not 1-dimensional; and the spectrum conjunct
fails independently: the eigenfunctions e^{λz} have eigenvalues
e^{λc} − 1 sweeping a continuum (for complex λ, not even real), not
the discrete real set {2 sin(kc/2)}.**

## The conjecture (verbatim from `conjectures/00000002251.md`)

> Definition: The difference operator Δ_c f = f(z+c) − f(z).
> Conjecture: The kernel of Δ_c has dimension 1, and the spectrum of
> Δ_c on meromorphic function spaces (differences of difference
> polynomials) is explicit of the {2 sin(kc/2)} type (difference
> spectrum).

## The refutation

ker Δ_c is exactly the space of c-periodic meromorphic functions.  It
contains the constants, but also g(z) = e^{2πiz/c} for every integer
k ≥ 1 (c-periodic since e^{2πi} = 1).  These members are not
proportional: g(0) = 1 while g(c/4) = i, so g is not a multiple of
any constant — the kernel strictly exceeds the 1-dimensional span of
the constants.  In fact the family {e^{2πikz/c}}_{k∈ℕ} is pairwise
non-proportional: at z = c/4 the members k = 0..3 take the four Gauss
units 1, i, −1, −i (pairwise distinct — kernel-certified), and z = c/8
separates k = 0..7 into 8 distinct values; no finite list exhausts
the family.  dim(ker Δ_c) = ∞ ≠ 1.  (The "dimension 1" reading is
correct only for rational functions on the Riemann sphere — not the
meromorphic function space of the conjecture, where difference
polynomials live.)

The spectrum conjunct fails independently.  On the eigenfunction
e^{λz}, Δ_c acts as multiplication by e^{λc} − 1; as λ ranges over ℂ
these eigenvalues sweep ℂ ∖ {0} — a continuum, generally non-real
(e.g. λ = 1 + i, c = 1.7 gives −1.705 + 5.428i) — nothing like the
fixed real discrete set {2 sin(kc/2)}.

## Verification

* `reproduce.py` — c-periodicity of e^{2πikz/c} for k = 1..8 (1e-9);
  the quarter- and eighth-grid value separations (4 and 8 pairwise
  distinct members); non-constancy of g; the eigenvalue continuum vs
  {2 sin(kc/2)} for k = −20..20.
* Lean 4 (core, v4.33.1), `lean4/` — `unit4_period` (the value-level
  c-periodicity g(z+c) = g(z), i.e. the Δ_c g = 0 certificate, by
  `rfl` on the cyclic unit table), `g_samples` (1, i, −1, −i),
  `g_values`/`four_distinct` (pairwise distinct), `not_constant`
  (a function with two distinct values equals no constant).  All 6
  audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the value skeleton on the quarter grid: the
cyclic unit table, its period-c shift identity, the distinctness of
the four values, and the non-constancy criterion.  The passage from
these samples to the function-space statements (e^{2πi} = 1, the
family's pairwise non-proportionality, the eigenvalue formula) is
classical complex analysis, cited in prose and reproduced numerically
by the script.  Both conjuncts are refuted: the kernel dimension and
the spectrum shape.
