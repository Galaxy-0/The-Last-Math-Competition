# Disproof of conjecture `00000000277`

**Verdict: FALSE — the square torus has an eigenvalue of multiplicity 8.**

## The conjecture (verbatim from `conjectures/00000000277.md`)

> Definition: M(T) is the maximum multiplicity of a Laplace eigenvalue on a
> planar flat torus T = ℂ/Λ, and M its supremum over all flat tori.
> Conjecture: M = 6 (6 is known to be attainable, and upper bounds ≥ 6 are
> constrained by congruence structure); and multiplicity six is attained
> only on the lattice torus with maximal automorphism group of order
> thirty-two.

**Object consistency.** We attack exactly: M = 6, with multiplicities
computed on the dual lattice as is standard for flat tori.

## The refutation

On the **square torus ℂ/ℤ²**, the Laplace eigenfunctions are e^{2πi⟨k,z⟩}
for k in the dual lattice ℤ², with eigenvalues 4π²|k|². The squared norm

    |k|² = 5

is attained by exactly **eight** lattice vectors: (±1, ±2) and (±2, ±1)
(kernel-enumerated over the exhaustive box [−4,4]²; any vector with
x²+y²=5 has |x|,|y| ≤ 2). Hence the eigenvalue 20π² has **multiplicity
8 > 6** on the square torus: M ≥ 8, refuting M = 6 (and with it the
"only on the order-32 automorphism lattice" clause).

(Indeed multiplicities on square tori are r₂(m) counts, which are
unbounded — r₂(5^j) = 4(j+1) — so no finite bound of this size can hold;
the single certificate above suffices.)

## Reproduce

`python3 reproduce.py` — lists all lattice vectors with |k|² = 5 (8 of
them), and r₂(5^j) for j = 1..4 showing unbounded multiplicities.
Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 2 theorems
(`count_is_8` via kernel enumeration of the box, `eight_gt_six`), both
`does not depend on any axioms`.

## Boundary

Only M = 6 is refuted (M ≥ 8 from one torus). The true supremum M = ∞ is
indicated by reproduce.py but not formalized.
