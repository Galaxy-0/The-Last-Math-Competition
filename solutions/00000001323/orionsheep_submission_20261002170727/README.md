# Disproof of conjecture `00000001323`

**Verdict: FALSE — an order-5 automorphism with Jacobian 1 exists.**

## The conjecture (verbatim from `conjectures/00000001323.md`)

> Definition: The Jacobian-conjecture class in the automorphism group
> Aut(Cⁿ). Conjecture: In Aut(C²), the set of possible periods of elements
> with Jacobian constant 1 is {1, 2, 3, 4, 6} (a conformal-symmetry
> restriction).

**Object consistency.** We attack exactly: period of an element of
Aut(C²) whose (constant) Jacobian determinant is 1.

## The counterexample

**A = diag(ζ₅, ζ₅⁻¹)** where ζ₅ is a primitive 5th root of unity.

- A is a **linear** automorphism of ℂ², hence in Aut(ℂ²);
- its Jacobian is the constant det A = ζ₅ · ζ₅⁻¹ = **1**;
- Aᵏ = diag(ζ₅ᵏ, ζ₅⁻ᵏ) = I ⟺ ζ₅ᵏ = 1 ⟺ **5 | k**: the period is
  exactly **5**;
- 5 ∉ {1, 2, 3, 4, 6}.

## Lean certificate

Arithmetic is certified in the cyclotomic quotient
ℤ[t]/(t⁴+t³+t²+t+1) = ℤ[ζ₅] (elements are coefficient 4-vectors;
multiplication reduces t⁴ = −(t³+t²+t+1), t⁵ = 1, t⁶ = t):

- `t · t⁴ = 1` and `t⁴ · t = 1` (so t is a unit and det diag(t, t⁴) = 1);
- `tᵏ ≠ 1` for k = 1..4 (t is a *primitive* 5th root: components 0,0,0,−1);
- `(t⁴)ᵏ ≠ 1` for k = 1..4 (t⁸ = t³, t¹² = t², t¹⁶ = t);
- `5 ∉ {1,2,3,4,6}`.

The identification ℤ[t]/p(t) ≅ ℤ[ζ₅] ⊂ ℂ (t ↦ ζ₅) is the standard
isomorphism — the only step outside the kernel, and it is where the
matrix diag(t, t⁴) becomes diag(ζ₅, ζ₅⁻¹). 13 theorems, all
`does not depend on any axioms`.

## Reproduce

`python3 reproduce.py` — does the same arithmetic over ℤ[ζ₅] with
polynomial reduction, AND evaluates numerically with `cmath` (ζ = e^{2πi/5})
checking det = 1 and Aᵏ ≠ I for k = 1..4, A⁵ = I. Exit 0 iff all pass.

## Boundary

Only the literal period-set claim is refuted. (Note the set {1,2,3,4,6} is
the familiar crystallographic restriction — true for *finite subgroups*
orderwise in several settings — but periods of individual Jacobian-1
automorphisms are unconstrained by it.)
