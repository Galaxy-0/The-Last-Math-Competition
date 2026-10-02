# Disproof of conjecture `00000002144`

**Verdict: FALSE — the star already exceeds the conjectured extremum.**

## The conjecture (verbatim from `conjectures/00000002144.md`)

> Definition: The maximal eigenvalue multiplicity of a tree. Conjecture:
> The extremum is ⌈(n+1)/3⌉, realized by gluing a path with stars; and the
> kernel of the realization is the matching number.

**Object consistency.** We attack exactly: the maximum eigenvalue
multiplicity over trees on n vertices, claimed to be ⌈(n+1)/3⌉.

## The counterexample

The **star** K_{1,n−1} is a tree whose spectrum is classically
{√(n−1), −√(n−1), 0^(n−2)} — eigenvalue 0 has multiplicity **n−2**.
(Elementary: its adjacency matrix has rank 2, since the n−1 leaf rows are
all equal to the first standard basis vector; equivalently the
characteristic polynomial is x^{n−2}(x²−(n−1)).)

| n | star K_{1,n−1}: mult of 0 | conjectured ⌈(n+1)/3⌉ |
|---|---|---|
| 5 | **3** | 2 |
| 7 | **5** | 3 |
| 9 | **7** | 4 |

The conjectured extremum is exceeded by the simplest tree, at every n ≥ 5.
(Incidentally the true maximum over trees on n vertices is n−2 for
K_{1,n−1}... no — the true extremal multiplicity for trees is known to be
attained by matching-like trees; the star gives n−2 only because n−2
leaves... note n−2 is achieved; the conjecture's ceiling formula is far
below it.)

## Reproduce

`python3 reproduce.py` — recomputes the star spectra numerically (numpy)
for n = 5, 7, 9 and prints the 0-multiplicities vs the bounds. Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 9 theorems
(multiplicity, bound, violation at n = 5, 7, 9), all
`does not depend on any axioms`. Scope: the star spectrum is classical
(proof sketch above); the kernel certifies the arithmetic.

## Boundary

Only the ceiling-formula claim is refuted. The "kernel is the matching
number" clause is not addressed.
