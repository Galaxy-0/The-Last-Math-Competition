# Conjecture 00000002844 — literal scalar-eigenvalue counterexample

The Lean project models the actual order-three tensor
`T : Fin 1 → Fin 1 → Fin 1 → ℂ` whose sole entry is `1`. It proves the tensor
is symmetric, defines the full contraction `Tᵢⱼₖ xⱼ xₖ`, imposes the
complex-bilinear unit condition `∑ xᵢ² = 1` and nonzero-vector condition, and
forms the set of scalar eigenvalues witnessed by such vectors. The proved set
is exactly `{1, -1}`, with cardinality `2`; the displayed formula at `d=3,
n=1` is `1`.

This disproof is deliberately scoped to the source conjecture's literal count
of distinct scalar E-eigenvalues. The standard terminology supports this
reading: Sodomaco's Definition 1.1 calls `λ` an E-eigenvalue and `(λ,x)` an
E-eigenpair; for odd order it explicitly notes that `(λ,x)` gives
`(-λ,-x)`. However, the standard odd-order counting theorem counts sign-pairs
`(λ,-λ)`, not raw scalar values, and the E-characteristic polynomial degree
is twice that pair count. Thus this Lean project does not claim to refute a
sign-pair-counting version of the formula or formally establish a resultant
degree statement. Under sign-pair counting, `{1,-1}` contributes one class,
which agrees with the formula here.

Primary reference: Luca Sodomaco, *The Product of the Eigenvalues of a
Symmetric Tensor*, Definition 1.1 and Theorem 1.3, pp. 1 and 3:
[arXiv:1802.10173](https://arxiv.org/abs/1802.10173).

Lean 4.33.1 / Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

From `lean/`, run `lake update`, `lake exe cache get`, and `lake build`.
The pinned dependency lockfile is included. The two printed terminal
theorem audits have only `propext`, `Classical.choice`, and `Quot.sound`.
The report and its visually checked PDF are `solution.tex` and `solution.pdf`.
