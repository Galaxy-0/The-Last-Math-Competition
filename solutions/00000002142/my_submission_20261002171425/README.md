# Disproof of conjecture `00000002142`

**Verdict: FALSE — the parameter set (460,153,32,57) admits no strongly
regular graph, so the conjectured mate count has no subject matter.**

## The conjecture (verbatim from `conjectures/00000002142.md`)

> Definition: Cospectral mates of SRGs are strongly regular graphs with the
> same parameters but non-isomorphic. Conjecture: The number of mates with
> parameters (460,153,32,57) is explicit; and the kernel of the number is a
> biplane count. (SRG-460 biplane count mates explicit)

**Object consistency.** We attack exactly the parameter set (v,k,λ,μ) =
(460,153,32,57) named in the conjecture.

## The refutation

Every SRG(v,k,λ,μ) satisfies the classical two-path identity
(**necessary condition**, from double counting):

> Fix a vertex x. Count length-2 paths from x to vertices non-adjacent to
> x. Each of the k neighbors of x has k−λ−1 neighbors other than x itself:
> k(k−λ−1) paths. Each of the v−k−1 non-neighbors of x is reached by such
> a path exactly μ times: (v−k−1)μ paths. Hence
> k(k−λ−1) = (v−k−1)μ.

At (460,153,32,57):

    153 · (153 − 32 − 1) = 153 · 120 = 18360
    (460 − 153 − 1) · 57 = 306 · 57   = 17442

**18360 ≠ 17442.** No SRG with these parameters exists. Consequently there
are no "cospectral mates with parameters (460,153,32,57)" — the conjectured
explicit count and its biplane kernel describe an empty family.

## Boundary (per the 1016/#130 review convention)

- Literal layer: with zero SRGs of these parameters, the number of mates is
  0 — there is no positive "explicit" enumeration and no biplane kernel, so
  the asserted structure does not exist.
- Definitional layer: the generator picked an infeasible parameter set
  (violating a classical necessary identity), which is exactly the kind of
  pathology `well_definedness_level` should flag (cf. #154).

## Reproduce

`python3 reproduce.py` — the two products, the failed identity, and a
brute-force check that no 4-vertex-scale sanity issue exists (the identity
is checked on known feasible SRG parameter sets where it holds). Exit 0.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 5 theorems
(`kle`, `vkm`, `lhs`, `rhs`, `identity_fails`), all
`does not depend on any axioms`.
