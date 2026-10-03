# Disproof of conjecture `00000002715`

**Verdict: FALSE — a shellable 3-dimensional manifold complex exists on 5
vertices, so the conjectured minimal vertex count of twelve is wrong (and
the minimal example is a simplex boundary, not an "edge triangulation").**

## The conjecture (verbatim from `conjectures/00000002715.md`)

> Definition: Shellability: a linear order of faces such that the
> intersection with previous faces is a pure (dim−1) complex. Conjecture:
> The minimal scale of non-shellable manifolds: the minimal vertex count
> of a shellable 3-dimensional manifold complex is twelve, with the
> minimal example an edge triangulation; for higher dimensions, the
> minimal vertex count of non-shellable manifolds is a linear function of
> the combinatorial sphere vertex count. (shellable minimal scale)

## Object consistency

We attack the claim exactly as written, with the conjecture's **own**
definition of shellability ("a linear order of faces such that the
intersection with previous faces is a pure (dim−1) complex"). The
counterexample is the most standard object in the field: the boundary
∂Δ⁴ of the 4-simplex.

## The counterexample: ∂Δ⁴

∂Δ⁴ has vertex set {0,1,2,3,4} and C(5,4) = 5 tetrahedral facets.

1. **It is a closed combinatorial 3-manifold.** The link of each vertex v
   is the boundary of the 3-simplex on the other four vertices: its
   facets are the 3-subsets of V∖{v} (kernel-certified), a combinatorial
   2-sphere with f-vector (4, 6, 4).
2. **It is shellable, in the conjecture's own terms.** In the
   lexicographic facet order [0123], [0124], [0134], [0234], [1234], for
   every facet the faces already covered by earlier facets form a pure
   2-dimensional complex: every covered vertex and every covered edge
   lies in a covered triangle (kernel-certified, exactly the stated
   "intersection with previous faces is a pure (dim−1) complex"
   condition). Classically *every* order works for a simplex boundary;
   one explicit certified order suffices.
3. **It has 5 vertices.** 5 < 12, and the minimum over shellable
   3-dimensional manifold complexes is therefore ≤ 5 ≠ 12.

So the displayed minimal vertex count "twelve" is false as stated, and
the "minimal example is an edge triangulation" clause is false as well
(the vertex-minimal shellable example is a simplex boundary).

## Reading caveat, honestly stated

The conjecture's header speaks of "non-shellable" manifolds while the
formal sentence says "shellable"; we refute the sentence as written. For
completeness, under the presumably intended "non-shellable" repair:

* if 3-manifold **balls** (with boundary) count, the claim is also
  false: there are 29 vertex-minimal **non-shellable 3-balls with 9
  vertices** (F. H. Lutz, *Combinatorial 3-manifolds with 10 vertices*,
  arXiv:math/0604018 — complete enumeration);
* if restricted to **closed** 3-manifolds, the threshold is not known to
  be 12: all 3-spheres with up to 10 vertices are shellable
  (arXiv:math/0604018), the smallest known non-shellable **closed**
  example has 13 vertices (F. H. Lutz, *Small examples of
  non-constructible simplicial balls and spheres*, arXiv:math/0309149),
  and the cases 11–12 vertices are open. So no defensible reading makes
  "twelve" an established fact, and the literal reading is refuted by
  the certified example above.

## Verification

* `reproduce.py` — enumerates the face lattice of ∂Δ⁴ from scratch,
  checks the link structure (all links are tetrahedron boundaries with
  f-vector (4,6,4)) and **exhaustively checks all 5! = 120 facet orders**:
  every one satisfies the conjecture's shelling condition; prints 5 < 12.
* Lean 4 (core, v4.33.1, no Mathlib) — `lean4/`: 7 theorems, all closed
  kernel computations covering the lexicographic order shelling check,
  the link facet counts, the exact vertex count, and 5 < 12; all report
  `does not depend on any axioms`.

## Boundary

Only the 3-dimensional clause is addressed ("minimal vertex count ...
is twelve, minimal example an edge triangulation"); the vague
higher-dimensional clause is not.
