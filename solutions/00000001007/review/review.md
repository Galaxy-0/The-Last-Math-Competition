# Solution Review — Conjecture 00000001007 (PR 535)

**Submission:** jilint777 — `jilint777_submission_20261004154608`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read independently. The report quotes and correctly targets its literal even-characteristic universal clause.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded for all five pages. The shipped and rebuilt reports have matching content after a bullet-glyph extraction normalization; no overfull boxes occur (only nonfatal underfull lines caused by long identifiers).
- Lean: self-contained Lean 4.19.0 core project built successfully, and direct `lake env lean -DwarningAsError=true Main.lean` passed.
- Axioms: no theorem uses a nonstandard axiom. Core finite checks use no axioms; other printed theorems use only `propext`, `Quot.sound`, and standard `Classical.choice` where applicable. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe code, external implementation, or kernel bypass occurs.
- Auxiliary code: `verify.py` exited 0 with all exhaustive checks passing. A separately implemented GF(8) checker independently reproduced the key line, rank, non-collinearity, and control checks.
- Base metadata marks the conjecture unsolved.

## Semantic audit
In GF(8), the lifted Suzuki–Tits set
`T={(1,x,y,xy+x⁶+y⁴,x³+y²):x,y∈GF(8)}∪{(0,0,0,1,0)}`
lies on the parabolic quadric `Q:x₀x₃+x₁x₂+x₄²=0`. It has q²+1=65 distinct projective points. The polar form is nonzero on every pair, so no two are collinear on Q; equivalently, exhaustive enumeration shows each of the 585 Q-lines meets T exactly once. Therefore T is an ovoid in even characteristic q=8.

It cannot be an elliptic quadric in either standard sense. As a subset of PG(4,8), every elliptic quadric section lies in a hyperplane, but T has linear span/rank 5: the points `t(0,y)` force four linear coefficients to vanish, and `t(1,0)` forces the last. Under projection from the nucleus to PG(3,8), every elliptic quadric lies on a quadratic surface, but evaluation on four families of Tits points kills all ten quadratic coefficients; equivalently, its quadratic-monomial matrix has rank 10. Thus both necessary conditions fail.

Lean constructs GF(8), checks its field axioms and characteristic, proves the quadratic form's polarization and nondegeneracy, defines the finite ovoid predicate, and proves T's ovoid status by kernel-checked finite verification. It avoids brute-forcing all hyperplanes/quadrics by using explicit inverse-matrix certificates for five linearly independent points and ten independent quadratic monomials. It proves non-vacuity with a genuine elliptic control ovoid and includes an any-reading theorem covering predicates that imply either standard elliptic condition. The independent Python verifier exhaustively checks all lines, hyperplanes, triples, ranks, and the control.

The conjecture's parenthetical incorrectly places Suzuki examples in odd characteristic, but the literal universal even-characteristic claim is unqualified. Since q=8 is even and T is a non-elliptic ovoid, the conjecture is false as stated.

## Issues found
None blocking.

## Verdict
APPROVED. The Suzuki–Tits ovoid of Q(4,8) is a genuine ovoid but fails both standard necessary conditions for being an elliptic quadric; the exhaustive computations, hand proofs, self-contained Lean build, and independent auxiliary checks all agree.
