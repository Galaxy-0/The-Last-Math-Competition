# Solution Review — Conjecture 00000001230 (PR 536)

**Submission:** jilint777 — `jilint777_submission_20261004155214`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read independently. The report correctly targets its stated direct-sum decomposition and treats the unspecified exponents in their weakest existential form.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded for all six pages; the shipped and rebuilt reports have matching content after normalizing the shipped PDF's bullet ToUnicode glyph. No TeX warnings.
- Lean: self-contained Lean 4.19.0 core project built successfully; direct `lake env lean -DwarningAsError=true Main.lean` also succeeded.
- Axioms: every printed theorem depends only on `propext` and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary code: `verify.py` exited 0 with every exact Smith-normal-form and witness check passing. A separate SymPy calculation independently reproduced the two key witness orders.
- Base metadata marks the conjecture unsolved.

## Semantic audit
The grid `[2]×[2]` is the cycle C₄. Its reduced Laplacian has determinant 4 and its sandpile group is ℤ/4: the chip `e₀` satisfies `4e₀=L̃(3,1,2)` but `2e₀` is not in the Laplacian image. For side lengths `(2,2)`, every subset gcd is 0 or 2. In every product of ℤ and ℤ/2 summands, `4x=0` forces `2x=0`, so a group with an element of exact order 4 cannot inject, much less be isomorphic. Therefore no choice of exponents `e(S)` can make
`Jac([2]×[2])≅⊕_S(ℤ/gcd S)^{e(S)}`.
This refutes the universal first clause of the conjecture.

The Lean formalization builds actual grid Laplacians and cokernels rather than assuming a group. It proves the exact order witness, an explicit ℤ/4 isomorphism, no additive injection into any arbitrary product with moduli 0,1,2, and the resulting failure under vertex-count and edge-count conventions. It also handles Pic and Pic⁰ readings, a dimension-three cube counterexample, and the lcm/product misreading using `[2]×[3]≅` sandpile group ℤ/15 with an element of exact order 5 while all relevant moduli divide 6. Path sanity checks and the explicit C₄ isomorphism prevent vacuity.

The report clearly separates the rigorous main result from supplemental Python-only torus/strong-product remarks. Since the conjecture's second clause is vague and any explicit two-dimensional formula of the stated direct-sum form is a particular choice of exponents, the stronger no-exponents obstruction already refutes the conjunction.

## Issues found
None blocking.

## Verdict
APPROVED. `Jac([2]×[2])≅ℤ/4` cannot be built from subset-gcd cyclic summands, and robust formal/numerical checks cover alternative conventions and even lcm/product readings.
