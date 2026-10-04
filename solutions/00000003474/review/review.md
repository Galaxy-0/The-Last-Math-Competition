# Solution Review — Conjecture 00000003474 (PR 449)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261004113847`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read; `SOURCE.md` is byte-identical to the official file.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. Both shipped and rebuilt PDFs have two pages with matching semantic content after extraction normalization; no mathematical discrepancy.
- Lean: fresh Lean 4.19.0/Mathlib `c44e0c8e...` build passed, as did direct `lake env lean -DwarningAsError=true Main.lean`.
- Axioms: core/final theorems use only `propext`, `Classical.choice`, and `Quot.sound`; simplicity checks use none. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, `extern`, or kernel-check bypass occurs.
- Auxiliary code: `verify.py` exited 0 after enumerating all 32 and 1024 induced subsets over GF(2). A separate independent recurrence and rank calculation reproduced both polynomials and the root-location certificate.
- Base metadata marks the conjecture unsolved.

## Semantic audit
Using the explicitly identified original one-variable ABS interlace polynomial, the path recurrence gives `q(P5;x)=x^3+5x^2+2x=x(x^2+5x+2)`. Since the conjecture imposes no connectedness restriction and interlace polynomials multiply over disjoint unions, `q(P5⊔P5;x)=x^2(x^2+5x+2)^2`. Thus `r=(-5-√17)/2` is a nonzero real root of multiplicity exactly two, and `√17>3` gives `r<-4`. A real repeated root outside [-4,0] refutes the conjecture's first multiple-root-location clause, hence the full conjunctive statement as written.

The Lean witness is a genuine ten-vertex loopless symmetric adjacency matrix for two disjoint P5 components. Deletion and the ABS pivot are implemented directly; the polynomial recursion is total; its relation to the evaluated leaf reduction is proved generally; and graph simplicity, the two polynomial identities, nonzero status, square divisibility at `r`, and `r<-4` are all proved. The report clearly identifies the standard original interlace-polynomial convention and does not claim results for other variants or for the conjecture's other clauses. The independent GF(2) subset-nullity computation provides a separate exact cross-check of the polynomial values.

## Formalization boundary
General pivot-order independence and the equivalence of the pivot recurrence with the subset-nullity formula are cited published ABS results rather than re-proved. This does not weaken the submitted counterexample: the Lean theorem derives the polynomial for a concrete graph from the original recurrence and makes no assumption assigning a precomputed polynomial to the witness. The disclosed boundary is acceptable.

## Issues found
None blocking.

## Verdict
APPROVED. The mathematical computation, independent exact verification, and Lean build/axiom audit all support a genuine repeated real interlace root below -4 for an admissible finite simple graph.
