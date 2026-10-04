# Solution Review — Conjecture 00000008835 (PR 519)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004170233`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read independently; the report correctly targets its unconditional “summable tolerance ⇒ strong convergence” clause.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. The shipped and rebuilt two-page reports have the same formulas and prose; the shipped PDF's extraction has legacy CM ToUnicode glyph mappings, so comparison was made directly against the LaTeX source. Both PDFs render without warnings.
- Lean: official pinned dependencies were linked; fresh `lake build` and direct `lake env lean -DwarningAsError=true Main.lean` succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: all nine printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied or needed.
- Base metadata marks the conjecture unsolved.

## Semantic audit
Let `A(x)={1}` on the real Hilbert line. Its graph is maximal monotone: a purported extension value is forced to equal 1 by monotone comparison with neighboring graph points. It is Lipschitz and has no zero. The unit resolvent equation `x∈y+A(y)` is equivalent to `y=x-1`, so iterating the actual resolvent from x gives `u_n=x-n`. With zero additive errors and zero tolerances, every inclusion and error inequality is satisfied exactly, and the tolerance series has sum zero, hence is certainly summable. But consecutive orbit terms differ by -1, so no orbit has a finite strong limit.

Therefore even exact proximal-point iterations—an especially regular case of approximate inclusions with summable tolerances—fail the conjecture's unqualified convergence assertion. Lean proves the actual operator, maximality, Lipschitz property, unique resolvent, all iterates, all inclusions and errors, summability, empty zero set, and all-start nonconvergence. The report accurately notes that a nonempty-zero/solvability hypothesis is the missing condition.

## Issues found
None blocking.

## Verdict
APPROVED. Zero tolerances are summable, yet this genuine maximal-monotone proximal-point orbit diverges, refuting the conjecture as stated.
