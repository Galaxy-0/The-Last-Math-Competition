# Solution Review — Conjecture 00000008819 (PR 517)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004174500`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read; `verification/original.md` is byte-identical to the official file.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. The shipped and rebuilt two-page PDFs have matching semantic content; apparent raw extraction differences are only alternate ToUnicode parenthesis mappings. No TeX warnings.
- Lean: official pinned dependencies were linked; fresh `lake build` and direct `lake env lean -DwarningAsError=true Main.lean` succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: all five printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied or needed.
- Base metadata marks the conjecture unsolved.

## Semantic audit
The conjecture claims convergence for all closed proper convex objectives under Lipschitz gradients and cocoercivity, without requiring a minimizer. Take `f(x)=-x` and `g(x)=0`. Both are finite real-valued, proper, closed, and convex. The gradient `-1` is 1-Lipschitz and 1-cocoercive. For step 1, `0<γ<2/L`, and the proximal problem for g has unique solution `prox_g(y)=y`. Therefore
`T(x)=prox_g(x-γ∇f(x))=prox_g(x+1)=x+1`,
so every iterate sequence is `x₀+k` and diverges in norm and weakly. The objective has no minimizer because `-x` strictly decreases at every point. This refutes the universal convergence-domain clause; the other FISTA and heavy-ball clauses are not needed.

Lean uses actual real functions, epigraphs, convexity, gradients, Lipschitz and cocoercivity, full global proximal-minimizer inequalities, unique prox points, the forward-backward step, all iterates, nonattainment, and norm/weak nonconvergence. No conclusion is supplied as an assumption.

## Issues found
None blocking.

## Verdict
APPROVED. A genuine safe-step forward-backward iteration for a closed proper convex objective with the advertised gradient properties diverges, decisively refuting the unqualified convergence-domain assertion.
