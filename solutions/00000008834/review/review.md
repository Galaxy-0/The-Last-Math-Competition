# Solution Review — Conjecture 00000008834 (PR 514)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004171500`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture read; the preserved `verification/original.md` is byte-identical to the official file.
- Change policy: only the declared submission directory is added.
- LaTeX: independent `latexmk` build succeeded. The shipped and rebuilt one-page PDFs have identical extracted semantic content and no TeX warnings.
- Lean: official pinned dependencies were linked; `lake build` and ordinary direct `lake env lean Main.lean` both succeeded under Lean 4.19.0/Mathlib `c44e0c8e...`.
- Axioms: all six printed results depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe implementation, external implementation, or kernel bypass occurs.
- Auxiliary programs: none supplied or needed.
- Duplicate status: base metadata marks the conjecture unsolved.

## Semantic audit
The operator `A(x)={1}` on ℝ is monotone and maximal monotone. Maximality follows because a purported extension point `(x,u)` compared with `(x-1,1)` and `(x+1,1)` forces both `u≥1` and `u≤1`. It has no zero, which the unqualified source statement does not exclude.

For every ε>0, `0∈A(x)+εx` is exactly `1+εx=0`, hence has the unique solution `-1/ε`. Taking ε(t)=1/(t+1)>0, ε(t)→0, gives the divergent Tikhonov-root path `-(t+1)`. The submission then supplies an actual smooth viscosity trajectory `u(t)=-(t+1)/2`; since `u'=-1/2`, `u'(t)+1+ε(t)u(t)=0`, so it solves the regularized differential inclusion and also diverges. Therefore both standard readings of the convergence claim fail, even weakly. The first convergence conjunct is false, making the later rate clause irrelevant.

Lean proves maximality against arbitrary monotone graph extensions, absence of zeros, unique regularized roots, positivity and vanishing of ε, the derivative, the inclusion, and norm/weak nonconvergence. The final theorem combines these actual objects; no nonconvergence is assumed from emptiness of the zero set.

## Issues found
- Non-blocking Lean linter warnings: a dead `norm_num` tactic and two no-op tactics cause `lake build` warnings and make a warning-as-error direct run fail. Ordinary `lake build` and direct elaboration both exit successfully; the kernel checks every proof, and the warnings do not affect logical completeness.

## Verdict
APPROVED. The unqualified conjecture is refuted by a genuine maximal monotone operator with both divergent Tikhonov-root and viscosity-flow trajectories. All substantive build, PDF, axiom, path, and semantic checks pass.
