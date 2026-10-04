# Solution Review — Conjecture 00000008776 (PR 523)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004180000`
**Reviewer:** independent competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — the third explicit clause asserts that SGD with the optimal residual-proportional sampling distribution “always converges faster than uniform sampling,” with a stated improvement ratio.
- Change scope: only the allowed submission directory was added. Base metadata marks the conjecture unsolved and no prior solution existed.
- LaTeX: independently rebuilt with `latexmk -pdf -interaction=nonstopmode -halt-on-error disproof.tex` (exit 0; two pages; no errors or unresolved warnings). Shipped/fresh text agrees up to font and matrix-delimiter extraction artifacts; both shipped pages were split and rasterized.
- Lean build: Lean 4.19.0 / Lake 5.0.0, Mathlib exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`; exact official dependencies linked via the supplied script and Main compiled independently. `lake build` exit 0 (`[2806/2807] Built Main`) and plain direct `lake env lean Main.lean` exit 0. All seven audited theorems use only `[propext, Classical.choice, Quot.sound]`.
- Forbidden content: no executable `sorry`, `admit`, `native_decide`, axiom declaration, `unsafe`, `implemented_by`, `extern`, or `skipKernelTC`; broad hits are prose-only.
- Auxiliary code: none is supplied or needed.
## Semantic audit
The counterexample uses the actual consistent overdetermined system \(A=(1,1)^T\), \(b=(0,0)^T\), with nonzero identical rows. The unique least-squares minimizer is \(0\), each row loss is \(x^2/2\), and the mean normal matrix is \(1\), so the diagonal preconditioner is also \(1\). At every nonzero state the two preconditioned residuals coincide; therefore squared-residual-proportional sampling gives probabilities \((1/2,1/2)\), exactly uniform. Lean proves the normalized score formula and equality of the residual and uniform PMFs. It also proves sampling variance zero for every PMF, confirming this uniform law is genuinely optimal rather than merely called optimal.

With step \(1/2\), every row gradient is \(x\), so every sampled update is \(x-x/2=x/2\). Starting from 1, the full law after \(k\) steps is the point mass at \(2^{-k}\), regardless of the sampling kernel. Lean constructs these laws through actual PMF bind kernels, proves positivity at finite times, computes expected error \(2^{-k}\), and proves convergence to 0. Thus residual and uniform sampling have identical laws and identical expected errors at every step; strict improvement is impossible. This refutes the explicit “always faster” clause without relying on any convention at \(x=0\), since the iterates remain positive.

The first Kaczmarz decay clause, block-size claims, and harmonic-ratio formula are not needed and the report says so. The counterexample does not deny improvements for other systems or non-strict comparisons under extra hypotheses.
## Issues found
The Lean source has three harmless style/linter warnings at line 36 (unreachable/no-op `ring` and unnecessary `<;>`). They are recorded accurately in the shipped build log, do not introduce any proof gap, and the documented `lake build` succeeds. `lake env lean -DwarningAsError=true` consequently exits 1 on the first warning; this command is not part of the submission's reproduction instructions. The plain build and axiom audit are complete.
## Verdict rationale
An admissible overdetermined system yields exactly the same optimal residual sampler, full stochastic process, expected error, and convergence rate as uniform sampling. This decisively disproves the conjecture's universal strict-improvement assertion. The warnings are cosmetic, not incomplete or unsafe proofs.

## Disposition
APPROVED — ready to merge (PR 523). Independent fresh rebuild, direct plain Lean check, axiom audit, PDF rebuild/comparison, source inspection, forbidden-pattern scan, and semantic audit all passed; the documented build succeeds despite three non-blocking style warnings.
