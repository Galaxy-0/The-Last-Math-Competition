# Solution Review — Conjecture 00000007744 (PR 719)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261005212847`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read in both languages; `original_conjecture.md` is byte-identical to the official `conjectures/00000007744.md`.
- Change policy: only the declared submission folder is added; no metadata, conjecture, root, or unrelated files are changed.
- LaTeX: independently rebuilt with `latexmk -xelatex` (ctex document, exit 0). Shipped and rebuilt PDFs contain identical text.
- Lean: fresh `lake build` under Lean 4.19.0 / Mathlib `c44e0c8e...` succeeded with zero errors and zero warnings.
- Axioms: independent `#print axioms` on `conjecture7744_false`, `no_required_second_order_limit`, `no_claimed_quadratic_limit`, and `quadraticTrace_eq` shows only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe definition, `implemented_by`, or `extern`.
- Auxiliary code: `verification/check_small_ensembles.py` and `verification/independent_count_check.py` (exact rational arithmetic) both exited 0 and reproduce the report's table — 1 labeled cubic graph on 4 vertices and 70 on 6 vertices, all normalized traces equal to 3, centered variance 0 versus claimed limit 8/9. The bespoke independent verifier (fresh copy, strict replays, 83-declaration audit, nine dependency pins) also exited 0 under my run.
- Duplicate status: base metadata marks 00000007744 unproven and undisproven.

## Semantic audit
The Chinese text makes the second-order process explicit: (tr p(A) − E)·√n. The decisive observation is that the x² coordinate is degenerate in the uniform d-regular model: (A²)_{vv} = Σ_w A_{vw}A_{wv} = deg(v) = d, so tr(A²) = nd for every d-regular graph. The centered, √n-scaled quadratic trace is therefore identically zero — for any deterministic matrix/trace normalization, including the standard a = 1, b = 1/n and the unnormalized trace. This is a complete proof of Proposition 1 of the report and is correctly formalized in `quadraticTrace_eq` with `adjMatrix_mul_self_apply_self` and the regularity hypothesis.

The quantifier structure is right. The conjecture asserts a conjunction: the joint limit process exists, is Gaussian, has the stated covariance, and in particular the x² coordinate has Var = 4 − 12/d + 8/d². The Lean predicate `RequiredSecondOrderLimit` states only the necessary part — existence of all finite-dimensional weak limits plus that variance identity — and its negation refutes the whole conjunction without redefining Gaussianity or the covariance rule. At d = 3 the prescribed variance is 8/9 > 0 while every possible weak limit has variance 0: all coordinate laws are exactly Dirac at zero, uniqueness of weak limits in Mathlib's Hausdorff `ProbabilityMeasure` topology identifies the limit with δ₀, and `variance id` under δ₀ is 0. No interchange of variance and limits occurs.

The model is faithful: sampling is uniform over the entire subtype of labeled simple d-regular graphs on the vertex set (`PMF.uniformOfFintype`, equal masses proved), not over a configuration-model surrogate; the disjoint K_{d+1} block graphs serve only as nonemptiness witnesses at the unbounded sizes (k+1)(d+1). Joint laws are genuine pushforwards, coordinate marginals arise by continuous projection, and the x² specialization of the polynomial trace is proved, not assumed. The report correctly does not dispute the first-order Kesten–McKay convergence and makes no claim about other coordinates; the refutation rests solely on the explicitly prescribed, provably false x² variance.

## Issues found
None blocking.

## Verdict
APPROVED. The determinism tr(A²) = nd is verified, the resulting Dirac-at-zero limit with variance 0 contradicts the conjecture's prescribed 8/9 at d = 3 exactly as stated, all quantifier directions are faithful, and every independent build, axiom audit, and auxiliary computation passes.
