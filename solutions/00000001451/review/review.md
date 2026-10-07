# Solution Review — Conjecture 00000001451 (PR 745)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261006031428`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results
- Conjecture read in both languages; `ORIGINAL.md` is byte-identical to the official `conjectures/00000001451.md`.
- Change policy: only the declared submission folder is added; no metadata, conjecture, root, or unrelated files are changed.
- LaTeX: independently rebuilt with `latexmk -pdf` (exit 0). Shipped and rebuilt PDFs contain identical text after ligature/line-break extraction normalization.
- Lean: fresh `lake build` under Lean 4.19.0 / Mathlib `c44e0c8e...` succeeded with zero errors and zero warnings.
- Axioms: independent `#print axioms` on `conjecture_exact_false`, `conjecture_asymptotic_false`, `conjecture_order_false`, `dimension_two_not_theta`, and `Vanishing.exists_sqrt_gap` shows only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe definition, `implemented_by`, or `extern` anywhere in the project.
- Auxiliary code: `verify.py` (fresh build, strict module replay, declaration audit, dependency pins) exited 0 under my run with the pinned package pool. The argument itself is symbolic; no numerical computation supports it.
- Duplicate status: base metadata marks 00000001451 unproven and undisproven.

## Semantic audit
Both language versions print the rate c_d·ε^((d−1)/2) with the positive exponent, together with the exact definition vol(K△P) ≤ ε·vol K and the phrase "the constant in the optimal approximation order". The submission negates the printed statement at d = 2 under three increasingly weak readings — literal equality to a positive constant on some interval, positive leading asymptotic constant (ratio tending to 1), and a two-sided Θ(ε^((d−1)/2)) order — each negated in its dimension-universal form, which is the exact negation of the stated claim; refuting the d = 2 instance defeats any reading that requires the formula for all d.

The obstruction is a genuine mathematical fact and is airtight: facet counts are natural numbers, and for t = min(√δ, 1/b)/2 the error ε = t² lies in (0, δ) with b·√ε = b·t < 1 and a·√ε > 0, so no natural number can lie between a·√ε and b·√ε. Hence even the weakest two-sided order reading is impossible, and the exact-equality and asymptotic readings imply it. Note the argument does not depend on what the minimal facet count actually is (in reality it grows like ε^{−1/2}); it only uses that any value of the printed formula is eventually below 1 while the count is a positive integer. No sign-corrected rate ε^{−(d−1)/2} is asserted or refuted — the report states this scope boundary explicitly, which is exactly the right discipline.

The definitions are faithful: polytopes are convex hulls of finite point sets in `EuclideanSpace ℝ (Fin d)`; facets are nonempty proper exposed faces of intrinsic codimension one; the approximation condition is the actual Lebesgue volume of the symmetric difference; the ε factor enters as `ENNReal.ofReal ε`, which equals ε for ε > 0; and "minimal" is formalized as an attained minimum over facet counts, with finiteness of exposed faces, uniqueness of counts and minima, and the equivalence of attainment with existence of an approximant all proved (`minimum_exists_iff`). The witnesses n in the three printed readings are actual attained minima, so no vacuous or default-valued quantifier is used.

## Issues found
None blocking.

## Verdict
APPROVED. The integer obstruction against the printed positive exponent is rigorous and correctly quantified, the geometric vocabulary is faithful to the source definition, all independent builds and audits pass, and the decisive theorems negate the printed claim under every reasonable reading of "is c_d·ε^((d−1)/2)".
