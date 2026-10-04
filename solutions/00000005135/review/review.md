# Solution Review — Conjecture 00000005135 (PR 355)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003215646`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-04

## Checklist results
- Conjecture read: yes — attainable domain of the supremal Hankel structured/unstructured condition-number ratio is claimed to be the closed interval [1, √n], upper end attained by symbol pairs.
- LaTeX: compiled in /tmp/tlmc-review2/scratch/pr-355 (pdflatex twice, exit 0 both passes); shipped main.pdf is a genuine 2-page PDF whose extracted text matches the tex word-for-word; tex/pdf/Main.lean SHA-256 all match VALIDATION.json.
- Lean build: fresh `rm -rf .lake && lake build` exit 0, no warnings (lakefile sets warningAsError=true; only info output is the four `#print axioms` lines, all "does not depend on any axioms"). Toolchain lean4:v4.19.0, bundled Std only, no external packages.
- Forbidden content: grep for sorry/admit/native_decide/axiom-decl/unsafe/implemented_by/extern/skipKernelTC found nothing (grep exit 1). `#print axioms conjecture_5135_endpoint_false` → empty axiom list. `decide` appears only in the Int consistency model (kernel-checked).
- Auxiliary code: none shipped (no verify.py etc.); nothing to run. The only numeric fact used is √4 = 2 > 1, verified trivially. No computational part of the conjecture is left uncovered (the disproof is analytic).
## Semantic audit
Conjecture literal claim (EN): "The attainable domain of the supremal ratio in the Hankel case is the explicit interval from one to the square root of the dimension, the upper end attained by symbol pairs, and the domain is closed." The ratio is defined in the Definition as "the ratio of structured to unstructured condition numbers", i.e. r = κ_s/κ_u with the structured domain (Hankel perturbations) a subset of the unstructured domain.

Key Lean definitions (lean/Main.lean):
- `Hankel {K n} (E : Matrix K n) : Prop := ∀ i j k l, i.val + j.val = k.val + l.val → E i j = E k l` — the correct anti-diagonal Hankel condition.
- `ConditioningProblem` bundles one `norm` and one `amplification` (arbitrary, so covering every derivative-derived sensitivity functional), with `structured_spec : IsLUB O (HankelDirections O norm) amplification structured` and `unstructured_spec : IsLUB O (UnitDirections O norm) amplification unstructured`, `IsLUB` being the full leastness predicate. Same norm ball for both — the standard comparison.
- `IsRatio O P r := O.mul r P.unstructured = P.structured` — division-free ratio with positive denominator hypothesis `denominator_positive`.
- Final theorem: `theorem conjecture_5135_endpoint_false {K R} (O : OrderedScale R) : ¬ EndpointAtFour (K := K) O`, where `EndpointAtFour := ∃ family, (∀ r, family r → AttainableRatio O 4 r) ∧ IsLUB O family id (two O)`.

The chain `lub_mono → condition_numbers_ordered (κ_s ≤ κ_u) → every_ratio_le_one (r ≤ 1) → every_supremal_ratio_le_one → conjecture_5135_endpoint_false` is mathematically airtight: the Hankel unit ball is a subset of the full unit ball (`fun _ h => h.1`), so its LUB is ≤ the LUB; every defined ratio and every supremum over ANY family of attainable ratios is ≤ 1, while the conjectured endpoint in dimension 4 is √4 = 2 > 1 (`one_lt_two` via `lt_add_right`). Since a symbol pair induces a conditioning problem and the family of symbol-pair ratios is a family of attainable ratios, attainment at the upper end (and hence the claimed interval/closedness of [1,√n]) is refuted for n = 4 (equivalently any n ≥ 2). The theorem is universally quantified over all K, all ordered-scalar structures O (which include ℝ), and all admissible problems, so it is not vacuous and covers every actual instantiation; the integer model `integerScale` only witnesses interface consistency.

Interpretation disclosure: the interval [1,√n] would be plausible for the inverse ratio κ_u/κ_s (likely the "intended" reading), but both the English ("structured to unstructured") and the Chinese ("结构化与非结构化条件数之比") order the ratio as κ_s/κ_u, which is what is formalized; the tex explicitly discloses that differently-scaled norms on the two sides would be a different definition. Under the authoritative literal bilingual statement plus the standard same-norm comparison (Arslan–Noferini–Tisseur), the disproof is sound.
## Issues found
none blocking
## Verdict rationale
The Lean project builds clean with empty axiom lists, the PDF and tex are genuine and consistent, no forbidden content exists, and the formalization faithfully encodes the conjecture's own objects (Hankel anti-diagonal structure, structured/unstructured condition numbers over the same norm and amplification, ratio, supremum over families, the √n endpoint). The final theorem genuinely contradicts the literal claim at n = 4 under the standard comparison, is fully general (not one example, not vacuous), and the interpretation call is explicitly disclosed in the manuscript.

## Disposition
APPROVED — merged into main (PR 355). Independent fresh rebuild of the Lean project (exit 0, warnings-as-errors where set, only standard foundational axioms), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem establishes or refutes the conjecture as stated in both language versions.
