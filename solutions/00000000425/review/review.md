# Solution Review — Conjecture 00000000425 (PR 304)

**Submission:** gaochengzhecpu — `gaochengzhecpu_submission_20261003091740`
**Reviewer:** competition review pipeline (structure + build + semantic audit)
**Date:** 2026-10-03

## Checklist results
- Conjecture read: yes — the coefficient sequence of the diagonal specialization of MacMahon's boxed plane-partition product always satisfies coefficientwise log-concavity (equality only at the diagonal single cell).
- LaTeX: compiled ok (pdflatex run twice, exit 0 both, 2 pages, 187 KB); included main.pdf is a real PDF (42 KB, 2 pages — verified by decompressing object streams); tex and pdf agree.
- Lean build: fresh build after `rm -rf .lake`, exit 0, no warnings (`-DwarningAsError=true` active), toolchain v4.19.0, no dependencies beyond Std.
- Forbidden content: none — no `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `@[implemented_by]`, `extern`. Only `set_option maxRecDepth/maxHeartbeats` (allowed). `#print axioms` present: final theorems depend only on [propext, Quot.sound(, Classical.choice)] — no sorryAx.
- Auxiliary code: verify.py run, exit 0; regenerated auxiliary-verification.json content-identical to recorded (inner sha256 map identical, outer file hash matches verification.json record). auxiliary-results.json matches reproduced output. All recorded file hashes match current files; official conjecture sha256 matches `original_source_sha256`.
## Semantic audit
Conjecture (literal): "The coefficient sequence of the diagonal specialization always satisfies coefficientwise log-concavity." Two plausible readings; both are formalized and refuted.

Reading 1 (fixed diagonal/cubic box). Lean enumerates all 81 candidate 2×2 arrays with entries in Fin 3 under the exact plane-partition predicate `IsPlanePartition g := a ≥ b ∧ a ≥ c ∧ b ≥ d ∧ c ≥ d` (all four weak-monotonicity inequalities of a 2×2 plane partition; box 2×2×2 via entries ≤ 2) and proves completeness (`allGrids_complete`), no duplicates, and membership_exact. The volume generating coefficients are (1,1,3,3,4,3,3,1,1) (`full_coefficient_list`, kernel decide), so `conjecture425_counterexample : ¬ LogConcave coefficient` via c₁² = 1 < 3 = c₀c₂. Moreover the disproof is anchored in the conjecture's actual product: `macMahonNumerator/Denominator n` are the genuine three-fold products ∏_{i,j,k=1..n}(1−q^{i+j+k−1}) resp. (1−q^{i+j+k−2}) (0-based shift +2/+1), `IsMacMahonCubeSeries n f := ∀ k, seriesMul (macMahonDenominator n) f k = macMahonNumerator n k` (i.e. D·F = N), and `macmahon_cube_two_not_logconcave (f) (hf : IsMacMahonCubeSeries 2 f) : ¬SeriesLogConcave f` shows ANY series satisfying the MacMahon equation for the 2×2×2 box starts 1,1,3 and fails log-concavity; `macmahon_product_counterexample` instantiates with the explicitly constructed infinite quotient `macMahonCubeTwo := formalQuotient D₂ N₂`, whose spec `D·F = N` at every index is proved (`formalQuotient_spec`). No appeal to MacMahon's counting theorem is needed.

Reading 2 (coefficientwise log-concavity across box sizes: every coefficient of Fₙ² − F_{n−1}F_{n+1} ≥ 0). `macmahon_cross_size_coefficient (f1 f2 f3) (h1 h2 h3) : seriesMul f2 f2 28 − seriesMul f1 f3 28 = −1` for arbitrary series satisfying the three MacMahon equations; the finite tables C₁, C₂, C₃ are pinned to the true quotients by `equation_prefix_unique` (strong induction, valid since Dₙ(0)=1, kernel-verified) plus the factor-by-factor kernel computations of the actual products through degree 28. `macmahon_diagonal_coefficientwise_counterexample : ¬DiagonalCoefficientwiseLogConcavity` refutes the universal claim at n = 2 using the constructed quotients (existentially witnessed by `macMahonCubeOne/Two/Three` with their specs). The n=3 table sums to 980 and is palindromic of degree 27 — consistent with the known count of plane partitions in the 3×3×3 box.

Hypotheses/contradiction: the 2×2×2 box is genuinely a "diagonal specialization" (equal side lengths, the reading pinned in SOURCE.md); the theorems establish exactly the negation of the conjectured log-concavity, for both readings. The second clause of the conjecture (equality only at the diagonal single cell) is moot once strict log-concavity fails, as the report states. Not vacuous: the objects are the actual boxed-plane-partition/MacMahon-product objects, not an unrelated arithmetic fact.

LaTeX/Lean match: same polynomial 1+q+3q²+3q³+4q⁴+3q⁵+3q⁶+q⁷+q⁸, same coefficients (1,1,3), same q²⁸ coefficient −1, same theorem names.
## Issues found
- Minor (non-blocking): the interpretation "diagonal specialization = equal box side lengths" is one plausible reading of the terse official statement; since both this and the cross-size reading are refuted, and any specialization retaining the 2×2×2 cubic product fails identically, the disproof is robust to the ambiguity.
- Minor (non-blocking): equality-characterization clause of the conjecture not formalized (unnecessary; the log-concavity clause is the decisive one and is refuted).
## Verdict rationale
The submission compiles cleanly, contains no placeholders or exotic axioms, runs and reproduces all auxiliary computations exactly, and its Lean theorems refute the conjecture on both plausible readings using the conjecture's own objects: the genuine MacMahon product (constructed as an explicit infinite formal quotient with a proved full spec and uniqueness) for the diagonal 2×2×2 box has coefficients 1,1,3,…, which is not log-concave, and F₂² − F₁F₃ has q²⁸-coefficient −1. The report and the Lean file agree in every number. This is a genuine, non-vacuous disproof.

## Disposition
APPROVED — merged into main (PR 304). Independent fresh rebuild of the Lean project (Lean 4.19.0, `lake build` with warnings-as-errors, exit 0, axioms limited to the standard Lean foundational set), LaTeX recompilation, auxiliary-script re-runs, and a semantic audit confirming the Lean theorem refutes the conjecture as stated in both language versions.
