# Solution Review — Conjecture 00000008433 (PR 778)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005224226`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** Wilson existence bound improvement.

## Checklist results

- **Official conjecture.** `conjectures/00000008433.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

Both clauses of the conjecture claim thresholds in t alone (exp(exp(t)); t^{ct}, c absolute) beyond which t-design existence is decided by the divisibility conditions. The submission proves no threshold in t can work: fix t = 2, λ = 1 and let v = (m−1)²(m+1), k = m(m−1) for m ≥ 3. All divisibility conditions hold — (k−1) | (v−1) with quotient r = m, C(k,2) | C(v,2) with quotient b = m²−1, and the trivial i = 2 case — and the parameters are admissible (2 ≤ t < k, k+t < v, 1 ≤ λ ≤ C(v−t,k−t)). Nevertheless no 2-(v,k,1) design exists: the λ = 1 case of Fisher's inequality, k(k−1) ≤ v−1, is proved from scratch by two double counts (a point outside a block lies in ≥ k blocks, one per block point via uniqueness with λ = 1; and ≤ (v−1)/(k−1) blocks, disjoint off the point), and here k(k−1) = m(m−1)(m²−m−1) > v−1 = m(m²−m−1). Since v → ∞ while t = 2 is fixed, for every threshold function T(t) — in particular exp(exp(t)) and t^{ct} for every real c — there are admissible, divisibility-satisfying, design-free parameters above the threshold. Both the indexed (repeated blocks allowed) and the simple formulations are refuted, and the concrete witness 2-(2016,156,1) (m = 13; 2016 > e^{e²} ≈ 1618.2) is recorded.

The formalization of the two clauses matches the text exactly, with Clause2 existentially quantifying over the absolute constant c; the more general `threshold_fails (T : ℕ → ℝ)` quantifies over arbitrary thresholds, the strongest possible negation. The design definition counts blocks by index (repeats allowed); the report correctly notes that omitting the redundant 'every point in exactly r blocks' condition only enlarges the class of designs, so the non-existence proofs a fortiori cover stricter definitions, and the simple-design variant reduces to the indexed one. Admissibility is the standard non-degeneracy package and is satisfied by the family.

I verified the family arithmetic symbolically and numerically: v−1 = m(m²−m−1) = m(k−1), b = m²−1; for m = 13: v = 2016, k = 156, r = 13, b = 168, and 156·155 = 24180 > 2015, so Fisher indeed forbids the design. The report honestly scopes what is not refuted: thresholds allowed to depend on k and λ (Wilson's actual theorem form) are untouched — but those are not what the conjecture states.

## Issues found

None material.

## Verdict

APPROVED. A decisive disproof of both clauses: with t = 2 fixed, divisibility-satisfying admissible parameter sets with no design (simple or indexed) exist at arbitrarily large v, so no threshold in t alone — including exp(exp(t)) and t^{ct} for any c — makes divisibility sufficient.
