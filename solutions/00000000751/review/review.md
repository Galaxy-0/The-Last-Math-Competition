# Solution Review — Conjecture 00000000751 (PR 748)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005202159`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `/Users/xinranwang/Documents/GitHub/The-Last-Math-Competition-2/conjectures/00000000751.md` read in full (bilingual). Shipped `conjecture.md` is byte-identical to it (`diff` empty).
- LaTeX: rebuilt independently with `latexmk -pdf -interaction=nonstopmode`; succeeds. Shipped vs rebuilt PDF text compared with pypdf after normalization: content matches; differences are glyph-extraction artifacts only (↦, ff-ligature, delimiter mappings of the authoring platform's fonts), cosmetic.
- Lean: `lake build` succeeds with zero errors and zero warnings (Lean v4.33.1, Mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474, prebuilt pool poolM04). Earlier "Too many open files" log entries were environmental (host fd limit), not a property of the submission.
- Axioms: `lake env lean Axioms.lean` prints `[propext, Classical.choice, Quot.sound]` for both `C751.conjecture751_false` and `C751.conjecture751_false_Cp`, matching `verification/axioms.txt`. Supplementary audit: `both_directions_fail`, `fatouSet_sq`, `not_equicontinuousAt_lin` also only the standard three. No `sorry`/`native_decide`/`admit`/`unsafe`/`extern`/`implemented_by`/declared `axiom`.
- Aux code: `verification/` = `SHA256SUMS.txt`, `axioms.txt`, `build.txt`; every hash reproduces byte-exactly after LF→CRLF normalization; `axioms.txt`/`build.txt` match my independent rerun.
- Metadata: `metadata.csv` lists 00000000751 as unsolved; no solution folder on `main`.

## Semantic audit

The conjecture asserts, for iterations of rational functions over Q_p, that the Fatou set is completely invariant and open and that the Julia set is nonempty exactly for degree ≥ 2 ("a complex-p parallel structure"). The submission formalizes the classical non-archimedean setup: ℙ¹(K) as an inductive type with the chordal metric ρ(z,w) = ‖z−w‖/(max(1,‖z‖)max(1,‖w‖)) of Benedetto–Lee (quoted with source; the metric-space structure, including all triangle-inequality cases, is proved in Lean), the action of Mathlib `RatFunc K` on ℙ¹ through reduced numerator/denominator with degree max(deg num, deg den), the Fatou set as the locus of equicontinuity of the iterates for the chordal metric, and three standard readings of the Julia set: complement of the Fatou set, points of non-equicontinuity, and closure of repelling periodic points. The garbled phrase "field of uniformly rational functions" is handled honestly: the submission reads "uniformly" as the uniform (equicontinuity) condition defining the Fatou set, states its reading explicitly, and refutes the biconditional — which is the substantive, checkable part of the conjecture — under every reading.

Both directions of the biconditional fail, with explicit rational functions over Q_p. Degree 2: z ↦ z² satisfies ρ(x²,y²) ≤ ρ(x,y) on all of ℙ¹ over any nontrivially normed ultrametric field, because ‖x²−y²‖ = ‖(x−y)(x+y)‖ ≤ ‖x−y‖·max(‖x‖,‖y‖) ≤ ‖x−y‖·M(x)M(y) while M(x²) = M(x)²; all iterates are 1-Lipschitz, so the family is uniformly equicontinuous, Fatou = ℙ¹, and the Julia sets (J1), (J2) are empty. For (J3), a periodic point z of z² has ‖z‖ ≤ 1 and multiplier ‖2ⁿ z^{2ⁿ−1}‖ ≤ 1 (ultrametric bound on integers; at ∞ the conjugate w ↦ w^{2ⁿ} has derivative 0 at 0), so no periodic point is repelling and (J3) is empty too. Thus deg = 2 with empty Julia set. Degree 1: z ↦ z/p has 0 as a fixed point with multiplier p⁻¹ of norm p > 1, and the points 2ⁿ (i.e. pⁿ) tend to 0 while their n-th iterates equal 1 at chordal distance 1 from 0, so the iterates are not equicontinuous at 0; 0 lies in (J1), (J2), and (J3). Thus deg = 1 with nonempty Julia set. Both counterexamples are instantiated over Q_p for every prime p and over C_p (with ‖p‖_{C_p} = ‖p⟩_{Q_p} proved via Mathlib's norm extension lemma).

The mathematics is correct and consistent with the known non-archimedean phenomenon (the report quotes Wikipedia's Arithmetic dynamics: "in the nonarchimedean setting, the Fatou set is always nonempty, but the Julia set may be empty"). I verified numerically over Q_2: the chordal Lipschitz ratio of z² never exceeded 1 on 20000 random rational pairs, and the sequence ρ(pⁿ, 0) → 0 with n-th iterates at distance 1 reproduces the non-equicontinuity exactly as proved. Quantifier structure is faithful: the formalized `Conjecture J` is the conjunction of openness/complete-invariance (of the complement of J, i.e. the Fatou set) with the biconditional (J nonempty ↔ 2 ≤ deg), universally quantified over rational functions of degree ≥ 1 — a restriction strictly favoring the conjecture — and the disproof exhibits, for each reading, concrete maps satisfying the hypotheses that violate the biconditional in both directions. The submission honestly declares scope limits (Berkovich line not treated; clause (A) not examined, which is immaterial since clause (B) fails). No toy surrogate: the counterexamples live in Q_p(z), the conjecture's own setting.

## Issues found

None blocking. (SHA256SUMS mismatches are CRLF→LF normalization artifacts, reconciled byte-exactly. The report reuses definitions from the author's package for conjecture 00000000745, disclosed with license note.)

## Verdict

APPROVED. A decisive, faithful disproof: over Q_p (and C_p), the degree-2 map z ↦ z² has empty Julia set under all three standard readings (chordal 1-Lipschitzness forces equicontinuity everywhere), while the degree-1 map z ↦ z/p has a nonempty Julia set (repelling fixed point 0), so the conjectured biconditional "Julia nonempty iff degree ≥ 2" fails in both directions for every prime p. Build, axioms, report, and auxiliary verification files all check out, and the analysis was independently confirmed numerically.
