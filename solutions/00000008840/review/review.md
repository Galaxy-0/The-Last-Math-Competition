# Solution Review — Conjecture 00000008840 (PR 569)

**Submission:** ziangni-sys — `ziangni-sys_submission_20261004204900`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results
- Official bilingual conjecture `conjectures/00000008840.md` read in full: the graph version of Minty's theorem is claimed to "always hold" for monotone inclusions under splitting, with the zero set closed convex and given by fixed points of the graph reflection. No maximal-monotonicity hypothesis appears in either language; no SOURCE.md in the submission (absent, not failed).
- LaTeX: `report.tex` rebuilt from scratch with `latexmk -pdf` (clean, 2 pages). Because pypdf maps the Tectonic math fonts poorly (braces→f/g, angle brackets→h/i, ∞→1), the PDF comparison was redone with MuPDF text extraction: **content identical**, the only residual differences being fi/fl ligature codepoints; the shipped PDF verifiably displays the full correct mathematics (−1 for x ≤ 0, (−∞,−1] ∪ (0,1) ∪ [2,∞) etc.).
- Lean: fresh `lake build`, lean4 v4.19.0, Mathlib pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b` — **0 errors**, one cosmetic linter warning (`tac1 <;> tac2`, Main.lean:72).
- Axioms: `Main.lean` runs `#print axioms` on all eleven results including the final `counterexample`; every one depends only on `[propext, Classical.choice, Quot.sound]`. No `sorry`/`native_decide`/`axiom`/`unsafe`/`admit` anywhere in the submission.
- Auxiliary code: none (README/VERIFICATION prose only).
- Repo metadata: conjecture unsolved; submission claims a disproof.

## Semantic audit
The conjecture asserts, universally for monotone inclusions, that the graph version of Minty's characterization holds and the zero set is closed and convex. The submission's counterexample is the canonical demonstration that monotonicity alone is insufficient: A: ℝ → ℝ with A(x) = −1 on x ≤ 0, 0 on 0 < x < 1, 1 on x ≥ 1. The operator is nondecreasing (full three-region case analysis in Lean via `split_ifs <;> linarith` and `Monotone A`), hence a monotone operator on the real Hilbert space with the genuine inner product (`0 ≤ ⟪x−y, A x − A y⟫` for all x, y), and its graph is a monotone relation with full domain ℝ. The zero set is exactly (0,1) — proved as literal equality with `Set.Ioo 0 1` — with closure [0,1] via Mathlib's order-topology `closure_Ioo`; since 0 lies in the closure but A(0) = −1 ≠ 0, the zero set is not `IsClosed`. That alone refutes the stated closed-convex conjunction (the submission honestly notes convexity holds and the graph-reflection fixed-point clause need not be interpreted once the conjunction is broken). I re-verified every property numerically (monotonicity on a grid, zeros exactly on (0,1), x + A(x) never 0, x·A(x) ≥ 0).

The formalization is faithful: definitions are the actual piecewise function, the actual graph `{p | p.2 = A p.1}`, the actual preimage zero set, Mathlib's real inner product and `IsClosed`; no surrogate notions. The quantifier structure — one everywhere-defined monotone graph whose zero set fails closedness — is exactly the negation of the universal claim as literally stated in both official languages. Beyond the minimum, the submission proves 0 ∉ range(I + A) (values confined to (−∞,−1] ∪ (0,1) ∪ [2,∞)), showing the Minty surjectivity half also cannot hold without maximality, and constructs the explicit proper monotone extension G ∪ {(0,0)} with x·A(x) ≥ 0 verified casewise and (0,0) ∉ G — a clean proof that G is not maximal monotone, so the disproof is fully consistent with the classical Minty theorem it does not challenge. The report and the Lean development agree statement by statement, and the final `counterexample` theorem conjoins full domain, graph monotonicity, non-closedness of the zero set, and the range obstruction.

## Issues found
None blocking. (The shipped Tectonic PDF's symbol fonts confuse pypdf extraction; MuPDF extraction resolves this and confirms identical content. One cosmetic `<;>` linter warning.)

## Verdict
APPROVED. The counterexample is mathematically correct and re-verified independently, the formalization matches the official bilingual text's unqualified universal claim exactly (no maximality hypothesis appears there), the build is clean with only the three standard axioms, and the submission transparently delimits scope, explicitly preserving the valid maximal-monotone Minty theorem.
