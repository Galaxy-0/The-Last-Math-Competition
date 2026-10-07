# Solution Review — Conjecture 00000002149 (PR 674)

**Submission:** Jackmeson1 — `solutions/00000002149/Jackmeson1_submission_20261005102615`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (English + Chinese); `conjecture.md` byte-identical to the official file.
- **LaTeX report:** read in full; independently rebuilt with `latexmk` — exit 0.
- **PDF match:** normalized text of shipped vs. rebuilt PDFs differs only in glyph-extraction artifacts (è vs. \`e, underscore removals). Content identical.
- **Lean build:** `lake build` succeeded, 8708 jobs, zero errors, zero warnings.
- **Axioms:** independent scratch `Check.lean` for `conjecture_2149_false`: exactly `[propext, Classical.choice, Quot.sound]`.
- **Cheating scan:** clean.
- **Auxiliary code:** none shipped.
- **Semantic audit:** pass (see below).
- **Sources:** the (M1)–(M3) definition and the quoted μ-values match the cited Wikipedia article on the Colin de Verdière invariant; only the submission folder is added; metadata marks the conjecture unsolved.

## Semantic audit

The conjecture asserts μ(Ḡ) ≤ |V| − ω(G) − 1 for every finite simple graph, with equality attained for complete graphs. The submission refutes the inequality on two infinite families, one of which is the very family the conjecture names for tightness.

Family (a): G = K_n. Then Ḡ is edgeless, ω(K_n) = n, and the claimed bound is −1. The matrix M = diag(−1, 0, 1, …, 1) is admissible for Ḡ: (M1) trivial (no edges), (M2) exactly one negative eigenvalue (Lean counts negative entries of a diagonal matrix via `roots_charpoly_eq_eigenvalues`), (M3) MX = 0 with X symmetric, zero diagonal, and vanishing on non-edges forces X = 0 (d_i X_ij = 0 kills off-diagonal entries by symmetry, and X_ii = 0 by hypothesis). For n ≥ 2 the corank is 1, so μ(Ḡ) ≥ 1 > −1; for n = 1 the single entry −1 is admissible, so the admissible set is nonempty and μ ≥ 0 > −1.

Family (b): G edgeless on n ≥ 2 vertices. Then Ḡ = K_n, ω(G) = 1, bound n − 2. The matrix M = −J is admissible for K_n: (M1) all off-diagonal entries −1 < 0; (M3) X must vanish on the diagonal and on every off-diagonal pair, hence X = 0; (M2) M² = −nM forces every eigenvalue in {0, −n} (with eigenvector), and the trace −n forces exactly one eigenvalue equal to −n, so exactly one negative eigenvalue; rank 1 via Mathlib's `rank_eq_card_non_zero_eigs`. Hence μ(K_n) ≥ n − 1 > n − 2. This family also removes any doubt that the failure is a sign-convention artifact: n − 2 ≥ 0 and the excess is positive in any convention.

Faithfulness: the Lean definition is the standard Colin de Verdière parameter — symmetric real matrices, (M1) sign conditions off-diagonal, (M2) exactly one negative eigenvalue counted with multiplicity (Mathlib's `IsHermitian.eigenvalues` lists with multiplicity, matching "multiplicity 1"), (M3) the strong Arnold hypothesis over symmetric X with X_ij = 0 when i = j or M_ij ≠ 0, which equals "i = j or ij ∈ E" by (M1) — the report's equivalence is correct. μ is the supremum of coranks over admissible matrices, and the decisive theorem exhibits explicit admissible matrices whose coranks exceed the claimed bounds, so μ(G) exceeds the bound in the standard ℝ-valued sense as well; the ℕ-valued encoding in Lean cannot mask this because the exhibited lower bounds (1 and n−1) are strictly above the claimed bounds (−1 and n−2) in the actual integer order. I verified the classical values agree: μ(K_n) = n−1 and μ(edgeless) = 0/1 (n = 1 / n ≥ 2).

Sanity check: for n = 3, family (b) gives bound 1 vs μ(K₃) ≥ 2 — indeed the 3×3 matrix −J has eigenvalues −3, 0, 0 ✓.

## Issues found

- Minor: μ is ℕ-valued in Lean (standard convention sets μ(K₀) = −1); the report flags this and the explicit-corank lower bounds make the refutation convention-independent.

## Verdict

APPROVED. Two explicit, fully formalized infinite counterexample families (including the conjecture's own tightness example) refute the bound with the standard definition; build and independent axiom audit clean.
