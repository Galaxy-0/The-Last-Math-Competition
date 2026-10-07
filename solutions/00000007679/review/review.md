# Solution Review — Conjecture 00000007679 (PR 673)

**Submission:** Jackmeson1 — `solutions/00000007679/Jackmeson1_submission_20261005102202`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (English + Chinese); `conjecture.md` byte-identical to the official file.
- **LaTeX report:** read in full; independently rebuilt with `latexmk` — exit 0.
- **PDF match:** normalized text of shipped vs. rebuilt PDFs differs only in math-glyph extraction artifacts (∏→q, ∑→p, −, q-binomial brackets, subscripts). Content identical.
- **Lean build:** `lake build` succeeded, 8708 jobs, zero errors, zero warnings.
- **Axioms:** independent scratch `Check.lean` for `conjecture_7679_false`, `S_eq_prod`, `zeroSet_eq`, `jordan_not_subset_real`: all exactly `[propext, Classical.choice, Quot.sound]`.
- **Cheating scan:** clean.
- **Auxiliary code:** none shipped; I additionally verified numerically (exact rational arithmetic) that S_N(z) equals ∏_{k<N}(1 − z q^k) with zeros q^{−k} for q = 1/2, 3/4 and N = 3, 5.
- **Semantic audit:** pass (see below).
- **Sources:** the q-binomial/Cauchy identity, quasicircle and Jordan curve definitions match the cited Wikipedia pages; only the submission folder is added; metadata marks the conjecture unsolved.

## Semantic audit

The conjecture claims that for each 0 < q < 1 the zero set of S_N(z) = Σ_{n≤N} (−1)ⁿ q^{n(n−1)/2} [N choose n]_q zⁿ converges to a quasicircle Jordan curve with envelope controlled by ±q^{−N} and conformal scaling constant 1 + 2q. The submission proves the defining identity S_N(z) = ∏_{k=0}^{N−1}(1 − z q^k) — the finite q-binomial (Cauchy binomial) theorem, reproved in Lean via the q-Pascal rule — so Z_N = {q^{−k} : 0 ≤ k < N} is a finite subset of the positive real axis for every N. Consequently the union of all zero sets is contained in the real line, and so is the union of any real-affine normalization a_N Z_N + b_N. Since no Jordan curve is contained in the real line (the Lean proves this by an intermediate-value argument on Re γ(e^{it})), no Jordan curve — quasicircle or otherwise — can be the Hausdorff limit, nor even satisfy the weakest convergence requirement Γ ⊆ closure(∪_N Z_N). The envelope and 1 + 2q clauses concern a curve that does not exist, so the conjectured conjunction fails.

Faithfulness: the definition of S_N is taken literally from the conjecture (Gaussian binomial via q-Pochhammer ratios, vanishing for n > N, exponent n(n−1)/2 in ℕ); the limit notion is formalized at its weakest (Γ ⊆ closure of the union, plus Mathlib's extended Hausdorff edist for reading (H)) — both are refuted, and any standard set-convergence notion in ℂ implies the cluster-point condition (W). The reduction allows arbitrary real sequences a_N, b_N, which covers the rescaling z ↦ q^N z suggested by the points ±q^{−N} (q^N is real), so the refutation is robust to the only normalization the conjecture's own control-points language suggests. Complex (non-real) normalizations and spherical convergence are honestly flagged as not treated; neither is stated by the text.

The supporting lemmas are all proved, not assumed: q-Pascal (including the k ≥ N boundary cases), the recursion S_{N+1} = (1 − z q^N)S_N (the coefficient identity (m+1)m/2 + (N−m) = N + m(m−1)/2 is exactly right), injectivity of the neighbor description in the product formula, and the IVT argument for Jordan curves (f(0) ≠ f(π), a value between them is taken on both arcs, contradicting injectivity).

Sanity check: q = 1/2, N = 5: S_5(z) = ∏_{k<5}(1 − z 2^{−k}), zeros 1, 2, 4, 8, 16 — real, positive, receding like q^{−k}; the "quasicircle" would have to be a subset of ℝ, impossible for a Jordan curve.

## Issues found

- None material. The genuinely stated claim (convergence of the zero sets, unnormalized or real-normalized) is refuted in its weakest form; non-stated readings (complex normalization, Riemann sphere) are transparently disclosed.

## Verdict

APPROVED. An exact identity (finite q-binomial theorem) reduces the zero sets to positive real points, and the Lean proves no Jordan curve can be their limit under Hausdorff or weaker convergence; definitions are literal, the build and independent axiom audit are clean.
