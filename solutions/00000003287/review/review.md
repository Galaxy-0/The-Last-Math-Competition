# Solution Review — Conjecture 00000003287 (PR 762)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005212842`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000003287.md` read in full (bilingual); shipped `conjecture.md` is byte-identical to it (`diff` clean). Note: the shipped `verification/SHA256SUMS.txt` lists three stale hashes (`conjecture.md`, `lean/Conjecture3287/Basic.lean`, `proof.tex`); all three files were verified correct by direct diff/read/rebuild — a bookkeeping artifact only.
- LaTeX rebuild: `latexmk -pdf` in a scratch dir succeeds; shipped and rebuilt `proof.pdf` match after whitespace/ligature normalization; remaining differences are font glyph-extraction artifacts only (∫/∏/∈/≠/⟨⟩ extracted at different Unicode points, `_` handling) — cosmetic.
- Lean build: `lake build` succeeds with zero errors and zero warnings (Lean 4.33.1, Mathlib v4.33.1, pool rev `0df444a360`, ~104 s).
- Axioms: independent `lake env lean Check.lean` with `#print axioms` for ALL eleven theorems (`gauss_christoffel`, `three_term_recurrence`, `exists_monicOrthogonal`, `monicOrthogonal_unique`, `roots_card_eq`, `roots_nodup`, `exact_of_roots`, `weight_pos`, `not_exact_two_mul`, `precision_le`, `nodes_eq`) — each depends only on `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `native_decide`, `extern`, `unsafe`, or declared `axiom`.
- Aux code: `verification/build.txt` and `verification/axioms.txt` match the reviewer's fresh rebuild and axiom output; no runnable scripts shipped (none needed).
- Metadata: `metadata.csv` lists 00000003287 as unsolved.

## Semantic audit

The conjecture is the classical Gauss–Christoffel theorem: the nodes of Gauss quadrature are polynomial zeros (the zeros of the degree-n orthogonal polynomial), and the algebraic precision of the quadrature is the maximum 2n−1. The submission proves exactly this, in the general measure setting: μ on ℝ with `FiniteMoments` (x ↦ x^k integrable for all k, so μ is finite and every polynomial is integrable) and `NotFinitelySupported` (μ gives positive mass to the complement of every finite set — the standard "infinitely many points of growth" positive-definiteness condition). The lemma `notFinitelySupported_withDensity` shows μ = w(x)dx satisfies the support condition whenever w is not a.e. zero, so the conjecture's "weight functions" are covered; the moment condition is kept as an explicit hypothesis, as it must be.

The decisive theorem `gauss_christoffel` matches the conjecture's quantifier structure: for every such μ and every n ≥ 1, (i) the monic orthogonal p_n exists and is unique; (ii) p_n has n real, simple zeros; (iii) the Gauss rule — nodes the increasing enumeration of the zeros, weights the Christoffel numbers λ_i = ∫ℓ_i dμ — has positive weights, is exact up to degree 2n−1, is not exact at 2n, and has `algebraicPrecision` exactly 2n−1; (iv) conversely, every n-node rule exact up to 2n−1 has p_n = ∏(X − x_i), i.e. its nodes are exactly the zeros of p_n; (v) no n-node rule with arbitrary nodes and weights is exact at any degree above 2n−1, so the maximum precision is 2n−1. Both halves of the written conjecture ("nodes are polynomial zeros", "precision is the maximum 2n−1") are thus established, with the maximality made precise in the only sensible way (no rule can exceed it, the Gauss rule attains it; the sSup is computed via a greatest element, so no convention artifact arises). `three_term_recurrence` additionally realizes the Definition's "three-term recurrence families": p_{n+2} = (X−a)p_{n+1} − b·p_n with b > 0.

The mathematics is the classical one and the reviewer verified each step and re-derived it independently: positivity of the moment functional on nonzero nonnegative polynomials (via infinite support); existence by finite-dimensional linear algebra (the moment matrix on degree-<n polynomials is positive definite, so X^n − (best approximation) is orthogonal); uniqueness from I((p−q)²) = 0; the n real simple zeros from "no nonzero s of degree < n has p_n·s ≥ 0" (IVT for the root-free factor, multiplicity-2 factor (X−a)²s² otherwise); exactness to 2n−1 by division f = p_n·d + r with both d and r of degree < n, orthogonality killing ∫p_n d, and Lagrange interpolation of r; maximality from ∫ω² > 0 vs. rule value 0 for ω = ∏(X − x_i); node uniqueness from ω being monic orthogonal. A numerical check (Legendre, n = 2: p₂ = x² − 1/3, nodes ±1/√3, weights 1, exact through degree 3, ∫x⁴ = 2/5 ≠ 2/9 = rule value at degree 4) agrees. Favard's converse (recurrence without a weight) is not formalized, disclosed in README/tex, and not needed for the weight-based quadrature claim; the restriction n ≥ 1 is appropriate.

## Issues found

None blocking. Cosmetic: three stale hashes in `verification/SHA256SUMS.txt` (the files themselves are correct, as verified by independent rebuild, read, and diff against the official conjecture).

## Verdict

APPROVED. A complete, faithful, fully machine-checked proof of the conjecture as written — the classical Gauss–Christoffel theorem: the Gauss nodes are exactly the zeros of the degree-n orthogonal polynomial and the algebraic precision 2n−1 is attained by the Gauss rule and is maximal among all n-node rules. The formalization uses the conjecture's own objects (orthogonal polynomial families of weight functions/measures, quadrature nodes and weights, algebraic precision), the build is clean with only the three permitted axioms, and report and Lean agree throughout.
