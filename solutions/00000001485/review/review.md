# Solution Review — Conjecture 00000001485 (PR 731)

**Submission:** Jackmeson1 — `solutions/00000001485/Jackmeson1_submission_20261005171904`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- Official conjecture `conjectures/00000001485.md` read in full (English + Chinese). Shipped `conjecture.md` is **byte-identical** to the official file (diff clean).
- LaTeX: full `proof.tex` (243 lines) read. Independently rebuilt with `latexmk -pdf -interaction=nonstopmode` in a scratch dir — build succeeds (4 pages). Shipped vs rebuilt PDF text compared with pypdf after normalization: ≥ 99.4% character-stream similarity; all differences are math-glyph extraction artifacts (radical/absolute-value/∏ symbols extracted differently by the two font subsets), no content difference.
- Lean build: `lake build` re-run in the extracted project — **Build completed successfully (8708 jobs), zero errors, no warnings of substance**. Toolchain Lean 4.33.1, Mathlib v4.33.1 (pool prebuilt rev 0df444a360), `.lake/packages` symlinked to the assigned pool.
- Axioms: fresh `lake env lean Check.lean` audit printing axioms for **every** decisive theorem (`conjecture_00000001485_false`, `A_hyperbolic`, `fix_cat`, `radius_le_half`, `hasProd_zeta`, `coeff_zeta_ge`, `fix_le_orbits`, `card_ker_tmap`, `flow_periodic_iff`) reports exactly `[propext, Classical.choice, Quot.sound]` in all cases. Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom`: only English prose hits in README/SEMANTIC_REVIEW/proof.tex; none in Lean code. `decide` is used only for 2×2 integer matrix identities (AA⁻¹ = I, A² = 3A−I, det A = 1, traces), which is legitimate.
- Aux code: `verification/build.txt` matches my fresh rebuild (same 8708-job success); `verification/axioms.txt` matches my fresh axiom output. `SHA256SUMS.txt` verifies for 12 of 14 files; the two failures (`conjecture.md`, `lean/Conjecture1485/Basic.lean`) were computed on CRLF (pre-git-normalization) variants — the recorded digests match the CRLF versions of exactly these files, and both files were separately verified intact against the PR ref and the official conjecture. Non-blocking.
- Metadata: `metadata.csv` lists 00000001485 as `proven=false, disproven=false` (unsolved); no solution folder for this conjecture exists on the main branch, consistent with the README eligibility statement.

## Semantic audit

The conjecture defines the zeta function of a suspension of an invertible map as the generating function ζ(z) = ∏(1−z^p)⁻¹ of its periodic counts, and claims that **for every hyperbolic suspension** ζ has radius of convergence 1 with singular set on the unit circle exactly the roots of unity, and that no hyperbolic suspension has radius > 1. This is a conjunction; the submission refutes the first ("for every") clause, which suffices.

The submission instantiates the conjecture's own objects, not a surrogate: T² = ℝ²/ℤ² is the actual quotient group in Lean (`Torus`), Arnold's cat map A = [[2,1],[1,1]] is an actual automorphism of it (`cat`), hyperbolicity is proved by the standard criterion for toral automorphisms (det a unit; no complex eigenvalue of modulus 1 — `A_hyperbolic`), and the unit-roof suspension (mapping torus) with its time-translation flow is constructed (`Suspension`, `flow`). The key faithfulness link is proved in Lean, not asserted: `flow_periodic_iff` shows φ_s[x,t] = [x,t] (s > 0) iff s is a positive integer n with catⁿx = x, so the closed orbits and periods of the suspension flow are exactly the periodic orbits and periods of the base map — hence the suspension's Euler product is the product over the cat map's orbits that is analyzed. A cat-map suspension is the textbook example of a hyperbolic (Anosov) suspension, so the counterexample satisfies the hypothesis "hyperbolic suspension"; refuting the universal claim on this subclass is a valid refutation of the full claim.

The mathematics is complete and correct. For every n ≥ 1 the periodic count is proved exactly: Fix(catⁿ) = ker tmap(Aⁿ−I) has |det(Aⁿ−I)| elements (`card_ker_tmap` via Mathlib's Smith-normal-form index theorem), and det(Aⁿ−I) = 2 − tr(Aⁿ) ≤ −(2ⁿ−1) by the trace recursion t_{n+2} = 3t_{n+1} − t_n. The Euler product is proved to converge unconditionally in ℝ⟦z⟧ (`hasProd_zeta`), each orbit contributing its own factor — the standard reading of ∏(1−z^p)⁻¹ as a product over periodic orbits; the alternative "product over the set of period values" is explicitly declared out of scope (it encodes no periodic counts and is not the conjecture's definition). Since ζ_k ≥ #{orbits of period dividing k} ≥ #Fix(catᵏ)/k ≥ (2ᵏ−1)/k, the coefficient growth forces `FormalMultilinearSeries.radius` ≤ 1/2 (`radius_le_half`), proved rigorously via the norm bound on the tail of a convergent power series. Numerical sanity check: #Fix(catⁿ) for n = 1..7 is 1, 5, 16, 45, 121, 320, 841, matching |det(Aⁿ−I)| and ≥ 2ⁿ−1; the true radius is 1/λ₊ = (3−√5)/2 ≈ 0.382 < 1, consistent with the general fact that the radius equals e^{−topological entropy} < 1 for positive-entropy hyperbolic suspensions. So "radius = 1" is genuinely false, and radius ≤ 1/2 also trivially satisfies the "no radius > 1" clause. The exact radius (3−√5)/2 is presented in the paper as extra information beyond the formalized bound, correctly labeled.

Scope disclosures are honest: the singular-set clause is not formalized (with a correct prose remark that the roots of unity are not closed while the non-continuation set on the circle of convergence is); general Anosov flows beyond the toral subclass are not formalized. Neither weakens the refutation of the "for every" clause.

## Issues found

None blocking. (Cosmetic: the two SHA256SUMS.txt entries mentioned above reflect CRLF pre-normalization digests; contents verified intact.)

## Verdict

APPROVED. This is a faithful, complete, machine-checked disproof of the radius-1 clause of conjecture 00000001485 by the canonical counterexample (the cat-map suspension), with every object — torus, hyperbolic automorphism, suspension flow, orbit-period correspondence, convergent Euler product, exact periodic counts, and the radius bound — formalized in Lean/Mathlib, zero build errors, and only the three standard axioms. The conjunction fails; the submission proves exactly what it claims.
