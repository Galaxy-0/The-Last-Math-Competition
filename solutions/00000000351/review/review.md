# Solution Review — Conjecture 00000000351 (PR 784)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261006003326`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

**Kind:** DISPROOF. **Conjecture:** Dn lattice covering optimal through dimension eight.

## Checklist results

- **Official conjecture.** `conjectures/00000000351.md` read in full (bilingual); the submission's `conjecture.md` copy is byte-identical to it.
- **LaTeX report.** `proof.tex` read in full; rebuilt independently with `latexmk -pdf -interaction=nonstopmode` in a scratch directory (exit 0). Extracted text of shipped and rebuilt PDFs agrees after whitespace normalization; residual differences are font/ToUnicode glyph artifacts only (ligatures, math symbols such as ∑, ‖·‖, ≥), not content.
- **Lean build.** `lake build` with toolchain v4.33.1 / Mathlib `0df444a360` (prebuilt package pool via `.lake/packages` symlink): exit 0, zero errors. No warnings.
- **No cheating.** Grep for `sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, declared `axiom` over all `.lean` files: clean. `#print axioms` re-run independently (`lake env lean Axioms.lean`) for every decisive theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- **Auxiliary code.** `verification/` contains the build log, axiom output and a SHA-256 manifest; all entries verify against the extracted files (matching after CRLF normalization, consistent with the submitter's Windows build environment). Self-reported build/axiom outputs agree with my independent runs. No other executable auxiliary code is shipped.
- **Semantic audit.** Pass; details below.

## Semantic audit

The conjecture asserts (as a conjunction) that the D_n lattices are covering-optimal for dimensions up to eight. The submission refutes the first clause at n = 3: the body-centred cubic lattice `bcc` = ℤ-span{e₁, e₂, (½,½,½)} has covering density ≤ 125π/192, while every similar copy c·φ(D₃) has covering density ≥ 2π/3 — the lower bound from the certified deep hole (1,0,0) at distance ≥ 1 from every point of D₃ (so μ ≥ |c| after scaling), the upper bound from covolume 2|c|³ (basis of determinant 2, |det φ| = 1 for a linear isometry) against covolume(bcc) = ½ with its explicit 5/8-covering. Since 125π/192 ≈ 2.0453 < 2.0944 ≈ 2π/3 strictly, no similar copy of D₃ minimizes covering density among lattices: `not_DCoveringOptimal_three`, hence `conjecture_351_false : ¬ ∀ n ∈ [3,8], DCoveringOptimal n`.

The reading is the standard lattice-covering one (Schürmann–Vallentin's Problem 2.1), the definitions (covering radius as infimum, density = ball volume / covolume, similar copy = c·φ, optimality quantified over all discrete co-compact ℤ-lattices) are faithful, and the counterexample satisfies every stated hypothesis: bcc is a genuine lattice, D₃ = {x ∈ ℤ³ : Σxᵢ even} is the standard even-sum lattice, and the density comparison is over all lattices, not just similar copies. The disproof direction is airtight: an optimality claim is killed by one competitor lattice that is strictly better. The mathematics is also the historically correct one — that BCC beats FCC (= D₃) in ℝ³ is Bambah's classical theorem — and the submission proves everything from scratch rather than citing it.

Numerically I re-verified 125π/192 = 2.04531 < 2π/3 = 2.09440, covolume(bcc) = ½, Θ(D₃) = (4π/3)/2 = 2π/3, and the round-to-{z, z+½} covering argument (squared-distance sum ≤ ¾, so one of the two candidates is within 5/8). The report transparently discloses the one caveat: under the root-system convention that reserves type D_n for n ≥ 4, dimension 3 would be out of range; under the even-sum-lattice convention (the one used by the covering literature and the only one under which 'the D_n lattices' is defined for all n ≤ 8 uniformly), 3 is in range and the literal statement is false. The formalized statement `¬ ∀ n ∈ Finset.Icc 3 8, ...` matches the literal text.

## Issues found

Minor, disclosed in the submission itself: the root-system naming convention (type D_n for n ≥ 4) would place the counterexample dimension outside the intended family; the submission argues, correctly in my view, that the covering-problem reading of 'the D_n lattices' is the intended object and covers n = 3. No other issues.

## Verdict

APPROVED. A clean, explicit, fully machine-checked counterexample showing D₃ is not covering-optimal (BCC strictly better), refuting the conjecture's first clause and with it the conjunction; the convention caveat is disclosed and does not affect the formalized negation of the literal statement.
