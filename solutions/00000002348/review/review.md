# Solution Review — Conjecture 00000002348 (PR 697)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005124552`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (`conjectures/00000002348.md`, bilingual). Shipped `conjecture.md` is **byte-identical** to the official file (`diff` clean). The entry for `conjecture.md` in the submission's `verification/SHA256SUMS.txt` is stale (hash of an earlier copy); the shipped copy matches the official file.
- **LaTeX rebuild:** `latexmk` from the shipped `proof.tex` in a scratch dir, exit 0. **PDF comparison:** content matches; only cosmetic extraction artifacts (ligatures, math glyphs mapped to control codes by the submitter's font encoding, spacing).
- **lake build:** succeeds with **zero errors and zero warnings** (Lean 4.33.1, Mathlib v4.33.1, pool rev 0df444a360). During review the extracted project was missing the built root module `Conjecture2348.olean`; `lake build Conjecture2348` rebuilt it cleanly (11 s) from the committed sources, so this is an artifact of the extracted build directory, not of the submission (the submitter's own `verification/build.txt` records the full successful build including the root module).
- **Axioms:** fresh `lake env lean Axioms.lean`: `C2348.conjecture_2348_false_exact` and `C2348.conjecture_2348_false_order` depend only on `propext`, `Classical.choice`, `Quot.sound`. Cheat greps (`sorry`, `native_decide`, `admit`, `implemented_by`, `extern`, `unsafe`, `axiom`) are clean.
- **Aux code:** none (verification folder holds only logs/checksums; its `axioms.txt` matches the fresh run).
- **Metadata:** `metadata.csv` lists 00000002348 as `proven=false, disproven=false` (unsolved).

## Semantic audit

The conjecture states that the expected condition number of the norm matrix of random interpolation on smooth varieties is `m^(−1/2)` (`m` the sample count, a negative half power), the expectation arising from a logarithmic-potential integral of the determinant. The submission refutes both defensible readings of "is `m^(−1/2)`": the exact reading `E[κ] = m^(−1/2)` and the order reading `E[κ] ≤ C·m^(−1/2)` eventually for some constant `C` (which subsumes `= C·m^(−1/2)`, `Θ(m^(−1/2))`, `O(m^(−1/2))` and `∼ c·m^(−1/2)`). The report explicitly scopes what is not refuted (`m = 1`, where `m^(−1/2) = 1`, and non-literal rewordings that change the quantity), which is the right level of honesty.

The formalization is faithful. The decisive theorems quantify over **every** probability space and **every** random matrix, with matrix sizes allowed to depend on `m`; the conjecture's norm matrix is a random matrix whatever its precise construction (variety, sampling law, basis), so the universal statement subsumes every instantiation of the conjecture's objects — there is no toy instance and no assumed hypothesis. Both standard condition numbers are formalized on real matrices: `condNum A = ‖A‖·‖A⁻¹‖` in a general nontrivial normed ring (instantiated with Mathlib's L2 operator norm, with `condNum_matrix_eq` unfolding it to `‖A‖₂‖A⁻¹‖₂` for `det A ≠ 0` and `⊤` for `det A = 0`), and `svCond A = σ_max/σ_min` for rectangular matrices acting on Euclidean spaces (`⊤` when `σ_min = 0`). The expectation is the lower Lebesgue integral `∫⁻` on `ℝ≥0∞`, so no measurability or integrability hypothesis is smuggled in; a Bochner-integral variant for a.e.-invertible integrable families is included.

The mathematics is airtight. `κ(A) = ‖A‖‖A⁻¹‖ ≥ ‖A·A⁻¹‖ = ‖1‖ ≥ 1` by submultiplicativity and `‖1‖ ≥ 1` for `1 ≠ 0`; `σ_min ≤ ‖Ae₁‖ ≤ σ_max` gives `κ₂ ≥ 1`; a pointwise `≥ 1` random variable has expectation `≥ 1` under any probability measure; and `m^(−1/2) < 1` for `m ≥ 2`. For the order reading, choosing `m > max(M, C²)` makes `C·m^(−1/2) = C/√m < 1 ≤ E[κ]`, so no eventual bound with any real `C` can hold. I verified the inequality chain by hand and numerically; the Lean proofs compile against Mathlib and the axiom dependencies are the standard three. The negation proved is exactly the negation of the conjecture as written (for either reading), and the counterfactual hypothesis `ringKrullDim`-style assumptions are absent because none are needed — the obstruction is universal.

## Issues found

None blocking. (Non-blocking: stale `conjecture.md` entry in `verification/SHA256SUMS.txt`; missing root-module olean in the extracted build directory, rebuilt successfully during review.)

## Verdict

APPROVED. A universal, hypothesis-free obstruction (`E[κ] ≥ 1 > m^(−1/2)`) formalized on the actual objects — real matrices, spectral and singular-value condition numbers, Lebesgue expectation — refuting the conjecture exactly as written under both the exact and the order-of-magnitude reading. Clean build, standard axioms only, and a report whose scope claims match the Lean theorems precisely.
