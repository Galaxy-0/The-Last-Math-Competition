# Solution Review — Conjecture 00000001128 (PR 696)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005124131`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (`conjectures/00000001128.md`, bilingual). Shipped `conjecture.md` is **byte-identical** to the official file (`diff` clean). Note: the entry for `conjecture.md` in the submission's own `verification/SHA256SUMS.txt` does not match the shipped file — the shipped copy matches the official file exactly, so the recorded hash is stale, not a content divergence.
- **LaTeX rebuild:** `latexmk -pdf -interaction=nonstopmode` in a scratch dir from the shipped `proof.tex`, exit 0. **PDF comparison** (pypdf, whitespace-normalized): content matches; differences are exclusively glyph/ligature extraction artifacts from the submitter's TeX fonts (e.g. `≥`, `−`, `∈`, `⊥` extracted as control chars; `ﬀ`/`ff`), which is cosmetic.
- **lake build:** succeeds with **zero errors and zero warnings** (Lean 4.33.1, Mathlib v4.33.1, pool rev 0df444a360), 8708 jobs.
- **Axioms:** fresh `lake env lean Axioms.lean`: `C1128.disproof` and `C1128.disproof_321_avoiding` depend only on `propext`, `Classical.choice`, `Quot.sound`. Grep for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/`axiom` is clean.
- **Aux code:** none (verification folder contains only build/axiom logs and checksums; shipped axiom output matches the fresh run).
- **Metadata:** `metadata.csv` lists 00000001128 as `proven=false, disproven=false` (unsolved).

## Semantic audit

The conjecture asserts that the maximal monomial coefficient of the degree-`j` part of the Schubert polynomial, `M(w,j)`, equals `min(j, ℓ(w), ⌈ℓ(w)/2⌉)! · C(w)` with `C(w)` a lattice-path count, with a product formula for `C(w)` on 321-avoiding permutations and, in particular, a claim about `M(w, ℓ(w))`. The submission refutes the universal equality, covering both natural readings: (R1) for all permutations `w`, via `w = 321 = w₀ ∈ S₃`; (R2) for 321-avoiding permutations, via `w = 4123 ∈ S₄`. In both cases `ℓ(w) = 3` and `M = 1`, while the conjectured right side is `min(3,3,2)!·C = 2C`, and the Lean theorems exclude every integer `C`, a fortiori every nonnegative lattice-path count. The refutation lands exactly at `j = ℓ(w)`, the case the conjecture text itself singles out; the product-formula and increasing-subsequence clauses are not needed to kill the main identity and are not separately addressed, which the report states honestly.

The formalization is faithful to the conjecture's own objects. The divided difference `∂_i` is the exact quotient `(P − s_iP)/(x_i − x_{i+1})` in genuine `MvPolynomial (Fin (n+1)) ℤ`, with divisibility proved for every `P` by induction and uniqueness from the domain property. Schubert polynomials are captured by the Lascoux–Schützenberger characterization (`IsSchubert`: `𝔖_{w₀} = x^δ`, `∂_i𝔖_w = 𝔖_{ws_i}` on descents, `0` on ascents), which is the standard recursive definition. Decisively, the theorems are not stated for a hardcoded polynomial: `disproof` and `disproof_321_avoiding` quantify over **every** family `S` satisfying `IsSchubert`, so no uniqueness theorem is needed and there is no toy surrogate — the true Schubert polynomials satisfy the characterization, hence the refutation applies to them. The `S₃` and `S₄` explicit families are verified in Lean against all conditions of the characterization (24 × 3 cases for `S₄`), so the setting is non-vacuous; `𝔖₄₁₂₃ = x₀³` is derived from `w₀ = 4321` by the descent chain `4321 → 4312 → 4132 → 4123`, exactly the divided-difference construction the earlier rejection (orionsheep PR #201) demanded.

The mathematics is correct. I checked it independently: `𝔖_{w₀} = x₁²x₂` on `S₃` is the defining base case, with single degree-3 monomial of coefficient 1; `∂₃∂₂∂₃(x₁³x₂²x₃) = x₁³` computed by hand matches; `4123 = [4,1,2,3]` has inversions {(1,2),(1,3),(1,4)}, so `ℓ = 3`, and no decreasing subsequence of length 3, so it is 321-avoiding. The `S₃`/`S₄` polynomial tables I spot-checked by hand (123, 213, 132, 231, 312, and the zero-row/`x₀³` entries of `S₄`) satisfy the recursion. The bottom-`WithBot` convention for `maxCoeff` is harmless: both witnesses have nonempty degree-3 parts. The counterexample satisfies every stated hypothesis of the conjecture, and the negation proved is exactly the negation of the asserted identity (the Lean statement is even stronger, excluding all integer `C`).

## Issues found

None blocking. (Non-blocking: the `verification/SHA256SUMS.txt` entry for `conjecture.md` is stale — the shipped file is byte-identical to the official conjecture, which is what matters.)

## Verdict

APPROVED. This is a faithful and decisive disproof of conjecture 00000001128 as written: real Schubert polynomials via the standard Lascoux–Schützenberger characterization with proved divided differences, a counterexample at `w = 321, j = 3` (and a 321-avoiding one at `4123 ∈ S₄`) satisfying all hypotheses, clean build, standard axioms only, and a report that matches the Lean code. Both readings of the quantifier structure are covered, so no charitable reinterpretation survives.
