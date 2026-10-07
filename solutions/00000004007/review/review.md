# Solution Review — Conjecture 00000004007 (PR 692)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005122242`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture:** read in full (bilingual). The submission's `conjecture.md` is byte-identical to `conjectures/00000004007.md`.
- **LaTeX report:** read in full; rebuilt independently with `latexmk -pdf`; rebuild exited 0.
- **PDF match:** shipped vs rebuilt PDF text agrees after normalization; differences are only math-glyph/ligature extraction artifacts.
- **Lean build:** `lake build` (v4.33.1, Mathlib 0df444a360) exited 0, no errors, no warnings.
- **Axiom audit:** no forbidden keywords; re-ran `lake env lean Axioms.lean`: `Tlmc4007.conjecture_00000004007_false` and `Tlmc4007.fails_at_diagonal` depend only on `[propext, Classical.choice, Quot.sound]`.
- **Auxiliary code:** `verification/axioms.txt` and `build.txt` reproduce my runs; `SHA256SUMS.txt` has a stale `conjecture.md` entry and one stale `Basic.lean` entry (the shipped `Basic.lean` is what builds and audits clean).
- **Semantic audit:** pass (see below).
- **Scope:** the PR adds only `solutions/00000004007/Jackmeson1_submission_20261005122242/`; no existing solution on `main`.

## Semantic audit

The `pVar` definition is the conjecture's, verbatim: the `p`-th root of the supremum over partitions `a = t₀ < … < tₙ = b` of `Σ‖X(tᵢ) − X(tᵢ₋₁)‖^p` (values in `ℝ≥0∞` so the supremum always exists; the counterexample is finite-valued, so this normalization is never load-bearing). The claimed inequality is formalized with `q` a Mathlib `Real.HolderConjugate` of `p` (so `1/p + 1/q = 1`, `q > 1`), matching the conjecture's "conjugate exponent".

The disproof is a one-line idea, executed rigorously: `pVar` is 1-homogeneous (`incrSum_smul`, then `iSup` commutes with multiplication and `rpow` splits), hence at `Y = X`, `‖X + X‖ = ‖2X‖ = 2‖X‖` while the right side is `(‖X‖^q + ‖X‖^q)^{1/q} = 2^{1/q}‖X‖ < 2‖X‖` for every path of finite nonzero `p`-variation, since `1/q < 1`. To show the failure is not vacuous the submission computes `pVar` of `X(t) = t` on `[0,1]` exactly: telescoping plus `Δᵢ^p ≤ Δᵢ` (valid since every increment is in `[0,1]` when `b − a = 1`) gives the upper bound 1, and the two-point partition attains it. So a concrete continuous path violates the inequality with `‖X+X‖ = 2 > 2^{1/q}`. The `p = 1` endpoint (`q = ∞`, right side read as `max`) is handled separately, and two alternative normalizations — the raw supremum without the `p`-th root, and `X + Y` read as concatenation of two paths (where `pVar(t ↦ t)` on `[0,2]` is ≥ 2 against pieces of variation 1) — are refuted as well.

Mathematically the claim is indeed false: any nontrivial homogeneous functional fails a `q`-concave triangle inequality with `q > 1` on the diagonal; the correct inequality for `p`-variation would involve `p`, not its conjugate. I checked the inequality direction and the arithmetic (`2^{1/q} < 2` iff `q > 1`) and the ENNReal manipulation in `fails_at_diagonal` (`2^{1/q}·v < 2v` multiplied by finite nonzero `v`) — all sound. Refuting the inequality refutes the whole conjecture including its "cannot be enlarged" optimality clause.

## Issues found

- Minor hygiene: two stale entries in `verification/SHA256SUMS.txt` (see above); no effect on correctness.
- The report's scope section honestly notes the unaddressed regimes `0 < p < 1` and `p = ∞`; neither is needed since the clause is refuted for every `1 ≤ p < ∞`.

## Verdict

APPROVED. A decisive, faithful, and genuinely formalized disproof (the first for this conjecture with the p-variation actually defined in Lean), with clean build, axioms, and report-to-Lean agreement.
