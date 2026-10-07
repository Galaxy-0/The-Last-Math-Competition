# Solution Review — Conjecture 00000002805 (PR 702)

**Submission:** Jackmeson1 — `Jackmeson1_submission_20261005130101`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read; copy check.** Read `conjectures/00000002805.md` in full (bilingual). Shipped `conjecture.md` is byte-identical to it (`diff` clean).
- **LaTeX rebuild + PDF comparison.** Fresh `latexmk -pdf` build: exit 0, 3 pages matching the shipped PDF. Extraction differences are only math-glyph/font-substitution artifacts (e.g. `(‖ω‖_H ≤ 1)` extracting as `fkkh1g`, spacing around quotes); rendered pages are content-identical. Cosmetic.
- **Lean build.** `lake build` from scratch: zero errors, 8708 jobs, exit 0 (toolchain `leanprover/lean4:v4.33.1`, Mathlib v4.33.1, pool rev 0df444a360). Incremental rebuild of the extracted tree confirms shipped sources match the built state.
- **Axioms.** No `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, or declared `axiom`. The shipped `axioms.txt` prints only `schilder_rigidity_false`, so I ran an independent scratch check for every decisive theorem: `schilder_rigidity_false`, `schilder_rigidity_false_open`, `schilderRate_straightPath`, `cmNormSq_straightPath` — all `[propext, Classical.choice, Quot.sound]`, only the standard three.
- **Aux code.** `Axioms.lean` output matches the report's claim (for the one theorem it prints). Note: `verification/SHA256SUMS.txt` has two stale entries (`conjecture.md`, `lean/Conjecture2805/Basic.lean`) that do not match the shipped files; both verified correct independently.
- **Metadata.** `metadata.csv` lists 00000002805 as unsolved (proven = false, disproven = false); no competing solution folder on main.

## Semantic audit

The conjecture is a conjunction: (i) "Cameron–Martin rigidity of the Schilder rate: the rate function vanishes if and only if the path lies in the Cameron–Martin unit ball", and (ii) a chi-square spectral law on the sphere. The submission refutes (i), which suffices for the conjunction, and — unlike the earlier closed PR #277 — makes no claim about (ii).

The formalization uses the conjecture's own objects, not surrogates. The path space C₀([0,T]; ℝ^d) is continuous paths vanishing at 0; the Cameron–Martin space is the absolutely continuous paths (Mathlib's `AbsolutelyContinuousOnInterval`) whose derivative is in L²; the rate function is I(ω) = ½∫₀ᵀ‖ω̇‖² on absolutely continuous paths and +∞ otherwise, which is precisely the explicit good rate function of Schilder's theorem quoted from the source. Both readings of "unit ball" (closed, open) are formalized and both refuted, for every dimension d ≥ 1 and horizon T > 0. The decisive theorems are ¬∀ω ∈ C₀, (I(ω) = 0 ↔ ω in the ball) — the exact negation of clause (i) — so the quantifier structure matches.

The mathematics is correct and elementary. The straight path ω₀(t) = t·e₀/(2√T) is continuous, starts at 0, is C¹ hence absolutely continuous, with ω̇₀ = e₀/(2√T) ∈ L². Hence ‖ω₀‖²_H = ∫₀ᵀ dt/(4T) = 1/4 < 1, placing it in the open (a fortiori closed) unit ball, while I(ω₀) = ½·¼ = 1/8 ≠ 0. This is exactly as expected: I = ½‖ω‖²_H vanishes only at the zero path, whereas the CM unit ball is the sublevel set {I ≤ ½}, so "vanishes iff in the unit ball" could never hold. The report correctly notes this "what is true" remark without relying on it. I hand-verified the arithmetic and the Lean computations (constant-derivative integral, `Real.volume_Icc`) line up.

This submission also cures the defect of the earlier closed submission, whose "refutation" was vacuous ℕ trivia with no Schilder or Cameron–Martin objects in Lean; here every object of the conjecture's first clause appears in the formalization and the witness is a genuine path in the genuine ball.

## Issues found

- Non-blocking: the shipped `verification/axioms.txt` covers only one of the two main theorems named in the README; the reviewer independently verified the second (`schilder_rigidity_false_open`) and supporting lemmas — all clean.
- Non-blocking: `verification/SHA256SUMS.txt` lists two stale hashes (`conjecture.md`, `lean/Conjecture2805/Basic.lean`); both files verified correct independently. The other entries check out.

## Verdict

APPROVED. The submission refutes the conjecture's first clause with a concrete, faithful counterexample on the conjecture's own objects (real path space, real Cameron–Martin space, the textbook Schilder rate), for both readings of "unit ball" and all d, T; the quantifier structure of the refuted statement is the exact negation of the stated rigidity claim, the mathematics is certain and independently checked, and the Lean development builds cleanly depending only on propext, Classical.choice and Quot.sound.
