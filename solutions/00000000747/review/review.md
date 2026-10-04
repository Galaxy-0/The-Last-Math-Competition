# Solution Review — Conjecture 00000000747 (PR 425)

**Submission:** C0ldSmi1e — `C0ldSmi1e_submission_20261004070740`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-04

## Checklist results

- **Eligibility and prior submission.** The three-dot diff from the supplied clean base adds only the correctly named personal submission folder. Base metadata again marks conjecture 00000000747 unsolved after the maintainer removed PR 35. I independently inspected old commit `5daa67497ec88d9d37f1c63e407e4f6b6d3a7267` and removal commit `541cf4fbc7aef3e17085577f6403c11c09f31fe1`. The old Lean final theorem was only congruences modulo `5^8`, `Fin 5`, and one finite lifting step, with no `Z_5` object. The new PR description and `PRIOR_SUBMISSION.md` accurately account for that formalization gap and also identify the old report's incorrect `p^n` count of p-adic roots of `X^{p^n}-X`; the correct count is `p` for every positive `n`. This satisfies the corrective-submission rule.
- **Official statement.** The submitted `conjecture.md` is byte-identical to `conjectures/00000000747.md`.
- **LaTeX and PDF.** I read the complete three-page report, including the scope discussion, prior-submission correction, formalization section, and references. A fresh `latexmk -pdf` build succeeded (exit 0; 3 pages). Text extraction and Ghostscript page rendering confirmed the shipped and fresh reports have the same content and section order, aside from compiler/spacing/ligature extraction differences. No auxiliary numerical program is used or required.
- **Lean.** After preseeding the official Mathlib cache with `/tmp/preseed_mathlib_cache.sh`, a fresh `lake build` completed successfully. Direct strict replay of `Conjecture747.lean` and `Check.lean`, with warnings treated as errors, both exited 0. Eight central audits report exactly `[propext, Classical.choice, Quot.sound]`.
- **Forbidden-content scan.** No submitted `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `skipKernelTC`, or trust override occurs. The only “axiom” lines are legitimate `#print axioms` audits. Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned.

## Semantic audit

The official statement concerns iterative fixed points of `x ↦ x^p` in the p-adic integers for primes `p≥5`. Lean uses Mathlib's actual `PadicInt p` type (not `Fin`, `ℕ` residues, or a modulus-only surrogate). Its `powerMap p x` is literally `x^p`, and `iterativeFixed` requires a positive natural iterate of that actual function to fix `x`.

For every prime `p≥5`, `p` is odd. Therefore in the characteristic-zero ring `ℤ_p`,

`(-1)^p = -1`.

Moreover, once `-1` is fixed, every further iterate fixes it; Lean proves this using `Function.iterate` for every natural `n`, then instantiates the positive iterate `n=1`. Since `ℤ_p` has characteristic zero, `-1` is distinct from both `0` and `1`. Thus for `p=5` (indeed for every allowed prime), there is an actual p-adic point outside `{0,1}` fixed by the map and every positive iterate.

This directly negates the universal claim. The submission proves two final theorems: `not_directFixedPointClaim`, for ordinary fixed points, and the stronger `conjecture747_disproof`, for the positive-iterate interpretation. The formal predicates quantify over every prime at least five and every p-adic integer. The local prime-five instance and the all-prime counterexample are both proved, so the result is non-vacuous.

The parenthetical phrase “superattracting orbits” does not state a derivative-zero condition in either official language. The report transparently says it does not claim that `-1` is superattracting. Even on a derivative-sensitive reading, this does not rescue the stated claim that the fixed points are only 0 and 1: the official proposition itself is a set-membership assertion about iterative fixed points, and `-1` is plainly one. No Hensel theorem, finite residue certificate, or external result is load-bearing here.

The prior-report correction is also mathematically sound: modulo `p`, every residue satisfies `X^{p^n}-X=0`, while the derivative is congruent to `-1`; simple-root Hensel lifting gives exactly one p-adic lift per residue, hence `p` roots, not `p^n`.

## Verdict rationale

This repair fixes the earlier finite-shadow defect by proving the witness in the actual p-adic integer ring. The mathematics is elementary and decisive, the quantifier/domain correspondence is faithful, the stronger all-iterate theorem rules out vacuity, and all independent builds, strict replays, axiom audits, scans, and historical checks pass.

## Disposition

APPROVED — ready for merge (PR 425). No merge action was taken by this reviewer.
