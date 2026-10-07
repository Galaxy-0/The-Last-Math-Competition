# Solution Review — Conjecture 00000000125 (PR 741)

**Submission:** Jackmeson1 — `solutions/00000000125/Jackmeson1_submission_20261005194607`
**Reviewer:** independent competition reviewer
**Date:** 2026-10-06

## Checklist results

- **Official conjecture read in full** (English + Chinese) from `conjectures/00000000125.md`: the number of SL₂(F_p) elements whose trace has absolute value a prime is asymptotic to c·p²/log p, with c explicit from a Sato–Tate type density. Shipped `conjecture.md` is **byte-identical** to the official file (`diff` clean).
- **LaTeX rebuild:** independent `latexmk -pdf` from the shipped `proof.tex` succeeds; pypdf comparison (normalized) shows identical content; all differences are glyph-extraction/kerning artifacts of the shipped font subsets (∼/≤/≥/−/∈/{,} extracted as control codes or ASCII stand-ins) — cosmetic.
- **Lean build:** independent `lake build` (Lean `v4.33.1`, Mathlib v4.33.1, pool rev 0df444a360) — **Build completed successfully (8708 jobs), zero errors, zero warnings**, ~55 s.
- **Axioms:** `lake env lean Axioms.lean` prints only `[propext, Classical.choice, Quot.sound]` for `C125.conjecture125_false`; matches `verification/axioms.txt`. Greps for `sorry`/`native_decide`/`admit`/`implemented_by`/`extern`/`unsafe`/declared `axiom` are clean.
- **Aux code:** no computation scripts; `verification/build.txt` consistent with the independent rebuild; `SHA256SUMS.txt` — the two mismatches (`conjecture.md`, `lean/Conjecture125/Basic.lean`) match exactly after CRLF conversion (Windows hashing artifact); all 12 other entries verify as stored.
- **Metadata:** `metadata.csv` lists 00000000125 as unsolved; no solution folder for it on main. README eligibility accurate; README line count (190) matches the Lean file.

## Semantic audit

The trace of A ∈ SL₂(F_p) lives in F_p, so the conjecture's "absolute value is a prime" only becomes well-defined after lifting F_p → Z. The submission handles this honestly and completely: it formalizes N_L(p) = #{A ∈ SL₂(F_p) : |L(tr A)| prime} for an arbitrary lift L, proves the disproof for every lift satisfying the mild condition that L(2) have prime absolute value for all large primes p, and instantiates it for the two canonical lifts — the centered representative (ZMod.valMinAbs, which sends 2 to 2 for p ≥ 4) and the standard representative (ZMod.val, 2 for p ≥ 3). Since every reasonable reading of the conjecture uses one of these two lifts, the decisive theorem `conjecture125_false` (¬Conjecture125 centeredLift ∧ ¬Conjecture125 standardLift, plus failure of O(p²/log p) for both) is an exact negation of the conjecture's asymptotic claim; no hypothesis is strengthened and no definition is redefined to trivialize the claim. The Lean objects are the conjecture's own: Mathlib's `Matrix.SpecialLinearGroup (Fin 2) (ZMod p)` is exactly SL₂(F_p), with `Matrix.trace`, ordinary Nat.Prime, and passage to infinity through the primes modeled by atTop on the prime subtype.

The mathematics is elementary and correct. The family T(a,b) = [[a, b], [−(a−1)²b⁻¹, 2−a]] has determinant a(2−a) + (a−1)² = 1 (verified in Lean by `linear_combination`) and trace 2, and the (0,0) and (0,1) entries recover a and b, so the map (a,b) ∈ F_p × F_p^× → SL₂(F_p) is injective; hence N_L(p) ≥ p(p−1) = p² − p whenever |L(2)| is prime. If N_L(p) ≤ C·p²/log p eventually, then at a prime p ≥ 3 with log p > 2C: log p · p(p−1) ≤ C·p² forces C ≥ log p·(p−2) ≥ 2C·1, i.e. p ≤ 2 — contradiction (the Lean `nlinarith` discharge matches this). So N_L is not O(p²/log p), which for every real c rules out N_L ~ c·p²/log p and N_L/(c·p²/log p) → 1. The gap is not marginal: the trace-2 fibre alone has ~p² elements, already larger than c·p²/log p by an unbounded factor log p (and the report's unformalized remark — each trace fibre has p² + χ(t²−4)p elements, so the true order is p³/log p — is itself correct, as I verified exactly for p = 5: fibre sizes 30, 20, 25, 25, 20). A brute-force check of SL₂(F_5) confirms |SL₂(F_5)| = 120, N(centered lift) = 50 ≥ p(p−1) = 20, and exactly 20 distinct trace-2 matrices in the family.

Faithfulness gate: no assumed theorem, no toy surrogate — the decisive theorem quantifies over the actual group and the actual count, and the counterexample family lives inside SL₂(F_p) for every prime p.

## Issues found

None blocking. Trivial notes: (i) SHA256SUMS CRLF artifact as above; (ii) the genuinely ambiguous phrase "absolute value of the trace" is handled by covering both standard lifts plus a general-lift theorem, with the uncovered readings (lifts sending 2 to a non-prime infinitely often) explicitly disclosed in the README — an honest scoping, not a loophole.

## Verdict

APPROVED. A faithful, complete, machine-checked disproof: N(p) ≥ p(p−1) for both standard integer lifts of the trace, so the count is not O(p²/log p) along the primes, and no real c makes N(p) asymptotic to c·p²/log p or the ratio tend to 1 — the conjectured asymptotic (with its Sato–Tate constant) fails by an unbounded factor. Build clean, axioms minimal, report matches the code.
